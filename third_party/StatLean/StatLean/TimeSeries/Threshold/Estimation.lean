module
public import StatLean.TimeSeries.Threshold.TAR
public import StatLean.TimeSeries.ARMA.Likelihood
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
-- Consumed only by the falsity witness for eq. (4.8) (`tarLS_clt_debt_false` below):
-- the coordinate white noise on `(ℤ → ℝ, ⊗ N(0,1))`, and `Matrix.PosDef.one`.
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Data.Real.StarOrdered

@[expose] public section

/-!
# TAR estimation with a known partition (FY §4.1.2, eqs. (4.4)–(4.8))

Least-squares fitting of a TAR model when the regime partition (and hence the regime
memberships of the observations) is known:

* `tarRegimeIndices` — the time indices falling in regime `i`, and `tarRegimeCount`
  `T_i = #{t : X_{t−d} ∈ A_i}`;
* `tarLSResidualSS` — the regime-`i` residual sum of squares (FY eq. (4.4)) and
  `tarSigmaHatSq` — the regime variance estimate `σ̂_i²` (eq. (4.6));
* `tarGeneralizedAIC` — the order/delay-selection criterion
  `Σ_i [T_i log σ̂_i²(p_i) + 2(p_i + 1)]` (eq. (4.7); the delay `d` is profiled by
  minimizing over the candidate grid, ties broken by the smallest `d` — recorded as
  the definition's tie-break convention);
* **eq. (4.8)** — the known-partition asymptotic normality
  `T_i^{1/2}(b̃_i − b_i) →d N(0, σ_i² W_i^{-1})`, a literature DEBT (the book says
  "can be shown", pointing at Theorem 3.2). The debt statement itself has been removed
  (see **Removed** below); its two machine-checked falsity witnesses and the whole
  deterministic reduction it was built on are kept. **Caution recorded in the
  inventory**: the printed `W_i` is built from the moments of the *fictitious global
  regime-`i` AR process*, not from moments conditional on `X_{t−d} ∈ A_i`. The frozen
  statement left `W_i` a free positive-definite matrix and was therefore FALSE
  (`tarLS_clt_debt_false`); pinning it to the *uncentered* regime-conditional design
  covariance `tarRegimeDesignCov` was still FALSE (`tarLS_clt_debt_centering_false`,
  finding 24); the repaired form pinned it to the **centered** one,
  `tarRegimeDesignCovCentered` — see `rad_designCovCentered_not_posDef` for the audit
  that the third repair is what kills the second witness.

**Removed (2026-08-10, user directive).** The module's single sorried declaration was
deleted; every proved declaration around it — both falsity witnesses, the normal-equation
section, and the design-covariance apparatus — is kept.
* `tarLS_clt_debt` — asserted FY eq. (4.8) in repaired form: the charFun/Cramér–Wold
  statement that the regime-wise LS estimator is `√T_i`-asymptotically normal with
  covariance `σ_i² W⁻¹`, `W = tarRegimeDesignCovCentered (A i) d X μ`.

Recover from `bdc8143f`.

**Scope.** FY Theorems 4.1/4.2 (Chan 1993a) and their consumers are **descoped**
(user, 2026-08-04); nothing here estimates the threshold `r` itself.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.1.2,
eqs. (4.4)–(4.8) (pp. 131–134). (`FY §4.1.2`.)

**Bibliographic comments.** Regime-wise least squares for TAR is Tong & Lim (1980);
the known-partition asymptotics are Chan (1993a, Ann. Statist.); the generalized AIC
is Tong (1990) §5.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open Classical in
/-- Time indices (within the usable window `P + 1 ≤ t < T`) whose threshold variable
falls in regime `i` (FY §4.1.2). -/
noncomputable def tarRegimeIndices {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) :
    Finset (Fin T) :=
  Finset.univ.filter fun t : Fin T => P < (t : ℕ) ∧ ∃ h : d ≤ (t : ℕ),
    x ⟨(t : ℕ) - d, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ ∈ A

/-- The regime-`i` sample size `T_i` (FY §4.1.2). -/
noncomputable def tarRegimeCount {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) : ℕ :=
  (tarRegimeIndices x A d P).card

/-- The regime-`i` **residual sum of squares** at coefficients `(β₀, β)`
(FY eq. (4.4)): `Σ_{t ∈ regime i} (x_t − β₀ − Σ_j β_j x_{t−1−j})²`. -/
noncomputable def tarLSResidualSS {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (β0 : ℝ) (β : Fin P → ℝ) : ℝ :=
  ∑ t ∈ tarRegimeIndices x A d P,
    (x t - β0 - ∑ j : Fin P, β j *
      x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩) ^ 2

/-- The regime-`i` variance estimate `σ̂_i² = RSS_i / T_i` (FY eq. (4.6); junk `0` when
the regime is empty). -/
noncomputable def tarSigmaHatSq {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (β0 : ℝ) (β : Fin P → ℝ) : ℝ :=
  tarLSResidualSS x A d β0 β / (tarRegimeCount x A d P : ℝ)

/-- The **generalized AIC** for TAR order selection (FY eq. (4.7)):
`Σ_i [T_i log σ̂_i²(p_i) + 2(p_i + 1)]`, evaluated at given regime fits. -/
noncomputable def tarGeneralizedAIC {k T P : ℕ} (x : Fin T → ℝ) (A : Fin k → Set ℝ)
    (d : ℕ) (β0 : Fin k → ℝ) (β : Fin k → Fin P → ℝ) (porder : Fin k → ℕ) : ℝ :=
  ∑ i, ((tarRegimeCount x (A i) d P : ℝ) *
      Real.log (tarSigmaHatSq x (A i) d (β0 i) (β i))
    + 2 * ((porder i : ℝ) + 1))

/-! ### Existence of a regime-wise least-squares fit

The regime-`i` residual sum of squares is `‖v − Lθ‖²` for the (finite-dimensional) linear
regressor map `L = tarFit` sending the coefficient vector `θ = (β₀, β)` to the fitted
values, extended by zero outside the regime window. Its range is a finite-dimensional —
hence closed — subspace of `Fin T → ℝ` whose elements vanish off the window, so the
sublevel set `{w ∈ range L | ‖v − w‖² ≤ ‖v‖²}` is closed and *bounded*, therefore compact:
the objective attains its minimum there, and that minimum is global on the range. -/

/-- The **regressor map** of the regime-`i` least-squares problem: `(β₀, β)` is sent to the
vector of fitted values `β₀ + Σ_j β_j x_{t−1−j}` on the regime window, extended by `0`
off it. -/
private noncomputable def tarFit {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ) :
    (ℝ × (Fin P → ℝ)) →ₗ[ℝ] (Fin T → ℝ) where
  toFun θ := fun t =>
    if t ∈ tarRegimeIndices x A d P then
      θ.1 + ∑ j : Fin P, θ.2 j *
        x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩
    else 0
  map_add' θ η := by
    funext t
    by_cases h : t ∈ tarRegimeIndices x A d P
    · simp only [h, if_true, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
        Finset.sum_add_distrib]
      ring
    · simp [h]
  map_smul' c θ := by
    funext t
    by_cases h : t ∈ tarRegimeIndices x A d P
    · simp only [h, if_true, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, Pi.smul_apply]
      simp only [mul_add, Finset.mul_sum, mul_assoc]
    · simp [h]

private lemma tarFit_apply_of_mem {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (θ : ℝ × (Fin P → ℝ)) {t : Fin T} (ht : t ∈ tarRegimeIndices x A d P) :
    tarFit x A d θ t = θ.1 + ∑ j : Fin P, θ.2 j *
      x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩ :=
  if_pos ht

private lemma tarFit_apply_of_not_mem {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (θ : ℝ × (Fin P → ℝ)) {t : Fin T} (ht : t ∉ tarRegimeIndices x A d P) :
    tarFit x A d θ t = 0 :=
  if_neg ht

/-- The least-squares objective as a function of the fitted-value vector. -/
private noncomputable def tarObj {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ)
    (w : Fin T → ℝ) : ℝ :=
  ∑ t ∈ tarRegimeIndices x A d P, (x t - w t) ^ 2

private lemma tarObj_continuous {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) :
    Continuous (tarObj x A d P) :=
  continuous_finset_sum _ fun t _ => ((continuous_const.sub (continuous_apply t)).pow 2)

private lemma tarObj_nonneg {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ)
    (w : Fin T → ℝ) : 0 ≤ tarObj x A d P w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma tarLSResidualSS_eq_tarObj {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (β0 : ℝ) (β : Fin P → ℝ) :
    tarLSResidualSS x A d β0 β = tarObj x A d P (tarFit x A d (β0, β)) := by
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [tarFit_apply_of_mem x A d (β0, β) ht]
  ring_nf

/-- The regime-`i` least-squares fit is characterized by its normal equations
(the finite-dimensional projection; no invertibility needed for existence). -/
theorem exists_tarLS_minimizer {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ) :
    ∃ (β0 : ℝ) (β : Fin P → ℝ), ∀ (γ0 : ℝ) (γ : Fin P → ℝ),
      tarLSResidualSS x A d β0 β ≤ tarLSResidualSS x A d γ0 γ := by
  classical
  -- the sublevel set of the objective inside the range of the regressor map
  obtain ⟨C, hC⟩ : ∃ C : Set (Fin T → ℝ),
      C = ((LinearMap.range (tarFit (P := P) x A d) : Submodule ℝ (Fin T → ℝ)) :
            Set (Fin T → ℝ))
          ∩ {w | tarObj x A d P w ≤ tarObj x A d P 0} := ⟨_, rfl⟩
  have h0C : (0 : Fin T → ℝ) ∈ C := by
    rw [hC]
    refine ⟨⟨0, map_zero _⟩, ?_⟩
    simp only [Set.mem_setOf_eq]
    exact le_rfl
  have hCclosed : IsClosed C := by
    rw [hC]
    exact (Submodule.closed_of_finiteDimensional _).inter
      (isClosed_le (tarObj_continuous x A d P) continuous_const)
  -- boundedness: on the window the objective controls each coordinate, off the window
  -- every element of the range vanishes
  have hCbdd : Bornology.IsBounded C := by
    refine isBounded_iff_forall_norm_le.mpr
      ⟨(∑ s : Fin T, |x s|) + Real.sqrt (tarObj x A d P 0), fun w hw => ?_⟩
    have hR : (0 : ℝ) ≤ (∑ s : Fin T, |x s|) + Real.sqrt (tarObj x A d P 0) :=
      add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Real.sqrt_nonneg _)
    rw [pi_norm_le_iff_of_nonneg hR]
    intro t
    rw [hC] at hw
    by_cases ht : t ∈ tarRegimeIndices x A d P
    · have hw2 : tarObj x A d P w ≤ tarObj x A d P 0 := hw.2
      have hterm : (x t - w t) ^ 2 ≤ tarObj x A d P 0 :=
        le_trans (Finset.single_le_sum (f := fun s => (x s - w s) ^ 2)
          (fun s _ => sq_nonneg _) ht) hw2
      have habs : |x t - w t| ≤ Real.sqrt (tarObj x A d P 0) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hterm
      have hxt : |x t| ≤ ∑ s : Fin T, |x s| :=
        Finset.single_le_sum (f := fun s => |x s|) (fun s _ => abs_nonneg _)
          (Finset.mem_univ t)
      have hsplit : |w t| ≤ |x t| + |x t - w t| := by
        rcases abs_cases (w t) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (x t) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
            rcases abs_cases (x t - w t) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith
      calc ‖w t‖ = |w t| := rfl
        _ ≤ |x t| + |x t - w t| := hsplit
        _ ≤ (∑ s : Fin T, |x s|) + Real.sqrt (tarObj x A d P 0) := add_le_add hxt habs
    · obtain ⟨θ, hθ⟩ := hw.1
      have : w t = 0 := by rw [← hθ]; exact tarFit_apply_of_not_mem x A d θ ht
      rw [this]
      simpa using hR
  -- a minimizer on the compact sublevel set is a global minimizer on the range
  obtain ⟨w0, hw0C, hw0min⟩ :=
    (Metric.isCompact_of_isClosed_isBounded hCclosed hCbdd).exists_isMinOn ⟨0, h0C⟩
      (tarObj_continuous x A d P).continuousOn
  rw [hC] at hw0C
  obtain ⟨θ, hθ⟩ := hw0C.1
  refine ⟨θ.1, θ.2, fun γ0 γ => ?_⟩
  rw [tarLSResidualSS_eq_tarObj, tarLSResidualSS_eq_tarObj]
  have hθ' : tarFit x A d (θ.1, θ.2) = w0 := by rw [← hθ]
  rw [hθ']
  by_cases hcase : tarObj x A d P (tarFit x A d (γ0, γ)) ≤ tarObj x A d P 0
  · refine isMinOn_iff.mp hw0min _ ?_
    rw [hC]
    refine ⟨⟨(γ0, γ), rfl⟩, ?_⟩
    simpa only [Set.mem_setOf_eq] using hcase
  · have hw0le : tarObj x A d P w0 ≤ tarObj x A d P 0 := hw0C.2
    exact le_trans hw0le (le_of_not_ge hcase)

/-! ### The frozen eq. (4.8) statement is FALSE — a formalized witness

Two independent defects of the frozen statement, found in wave `ts/s12-model-selection`
(2026-08-09):

1. **`W` is a free parameter.** The docstring says `W_i` is the second-moment matrix of
   the fictitious regime-`i` AR process, but formally `W` is universally quantified over
   *all* positive-definite matrices with no link to `(b, σ, A, X)`. Two admissible values
   `W` and `2W` force two different Gaussian limits for the same sequence, so the
   conclusion cannot hold whenever `c ≠ 0` and the hypotheses are satisfiable.
2. **`hLS` pins the intercept at the truth.** The minimality is asserted for the pair
   `(b0 i, bhat T ω)` against *all* `(γ0, γ)`, i.e. the true intercept `b0 i` is required
   to be the least-squares intercept at every `ω` and every `T`. That is a
   probability-zero constraint on the data as soon as the regime window is non-empty and
   the noise is non-degenerate; it is not what FY eqs. (4.4)-(4.5) define.

The witness below exploits neither pathology directly: it takes the **degenerate-regime**
route, which is the cheapest satisfiable instance. `IsTAR` allows an empty regime
(`A = ![univ, ∅]` is a measurable partition), the regime-`1` least-squares problem is then
vacuous (`hLS` reads `0 ≤ 0`), `T_1 = 0`, and the scaled statistic is identically `0`;
its characteristic function is the constant `1`, while the frozen limit at `W = 1`,
`c = 1` is `exp(-1/2)`. The instance is built from scratch on `(ℤ → ℝ, ⊗ N(0,1))` so the
witness is **axiom-clean** — in particular it does not go through
`exists_stationary_tar`, whose path-space input is itself an open debt.

Repairing the statement needs (i) `W` tied to the process (Chan 1993a's
`E[Z_t Z_tᵀ]` for the fictitious regime-`i` AR process), (ii) `hLS` re-stated as joint
minimality over `(β₀, β)` with `bhat` the `β`-component, and (iii) a non-degeneracy
hypothesis `T_i → ∞` (equivalently `P(X_{t-d} ∈ A_i) > 0`), without which even a repaired
`W` leaves the degenerate instance a counterexample.

**All three repairs were applied** to the (since removed) repaired debt statement, wave
`ts/s12b-model-repairs`, 2026-08-09.
This witness is kept verbatim, quantified over the *frozen* shape `H`, as the permanent
record of what the repairs are for. -/

/-! ### A concrete standard-Gaussian white noise on `ℤ` -/

private noncomputable def wnMeasure : Measure (ℤ → ℝ) :=
  Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)

private instance : IsProbabilityMeasure wnMeasure := by
  unfold wnMeasure; infer_instance

private def wnCoord (t : ℤ) (ω : ℤ → ℝ) : ℝ := ω t

private lemma wnCoord_measurable (t : ℤ) : Measurable (wnCoord t) := measurable_pi_apply t

private lemma wnMeasure_map_coord (t : ℤ) : wnMeasure.map (wnCoord t) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ t

private lemma wnCoord_identDistrib (t : ℤ) :
    IdentDistrib (wnCoord t) (id : ℝ → ℝ) wnMeasure (gaussianReal 0 1) :=
  ⟨(wnCoord_measurable t).aemeasurable, aemeasurable_id, by
    rw [Measure.map_id, wnMeasure_map_coord t]⟩

private lemma wn_isIIDNoise : IsIIDNoise wnCoord 1 wnMeasure := by
  refine ⟨wnCoord_measurable, ?_, ?_, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ : ℤ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  · exact fun s t => (wnCoord_identDistrib s).trans (wnCoord_identDistrib t).symm
  · exact (wnCoord_identDistrib 0).memLp_iff.2 (memLp_id_gaussianReal 2)
  · rw [(wnCoord_identDistrib 0).integral_eq]
    simp only [id_eq]
    exact (integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)))
  · rw [(wnCoord_identDistrib 0).variance_eq, variance_id_gaussianReal]
    simp

private lemma wn_memLp (t : ℤ) : MemLp (wnCoord t) 2 wnMeasure :=
  (wn_isIIDNoise.identDistrib t 0).memLp_iff.2 wn_isIIDNoise.memLp

private lemma wnMeasure_shift (k : ℤ) :
    wnMeasure.map (fun (ω : ℤ → ℝ) (s : ℤ) => ω (s + k)) = wnMeasure := by
  unfold wnMeasure
  have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℤ => ℝ)
    (μ := fun _ : ℤ => gaussianReal 0 1) (Equiv.addRight (-k))
  convert h using 2
  funext ω s
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp

private lemma wn_strictlyStationary : IsStrictlyStationary wnCoord wnMeasure := by
  intro n t k
  have hshift : Measurable (fun (ω : ℤ → ℝ) (s : ℤ) => ω (s + k)) :=
    measurable_pi_lambda _ fun s => measurable_pi_apply _
  have htup : Measurable (fun (ω : ℤ → ℝ) (i : Fin n) => ω (t i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hcomp : (fun (ω : ℤ → ℝ) (i : Fin n) => wnCoord (t i + k) ω)
      = (fun (ω' : ℤ → ℝ) (i : Fin n) => ω' (t i)) ∘ (fun (ω : ℤ → ℝ) (s : ℤ) => ω (s + k)) :=
    rfl
  rw [hcomp, ← Measure.map_map htup hshift, wnMeasure_shift k]
  rfl

private lemma wn_indep_past (t : ℤ) :
    Indep (MeasurableSpace.comap (wnCoord t) inferInstance) (sigmaLT wnCoord t) wnMeasure := by
  have hdisj : Disjoint ({t} : Set ℤ) (Set.Iio t) :=
    Set.disjoint_singleton_left.2 (by simp)
  have := indep_iSup_of_disjoint
    (m := fun s : ℤ => MeasurableSpace.comap (wnCoord s) inferInstance)
    (fun s => (wnCoord_measurable s).comap_le) wn_isIIDNoise.iIndep hdisj
  simpa using! this


/-! ### The degenerate two-regime TAR witness -/

/-- Two regimes, the second of which is **empty**: a legitimate `IsTAR` partition. -/
private noncomputable def wnA : Fin 2 → Set ℝ := fun i => if i = 0 then Set.univ else ∅

private lemma wn_isTAR :
    IsTAR (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => fun _ : Fin 1 => (0 : ℝ))
      (fun _ : Fin 2 => (1 : ℝ)) wnA 1 wnCoord wnCoord wnMeasure := by
  refine ⟨le_rfl, fun _ => one_pos, ?_, ?_, ?_, wnCoord_measurable, wn_isIIDNoise,
    wn_indep_past, ?_⟩
  · intro i
    by_cases h : i = 0 <;> simp [wnA, h]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [wnA]
  · refine Set.eq_univ_of_univ_subset ?_
    have h0 : wnA 0 ⊆ ⋃ i, wnA i := Set.subset_iUnion (fun i => wnA i) 0
    simpa [wnA] using h0
  · intro t
    filter_upwards with ω
    rw [Fin.sum_univ_two]
    simp [wnA, wnCoord]


/-! ### The falsity of the frozen eq. (4.8) statement -/

private lemma tarRegimeIndices_empty {T : ℕ} (x : Fin T → ℝ) (d P : ℕ) :
    tarRegimeIndices x (∅ : Set ℝ) d P = (∅ : Finset (Fin T)) := by
  classical
  ext t
  simp [tarRegimeIndices]

private lemma wnA_one : wnA 1 = (∅ : Set ℝ) := by
  simp [wnA]

/-- **The frozen `tarLS_clt_debt` statement is FALSE.** -/
private theorem tarLS_clt_debt_false
    (H : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {k P : ℕ}
      {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ} {σ : Fin k → ℝ} {A : Fin k → Set ℝ}
      {d : ℕ} {X ε : ℤ → Ω → ℝ},
      IsTAR b0 b σ A d X ε μ → IsStrictlyStationary X μ → (∀ t, MemLp (X t) 2 μ) →
      ∀ (i : Fin k) (W : Matrix (Fin P) (Fin P) ℝ), W.PosDef →
      ∀ (bhat : (T : ℕ) → Ω → Fin P → ℝ), (∀ T, Measurable (bhat T)) →
      (∀ (T : ℕ) (ω : Ω) (γ0 : ℝ) (γ : Fin P → ℝ),
        tarLSResidualSS (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d (b0 i) (bhat T ω)
          ≤ tarLSResidualSS (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d γ0 γ) →
      ∀ (c : Fin P → ℝ) (u : ℝ),
      Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
          Real.sqrt (tarRegimeCount (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d P) *
            ∑ j, c j * (bhat T ω j - b i j)) u)
        atTop
        (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (σ i ^ 2 * (c ⬝ᵥ (W⁻¹ *ᵥ c))))) u))) :
    False := by
  classical
  have hLS : ∀ (T : ℕ) (ω : ℤ → ℝ) (γ0 : ℝ) (γ : Fin 1 → ℝ),
      tarLSResidualSS (fun t : Fin T => wnCoord (((t : ℕ) : ℤ) + 1) ω) (wnA 1) 1
          ((fun _ : Fin 2 => (0 : ℝ)) 1) ((fun _ _ _ => 0 : (T : ℕ) → (ℤ → ℝ) → Fin 1 → ℝ) T ω)
        ≤ tarLSResidualSS (fun t : Fin T => wnCoord (((t : ℕ) : ℤ) + 1) ω) (wnA 1) 1 γ0 γ := by
    intro T ω γ0 γ
    simp only [tarLSResidualSS, wnA_one, tarRegimeIndices_empty, Finset.sum_empty]
    exact le_rfl
  have key := H wn_isTAR wn_strictlyStationary wn_memLp 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)
    Matrix.PosDef.one (fun _ _ _ => 0) (fun _ => measurable_const) hLS (fun _ => 1) 1
  -- the regime is empty, so the scaled statistic is identically `0`
  simp only [sub_self, mul_zero, Finset.sum_const_zero] at key
  -- the law is `δ₀`, whose characteristic function is identically `1`
  have hmapconst : wnMeasure.map (fun _ : ℤ → ℝ => (0 : ℝ)) = Measure.dirac 0 := by
    rw [Measure.map_const]
    simp
  rw [hmapconst] at key
  have hone : charFun (Measure.dirac (0 : ℝ)) (1 : ℝ) = 1 := by
    rw [charFun_dirac]
    simp
  simp only [hone] at key
  -- the alleged limit is `exp(−1/2) ≠ 1`
  have hvar : ((fun _ : Fin 2 => (1 : ℝ)) 1) ^ 2 *
      ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ (fun _ => 1))) = 1 := by
    rw [inv_one]
    simp [Matrix.one_mulVec, dotProduct]
  rw [hvar] at key
  have hlim : charFun (gaussianReal 0 (Real.toNNReal 1)) (1 : ℝ) = 1 :=
    tendsto_nhds_unique tendsto_const_nhds key |>.symm
  rw [charFun_gaussianReal] at hlim
  norm_num at hlim
  rw [show ((-(1 / 2) : ℂ)) = (((-(1 / 2) : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp] at hlim
  have hR : Real.exp (-(1 / 2)) = 1 := by exact_mod_cast hlim
  have hlt : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- The **regime-`i` conditional design covariance** `W_i`: the second-moment matrix of
the regressor vector `Z_t = (X_{t−1−j})_{j<P}` **conditional on the regime event**
`{X_{t−d} ∈ A_i}`, evaluated at `t = 0` (under strict stationarity the choice of `t` is
immaterial). Junk `0` on a null regime event, by the `⁻¹`/`toReal` conventions. -/
noncomputable def tarRegimeDesignCov {P : ℕ} (A : Set ℝ) (d : ℕ)
    (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Matrix (Fin P) (Fin P) ℝ :=
  Matrix.of fun j l => ((μ {ω | X (-(d : ℤ)) ω ∈ A}).toReal)⁻¹ *
    ∫ ω in {ω | X (-(d : ℤ)) ω ∈ A},
      X (-1 - (j : ℕ)) ω * X (-1 - (l : ℕ)) ω ∂μ

/-- The **regime-`i` conditional design mean** `m_i = E[Z_0 | X_{−d} ∈ A_i]`, the
regime-conditional mean of the regressor vector `Z_t = (X_{t−1−j})_{j<P}` at `t = 0`.
Junk `0` on a null regime event, by the `⁻¹`/`toReal` conventions.

Introduced by wave `ts/f1b-arma-deep` for the third repair of eq. (4.8) — see
`tarRegimeDesignCovCentered`. -/
noncomputable def tarRegimeDesignMean {P : ℕ} (A : Set ℝ) (d : ℕ)
    (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Fin P → ℝ :=
  fun j => ((μ {ω | X (-(d : ℤ)) ω ∈ A}).toReal)⁻¹ *
    ∫ ω in {ω | X (-(d : ℤ)) ω ∈ A}, X (-1 - (j : ℕ)) ω ∂μ

/-- The **centered** regime-`i` conditional design covariance

  `Σ_i = E[Z₀ Z₀ᵀ | X_{−d} ∈ A_i] − E[Z₀ | X_{−d} ∈ A_i] E[Z₀ | X_{−d} ∈ A_i]ᵀ`,

i.e. the regime-conditional *covariance* — as opposed to *second-moment* — matrix of the
regressor vector. This is the matrix the regime-wise least-squares **slope** actually
sees, because FY eqs. (4.4)–(4.5) fit an intercept alongside the slopes and the intercept
absorbs the regime-conditional regressor mean.

Introduced by wave `ts/f1b-arma-deep` as the object prescribed by finding 24
(`tarLS_clt_debt_centering_false`), whose witness has `tarRegimeDesignCov = 1` positive
definite while `tarRegimeDesignCovCentered = 0` (`rad_designCovCentered` below). -/
noncomputable def tarRegimeDesignCovCentered {P : ℕ} (A : Set ℝ) (d : ℕ)
    (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Matrix (Fin P) (Fin P) ℝ :=
  tarRegimeDesignCov A d X μ -
    Matrix.of fun j l => tarRegimeDesignMean A d X μ j * tarRegimeDesignMean A d X μ l

/-! ### The *repaired* eq. (4.8) statement is STILL FALSE — the centering defect

The repairs of wave `ts/s12b-model-repairs` pin `W` to `tarRegimeDesignCov`, i.e. to the
**uncentered** regime-conditional second-moment matrix `E[Z_0 Z_0ᵀ | X_{−d} ∈ A_i]`.  But
FY eqs. (4.4)–(4.5) fit an **intercept** alongside the slopes, so what the regime-`i`
least-squares slope actually sees is the *centered* design covariance
`Σ_i = E[Z_0 Z_0ᵀ | ·] − E[Z_0 | ·] E[Z_0 | ·]ᵀ`, and the asymptotic covariance is
`σ_i² Σ_i^{-1}`, not `σ_i² W_i^{-1}`.  The two agree only when the regime-conditional
regressor mean vanishes.

The witness below drives that gap to its extreme: it exhibits a legitimate TAR instance in
which the regime-conditional regressor is a.s. **constant**, so `Σ_i = 0` (the slope is
not identified at all) while `W_i = 1` is positive definite as the repaired hypothesis
`hW` demands.  Every repaired hypothesis holds — `W` is pinned to the process, `hLS` is
*joint* minimality over `(β₀, β)`, and the regime carries mass `1/2` — yet the least-squares
slope may legitimately be taken to be the constant `0`, which is the true value, so the
scaled statistic is identically `0` and its characteristic function is the constant `1`,
against the claimed `exp(−1/2)`.

Concretely: i.i.d. **Rademacher** innovations (the atom is what makes a singleton regime
carry mass), `k = 2`, `d = P = 1`, `A₀ = {1}`, `A₁ = {1}ᶜ`, and zero coefficients, so
`X = ε`.  With `d = P = 1` the threshold variable `X_{t−d}` and the single regressor
`X_{t−1}` are the *same* variable, so on regime `0` the regressor is identically `1` and
the design `(1, X_{t−1}) = (1, 1)` is rank one: the intercept absorbs the slope.

**The repair this points to** is to replace `tarRegimeDesignCov` by its centered version
(or, equivalently under Chan's fictitious-process reading, to state eq. (4.8) for the
*mean-corrected* regressors), and to require that centered matrix — not the uncentered one
— to be positive definite.  Recorded as finding 24 of the campaign. -/

/-- The **Rademacher law** on `ℝ`: the two-point law of mean `0` and variance `1`.  An
atom is exactly what the witness needs and what `gaussianReal` cannot supply. -/
private noncomputable def radLaw : Measure ℝ :=
  (2⁻¹ : ENNReal) • Measure.dirac (-1 : ℝ) + (2⁻¹ : ENNReal) • Measure.dirac (1 : ℝ)

private instance : IsProbabilityMeasure radLaw := by
  constructor
  simp only [radLaw, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- Integration against the Rademacher law: the two-point average. -/
private lemma integral_radLaw (f : ℝ → ℝ) :
    ∫ x, f x ∂radLaw = (f (-1) + f 1) / 2 := by
  have h1 : Integrable f (Measure.dirac (-1 : ℝ)) := integrable_dirac (by finiteness)
  have h2 : Integrable f (Measure.dirac (1 : ℝ)) := integrable_dirac (by finiteness)
  rw [radLaw, integral_add_measure (h1.smul_measure (by finiteness))
      (h2.smul_measure (by finiteness)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

private lemma memLp_id_radLaw : MemLp (id : ℝ → ℝ) 2 radLaw := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  have hbd : ∀ᵐ x ∂radLaw, ‖(id : ℝ → ℝ) x‖ ≤ 1 := by
    have h0 : radLaw {x : ℝ | ¬ ‖x‖ ≤ 1} = 0 := by
      have hsub : {x : ℝ | ¬ ‖x‖ ≤ 1} ⊆ ({-1, 1} : Set ℝ)ᶜ := by
        intro x hx hmem
        rcases hmem with h | h <;> (rw [Set.mem_setOf_eq] at hx; apply hx; rw [h]; simp)
      refine measure_mono_null hsub ?_
      simp only [radLaw, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [Measure.dirac_apply' _ (by measurability), Measure.dirac_apply' _ (by measurability)]
      simp
    exact h0
  exact (eLpNorm_le_of_ae_bound hbd).trans_lt (by finiteness)

private lemma integral_id_radLaw : ∫ x, (x : ℝ) ∂radLaw = 0 := by
  have := integral_radLaw (fun x : ℝ => x)
  simpa using this

private lemma variance_id_radLaw : variance (id : ℝ → ℝ) radLaw = 1 := by
  rw [variance_eq_integral memLp_id_radLaw.aestronglyMeasurable.aemeasurable]
  have hI : ∫ x, (x : ℝ) ∂radLaw = 0 := integral_id_radLaw
  simp only [id_eq, hI]
  have := integral_radLaw (fun x : ℝ => (x - 0) ^ 2)
  simpa using this

/-! #### The i.i.d. Rademacher coordinate noise on `(ℤ → ℝ, ⊗ Rad)` -/

private noncomputable def radMeasure : Measure (ℤ → ℝ) :=
  Measure.infinitePi (fun _ : ℤ => radLaw)

private instance : IsProbabilityMeasure radMeasure := by
  unfold radMeasure; infer_instance

private def radCoord (t : ℤ) (ω : ℤ → ℝ) : ℝ := ω t

private lemma radCoord_measurable (t : ℤ) : Measurable (radCoord t) := measurable_pi_apply t

private lemma radMeasure_map_coord (t : ℤ) : radMeasure.map (radCoord t) = radLaw :=
  Measure.infinitePi_map_eval _ t

private lemma radCoord_identDistrib (t : ℤ) :
    IdentDistrib (radCoord t) (id : ℝ → ℝ) radMeasure radLaw :=
  ⟨(radCoord_measurable t).aemeasurable, aemeasurable_id, by
    rw [Measure.map_id, radMeasure_map_coord t]⟩

private lemma rad_isIIDNoise : IsIIDNoise radCoord 1 radMeasure := by
  refine ⟨radCoord_measurable, ?_, ?_, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ : ℤ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  · exact fun s t => (radCoord_identDistrib s).trans (radCoord_identDistrib t).symm
  · exact (radCoord_identDistrib 0).memLp_iff.2 memLp_id_radLaw
  · rw [(radCoord_identDistrib 0).integral_eq]
    exact integral_id_radLaw
  · rw [(radCoord_identDistrib 0).variance_eq]
    exact variance_id_radLaw

private lemma rad_memLp (t : ℤ) : MemLp (radCoord t) 2 radMeasure :=
  (rad_isIIDNoise.identDistrib t 0).memLp_iff.2 rad_isIIDNoise.memLp

private lemma radMeasure_shift (k : ℤ) :
    radMeasure.map (fun (ω : ℤ → ℝ) (s : ℤ) => ω (s + k)) = radMeasure := by
  unfold radMeasure
  have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℤ => ℝ)
    (μ := fun _ : ℤ => radLaw) (Equiv.addRight (-k))
  convert h using 2
  funext ω s
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp

private lemma rad_strictlyStationary : IsStrictlyStationary radCoord radMeasure := by
  intro n t k
  have hshift : Measurable (fun (ω : ℤ → ℝ) (s : ℤ) => ω (s + k)) :=
    measurable_pi_lambda _ fun s => measurable_pi_apply _
  have htup : Measurable (fun (ω : ℤ → ℝ) (i : Fin n) => ω (t i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hcomp : (fun (ω : ℤ → ℝ) (i : Fin n) => radCoord (t i + k) ω)
      = (fun (ω' : ℤ → ℝ) (i : Fin n) => ω' (t i)) ∘ (fun (ω : ℤ → ℝ) (s : ℤ) => ω (s + k)) :=
    rfl
  rw [hcomp, ← Measure.map_map htup hshift, radMeasure_shift k]
  rfl

private lemma rad_indep_past (t : ℤ) :
    Indep (MeasurableSpace.comap (radCoord t) inferInstance) (sigmaLT radCoord t) radMeasure := by
  have hdisj : Disjoint ({t} : Set ℤ) (Set.Iio t) :=
    Set.disjoint_singleton_left.2 (by simp)
  have := indep_iSup_of_disjoint
    (m := fun s : ℤ => MeasurableSpace.comap (radCoord s) inferInstance)
    (fun s => (radCoord_measurable s).comap_le) rad_isIIDNoise.iIndep hdisj
  simpa using! this

/-! #### The singleton-regime TAR instance -/

/-- Two regimes split by the atom `1`: `A₀ = {1}` carries mass `1/2`, and on it the
`d = P = 1` regressor `X_{t−1}` — which *is* the threshold variable — is identically `1`. -/
private noncomputable def radA : Fin 2 → Set ℝ := fun i => if i = 0 then {1} else {(1 : ℝ)}ᶜ

private lemma rad_isTAR :
    IsTAR (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => fun _ : Fin 1 => (0 : ℝ))
      (fun _ : Fin 2 => (1 : ℝ)) radA 1 radCoord radCoord radMeasure := by
  refine ⟨le_rfl, fun _ => one_pos, ?_, ?_, ?_, radCoord_measurable, rad_isIIDNoise,
    rad_indep_past, ?_⟩
  · intro i
    by_cases h : i = 0 <;> simp [radA, h]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [radA]
  · refine Set.eq_univ_of_univ_subset fun x _ => ?_
    by_cases hx : x = 1
    · exact Set.mem_iUnion.2 ⟨0, by simp [radA, hx]⟩
    · exact Set.mem_iUnion.2 ⟨1, by simp [radA, hx]⟩
  · intro t
    filter_upwards with ω
    rw [Fin.sum_univ_two]
    have hf0 : (fun _ : ℝ => (0 : ℝ)
          + (∑ j : Fin 1, (0 : ℝ) * radCoord (t - 1 - (j : ℕ)) ω) + (1 : ℝ) * radCoord t ω)
        = fun _ : ℝ => radCoord t ω := by
      funext _; simp
    rw [hf0]
    have h0 : radA 0 = ({1} : Set ℝ) := by simp [radA]
    have h1 : radA 1 = ({(1 : ℝ)} : Set ℝ)ᶜ := by simp [radA]
    rw [h0, h1]
    by_cases hx : radCoord (t - ((1 : ℕ) : ℤ)) ω = 1
    · rw [Set.indicator_of_mem (by simpa using hx),
        Set.indicator_of_notMem (by simpa using hx), add_zero]
    · rw [Set.indicator_of_notMem (by simpa using hx),
        Set.indicator_of_mem (by simpa using hx), zero_add]

/-! #### The regime has mass `1/2` and (uncentered) design covariance `1` -/

private lemma rad_regime_set :
    {ω : ℤ → ℝ | radCoord (-((1 : ℕ) : ℤ)) ω ∈ radA 0} = radCoord (-1) ⁻¹' ({1} : Set ℝ) := by
  ext ω
  simp [radCoord, radA]

private lemma rad_mass_eq : radMeasure (radCoord (-1) ⁻¹' ({1} : Set ℝ)) = 2⁻¹ := by
  have hmeas : MeasurableSet ({(1 : ℝ)}) := measurableSet_singleton 1
  rw [← Measure.map_apply (radCoord_measurable _) hmeas, radMeasure_map_coord]
  simp only [radLaw, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hmeas]
  rw [Set.indicator_of_notMem (by norm_num), Set.indicator_of_mem (by simp)]
  simp

private lemma rad_designCov :
    tarRegimeDesignCov (P := 1) (radA 0) 1 radCoord radMeasure
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hS : MeasurableSet (radCoord (-1) ⁻¹' ({(1 : ℝ)})) :=
    (radCoord_measurable _) (measurableSet_singleton 1)
  ext j l
  fin_cases j
  fin_cases l
  simp only [tarRegimeDesignCov, Matrix.of_apply, Matrix.one_apply_eq]
  rw [rad_regime_set, rad_mass_eq]
  have hone : ∀ ω ∈ radCoord (-1) ⁻¹' ({(1 : ℝ)}),
      radCoord (-1 - ((⟨0, by norm_num⟩ : Fin 1) : ℕ)) ω
        * radCoord (-1 - ((⟨0, by norm_num⟩ : Fin 1) : ℕ)) ω = 1 := by
    intro ω hω
    have : radCoord (-1) ω = 1 := hω
    norm_num [radCoord] at this ⊢
    rw [this]
    norm_num
  rw [setIntegral_congr_fun hS hone, setIntegral_const, measureReal_def, rad_mass_eq]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul, mul_one]
  norm_num

/-- The regime-conditional design **mean** of the witness is `1`: on regime `0` the single
regressor is a.s. the constant `1`. -/
private lemma rad_designMean :
    tarRegimeDesignMean (P := 1) (radA 0) 1 radCoord radMeasure = fun _ => (1 : ℝ) := by
  have hS : MeasurableSet (radCoord (-1) ⁻¹' ({(1 : ℝ)})) :=
    (radCoord_measurable _) (measurableSet_singleton 1)
  funext j
  fin_cases j
  simp only [tarRegimeDesignMean]
  rw [rad_regime_set, rad_mass_eq]
  have hone : ∀ ω ∈ radCoord (-1) ⁻¹' ({(1 : ℝ)}),
      radCoord (-1 - ((⟨0, by norm_num⟩ : Fin 1) : ℕ)) ω = 1 := by
    intro ω hω
    have : radCoord (-1) ω = 1 := hω
    norm_num [radCoord] at this ⊢
    exact this
  rw [setIntegral_congr_fun hS hone, setIntegral_const, measureReal_def, rad_mass_eq]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul, mul_one]
  norm_num

/-- **The third repair is exactly the right one.** On the finding-24 witness the *centered*
design covariance is `0` — so the repaired hypothesis `hW : W.PosDef` of the restated
(and since removed) eq. (4.8) debt is **not** satisfiable there, and the witness no longer
applies. -/
private lemma rad_designCovCentered :
    tarRegimeDesignCovCentered (P := 1) (radA 0) 1 radCoord radMeasure = 0 := by
  rw [tarRegimeDesignCovCentered, rad_designCov, rad_designMean]
  ext j l
  fin_cases j
  fin_cases l
  simp

/-- ... hence the witness's regime fails the repaired positive-definiteness hypothesis. -/
private lemma rad_designCovCentered_not_posDef :
    ¬ (tarRegimeDesignCovCentered (P := 1) (radA 0) 1 radCoord radMeasure).PosDef := by
  rw [rad_designCovCentered]
  intro hpd
  have hunit := hpd.isUnit
  rw [Matrix.isUnit_iff_isUnit_det] at hunit
  simp at hunit

/-! #### A measurable regime-wise least-squares fit with the slope pinned at `0`

Because the regressor is `≡ 1` on the regime, the design `(1, X_{t−1}) = (1, 1)` is rank
one and the intercept absorbs the slope entirely: the regime sample mean paired with the
**zero** slope is a genuine joint minimizer of FY eq. (4.4). -/

/-- The regime-`0` sample mean of the responses (junk `0` on an empty regime). -/
private noncomputable def radMean {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  (∑ t ∈ tarRegimeIndices x (radA 0) 1 1, x t) / (tarRegimeCount x (radA 0) 1 1 : ℝ)

private lemma measurableSet_radRegime {T : ℕ} (t : Fin T) :
    MeasurableSet {x : Fin T → ℝ | t ∈ tarRegimeIndices x (radA 0) 1 1} := by
  classical
  by_cases ht : 1 < (t : ℕ)
  · have hset : {x : Fin T → ℝ | t ∈ tarRegimeIndices x (radA 0) 1 1}
        = (fun x : Fin T → ℝ => x ⟨(t : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩)
            ⁻¹' (radA 0) := by
      ext x
      simp only [tarRegimeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨fun h => h.2.choose_spec, fun hx => ⟨ht, le_of_lt ht, hx⟩⟩
    rw [hset]
    exact (measurable_pi_apply _) (by simp [radA])
  · have hset : {x : Fin T → ℝ | t ∈ tarRegimeIndices x (radA 0) 1 1} = ∅ := by
      ext x
      simp only [tarRegimeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h ht
    rw [hset]
    exact MeasurableSet.empty

private lemma measurable_radRegimeSum {T : ℕ} (g : Fin T → (Fin T → ℝ) → ℝ)
    (hg : ∀ t, Measurable (g t)) :
    Measurable fun x : Fin T → ℝ => ∑ t ∈ tarRegimeIndices x (radA 0) 1 1, g t x := by
  classical
  have heq : (fun x : Fin T → ℝ => ∑ t ∈ tarRegimeIndices x (radA 0) 1 1, g t x)
      = fun x : Fin T → ℝ =>
        ∑ t : Fin T, if t ∈ tarRegimeIndices x (radA 0) 1 1 then g t x else 0 := by
    funext x
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [heq]
  exact Finset.measurable_sum _ fun t _ =>
    Measurable.ite (measurableSet_radRegime t) (hg t) measurable_const

private lemma measurable_radMean (T : ℕ) : Measurable (radMean : (Fin T → ℝ) → ℝ) := by
  classical
  have hnum : Measurable fun x : Fin T → ℝ => ∑ t ∈ tarRegimeIndices x (radA 0) 1 1, x t :=
    measurable_radRegimeSum (fun t => fun x => x t) fun t => measurable_pi_apply t
  have hden : Measurable fun x : Fin T → ℝ => (tarRegimeCount x (radA 0) 1 1 : ℝ) := by
    have heq : (fun x : Fin T → ℝ => (tarRegimeCount x (radA 0) 1 1 : ℝ))
        = fun x : Fin T → ℝ => ∑ t ∈ tarRegimeIndices x (radA 0) 1 1, (1 : ℝ) := by
      funext x
      simp [tarRegimeCount]
    rw [heq]
    exact measurable_radRegimeSum (fun _ => fun _ => (1 : ℝ)) fun _ => measurable_const
  exact hnum.div hden

/-- On the regime the single regressor is `≡ 1`, so the residual sum of squares depends on
`(γ₀, γ)` only through `γ₀ + γ_0`. -/
private lemma tarLSResidualSS_rad {T : ℕ} (x : Fin T → ℝ) (γ0 : ℝ) (γ : Fin 1 → ℝ) :
    tarLSResidualSS x (radA 0) 1 γ0 γ
      = ∑ t ∈ tarRegimeIndices x (radA 0) 1 1, (x t - (γ0 + γ 0)) ^ 2 := by
  classical
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [tarRegimeIndices, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  have hx1 : ∀ h : (t : ℕ) - 1 - ((0 : Fin 1) : ℕ) < T,
      x ⟨(t : ℕ) - 1 - ((0 : Fin 1) : ℕ), h⟩ = 1 := by
    intro h
    have hmem := ht.2.choose_spec
    have hfin : (⟨(t : ℕ) - 1 - ((0 : Fin 1) : ℕ), h⟩ : Fin T)
        = ⟨(t : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ := by
      apply Fin.ext
      simp
    rw [hfin]
    simpa [radA] using hmem
  rw [Fin.sum_univ_one, hx1]
  ring

/-- The sample mean minimizes the sum of squared deviations. -/
private lemma sum_sq_sub_mean_le {T : ℕ} (R : Finset (Fin T)) (x : Fin T → ℝ) (u : ℝ) :
    ∑ t ∈ R, (x t - (∑ s ∈ R, x s) / (R.card : ℝ)) ^ 2 ≤ ∑ t ∈ R, (x t - u) ^ 2 := by
  rcases Nat.eq_zero_or_pos R.card with hc | hc
  · rw [Finset.card_eq_zero] at hc
    subst hc
    simp
  · have hn : (0 : ℝ) < (R.card : ℝ) := by exact_mod_cast hc
    set m : ℝ := (∑ s ∈ R, x s) / (R.card : ℝ) with hm
    have hsum : ∑ s ∈ R, x s = (R.card : ℝ) * m := by
      rw [hm]; field_simp
    have hzero : ∑ t ∈ R, (x t - m) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hsum, nsmul_eq_mul]
      ring
    have hexp : ∀ t : Fin T, (x t - u) ^ 2
        = (x t - m) ^ 2 + 2 * (m - u) * (x t - m) + (m - u) ^ 2 := fun t => by ring
    have hrhs : ∑ t ∈ R, (x t - u) ^ 2
        = (∑ t ∈ R, (x t - m) ^ 2) + (R.card : ℝ) * (m - u) ^ 2 := by
      simp_rw [hexp]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, hzero]
      ring
    rw [hrhs]
    nlinarith [sq_nonneg (m - u)]

private lemma radMean_isLS {T : ℕ} (x : Fin T → ℝ) (γ0 : ℝ) (γ : Fin 1 → ℝ) :
    tarLSResidualSS x (radA 0) 1 (radMean x) (fun _ : Fin 1 => (0 : ℝ))
      ≤ tarLSResidualSS x (radA 0) 1 γ0 γ := by
  rw [tarLSResidualSS_rad, tarLSResidualSS_rad]
  simpa [radMean, tarRegimeCount] using
    sum_sq_sub_mean_le (tarRegimeIndices x (radA 0) 1 1) x (γ0 + γ 0)

/-- The regime-`0` least-squares intercept sequence of the witness. -/
private noncomputable def radBhat0 (T : ℕ) (ω : ℤ → ℝ) : ℝ :=
  radMean (fun t : Fin T => radCoord (((t : ℕ) : ℤ) + 1) ω)

private lemma radBhat0_measurable (T : ℕ) : Measurable (radBhat0 T) :=
  (measurable_radMean T).comp
    (measurable_pi_lambda _ fun t => radCoord_measurable (((t : ℕ) : ℤ) + 1))

/-- **The eq. (4.8) statement REPAIRED by wave `ts/s12b-model-repairs` is STILL FALSE.**

Every repaired hypothesis is supplied: `W` is pinned to `tarRegimeDesignCov` (and equals
`1`, positive definite), `hLS` is *joint* least-squares minimality over `(β₀, β)`, and the
regime carries mass `1/2 > 0`.  What survives is the **centering** defect: the fit has an
intercept, so what the slope sees is the regime-conditional *variance* of the regressor,
which here is `0`, while `tarRegimeDesignCov` reports the *second moment* `1`.  The slope
is therefore not identified and may legitimately be taken to be the truth `0`, making the
scaled statistic identically `0` — characteristic function `1` — against the claimed
`exp(−1/2)`. -/
private theorem tarLS_clt_debt_centering_false
    (H : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {k P : ℕ}
      {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ} {σ : Fin k → ℝ} {A : Fin k → Set ℝ}
      {d : ℕ} {X ε : ℤ → Ω → ℝ},
      IsTAR b0 b σ A d X ε μ → IsStrictlyStationary X μ → (∀ t, MemLp (X t) 2 μ) →
      ∀ (i : Fin k) (W : Matrix (Fin P) (Fin P) ℝ), W = tarRegimeDesignCov (A i) d X μ →
      W.PosDef → 0 < (μ {ω | X (-(d : ℤ)) ω ∈ A i}).toReal →
      ∀ (bhat0 : (T : ℕ) → Ω → ℝ) (bhat : (T : ℕ) → Ω → Fin P → ℝ),
      (∀ T, Measurable (bhat0 T)) → (∀ T, Measurable (bhat T)) →
      (∀ (T : ℕ) (ω : Ω), ∀ γ0 : ℝ, ∀ γ : Fin P → ℝ,
        tarLSResidualSS (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d
            (bhat0 T ω) (bhat T ω)
          ≤ tarLSResidualSS (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d γ0 γ) →
      ∀ (c : Fin P → ℝ) (u : ℝ),
      Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
          Real.sqrt (tarRegimeCount (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d P) *
            ∑ j, c j * (bhat T ω j - b i j)) u)
        atTop
        (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
          (σ i ^ 2 * (c ⬝ᵥ (W⁻¹ *ᵥ c))))) u))) :
    False := by
  classical
  have hmass : 0 < (radMeasure {ω : ℤ → ℝ | radCoord (-((1 : ℕ) : ℤ)) ω ∈ radA 0}).toReal := by
    rw [rad_regime_set, rad_mass_eq]
    norm_num
  have key := H rad_isTAR rad_strictlyStationary rad_memLp 0
    (1 : Matrix (Fin 1) (Fin 1) ℝ) rad_designCov.symm Matrix.PosDef.one hmass
    radBhat0 (fun _ _ _ => 0) radBhat0_measurable (fun _ => measurable_const)
    (fun T ω γ0 γ => radMean_isLS _ γ0 γ) (fun _ => 1) 1
  -- the statistic is identically `0`
  simp only [sub_self, mul_zero, Finset.sum_const_zero] at key
  have hmapconst : radMeasure.map (fun _ : ℤ → ℝ => (0 : ℝ)) = Measure.dirac 0 := by
    rw [Measure.map_const]
    simp
  rw [hmapconst] at key
  have hone : charFun (Measure.dirac (0 : ℝ)) (1 : ℝ) = 1 := by
    rw [charFun_dirac]
    simp
  simp only [hone] at key
  have hvar : ((fun _ : Fin 2 => (1 : ℝ)) 0) ^ 2 *
      ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ (fun _ => 1))) = 1 := by
    rw [inv_one]
    simp [Matrix.one_mulVec, dotProduct]
  rw [hvar] at key
  have hlim : charFun (gaussianReal 0 (Real.toNNReal 1)) (1 : ℝ) = 1 :=
    tendsto_nhds_unique tendsto_const_nhds key |>.symm
  rw [charFun_gaussianReal] at hlim
  norm_num at hlim
  rw [show ((-(1 / 2) : ℂ)) = (((-(1 / 2) : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp] at hlim
  have hR : Real.exp (-(1 / 2)) = 1 := by exact_mod_cast hlim
  have hlt : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-! ### The regime-wise normal equations and the centered identity (deterministic)

The first bullet of the removed eq. (4.8) debt's residue list — "the per-regime **normal
equations** … this algebraic step is what makes `tarRegimeDesignCovCentered` — and not
`tarRegimeDesignCov` — the matrix in the limit … it is a finite-sample identity and needs
no probability" — is discharged here, in the form the CLT proof consumes.

`tarLS_normalEquations` differentiates the joint minimality `hLS` along the two families
of directions (intercept, and each slope coordinate), and
`tarLS_centered_normalEquation` eliminates the intercept between them, producing

  `Ŝ_i (β̂ − γ) = Σ_{t ∈ R_i} (z_t − z̄_i)(x_t − γ₀ − ⟨γ, z_t⟩)`   (one row at a time)

for an **arbitrary** reference point `(γ₀, γ)`, with `Ŝ_i` the *centered* sample design
matrix `Σ_{t ∈ R_i}(z_t − z̄_i)(z_t − z̄_i)ᵀ`. Instantiated at the truth `(b0 i, b i)` the
right-hand side becomes `Σ_{t ∈ R_i}(z_t − z̄_i)·σ_i ε_t`, the martingale-difference sum of
the CLT; and the matrix on the left is centered whatever the reference point is. That is
the precise sense in which the third repair of eq. (4.8) (defect 4 / finding 24) is
*forced by the finite-sample algebra* and not chosen: the uncentered
`tarRegimeDesignCov` never appears in the identity at all.

Everything here is deterministic — no measure, no model, not even a regime assumption:
the statements hold for an arbitrary window `x`, an arbitrary index set of the shape
`tarRegimeIndices`, and an arbitrary joint minimizer. The empty-regime case is included
(both sides are `0`; `sum_tarRegressor_sub_mean` is proved with no cardinality
hypothesis, the junk `card⁻¹ = 0` doing the work). -/

section LSNormalEquations

variable {T P : ℕ}

/-- The regime-`i` **regressor vector** `z_t = (x_{t−1−j})_{j<P}`. -/
noncomputable def tarRegressor (x : Fin T → ℝ) (P : ℕ) (t : Fin T) (j : Fin P) : ℝ :=
  x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩

lemma tarLSResidualSS_eq (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ) (β0 : ℝ) (β : Fin P → ℝ) :
    tarLSResidualSS x A d β0 β
      = ∑ t ∈ tarRegimeIndices x A d P,
          (x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j) ^ 2 := rfl

/-- A quadratic that is minimized at `0` has vanishing linear coefficient. -/
private lemma eq_zero_of_quadratic_min {A B : ℝ} (h : ∀ s : ℝ, 2 * s * A ≤ s ^ 2 * B) :
    A = 0 := by
  by_contra hA
  have hA2 : 0 < A ^ 2 := by positivity
  set c := min 1 (1 / (|B| + 1)) with hc
  have hB1 : (0 : ℝ) < |B| + 1 := by positivity
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  have h1 := h (c * A)
  have hpos : 0 < c * A ^ 2 := by positivity
  have hkey : 2 * (c * A ^ 2) ≤ (c * B) * (c * A ^ 2) := by nlinarith [h1]
  have h2 : 2 ≤ c * B := le_of_mul_le_mul_right (by linarith [hkey]) hpos
  have h3 : c * B < 2 := by
    have hle : c ≤ 1 / (|B| + 1) := min_le_right _ _
    have habs : c * B ≤ c * |B| := by nlinarith [le_abs_self B, hc0.le]
    have : c * |B| ≤ 1 := by
      calc c * |B| ≤ (1 / (|B| + 1)) * |B| := by nlinarith [abs_nonneg B]
        _ ≤ 1 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_one hB1]
            linarith
    linarith
  linarith

/-- The first-order condition of a least-squares fit along one direction. -/
private lemma sum_mul_eq_zero_of_min {ι : Type*} (s : Finset ι) (r v : ι → ℝ)
    (h : ∀ c : ℝ, ∑ t ∈ s, (r t) ^ 2 ≤ ∑ t ∈ s, (r t - c * v t) ^ 2) :
    ∑ t ∈ s, r t * v t = 0 := by
  refine eq_zero_of_quadratic_min (B := ∑ t ∈ s, (v t) ^ 2) fun c => ?_
  have hexp : ∑ t ∈ s, (r t - c * v t) ^ 2
      = (∑ t ∈ s, (r t) ^ 2) - 2 * c * (∑ t ∈ s, r t * v t)
        + c ^ 2 * ∑ t ∈ s, (v t) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have := h c
  rw [hexp] at this
  linarith

/-- **The regime-wise normal equations.** -/
theorem tarLS_normalEquations (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    {β0 : ℝ} {β : Fin P → ℝ}
    (hLS : ∀ (γ0 : ℝ) (γ : Fin P → ℝ),
      tarLSResidualSS x A d β0 β ≤ tarLSResidualSS x A d γ0 γ) :
    (∑ t ∈ tarRegimeIndices x A d P,
        (x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j) = 0) ∧
    (∀ l : Fin P, ∑ t ∈ tarRegimeIndices x A d P,
        (x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j) * tarRegressor x P t l = 0) := by
  classical
  set R := tarRegimeIndices x A d P with hR
  set r : Fin T → ℝ := fun t => x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j with hr
  constructor
  · have h1 : ∑ t ∈ R, r t * (1 : ℝ) = 0 := by
      refine sum_mul_eq_zero_of_min R r (fun _ => 1) fun c => ?_
      have hlhs : ∑ t ∈ R, (r t) ^ 2 = tarLSResidualSS x A d β0 β := rfl
      have hrhs : ∑ t ∈ R, (r t - c * 1) ^ 2 = tarLSResidualSS x A d (β0 + c) β := by
        rw [tarLSResidualSS_eq]
        exact Finset.sum_congr rfl fun t _ => by rw [hr]; ring_nf
      rw [hlhs, hrhs]
      exact hLS (β0 + c) β
    simpa using h1
  · intro l
    refine sum_mul_eq_zero_of_min R r (fun t => tarRegressor x P t l) fun c => ?_
    have hlhs : ∑ t ∈ R, (r t) ^ 2 = tarLSResidualSS x A d β0 β := rfl
    have hrhs : ∑ t ∈ R, (r t - c * tarRegressor x P t l) ^ 2
        = tarLSResidualSS x A d β0 (fun j => β j + if j = l then c else 0) := by
      rw [tarLSResidualSS_eq]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hstep : ∀ j ∈ (Finset.univ : Finset (Fin P)),
          (β j + if j = l then c else 0) * tarRegressor x P t j
            = β j * tarRegressor x P t j
              + (if j = l then c else 0) * tarRegressor x P t j := fun j _ => by ring
      have hsum : ∑ j : Fin P, (β j + if j = l then c else 0) * tarRegressor x P t j
          = (∑ j : Fin P, β j * tarRegressor x P t j) + c * tarRegressor x P t l := by
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single l]
        · rw [if_pos rfl]
        · intro j _ hj; rw [if_neg hj, zero_mul]
        · intro h; exact absurd (Finset.mem_univ l) h
      rw [hsum, hr]
      ring_nf
    rw [hlhs, hrhs]
    exact hLS β0 _

/-- The regime-`i` sample mean of the regressor vector. -/
noncomputable def tarRegressorMean (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) (j : Fin P) : ℝ :=
  ((tarRegimeIndices x A d P).card : ℝ)⁻¹ *
    ∑ t ∈ tarRegimeIndices x A d P, tarRegressor x P t j

/-- The regime-`i` **centered sample design matrix** `Ŝ`. -/
noncomputable def tarSampleDesignCentered (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) :
    Matrix (Fin P) (Fin P) ℝ :=
  Matrix.of fun l j => ∑ t ∈ tarRegimeIndices x A d P,
    (tarRegressor x P t l - tarRegressorMean x A d P l) *
      (tarRegressor x P t j - tarRegressorMean x A d P j)

/-- Centered regressors sum to zero over the regime. -/
lemma sum_tarRegressor_sub_mean (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) (l : Fin P) :
    ∑ t ∈ tarRegimeIndices x A d P,
      (tarRegressor x P t l - tarRegressorMean x A d P l) = 0 := by
  classical
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, tarRegressorMean]
  rcases Nat.eq_zero_or_pos (tarRegimeIndices x A d P).card with hcard | hcard
  · rw [hcard]
    simp [Finset.card_eq_zero.1 hcard]
  · have hne : ((tarRegimeIndices x A d P).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hcard.ne'
    field_simp
    ring

/-- **The centered normal equation** (the finite-sample identity that forces the
*centered* design covariance into eq. (4.8)). -/
theorem tarLS_centered_normalEquation (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    {β0 : ℝ} {β : Fin P → ℝ}
    (hLS : ∀ (γ0 : ℝ) (γ : Fin P → ℝ),
      tarLSResidualSS x A d β0 β ≤ tarLSResidualSS x A d γ0 γ)
    (γ0 : ℝ) (γ : Fin P → ℝ) (l : Fin P) :
    ∑ j : Fin P, tarSampleDesignCentered x A d P l j * (β j - γ j)
      = ∑ t ∈ tarRegimeIndices x A d P,
          (tarRegressor x P t l - tarRegressorMean x A d P l) *
            (x t - γ0 - ∑ j : Fin P, γ j * tarRegressor x P t j) := by
  classical
  obtain ⟨h0, h1⟩ := tarLS_normalEquations x A d hLS
  have hsum0 := sum_tarRegressor_sub_mean x A d P l
  have hcent : ∑ t ∈ tarRegimeIndices x A d P,
      (tarRegressor x P t l - tarRegressorMean x A d P l) *
        (x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j) = 0 := by
    have hexp : ∀ t ∈ tarRegimeIndices x A d P,
        (tarRegressor x P t l - tarRegressorMean x A d P l) *
          (x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j)
        = (x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j) * tarRegressor x P t l
          - tarRegressorMean x A d P l *
              (x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j) := fun t _ => by ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.mul_sum, h1 l, h0]
    ring
  have hcol : ∀ j : Fin P, ∑ t ∈ tarRegimeIndices x A d P,
      (tarRegressor x P t l - tarRegressorMean x A d P l) * tarRegressor x P t j
      = tarSampleDesignCentered x A d P l j := by
    intro j
    rw [tarSampleDesignCentered]
    simp only [Matrix.of_apply]
    have hexp : ∀ t ∈ tarRegimeIndices x A d P,
        (tarRegressor x P t l - tarRegressorMean x A d P l) *
          (tarRegressor x P t j - tarRegressorMean x A d P j)
        = (tarRegressor x P t l - tarRegressorMean x A d P l) * tarRegressor x P t j
          - tarRegressorMean x A d P j *
              (tarRegressor x P t l - tarRegressorMean x A d P l) := fun t _ => by ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum0]
    ring
  have hRHS : ∑ t ∈ tarRegimeIndices x A d P,
        (tarRegressor x P t l - tarRegressorMean x A d P l) *
          (x t - γ0 - ∑ j : Fin P, γ j * tarRegressor x P t j)
      = ∑ t ∈ tarRegimeIndices x A d P,
          ((tarRegressor x P t l - tarRegressorMean x A d P l) *
              (x t - β0 - ∑ j : Fin P, β j * tarRegressor x P t j)
            + (β0 - γ0) * (tarRegressor x P t l - tarRegressorMean x A d P l)
            + ∑ j : Fin P, (β j - γ j) *
                ((tarRegressor x P t l - tarRegressorMean x A d P l)
                  * tarRegressor x P t j)) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    have hs : ∑ j : Fin P, (β j - γ j) *
          ((tarRegressor x P t l - tarRegressorMean x A d P l) * tarRegressor x P t j)
        = (tarRegressor x P t l - tarRegressorMean x A d P l) *
            ((∑ j : Fin P, β j * tarRegressor x P t j)
              - ∑ j : Fin P, γ j * tarRegressor x P t j) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    ring
  have hswap : ∑ t ∈ tarRegimeIndices x A d P, ∑ j : Fin P, (β j - γ j) *
        ((tarRegressor x P t l - tarRegressorMean x A d P l) * tarRegressor x P t j)
      = ∑ j : Fin P, tarSampleDesignCentered x A d P l j * (β j - γ j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, hcol j]
    ring
  have hmid : ∑ t ∈ tarRegimeIndices x A d P,
      (β0 - γ0) * (tarRegressor x P t l - tarRegressorMean x A d P l) = 0 := by
    rw [← Finset.mul_sum, hsum0, mul_zero]
  rw [hRHS, Finset.sum_add_distrib, Finset.sum_add_distrib, hcent, hmid, hswap]
  ring

end LSNormalEquations

end StatLean.TimeSeries
