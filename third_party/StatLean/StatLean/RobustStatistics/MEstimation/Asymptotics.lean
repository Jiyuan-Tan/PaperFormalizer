module
public import StatLean.RobustStatistics.MEstimation.MLocationFunctional
public import StatLean.AsymptoticStatistics.Consistency.OneDimMonotoneConsistency
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Asymptotics of location M-estimators — by reuse of StatLean Z-estimation theory

Consistency and asymptotic normality of monotone location M-estimators (`MMY §10.2–10.3`,
Theorems 10.5 and 10.7): under i.i.d. sampling from `P`, a near-root sequence `θ̂ₙ` of the
empirical M-equation tends in probability to the population root `θ₀`, and

$$\sqrt n\,(\hat\theta_n - \theta_0) \Rightarrow
  N\!\left(0,\ \frac{E_P\,\psi(x-\theta_0)^2}{\big(E_P\,\psi'(x-\theta_0)\big)^2}\right)$$

(`MMY` eq. (2.24)–(2.25)). Per the charter, this file *reuses* the general machinery of
`StatLean/AsymptoticStatistics` rather than re-proving it:

* consistency instantiates `AsymptoticStatistics.Consistency.oneDim_monotone_zEstimator_consistent`
  (vdV Lemma 5.10) with the empirical score `θ ↦ -n⁻¹ ∑ ψ(Xᵢ - θ)` and the LLN
  `iid_lln_in_prob_seq`;
* Huber asymptotic normality instantiates the Lipschitz-score route
  `AsymptoticStatistics.EmpiricalProcess.zEstimator_asymptotic_normality` (vdV Theorem
  5.21), which needs no differentiability of `ψ` — exactly right for the kinked Huber
  score, whose population score is differentiable at `θ₀` once `P` has no atoms at the
  clipping knots.

**Hypothesis discipline.** The sign conditions on the population score encode the
identification of `θ₀` (`MMY` (10.7)); the near-root conditions describe how the
estimator sequence was constructed. Both are genuine external inputs. The LLN, the
CLT for the empirical score, and the differentiability of the population score at `θ₀`
are *derived internally* from the i.i.d. inputs.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.3.2 (eq.
(2.22)–(2.25)), §10.2 (Thm 10.5), §10.3 (Thm 10.7). Cross-reference: van der Vaart,
*Asymptotic Statistics*, Lemma 5.10 and Theorem 5.21 (`vdV §5.2–5.3`).

**Bibliographic comments.** Consistency and asymptotic normality of M-estimators under
minimal conditions are P. J. Huber, "The behavior of maximum likelihood estimates under
nonstandard conditions," *Proc. Fifth Berkeley Symp. Math. Statist. Probab.*, Vol. I, Univ.
California Press, 1967, pp. 221–233 (after Huber 1964); the modern empirical-process
treatment this file actually reuses is ch. 5 of van der Vaart, *Asymptotic Statistics*,
Cambridge Univ. Press, 1998.
-/

open MeasureTheory Filter Topology AsymptoticStatistics

namespace StatLean.RobustStatistics

/-- **Consistency of monotone location M-estimators** (`MMY` Theorem 10.5; vdV Lemma
5.10): under i.i.d. sampling from `P`, any near-root sequence of the empirical M-equation
for a bounded monotone continuous score tends in probability to the population root `θ₀`
identified by the sign change of the population score. -/
theorem mLocation_consistent
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {P : Measure ℝ} [IsProbabilityMeasure P] {ψ : ℝ → ℝ} {θ₀ : ℝ}
    {X : ℕ → Ξ → ℝ} {θhat : ℕ → Ξ → ℝ}
    -- USER-INPUT: i.i.d. data with common law P; MMY §10.2
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- USER-INPUT: continuous monotone bounded score (ψ-function shape); MMY Def 2.2, §2.3.1
    (hψc : Continuous ψ) (hψm : Monotone ψ) (hψb : ∃ C, ∀ u, |ψ u| ≤ C)
    -- USER-INPUT: θ₀ is identified — the population score changes sign strictly at θ₀;
    -- MMY Thm 10.5 / eq. (10.7)
    (hsign_lt : ∀ θ < θ₀, 0 < mLocationScore ψ P θ)
    (hsign_gt : ∀ θ, θ₀ < θ → mLocationScore ψ P θ < 0)
    -- USER-INPUT: θ̂ₙ nearly solves the empirical M-equation (in probability); MMY (10.1)
    (hnear : TendstoInMeasure μ
      (fun (n : ℕ) ξ => (n : ℝ)⁻¹ * ∑ i : Fin n, ψ (X i ξ - θhat n ξ)) atTop
      (fun _ => (0 : ℝ))) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => μ {ξ | ε ≤ |θhat n ξ - θ₀|}) atTop (𝓝 0) := by
  classical
  have hψmeas : Measurable ψ := hψc.measurable
  obtain ⟨C, hC⟩ := hψb
  -- The *negated* empirical score. `ψ` is nondecreasing and `θ ↦ x − θ` is antitone, so
  -- `θ ↦ n⁻¹∑ψ(Xᵢ − θ)` is nonincreasing; negating it produces the nondecreasing random
  -- criterion required by vdV Lemma 5.10, and flips the sign conditions into place.
  refine Consistency.oneDim_monotone_zEstimator_consistent_univ
    (Ψn := fun n ξ θ => -((n : ℝ)⁻¹ * ∑ i : Fin n, ψ (X i ξ - θ)))
    (Ψ := fun θ => -(mLocationScore ψ P θ)) ?_ ?_ ?_ ?_ ?_
  · -- Monotonicity in `θ` of the negated empirical score.
    intro n ξ a b hab
    simp only [neg_le_neg_iff]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hψm (by linarith))
      (by positivity)
  · -- Pointwise convergence in probability: the i.i.d. weak law at the fixed `θ`.
    intro θ
    have hgm : Measurable fun x : ℝ => ψ (x - θ) := hψmeas.comp (measurable_id.sub_const θ)
    have hgi : Integrable (fun x : ℝ => ψ (x - θ)) P :=
      Integrable.mono' (integrable_const C) hgm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hC (x - θ))
    have hlln := iid_lln_in_prob_seq P (fun x : ℝ => ψ (x - θ)) hgm hgi μ X
      hX_meas hX_indep hX_id hX_law
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    refine (hlln ε hε).congr fun n => ?_
    congr 1
    ext ξ
    simp only [Set.mem_setOf_eq, EmpiricalProcess.empiricalAvg, mLocationScore]
    rw [show -((n : ℝ)⁻¹ * ∑ i : Fin n, ψ (X (i : ℕ) ξ - θ)) - -(∫ x, ψ (x - θ) ∂P)
        = -((n : ℝ)⁻¹ * ∑ i : Fin n, ψ (X (i : ℕ) ξ - θ) - ∫ x, ψ (x - θ) ∂P) from by ring,
      norm_neg]
  · -- Near-root condition: negate the hypothesis.
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    refine ((tendstoInMeasure_iff_norm.mp hnear) ε hε).congr fun n => ?_
    congr 1
    ext ξ
    simp only [Set.mem_setOf_eq, sub_zero, norm_neg]
  · exact fun θ hθ => neg_lt_zero.mpr (hsign_lt θ hθ)
  · exact fun θ hθ => neg_pos.mpr (hsign_gt θ hθ)

/-- **Consistency of the Huber location estimator** (`MMY §2.3.2` + Thm 10.5): the Huber
score is continuous, monotone and bounded, so any near-root sequence tends to the
population Huber root identified by the sign conditions. -/
theorem huberLocation_consistent
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) {θ₀ : ℝ}
    {X : ℕ → Ξ → ℝ} {θhat : ℕ → Ξ → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- USER-INPUT: identification of θ₀; MMY Thm 10.5 / eq. (10.7)
    (hsign_lt : ∀ θ < θ₀, 0 < mLocationScore (huberPsi c) P θ)
    (hsign_gt : ∀ θ, θ₀ < θ → mLocationScore (huberPsi c) P θ < 0)
    -- USER-INPUT: near-root sequence; MMY (10.1)
    (hnear : TendstoInMeasure μ
      (fun (n : ℕ) ξ => (n : ℝ)⁻¹ * ∑ i : Fin n, huberPsi c (X i ξ - θhat n ξ)) atTop
      (fun _ => (0 : ℝ))) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => μ {ξ | ε ≤ |θhat n ξ - θ₀|}) atTop (𝓝 0) :=
  mLocation_consistent hX_meas hX_indep hX_id hX_law (huberPsi_continuous c)
    (huberPsi_monotone c) ⟨c, abs_huberPsi_le hc.le⟩ hsign_lt hsign_gt hnear

/-- **The asymptotic variance of the Huber location estimator** (`MMY` eq. (2.25)):
`v = E_P ψ_c(x-θ₀)² / P(|x-θ₀| < c)²`. -/
noncomputable def huberAsymptoticVariance (P : Measure ℝ) (c θ₀ : ℝ) : ℝ :=
  (∫ x, huberPsi c (x - θ₀) ^ 2 ∂P) / (P.real {x | |x - θ₀| < c}) ^ 2

/-- Above the upper knot the Huber score is the constant `c`. (Branch formula for the
derivative computation below; `Huber.lean` only exports the central-region formula.) -/
private theorem huberPsi_of_clip_le {c u : ℝ} (hc : 0 ≤ c) (h : c ≤ u) : huberPsi c u = c := by
  unfold huberPsi
  rw [min_eq_left h, max_eq_right (by linarith)]

/-- Below the lower knot the Huber score is the constant `-c`. -/
private theorem huberPsi_of_le_neg_clip {c u : ℝ} (hc : 0 ≤ c) (h : u ≤ -c) :
    huberPsi c u = -c := by
  unfold huberPsi
  rw [min_eq_right (by linarith), max_eq_left h]

/-- **Off the two clipping knots `x = θ₀ ± c` the map `θ ↦ ψ_c(x − θ)` is differentiable at
`θ₀`.** The derivative is `-1` on the central region `|x − θ₀| < c` and `0` outside it —
exactly the indicator whose `P`-integral is the `B = -P(|x − θ₀| < c)` of `MMY` Thm 10.7.
No two-sided gluing is needed: each of the three regions is *open* in `θ` around `θ₀`, so
the branch formula holds on a whole neighbourhood and `congr_of_eventuallyEq` applies. -/
private theorem hasDerivAt_huberPsi_sub {c θ₀ x : ℝ} (hc : 0 < c) (hx : |x - θ₀| ≠ c) :
    HasDerivAt (fun θ => huberPsi c (x - θ))
      (Set.indicator {y : ℝ | |y - θ₀| < c} (fun _ => (-1 : ℝ)) x) θ₀ := by
  rcases lt_or_gt_of_ne hx with hin | hout
  · -- Central region: `ψ_c(x − θ) = x − θ` on the open set `{θ | |x − θ| < c}`.
    rw [Set.indicator_of_mem (show x ∈ {y : ℝ | |y - θ₀| < c} from hin)]
    have h1 : HasDerivAt (fun θ : ℝ => x - θ) (-1 : ℝ) θ₀ := by
      simpa using (hasDerivAt_id θ₀).const_sub x
    refine h1.congr_of_eventuallyEq ?_
    have hopen : IsOpen {θ : ℝ | |x - θ| < c} :=
      isOpen_lt (continuous_const.sub continuous_id).abs continuous_const
    filter_upwards [hopen.mem_nhds (show |x - θ₀| < c from hin)] with θ hθ
    exact huberPsi_of_abs_le hc.le (le_of_lt hθ)
  · -- Outside the central region the score is locally constant (`c` or `-c`).
    rw [Set.indicator_of_notMem (by simpa using hout.le)]
    rcases lt_abs.mp hout with hA | hB
    · refine (hasDerivAt_const θ₀ c).congr_of_eventuallyEq ?_
      have hopen : IsOpen {θ : ℝ | c < x - θ} :=
        isOpen_lt continuous_const (continuous_const.sub continuous_id)
      filter_upwards [hopen.mem_nhds (show c < x - θ₀ from hA)] with θ hθ
      exact huberPsi_of_clip_le hc.le (le_of_lt hθ)
    · refine (hasDerivAt_const θ₀ (-c)).congr_of_eventuallyEq ?_
      have hopen : IsOpen {θ : ℝ | x - θ < -c} :=
        isOpen_lt (continuous_const.sub continuous_id) continuous_const
      filter_upwards [hopen.mem_nhds (show x - θ₀ < -c from by linarith)] with θ hθ
      exact huberPsi_of_le_neg_clip hc.le (le_of_lt hθ)

/-- Private, earlier-placed copy of `hasDerivAt_mLocationScore_huber` (below): the
normality theorem needs the population score's derivative *before* the frozen statement's
position in the file. The frozen theorem is this lemma verbatim. -/
private theorem hasDerivAt_mLocationScore_huber_aux
    {P : Measure ℝ} [IsProbabilityMeasure P] {c θ₀ : ℝ} (hc : 0 < c)
    (h_atom_add : P {θ₀ + c} = 0) (h_atom_sub : P {θ₀ - c} = 0) :
    HasDerivAt (mLocationScore (huberPsi c) P) (-(P.real {x | |x - θ₀| < c})) θ₀ := by
  classical
  set S : Set ℝ := {x : ℝ | |x - θ₀| < c} with hS_def
  have hS : MeasurableSet S :=
    measurableSet_lt (measurable_id.sub_const θ₀).abs measurable_const
  have hF'meas : Measurable (Set.indicator S (fun _ => (-1 : ℝ))) :=
    measurable_const.indicator hS
  -- The knot set `{x | |x − θ₀| = c} = {θ₀+c, θ₀−c}` is `P`-null: this is precisely where
  -- the atom hypotheses enter.
  have hnull : P {x : ℝ | |x - θ₀| = c} = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h_atom_add h_atom_sub)
    simp only [Set.mem_setOf_eq] at hx
    have : x = θ₀ + c ∨ x = θ₀ - c := by
      rcases (abs_eq hc.le).mp hx with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases this with h | h <;> simp [h]
  have hae : ∀ᵐ x ∂P, |x - θ₀| ≠ c := by
    rw [MeasureTheory.ae_iff]
    simpa using hnull
  have h_diff : ∀ᵐ x ∂P,
      HasDerivAt (fun θ => huberPsi c (x - θ)) (Set.indicator S (fun _ => (-1 : ℝ)) x) θ₀ := by
    filter_upwards [hae] with x hx using hasDerivAt_huberPsi_sub hc hx
  -- The parameter-Lipschitz domination: `θ ↦ ψ_c(x − θ)` is `1`-Lipschitz, uniformly in `x`,
  -- so the constant `1` is an (integrable) Lipschitz bound.
  have h_lip : ∀ᵐ x ∂P, LipschitzOnWith (Real.nnabs ((fun _ : ℝ => (1 : ℝ)) x))
      (fun θ => huberPsi c (x - θ)) Set.univ := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h1 : LipschitzWith 1 (fun θ : ℝ => huberPsi c (x - θ)) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have h := (huberPsi_lipschitz c).dist_le_mul (x - a) (x - b)
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h ⊢
      calc |huberPsi c (x - a) - huberPsi c (x - b)| ≤ |x - a - (x - b)| := h
        _ = |a - b| := by rw [show x - a - (x - b) = -(a - b) from by ring, abs_neg]
    simpa [show Real.nnabs (1 : ℝ) = 1 from by ext; simp] using
      (lipschitzOnWith_univ (K := 1) (f := fun θ : ℝ => huberPsi c (x - θ))).mpr h1
  have hcont : Continuous fun x : ℝ => huberPsi c (x - θ₀) :=
    (huberPsi_continuous c).comp (continuous_id.sub continuous_const)
  have hF_meas : ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (fun x : ℝ => huberPsi c (x - θ)) P :=
    Filter.Eventually.of_forall fun θ =>
      ((huberPsi_continuous c).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hF_int : Integrable (fun x : ℝ => huberPsi c (x - θ₀)) P :=
    Integrable.mono' (integrable_const c) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_huberPsi_le hc.le (x - θ₀))
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun θ x => huberPsi c (x - θ)) (x₀ := θ₀) (s := Set.univ)
    (bound := fun _ : ℝ => (1 : ℝ)) (F' := Set.indicator S (fun _ => (-1 : ℝ)))
    Filter.univ_mem hF_meas hF_int hF'meas.aestronglyMeasurable h_lip
    (integrable_const 1) h_diff
  have hval : ∫ x, Set.indicator S (fun _ => (-1 : ℝ)) x ∂P = -(P.real S) := by
    rw [integral_indicator_const (-1 : ℝ) hS]
    simp
  rw [hval] at hderiv
  exact hderiv

/-! ### `ℝ ↔ EuclideanSpace ℝ (Fin 1)` packaging for the `k = 1` instantiation

The Z-estimation engine carries its parameter in `EuclideanSpace ℝ (Fin k)`; the location
model is `k = 1`. These private helpers are the coordinate dictionary. -/

/-- The `Fin 1` Euclidean packaging of a real parameter. -/
private noncomputable def packFin1 (t : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single (0 : Fin 1) t

@[simp] private theorem packFin1_apply (t : ℝ) : (packFin1 t) 0 = t := by
  simp [packFin1]

/-- In one dimension the Euclidean norm *is* the absolute value of the single coordinate. -/
private theorem norm_euclideanFin1 (y : EuclideanSpace ℝ (Fin 1)) : ‖y‖ = |y 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

private theorem continuous_packFin1 : Continuous packFin1 :=
  LipschitzWith.continuous (K := 1)
    (LipschitzWith.of_dist_le_mul fun a b => by
      simp [packFin1])

/-- The coordinate functional as an inner product against `packFin1 1` — the form in which
`multivariateGaussian_map_inner_eq_gaussianReal` identifies the one-dimensional marginal. -/
private theorem inner_packFin1_one (y : EuclideanSpace ℝ (Fin 1)) :
    inner ℝ (packFin1 1) y = y 0 := by
  have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) (0 : Fin 1) (1 : ℝ) y
  simpa [packFin1] using h

/-- The Huber estimating function packaged as the `k = 1` criterion family of the
Z-estimation engine: one coordinate, evaluated at the single parameter coordinate. -/
private noncomputable def huberPsiFin1 (c : ℝ) :
    EuclideanSpace ℝ (Fin 1) → Fin 1 → (ℝ → ℝ) :=
  fun θ _ x => huberPsi c (x - θ 0)

/-- **Asymptotic normality of the Huber location estimator** (`MMY` Theorem 10.7 with eq.
(2.24)–(2.25); via vdV Theorem 5.21, the Lipschitz-score route): a consistent near-root
sequence at rate `o_P(n^{-1/2})` satisfies
`√n (θ̂ₙ - θ₀) ⇒ N(0, E ψ_c²/(P(|x-θ₀|<c))²)`. The absence of atoms at the clipping
knots makes the population score differentiable at `θ₀` with derivative
`-P(|x-θ₀| < c)`; that Fréchet condition is derived internally, not assumed.

**Form of the estimator.** `θhat : ∀ n, (Fin n → ℝ) → ℝ` is a *statistic of the sample*:
it is applied to `(X₁ ξ, …, Xₙ ξ)`, so the estimator is a measurable function of the data.
This is exactly what `MMY` Theorem 10.7 asserts (`θ̂ₙ = θ̂ₙ(x₁,…,xₙ)`), and it is the form
required by the Z-estimation engine
`AsymptoticStatistics.EmpiricalProcess.zEstimator_asymptotic_normality`, whose estimator
argument is `θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k)` and which everywhere
uses the composite `fun ξ => θ_hat n (fun i : Fin n => X i.val ξ)`.

*Scope note (deliberate, not an oversight).* The more general statement carrying an
arbitrary `ξ`-indexed sequence `θhat : ℕ → Ξ → ℝ` — a sequence of statistics on the base
space that need not factor through `(X₁,…,Xₙ)` — is believed true, since the engine's proof
only ever uses the composite; but establishing it here would require generalizing the
engine's estimator argument through `zEstimator_asymptotic_normality`,
`zEstimator_linear_representation`, `infinite_dim_z_estimator`, `modifiedRandomFunction`
and their dependents (5 files, ~210 occurrences) in `StatLean/AsymptoticStatistics/`,
which is out of this wave's scope. No such factorization is derivable from the hypotheses,
so the general form is not obtainable from this one.

*Universe restriction.* `Ξ : Type` (not `Type*`) is inherited from the engine, which fixes
`{Ξ : Type}`; lifting it is part of the same out-of-scope generalization. -/
theorem huberLocation_asymptoticNormal
    {Ξ : Type} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) {θ₀ : ℝ}
    {X : ℕ → Ξ → ℝ} (θhat : ∀ n, (Fin n → ℝ) → ℝ)
    -- USER-INPUT: i.i.d. data with common law P; MMY §10.3
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- USER-INPUT: θ₀ solves the population Huber equation; MMY (2.22)
    (hroot : IsMLocationRoot (huberPsi c) P θ₀)
    -- USER-INPUT: no atoms at the clipping knots; MMY §10.3 (Example 10.4: F continuous)
    (h_atom_add : P {θ₀ + c} = 0) (h_atom_sub : P {θ₀ - c} = 0)
    -- USER-INPUT: nondegenerate central mass (B ≠ 0 in Thm 10.7)
    (hmass : 0 < P.real {x | |x - θ₀| < c})
    -- LEAN-ONLY: measurable estimator sequence, for the image laws to exist
    (hθhat_meas : ∀ n, Measurable (fun ξ => θhat n (fun i : Fin n => X i.val ξ)))
    -- USER-INPUT: consistency of the estimator sequence (from `huberLocation_consistent`);
    -- MMY Thm 10.5
    (h_consist : ∀ ε > (0 : ℝ), Tendsto
      (fun n => μ {ξ | ε ≤ |θhat n (fun i : Fin n => X i.val ξ) - θ₀|}) atTop (𝓝 0))
    -- USER-INPUT: the estimating equation is solved at rate o_P(n^{-1/2}); MMY (10.1),
    -- vdV Thm 5.21 estimating-equation condition
    (h_est_eq : TendstoInMeasure μ
      (fun (n : ℕ) ξ => Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        huberPsi c (X i ξ - θhat n (fun i : Fin n => X i.val ξ))))
      atTop (fun _ => (0 : ℝ))) :
    WeakConverges
      (fun n => μ.map (fun ξ =>
        Real.sqrt n * (θhat n (fun i : Fin n => X i.val ξ) - θ₀)))
      (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (huberAsymptoticVariance P c θ₀))) := by
  classical
  -- ==========================================================================
  -- (1) The `k = 1` data of the instantiation.
  -- ==========================================================================
  set A : ℝ := P.real {x | |x - θ₀| < c} with hA_def
  have hA0 : A ≠ 0 := ne_of_gt hmass
  have hcoord_sub : ∀ a b : ℝ, ‖packFin1 a - packFin1 b‖ = |a - b| := by
    intro a b; rw [norm_euclideanFin1]; simp
  -- The derivative matrix `V = [-A]` is nonsingular.
  have hVdet : IsUnit (Matrix.of (fun _ _ : Fin 1 => -A)).det := by
    rw [Matrix.det_fin_one]
    exact isUnit_iff_ne_zero.mpr (by simpa using hA0)
  -- Envelope: the packaged score is `1`-Lipschitz in the parameter, uniformly in `x`.
  have hLip : ∀ θ₁ : EuclideanSpace ℝ (Fin 1), ‖θ₁ - packFin1 θ₀‖ < 1 →
      ∀ θ₂ : EuclideanSpace ℝ (Fin 1), ‖θ₂ - packFin1 θ₀‖ < 1 →
      ∀ (j : Fin 1) (x : ℝ),
        |huberPsiFin1 c θ₁ j x - huberPsiFin1 c θ₂ j x| ≤ (fun _ : ℝ => (1 : ℝ)) x
          * ‖θ₁ - θ₂‖ := by
    intro θ₁ _ θ₂ _ j x
    have h := (huberPsi_lipschitz c).dist_le_mul (x - θ₁ 0) (x - θ₂ 0)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    calc |huberPsiFin1 c θ₁ j x - huberPsiFin1 c θ₂ j x|
        ≤ |x - θ₁ 0 - (x - θ₂ 0)| := h
      _ = ‖θ₁ - θ₂‖ := by
          rw [norm_euclideanFin1]
          have h0 : (θ₁ - θ₂) 0 = θ₁ 0 - θ₂ 0 := by simp
          rw [h0, show x - θ₁ 0 - (x - θ₂ 0) = -(θ₁ 0 - θ₂ 0) from by ring, abs_neg]
      _ = (fun _ : ℝ => (1 : ℝ)) x * ‖θ₁ - θ₂‖ := (one_mul _).symm
  have hψmeasE : ∀ (θ : EuclideanSpace ℝ (Fin 1)) (j : Fin 1),
      Measurable (huberPsiFin1 c θ j) := fun θ j =>
    (huberPsi_continuous c).measurable.comp (measurable_id.sub_const _)
  have hrootE : ∀ h : Fin 1, ∫ x, huberPsiFin1 c (packFin1 θ₀) h x ∂P = 0 := by
    intro h; simpa [huberPsiFin1] using! hroot
  -- ==========================================================================
  -- (2) The Fréchet condition, from the derivative of the population score.
  -- ==========================================================================
  have hderiv := hasDerivAt_mLocationScore_huber_aux (P := P) hc h_atom_add h_atom_sub
  have hfrechet : ∀ ε > 0, ∃ δ > 0, ∀ θ : EuclideanSpace ℝ (Fin 1),
      0 < ‖θ - packFin1 θ₀‖ → ‖θ - packFin1 θ₀‖ < δ →
      (⨆ h, ENNReal.ofReal
          |∫ x, huberPsiFin1 c θ h x ∂P - ∫ x, huberPsiFin1 c (packFin1 θ₀) h x ∂P
            - EmpiricalProcess.Vlin (Matrix.of (fun _ _ : Fin 1 => -A)) (θ - packFin1 θ₀) h|)
        ≤ ENNReal.ofReal (ε * ‖θ - packFin1 θ₀‖) := by
    intro ε hε
    have hlo := Asymptotics.isLittleO_iff.mp (hasDerivAt_iff_isLittleO.mp hderiv) hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hlo
    refine ⟨δ, hδpos, fun θ _ hθ => ?_⟩
    have hnθ : ‖θ - packFin1 θ₀‖ = |θ 0 - θ₀| := by rw [norm_euclideanFin1]; simp
    have hdist : dist (θ 0) θ₀ < δ := by rw [Real.dist_eq, ← hnθ]; exact hθ
    have hb := hδ hdist
    simp only [Real.norm_eq_abs, smul_eq_mul] at hb
    rw [iSup_unique]
    refine ENNReal.ofReal_le_ofReal ?_
    have hV1 : EmpiricalProcess.Vlin (Matrix.of (fun _ _ : Fin 1 => -A))
        (θ - packFin1 θ₀) default = -A * (θ 0 - θ₀) := by
      simp [EmpiricalProcess.Vlin, Matrix.mulVec, dotProduct]
    rw [hV1, hnθ]
    have hI1 : ∀ t : ℝ, ∫ x, huberPsiFin1 c (packFin1 t) default x ∂P
        = mLocationScore (huberPsi c) P t := by
      intro t; simp [huberPsiFin1, mLocationScore]
    have hIθ : ∫ x, huberPsiFin1 c θ (default : Fin 1) x ∂P
        = mLocationScore (huberPsi c) P (θ 0) := by
      simp [huberPsiFin1, mLocationScore]
    rw [hIθ, hI1 θ₀]
    calc |mLocationScore (huberPsi c) P (θ 0) - mLocationScore (huberPsi c) P θ₀
            - -A * (θ 0 - θ₀)|
        = |mLocationScore (huberPsi c) P (θ 0) - mLocationScore (huberPsi c) P θ₀
            - (θ 0 - θ₀) * -A| := by ring_nf
      _ ≤ ε * |θ 0 - θ₀| := hb
  -- ==========================================================================
  -- (3) `L²` of the packaged score (bounded by the clipping constant).
  -- ==========================================================================
  have hpsiVec_meas : Measurable (EmpiricalProcess.psiVec (huberPsiFin1 c) (packFin1 θ₀)) := by
    refine (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.comp ?_
    exact measurable_pi_lambda _ fun _ => hψmeasE _ _
  have hL2 : MemLp (EmpiricalProcess.psiVec (huberPsiFin1 c) (packFin1 θ₀)) 2 P := by
    refine MemLp.of_bound hpsiVec_meas.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_euclideanFin1]
    simpa [EmpiricalProcess.psiVec, huberPsiFin1] using abs_huberPsi_le hc.le (x - θ₀)
  -- ==========================================================================
  -- (4) Consistency and the estimating equation, reshaped to the engine's modes.
  -- ==========================================================================
  have hΘmeas : ∀ n, Measurable
      (fun ξ => packFin1 (θhat n (fun i : Fin n => X i.val ξ))) := fun n =>
    continuous_packFin1.measurable.comp (hθhat_meas n)
  have hψ_joint : ∀ (n : ℕ) (h : Fin 1), Measurable
      (fun p : Ξ × ℝ => huberPsiFin1 c
        (packFin1 (θhat n (fun i : Fin n => X i.val p.1))) h p.2) := by
    intro n h
    simpa [huberPsiFin1, packFin1] using!
      (huberPsi_continuous c).measurable.comp
        (measurable_snd.sub ((hθhat_meas n).comp measurable_fst))
  have hcons : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ξ | ε < ‖packFin1 (θhat n (fun i : Fin n => X i.val ξ))
        - packFin1 θ₀‖}) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h_consist ε hε)
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => measure_mono ?_)
    intro ξ hξ
    simp only [Set.mem_setOf_eq, hcoord_sub] at hξ ⊢
    exact hξ.le
  have hest : EmpiricalProcess.TendstoZeroInOuterProbSup μ (fun n ξ h =>
      Real.sqrt n * EmpiricalProcess.empiricalAvg
        (huberPsiFin1 c (packFin1 (θhat n (fun i : Fin n => X i.val ξ))) h) n
          (fun i : Fin n => X i.val ξ)) := by
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendstoInMeasure_iff_norm.mp h_est_eq) ε hε)
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
    refine le_trans (EmpiricalProcess.outerMeasureStar_mono μ ?_)
      (EmpiricalProcess.outerMeasureStar_le_measure μ _)
    intro ξ hξ
    obtain ⟨_h, hh⟩ := hξ
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, sub_zero,
      EmpiricalProcess.empiricalAvg, huberPsiFin1, packFin1_apply] at hh ⊢
    exact hh.le
  -- ==========================================================================
  -- (5) Run the engine and identify the one-dimensional limit law.
  -- ==========================================================================
  have hWC := EmpiricalProcess.zEstimator_asymptotic_normality P (huberPsiFin1 c)
    (packFin1 θ₀) (Matrix.of (fun _ _ : Fin 1 => -A)) hVdet 1 one_pos
    (fun _ => 1) (memLp_const 1) measurable_const hLip hψmeasE hrootE hfrechet hL2
    (fun n s => packFin1 (θhat n s)) μ X hX_meas hX_indep hX_id hX_law hΘmeas
    hψ_joint hcons hest
  set J : Matrix (Fin 1) (Fin 1) ℝ :=
    (Matrix.of (fun _ _ : Fin 1 => -A))⁻¹ * EmpiricalProcess.psiCov P (huberPsiFin1 c)
      (packFin1 θ₀) * Matrix.transpose ((Matrix.of (fun _ _ : Fin 1 => -A))⁻¹) with hJ_def
  have hJpsd : J.PosSemidef := by
    rw [hJ_def, ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (EmpiricalProcess.psiCov_posSemidef P (huberPsiFin1 c) (packFin1 θ₀)
      hL2).mul_mul_conjTranspose_same _
  have hJ00 : J 0 0 = huberAsymptoticVariance P c θ₀ := by
    have hinv : ∀ i j : Fin 1, (Matrix.of (fun _ _ : Fin 1 => -A))⁻¹ i j = (-A)⁻¹ := by
      intro i j
      fin_cases i
      fin_cases j
      simp
    have hcov : EmpiricalProcess.psiCov P (huberPsiFin1 c) (packFin1 θ₀) 0 0
        = ∫ x, huberPsi c (x - θ₀) ^ 2 ∂P := by
      simp [EmpiricalProcess.psiCov, huberPsiFin1, sq]
    rw [hJ_def, huberAsymptoticVariance, ← hA_def]
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply, hinv, hcov]
    field_simp
  -- Coordinate functional and its two pushforward identities.
  have hLcont : Continuous fun y : EuclideanSpace ℝ (Fin 1) => inner ℝ (packFin1 1) y :=
    continuous_const.inner continuous_id
  have hmapped := hWC.map hLcont hLcont.measurable
  have hRHS : (ProbabilityTheory.multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin 1)) J).map
        (fun y : EuclideanSpace ℝ (Fin 1) => inner ℝ (packFin1 1) y)
      = ProbabilityTheory.gaussianReal 0 (Real.toNNReal (huberAsymptoticVariance P c θ₀)) := by
    rw [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal (packFin1 1) hJpsd]
    congr 1
    have : (packFin1 1).ofLp ⬝ᵥ J.mulVec (packFin1 1).ofLp = J 0 0 := by
      simp [dotProduct, Matrix.mulVec, packFin1]
    rw [this, hJ00]
  have hLHS : ∀ n : ℕ,
      (μ.map (fun ξ => Real.sqrt n •
          (packFin1 (θhat n (fun i : Fin n => X i.val ξ)) - packFin1 θ₀))).map
        (fun y : EuclideanSpace ℝ (Fin 1) => inner ℝ (packFin1 1) y)
      = μ.map (fun ξ => Real.sqrt n * (θhat n (fun i : Fin n => X i.val ξ) - θ₀)) := by
    intro n
    have hm : Measurable
        (fun ξ => Real.sqrt n •
          (packFin1 (θhat n (fun i : Fin n => X i.val ξ)) - packFin1 θ₀)) :=
      ((hΘmeas n).sub measurable_const).const_smul (Real.sqrt n)
    rw [Measure.map_map hLcont.measurable hm]
    congr 1
    funext ξ
    simp [Function.comp, inner_packFin1_one]
  rw [hRHS] at hmapped
  simpa only [hLHS] using hmapped

/-- **The population Huber score is differentiable at `θ₀` with derivative the negative
central mass** (the `B` of `MMY` Theorem 10.7 for the Huber score): derived from the
Lipschitz score and the absence of atoms at the knots, via differentiation under the
integral. Named separately because it is the analytic heart of the normality proof. -/
theorem hasDerivAt_mLocationScore_huber {P : Measure ℝ} [IsProbabilityMeasure P] {c θ₀ : ℝ}
    (hc : 0 < c)
    -- USER-INPUT: no atoms at the clipping knots; MMY §10.3
    (h_atom_add : P {θ₀ + c} = 0) (h_atom_sub : P {θ₀ - c} = 0) :
    HasDerivAt (mLocationScore (huberPsi c) P) (-(P.real {x | |x - θ₀| < c})) θ₀ :=
  hasDerivAt_mLocationScore_huber_aux hc h_atom_add h_atom_sub

end StatLean.RobustStatistics
