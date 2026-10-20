module
public import StatLean.AsymptoticStatistics.MEstimator.MEstimatorNormality
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal
public import StatLean.AsymptoticStatistics.EmpiricalProcess.OuterProbAsymptotics
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LipschitzShellModulus
public import StatLean.AsymptoticStatistics.MEstimator.MetricRate
public import StatLean.AsymptoticStatistics.MEstimator.NuisanceRate
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# M-estimator `√n`-rate of convergence (vdV Corollary 5.53 via Theorem 5.52)

This file establishes the `√n` rate `√n(θ̂ₙ − θ₀) = O_P(1)` used in the argmax
localization theorem.

vdV Corollary 5.53 (book p.77; PDF p.92) via Theorem 5.52 (peeling / concentric shells):
for a criterion `θ ↦ m_θ` whose population map `θ ↦ Pm_θ` has a curvature
upper bound `P(m_θ − m_{θ₀}) ≲ −‖θ − θ₀‖²` (rate exponent `α = 2`) and whose
localized empirical modulus satisfies `E*‖𝔾ₙ‖_{ℳδ} ≲ δ` (rate exponent
`β = 1`), a near-maximizer `θ̂ₙ` with `ℙₙm_{θ̂} ≥ ℙₙm_{θ₀} − O_P(n⁻¹)` and
`θ̂ₙ →ₚ θ₀` satisfies `√n(θ̂ₙ − θ₀) = O_P(1)`.

The proof specializes the general form of vdV Theorem 5.52 in `MEstimator/MetricRate.lean`.
It localizes to a closed ball and dilates the parameter so the curvature and modulus bounds
share one constant, instantiates `α = 2`, `β = 1`,
and transfers the resulting outer-probability rate back to the measurable
Euclidean estimator.

-/

namespace AsymptoticStatistics.MEstimator

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology RealInnerProductSpace Matrix

/-! ### Population curvature upper bound (`α = 2`) -/

/-- **Curvature upper bound** (vdV Corollary 5.53 and Theorem 5.52).

The population criterion `θ ↦ Pm_θ` drops off quadratically away from its maximum
`θ₀`: there is `C > 0` and a radius `ρ` with

    ∫ (m_θ − m_{θ₀}) ∂P ≤ − C · ‖θ − θ₀‖²   for all `‖θ − θ₀‖ < ρ`.

Deterministic. Derived from the second-order Taylor expansion of `θ ↦ Pm_θ` at
`θ₀` (the remainder hypothesis `hTaylor`) with symmetric negative-definite
second derivative `V` (`hVneg`): with `C := c/4` the leading quadratic term
`½⟪θ−θ₀, V(θ−θ₀)⟫ ≤ −(c/2)‖θ−θ₀‖²` dominates the `(c/4)‖θ−θ₀‖²` remainder. Rate
exponent `α = 2` for Thm 5.52. -/
theorem curvature_upper_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ)
    {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    (hTaylor : ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < ρ →
      |(∫ x, (m θ x - m θ₀ x) ∂P)
          - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫|
        ≤ (c / 4) * ‖θ - θ₀‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < ρ →
        ∫ x, (m θ x - m θ₀ x) ∂P ≤ - C * ‖θ - θ₀‖ ^ 2 := by
  obtain ⟨ρ, hρ, hT⟩ := hTaylor
  refine ⟨c / 4, by positivity, ρ, hρ, fun θ hθ => ?_⟩
  -- `|∫(mθ - mθ₀) - ½⟪·,V·⟫| ≤ (c/4)‖·‖²` gives an upper bound on the integral,
  -- and `⟪·,V·⟫ ≤ -c‖·‖²` (neg-definite) closes the curvature `-(c/4)‖·‖²`.
  have hle := (abs_le.mp (hT θ hθ)).2
  nlinarith [hle, hVneg (θ - θ₀)]

/-! ### Localized empirical modulus bound (`β = 1`) -/

/-- **Localized empirical modulus bound** (vdV Corollary 5.53 and Theorem 5.52).

The expected localized empirical modulus of the difference class grows linearly
in the shell radius `δ`: there are `C > 0`, `ρ > 0` with

    E* sup_{‖θ−θ₀‖<δ} |𝔾ₙ(m_θ − m_{θ₀})| ≤ C · δ   for all `0 < δ < ρ`,

uniformly in `n`. From the Lipschitz condition on `θ ↦ m_θ` (envelope `menv`):
the difference class `{m_θ − m_{θ₀} : ‖θ − θ₀‖ < δ}` has bracketing number
`≲ (1/δ)^d` (`bracketingNumber_le_of_lipschitz`), whose finite entropy integral
`J_{[]}(δ) ≲ δ` feeds the tight maximal inequality
`maximal_inequality_bracketing_tight` (`Maximal.lean`). Rate exponent `β = 1`.

`E*` is represented by `∫⁻ … supNormOver …`. The theorem
`lipschitzShellModulus_bound` gives the uniform-in-`n`,
linear-in-`δ` estimate through fixed-center bracketing. -/
theorem modulus_maximal_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ δ : ℝ, 0 < δ → δ < ρ → ∀ n : ℕ,
        ∫⁻ ξ, supNormOver
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
          ≤ ENNReal.ofReal (C * δ) := by
  -- Apply the fixed-center bracketing shell maximal inequality
  -- `lipschitzShellModulus_bound` (vdV Corollary 5.53 and Lemma 19.34).
  exact lipschitzShellModulus_bound P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
    μ X hX_meas hX_indep hX_id hX_law

/-! ### The `√n` rate (vdV Corollary 5.53)

The peeling core is decomposed into

* `exists_measureReal_gt_le` — per-index tightness of a single measurable rate;
* `isBoundedInProb_of_eventual_tail` — a general `O_P(1)` criterion: an
  eventually-uniform upper-tail bound plus per-index tightness gives
  `IsBoundedInProb`;
* `sqrtn_rate_eventual_tail` — the van der Vaart–Wellner peeling tail,
  with the slack cutoff parameterized by `K`;
* `sqrtn_rate_peeling` — their combination.
-/

/-- A single measurable
real random variable on a finite measure space is tight: its upper-tail mass
`μ.real {ξ | M < r ξ}` can be made `≤ ε` by taking the threshold `M` large.
Continuity from above (`tendsto_measure_iInter_atTop`) applied to the decreasing
sets `{ξ | (M : ℕ) < r ξ}`, whose intersection is empty (Archimedean). -/
private theorem exists_measureReal_gt_le {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsFiniteMeasure μ] (r : Ξ → ℝ) (hr : Measurable r)
    {ε : ℝ} (hε : 0 < ε) : ∃ M : ℝ, μ.real {ξ | M < r ξ} ≤ ε := by
  set s : ℕ → Set Ξ := fun M => {ξ | (M : ℝ) < r ξ} with hs_def
  have hmeas : ∀ M, MeasurableSet (s M) := fun M => measurableSet_lt measurable_const hr
  have hanti : Antitone s := by
    intro a b hab ξ hξ
    have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    exact lt_of_le_of_lt hcast hξ
  have hiInter : (⋂ M, s M) = ∅ := by
    ext ξ
    simp only [hs_def, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    obtain ⟨M, hM⟩ := exists_nat_gt (r ξ)
    exact ⟨M, hM.le⟩
  have htends : Tendsto (fun M => μ (s M)) atTop (𝓝 (μ (⋂ M, s M))) :=
    tendsto_measure_iInter_atTop (fun M => (hmeas M).nullMeasurableSet) hanti
      ⟨0, measure_ne_top μ _⟩
  rw [hiInter, measure_empty] at htends
  have hev : ∀ᶠ M in atTop, μ (s M) < ENNReal.ofReal ε :=
    htends.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨M, hM⟩ := hev.exists
  refine ⟨(M : ℝ), ?_⟩
  rw [measureReal_def]
  calc (μ (s M)).toReal ≤ (ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hM.le
    _ = ε := ENNReal.toReal_ofReal hε.le

/-- Derive `O_P(1)` from an eventually uniform tail bound.
A nonnegative measurable rate `r` is bounded in probability (`O_P(1)`) as soon as
its upper-tail mass is *eventually* uniformly small — i.e. for each `ε > 0` there
is a threshold `M` and an index `N` with `μ.real {ξ | M < r n ξ} ≤ ε` for all
`n ≥ N` — because the finitely many indices `n < N` are each individually tight
(`exists_measureReal_gt_le`); enlarging `M` to dominate all of them keeps the
bound uniform over *all* `n`. This is the "finitely many small `n` by enlarging
`M`" step of the peeling. -/
private theorem isBoundedInProb_of_eventual_tail {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r : ℕ → Ξ → ℝ)
    (hr_meas : ∀ n, Measurable (r n)) (hr_nonneg : ∀ n ξ, 0 ≤ r n ξ)
    (h_tail : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      μ.real {ξ | M < r n ξ} ≤ ε) :
    IsBoundedInProb (fun _ : ℕ => μ) r := by
  intro ε hε
  obtain ⟨M₀, N, hM₀⟩ := h_tail ε hε
  have hindiv : ∀ n : ℕ, ∃ M : ℝ, μ.real {ξ | M < r n ξ} ≤ ε :=
    fun n => exists_measureReal_gt_le μ (r n) (hr_meas n) hε
  -- Enlarge `M₀` to also dominate the finitely many indices `n < N`.
  have hcomb : ∀ K : ℕ, ∃ M : ℝ, M₀ ≤ M ∧ ∀ n, n < K → μ.real {ξ | M < r n ξ} ≤ ε := by
    intro K
    induction K with
    | zero => exact ⟨M₀, le_refl _, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
    | succ K ih =>
      obtain ⟨M, hM₀M, hMcov⟩ := ih
      obtain ⟨MK, hMK⟩ := hindiv K
      refine ⟨max M MK, le_trans hM₀M (le_max_left _ _), fun n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
      · exact le_trans (measureReal_mono
          (fun ξ hξ => lt_of_le_of_lt (le_max_left M MK) hξ)) (hMcov n hlt)
      · subst heq
        exact le_trans (measureReal_mono
          (fun ξ hξ => lt_of_le_of_lt (le_max_right M MK) hξ)) hMK
  obtain ⟨M, hM₀M, hMcov⟩ := hcomb N
  refine ⟨M, fun n => ?_⟩
  have hnorm : {ω | M < ‖r n ω‖} = {ξ | M < r n ξ} := by
    ext ξ; simp only [Set.mem_setOf_eq, Real.norm_of_nonneg (hr_nonneg n ξ)]
  change μ.real {ω | M < ‖r n ω‖} ≤ ε
  rw [hnorm]
  rcases lt_or_ge n N with hn | hn
  · exact hMcov n hn
  · exact le_trans (measureReal_mono (fun ξ hξ => lt_of_le_of_lt hM₀M hξ)) (hM₀ n hn)

/-- Any real `v ≥ 2^J` lies in a dyadic shell
`[2^j, 2^{j+1})` with `j ≥ J`. Elementary: the least `k` with `v < 2^{J+k+1}` exists
(Archimedean `pow_unbounded_of_one_lt`), and `j := J + k` works, with `2^j ≤ v` from
minimality. -/
private theorem dyadic_shell_index (v : ℝ) (J : ℕ) (hv : (2 : ℝ) ^ J ≤ v) :
    ∃ j : ℕ, J ≤ j ∧ (2 : ℝ) ^ j ≤ v ∧ v < (2 : ℝ) ^ (j + 1) := by
  have hex : ∃ k : ℕ, v < (2 : ℝ) ^ (J + k + 1) := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt v (one_lt_two)
    refine ⟨N, lt_of_lt_of_le hN ?_⟩
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  classical
  refine ⟨J + Nat.find hex, Nat.le_add_right _ _, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · simpa [h0] using hv
  · have hmin : ¬ v < (2 : ℝ) ^ (J + (Nat.find hex - 1) + 1) :=
      Nat.find_min hex (by omega)
    have heq : J + (Nat.find hex - 1) + 1 = J + Nat.find hex := by omega
    rw [heq] at hmin
    exact not_lt.mp hmin

/-- Population-mean
continuity).** The population mean-difference map `θ ↦ ∫ (m θ − m_{θ₀}) dP` is
globally Lipschitz, hence continuous. On a finite measure, `menv ∈ L²(P) ⊆ L¹(P)`,
so each `m θ − m θ'` is integrable and dominated by `|menv|·‖θ − θ'‖`; therefore
`|∫(m θ − m_{θ₀}) − ∫(m θ' − m_{θ₀})| = |∫(m θ − m θ')| ≤ (∫|menv| dP)·‖θ − θ'‖`.
This is the continuity of the `θ`-parametrised empirical process that drives the
separability reduction in `localizedModulus_aemeasurable`. -/
private theorem popMeanDiff_continuous
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ContinuousOn (fun θ : EuclideanSpace ℝ (Fin d) => ∫ ω, (m θ ω - m θ₀ ω) ∂P)
      (Metric.closedBall θ₀ ρ) := by
  have hmenv_int : Integrable menv P := hmenv.integrable (by norm_num)
  have habs_int : Integrable (fun ω => |menv ω|) P := hmenv_int.abs
  have hdiff_int : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ,
      Integrable (fun ω => m θ ω - m θ' ω) P := by
    intro θ hθ θ' hθ'
    refine Integrable.mono' (habs_int.mul_const ‖θ - θ'‖)
      (((hm_meas θ).sub (hm_meas θ')).aestronglyMeasurable)
      (Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]
    calc |m θ ω - m θ' ω| ≤ menv ω * ‖θ - θ'‖ := hLip θ hθ θ' hθ' ω
      _ ≤ |menv ω| * ‖θ - θ'‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have hL0 : (0 : ℝ) ≤ ∫ ω, |menv ω| ∂P := integral_nonneg (fun ω => abs_nonneg _)
  have hθ₀mem : θ₀ ∈ Metric.closedBall θ₀ ρ := Metric.mem_closedBall_self hρ.le
  refine (LipschitzOnWith.of_dist_le_mul
    (K := Real.toNNReal (∫ ω, |menv ω| ∂P)) (fun θ hθ θ' hθ' => ?_)).continuousOn
  rw [Real.dist_eq, Real.coe_toNNReal _ hL0, dist_eq_norm]
  have hsub : (∫ ω, (m θ ω - m θ₀ ω) ∂P) - (∫ ω, (m θ' ω - m θ₀ ω) ∂P)
      = ∫ ω, (m θ ω - m θ' ω) ∂P := by
    rw [← integral_sub (hdiff_int θ hθ θ₀ hθ₀mem) (hdiff_int θ' hθ' θ₀ hθ₀mem)]
    congr 1
    funext ω
    ring
  rw [hsub]
  calc |∫ ω, (m θ ω - m θ' ω) ∂P|
      ≤ ∫ ω, |m θ ω - m θ' ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, |menv ω| * ‖θ - θ'‖ ∂P := by
        refine integral_mono ((hdiff_int θ hθ θ' hθ').abs) (habs_int.mul_const _) (fun ω => ?_)
        calc |m θ ω - m θ' ω| ≤ menv ω * ‖θ - θ'‖ := hLip θ hθ θ' hθ' ω
          _ ≤ |menv ω| * ‖θ - θ'‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ = (∫ ω, |menv ω| ∂P) * ‖θ - θ'‖ := integral_mul_const _ _

/-- **Separability measurability of the localized empirical modulus** (standard
empirical-process fact, vdV §18–19). The `sup`-over-`θ` empirical modulus
`ξ ↦ sup_{‖θ−θ₀‖<δ} |𝔾ₙ(m_θ − m_{θ₀})|` is `AEMeasurable`. Although the supremum
ranges over an uncountable ball of parameters, `θ ↦ 𝔾ₙ(m_θ − m_{θ₀})` is continuous
in `θ` (the empirical average is Lipschitz via `hLip`, the population integral is
Lipschitz via `popMeanDiff_continuous`), so the supremum over the open ball equals
the countable supremum over a dense sequence (`TopologicalSpace.exists_dense_seq`),
each slice `ξ ↦ ofReal|𝔾ₙ(m_θ − m_{θ₀})|` being measurable (`Measurable.iSup`). It
is the sole measurability input to the Markov step of `sqrtn_rate_shell_bound`. -/
private theorem localizedModulus_aemeasurable
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (n : ℕ) (δ : ℝ) (hδρ : δ ≤ ρ) :
    AEMeasurable (fun ξ : Ξ => supNormOver
        {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
          g = fun ω => m θ ω - m θ₀ ω}
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) μ := by
  classical
  -- Continuity of `θ ↦ m θ x` on the ball for each fixed sample point (Lipschitz via `hLip`).
  have hm_cont : ∀ x : Ω, ContinuousOn (fun θ : EuclideanSpace ℝ (Fin d) => m θ x)
      (Metric.closedBall θ₀ ρ) := by
    intro x
    refine (LipschitzOnWith.of_dist_le_mul
      (K := Real.toNNReal |menv x|) (fun θ hθ θ' hθ' => ?_)).continuousOn
    rw [Real.dist_eq, Real.coe_toNNReal _ (abs_nonneg _), dist_eq_norm]
    calc |m θ x - m θ' x| ≤ menv x * ‖θ - θ'‖ := hLip θ hθ θ' hθ' x
      _ ≤ |menv x| * ‖θ - θ'‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  -- Continuity of the population-integral term on the ball.
  have hB_cont := popMeanDiff_continuous P m θ₀ hm_meas menv hmenv ρ hρ hLip
  -- Continuity of `θ ↦ 𝔾ₙ(m_θ − m_{θ₀})` on the ball for each fixed `ξ`.
  have hemp_cont : ∀ ξ : Ξ, ContinuousOn (fun θ : EuclideanSpace ℝ (Fin d) =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) (fun ω => m θ ω - m θ₀ ω))
      (Metric.closedBall θ₀ ρ) := by
    intro ξ
    have hsum : ContinuousOn (fun θ : EuclideanSpace ℝ (Fin d) =>
        ∑ i : Fin n, (m θ (X i.val ξ) - m θ₀ (X i.val ξ)))
        (Metric.closedBall θ₀ ρ) :=
      continuousOn_finset_sum Finset.univ
        (fun i _ => (hm_cont (X i.val ξ)).sub continuousOn_const)
    exact (ContinuousOn.sub (hsum.const_mul ((n : ℝ)⁻¹)) hB_cont).const_mul (Real.sqrt n)
  -- Measurability of each fixed-`θ` slice `ξ ↦ ofReal|𝔾ₙ(m_θ − m_{θ₀})|`.
  have hmeas_perθ : ∀ θ : EuclideanSpace ℝ (Fin d),
      Measurable (fun ξ : Ξ => ENNReal.ofReal
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => m θ ω - m θ₀ ω)|) := by
    intro θ
    have hg : Measurable (fun ω => m θ ω - m θ₀ ω) := (hm_meas θ).sub (hm_meas θ₀)
    have hE : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (fun ω => m θ ω - m θ₀ ω)) := by
      unfold empiricalProcess empiricalAvg
      refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum Finset.univ (fun i _ => hg.comp (hX_meas i.val))
    exact hE.abs.ennreal_ofReal
  refine Measurable.aemeasurable ?_
  by_cases hδ : 0 < δ
  · -- Nonempty `θ`-ball: reduce to a countable sup over a dense sequence.
    haveI : Nonempty {θ : EuclideanSpace ℝ (Fin d) // ‖θ - θ₀‖ < δ} :=
      ⟨⟨θ₀, by simpa using hδ⟩⟩
    obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq
      {θ : EuclideanSpace ℝ (Fin d) // ‖θ - θ₀‖ < δ}
    have hkey : (fun ξ : Ξ => supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        = fun ξ : Ξ => ⨆ j : ℕ, ENNReal.ofReal
            |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => m (q j).1 ω - m θ₀ ω)| := by
      funext ξ
      apply le_antisymm
      · simp only [supNormOver]
        refine iSup₂_le ?_
        rintro f ⟨θ, hθ, rfl⟩
        have hval_mem : ∀ θ' : {θ : EuclideanSpace ℝ (Fin d) // ‖θ - θ₀‖ < δ},
            (θ'.1 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall θ₀ ρ := by
          intro θ'
          rw [Metric.mem_closedBall, dist_eq_norm]
          exact le_of_lt (lt_of_lt_of_le θ'.2 hδρ)
        have hΨcont : Continuous
            (fun θ' : {θ : EuclideanSpace ℝ (Fin d) // ‖θ - θ₀‖ < δ} =>
              ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => m θ'.1 ω - m θ₀ ω)|) :=
          ((ENNReal.continuous_ofReal.comp continuous_abs).comp_continuousOn
            (hemp_cont ξ)).comp_continuous continuous_subtype_val hval_mem
        have hmem : (⟨θ, hθ⟩ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ - θ₀‖ < δ})
            ∈ closure (Set.range q) := hq _
        rw [mem_closure_iff_seq_limit] at hmem
        obtain ⟨y, hy_mem, hy_lim⟩ := hmem
        refine le_of_tendsto ((hΨcont.tendsto ⟨θ, hθ⟩).comp hy_lim)
          (Eventually.of_forall (fun k => ?_))
        obtain ⟨j, hj⟩ := hy_mem k
        simp only [Function.comp_apply]
        rw [← hj]
        exact le_iSup (fun j : ℕ => ENNReal.ofReal |empiricalProcess P n
          (fun i : Fin n => X i.val ξ) (fun ω => m (q j).1 ω - m θ₀ ω)|) j
      · refine iSup_le (fun j => ?_)
        exact le_supNormOver ⟨(q j).1, (q j).2, rfl⟩
    rw [hkey]
    exact Measurable.iSup (fun j => hmeas_perθ (q j).1)
  · -- Empty `θ`-ball (`δ ≤ 0`): the modulus is identically `0`.
    rw [not_lt] at hδ
    have hconst : (fun ξ : Ξ => supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        = fun _ => (0 : ℝ≥0∞) := by
      funext ξ
      refine le_antisymm ?_ (zero_le)
      simp only [supNormOver]
      refine iSup₂_le (fun f hf => ?_)
      obtain ⟨θ, hθ, -⟩ := hf
      exact absurd (hθ.trans_le hδ) (not_lt.mpr (norm_nonneg _))
    rw [hconst]
    exact measurable_const

/-- **van der Vaart–Wellner peeling shell-sum core.**
(vdV Theorem 5.52 / van der Vaart–Wellner Theorem 3.2.5; the concentric-shells
Markov bound). This is the analytic shell estimate for `mEstimator_sqrtn_rate`,
separated from the near-max and consistency events: for every `ε > 0` there
is a shell floor `J` such
that, **on the good region** where the estimator is within the localization
radius `ρloc` (`‖θ̂ − θ₀‖ < ρloc`) and the near-max slack is small
(`n·max(0, ℙₙm_{θ₀} − ℙₙm_{θ̂}) < K`), the mass above the floor `2ᴶ` is `≤ ε`,
uniformly in `n`.

`ρloc` is the localization radius, `≤ ρ₁` (so `hcurv` applies) and `2ρloc ≤ ρ₂`
(so on any reached shell `δ = 2ʲ⁺¹/√n < 2ρloc ≤ ρ₂` and `hmod` applies). The
separate `ρ` is the (larger) radius of the ball on which `m` is Lipschitz
(`ρ₂ ≤ ρ` via `hρ₂ρ`), guaranteeing every reached shell stays inside the
Lipschitz domain `closedBall θ₀ ρ`.

On the shell
`‖θ̂ − θ₀‖ ∈ [2ʲ/√n, 2ʲ⁺¹/√n)` inside the good region, the near-max lower bound
`ℙₙ(m_{θ̂} − m_{θ₀}) ≥ −K·n⁻¹` combined with the empirical decomposition
`ℙₙ(m_{θ̂} − m_{θ₀}) = ∫(m_{θ̂} − m_{θ₀}) + n^{−1/2}𝔾ₙ(m_{θ̂} − m_{θ₀})` (`hcurv`
is stated directly on the difference integral `∫(m_{θ̂} − m_{θ₀})`) yields
`½C₁·2²ʲ ≤ √n·|𝔾ₙ(m_{θ̂} − m_{θ₀})|`. Markov applied to `hmod` at
`δ = 2ʲ⁺¹/√n` bounds the shell mass by `(4C₂/C₁)·2⁻ʲ`, summable over `j ≥ J`,
giving the claimed `ε` for `2ᴶ` large.

For the parameterized slack cutoff, the good event gives `‖scaledSlack‖ < K`.
The shell floor is locked by choosing `J` with
`max (2 * K / C₁) (8 * C₂ / (C₁ * ε)) < (2 : ℝ) ^ J`; this is the only
change to the geometric floor, and the `n = 0` rate event remains empty.

The proof uses dyadic covering
(`dyadic_shell_index`),
per-shell curvature/near-max lower bound `½C₁·2²ʲ/√n ≤ 𝔾ₙ(m_{θ̂} − m_{θ₀})`,
`ENNReal`-Markov (`meas_ge_le_lintegral_div` against `hmod`), and the geometric
tsum `Σ_{j≥J}(4C₂/C₁)2⁻ʲ = (8C₂/C₁)2⁻ᴶ`. Measurability of the
`sup`-over-θ empirical modulus follows from `localizedModulus_aemeasurable`,
using the standard empirical-process separability reduction and the Lipschitz
condition `hLip`. -/
private theorem sqrtn_rate_shell_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (C₁ : ℝ) (hC₁ : 0 < C₁) (ρ₁ : ℝ) (hρ₁ : 0 < ρ₁)
    (hcurv : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < ρ₁ →
      ∫ x, (m θ x - m θ₀ x) ∂P ≤ - C₁ * ‖θ - θ₀‖ ^ 2)
    (C₂ : ℝ) (hC₂ : 0 < C₂) (ρ₂ : ℝ) (hρ₂ : 0 < ρ₂) (hρ₂ρ : ρ₂ ≤ ρ)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hmod : ∀ δ : ℝ, 0 < δ → δ < ρ₂ → ∀ n : ℕ,
      ∫⁻ ξ, supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal (C₂ * δ))
    (ρloc : ℝ) (hρ0 : 0 < ρloc) (hρρ₁ : ρloc ≤ ρ₁) (h2ρρ₂ : 2 * ρloc ≤ ρ₂)
    -- Positive cutoff supplied by the eventual scaled-slack tail bound.
    (K : ℝ) (hK : 0 < K)
    (hθhat_meas : ∀ n, Measurable (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ))) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ n : ℕ,
      μ.real ({ξ | (2 : ℝ) ^ J < Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}
          ∩ ({ξ | ρloc ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}
            ∪ {ξ | K ≤ ‖(n : ℝ) * max 0
                (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
                  - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
                      (fun i : Fin n => X i.val ξ))‖})ᶜ) ≤ ε := by
  intro ε hε
  have hC₁ne : C₁ ≠ 0 := hC₁.ne'
  have hεne : ε ≠ 0 := hε.ne'
  -- Choose the shell floor `J` (independent of `n`).
  -- Locked shell floor for random `O_P(1)` slack:
  -- `max (2 * K / C₁) (8 * C₂ / (C₁ * ε)) < 2^J`.
  set Kfloor : ℝ := max (2 * K / C₁) (8 * C₂ / (C₁ * ε)) with hKdef
  obtain ⟨J, hJK⟩ := pow_unbounded_of_one_lt Kfloor (one_lt_two)
  refine ⟨J, fun n => ?_⟩
  set A : Set Ξ :=
    {ξ | (2 : ℝ) ^ J < Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} with hAdef
  set Good : Set Ξ :=
    ({ξ | ρloc ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}
      ∪ {ξ | K ≤ ‖(n : ℝ) * max 0
          (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
            - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
                (fun i : Fin n => X i.val ξ))‖})ᶜ with hGooddef
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0`: `√0 = 0`, so `A = ∅`.
    subst hn0
    have hAe : A = (∅ : Set Ξ) := by
      rw [hAdef]
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt,
        Nat.cast_zero, Real.sqrt_zero, zero_mul]
      positivity
    rw [hAe, Set.empty_inter, measureReal_empty]
    exact hε.le
  · -- `n ≥ 1`.
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsqrtn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
    have hsqn0 : Real.sqrt n ≠ 0 := hsqrtn.ne'
    have hsqn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
    -- Per-shell measure bound (dyadic shell `[2^j, 2^{j+1})`, `j ≥ J`).
    have hshell : ∀ j : ℕ, J ≤ j →
        μ (({ξ | (2 : ℝ) ^ j ≤ Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ∧
              Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < (2 : ℝ) ^ (j + 1)}) ∩ Good)
          ≤ ENNReal.ofReal ((4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ j) := by
      intro j hjJ
      set Sh : Set Ξ :=
        {ξ | (2 : ℝ) ^ j ≤ Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ∧
          Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < (2 : ℝ) ^ (j + 1)}
        with hShdef
      set δ : ℝ := (2 : ℝ) ^ (j + 1) / Real.sqrt n with hδdef
      set t : ℝ := (C₁ / 2) * (2 : ℝ) ^ (2 * j) / Real.sqrt n with htdef
      have htpos : 0 < t := by rw [htdef]; positivity
      have hδpos : 0 < δ := by rw [hδdef]; positivity
      -- Curvature floor: `(C₁/2)·2^{2j} ≥ K` for `j ≥ J`.
      have hfloor : K ≤ (C₁ / 2) * (2 : ℝ) ^ (2 * j) := by
        have h2KC₁ : 2 * K / C₁ < (2 : ℝ) ^ J :=
          lt_of_le_of_lt (le_max_left _ _) hJK
        have hJle : J ≤ 2 * j := by omega
        have hpow_mono : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (2 * j) := pow_le_pow_right₀ (by norm_num) hJle
        have hbig : 2 * K / C₁ < (2 : ℝ) ^ (2 * j) :=
          lt_of_lt_of_le h2KC₁ hpow_mono
        have hstep : (C₁ / 2) * (2 * K / C₁) <
            (C₁ / 2) * (2 : ℝ) ^ (2 * j) :=
          mul_lt_mul_of_pos_left hbig (half_pos hC₁)
        have heqK : (C₁ / 2) * (2 * K / C₁) = K := by field_simp
        nlinarith [hstep, heqK, hK.le]
      by_cases hne : (Sh ∩ Good).Nonempty
      · -- Nonempty shell: derive `δ < ρ₂` from a witness, then Markov.
        obtain ⟨ξ₀, hξ₀Sh, hξ₀Good⟩ := hne
        rw [hShdef] at hξ₀Sh
        obtain ⟨hlb0, _⟩ := hξ₀Sh
        rw [hGooddef] at hξ₀Good
        simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hξ₀Good
        obtain ⟨hρlt0, _⟩ := hξ₀Good
        have hδρ₂ : δ < ρ₂ := by
          have h1 : (2 : ℝ) ^ j < Real.sqrt n * ρloc :=
            lt_of_le_of_lt hlb0 (mul_lt_mul_of_pos_left hρlt0 hsqrtn)
          have h2 : (2 : ℝ) ^ j / Real.sqrt n < ρloc :=
            (div_lt_iff₀ hsqrtn).mpr (by rw [mul_comm]; exact h1)
          rw [hδdef]
          have h3 : (2 : ℝ) ^ (j + 1) / Real.sqrt n = 2 * ((2 : ℝ) ^ j / Real.sqrt n) := by
            rw [pow_succ]; ring
          rw [h3]; linarith [h2, h2ρρ₂]
        -- Pointwise inclusion into the modulus super-level set.
        have hincl : Sh ∩ Good ⊆
            {ξ | ENNReal.ofReal t ≤ supNormOver
                {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
                  g = fun ω => m θ ω - m θ₀ ω}
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)} := by
          rintro ξ ⟨hξSh, hξGood⟩
          rw [hShdef] at hξSh
          obtain ⟨hlb, hub⟩ := hξSh
          rw [hGooddef] at hξGood
          simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hξGood
          obtain ⟨hρlt, hnear⟩ := hξGood
          simp only [Set.mem_setOf_eq]
          set xs : Fin n → Ω := fun i : Fin n => X i.val ξ with hxsdef
          set th : EuclideanSpace ℝ (Fin d) := θ_hat n xs with hthdef
          set g : Ω → ℝ := fun ω => m th ω - m θ₀ ω with hgdef
          -- Class membership of `g`.
          have hmem : g ∈ {gg : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
              gg = fun ω => m θ ω - m θ₀ ω} := by
            refine ⟨th, ?_, hgdef⟩
            rw [hδdef, lt_div_iff₀ hsqrtn, mul_comm]; exact hub
          -- Near-max ⇒ `n·(ℙₙm_{θ₀} − ℙₙm_{θ̂}) < K`.
          have hnear' : (n : ℝ) * (empiricalAvg (m θ₀) n xs - empiricalAvg (m th) n xs) < K := by
            have hnn : (0 : ℝ) ≤ (n : ℝ) *
                max 0 (empiricalAvg (m θ₀) n xs - empiricalAvg (m th) n xs) :=
              mul_nonneg hn'.le (le_max_left _ _)
            rw [Real.norm_of_nonneg hnn] at hnear
            exact lt_of_le_of_lt
              (mul_le_mul_of_nonneg_left (le_max_right _ _) hn'.le) hnear
          -- Empirical decomposition and curvature.
          have hEsub : empiricalAvg g n xs
              = empiricalAvg (m th) n xs - empiricalAvg (m θ₀) n xs := by
            rw [hgdef]; unfold empiricalAvg; rw [Finset.sum_sub_distrib, mul_sub]
          have hInt : (∫ x, g x ∂P) = ∫ x, (m th x - m θ₀ x) ∂P := by rw [hgdef]
          have hcurv_app : (∫ x, (m th x - m θ₀ x) ∂P) ≤ -C₁ * ‖th - θ₀‖ ^ 2 :=
            hcurv th (lt_of_lt_of_le hρlt hρρ₁)
          have hnsq : (2 : ℝ) ^ (2 * j) ≤ (n : ℝ) * ‖th - θ₀‖ ^ 2 := by
            have hsq_le : ((2 : ℝ) ^ j) ^ 2 ≤ (Real.sqrt n * ‖th - θ₀‖) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hlb 2
            have hL : ((2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ (2 * j) := by
              rw [← pow_mul]; congr 1; ring
            have hR : (Real.sqrt n * ‖th - θ₀‖) ^ 2 = (n : ℝ) * ‖th - θ₀‖ ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hn'.le]
            rw [hL, hR] at hsq_le; exact hsq_le
          -- `√n·𝔾ₙ(g) = n·(ℙₙg − Pg)`.
          have hEval : Real.sqrt n * empiricalProcess P n xs g
              = (n : ℝ) * (empiricalAvg g n xs - ∫ x, g x ∂P) := by
            unfold empiricalProcess; rw [← mul_assoc, hsqn]
          have hnE : -K < (n : ℝ) * empiricalAvg g n xs := by
            have hEeq : empiricalAvg g n xs
                = -(empiricalAvg (m θ₀) n xs - empiricalAvg (m th) n xs) := by rw [hEsub]; ring
            rw [hEeq]; nlinarith [hnear']
          have hnI : (n : ℝ) * (∫ x, g x ∂P) ≤ -(C₁ * ((n : ℝ) * ‖th - θ₀‖ ^ 2)) := by
            have hgle : (∫ x, g x ∂P) ≤ -C₁ * ‖th - θ₀‖ ^ 2 :=
              le_trans (le_of_eq hInt) hcurv_app
            calc (n : ℝ) * (∫ x, g x ∂P)
                ≤ (n : ℝ) * (-C₁ * ‖th - θ₀‖ ^ 2) := mul_le_mul_of_nonneg_left hgle hn'.le
              _ = -(C₁ * ((n : ℝ) * ‖th - θ₀‖ ^ 2)) := by ring
          have hpowle : C₁ * (2 : ℝ) ^ (2 * j) ≤ C₁ * ((n : ℝ) * ‖th - θ₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hnsq hC₁.le
          have hmain : (C₁ / 2) * (2 : ℝ) ^ (2 * j) ≤ Real.sqrt n * empiricalProcess P n xs g := by
            rw [hEval]; nlinarith [hnE, hnI, hpowle, hfloor]
          have ht_le : t ≤ empiricalProcess P n xs g := by
            have h1 : t * Real.sqrt n = (C₁ / 2) * (2 : ℝ) ^ (2 * j) := by
              rw [htdef]; field_simp
            have h2 : t * Real.sqrt n ≤ empiricalProcess P n xs g * Real.sqrt n := by
              rw [h1, mul_comm (empiricalProcess P n xs g) (Real.sqrt n)]; exact hmain
            exact le_of_mul_le_mul_right h2 hsqrtn
          calc ENNReal.ofReal t
              ≤ ENNReal.ofReal |empiricalProcess P n xs g| :=
                ENNReal.ofReal_le_ofReal (le_trans ht_le (le_abs_self _))
            _ ≤ supNormOver {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
                  g = fun ω => m θ ω - m θ₀ ω}
                (fun f => empiricalProcess P n xs f) := le_supNormOver hmem
        -- Markov + ratio.
        have haem : AEMeasurable (fun ξ : Ξ => supNormOver
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) μ :=
          localizedModulus_aemeasurable P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
            μ X hX_meas n δ (le_trans hδρ₂.le hρ₂ρ)
        have hmarkov := meas_ge_le_lintegral_div haem
          (ENNReal.ofReal_pos.mpr htpos).ne' ENNReal.ofReal_ne_top
        calc μ (Sh ∩ Good)
            ≤ μ {ξ | ENNReal.ofReal t ≤ supNormOver
                {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
                  g = fun ω => m θ ω - m θ₀ ω}
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)} :=
              measure_mono hincl
          _ ≤ (∫⁻ ξ, supNormOver
                {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
                  g = fun ω => m θ ω - m θ₀ ω}
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ)
                / ENNReal.ofReal t := hmarkov
          _ ≤ ENNReal.ofReal (C₂ * δ) / ENNReal.ofReal t :=
              ENNReal.div_le_div_right (hmod δ hδpos hδρ₂ n) _
          _ = ENNReal.ofReal ((4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ j) := by
              rw [← ENNReal.ofReal_div_of_pos htpos]
              congr 1
              rw [hδdef, htdef]
              rw [show (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 from by rw [pow_succ]]
              rw [show (2 : ℝ) ^ (2 * j) = ((2 : ℝ) ^ j) ^ 2 from by rw [← pow_mul]; congr 1; ring]
              rw [show ((1 : ℝ) / 2) ^ j = ((2 : ℝ) ^ j)⁻¹ from by rw [one_div, inv_pow]]
              have hp0 : (2 : ℝ) ^ j ≠ 0 := by positivity
              field_simp
              ring
      · -- Empty shell: measure zero.
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, measure_empty]
        exact zero_le
    -- Geometric summability facts.
    have hbound_nonneg : ∀ k : ℕ, (0 : ℝ) ≤ (4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ (J + k) :=
      fun k => by positivity
    have hsummable : Summable (fun k : ℕ => (4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ (J + k)) := by
      apply Summable.mul_left
      have hrw : (fun k : ℕ => ((1 : ℝ) / 2) ^ (J + k))
          = (fun k => ((1 : ℝ) / 2) ^ J * ((1 : ℝ) / 2) ^ k) := by funext k; rw [pow_add]
      rw [hrw]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have htsum_eq : ∑' k : ℕ, (4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ (J + k)
        = (8 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J := by
      have hgeo : ∑' k : ℕ, ((1 : ℝ) / 2) ^ k = 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
      calc ∑' k : ℕ, (4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ (J + k)
          = ∑' k : ℕ, ((4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J) * ((1 : ℝ) / 2) ^ k := by
            congr 1; funext k; rw [pow_add]; ring
        _ = ((4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J) * ∑' k : ℕ, ((1 : ℝ) / 2) ^ k := tsum_mul_left
        _ = ((4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J) * 2 := by rw [hgeo]
        _ = (8 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J := by ring
    -- Cover the good region by shells `j ≥ J`.
    have hcover : A ∩ Good ⊆ ⋃ k : ℕ,
        (({ξ | (2 : ℝ) ^ (J + k) ≤ Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ∧
            Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < (2 : ℝ) ^ (J + k + 1)})
          ∩ Good) := by
      intro ξ hξ
      obtain ⟨hξA, hξG⟩ := hξ
      have hξA' : (2 : ℝ) ^ J <
          Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ := hξA
      obtain ⟨j, hjJ, hj1, hj2⟩ :=
        dyadic_shell_index (Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) J
          (le_of_lt hξA')
      refine Set.mem_iUnion.mpr ⟨j - J, ?_, hξG⟩
      have hjeq : J + (j - J) = j := by omega
      rw [hjeq]
      exact ⟨hj1, hj2⟩
    -- Measure bound via subadditivity + per-shell bound.
    have hμle : μ (A ∩ Good) ≤ ENNReal.ofReal ((8 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J) := by
      calc μ (A ∩ Good)
          ≤ μ (⋃ k : ℕ,
              (({ξ | (2 : ℝ) ^ (J + k) ≤ Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ∧
                  Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < (2 : ℝ) ^ (J + k + 1)})
                ∩ Good)) := measure_mono hcover
        _ ≤ ∑' k : ℕ, μ (({ξ | (2 : ℝ) ^ (J + k) ≤
              Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ∧
              Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < (2 : ℝ) ^ (J + k + 1)})
                ∩ Good) := measure_iUnion_le _
        _ ≤ ∑' k : ℕ, ENNReal.ofReal ((4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ (J + k)) :=
            ENNReal.tsum_le_tsum (fun k => hshell (J + k) (Nat.le_add_right _ _))
        _ = ENNReal.ofReal (∑' k : ℕ, (4 * C₂ / C₁) * ((1 : ℝ) / 2) ^ (J + k)) :=
            (ENNReal.ofReal_tsum_of_nonneg hbound_nonneg hsummable).symm
        _ = ENNReal.ofReal ((8 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J) := by rw [htsum_eq]
    -- Finish: transfer to `μ.real` and use the `J`-choice.
    have hεbound : (8 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J ≤ ε := by
      have hKb : 8 * C₂ / (C₁ * ε) < (2 : ℝ) ^ J := lt_of_le_of_lt (le_max_right _ _) hJK
      have h2Jpos : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
      rw [show ((1 : ℝ) / 2) ^ J = 1 / (2 : ℝ) ^ J from by rw [div_pow, one_pow],
        mul_one_div, div_le_iff₀ h2Jpos]
      have hstep : ε * (8 * C₂ / (C₁ * ε)) < ε * (2 : ℝ) ^ J := mul_lt_mul_of_pos_left hKb hε
      have heq : ε * (8 * C₂ / (C₁ * ε)) = 8 * C₂ / C₁ := by field_simp
      linarith [hstep, heq]
    rw [measureReal_def]
    calc (μ (A ∩ Good)).toReal
        ≤ (ENNReal.ofReal ((8 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hμle
      _ = (8 * C₂ / C₁) * ((1 : ℝ) / 2) ^ J := ENNReal.toReal_ofReal (by positivity)
      _ ≤ ε := hεbound
/-- **van der Vaart–Wellner peeling tail** (vdV Theorem 5.52). For every
`ε > 0` there is a threshold `M`
and an index `N` with `μ.real {√n‖θ̂ₙ − θ₀‖ > M} ≤ ε` for all `n ≥ N`.

Assembles the analytic shell-sum core (`sqrtn_rate_shell_bound`) with the two
vanishing bad events, using localization radius `ρ = min ρ₁ (ρ₂/2)`:

* the **consistency** bad event `D_n = {ρ ≤ ‖θ̂ₙ − θ₀‖}` has `μ`-mass `→ 0`
  (`hConsistent` at level `ρ`);
* the **slack** bad event
  `B_n = {K ≤ ‖n·max(0, ℙₙm_{θ₀} − ℙₙm_{θ̂})‖}` has eventually small mass,
  given by the `O_P(1)` tail hypothesis `hSlackTail`.

Since `{√n‖θ̂ₙ − θ₀‖ > 2ᴶ} ⊆ (that set ∩ (D_n ∪ B_n)ᶜ) ∪ D_n ∪ B_n`, taking
`K` and its eventual tail bound from `hSlackTail`, then taking `J` from the shell
bound at `ε/3` and `N` past which both bad masses are `< ε/3`,
gives the `≤ ε` tail for all `n ≥ N`. -/
private theorem sqrtn_rate_eventual_tail
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (C₁ : ℝ) (hC₁ : 0 < C₁) (ρ₁ : ℝ) (hρ₁ : 0 < ρ₁)
    (hcurv : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < ρ₁ →
      ∫ x, (m θ x - m θ₀ x) ∂P ≤ - C₁ * ‖θ - θ₀‖ ^ 2)
    (C₂ : ℝ) (hC₂ : 0 < C₂) (ρ₂ : ℝ) (hρ₂ : 0 < ρ₂) (hρ₂ρ : ρ₂ ≤ ρ)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hmod : ∀ δ : ℝ, 0 < δ → δ < ρ₂ → ∀ n : ℕ,
      ∫⁻ ξ, supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal (C₂ * δ))
    -- A common eventual-tail bound derived from `O_P(1)`.
    (hSlackTail : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      μ.real {ξ | K ≤ ‖(n : ℝ) * max 0
        (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
          - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
              (fun i : Fin n => X i.val ξ))‖} ≤ η)
    (hConsistent : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    (hθhat_meas : ∀ n, Measurable (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ))) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      μ.real {ξ | M < Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} ≤ ε := by
  intro ε hε
  set ρloc : ℝ := min ρ₁ (ρ₂ / 2) with hρlocdef
  have hρ0 : 0 < ρloc := lt_min hρ₁ (half_pos hρ₂)
  have hρρ₁ : ρloc ≤ ρ₁ := min_le_left _ _
  have h2ρρ₂ : 2 * ρloc ≤ ρ₂ := by
    have hle : ρloc ≤ ρ₂ / 2 := min_le_right _ _
    linarith
  obtain ⟨K, hK, N₂, hN₂⟩ := hSlackTail (ε / 3) (by positivity)
  obtain ⟨J, hJ⟩ := sqrtn_rate_shell_bound P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
    C₁ hC₁ ρ₁ hρ₁ hcurv C₂ hC₂ ρ₂ hρ₂ hρ₂ρ θ_hat μ X hX_meas hX_indep hX_id hX_law hmod
    ρloc hρ0 hρρ₁ h2ρρ₂ K hK hθhat_meas (ε / 3) (by positivity)
  -- The consistency event vanishes; the chosen slack tail is eventually small.
  have hDev : ∀ᶠ n in atTop,
      μ.real {ω | ρloc ≤ ‖θ_hat n (fun i : Fin n => X i.val ω) - θ₀‖} < ε / 3 :=
    (hConsistent ρloc hρ0).eventually (Iio_mem_nhds (by positivity))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hDev
  refine ⟨(2 : ℝ) ^ J, max N₁ N₂, fun n hn => ?_⟩
  have hAcap := hJ n
  have hDbound := le_of_lt (hN₁ n (le_trans (le_max_left _ _) hn))
  have hBbound := hN₂ n (le_trans (le_max_right _ _) hn)
  set A : Set Ξ :=
    {ξ | (2 : ℝ) ^ J < Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} with hA
  set Dn : Set Ξ := {ξ | ρloc ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} with hDn
  set Bn : Set Ξ := {ξ | K ≤ ‖(n : ℝ) * max 0
      (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ))‖} with hBn
  -- `A ⊆ (A ∩ (Dn ∪ Bn)ᶜ) ∪ (Dn ∪ Bn)`; then subadditivity of `Measure.real`.
  have hsub : A ⊆ (A ∩ (Dn ∪ Bn)ᶜ) ∪ (Dn ∪ Bn) := by
    intro ξ hξ
    by_cases hb : ξ ∈ Dn ∪ Bn
    · exact Or.inr hb
    · exact Or.inl ⟨hξ, hb⟩
  calc μ.real A
      ≤ μ.real ((A ∩ (Dn ∪ Bn)ᶜ) ∪ (Dn ∪ Bn)) := measureReal_mono hsub
    _ ≤ μ.real (A ∩ (Dn ∪ Bn)ᶜ) + μ.real (Dn ∪ Bn) := measureReal_union_le _ _
    _ ≤ ε / 3 + (ε / 3 + ε / 3) :=
        add_le_add hAcap ((measureReal_union_le Dn Bn).trans (add_le_add hDbound hBbound))
    _ = ε := by ring
/-- **van der Vaart–Wellner peeling conclusion** (vdV Theorem 5.52). The
scalar rate `√n‖θ̂ₙ − θ₀‖ = O_P(1)` follows from the general `O_P(1)`
criterion `isBoundedInProb_of_eventual_tail` applied to the peeling tail
`sqrtn_rate_eventual_tail`. The rate is measurable via `hθhat_meas`
(`θ̂ₙ ∘ (X · ξ)` measurable ⟹ `√n‖θ̂ₙ − θ₀‖` measurable) and nonnegative. -/
private theorem sqrtn_rate_peeling
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (C₁ : ℝ) (hC₁ : 0 < C₁) (ρ₁ : ℝ) (hρ₁ : 0 < ρ₁)
    (hcurv : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < ρ₁ →
      ∫ x, (m θ x - m θ₀ x) ∂P ≤ - C₁ * ‖θ - θ₀‖ ^ 2)
    (C₂ : ℝ) (hC₂ : 0 < C₂) (ρ₂ : ℝ) (hρ₂ : 0 < ρ₂) (hρ₂ρ : ρ₂ ≤ ρ)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hmod : ∀ δ : ℝ, 0 < δ → δ < ρ₂ → ∀ n : ℕ,
      ∫⁻ ξ, supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal (C₂ * δ))
    -- The common eventual-tail bound used in the peeling estimate.
    (hSlackTail : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      μ.real {ξ | K ≤ ‖(n : ℝ) * max 0
        (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
          - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
              (fun i : Fin n => X i.val ξ))‖} ≤ η)
    (hConsistent : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    (hθhat_meas : ∀ n, Measurable (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ))) :
    IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) := by
  have hr_meas : ∀ n : ℕ, Measurable
      (fun ξ : Ξ => Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) :=
    fun n => (((hθhat_meas n).sub measurable_const).norm.const_mul _)
  have hr_nonneg : ∀ (n : ℕ) (ξ : Ξ),
      0 ≤ Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ :=
    fun n ξ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  exact isBoundedInProb_of_eventual_tail μ _ hr_meas hr_nonneg
    (sqrtn_rate_eventual_tail P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
      C₁ hC₁ ρ₁ hρ₁ hcurv C₂ hC₂ ρ₂ hρ₂ hρ₂ρ θ_hat μ X hX_meas hX_indep hX_id hX_law
      hmod hSlackTail hConsistent hθhat_meas)
/-- **M-estimator `√n` rate of convergence** (vdV Corollary 5.53).

Under the curvature bound (`V`/`hVneg`/`hTaylor`), the Lipschitz
condition (`hLip`/`menv`), near-maximization at the
`O_P(n⁻¹)` scale (encoded as boundedness in probability of the scaled positive
slack `n·max(0, ℙₙm_{θ₀} − ℙₙm_{θ̂})`), and consistency `θ̂ₙ →ₚ θ₀`,

    √n(θ̂ₙ − θ₀) = O_P(1),   i.e.  IsBoundedInProb μ (fun n ξ => √n • (θ̂ₙ − θ₀)).

The proof uses a closed-ball subtype for the local integrability domain.
The dilation `T(φ) = θ₀ + k(φ-θ₀)` reconciles the curvature and modulus constants,
and `localizedModulus_aemeasurable` turns the `lintegral` bound into the
genuine outer expectation required by `mEstimator_rate_of_convergence_outer` at
`α = 2`, `β = 1`.  Its shifted outer conclusion is transferred back to the
measurable original estimator, including the finite `n = 0` prefix. -/
theorem mEstimator_sqrtn_rate
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ)
    {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hTaylor : ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < ρ →
      |(∫ x, (m θ x - m θ₀ x) ∂P)
          - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫|
        ≤ (c / 4) * ‖θ - θ₀‖ ^ 2)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- Corollary 5.53 near-maximality at the `O_P(n⁻¹)` scale.
    (hNearMax : IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ))))
    (hConsistent : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    -- Measurability of the estimator (vdV Cor 5.53 assumes a measurable estimator;
    -- makes the peeling shell events `μ`-measurable).
    (hθhat_meas : ∀ n, Measurable (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ))) :
    IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) := by
  classical
  obtain ⟨C₁, hC₁, ρ₁, hρ₁, hcurv⟩ := curvature_upper_bound P m θ₀ V hc hVneg hTaylor
  obtain ⟨C₂, hC₂, ρ₂, hρ₂, hmod⟩ := modulus_maximal_bound P m θ₀ hm_meas menv hmenv
    hmenv_meas ρ hρ hLip μ X hX_meas hX_indep hX_id hX_law
  let ρloc : ℝ := min ρ (min ρ₁ ρ₂)
  have hρloc : 0 < ρloc := lt_min hρ (lt_min hρ₁ hρ₂)
  let k : ℝ := 4 * C₂ / C₁ + 1
  have hk : 0 < k := by dsimp [k]; positivity
  have hkC : 4 * C₂ / C₁ < k := by simp [k]
  let rloc : ℝ := ρloc / k
  have hrloc : 0 < rloc := div_pos hρloc hk
  let Θloc := {θ : EuclideanSpace ℝ (Fin d) // θ ∈ Metric.closedBall θ₀ rloc}
  let θ₀loc : Θloc := ⟨θ₀, Metric.mem_closedBall_self hrloc.le⟩
  let T : Θloc → EuclideanSpace ℝ (Fin d) := fun θ => θ₀ + k • (θ.1 - θ₀)
  have hT_mem : ∀ θ : Θloc, T θ ∈ Metric.closedBall θ₀ ρloc := by
    intro θ
    have hθ := θ.property
    rw [Metric.mem_closedBall, dist_eq_norm] at hθ ⊢
    have hkrloc : k * rloc = ρloc := by
      dsimp [rloc]
      field_simp
    simp only [T, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    nlinarith
  have hT0 : T θ₀loc = θ₀ := by simp [T, θ₀loc]
  let mloc : Θloc → Ω → ℝ := fun θ => m (T θ)
  have hmloc_meas : ∀ θ, Measurable (mloc θ) := fun θ => hm_meas (T θ)
  have hmloc_int : ∀ θ, Integrable (fun ω => mloc θ ω - mloc θ₀loc ω) P := by
    intro θ
    have hρlocρ : ρloc ≤ ρ := min_le_left _ _
    have hTθρ : T θ ∈ Metric.closedBall θ₀ ρ :=
      Metric.closedBall_subset_closedBall hρlocρ (hT_mem θ)
    have hθ₀ρ : θ₀ ∈ Metric.closedBall θ₀ ρ := Metric.mem_closedBall_self hρ.le
    have hdom : Integrable (fun ω => |menv ω| * ‖T θ - θ₀‖) P :=
      (hmenv.integrable (by norm_num)).abs.mul_const _
    refine hdom.mono' ((hmloc_meas θ).sub (hmloc_meas θ₀loc)).aestronglyMeasurable ?_
    filter_upwards with ω
    change |m (T θ) ω - m (T θ₀loc) ω| ≤ |menv ω| * ‖T θ - θ₀‖
    rw [hT0]
    calc
      |m (T θ) ω - m θ₀ ω| ≤ menv ω * ‖T θ - θ₀‖ :=
        hLip (T θ) hTθρ θ₀ hθ₀ρ ω
      _ ≤ |menv ω| * ‖T θ - θ₀‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  let raw : ℕ → Ξ → EuclideanSpace ℝ (Fin d) := fun n ξ =>
    θ_hat (n + 1) (fun i : Fin (n + 1) => X i.val ξ)
  let pre : ℕ → Ξ → EuclideanSpace ℝ (Fin d) := fun n ξ =>
    θ₀ + k⁻¹ • (raw n ξ - θ₀)
  let θloc : ℕ → Ξ → Θloc := fun n ξ =>
    if h : pre n ξ ∈ Metric.closedBall θ₀ rloc then ⟨pre n ξ, h⟩ else θ₀loc
  let Rloc : ℕ → Ξ → ℝ := fun n ξ =>
    if pre n ξ ∈ Metric.closedBall θ₀ rloc then
      max 0 (empiricalAvg (m θ₀) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) -
        empiricalAvg (m (raw n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ))
    else 0
  let C : ℝ := C₂ * k
  have hC : 0 < C := mul_pos hC₂ hk
  have hcurv' : ∀ δ, 0 < δ → δ < rloc → ∀ θ : Θloc,
      δ / 2 < dist θ θ₀loc → dist θ θ₀loc < δ →
      ∫ ω, (mloc θ ω - mloc θ₀loc ω) ∂P ≤ -C * Real.rpow δ 2 := by
    intro δ hδ hδrloc θ hθlo hθhi
    have hkrloc : k * rloc = ρloc := by
      dsimp [rloc]
      field_simp
    have hdistT : ‖T θ - θ₀‖ = k * dist θ θ₀loc := by
      rw [show T θ - θ₀ = k • (θ.1 - θ₀) by simp [T]]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
      congr 1
    have hTθρ₁ : ‖T θ - θ₀‖ < ρ₁ := by
      rw [hdistT]
      have : k * δ < ρloc := by nlinarith
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hθhi hk) <|
        le_trans this.le (le_trans (min_le_right _ _) (min_le_left _ _))
    have hcoef0 : 4 * C₂ < k * C₁ := (div_lt_iff₀ hC₁).mp hkC
    have hsq : δ ^ 2 / 4 < (dist θ θ₀loc) ^ 2 := by
      nlinarith [sq_nonneg (dist θ θ₀loc - δ / 2)]
    have hcoefδ := mul_lt_mul_of_pos_right hcoef0
      (div_pos (mul_pos hk (sq_pos_of_pos hδ)) (by norm_num : (0 : ℝ) < 4))
    have hcurvδ := mul_lt_mul_of_pos_left hsq (mul_pos hC₁ (sq_pos_of_pos hk))
    have hcoef : C₂ * k * δ ^ 2 < C₁ * (k * dist θ θ₀loc) ^ 2 := by
      nlinarith
    change ∫ ω, (m (T θ) ω - m (T θ₀loc) ω) ∂P ≤ -C * Real.rpow δ 2
    rw [hT0]
    have hrpow₂ : Real.rpow δ 2 = δ ^ 2 := by norm_num [Real.rpow_natCast]
    rw [hrpow₂]
    calc
      ∫ ω, (m (T θ) ω - m θ₀ ω) ∂P ≤ -C₁ * ‖T θ - θ₀‖ ^ 2 := hcurv (T θ) hTθρ₁
      _ = -C₁ * (k * dist θ θ₀loc) ^ 2 := by rw [hdistT]
      _ ≤ -(C₂ * k) * δ ^ 2 := by linarith
  have hmod' : ∀ δ, 0 < δ → δ < rloc → ∀ n,
      outerExpectation μ (fun ξ =>
        ⨆ θ : {θ : Θloc // dist θ θ₀loc < δ}, ENNReal.ofReal
          |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ)
            (fun ω => mloc θ.1 ω - mloc θ₀loc ω)|) ≤
        ENNReal.ofReal (C * Real.rpow δ 1) := by
    intro δ hδ hδrloc n
    let δo : ℝ := k * δ
    have hδo : 0 < δo := mul_pos hk hδ
    have hkrloc : k * rloc = ρloc := by
      dsimp [rloc]
      field_simp
    have hδoloc : δo < ρloc := by dsimp [δo]; nlinarith
    have hδoρ₂ : δo < ρ₂ :=
      lt_of_lt_of_le hδoloc (le_trans (min_le_right _ _) (min_le_right _ _))
    have hδoρ : δo ≤ ρ :=
      le_trans hδoloc.le (min_le_left _ _)
    let Z : Ξ → ℝ≥0∞ := fun ξ => supNormOver
      {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δo ∧
        g = fun ω => m θ ω - m θ₀ ω}
      (fun f => empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ) f)
    have hsmall : (fun ξ =>
        ⨆ θ : {θ : Θloc // dist θ θ₀loc < δ}, ENNReal.ofReal
          |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ)
            (fun ω => mloc θ.1 ω - mloc θ₀loc ω)|) ≤ Z := by
      intro ξ
      refine iSup_le fun θ => ?_
      apply le_supNormOver
      refine ⟨T θ.1, ?_, ?_⟩
      · have hdistT : ‖T θ.1 - θ₀‖ = k * dist θ.1 θ₀loc := by
          rw [show T θ.1 - θ₀ = k • (θ.1.1 - θ₀) by simp [T]]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
          congr 1
        rw [hdistT]
        exact mul_lt_mul_of_pos_left θ.property hk
      · funext ω
        change m (T θ.1) ω - m (T θ₀loc) ω = m (T θ.1) ω - m θ₀ ω
        rw [hT0]
    have hZmeas : AEMeasurable Z μ := by
      dsimp [Z]
      exact localizedModulus_aemeasurable P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
        μ X hX_meas (n + 1) δo hδoρ
    calc
      outerExpectation μ (fun ξ =>
          ⨆ θ : {θ : Θloc // dist θ θ₀loc < δ}, ENNReal.ofReal
            |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ)
              (fun ω => mloc θ.1 ω - mloc θ₀loc ω)|) ≤
          outerExpectation μ Z := outerExpectation_mono hsmall
      _ = ∫⁻ ξ, Z ξ ∂μ := outerExpectation_eq_lintegral_of_aemeasurable μ Z hZmeas
      _ ≤ ENNReal.ofReal (C₂ * δo) := hmod δo hδo hδoρ₂ (n + 1)
      _ = ENNReal.ofReal (C * Real.rpow δ 1) := by
        congr 1
        have hrpow₁ : Real.rpow δ 1 = δ := by norm_num [Real.rpow_natCast]
        rw [hrpow₁]
        simp only [C, δo]
        ring
  have hNearMax' : ∀ n ξ,
      empiricalAvg (mloc (θloc n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) ≥
        empiricalAvg (mloc θ₀loc) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) - Rloc n ξ := by
    intro n ξ
    by_cases hp : pre n ξ ∈ Metric.closedBall θ₀ rloc
    · have hTpre : T (⟨pre n ξ, hp⟩ : Θloc) = raw n ξ := by
        simp only [T, pre]
        rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hk.ne', one_smul, add_sub_cancel]
      simp only [θloc, dif_pos hp, Rloc, if_pos hp]
      change empiricalAvg (m (T (⟨pre n ξ, hp⟩ : Θloc))) (n + 1)
          (fun i : Fin (n + 1) => X i.val ξ) ≥
        empiricalAvg (m (T θ₀loc)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) -
          max 0 (empiricalAvg (m θ₀) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) -
            empiricalAvg (m (raw n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ))
      rw [hTpre, hT0]
      linarith [le_max_right 0
        (empiricalAvg (m θ₀) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) -
          empiricalAvg (m (raw n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ))]
    · have hp' : ¬ dist (pre n ξ) θ₀ ≤ rloc := by
        simpa only [Metric.mem_closedBall] using hp
      simp [θloc, Rloc, Metric.mem_closedBall, hp', mloc, hT0]
  have hR_nonneg : ∀ n ξ, 0 ≤ Rloc n ξ := by
    intro n ξ
    simp only [Rloc]
    split <;> positivity
  have hR : IsBoundedInOuterProbScalar μ (fun n ξ =>
      Real.rpow (rateScale 2 1 n) 2 * Rloc n ξ) := by
    have hRord : IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
        Real.rpow (rateScale 2 1 n) 2 * Rloc n ξ) := by
      intro η hη
      obtain ⟨M, hM⟩ := hNearMax η hη
      refine ⟨max M 0, fun n => ?_⟩
      refine le_trans (measureReal_mono (fun ξ hξ => ?_)) (hM (n + 1))
      have hscale : Real.rpow (rateScale 2 1 n) 2 = ((n + 1 : ℕ) : ℝ) := by
        norm_num [rateScale, Real.rpow_natCast]
        rw [← Real.sqrt_eq_rpow]
        exact Real.sq_sqrt (by positivity)
      by_cases hp : pre n ξ ∈ Metric.closedBall θ₀ rloc
      · have hRloc : Rloc n ξ = max 0
            (empiricalAvg (m θ₀) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) -
              empiricalAvg (m (raw n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ)) := by
          have hp' : dist (pre n ξ) θ₀ ≤ rloc := by
            simpa only [Metric.mem_closedBall] using hp
          simp [Rloc, Metric.mem_closedBall, hp']
        change max M 0 < ‖Real.rpow (rateScale 2 1 n) 2 * Rloc n ξ‖ at hξ
        rw [hscale, hRloc] at hξ
        change M < ‖((n + 1 : ℕ) : ℝ) * max 0
          (empiricalAvg (m θ₀) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) -
            empiricalAvg (m (raw n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ))‖
        exact lt_of_le_of_lt (le_max_left M 0) hξ
      · have hp' : ¬ dist (pre n ξ) θ₀ ≤ rloc := by
          simpa only [Metric.mem_closedBall] using hp
        have hRloc : Rloc n ξ = 0 := by simp [Rloc, Metric.mem_closedBall, hp']
        change max M 0 < ‖Real.rpow (rateScale 2 1 n) 2 * Rloc n ξ‖ at hξ
        simp [hRloc] at hξ
    apply isBoundedInOuterProbScalar_of_isBoundedInProb μ _
    exact hRord
  have hcons : TendstoZeroInOuterProbScalar μ (fun n ξ => dist (θloc n ξ) θ₀loc) := by
    intro ε hε
    have hpre_meas : ∀ n, Measurable (pre n) := by
      intro n
      exact measurable_const.add
        (((hθhat_meas (n + 1)).sub measurable_const).const_smul k⁻¹)
    have hlocal_meas : ∀ n, Measurable (fun ξ => dist (θloc n ξ) θ₀loc) := by
      intro n
      have hp : MeasurableSet { ξ | dist (pre n ξ) θ₀ ≤ rloc } :=
        measurableSet_le ((hpre_meas n).dist measurable_const) measurable_const
      have heq : (fun ξ => dist (θloc n ξ) θ₀loc) = fun ξ =>
          if dist (pre n ξ) θ₀ ≤ rloc then dist (pre n ξ) θ₀ else 0 := by
        funext ξ
        by_cases h : dist (pre n ξ) θ₀ ≤ rloc
        · simp only [θloc, Metric.mem_closedBall, h, dif_pos, if_pos]
          rfl
        · simp [θloc, Metric.mem_closedBall, h, θ₀loc]
      rw [heq]
      exact Measurable.ite hp ((hpre_meas n).dist measurable_const) measurable_const
    let A : ℕ → Set Ξ := fun n => {ξ | ε < |dist (θloc n ξ) θ₀loc|}
    let B : ℕ → Set Ξ := fun n => {ξ | k * ε ≤ ‖raw n ξ - θ₀‖}
    have hAB : ∀ n, A n ⊆ B n := by
      intro n ξ hξ
      simp only [A, Set.mem_setOf_eq, abs_of_nonneg dist_nonneg] at hξ
      change k * ε ≤ ‖raw n ξ - θ₀‖
      by_cases hp' : dist (pre n ξ) θ₀ ≤ rloc
      · have hp : pre n ξ ∈ Metric.closedBall θ₀ rloc := by
          simpa only [Metric.mem_closedBall] using hp'
        have hTpre : T (⟨pre n ξ, hp⟩ : Θloc) = raw n ξ := by
          simp only [T, pre]
          rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hk.ne', one_smul,
            add_sub_cancel]
        have hdistT : ‖T (⟨pre n ξ, hp⟩ : Θloc) - θ₀‖ =
            k * dist (⟨pre n ξ, hp⟩ : Θloc) θ₀loc := by
          rw [show T (⟨pre n ξ, hp⟩ : Θloc) - θ₀ = k • (pre n ξ - θ₀) by
            simp [T]]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
          congr 1
        rw [← hTpre, hdistT]
        have : ε < dist (⟨pre n ξ, hp⟩ : Θloc) θ₀loc := by
          simpa [θloc, Metric.mem_closedBall, hp'] using hξ
        exact (mul_lt_mul_of_pos_left this hk).le
      · have : ¬ ε < 0 := not_lt_of_ge hε.le
        exact (this (by simpa [θloc, Metric.mem_closedBall, hp'] using hξ)).elim
    have hBreal : Tendsto (fun n => μ.real (B n)) atTop (nhds 0) := by
      have hs := (hConsistent (k * ε) (mul_pos hk hε)).comp (tendsto_add_atTop_nat 1)
      simpa [B, raw] using! hs
    have hBmeasure : Tendsto (fun n => μ (B n)) atTop (nhds 0) := by
      have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hBreal
      convert hofReal using 1
      · funext n
        simp only [Function.comp_apply]
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
      · simp
    change Tendsto (fun n => μ.outerMeasureStar (A n)) atTop (nhds 0)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBmeasure
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
    rw [outerMeasureStar_eq_measure (measurableSet_lt measurable_const (hlocal_meas n).abs)]
    exact measure_mono (hAB n)
  have houter := mEstimator_rate_of_convergence_outer P μ mloc θ₀loc hmloc_meas
    X θloc Rloc 2 1 C rloc (by norm_num) (by norm_num) hC hrloc
    (fun θ _ => hmloc_int θ) hcurv' hmod' hNearMax' hR_nonneg hR hcons
  have hpre_meas' : ∀ n, Measurable (pre n) := by
    intro n
    exact measurable_const.add
      (((hθhat_meas (n + 1)).sub measurable_const).const_smul k⁻¹)
  have hlocal_meas' : ∀ n, Measurable (fun ξ => dist (θloc n ξ) θ₀loc) := by
    intro n
    have hp : MeasurableSet { ξ | dist (pre n ξ) θ₀ ≤ rloc } :=
      measurableSet_le ((hpre_meas' n).dist measurable_const) measurable_const
    have heq : (fun ξ => dist (θloc n ξ) θ₀loc) = fun ξ =>
        if dist (pre n ξ) θ₀ ≤ rloc then dist (pre n ξ) θ₀ else 0 := by
      funext ξ
      by_cases h : dist (pre n ξ) θ₀ ≤ rloc
      · simp only [θloc, Metric.mem_closedBall, h, dif_pos, if_pos]
        rfl
      · simp [θloc, Metric.mem_closedBall, h, θ₀loc]
    rw [heq]
    exact Measurable.ite hp ((hpre_meas' n).dist measurable_const) measurable_const
  have hshiftTail : ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      μ.real {ξ | M < Real.sqrt (n + 1 : ℝ) * ‖raw n ξ - θ₀‖} ≤ η := by
    intro η hη
    obtain ⟨M, hM⟩ := houter (η / 4) (by positivity)
    have hM_event : ∀ᶠ n in atTop,
        μ.outerMeasureStar {ξ | M < |rateScale 2 1 n * dist (θloc n ξ) θ₀loc|} <
          ENNReal.ofReal (η / 2) := by
      exact Filter.eventually_lt_of_limsup_lt
        (lt_of_le_of_lt hM ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)))
        (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    have hbad_event : ∀ᶠ n in atTop,
        μ.real {ξ | ρloc ≤ ‖raw n ξ - θ₀‖} < η / 2 := by
      have hs := (hConsistent ρloc hρloc).comp (tendsto_add_atTop_nat 1)
      have hs' : Tendsto (fun n => μ.real {ξ | ρloc ≤ ‖raw n ξ - θ₀‖}) atTop
          (nhds 0) := by simpa [raw] using! hs
      exact hs'.eventually (Iio_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hM_event.and hbad_event)
    refine ⟨k * M, N, fun n hn => ?_⟩
    have htail := (hN n hn).1
    have hbad := (hN n hn).2.le
    let Aloc : Set Ξ := {ξ | M < rateScale 2 1 n * dist (θloc n ξ) θ₀loc}
    let Abad : Set Ξ := {ξ | ρloc ≤ ‖raw n ξ - θ₀‖}
    have hAloc_meas : MeasurableSet Aloc := by
      exact measurableSet_lt measurable_const ((hlocal_meas' n).const_mul _)
    have hAloc : μ.real Aloc ≤ η / 2 := by
      have hevent : {ξ | M < |rateScale 2 1 n * dist (θloc n ξ) θ₀loc|} = Aloc := by
        ext ξ
        simp only [Set.mem_setOf_eq, Aloc]
        have hz : 0 ≤ rateScale 2 1 n * dist (θloc n ξ) θ₀loc :=
          mul_nonneg (Real.rpow_nonneg (by positivity) _) dist_nonneg
        rw [abs_of_nonneg hz]
      have hmeasure : μ Aloc < ENNReal.ofReal (η / 2) := by
        rw [← outerMeasureStar_eq_measure hAloc_meas, ← hevent]
        exact htail
      have hofReal : ENNReal.ofReal (μ.real Aloc) < ENNReal.ofReal (η / 2) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact hmeasure
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hofReal)
    have hsub : {ξ | k * M < Real.sqrt (n + 1 : ℝ) * ‖raw n ξ - θ₀‖} ⊆
        Aloc ∪ Abad := by
      intro ξ hξ
      change k * M < Real.sqrt (n + 1 : ℝ) * ‖raw n ξ - θ₀‖ at hξ
      by_cases hp' : dist (pre n ξ) θ₀ ≤ rloc
      · left
        have hp : pre n ξ ∈ Metric.closedBall θ₀ rloc := by
          simpa only [Metric.mem_closedBall] using hp'
        have hTpre : T (⟨pre n ξ, hp⟩ : Θloc) = raw n ξ := by
          simp only [T, pre]
          rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hk.ne', one_smul,
            add_sub_cancel]
        have hdistT : ‖T (⟨pre n ξ, hp⟩ : Θloc) - θ₀‖ =
            k * dist (⟨pre n ξ, hp⟩ : Θloc) θ₀loc := by
          rw [show T (⟨pre n ξ, hp⟩ : Θloc) - θ₀ = k • (pre n ξ - θ₀) by
            simp [T]]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
          congr 1
        have hscale : rateScale 2 1 n = Real.sqrt (n + 1 : ℝ) := by
          norm_num [rateScale]
          rw [Real.sqrt_eq_rpow]
        simp only [Aloc, Set.mem_setOf_eq]
        rw [← hscale, ← hTpre, hdistT] at hξ
        have : k * M < k * (rateScale 2 1 n *
            dist (⟨pre n ξ, hp⟩ : Θloc) θ₀loc) := by nlinarith
        have : M < rateScale 2 1 n *
            dist (⟨pre n ξ, hp⟩ : Θloc) θ₀loc := by nlinarith
        simpa [θloc, Metric.mem_closedBall, hp'] using this
      · right
        simp only [Abad, Set.mem_setOf_eq]
        have hpre_dist : dist (pre n ξ) θ₀ = k⁻¹ * ‖raw n ξ - θ₀‖ := by
          simp only [pre, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hk), dist_eq_norm]
        have hkrloc : k * rloc = ρloc := by
          dsimp [rloc]
          field_simp
        have : rloc < dist (pre n ξ) θ₀ := lt_of_not_ge hp'
        rw [hpre_dist] at this
        have hkinv : k * k⁻¹ = 1 := mul_inv_cancel₀ hk.ne'
        nlinarith
    calc
      μ.real {ξ | k * M < Real.sqrt (n + 1 : ℝ) * ‖raw n ξ - θ₀‖}
          ≤ μ.real (Aloc ∪ Abad) := measureReal_mono hsub
      _ ≤ μ.real Aloc + μ.real Abad := measureReal_union_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add hAloc hbad
      _ = η := by ring
  have hshift : IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt (n + 1 : ℝ) * ‖raw n ξ - θ₀‖) := by
    apply isBoundedInProb_of_eventual_tail μ _
    · intro n
      exact ((hθhat_meas (n + 1)).sub measurable_const).norm.const_mul _
    · intro n ξ
      positivity
    · exact hshiftTail
  intro η hη
  obtain ⟨M, hM⟩ := hshift η hη
  refine ⟨max M 0, fun n => ?_⟩
  cases n with
  | zero => simpa using hη.le
  | succ n =>
      refine le_trans (measureReal_mono (fun ξ hξ => ?_)) (hM n)
      have hnorm : ‖Real.sqrt (n + 1 : ℝ) • (raw n ξ - θ₀)‖ =
          Real.sqrt (n + 1 : ℝ) * ‖raw n ξ - θ₀‖ := by
        rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      change max M 0 < ‖Real.sqrt (((n + 1 : ℕ) : ℝ)) • (raw n ξ - θ₀)‖ at hξ
      norm_num only [Nat.cast_add, Nat.cast_one] at hξ
      rw [hnorm] at hξ
      change M < ‖Real.sqrt (n + 1 : ℝ) * ‖raw n ξ - θ₀‖‖
      rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      exact lt_of_le_of_lt (le_max_left M 0) hξ

/-- **Form with the stronger `o_P(n⁻¹)` near-maximality assumption.**

Its near-maximality input is the stronger `TendstoInProbZero` assumption, which implies the
`O_P(n⁻¹)` assumption of `mEstimator_sqrtn_rate`. -/
theorem mEstimator_sqrtn_rate_of_tendstoInProbZero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ)
    {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hTaylor : ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < ρ →
      |(∫ x, (m θ x - m θ₀ x) ∂P)
          - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫|
        ≤ (c / 4) * ‖θ - θ₀‖ ^ 2)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- The stronger `o_P(n⁻¹)` near-maximality assumption used here.
    (hNearMax : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * max 0 (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)
        - empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
            (fun i : Fin n => X i.val ξ))))
    (hConsistent : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    (hθhat_meas : ∀ n, Measurable (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ))) :
    IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) := by
  classical
  let r : ℝ := ρ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let θclip : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) := fun n xs =>
    if ‖θ_hat n xs - θ₀‖ ≤ r then θ_hat n xs else θ₀
  have hclip_meas : ∀ n, Measurable (fun ξ : Ξ =>
      θclip n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hs : MeasurableSet {ξ : Ξ |
        ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ≤ r} :=
      measurableSet_le ((hθhat_meas n).sub measurable_const).norm measurable_const
    exact Measurable.ite hs (hθhat_meas n) measurable_const
  have hclip_mem : ∀ n ξ,
      θclip n (fun i : Fin n => X i.val ξ) ∈ Metric.closedBall θ₀ r := by
    intro n ξ
    by_cases h : ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ≤ r
    · simp [θclip, h, Metric.mem_closedBall, dist_eq_norm]
    · simp [θclip, h, Metric.mem_closedBall, hr.le]
  let Θr := {θ : EuclideanSpace ℝ (Fin d) // θ ∈ Metric.closedBall θ₀ r}
  have hΘrρ : ∀ θ : Θr, θ.1 ∈ Metric.closedBall θ₀ ρ := by
    intro θ
    exact Metric.closedBall_subset_closedBall (by dsimp [r]; linarith) θ.property
  have hm_cont : ∀ ω, Continuous (fun θ : Θr => m θ.1 ω) := by
    intro ω
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal |menv ω|)
      (fun θ θ' => ?_)).continuous
    rw [Real.dist_eq, Real.coe_toNNReal _ (abs_nonneg _)]
    calc
      |m θ.1 ω - m θ'.1 ω| ≤ menv ω * ‖θ.1 - θ'.1‖ :=
        hLip θ.1 (hΘrρ θ) θ'.1 (hΘrρ θ') ω
      _ ≤ |menv ω| * ‖θ.1 - θ'.1‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ = |menv ω| * dist θ θ' := by congr 1
  have hm_joint : Measurable (Function.uncurry (fun θ : Θr => m θ.1)) :=
    measurable_uncurry_of_continuous_of_measurable hm_cont (fun θ => hm_meas θ.1)
  let slack : ℕ → Ξ → ℝ := fun n ξ =>
    (n : ℝ) * max 0
      (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ) -
        empiricalAvg (m (θclip n (fun i : Fin n => X i.val ξ))) n
          (fun i : Fin n => X i.val ξ))
  have hslack_meas : ∀ n, Measurable (slack n) := by
    intro n
    let qloc : Ξ → Θr := fun ξ =>
      ⟨θclip n (fun i : Fin n => X i.val ξ), hclip_mem n ξ⟩
    have hqloc : Measurable qloc := (hclip_meas n).subtype_mk
    have hbase : Measurable (fun ξ : Ξ =>
        empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ)) := by
      unfold empiricalAvg
      exact (Finset.measurable_sum Finset.univ fun i _ =>
        (hm_meas θ₀).comp (hX_meas i.val)).const_mul _
    have hq : Measurable (fun ξ : Ξ =>
        empiricalAvg (m (θclip n (fun i : Fin n => X i.val ξ))) n
          (fun i : Fin n => X i.val ξ)) := by
      unfold empiricalAvg
      refine (Finset.measurable_sum Finset.univ (fun i _ => ?_)).const_mul _
      exact hm_joint.comp (hqloc.prodMk (hX_meas i.val))
    exact (measurable_const.max (hbase.sub hq)).const_mul _
  have hnear_clip_zero : TendstoInProbZero (fun _ : ℕ => μ) slack := by
    intro ε hε
    refine Metric.tendsto_atTop.mpr fun η hη => ?_
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hNearMax ε hε) (η / 2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp (hConsistent r hr) (η / 2) (by positivity)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hsub : {ξ | ε ≤ ‖slack n ξ‖} ⊆
        {ξ | ε ≤ ‖(n : ℝ) * max 0
          (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ) -
            empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
              (fun i : Fin n => X i.val ξ))‖} ∪
        {ξ | r ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} := by
      intro ξ hξ
      by_cases h : ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ≤ r
      · left
        simpa [slack, θclip, h] using hξ
      · right
        exact (lt_of_not_ge h).le
    have h₁ := hN₁ n (le_trans (le_max_left _ _) hn)
    have h₂ := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h₁ h₂
    calc
      μ.real {ξ | ε ≤ ‖slack n ξ‖}
          ≤ μ.real ({ξ | ε ≤ ‖(n : ℝ) * max 0
            (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ) -
              empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
                (fun i : Fin n => X i.val ξ))‖} ∪
            {ξ | r ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) :=
        measureReal_mono hsub
      _ ≤ μ.real {ξ | ε ≤ ‖(n : ℝ) * max 0
            (empiricalAvg (m θ₀) n (fun i : Fin n => X i.val ξ) -
              empiricalAvg (m (θ_hat n (fun i : Fin n => X i.val ξ))) n
                (fun i : Fin n => X i.val ξ))‖} +
          μ.real {ξ | r ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} :=
        measureReal_union_le _ _
      _ < η := by linarith
  have hnear_clip : IsBoundedInProb (fun _ : ℕ => μ) slack :=
    hnear_clip_zero.isBoundedInProb hslack_meas
  have hcons_clip : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      θclip n (fun i : Fin n => X i.val ξ) - θ₀) := by
    intro ε hε
    refine Metric.tendsto_atTop.mpr fun η hη => ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hConsistent ε hε) η hη
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hsub : {ξ | ε ≤ ‖θclip n (fun i : Fin n => X i.val ξ) - θ₀‖} ⊆
        {ξ | ε ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} := fun ξ hξ => by
      by_cases h : ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ≤ r
      · simpa [θclip, h] using hξ
      · have : ε ≤ 0 := by simpa [θclip, h] using hξ
        exact (not_le_of_gt hε this).elim
    have hle := measureReal_mono (μ := μ) hsub
    have ht := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at ht
    exact lt_of_le_of_lt hle ht
  have hclip_rate := mEstimator_sqrtn_rate P m θ₀ V hc hVneg hm_meas menv hmenv hmenv_meas
    ρ hρ hLip hTaylor θclip μ X hX_meas hX_indep hX_id hX_law
    hnear_clip hcons_clip hclip_meas
  have horig_tail : ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      μ.real {ξ | M < Real.sqrt n *
        ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} ≤ η := by
    intro η hη
    obtain ⟨M, hM⟩ := hclip_rate (η / 2) (by positivity)
    have hbad_event : ∀ᶠ n in atTop,
        μ.real {ξ | r ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} < η / 2 :=
      (hConsistent r hr).eventually (Iio_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbad_event
    refine ⟨M, N, fun n hn => ?_⟩
    have hsub : {ξ | M < Real.sqrt n *
        ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} ⊆
        {ξ | M < ‖Real.sqrt n •
          (θclip n (fun i : Fin n => X i.val ξ) - θ₀)‖} ∪
        {ξ | r ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} := by
      intro ξ hξ
      by_cases h : ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ≤ r
      · left
        simpa [θclip, h, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hξ
      · right
        exact (lt_of_not_ge h).le
    calc
      μ.real {ξ | M < Real.sqrt n *
          ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}
          ≤ μ.real ({ξ | M < ‖Real.sqrt n •
              (θclip n (fun i : Fin n => X i.val ξ) - θ₀)‖} ∪
            {ξ | r ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) :=
        measureReal_mono hsub
      _ ≤ μ.real {ξ | M < ‖Real.sqrt n •
            (θclip n (fun i : Fin n => X i.val ξ) - θ₀)‖} +
          μ.real {ξ | r ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} :=
        measureReal_union_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add (hM n) (hN n hn).le
      _ = η := by ring
  have hscalar : IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) := by
    apply isBoundedInProb_of_eventual_tail μ _
    · intro n
      exact ((hθhat_meas n).sub measurable_const).norm.const_mul _
    · intro n ξ
      positivity
    · exact horig_tail
  intro η hη
  obtain ⟨M, hM⟩ := hscalar η hη
  refine ⟨M, fun n => ?_⟩
  refine le_of_eq_of_le ?_ (hM n)
  congr 1
  ext ξ
  simp only [Set.mem_setOf_eq]
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]

end AsymptoticStatistics.MEstimator
