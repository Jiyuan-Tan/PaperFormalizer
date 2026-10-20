module
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import StatLean.AsymptoticStatistics.ForMathlib.Slutsky
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

/-!
# The delta method (van der Vaart, *Asymptotic Statistics*, Theorem 3.1)

If a statistic satisfies `sqn k • (T k − θ₀) ⇝ ν` for a scale `sqn k → ∞`, and `φ` is
(Fréchet-)differentiable at `θ₀` with derivative `φ'`, then
`sqn k • (φ (T k) − φ θ₀) ⇝ ν.map φ'`, and moreover the linearization error
`sqn k • (φ (T k) − φ θ₀ − φ' (T k − θ₀))` tends to `0` in probability.

Stated at the project's varying-base level (`Ω : ℕ → Type*`, laws as pushforwards). The
domain `E` and codomain `F` are general normed `ℝ`-spaces; van der Vaart's `ℝᵏ → ℝᵐ` is
the instance `E := EuclideanSpace ℝ (Fin k)`, `F := EuclideanSpace ℝ (Fin m)`.

## Structure

* `delta_method_remainder` — vdV **Lemma 2.12** specialized to `p = 1`: the stochastic
  first-order Taylor remainder. Given consistency `T k → θ₀` in probability and
  tightness `sqn k • (T k − θ₀) = O_P(1)`, the scaled Fréchet remainder `→ₚ 0`. **The one
  genuinely new mathematical brick.**
* `delta_method` — the main theorem. Consistency and tightness are **derived** from the weak
  convergence hypothesis `h_wc` (Prokhorov, via `isBoundedInProb_of_weakConverges` and
  `tendstoInProbZero_of_isBoundedInProb_smul`); they are *not* free hypotheses. Assembly:
  push the source law through the linear `φ'` (`WeakConverges.map`), then bridge to the
  target law by `WeakConverges.slutsky_of_tendstoInMeasure_dist`, absorbing the remainder.
-/

open MeasureTheory Filter Topology Set

namespace AsymptoticStatistics

variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]

/-- **vdV Lemma 2.12 (`p = 1`): the stochastic first-order Taylor remainder.**

Let `φ` be Fréchet-differentiable at `θ₀` with derivative `φ'`. If `T k → θ₀` in
probability (`h_cons`) and `sqn k • (T k − θ₀)` is bounded in probability (`h_OP`), then
the scaled linearization error `sqn k • (φ (T k) − φ θ₀ − φ' (T k − θ₀))` tends to `0` in
probability.

Proof (the ε-δ crux): differentiability gives, for every `c > 0`, a `δ > 0` with
`‖φ x − φ θ₀ − φ' (x − θ₀)‖ ≤ c ‖x − θ₀‖` whenever `‖x − θ₀‖ < δ`
(`HasFDerivAt.isLittleO`). On the event `{‖T k − θ₀‖ < δ} ∩ {‖sqn k • (T k − θ₀)‖ ≤ M}`
(with `M` from `h_OP`, `c := ε/(2M)`) the scaled remainder is `≤ ε/2`; the complementary
mass splits as `{δ ≤ ‖T k − θ₀‖}` (→ 0 by `h_cons`) plus the tight tail (≤ ε by `h_OP`). -/
theorem delta_method_remainder
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {T : ∀ k, Ω k → E} {φ : E → F} {φ' : E →L[ℝ] F} {θ₀ : E}
    (hφ : HasFDerivAt φ φ' θ₀)
    {sqn : ℕ → ℝ}
    (h_cons : TendstoInProbZero P (fun k ω => T k ω - θ₀))
    (h_OP : IsBoundedInProb P (fun k ω => sqn k • (T k ω - θ₀))) :
    TendstoInProbZero P
      (fun k ω => sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))) := by
  intro ε hε
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  have hη2 : (0:ℝ) < η / 2 := by positivity
  -- tightness threshold `M > 0`
  obtain ⟨M₀, hM₀⟩ := h_OP (η / 2) hη2
  set M : ℝ := max M₀ 1 with hM_def
  have hM_pos : 0 < M := lt_of_lt_of_le one_pos (le_max_right M₀ 1)
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have hMbound : ∀ k, (P k).real {ω | M < ‖sqn k • (T k ω - θ₀)‖} ≤ η / 2 := fun k =>
    le_trans (measureReal_mono fun ω hω => lt_of_le_of_lt (le_max_left M₀ 1) hω) (hM₀ k)
  -- little-o extraction with `c := ε / (2M)`
  have hc : (0:ℝ) < ε / (2 * M) := by positivity
  have hcM : ε / (2 * M) * M = ε / 2 := by field_simp
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.eventually_nhds_iff.mp ((Asymptotics.isLittleO_iff.mp hφ.isLittleO) hc)
  -- consistency gives an index past which the `{δ ≤ ‖T−θ₀‖}` mass is `< η/2`
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_cons δ hδ_pos) (η / 2) hη2
  refine ⟨N, fun k hk => ?_⟩
  -- the bad event splits into the two controlled events
  have hsub : {ω | ε ≤ ‖sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))‖}
      ⊆ {ω | δ ≤ ‖T k ω - θ₀‖} ∪ {ω | M < ‖sqn k • (T k ω - θ₀)‖} := by
    intro ω hω
    by_cases hd : δ ≤ ‖T k ω - θ₀‖
    · exact Or.inl hd
    · refine Or.inr ?_
      show M < ‖sqn k • (T k ω - θ₀)‖
      push_neg at hd
      by_contra hM'
      push_neg at hM'
      have hxδ : dist (T k ω) θ₀ < δ := by rwa [dist_eq_norm]
      have hR : ‖φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀)‖ ≤ (ε / (2 * M)) * ‖T k ω - θ₀‖ :=
        hδ hxδ
      have hchain : ‖sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))‖ ≤ ε / 2 := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |sqn k| * ‖φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀)‖
            ≤ |sqn k| * ((ε / (2 * M)) * ‖T k ω - θ₀‖) :=
              mul_le_mul_of_nonneg_left hR (abs_nonneg _)
          _ = (ε / (2 * M)) * (|sqn k| * ‖T k ω - θ₀‖) := by ring
          _ = (ε / (2 * M)) * ‖sqn k • (T k ω - θ₀)‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ (ε / (2 * M)) * M := mul_le_mul_of_nonneg_left hM' (le_of_lt hc)
          _ = ε / 2 := hcM
      linarith [le_trans hω hchain]
  have hunion : (P k).real {ω | ε ≤ ‖sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))‖}
      ≤ (P k).real {ω | δ ≤ ‖T k ω - θ₀‖}
        + (P k).real {ω | M < ‖sqn k • (T k ω - θ₀)‖} :=
    le_trans (measureReal_mono hsub) (measureReal_union_le _ _)
  have hcons_k : (P k).real {ω | δ ≤ ‖T k ω - θ₀‖} < η / 2 := by
    have := hN k hk
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc (P k).real {ω | ε ≤ ‖sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))‖}
      ≤ (P k).real {ω | δ ≤ ‖T k ω - θ₀‖}
        + (P k).real {ω | M < ‖sqn k • (T k ω - θ₀)‖} := hunion
    _ < η / 2 + η / 2 := add_lt_add_of_lt_of_le hcons_k (hMbound k)
    _ = η := by ring

/-- **The delta method — van der Vaart, Theorem 3.1.**

Let `T k : Ω k → E` be a (measurable) statistic, `φ : E → F` (measurably) differentiable
at `θ₀` with derivative `φ'`, and `sqn k → ∞`. If the rescaled centered statistic
`sqn k • (T k − θ₀)` has laws converging weakly to a probability measure `ν`, then:

* `sqn k • (φ (T k) − φ θ₀)` has laws converging weakly to `ν.map φ'`, and
* the linearization error `sqn k • (φ (T k) − φ θ₀ − φ' (T k − θ₀)) →ₚ 0` (the
  "moreover" clause of Theorem 3.1).

Consistency `T k → θ₀` and tightness `sqn k • (T k − θ₀) = O_P(1)` are **derived** from
`h_wc` (they are forced by the setup, not free inputs). -/
theorem delta_method
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
      [SecondCountableTopology E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
      [SecondCountableTopology F] [Nonempty F]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {T : ∀ k, Ω k → E} (hT_meas : ∀ k, Measurable (T k))
    {φ : E → F} {φ' : E →L[ℝ] F} {θ₀ : E}
    (hφ : HasFDerivAt φ φ' θ₀)
    (hφT_meas : ∀ k, AEMeasurable (fun ω => φ (T k ω)) (P k))
    {sqn : ℕ → ℝ} (h_sqn : Tendsto sqn atTop atTop)
    {ν : Measure E} [IsProbabilityMeasure ν]
    (h_wc : WeakConverges (fun k => (P k).map (fun ω => sqn k • (T k ω - θ₀))) ν) :
    WeakConverges (fun k => (P k).map (fun ω => sqn k • (φ (T k ω) - φ θ₀))) (ν.map φ')
      ∧ TendstoInProbZero P
          (fun k ω => sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))) := by
  -- measurability of the rescaled centered statistic
  have hZ_meas : ∀ k, Measurable (fun ω => sqn k • (T k ω - θ₀)) := fun k =>
    ((hT_meas k).sub measurable_const).const_smul (sqn k)
  -- (1) tightness O_P(1) and (2) consistency, both derived from `h_wc`
  have h_OP : IsBoundedInProb P (fun k ω => sqn k • (T k ω - θ₀)) :=
    isBoundedInProb_of_weakConverges hZ_meas h_wc
  have h_cons : TendstoInProbZero P (fun k ω => T k ω - θ₀) :=
    tendstoInProbZero_of_isBoundedInProb_smul (Z := fun k ω => T k ω - θ₀) h_sqn h_OP
  -- (3) the linearization error (the `moreover` clause) — second conjunct
  have h_rem : TendstoInProbZero P
      (fun k ω => sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))) :=
    delta_method_remainder hφ h_cons h_OP
  -- (4) push the source law through the linear part `φ'`
  have hlaw : ∀ k, (P k).map (fun ω => sqn k • φ' (T k ω - θ₀))
      = ((P k).map (fun ω => sqn k • (T k ω - θ₀))).map φ' := by
    intro k
    rw [Measure.map_map φ'.continuous.measurable (hZ_meas k)]
    congr 1
    funext ω
    rw [Function.comp_apply]
    exact (φ'.map_smul (sqn k) (T k ω - θ₀)).symm
  have h_lin : WeakConverges
      (fun k => (P k).map (fun ω => sqn k • φ' (T k ω - θ₀))) (ν.map φ') := by
    have hmap := h_wc.map φ'.continuous φ'.continuous.measurable
    simpa only [hlaw] using hmap
  -- (5) Slutsky bridge: the target law differs from the linear law by the remainder
  haveI : IsProbabilityMeasure (ν.map φ') :=
    Measure.isProbabilityMeasure_map φ'.continuous.measurable.aemeasurable
  have hXmeas : ∀ k, AEMeasurable (fun ω => sqn k • φ' (T k ω - θ₀)) (P k) := fun k =>
    ((φ'.continuous.measurable.comp ((hT_meas k).sub measurable_const)).const_smul
      (sqn k)).aemeasurable
  have hYmeas : ∀ k, AEMeasurable (fun ω => sqn k • (φ (T k ω) - φ θ₀)) (P k) := fun k =>
    ((hφT_meas k).sub aemeasurable_const).const_smul (sqn k)
  have h_weak : WeakConverges
      (fun k => (P k).map (fun ω => sqn k • (φ (T k ω) - φ θ₀))) (ν.map φ') := by
    refine WeakConverges.slutsky_of_tendstoInMeasure_dist hXmeas hYmeas h_lin ?_
    intro ε hε
    have hset : ∀ k, {ω | ε ≤ dist (sqn k • φ' (T k ω - θ₀))
          (sqn k • (φ (T k ω) - φ θ₀))}
        = {ω | ε ≤ ‖sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))‖} := by
      intro k
      ext ω
      simp only [Set.mem_setOf_eq]
      have hdiff : sqn k • φ' (T k ω - θ₀) - sqn k • (φ (T k ω) - φ θ₀)
          = -(sqn k • (φ (T k ω) - φ θ₀ - φ' (T k ω - θ₀))) := by
        rw [← smul_sub, ← smul_neg]; congr 1; abel
      rw [dist_eq_norm, hdiff, norm_neg]
    simp only [hset]
    exact h_rem ε hε
  exact ⟨h_weak, h_rem⟩

end AsymptoticStatistics
