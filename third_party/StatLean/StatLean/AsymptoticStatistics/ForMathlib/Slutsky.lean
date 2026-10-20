module
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

@[expose] public section

/-!
# Slutsky perturbation for `WeakConverges`

Slutsky's theorem in the "close-in-probability" form, stated at the project's
pushforward-measure level (`WeakConverges`). Given two sequences of random variables
`X n, Y n : Ω n → E` (base measures `P n` varying in both space and total mass), if

* the push-forward laws `(P n).map (X n)` weakly converge to `ν`, and
* the pair `dist (X n) (Y n)` converges to `0` in `P n`-probability,

then `(P n).map (Y n)` weakly converges to `ν` as well. This is the "varying base"
version — Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub` only covers a
single fixed base measure on a single space.

Used by Theorem 7.10 Step 3 to absorb the `LAN_expansion_iii` residual (an `o_P(1)`
under `P^n_{θ₀}`) into the joint weak convergence of `(T_n, log-likelihood)`.

The proof mirrors Mathlib's: reduce to Lipschitz test functions via
`tendsto_iff_forall_lipschitz_integral_tendsto`, then split `|F(Y) − F(X)|` on
`{dist < ε/2} ∪ {dist ≥ ε/2}` using the Lipschitz bound and the sup norm.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- **Slutsky-by-distance for `WeakConverges`**: if `(P n).map (X n) ⇝ ν` and
`dist (X n) (Y n) →_P 0` under `P n`, then `(P n).map (Y n) ⇝ ν`.

Varying-base version (each `P n` lives on its own space `Ω n`). Adapted from
`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`, which is stated for a
single base `μ''` on a normed additive group. The three-piece estimate
`|∫F Y − ∫F ν| ≤ L·(ε/2) + 2·‖F‖∞ · P{dist ≥ ε/2} + |∫F X − ∫F ν|` carries over
without change; we use `dist` in place of `‖·-·‖`. -/
theorem WeakConverges.slutsky_of_tendstoInMeasure_dist
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [Nonempty E]
    [OpensMeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Ω n → E} {ν : Measure E} [IsProbabilityMeasure ν]
    (hX_meas : ∀ n, AEMeasurable (X n) (P n))
    (hY_meas : ∀ n, AEMeasurable (Y n) (P n))
    (hX : WeakConverges (fun n => (P n).map (X n)) ν)
    (hDist : ∀ ε > 0,
        Tendsto (fun n => (P n).real {ω | ε ≤ dist (X n ω) (Y n ω)}) atTop (𝓝 0)) :
    WeakConverges (fun n => (P n).map (Y n)) ν := by
  classical
  haveI h_prob_X : ∀ n, IsProbabilityMeasure ((P n).map (X n)) := fun n =>
    Measure.isProbabilityMeasure_map (hX_meas n)
  haveI h_prob_Y : ∀ n, IsProbabilityMeasure ((P n).map (Y n)) := fun n =>
    Measure.isProbabilityMeasure_map (hY_meas n)
  -- Package the pushforwards as `ProbabilityMeasure` so we can apply the Lipschitz
  -- characterisation of weak convergence. Use local `let`-bindings to keep the
  -- subtype folded under `rw [tendsto_iff_forall_lipschitz_integral_tendsto]`.
  let pX : ℕ → ProbabilityMeasure E := fun n => ⟨(P n).map (X n), h_prob_X n⟩
  let pY : ℕ → ProbabilityMeasure E := fun n => ⟨(P n).map (Y n), h_prob_Y n⟩
  let pν : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have h_coe_X : ∀ n, (pX n : Measure E) = (P n).map (X n) := fun _ => rfl
  have h_coe_Y : ∀ n, (pY n : Measure E) = (P n).map (Y n) := fun _ => rfl
  have h_coe_ν : (pν : Measure E) = ν := rfl
  -- `hX` rewrites to `Tendsto pX atTop (𝓝 pν)`.
  have h_probmeas_tendsto : Tendsto pX atTop (𝓝 pν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simp_rw [h_coe_X, h_coe_ν]
    exact hX f
  -- Conclude via the same bridge applied to `pY`.
  suffices h_target : Tendsto pY atTop (𝓝 pν) by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h_target
    intro f
    simpa [h_coe_Y, h_coe_ν] using h_target f
  -- Reduce to Lipschitz test functions.
  rw [tendsto_iff_forall_lipschitz_integral_tendsto] at h_probmeas_tendsto ⊢
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  simp_rw [h_coe_X, h_coe_ν] at h_probmeas_tendsto
  simp_rw [h_coe_Y, h_coe_ν]
  let x₀ : E := Classical.arbitrary E
  -- Bounded Lipschitz test function. Degenerate L = 0 ⇒ F constant.
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul, probReal_univ]
    exact tendsto_const_nhds
  -- Now `F` is `L`-Lipschitz with `L > 0`; use a classic three-piece ε-δ estimate.
  have hF_cont : Continuous F := hF_lip.continuous
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in atTop, |∫ ω, F ω ∂((P n).map (Y n))
      - ∫ ω, F ω ∂ν| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- Step A: transfer the integrals from pushforward to base via `integral_map`.
  have h_push_X : ∀ n, ∫ ω, F ω ∂((P n).map (X n)) = ∫ ω, F (X n ω) ∂(P n) := fun n =>
    integral_map (hX_meas n) hF_cont.aestronglyMeasurable
  have h_push_Y : ∀ n, ∫ ω, F ω ∂((P n).map (Y n)) = ∫ ω, F (Y n ω) ∂(P n) := fun n =>
    integral_map (hY_meas n) hF_cont.aestronglyMeasurable
  -- Step B: the three-piece inequality — bound `|∫F(Y) − ∫F(ν)|` in terms of
  -- `|∫F(X) − ∫F(ν)|` plus Lipschitz-residual and tail contributions.
  have h_le : ∀ n, |∫ ω, F ω ∂((P n).map (Y n)) - ∫ ω, F ω ∂ν|
      ≤ L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
        + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν| := by
    intro n
    refine (abs_sub_le (∫ ω, F ω ∂((P n).map (Y n))) (∫ ω, F ω ∂((P n).map (X n)))
      (∫ ω, F ω ∂ν)).trans ?_
    gcongr
    -- The first piece: `|∫F(Y) − ∫F(X)| ≤ L·(ε/2) + M·P{dist ≥ ε/2}`.
    rw [h_push_Y, h_push_X]
    have h_int_X : Integrable (fun ω => F (X n ω)) (P n) := by
      refine Integrable.of_bound (hF_cont.aemeasurable.comp_aemeasurable (hX_meas n)
        |>.aestronglyMeasurable) (‖F x₀‖ + M) ?_
      refine ae_of_all _ (fun a => ?_)
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans (hF_bounded _ _)
    have h_int_Y : Integrable (fun ω => F (Y n ω)) (P n) := by
      refine Integrable.of_bound (hF_cont.aemeasurable.comp_aemeasurable (hY_meas n)
        |>.aestronglyMeasurable) (‖F x₀‖ + M) ?_
      refine ae_of_all _ (fun a => ?_)
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans (hF_bounded _ _)
    have h_int_sub : Integrable (fun ω => ‖F (Y n ω) - F (X n ω)‖) (P n) :=
      (h_int_Y.sub h_int_X).norm
    rw [← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ ω, F (Y n ω) - F (X n ω) ∂(P n)‖
        ≤ ∫ ω, ‖F (Y n ω) - F (X n ω)‖ ∂(P n) := norm_integral_le_integral_norm _
      _ = ∫ ω in {a | dist (X n a) (Y n a) < ε / 2},
            ‖F (Y n ω) - F (X n ω)‖ ∂(P n)
          + ∫ ω in {a | ε / 2 ≤ dist (X n a) (Y n a)},
            ‖F (Y n ω) - F (X n ω)‖ ∂(P n) := by
          symm
          simp_rw [← not_lt]
          refine integral_add_compl₀ ?_ h_int_sub
          refine nullMeasurableSet_lt ?_ (by fun_prop)
          exact (hX_meas n).dist (hY_meas n)
      _ ≤ ∫ ω in {a | dist (X n a) (Y n a) < ε / 2}, L * (ε / 2) ∂(P n)
          + ∫ ω in {a | ε / 2 ≤ dist (X n a) (Y n a)}, M ∂(P n) := by
          gcongr ?_ + ?_
          · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_
              (fun ω hω => ?_)
            · refine nullMeasurableSet_lt ?_ (by fun_prop)
              exact (hX_meas n).dist (hY_meas n)
            · simp only [Set.mem_setOf_eq] at hω
              have h_le : dist (Y n ω) (X n ω) ≤ ε / 2 := by
                rw [dist_comm]; exact hω.le
              have := hF_lip.dist_le_mul_of_le h_le
              simpa [Real.dist_eq, Real.norm_eq_abs] using this
          · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const (fun a => ?_)
            rw [← dist_eq_norm]
            convert hF_bounded _ _
      _ = L * (ε / 2) * (P n).real {a | dist (X n a) (Y n a) < ε / 2}
          + M * (P n).real {a | ε / 2 ≤ dist (X n a) (Y n a)} := by
          simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
            Set.univ_inter, smul_eq_mul]
          ring
      _ ≤ L * (ε / 2)
          + M * (P n).real {a | ε / 2 ≤ dist (X n a) (Y n a)} := by
          rw [mul_assoc]
          gcongr
          grw [measureReal_le_one, mul_one]
  -- Step C: the RHS tends to `L * (ε / 2) + 0 + 0`; we win because `L * (ε / 2) < L * ε`.
  have h_tendsto : Tendsto (fun n =>
      L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
        + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν|)
      atTop (𝓝 (L * (ε / 2))) := by
    suffices Tendsto (fun n =>
        L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
          + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν|)
        atTop (𝓝 (L * (ε / 2) + M * 0 + 0)) by simpa using this
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · exact tendsto_const_nhds
    · exact hDist (ε / 2) (by positivity)
    · -- `|∫F(X) − ∫F(ν)| → 0` from the assumed weak convergence.
      have := h_probmeas_tendsto F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
      simp_rw [Metric.tendsto_nhds, Real.dist_eq] at this
      rw [Metric.tendsto_nhds]
      intro δ hδ
      filter_upwards [this δ hδ] with n hn
      rw [Real.dist_eq, sub_zero, abs_abs]
      exact hn
  have h_strict : (L : ℝ) * (ε / 2) < L * ε := by
    have : (0 : ℝ) < L * (ε / 2) := by positivity
    linarith [this]
  have := h_tendsto.eventually_lt_const h_strict
  filter_upwards [this] with n hn
  exact lt_of_le_of_lt (h_le n) hn

end AsymptoticStatistics
