module
public import StatLean.ComputationalStatistics.Core.Defs
public import StatLean.ComputationalStatistics.ForMathlib.PiMoments
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Importance sampling

Importance sampling is the change-of-measure method of Monte Carlo (ECS §2.6):
to estimate `∫ g dP`, sample from a proposal `Q` with `P ≪ Q` and average
`g·w` where `w = dP/dQ` is the importance weight.

* `importanceWeight` — the weight `w = (dP/dQ).toReal`;
* `integral_importanceWeight_mul` — the change-of-measure identity
  `∫ g·w dQ = ∫ g dP` (a textbook-named wrapper of the pinned Mathlib
  `MeasureTheory.integral_toReal_rnDeriv_mul`, per the load-don't-reprove rule);
* `importanceSampling_unbiased`, `importanceSampling_variance` — moments of the
  importance-sampling estimator `(1/n)·Σᵢ g(Xᵢ)·w(Xᵢ)`, `Xᵢ ~ Q` i.i.d.
  (ECS §2.6, eq. (2.11));
* `lintegral_sq_le_lintegral_sq_div`, `lintegral_sq_div_optimalImportance` —
  the optimal-importance-function bound `(∫ f dν)² ≤ ∫ f²/p dν` over densities
  `p`, with equality at `p* = f/∫f` (ECS §2.6, the Jensen-inequality display):
  the mathematical content of "sample more heavily where `f` is large".

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.6 (reducing variance; importance sampling,
eq. (2.11) and the optimal-density display on p. 60).  (`ECS §2.6`.)

**Proof formalization notes.**

* The estimator statements are over the canonical product `Measure.pi
  (fun _ : Fin n => Q)`; they are `PiMoments` lemmas at the integrand `g·w`.
* Absolute continuity `P ≪ Q` is the book's support condition ("the majorizing
  density must not vanish where the target is positive"); without it the
  estimator is not even well-posed, so it appears as a hypothesis, not a
  conclusion.
* The optimal-importance bound is stated in `ℝ≥0∞` with the `0/0 = 0`, `x/0 = ∞`
  junk conventions, which make it hypothesis-free beyond measurability and
  `∫⁻ p dν = 1`: where `p` vanishes but `f` does not, the right-hand side is
  `∞` and the bound is trivial.  The optimizer `p* = f/∫⁻f` achieves equality
  for every measurable `f`, including the degenerate cases `∫⁻ f ∈ {0, ∞}`.

**Bibliographic comments.** Importance sampling goes back to Kahn–Marshall
(*J. Oper. Res. Soc. Amer.* **1** (1953), 263–278); the optimal-density result
is Rubinstein's Theorem 4.3.1 (*Simulation and the Monte Carlo Method*, Wiley,
1981) and appears in ECS §2.6 via Jensen's inequality.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P Q : Measure 𝓧}

/-- The **importance weight** `w = dP/dQ` (ECS §2.6): the Radon–Nikodym
derivative of the target with respect to the proposal, as a real function.
Edge behaviour: `w = 0` wherever the derivative is infinite (a `Q`-null set
when `P ≪ Q` and `P` is finite). -/
noncomputable def importanceWeight (P Q : Measure 𝓧) : 𝓧 → ℝ :=
  fun z => (P.rnDeriv Q z).toReal

/-- **The importance-sampling identity** (ECS §2.6, p. 60 display):
`∫ g·(dP/dQ) dQ = ∫ g dP` under `P ≪ Q`.  Wrapper of the pinned Mathlib
`integral_toReal_rnDeriv_mul`. -/
theorem integral_importanceWeight_mul [SigmaFinite P] [SigmaFinite Q] {g : 𝓧 → ℝ}
    -- USER-INPUT: the target is dominated by the proposal; ECS §2.6
    (hPQ : P ≪ Q) :
    ∫ z, g z * importanceWeight P Q z ∂Q = ∫ z, g z ∂P := by
  rw [← MeasureTheory.integral_toReal_rnDeriv_mul (μ := P) (ν := Q) hPQ (f := g)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)

/-- **Unbiasedness of the importance-sampling estimator** (ECS §2.6,
eq. (2.11)): sampling i.i.d. from the proposal `Q` and averaging `g·w` has
expectation `∫ g dP`. -/
theorem importanceSampling_unbiased [IsProbabilityMeasure Q] [SigmaFinite P]
    {n : ℕ} [NeZero n] {g : 𝓧 → ℝ}
    -- USER-INPUT: the target is dominated by the proposal; ECS §2.6
    (hPQ : P ≪ Q)
    -- USER-INPUT: the weighted integrand has a finite first moment under the proposal; ECS §2.6
    (hgw : Integrable (fun z => g z * importanceWeight P Q z) Q) :
    ∫ x, mcEstimate (fun z => g z * importanceWeight P Q z) x
        ∂(Measure.pi fun _ : Fin n => Q)
      = ∫ z, g z ∂P := by
  exact (integral_avg_eval_pi (P := Q) hgw).trans (integral_importanceWeight_mul hPQ)

/-- **Variance of the importance-sampling estimator** (ECS §2.6):
`Var(Î_IS) = Var_Q(g·w)/n`. -/
theorem importanceSampling_variance [IsProbabilityMeasure Q] {n : ℕ} [NeZero n]
    {g : 𝓧 → ℝ}
    -- USER-INPUT: the weighted integrand has a finite second moment under the proposal; ECS §2.6
    (hgw : MemLp (fun z => g z * importanceWeight P Q z) 2 Q) :
    variance (mcEstimate fun z => g z * importanceWeight P Q z)
        (Measure.pi fun _ : Fin n => Q)
      = variance (fun z => g z * importanceWeight P Q z) Q / n := by
  have hfun : (mcEstimate fun z => g z * importanceWeight P Q z)
      = fun x : Fin n → 𝓧 => (n : ℝ)⁻¹ * ∑ i, (fun z => g z * importanceWeight P Q z) (x i) :=
    rfl
  rw [hfun]
  exact variance_avg_eval_pi (P := Q) (g := fun z => g z * importanceWeight P Q z) hgw

variable {ν : Measure 𝓧}

/-- `(x^{1/2})^2 = x` in `ℝ≥0∞`, in the `rpow`/`rpow` form produced by Hölder. -/
private lemma rpow_half_rpow_two (x : ℝ≥0∞) : (x ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- `(x^{1/2})^2 = x` in `ℝ≥0∞`, with a natural-number outer power. -/
private lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) = x := by
  rw [← ENNReal.rpow_natCast (x ^ ((2 : ℝ)⁻¹)) 2, ← ENNReal.rpow_mul]
  norm_num

/-- **The optimal-importance-function lower bound** (ECS §2.6, p. 60): for any
importance density `p` with `∫⁻ p dν = 1`, the second moment of the weighted
integrand satisfies `(∫⁻ f dν)² ≤ ∫⁻ f²/p dν`.  Stated in `ℝ≥0∞`, so no
support condition is needed: where `p = 0 < f` the right-hand side is `∞`. -/
theorem lintegral_sq_le_lintegral_sq_div {f p : 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the integrand (regularity)
    (hf : Measurable f)
    -- LEAN-ONLY: measurability of the importance density (regularity)
    (hp : Measurable p)
    -- USER-INPUT: `p` is a probability density w.r.t. the base measure; ECS §2.6
    (hp1 : ∫⁻ z, p z ∂ν = 1) :
    (∫⁻ z, f z ∂ν) ^ 2 ≤ ∫⁻ z, f z ^ 2 / p z ∂ν := by
  have hmeas : Measurable fun z => f z ^ 2 / p z := (hf.pow_const 2).div hp
  by_cases hE : ν {z | p z = 0 ∧ f z ≠ 0} = 0
  · -- The genuine case: `p` vanishes only where `f` does, so Cauchy–Schwarz applies.
    have hpfin : ∀ᵐ z ∂ν, p z ≠ ∞ := by
      filter_upwards [ae_lt_top hp (by rw [hp1]; exact ENNReal.one_ne_top)] with z hz
      exact hz.ne
    have hEz : ∀ᵐ z ∂ν, p z = 0 → f z = 0 := by
      rw [ae_iff]
      refine Eq.trans (congrArg ν ?_) hE
      ext z
      simp only [Set.mem_setOf_eq, Classical.not_imp]
    -- The pointwise Cauchy–Schwarz splitting `f = (f²/p)^{1/2} · p^{1/2}`.
    have key : ∀ᵐ z ∂ν,
        f z = (f z ^ 2 / p z) ^ ((2 : ℝ)⁻¹) * (p z) ^ ((2 : ℝ)⁻¹) := by
      filter_upwards [hpfin, hEz] with z h1 h2
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.div_mul_cancel' (fun h => by simp [h2 h]) (fun h => absurd h h1)]
      rw [← ENNReal.rpow_natCast (f z) 2, ← ENNReal.rpow_mul]
      norm_num
    have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
      (p := (2 : ℝ)) (q := (2 : ℝ)) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (f := fun z => (f z ^ 2 / p z) ^ ((2 : ℝ)⁻¹))
      (g := fun z => (p z) ^ ((2 : ℝ)⁻¹))
      ((hmeas.pow_const _).aemeasurable) ((hp.pow_const _).aemeasurable)
    simp only [Pi.mul_apply, rpow_half_rpow_two] at hCS
    rw [hp1, ENNReal.one_rpow, mul_one] at hCS
    have hlin : ∫⁻ z, f z ∂ν ≤ (∫⁻ z, f z ^ 2 / p z ∂ν) ^ ((2 : ℝ)⁻¹) := by
      refine le_trans (le_of_eq (lintegral_congr_ae key)) ?_
      simpa only [one_div] using hCS
    calc (∫⁻ z, f z ∂ν) ^ 2
        ≤ ((∫⁻ z, f z ^ 2 / p z ∂ν) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) := by gcongr
      _ = ∫⁻ z, f z ^ 2 / p z ∂ν := rpow_half_sq _
  · -- `p` vanishes on a positive-measure set where `f` does not: the bound is `∞`.
    have : ∫⁻ z, f z ^ 2 / p z ∂ν = ∞ := by
      refine lintegral_eq_top_of_measure_eq_top_ne_zero hmeas.aemeasurable fun h => hE ?_
      refine measure_mono_null (fun z hz => ?_) h
      simp only [Set.mem_setOf_eq] at hz ⊢
      rw [hz.1, ENNReal.div_zero (pow_ne_zero 2 hz.2)]
    rw [this]
    exact le_top

/-- **The optimal importance function achieves the bound** (ECS §2.6, p. 60):
at `p* = f / ∫⁻ f dν`, the second moment equals `(∫⁻ f dν)²`.  Holds for every
measurable `f`, including the degenerate cases `∫⁻ f ∈ {0, ∞}`, by the `ℝ≥0∞`
division conventions. -/
theorem lintegral_sq_div_optimalImportance {f : 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the integrand (regularity)
    (hf : Measurable f) :
    ∫⁻ z, f z ^ 2 / (f z / ∫⁻ y, f y ∂ν) ∂ν = (∫⁻ z, f z ∂ν) ^ 2 := by
  set c := ∫⁻ y, f y ∂ν with hc
  have hmeas : Measurable fun z => f z ^ 2 / (f z / c) :=
    (hf.pow_const 2).div (hf.div_const c)
  have hcf : c = ∫⁻ z, f z ∂ν := hc
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- Degenerate: `f = 0` a.e., both sides vanish.
    have hf0 : f =ᵐ[ν] 0 := (lintegral_eq_zero_iff hf).mp (hcf ▸ hc0)
    have hLHS : ∫⁻ z, f z ^ 2 / (f z / c) ∂ν = 0 := by
      refine (lintegral_eq_zero_iff hmeas).mpr ?_
      filter_upwards [hf0] with z hz
      simp only [Pi.zero_apply] at hz
      simp [hz]
    rw [hLHS, hc0]
    simp
  rcases eq_or_ne c ∞ with hcT | hcT
  · -- Degenerate: `∫⁻ f = ∞`, and the integrand is `∞` on a positive-measure set.
    have hne : ¬ f =ᵐ[ν] 0 := fun h => hc0 (hcf ▸ (lintegral_eq_zero_iff hf).mpr h)
    have hLHS : ∫⁻ z, f z ^ 2 / (f z / c) ∂ν = ∞ := by
      refine lintegral_eq_top_of_measure_eq_top_ne_zero hmeas.aemeasurable fun h => hne ?_
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun z hz => ?_) h
      simp only [Set.mem_setOf_eq, Pi.zero_apply] at hz ⊢
      rw [hcT, ENNReal.div_top, ENNReal.div_zero (pow_ne_zero 2 hz)]
    rw [hLHS, hcT]
    simp
  · -- The generic case: the integrand is a.e. `f · c`.
    have hffin : ∀ᵐ z ∂ν, f z ≠ ∞ := by
      filter_upwards [ae_lt_top hf (hcf ▸ hcT)] with z hz
      exact hz.ne
    have hkey : ∀ᵐ z ∂ν, f z ^ 2 / (f z / c) = f z * c := by
      filter_upwards [hffin] with z hzT
      rcases eq_or_ne (f z) 0 with hz0 | hz0
      · simp [hz0]
      have hd0 : f z / c ≠ 0 := by
        simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
        exact ⟨hz0, hcT⟩
      have hdT : f z / c ≠ ∞ := by
        simp only [ne_eq, ENNReal.div_eq_top, not_or, not_and_or]
        exact ⟨Or.inr hc0, Or.inl hzT⟩
      have hstep : f z * c = f z ^ 2 / (f z / c) := by
        rw [ENNReal.eq_div_iff hd0 hdT, mul_comm (f z) c, ← mul_assoc,
          ENNReal.div_mul_cancel hc0 hcT, pow_two]
      exact hstep.symm
    rw [lintegral_congr_ae hkey, lintegral_mul_const' c f hcT, ← hcf, pow_two]

end StatLean.ComputationalStatistics
