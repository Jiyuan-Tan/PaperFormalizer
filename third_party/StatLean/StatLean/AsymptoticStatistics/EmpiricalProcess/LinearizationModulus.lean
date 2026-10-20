module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LipschitzShellModulus
public import StatLean.AsymptoticStatistics.EmpiricalProcess.IIDChebyshev
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation

@[expose] public section

/-!
# √n-scaled shell / linearization modulus (vdV Lem 19.34 / Thm 19.28)

The principal conclusion, also stated as
`LinearizationEquicontinuity.sqrtScaled_shell_modulus_tendstoZero`, is:

    ∀ ε > 0, ∀ η > 0, ∃ δ > 0,
      limsupₙ μ* { ξ | ∃ h₁ h₂ ∈ ball_M, ‖h₁ − h₂‖ < δ ∧
        ε < |𝔾ₙ(√n·(m_{θ₀+h₁/√n} − m_{θ₀})) − 𝔾ₙ(√n·(m_{θ₀+h₂/√n} − m_{θ₀}))| }
      ≤ ofReal η.

## The mathematically correct route (SCALED shell, fixed localization scale)

The **key subtlety** is the outer `√n`.  Writing `f_{n,h} := √n·(m_{θ₀+h/√n} − m_{θ₀})`
(the `scaledIncrement`), the pair oscillation is
`𝔾ₙ(f_{n,h₁}) − 𝔾ₙ(f_{n,h₂}) = 𝔾ₙ(f_{n,h₁} − f_{n,h₂})` (linearity), and
`f_{n,h₁} − f_{n,h₂} = √n·(m_{θ₀+h₁/√n} − m_{θ₀+h₂/√n})` has `L²(P)`-radius
`≤ ‖menv‖₂·‖h₁ − h₂‖` — an `O(1)` scale, **NOT** shrinking with `n`.  So the correct
localization is into the **scaled shell** `{f_{n,h} : ‖h‖ ≤ M}` (Euclidean radius `M`,
**fixed**) at a **fixed** localization scale `s = ‖menv‖₂·δ`, NOT into the un-scaled shell
of radius `M/√n`.

`f_{n,h} = shellPsi (scaledIncrement m θ₀ n) 0 h` (because `scaledIncrement m θ₀ n 0 = 0`),
and `scaledIncrement m θ₀ n` is `menv`-Lipschitz in `h` with the **same** envelope `menv`
(the `√n` and `1/√n` cancel).  So the whole `LipschitzShellModulus` bracketing machinery
applies to `scaledIncrement m θ₀ n` at radius `M` and scale `s`, uniformly in `n`.

## Route

1. `oscillation ≤ supNormOver (localizedDifferenceClass (scaledShell_M) P s) 𝔾ₙ`,
   `s = ‖menv‖₂·δ` (`scaledIncrement_lipschitz`, `mem_localizedDifferenceClass`).
2. Markov (`outerExpectation_markov` / `meas_ge_le_lintegral_div`):
   `μ*{sup > ε} ≤ (∫ sup)/ε`.
3. Localized chaining bound (`scaledShell_localizedChainBound_freeS`, free `s`, uniform `c`):
   `∫ sup ≤ c·J(s) + c·√n·Tail(√n·Mc)`.
4. `limsupₙ`: the entropy term `c·J(s)` is `n`-uniform (relative bracketing,
   `shell_bracketingEntropyIntegral_freeS`), and the tail `→ 0` as `n → ∞`
   (`envelopeTail_vanishes`, DCT-to-0 for `Φ = 2M|menv| ∈ L²`).  So
   `limsupₙ (∫ sup) ≤ c·J(s)`.
5. `J(s) ≤ ofReal(entropyScaleBound C M s)` with
   `entropyScaleBound C M s = 2·√(log 2 + d·|log(2CM/s)| + d)·s → 0` as `s → 0`
   (`entropyScaleBound_tendsto_zero`), so pick `δ` (hence `s`) small enough that
   `c·J(s)/ε ≤ η`.

vdV §19.5, Lem 19.31 / Lem 19.34 / Thm 19.28.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology NNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-! ### The √n-scaled local increment `f_{n,h} = √n·(m_{θ₀+h/√n} − m_{θ₀})` -/

/-- The **√n-scaled local increment** `f_{n,h}(ω) = √n·(m_{θ₀+h/√n}(ω) − m_{θ₀}(ω))`.
This is the function whose empirical process the target modulus controls; its Euclidean
`L²`-radius is `O(1)` (not shrinking), which is why the `√n` reparametrization keeps the
class Donsker. -/
noncomputable def scaledIncrement
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    EuclideanSpace ℝ (Fin d) → Ω → ℝ :=
  fun h ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)

omit [MeasurableSpace Ω] in
/-- `scaledIncrement m θ₀ n 0 = 0`: at `h = 0` the shifted parameter is `θ₀` itself, so the
increment vanishes.  This makes `scaledIncrement m θ₀ n` a `shellPsi`-shape centred at `0`. -/
@[simp] lemma scaledIncrement_apply_zero
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    scaledIncrement m θ₀ n 0 = fun _ => (0 : ℝ) := by
  funext ω
  simp only [scaledIncrement, smul_zero, add_zero, sub_self, mul_zero]

/-- `scaledIncrement m θ₀ n h` is measurable in `ω` (difference of measurables, scaled). -/
lemma scaledIncrement_measurable
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (hm_meas : ∀ θ, Measurable (m θ)) (h : EuclideanSpace ℝ (Fin d)) :
    Measurable (scaledIncrement m θ₀ n h) := by
  unfold scaledIncrement
  exact (measurable_const.mul ((hm_meas _).sub (hm_meas θ₀)))

omit [MeasurableSpace Ω] in
/-- **Same-envelope Lipschitz (localized).** For `n ≥ 1`, `scaledIncrement m θ₀ n` is
`menv`-Lipschitz in `h` with the **same** envelope `menv`: the outer `√n` and the inner
`(√n)⁻¹` from the `h/√n` shift cancel.  This is what lets the `LipschitzShellModulus`
machinery run at the fixed localization scale.

`hLip` is only assumed on the `θ₀`-ball `closedBall θ₀ ρ` (vdV "neighborhood of θ₀"); the two
shifted points `θ₀ + (√n)⁻¹•hᵢ` land in that ball exactly when `‖hᵢ‖ ≤ ρ·√n` (the small-`n`
guards `hh₁`, `hh₂`). Consequently the proof splits at
`n ≥ N₀ := ⌈(M/ρ)²⌉`; a `limsup`/`Tendsto`
conclusion ignores the finite prefix. -/
lemma scaledIncrement_lipschitz
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {n : ℕ} (hn : 1 ≤ n) (h₁ h₂ : EuclideanSpace ℝ (Fin d))
    (hh₁ : ‖h₁‖ ≤ ρ * Real.sqrt n) (hh₂ : ‖h₂‖ ≤ ρ * Real.sqrt n) (ω : Ω) :
    |scaledIncrement m θ₀ n h₁ ω - scaledIncrement m θ₀ n h₂ ω| ≤ menv ω * ‖h₁ - h₂‖ := by
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hne : Real.sqrt n ≠ 0 := hsqrt_pos.ne'
  have hmem : ∀ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ ρ * Real.sqrt n →
      θ₀ + (Real.sqrt n)⁻¹ • h ∈ Metric.closedBall θ₀ ρ := by
    intro h hh
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hsqrt_pos), inv_mul_eq_div, div_le_iff₀ hsqrt_pos]
    exact hh
  have hdiff : scaledIncrement m θ₀ n h₁ ω - scaledIncrement m θ₀ n h₂ ω
      = Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁) ω
          - m (θ₀ + (Real.sqrt n)⁻¹ • h₂) ω) := by
    simp only [scaledIncrement]; ring
  rw [hdiff, abs_mul, abs_of_pos hsqrt_pos]
  have hab : ‖(θ₀ + (Real.sqrt n)⁻¹ • h₁) - (θ₀ + (Real.sqrt n)⁻¹ • h₂)‖
      = (Real.sqrt n)⁻¹ * ‖h₁ - h₂‖ := by
    have hvec : (θ₀ + (Real.sqrt n)⁻¹ • h₁) - (θ₀ + (Real.sqrt n)⁻¹ • h₂)
        = (Real.sqrt n)⁻¹ • (h₁ - h₂) := by rw [smul_sub]; abel
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt_pos)]
  calc Real.sqrt n * |m (θ₀ + (Real.sqrt n)⁻¹ • h₁) ω - m (θ₀ + (Real.sqrt n)⁻¹ • h₂) ω|
      ≤ Real.sqrt n * (menv ω
          * ‖(θ₀ + (Real.sqrt n)⁻¹ • h₁) - (θ₀ + (Real.sqrt n)⁻¹ • h₂)‖) :=
        mul_le_mul_of_nonneg_left
          (hLip _ (hmem h₁ hh₁) _ (hmem h₂ hh₂) ω) hsqrt_pos.le
    _ = Real.sqrt n * (menv ω * ((Real.sqrt n)⁻¹ * ‖h₁ - h₂‖)) := by rw [hab]
    _ = menv ω * ‖h₁ - h₂‖ := by
        rw [show Real.sqrt ↑n * (menv ω * ((Real.sqrt ↑n)⁻¹ * ‖h₁ - h₂‖))
              = (Real.sqrt ↑n * (Real.sqrt ↑n)⁻¹) * (menv ω * ‖h₁ - h₂‖) by ring,
          mul_inv_cancel₀ hne, one_mul]

omit [MeasurableSpace Ω] in
/-- The local increment at an arbitrary deterministic rate `r`: this definition is total,
including at indices where `r n = 0`. -/
noncomputable def scaledIncrementAt
    (r : ℕ → ℝ) (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    EuclideanSpace ℝ (Fin d) → Ω → ℝ :=
  fun h ω => r n * (m (θ₀ + (r n)⁻¹ • h) ω - m θ₀ ω)

omit [MeasurableSpace Ω] in
/-- `scaledIncrementAt r m θ₀ n 0 = 0` at every rate, including `r n = 0`. -/
@[simp] lemma scaledIncrementAt_apply_zero
    (r : ℕ → ℝ) (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    scaledIncrementAt r m θ₀ n 0 = fun _ => (0 : ℝ) := by
  funext ω
  simp only [scaledIncrementAt, smul_zero, add_zero, sub_self, mul_zero]

/-- `scaledIncrementAt r m θ₀ n h` is measurable in the observation. -/
lemma scaledIncrementAt_measurable
    (r : ℕ → ℝ) (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (hm_meas : ∀ θ, Measurable (m θ)) (h : EuclideanSpace ℝ (Fin d)) :
    Measurable (scaledIncrementAt r m θ₀ n h) := by
  unfold scaledIncrementAt
  exact (hm_meas _).sub (hm_meas θ₀) |>.const_mul _

omit [MeasurableSpace Ω] in
/-- At a positive rate, the outer rate and inverse parameter shift cancel, so the arbitrary-
rate local increment has the same localized Lipschitz envelope as the original criterion. -/
lemma scaledIncrementAt_lipschitz
    (r : ℕ → ℝ) (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (menv : Ω → ℝ) (ρ : ℝ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
      |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {n : ℕ} (hrn : 0 < r n) (h₁ h₂ : EuclideanSpace ℝ (Fin d))
    (hh₁ : ‖h₁‖ ≤ ρ * r n) (hh₂ : ‖h₂‖ ≤ ρ * r n) (ω : Ω) :
    |scaledIncrementAt r m θ₀ n h₁ ω - scaledIncrementAt r m θ₀ n h₂ ω|
      ≤ menv ω * ‖h₁ - h₂‖ := by
  have hrn_ne : r n ≠ 0 := hrn.ne'
  have hmem : ∀ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ ρ * r n →
      θ₀ + (r n)⁻¹ • h ∈ Metric.closedBall θ₀ ρ := by
    intro h hh
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hrn), inv_mul_eq_div, div_le_iff₀ hrn]
    exact hh
  have hdiff : scaledIncrementAt r m θ₀ n h₁ ω - scaledIncrementAt r m θ₀ n h₂ ω
      = r n * (m (θ₀ + (r n)⁻¹ • h₁) ω - m (θ₀ + (r n)⁻¹ • h₂) ω) := by
    simp only [scaledIncrementAt]
    ring
  rw [hdiff, abs_mul, abs_of_pos hrn]
  have hab : ‖(θ₀ + (r n)⁻¹ • h₁) - (θ₀ + (r n)⁻¹ • h₂)‖
      = (r n)⁻¹ * ‖h₁ - h₂‖ := by
    have hvec : (θ₀ + (r n)⁻¹ • h₁) - (θ₀ + (r n)⁻¹ • h₂)
        = (r n)⁻¹ • (h₁ - h₂) := by rw [smul_sub]; abel
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrn)]
  calc r n * |m (θ₀ + (r n)⁻¹ • h₁) ω - m (θ₀ + (r n)⁻¹ • h₂) ω|
      ≤ r n * (menv ω * ‖(θ₀ + (r n)⁻¹ • h₁) - (θ₀ + (r n)⁻¹ • h₂)‖) :=
        mul_le_mul_of_nonneg_left
          (hLip _ (hmem h₁ hh₁) _ (hmem h₂ hh₂) ω) hrn.le
    _ = r n * (menv ω * ((r n)⁻¹ * ‖h₁ - h₂‖)) := by rw [hab]
    _ = menv ω * ‖h₁ - h₂‖ := by
      rw [show r n * (menv ω * ((r n)⁻¹ * ‖h₁ - h₂‖))
            = (r n * (r n)⁻¹) * (menv ω * ‖h₁ - h₂‖) by ring,
        mul_inv_cancel₀ hrn_ne, one_mul]

/-! ### Free-scale relative bracketing entropy of the shell

The entropy integral of the (fixed-centre) shell of radius `R` at a **free** localization
scale `s ∈ (0, R]`.  Because the bracketing number is *relative* (`∝ (R/s)^d`), the integral
is `≤ 2·√(log 2 + d·|log(2CR/s)| + d)·s`, which `→ 0` as `s → 0` (the `√log(R/s)` factor is
sub-linear).  This is the free-scale analogue of `paramClass_shell_bracketingEntropyIntegral_le`
(which is tied to `s = δ·(‖menv‖₂+1)`). The explicit constant makes the
`s → 0` limit immediate. -/

/-- `∫₀^δq √(δq/ε) dε = 2·δq`. -/
private lemma lintegral_sqrt_ratio' {δq : ℝ} (hδq : 0 < δq) :
    ∫⁻ ε in Set.Ioc (0 : ℝ) δq, ENNReal.ofReal (Real.sqrt (δq / ε)) ∂volume
      = ENNReal.ofReal (2 * δq) := by
  have hfun : Set.EqOn (fun ε : ℝ => Real.sqrt (δq / ε))
      (fun ε => Real.sqrt δq * ε ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 δq) := by
    intro ε hε
    have hε0 : 0 < ε := hε.1
    change Real.sqrt (δq / ε) = Real.sqrt δq * ε ^ (-(1 / 2) : ℝ)
    rw [Real.rpow_neg hε0.le, ← Real.sqrt_eq_rpow, Real.sqrt_div hδq.le, div_eq_mul_inv]
  have hint_pow : IntegrableOn (fun ε : ℝ => ε ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 δq) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).1
  have hbase : IntegrableOn (fun ε : ℝ => Real.sqrt δq * ε ^ (-(1 / 2) : ℝ))
      (Set.Ioc 0 δq) volume := hint_pow.const_mul (Real.sqrt δq)
  have hint : IntegrableOn (fun ε : ℝ => Real.sqrt (δq / ε)) (Set.Ioc 0 δq) volume :=
    hbase.congr_fun hfun.symm measurableSet_Ioc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 δq)] (fun ε => Real.sqrt (δq / ε)) :=
    Eventually.of_forall (fun ε => Real.sqrt_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioc hfun, integral_const_mul,
    ← intervalIntegral.integral_of_le hδq.le, integral_rpow (Or.inl (by norm_num))]
  have h0 : (0 : ℝ) ^ (-(1 / 2) + 1 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  have hd : δq ^ (-(1 / 2) + 1 : ℝ) = Real.sqrt δq := by
    rw [show (-(1 / 2) + 1 : ℝ) = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  rw [h0, hd, sub_zero, show (-(1 / 2) + 1 : ℝ) = 1 / 2 by norm_num,
    show Real.sqrt δq * (Real.sqrt δq / (1 / 2)) = 2 * (Real.sqrt δq * Real.sqrt δq) from by ring,
    Real.mul_self_sqrt hδq.le]

/-- Explicit-constant form of `sqrt_log_pow_ratio_lintegral_le`: the leading
constant is `2·√(log 2 + p·|log C| + p)`, which is independent of the scale
and therefore suitable for `s → 0` limits. -/
private lemma sqrt_log_pow_ratio_lintegral_le_explicit
    (C : ℝ) (hC : 0 < C) (p : ℕ) {δq : ℝ} (hδq : 0 < δq) :
    ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
        ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δq / ε) ^ p))) ∂volume
      ≤ ENNReal.ofReal (2 * Real.sqrt (Real.log 2 + p * |Real.log C| + p) * δq) := by
  set A : ℝ := Real.log 2 + p * |Real.log C| + p with hAdef
  have hA_pos : 0 < A := by
    have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ (p : ℝ) * |Real.log C| := by positivity
    rw [hAdef]; positivity
  set B : ℝ := Real.sqrt A with hBdef
  have hB_pos : 0 < B := Real.sqrt_pos.mpr hA_pos
  have hB_nn : 0 ≤ B := hB_pos.le
  -- Pointwise: `√log(1 + (Cδq/ε)^p) ≤ B·√(δq/ε)` on `(0, δq]`.
  have hpoint : ∀ ε ∈ Set.Ioc (0 : ℝ) δq,
      Real.sqrt (Real.log (1 + (C * δq / ε) ^ p)) ≤ B * Real.sqrt (δq / ε) := by
    intro ε hε
    obtain ⟨hε0, hεδ⟩ := hε
    set y : ℝ := δq / ε with hy
    have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hε0]; linarith
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    have hCδε : C * δq / ε = C * y := by rw [hy]; ring
    rw [hCδε]
    have hlogy_nn : 0 ≤ Real.log y := Real.log_nonneg hy1
    have hlogy_le : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    have hlog_le : Real.log (1 + (C * y) ^ p) ≤ A * y := by
      have hl2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hl2 : Real.log 2 ≤ Real.log 2 * y := by nlinarith [hl2_pos, hy1]
      by_cases hge : 1 ≤ (C * y) ^ p
      · have hCyp_pos : 0 < (C * y) ^ p := by positivity
        have ha : (0 : ℝ) ≤ (p : ℝ) * |Real.log C| :=
          mul_nonneg (Nat.cast_nonneg p) (abs_nonneg _)
        have hpc : (p : ℝ) * |Real.log C| ≤ (p : ℝ) * |Real.log C| * y := by nlinarith [ha, hy1]
        have hply : (p : ℝ) * Real.log y ≤ (p : ℝ) * y :=
          mul_le_mul_of_nonneg_left hlogy_le (Nat.cast_nonneg p)
        calc Real.log (1 + (C * y) ^ p)
            ≤ Real.log (2 * (C * y) ^ p) := Real.log_le_log (by positivity) (by linarith)
          _ = Real.log 2 + p * Real.log (C * y) := by
              rw [Real.log_mul two_ne_zero hCyp_pos.ne', Real.log_pow]
          _ = Real.log 2 + p * (Real.log C + Real.log y) := by rw [Real.log_mul hC.ne' hy0.ne']
          _ ≤ Real.log 2 + p * (|Real.log C| + Real.log y) := by
              gcongr; exact le_abs_self _
          _ = Real.log 2 + p * |Real.log C| + p * Real.log y := by ring
          _ ≤ Real.log 2 * y + p * |Real.log C| * y + p * y := by linarith
          _ = A * y := by rw [hAdef]; ring
      · have hlt : (C * y) ^ p < 1 := not_le.mp hge
        have hCyp_nn : (0 : ℝ) ≤ (C * y) ^ p := by positivity
        calc Real.log (1 + (C * y) ^ p)
            ≤ Real.log 2 := Real.log_le_log (by positivity) (by linarith)
          _ ≤ Real.log 2 * y := hl2
          _ ≤ A * y := by
              rw [hAdef]
              nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) * |Real.log C|) hy0.le,
                mul_nonneg (Nat.cast_nonneg p) hy0.le]
    calc Real.sqrt (Real.log (1 + (C * y) ^ p))
        ≤ Real.sqrt (A * y) := Real.sqrt_le_sqrt hlog_le
      _ = Real.sqrt A * Real.sqrt y := Real.sqrt_mul hA_pos.le y
      _ = B * Real.sqrt y := by rw [hBdef]
  calc ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
        ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δq / ε) ^ p))) ∂volume
      ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) δq, ENNReal.ofReal (B * Real.sqrt (δq / ε)) ∂volume :=
        setLIntegral_mono_ae' measurableSet_Ioc
          (Eventually.of_forall fun ε hε => ENNReal.ofReal_le_ofReal (hpoint ε hε))
    _ = ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
          ENNReal.ofReal B * ENNReal.ofReal (Real.sqrt (δq / ε)) ∂volume :=
        lintegral_congr fun ε => ENNReal.ofReal_mul hB_nn
    _ = ENNReal.ofReal B * ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
          ENNReal.ofReal (Real.sqrt (δq / ε)) ∂volume :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal B * ENNReal.ofReal (2 * δq) := by rw [lintegral_sqrt_ratio' hδq]
    _ = ENNReal.ofReal (2 * B * δq) := by
        rw [← ENNReal.ofReal_mul hB_nn]; congr 1; ring
    _ = ENNReal.ofReal (2 * Real.sqrt (Real.log 2 + p * |Real.log C| + p) * δq) := by
        rw [hBdef, hAdef]

/-- Closed-ball relative bracketing-number bound. -/
private theorem shellClosedBall_bracketingNumber_le' {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ), (∀ θ, Measurable (m θ)) →
      ∀ δ : ℝ, 0 < δ →
        (∀ θ₁ ∈ Metric.closedBall θ₀ δ, ∀ θ₂ ∈ Metric.closedBall θ₀ δ, ∀ ω,
            |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) →
        ∀ t : ℝ, 0 < t →
        t ≤ 2 * δ * ((eLpNorm menv 2 P).toReal + 1) →
      ∃ N : ℕ, bracketingNumber t
          (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ)) 2 P ≤ (N : ℕ∞) ∧
        (N : ℝ) ≤ (d : ℝ) * (C * δ / t) ^ d := by
  classical
  set M : ℝ := (eLpNorm menv 2 P).toReal with hMdef
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  have hMp1_pos : (0 : ℝ) < M + 1 := by positivity
  obtain ⟨Ce, hCe_pos, hcover⟩ :=
    coveringNumber_le_of_bounded_euclidean (Metric.closedBall θ₀ 1) Metric.isBounded_closedBall
  refine ⟨2 * Ce * (M + 1), by positivity, fun m hm_meas δ hδ hLip t ht htle => ?_⟩
  set η : ℝ := t / (2 * (M + 1) * δ) with hηdef
  have hden_pos : (0 : ℝ) < 2 * (M + 1) * δ := by positivity
  have hη_pos : 0 < η := by rw [hηdef]; positivity
  have hη_le : η ≤ 1 := by
    rw [hηdef, div_le_one hden_pos]; nlinarith [htle]
  obtain ⟨S, hSΘ, hΘcover, hScard⟩ := hcover η hη_pos hη_le
  set ρ : ℝ := δ * η with hρdef
  have hρ_pos : 0 < ρ := by rw [hρdef]; positivity
  set Simg : Finset (EuclideanSpace ℝ (Fin d)) :=
    S.image (fun c => θ₀ + δ • (c - θ₀)) with hSimg
  have hSimg_sub : ↑Simg ⊆ Metric.closedBall θ₀ δ := by
    intro c' hc'
    rw [hSimg, Finset.coe_image, Set.mem_image] at hc'
    obtain ⟨c, hcS, rfl⟩ := hc'
    have hc_norm : ‖c - θ₀‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp (hSΘ (Finset.mem_coe.mpr hcS))
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hδ]
    calc δ * ‖c - θ₀‖ ≤ δ * 1 := mul_le_mul_of_nonneg_left hc_norm hδ.le
      _ = δ := mul_one δ
  have hSimg_net : Metric.closedBall θ₀ δ ⊆ ⋃ c ∈ Simg, Metric.ball c ρ := by
    intro x hx
    have hx_norm : ‖x - θ₀‖ ≤ δ := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hx
    set u : EuclideanSpace ℝ (Fin d) := θ₀ + δ⁻¹ • (x - θ₀) with hudef
    have hu_norm : ‖u - θ₀‖ ≤ 1 := by
      have huθ : u - θ₀ = δ⁻¹ • (x - θ₀) := by rw [hudef, add_sub_cancel_left]
      rw [huθ, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
      calc δ⁻¹ * ‖x - θ₀‖ ≤ δ⁻¹ * δ :=
            mul_le_mul_of_nonneg_left hx_norm (inv_pos.mpr hδ).le
        _ = 1 := inv_mul_cancel₀ hδ.ne'
    have huΘ : u ∈ Metric.closedBall θ₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hu_norm
    obtain ⟨c, hcS, hcu⟩ := Set.mem_iUnion₂.mp (hΘcover huΘ)
    have hcu_lt : ‖u - c‖ < η := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hcu
    refine Set.mem_iUnion₂.mpr ⟨θ₀ + δ • (c - θ₀), ?_, ?_⟩
    · rw [hSimg]; exact Finset.mem_image_of_mem _ hcS
    · rw [Metric.mem_ball, dist_eq_norm]
      have hvec : x - (θ₀ + δ • (c - θ₀)) = δ • (u - c) := by
        simp only [hudef, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
        abel
      rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hρdef]
      exact mul_lt_mul_of_pos_left hcu_lt hδ
  have hscale : 2 * ρ * M < t := by
    rw [hρdef]
    have hrw : 2 * (δ * η) * M = t * M / (M + 1) := by
      rw [hηdef]; field_simp
    rw [hrw, div_lt_iff₀ hMp1_pos]; nlinarith [ht, hM_nn]
  have hψmeas : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ j : Fin d,
      Measurable (shellPsi m θ₀ θ j) := by
    intro θ _ j; exact (hm_meas θ).sub (hm_meas θ₀)
  have hBN := bracketingNumber_le_of_lipschitz P (shellPsi m θ₀) (Metric.closedBall θ₀ δ)
    menv hmenv hmenv_meas hψmeas
    (fun θ hθδ j => shellPsi_memLp m θ₀ hm_meas menv hmenv δ hδ hLip θ hθδ j)
    (fun θ₁ hθ₁δ θ₂ hθ₂δ j x => shellPsi_lipschitz m θ₀ menv δ hδ hLip θ₁ hθ₁δ θ₂ hθ₂δ j x)
    hρ_pos hSimg_sub hSimg_net hscale
  refine ⟨d * Simg.card, hBN, ?_⟩
  have hcard_le : (Simg.card : ℝ) ≤ (S.card : ℝ) := by
    rw [hSimg]; exact_mod_cast Finset.card_image_le
  have hCeη : Ce / η = 2 * Ce * (M + 1) * δ / t := by
    rw [hηdef, div_div_eq_mul_div]; ring
  rw [Nat.cast_mul]
  calc (d : ℝ) * (Simg.card : ℝ)
      ≤ (d : ℝ) * (Ce / η) ^ d :=
        mul_le_mul_of_nonneg_left (le_trans hcard_le hScard) (Nat.cast_nonneg d)
    _ = (d : ℝ) * (2 * Ce * (M + 1) * δ / t) ^ d := by rw [hCeη]

/-- **Free-scale relative bracketing entropy of the shell.**

For the fixed-centre shell `F_R = paramClass (shellPsi m θ₀) (ball θ₀ R)` and any localization
scale `s ∈ (0, R]`,

    J_{[]}(s, F_R) ≤ 2·√(log 2 + d·|log(2·C·R/s)| + d)·s ,

with `C > 0` `δ`-free (the shell covering constant).  The RHS `→ 0` as `s → 0`
(`entropyScaleBound_tendsto_zero`). -/
theorem shell_bracketingEntropyIntegral_freeS {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ), (∀ θ, Measurable (m θ)) →
      ∀ R : ℝ, 0 < R →
        (∀ θ₁ ∈ Metric.closedBall θ₀ R, ∀ θ₂ ∈ Metric.closedBall θ₀ R, ∀ ω,
            |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) →
        ∀ s : ℝ, 0 < s → s ≤ R →
      bracketingEntropyIntegral s (paramClass (shellPsi m θ₀) (Metric.ball θ₀ R)) P
        ≤ ENNReal.ofReal
            (2 * Real.sqrt (Real.log 2 + d * |Real.log (2 * C * R / s)| + d) * s) := by
  classical
  obtain ⟨C, hC_pos, hBN⟩ :=
    shellClosedBall_bracketingNumber_le' P θ₀ menv hmenv hmenv_meas
  set Mv : ℝ := (eLpNorm menv 2 P).toReal with hMvdef
  have hMv_nn : 0 ≤ Mv := ENNReal.toReal_nonneg
  refine ⟨C, hC_pos, fun m hm_meas R hR hLip s hs hsR => ?_⟩
  -- Reduce to the CLOSED shell by class monotonicity.
  have hmono_class :
      bracketingEntropyIntegral s (paramClass (shellPsi m θ₀) (Metric.ball θ₀ R)) P
        ≤ bracketingEntropyIntegral s
            (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ R)) P := by
    apply bracketingEntropyIntegral_mono_class
    rintro g ⟨θ, hθ, j, rfl⟩
    exact ⟨θ, Metric.ball_subset_closedBall hθ, j, rfl⟩
  -- Pointwise domination of the closed-shell entropy integrand on `Ioc 0 s`.
  have hdom : ∀ ε ∈ Set.Ioc (0 : ℝ) s,
      entropyIntegrand ε (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ R)) P
        ≤ ENNReal.ofReal (Real.sqrt (Real.log (1 + ((2 * C * R / s) * s / ε) ^ d))) := by
    intro ε hε
    obtain ⟨hε0, hεs⟩ := hε
    -- gate for `shellClosedBall_bracketingNumber_le'`: `ε ≤ 2R(‖menv‖₂+1)`.
    have htle : ε ≤ 2 * R * (Mv + 1) := by
      have h1 : (1 : ℝ) ≤ Mv + 1 := by linarith [hMv_nn]
      have h2 : R ≤ 2 * R * (Mv + 1) := by nlinarith [hR.le, h1]
      linarith [hεs, hsR, h2]
    obtain ⟨N, hN_le, hN_bd⟩ := hBN m hm_meas R hR hLip ε hε0 htle
    calc entropyIntegrand ε (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ R)) P
        = entropyWeight (bracketingNumber ε
            (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ R)) 2 P) := rfl
      _ ≤ entropyWeight (N : ℕ∞) := entropyWeight_mono hN_le
      _ = ENNReal.ofReal (Real.sqrt (Real.log (1 + (N : ℝ)))) := entropyWeight_coe N
      _ ≤ ENNReal.ofReal (Real.sqrt (Real.log (1 + ((2 * C * R / s) * s / ε) ^ d))) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.sqrt_le_sqrt
          apply Real.log_le_log (by positivity)
          have hrw : (2 * C * R / s) * s / ε = 2 * C * R / ε := by
            field_simp
          rw [hrw]
          have hNle : (N : ℝ) ≤ (2 * C * R / ε) ^ d := by
            calc (N : ℝ)
                ≤ (d : ℝ) * (C * R / ε) ^ d := hN_bd
              _ ≤ (2 : ℝ) ^ d * (C * R / ε) ^ d := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact_mod_cast (Nat.lt_two_pow_self (n := d)).le
              _ = (2 * (C * R / ε)) ^ d := by rw [mul_pow]
              _ = (2 * C * R / ε) ^ d := by rw [show 2 * (C * R / ε) = 2 * C * R / ε by ring]
          linarith [hNle]
  calc bracketingEntropyIntegral s (paramClass (shellPsi m θ₀) (Metric.ball θ₀ R)) P
      ≤ bracketingEntropyIntegral s
          (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ R)) P := hmono_class
    _ = ∫⁻ ε in Set.Ioc (0 : ℝ) s,
          entropyIntegrand ε (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ R)) P ∂volume :=
        bracketingEntropyIntegral_eq_setLIntegral s _ P
    _ ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) s,
          ENNReal.ofReal (Real.sqrt (Real.log (1 + ((2 * C * R / s) * s / ε) ^ d))) ∂volume :=
        setLIntegral_mono_ae' measurableSet_Ioc (Eventually.of_forall hdom)
    _ ≤ ENNReal.ofReal
          (2 * Real.sqrt (Real.log 2 + d * |Real.log (2 * C * R / s)| + d) * s) :=
        sqrt_log_pow_ratio_lintegral_le_explicit (2 * C * R / s) (by positivity) d hs

/-- The leading bound `s ↦ 2·√(log 2 + d·|log(2CR/s)| + d)·s → 0` as `s → 0⁺`
(the `√log(R/s)` factor is beaten by the linear `s`). -/
theorem entropyScaleBound_tendsto_zero {d : ℕ} (C R : ℝ) (hC : 0 < C) (hR : 0 < R) :
    Tendsto (fun s : ℝ =>
        2 * Real.sqrt (Real.log 2 + d * |Real.log (2 * C * R / s)| + d) * s)
      (𝓝[>] 0) (𝓝 0) := by
  have hK : (0 : ℝ) < 2 * C * R := by positivity
  -- Step 1: `log u / u² → 0` as `u → ∞`.
  have hlog_u2 : Tendsto (fun u : ℝ => Real.log u / u ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
      have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      simpa [id] using this
    have h2 : Tendsto (fun u : ℝ => (Real.log u / u) * u⁻¹) atTop (𝓝 0) := by
      simpa using h1.mul tendsto_inv_atTop_zero
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp
  -- Step 2: `|log u|/u² → 0` (abs harmless for large u), so `|log u|·(2CR/u)² → 0`.
  have houter : Tendsto (fun u : ℝ => |Real.log u| * (2 * C * R / u) ^ 2) atTop (𝓝 0) := by
    have habs : Tendsto (fun u : ℝ => |Real.log u| / u ^ 2) atTop (𝓝 0) := by
      have hle : Tendsto (fun u : ℝ => |Real.log u / u ^ 2|) atTop (𝓝 0) := by
        simpa using hlog_u2.abs
      refine hle.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 2)]
    have := habs.const_mul ((2 * C * R) ^ 2)
    simpa using this.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      rw [div_pow]; ring)
  -- Step 3: compose with `u = 2CR/s → ∞`.
  have hu : Tendsto (fun s : ℝ => 2 * C * R / s) (𝓝[>] 0) atTop := by
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hK
    refine this.congr ?_
    intro s; rw [div_eq_mul_inv]
  have hkey : Tendsto (fun s : ℝ => |Real.log (2 * C * R / s)| * s ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hcomp := houter.comp hu
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 < s := hs
    simp only [Function.comp]
    rw [show 2 * C * R / (2 * C * R / s) = s by field_simp]
  -- Step 4: `(log2 + d|log(2CR/s)| + d)·s² → 0`.
  have hbig : Tendsto (fun s : ℝ =>
      (Real.log 2 + d * |Real.log (2 * C * R / s)| + d) * s ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hconst : Tendsto (fun s : ℝ => (Real.log 2 + d) * s ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have hs2 : Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun s : ℝ => s ^ 2) (𝓝 (0:ℝ)) (𝓝 0) := by
          have := (continuous_pow 2).tendsto (0 : ℝ); simpa using this
        exact this.mono_left nhdsWithin_le_nhds
      simpa using hs2.const_mul (Real.log 2 + d)
    have hmid : Tendsto (fun s : ℝ => (d : ℝ) * (|Real.log (2 * C * R / s)| * s ^ 2))
        (𝓝[>] 0) (𝓝 0) := by simpa using hkey.const_mul (d : ℝ)
    have hsum := hconst.add hmid
    simp only [add_zero] at hsum
    refine hsum.congr ?_
    intro s; ring
  -- Step 5: `f s = 2·√((...)·s²)` for `s > 0`, and `√ ∘ hbig → √0 = 0`.
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt
      ((Real.log 2 + d * |Real.log (2 * C * R / s)| + d) * s ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hbig
    simpa [Real.sqrt_zero] using! this
  have hfinal : Tendsto (fun s : ℝ => 2 * Real.sqrt
      ((Real.log 2 + d * |Real.log (2 * C * R / s)| + d) * s ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hsqrt.const_mul 2
  refine hfinal.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 < s := hs
  have hXnn : 0 ≤ Real.log 2 + d * |Real.log (2 * C * R / s)| + d := by
    have h1 : 0 ≤ Real.log 2 := (Real.log_nonneg (by norm_num))
    positivity
  rw [Real.sqrt_mul hXnn, Real.sqrt_sq hs0.le]
  ring

/-! ### Free-scale bracketing number of the localized difference class

Free-scale analogue of `shell_localizedDiff_bracketingNumber_le`: a single `N*` (free of
`s`, function of the ratio `R/s`) bounds both localized-difference bracketing numbers at
scales `s`, `s/2` for the shell of radius `R` at localization scale `s`. -/

/-- **Free-scale uniform relative bracketing number of the localized difference class.**

The bracketing constant `C = 2·Ce·(‖menv‖₂+1)` (from the unit-ball covering number `Ce`)
depends only on `(θ₀, menv)`, not on the specific function `m`. The explicit count is
`⌊d·(4CR/s)^d⌋₊²`. This uniformity gives the √n-scaled chaining bound one truncation
lower-bound constant `cM` uniformly across the family `m := scaledIncrement m₀ θ₀ n`. -/
theorem shell_localizedDiff_bracketingNumber_freeS {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ), (∀ θ, Measurable (m θ)) →
        (∀ θ₁ ∈ Metric.closedBall θ₀ R, ∀ θ₂ ∈ Metric.closedBall θ₀ R, ∀ ω,
            |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) →
      ∀ s : ℝ, 0 < s → s ≤ R →
      bracketingNumber s
          (localizedDifferenceClass (paramClass (shellPsi m θ₀) (Metric.ball θ₀ R)) P s) 2 P
          ≤ ((⌊(d : ℝ) * (4 * C * R / s) ^ d⌋₊ ^ 2 : ℕ) : ℕ∞) ∧
      bracketingNumber (s / 2)
          (localizedDifferenceClass (paramClass (shellPsi m θ₀) (Metric.ball θ₀ R)) P s) 2 P
          ≤ ((⌊(d : ℝ) * (4 * C * R / s) ^ d⌋₊ ^ 2 : ℕ) : ℕ∞) := by
  classical
  obtain ⟨C, hC_pos, hBN⟩ :=
    shellClosedBall_bracketingNumber_le' P θ₀ menv hmenv hmenv_meas
  set Mv : ℝ := (eLpNorm menv 2 P).toReal with hMvdef
  have hMv_nn : 0 ≤ Mv := ENNReal.toReal_nonneg
  refine ⟨C, hC_pos, fun m hm_meas hLip s hs hsR => ?_⟩
  set K' : ℝ := (d : ℝ) * (4 * C * R / s) ^ d with hK'_def
  set Kf : ℕ := ⌊K'⌋₊ with hKf_def
  set F : Set (Ω → ℝ) := paramClass (shellPsi m θ₀) (Metric.ball θ₀ R) with hF_def
  set Fc : Set (Ω → ℝ) := paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ R) with hFc_def
  have hFsub : F ⊆ Fc := by
    rw [hF_def, hFc_def]; rintro g ⟨θ, hθ, j, rfl⟩
    exact ⟨θ, Metric.ball_subset_closedBall hθ, j, rfl⟩
  -- Core: for `s/2 ≤ t ≤ s`, `N_{[]}(t, localizedDiff F s) ≤ (Kf : ℕ∞)²`.
  have hbn : ∀ t : ℝ, s / 2 ≤ t → t ≤ s →
      bracketingNumber t (localizedDifferenceClass F P s) 2 P ≤ (Kf : ℕ∞) ^ 2 := by
    intro t ht_lo ht_hi
    have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht_lo
    have ht2_pos : (0 : ℝ) < t / 2 := by positivity
    have ht2_le : t / 2 ≤ 2 * R * (Mv + 1) := by
      have h1 : (1 : ℝ) ≤ Mv + 1 := by linarith [hMv_nn]
      have h2 : R ≤ 2 * R * (Mv + 1) := by nlinarith [hR.le, h1]
      have h3 : t / 2 ≤ R := by linarith [ht_hi, hsR]
      linarith [h3, h2]
    obtain ⟨Na, hNa_le, hNa_bd⟩ := hBN m hm_meas R hR hLip (t / 2) ht2_pos ht2_le
    have hNa_K' : (Na : ℝ) ≤ K' := by
      refine le_trans hNa_bd ?_
      rw [hK'_def]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      apply pow_le_pow_left₀ (by positivity) _ d
      have ht2_ge : s / 4 ≤ t / 2 := by linarith [ht_lo]
      calc C * R / (t / 2)
          ≤ C * R / (s / 4) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) ht2_ge
        _ = 4 * C * R / s := by rw [div_div_eq_mul_div]; ring
    have hNa_Kf : Na ≤ Kf := by rw [hKf_def]; exact Nat.le_floor hNa_K'
    have hcov : HasFiniteBracketingCover F (t / 2) 2 P := by
      apply bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mp
      calc bracketingNumber (t / 2) F 2 P
          ≤ bracketingNumber (t / 2) Fc 2 P := bracketingNumber_mono_class hFsub
        _ ≤ (Na : ℕ∞) := hNa_le
        _ < ⊤ := ENat.coe_lt_top Na
    calc bracketingNumber t (localizedDifferenceClass F P s) 2 P
        ≤ bracketingNumber t (differenceClass F) 2 P :=
          bracketingNumber_mono_class localizedDifferenceClass_subset
      _ ≤ (bracketingNumber (t / 2) F 2 P) ^ 2 :=
          bracketingNumber_differenceClass_le_sq ht_pos hcov
      _ ≤ (bracketingNumber (t / 2) Fc 2 P) ^ 2 :=
          pow_le_pow_left' (bracketingNumber_mono_class hFsub) 2
      _ ≤ (Na : ℕ∞) ^ 2 := pow_le_pow_left' hNa_le 2
      _ ≤ (Kf : ℕ∞) ^ 2 := pow_le_pow_left' (by exact_mod_cast hNa_Kf) 2
  have hcast : (Kf : ℕ∞) ^ 2 = ((Kf ^ 2 : ℕ) : ℕ∞) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h := hbn s (by linarith [hs]) le_rfl
    rwa [hcast] at h
  · have h := hbn (s / 2) le_rfl (by linarith [hs]); rwa [hcast] at h

/-! ### DCT tail — the envelope tail vanishes -/

/-- **Envelope tail vanishes (DCT-to-0).**  For a fixed `Φ ∈ L²(P)` and clamp coefficient
`a > 0`, the `√n`-scaled truncated envelope tail `→ 0`:

    √n·∫ |Φ|·1{√n·a < |Φ|} → 0    as n → ∞.

On `{√n·a < |Φ|}` one has `√n·|Φ| ≤ |Φ|²/a` (Chebyshev), so the tail is
`≤ (1/a)·∫ |Φ|²·1{|Φ| > √n·a} → 0` by dominated convergence (`Φ² ∈ L¹`, indicators `↓ 0`).
This is the mechanism the localized-chaining docstring names ("`√n·E[|Φ|·1{|Φ|>√n·M}] → 0`"). -/
theorem envelopeTail_vanishes {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Φ : Ω → ℝ) (hΦ : MemLp Φ 2 P) (hΦ_meas : Measurable Φ)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n)
        * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
            * Set.indicator {x | Real.sqrt n * a < |Φ x|} 1 ω ∂P) atTop (𝓝 0) := by
  have hΦabs_meas : Measurable (fun ω => |Φ ω|) := hΦ_meas.abs
  -- `∫⁻ |Φ|² < ∞`.
  have hT_ne : ∫⁻ ω, ENNReal.ofReal (|Φ ω| ^ 2) ∂P ≠ ∞ := by
    have h_eLp : eLpNorm Φ 2 P < ∞ := hΦ.eLpNorm_lt_top
    have h_rpow := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := P) (f := Φ) (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) h_eLp
    have h_two : (2 : ℝ≥0∞).toReal = (2 : ℕ) := by norm_num
    rw [h_two] at h_rpow
    have h_int_eq : ∫⁻ ω, ENNReal.ofReal (|Φ ω| ^ 2) ∂P
        = ∫⁻ a, ‖Φ a‖ₑ ^ ((2 : ℕ) : ℝ) ∂P := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
    rw [h_int_eq]; exact h_rpow.ne
  set bnd : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (|Φ ω| ^ 2 / a) with hbnd
  set G : ℕ → Ω → ℝ≥0∞ :=
    fun n ω => bnd ω * Set.indicator {x | Real.sqrt n * a < |Φ x|} 1 ω with hG
  have hset_meas : ∀ n : ℕ, MeasurableSet {x | Real.sqrt n * a < |Φ x|} :=
    fun n => measurableSet_lt measurable_const hΦabs_meas
  have hbnd_meas : Measurable bnd := by
    simp only [hbnd]; exact ((hΦabs_meas.pow_const 2).div_const a).ennreal_ofReal
  -- `∫⁻ bnd < ∞`.
  have hbnd_ne : ∫⁻ ω, bnd ω ∂P ≠ ∞ := by
    have heq : ∀ ω, bnd ω = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (|Φ ω| ^ 2) := by
      intro ω
      simp only [hbnd]
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ a⁻¹), div_eq_inv_mul]
    rw [lintegral_congr heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT_ne
  -- DCT: `∫⁻ G n → 0`.
  have hDCT : Tendsto (fun n => ∫⁻ ω, G n ω ∂P) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ∫⁻ ω, G n ω ∂P) atTop (𝓝 (∫⁻ ω, (0 : ℝ≥0∞) ∂P)) := by
      refine tendsto_lintegral_of_dominated_convergence (f := fun _ => (0 : ℝ≥0∞)) bnd
        (fun n => hbnd_meas.mul ((measurable_const).indicator (hset_meas n)))
        (fun n => Eventually.of_forall fun ω => ?_)
        hbnd_ne (Eventually.of_forall fun ω => ?_)
      · calc G n ω = bnd ω * Set.indicator {x | Real.sqrt n * a < |Φ x|} 1 ω := rfl
          _ ≤ bnd ω * 1 := by
              gcongr; rw [Set.indicator_apply]; split_ifs <;> simp
          _ = bnd ω := mul_one _
      · -- pointwise `G n ω → 0`: eventually the indicator is `0`.
        have hev : (fun n : ℕ => G n ω) =ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) := by
          have hsn0 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
            Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
          have hsn : Tendsto (fun n : ℕ => Real.sqrt n * a) atTop atTop :=
            Tendsto.atTop_mul_const ha hsn0
          filter_upwards [hsn.eventually_gt_atTop (|Φ ω|)] with n hn
          simp only [hG]
          have hnot : ω ∉ {x | Real.sqrt n * a < |Φ x|} := by
            simp only [Set.mem_setOf_eq]; linarith
          rw [Set.indicator_of_notMem hnot, mul_zero]
        exact tendsto_const_nhds.congr' hev.symm
    simpa using hlim
  -- Squeeze the target between `0` and `∫⁻ G n`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hDCT
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  -- `ofReal(√n)·∫⁻(ofReal|Φ|·ind) = ∫⁻ ofReal(√n)·(ofReal|Φ|·ind) ≤ ∫⁻ G n`.
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  simp only [hG, hbnd]
  by_cases hω : ω ∈ {x | Real.sqrt n * a < |Φ x|}
  · have hωlt : Real.sqrt n * a < |Φ ω| := hω
    rw [Set.indicator_of_mem hω]
    simp only [Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hsn_le : Real.sqrt n ≤ |Φ ω| / a := by rw [le_div_iff₀ ha]; linarith
    calc Real.sqrt n * |Φ ω| ≤ (|Φ ω| / a) * |Φ ω| :=
          mul_le_mul_of_nonneg_right hsn_le (abs_nonneg _)
      _ = |Φ ω| ^ 2 / a := by ring
  · rw [Set.indicator_of_notMem hω]; simp

/-! ### Free-scale localized chaining bound for the scaled shell -/

/-- **Free-scale localized chaining bound (scaled shell).**  The localized maximal inequality
for the empirical process over `localizedDifferenceClass (scaledShell_M) P s`, at a **free**
localization scale `s` decoupled from the shell radius `M`, with a **uniform** constant `c`
(over `n`, hence over the varying `scaledIncrement m θ₀ n`) and clamp lower bound `Mc ≥ cM·s`.

Mirrors `LipschitzShellModulus.localizedChainBound_shell_MLower` but (a) uses
`scaledIncrement m θ₀ n` (centred at `0`, radius `M`), (b) keeps `s` free (not `= δ·(‖menv‖₂+1)`),
feeding the free-scale `N*` of `shell_localizedDiff_bracketingNumber_freeS`. -/
theorem scaledShell_localizedChainBound_freeS {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (hX_law : μ.map (X 0) = P)
    (M : ℝ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℝ, 0 < s → s ≤ min M (1 / 4) → ∃ cM : ℝ, 0 < cM ∧
        ∀ n : ℕ, 1 ≤ n → M ≤ ρ * Real.sqrt n →
        ∃ Mc : ℝ, cM * s ≤ Mc ∧ 0 < Mc ∧
          ∫⁻ ξ, supNormOver
              (localizedDifferenceClass
                (paramClass (shellPsi (scaledIncrement m θ₀ n) 0) (Metric.ball 0 M)) P s)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
            ≤ ENNReal.ofReal c
                * bracketingEntropyIntegral s
                    (paramClass (shellPsi (scaledIncrement m θ₀ n) 0) (Metric.ball 0 M)) P
              + ENNReal.ofReal c
                  * (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv M ω|)
                        * Set.indicator {x | Real.sqrt n * Mc < |shellDiffEnvelope menv M x|}
                            1 ω ∂P) := by
  classical
  -- Step 1: choose the `F`-independent uniform constant `c₀`.
  obtain ⟨c₀, hc₀_one, hengine⟩ :=
    chain_supnorm_dyadic_bound_uniform (P := P) (μ := μ) hX_meas hX_indep hX_id hX_law
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le one_pos hc₀_one
  -- Step 2: the `m`-uniform free-scale relative bracketing count constant (centre `0`, radius `M`).
  obtain ⟨Cbn, hCbn_pos, hfreeBN⟩ :=
    shell_localizedDiff_bracketingNumber_freeS P (0 : EuclideanSpace ℝ (Fin d))
      menv hmenv hmenv_meas M hM
  refine ⟨c₀ * (4 * Real.sqrt 2) + 4 * c₀, by positivity, fun s hs hsle => ?_⟩
  have hsM : s ≤ M := le_trans hsle (min_le_left _ _)
  have hs4 : s ≤ 1 / 4 := le_trans hsle (min_le_right _ _)
  -- The `n`-uniform bracketing count value (depends only on `d, Cbn, M, s`).
  set Nval : ℕ := ⌊(d : ℝ) * (4 * Cbn * M / s) ^ d⌋₊ ^ 2 with hNval_def
  refine ⟨min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((Nval * Nval : ℕ) : ℝ))))))
        (1 / (1 + Real.sqrt (Real.log (1 + (Nval : ℝ))))), by positivity, fun n hn hnρ => ?_⟩
  -- Step 3: the `√n`-scaled shell class at radius `M`, centred at `0`, and its regularity.
  set F : Set (Ω → ℝ) :=
    paramClass (shellPsi (scaledIncrement m θ₀ n) 0) (Metric.ball 0 M) with hF_def
  -- Small-`n` guard: on `closedBall 0 M`, `‖θ‖ ≤ M ≤ ρ·√n`, so the local `hLip` applies.
  have hguard : ∀ θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M,
      ‖θ‖ ≤ ρ * Real.sqrt n := by
    intro θ hθ
    have hθM : ‖θ‖ ≤ M := by rw [← dist_zero_right]; exact Metric.mem_closedBall.mp hθ
    exact hθM.trans hnρ
  have hInc_lip : ∀ θ₁ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M,
      ∀ θ₂ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M, ∀ ω,
      |scaledIncrement m θ₀ n θ₁ ω - scaledIncrement m θ₀ n θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖ :=
    fun θ₁ hθ₁ θ₂ hθ₂ ω =>
      scaledIncrement_lipschitz m θ₀ menv ρ hρ hLip hn θ₁ θ₂
        (hguard θ₁ hθ₁) (hguard θ₂ hθ₂) ω
  have hInc_meas : ∀ θ, Measurable (scaledIncrement m θ₀ n θ) :=
    fun θ => scaledIncrement_measurable m θ₀ n hm_meas θ
  have h0_mem : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M := by
    rw [Metric.mem_ball]; simpa using hM
  have hΘ_bdd : Bornology.IsBounded (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M) :=
    Metric.isBounded_ball
  have hψ_meas : ∀ θ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M, ∀ j : Fin d,
      Measurable (shellPsi (scaledIncrement m θ₀ n) 0 θ j) :=
    fun θ _ j => (hInc_meas θ).sub (hInc_meas 0)
  have hψ_L2 : ∀ θ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M, ∀ j : Fin d,
      MemLp (shellPsi (scaledIncrement m θ₀ n) 0 θ j) 2 P :=
    fun θ hθ j => shellPsi_memLp (scaledIncrement m θ₀ n) 0 hInc_meas menv hmenv M hM hInc_lip θ
      (Metric.ball_subset_closedBall hθ) j
  have hψLip : ∀ θ₁ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M,
      ∀ θ₂ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M, ∀ (j : Fin d) (x : Ω),
      |shellPsi (scaledIncrement m θ₀ n) 0 θ₁ j x - shellPsi (scaledIncrement m θ₀ n) 0 θ₂ j x|
        ≤ menv x * ‖θ₁ - θ₂‖ :=
    fun θ₁ hθ₁ θ₂ hθ₂ j x => shellPsi_lipschitz (scaledIncrement m θ₀ n) 0 menv M hM hInc_lip θ₁
      (Metric.ball_subset_closedBall hθ₁) θ₂ (Metric.ball_subset_closedBall hθ₂) j x
  have hF_int : bracketingEntropyIntegral 1 F P < ⊤ :=
    parametricClass_bracketingEntropyIntegral_lt_top P (shellPsi (scaledIncrement m θ₀ n) 0)
      (Metric.ball 0 M) hΘ_bdd menv hmenv hmenv_meas hψ_meas hψ_L2 hψLip
  have hF_ne : F.Nonempty :=
    ⟨shellPsi (scaledIncrement m θ₀ n) 0 0 ⟨0, hd⟩, ⟨0, h0_mem, ⟨0, hd⟩, rfl⟩⟩
  have hF_meas : ∀ f ∈ F, Measurable f := by
    rintro _ ⟨θ, _, j, rfl⟩; exact (hInc_meas θ).sub (hInc_meas 0)
  -- Step 4: envelope `Φ = shellDiffEnvelope menv M = 2M|menv|` of the difference class.
  have hΦ_meas : Measurable (shellDiffEnvelope menv M) := by
    unfold shellDiffEnvelope; exact hmenv_meas.norm.const_mul _
  have hΦ_L2 : MemLp (shellDiffEnvelope menv M) 2 P := by
    have hEq : shellDiffEnvelope menv M = fun ω => (2 * M) * ‖menv ω‖ := rfl
    rw [hEq]; exact hmenv.norm.const_mul' (2 * M)
  have hΦ_env : IsEnvelope (differenceClass F) (shellDiffEnvelope menv M) := by
    rintro _ ⟨f, g, ⟨θ, hθ, j, rfl⟩, ⟨θ', hθ', j', rfl⟩, rfl⟩ x
    simp only [shellPsi, shellDiffEnvelope]
    have heq : scaledIncrement m θ₀ n θ x - scaledIncrement m θ₀ n 0 x
        - (scaledIncrement m θ₀ n θ' x - scaledIncrement m θ₀ n 0 x)
        = scaledIncrement m θ₀ n θ x - scaledIncrement m θ₀ n θ' x := by ring
    rw [heq]
    have h2 : ‖θ - θ'‖ ≤ 2 * M := by
      have hθn : ‖θ‖ < M := by
        have := Metric.mem_ball.mp hθ; rwa [dist_zero_right] at this
      have hθ'n : ‖θ'‖ < M := by
        have := Metric.mem_ball.mp hθ'; rwa [dist_zero_right] at this
      calc ‖θ - θ'‖ ≤ ‖θ‖ + ‖θ'‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith
    calc |scaledIncrement m θ₀ n θ x - scaledIncrement m θ₀ n θ' x|
        ≤ menv x * ‖θ - θ'‖ :=
          hInc_lip θ (Metric.ball_subset_closedBall hθ) θ' (Metric.ball_subset_closedBall hθ') x
      _ ≤ |menv x| * (2 * M) :=
          mul_le_mul (le_abs_self _) h2 (norm_nonneg _) (abs_nonneg _)
      _ = 2 * M * ‖menv x‖ := by rw [Real.norm_eq_abs]; ring
  -- Step 5: the `F`-independent-constant core construction at scale `s`.
  obtain ⟨Mc, hMc_pos, _, hMc_Nbd, hbound⟩ :=
    localized_core_construction (F := F) hF_ne hF_meas hF_int
      μ X hX_meas hX_indep hX_id hX_law c₀ hc₀_one hengine
      (shellDiffEnvelope menv M) hΦ_meas hΦ_env hΦ_L2 hs hs4
  -- Feed the `n`-uniform count `Nval` into the clamp lower bound to get `cM·s ≤ Mc`.
  have hbn := hfreeBN (scaledIncrement m θ₀ n) hInc_meas hInc_lip s hs hsM
  rw [← hF_def] at hbn
  have hb1 : bracketingNumber s (localizedDifferenceClass F P s) 2 P ≤ (Nval : ℕ∞) := by
    rw [hNval_def]; exact hbn.1
  have hb2 : bracketingNumber (s / 2) (localizedDifferenceClass F P s) 2 P ≤ (Nval : ℕ∞) := by
    rw [hNval_def]; exact hbn.2
  exact ⟨Mc, hMc_Nbd Nval hb1 hb2, hMc_pos, hbound n hn⟩

/-- The free-scale localized chaining bound for an arbitrary deterministic local rate.
The empirical-process normalization and the envelope-tail threshold remain at `√n`; only the
criterion shell is reparametrized by `r n`. -/
theorem scaledShellAt_localizedChainBound_freeS
    {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ)) (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (hmenv_meas : Measurable menv) (ρ : ℝ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
      |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (r : ℕ → ℝ) (M : ℝ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 < s → s ≤ min M (1 / 4) → ∃ cM : ℝ, 0 < cM ∧
      ∀ n : ℕ, 1 ≤ n → 0 < r n → M ≤ ρ * r n → ∃ Mc : ℝ, cM * s ≤ Mc ∧ 0 < Mc ∧
      ∫⁻ ξ, supNormOver
          (localizedDifferenceClass
            (paramClass (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 M)) P s)
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal c * bracketingEntropyIntegral s
            (paramClass (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 M)) P
          + ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n) *
            ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv M ω|) *
              Set.indicator {x | Real.sqrt n * Mc < |shellDiffEnvelope menv M x|} 1 ω ∂P) := by
  classical
  obtain ⟨c₀, hc₀_one, hengine⟩ :=
    chain_supnorm_dyadic_bound_uniform (P := P) (μ := μ) hX_meas hX_indep hX_id hX_law
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le one_pos hc₀_one
  obtain ⟨Cbn, hCbn_pos, hfreeBN⟩ :=
    shell_localizedDiff_bracketingNumber_freeS P (0 : EuclideanSpace ℝ (Fin d))
      menv hmenv hmenv_meas M hM
  refine ⟨c₀ * (4 * Real.sqrt 2) + 4 * c₀, by positivity, fun s hs hsle => ?_⟩
  have hsM : s ≤ M := le_trans hsle (min_le_left _ _)
  have hs4 : s ≤ 1 / 4 := le_trans hsle (min_le_right _ _)
  set Nval : ℕ := ⌊(d : ℝ) * (4 * Cbn * M / s) ^ d⌋₊ ^ 2 with hNval_def
  refine ⟨min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((Nval * Nval : ℕ) : ℝ))))))
      (1 / (1 + Real.sqrt (Real.log (1 + (Nval : ℝ))))), by positivity,
    fun n hn hrn hnρ => ?_⟩
  set F : Set (Ω → ℝ) :=
    paramClass (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 M) with hF_def
  have hguard : ∀ θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M,
      ‖θ‖ ≤ ρ * r n := by
    intro θ hθ
    have hθM : ‖θ‖ ≤ M := by
      rw [← dist_zero_right]
      exact Metric.mem_closedBall.mp hθ
    exact hθM.trans hnρ
  have hInc_lip : ∀ θ₁ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M,
      ∀ θ₂ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M, ∀ ω,
      |scaledIncrementAt r m θ₀ n θ₁ ω - scaledIncrementAt r m θ₀ n θ₂ ω|
        ≤ menv ω * ‖θ₁ - θ₂‖ :=
    fun θ₁ hθ₁ θ₂ hθ₂ ω =>
      scaledIncrementAt_lipschitz r m θ₀ menv ρ hLip hrn θ₁ θ₂
        (hguard θ₁ hθ₁) (hguard θ₂ hθ₂) ω
  have hInc_meas : ∀ θ, Measurable (scaledIncrementAt r m θ₀ n θ) :=
    fun θ => scaledIncrementAt_measurable r m θ₀ n hm_meas θ
  have h0_mem : (0 : EuclideanSpace ℝ (Fin d)) ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M := by
    rw [Metric.mem_ball]
    simpa using hM
  have hΘ_bdd : Bornology.IsBounded (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M) :=
    Metric.isBounded_ball
  have hψ_meas : ∀ θ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M, ∀ j : Fin d,
      Measurable (shellPsi (scaledIncrementAt r m θ₀ n) 0 θ j) :=
    fun θ _ j => (hInc_meas θ).sub (hInc_meas 0)
  have hψ_L2 : ∀ θ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M, ∀ j : Fin d,
      MemLp (shellPsi (scaledIncrementAt r m θ₀ n) 0 θ j) 2 P :=
    fun θ hθ j => shellPsi_memLp (scaledIncrementAt r m θ₀ n) 0 hInc_meas menv hmenv M hM
      hInc_lip θ (Metric.ball_subset_closedBall hθ) j
  have hψLip : ∀ θ₁ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M,
      ∀ θ₂ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M, ∀ (j : Fin d) (x : Ω),
      |shellPsi (scaledIncrementAt r m θ₀ n) 0 θ₁ j x -
          shellPsi (scaledIncrementAt r m θ₀ n) 0 θ₂ j x| ≤ menv x * ‖θ₁ - θ₂‖ :=
    fun θ₁ hθ₁ θ₂ hθ₂ j x =>
      shellPsi_lipschitz (scaledIncrementAt r m θ₀ n) 0 menv M hM hInc_lip θ₁
        (Metric.ball_subset_closedBall hθ₁) θ₂ (Metric.ball_subset_closedBall hθ₂) j x
  have hF_int : bracketingEntropyIntegral 1 F P < ⊤ :=
    parametricClass_bracketingEntropyIntegral_lt_top P
      (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 M) hΘ_bdd menv hmenv
      hmenv_meas hψ_meas hψ_L2 hψLip
  have hF_ne : F.Nonempty :=
    ⟨shellPsi (scaledIncrementAt r m θ₀ n) 0 0 ⟨0, hd⟩, ⟨0, h0_mem, ⟨0, hd⟩, rfl⟩⟩
  have hF_meas : ∀ f ∈ F, Measurable f := by
    rintro _ ⟨θ, _, j, rfl⟩
    exact (hInc_meas θ).sub (hInc_meas 0)
  have hΦ_meas : Measurable (shellDiffEnvelope menv M) := by
    unfold shellDiffEnvelope
    exact hmenv_meas.norm.const_mul _
  have hΦ_L2 : MemLp (shellDiffEnvelope menv M) 2 P := by
    have hEq : shellDiffEnvelope menv M = fun ω => (2 * M) * ‖menv ω‖ := rfl
    rw [hEq]
    exact hmenv.norm.const_mul' (2 * M)
  have hΦ_env : IsEnvelope (differenceClass F) (shellDiffEnvelope menv M) := by
    rintro _ ⟨f, g, ⟨θ, hθ, j, rfl⟩, ⟨θ', hθ', j', rfl⟩, rfl⟩ x
    simp only [shellPsi, shellDiffEnvelope]
    have heq : scaledIncrementAt r m θ₀ n θ x - scaledIncrementAt r m θ₀ n 0 x
        - (scaledIncrementAt r m θ₀ n θ' x - scaledIncrementAt r m θ₀ n 0 x)
        = scaledIncrementAt r m θ₀ n θ x - scaledIncrementAt r m θ₀ n θ' x := by
      ring
    rw [heq]
    have h2 : ‖θ - θ'‖ ≤ 2 * M := by
      have hθn : ‖θ‖ < M := by
        have := Metric.mem_ball.mp hθ
        rwa [dist_zero_right] at this
      have hθ'n : ‖θ'‖ < M := by
        have := Metric.mem_ball.mp hθ'
        rwa [dist_zero_right] at this
      calc ‖θ - θ'‖ ≤ ‖θ‖ + ‖θ'‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith
    calc |scaledIncrementAt r m θ₀ n θ x - scaledIncrementAt r m θ₀ n θ' x|
        ≤ menv x * ‖θ - θ'‖ :=
          hInc_lip θ (Metric.ball_subset_closedBall hθ) θ'
            (Metric.ball_subset_closedBall hθ') x
      _ ≤ |menv x| * (2 * M) :=
          mul_le_mul (le_abs_self _) h2 (norm_nonneg _) (abs_nonneg _)
      _ = 2 * M * ‖menv x‖ := by rw [Real.norm_eq_abs]; ring
  obtain ⟨Mc, hMc_pos, _, hMc_Nbd, hbound⟩ :=
    localized_core_construction (F := F) hF_ne hF_meas hF_int
      μ X hX_meas hX_indep hX_id hX_law c₀ hc₀_one hengine
      (shellDiffEnvelope menv M) hΦ_meas hΦ_env hΦ_L2 hs hs4
  have hbn := hfreeBN (scaledIncrementAt r m θ₀ n) hInc_meas hInc_lip s hs hsM
  rw [← hF_def] at hbn
  have hb1 : bracketingNumber s (localizedDifferenceClass F P s) 2 P ≤ (Nval : ℕ∞) := by
    rw [hNval_def]
    exact hbn.1
  have hb2 : bracketingNumber (s / 2) (localizedDifferenceClass F P s) 2 P ≤
      (Nval : ℕ∞) := by
    rw [hNval_def]
    exact hbn.2
  exact ⟨Mc, hMc_Nbd Nval hb1 hb2, hMc_pos, hbound n hn⟩

/-! ### Markov bounds -/

/-- **Continuity of the population-mean difference** `θ ↦ ∫ (m_θ − m_{θ₀})` on the localization
ball. The map is Lipschitz with constant `∫|menv|` (`hLip` pointwise +
`integral_mono`) on `closedBall θ₀ ρ`,
hence continuous there.  Localized to the ball because `hLip` is only assumed near `θ₀`. -/
private theorem popMeanDiff_continuous'
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
  refine (LipschitzOnWith.of_dist_le_mul
    (K := Real.toNNReal (∫ ω, |menv ω| ∂P)) (fun θ hθ θ' hθ' => ?_)).continuousOn
  rw [Real.dist_eq, Real.coe_toNNReal _ hL0, dist_eq_norm]
  have hsub : (∫ ω, (m θ ω - m θ₀ ω) ∂P) - (∫ ω, (m θ' ω - m θ₀ ω) ∂P)
      = ∫ ω, (m θ ω - m θ' ω) ∂P := by
    rw [← integral_sub (hdiff_int θ hθ θ₀ (Metric.mem_closedBall_self hρ.le))
      (hdiff_int θ' hθ' θ₀ (Metric.mem_closedBall_self hρ.le))]
    congr 1; funext ω; ring
  rw [hsub]
  calc |∫ ω, (m θ ω - m θ' ω) ∂P|
      ≤ ∫ ω, |m θ ω - m θ' ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, |menv ω| * ‖θ - θ'‖ ∂P := by
        refine integral_mono ((hdiff_int θ hθ θ' hθ').abs) (habs_int.mul_const _) (fun ω => ?_)
        calc |m θ ω - m θ' ω| ≤ menv ω * ‖θ - θ'‖ := hLip θ hθ θ' hθ' ω
          _ ≤ |menv ω| * ‖θ - θ'‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ = (∫ ω, |menv ω| ∂P) * ‖θ - θ'‖ := integral_mul_const _ _

/-- **`P*` is dominated by `μ` on every set:** `P*(A) ≤ μ A`, by
`measure_eq_iInf` and the measurable majorant `1_t`. -/
private theorem outerMeasureStar_le_measure' {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (A : Set Ξ) : μ.outerMeasureStar A ≤ μ A := by
  rw [measure_eq_iInf]
  refine le_iInf fun t => le_iInf fun hts => le_iInf fun ht => ?_
  rw [Measure.outerMeasureStar, outerExpectation]
  calc (⨅ U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U},
          ∫⁻ ω, (U : Ξ → ℝ≥0∞) ω ∂μ)
      ≤ ∫⁻ ω, t.indicator 1 ω ∂μ :=
        iInf_le (fun U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U} =>
          ∫⁻ ω, (U : Ξ → ℝ≥0∞) ω ∂μ) ⟨t.indicator 1, measurable_one.indicator ht, fun ω => ?_⟩
    _ = μ t := lintegral_indicator_one ht
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (hts hω), le_refl]
  · simp only [Set.indicator_of_notMem hω, zero_le]

/-- **Aemeasurability of the parameter-constrained scaled-difference modulus.**

`ξ ↦ sup_{θ,θ' ∈ ball 0 R, ‖θ−θ'‖ < δ} |𝔾ₙ(scaledIncrement θ − scaledIncrement θ')|` is
`AEMeasurable`.  Although the supremum ranges over an uncountable pair-region, the map
`p = (θ,θ') ↦ 𝔾ₙ(inc_{p.1} − inc_{p.2})` is continuous (empirical average is a finite sum of
continuous evaluations; the population integral is continuous via `popMeanDiff_continuous`
composed with the affine reparametrisation `θ ↦ θ₀ + (√n)⁻¹·θ`), so the supremum over the
open pair-region equals the countable supremum over a dense sequence
(`TopologicalSpace.exists_dense_seq`), each slice being measurable.  This is the measurability
input to the outer-Markov step of `sqrtScaled_shell_modulus_bound`. -/
private theorem scaledDiffModulus_aemeasurable
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (n : ℕ) (R δ : ℝ) (hRρ : R ≤ ρ * Real.sqrt n) :
    AEMeasurable (fun ξ : Ξ => supNormOver
        {g : Ω → ℝ | ∃ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ ∧
          g = fun ω => scaledIncrement m θ₀ n p.1 ω - scaledIncrement m θ₀ n p.2 ω}
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) μ := by
  classical
  -- `ContinuousOn` of `θ ↦ m θ x` on the localization ball (Lipschitz via the local `hLip`).
  have hm_conton : ∀ x : Ω,
      ContinuousOn (fun θ : EuclideanSpace ℝ (Fin d) => m θ x) (Metric.closedBall θ₀ ρ) := by
    intro x
    refine (LipschitzOnWith.of_dist_le_mul
      (K := Real.toNNReal |menv x|) (fun θ hθ θ' hθ' => ?_)).continuousOn
    rw [Real.dist_eq, Real.coe_toNNReal _ (abs_nonneg _), dist_eq_norm]
    calc |m θ x - m θ' x| ≤ menv x * ‖θ - θ'‖ := hLip θ hθ θ' hθ' x
      _ ≤ |menv x| * ‖θ - θ'‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have hInc_meas : ∀ θ, Measurable (scaledIncrement m θ₀ n θ) :=
    fun θ => scaledIncrement_measurable m θ₀ n hm_meas θ
  -- The two affine coordinate maps `p' ↦ θ₀ + (√n)⁻¹•p'.1.i`: continuous on the pair-subtype and
  -- landing in `closedBall θ₀ ρ` (via the small-`n` guard `hRρ` + `‖p'.1.i‖ < R`).
  have hg1_cont : Continuous
      (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
          p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
        θ₀ + (Real.sqrt n)⁻¹ • p'.1.1) :=
    continuous_const.add ((continuous_fst.comp continuous_subtype_val).fun_const_smul _)
  have hg2_cont : Continuous
      (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
          p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
        θ₀ + (Real.sqrt n)⁻¹ • p'.1.2) :=
    continuous_const.add ((continuous_snd.comp continuous_subtype_val).fun_const_smul _)
  have hmem_ball : ∀ (v : EuclideanSpace ℝ (Fin d)), v ∈ Metric.ball 0 R →
      θ₀ + (Real.sqrt n)⁻¹ • v ∈ Metric.closedBall θ₀ ρ := by
    intro v hv
    have hnorm : ‖v‖ < R := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hv
    have hsqrt_pos : 0 < Real.sqrt n := by
      rcases lt_or_eq_of_le (Real.sqrt_nonneg (n : ℝ)) with h | h
      · exact h
      · exfalso
        have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hnorm
        rw [← h, mul_zero] at hRρ; linarith
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hsqrt_pos), inv_mul_eq_div, div_le_iff₀ hsqrt_pos]
    exact le_of_lt (lt_of_lt_of_le hnorm hRρ)
  have hg1_mem : ∀ p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ},
      θ₀ + (Real.sqrt n)⁻¹ • p'.1.1 ∈ Metric.closedBall θ₀ ρ :=
    fun p' => hmem_ball p'.1.1 p'.2.1
  have hg2_mem : ∀ p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ},
      θ₀ + (Real.sqrt n)⁻¹ • p'.1.2 ∈ Metric.closedBall θ₀ ρ :=
    fun p' => hmem_ball p'.1.2 p'.2.2.1
  -- Integrability of `scaledIncrement v` for `v` in the pair-region.
  have hmenv_int : Integrable menv P := hmenv.integrable one_le_two
  have hInc_int : ∀ v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R,
      Integrable (scaledIncrement m θ₀ n v) P := by
    intro v hv
    have hmemv : θ₀ + (Real.sqrt n)⁻¹ • v ∈ Metric.closedBall θ₀ ρ := hmem_ball v hv
    have hdiff : Integrable (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω) P := by
      refine Integrable.mono' (hmenv_int.abs.mul_const ‖θ₀ + (Real.sqrt n)⁻¹ • v - θ₀‖)
        (((hm_meas _).sub (hm_meas θ₀)).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      calc |m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω|
          ≤ menv ω * ‖θ₀ + (Real.sqrt n)⁻¹ • v - θ₀‖ :=
            hLip _ hmemv _ (Metric.mem_closedBall_self hρ.le) ω
        _ ≤ |menv ω| * ‖θ₀ + (Real.sqrt n)⁻¹ • v - θ₀‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    unfold scaledIncrement
    exact hdiff.const_mul (Real.sqrt n)
  -- `ContinuousOn` of `θ ↦ ∫ (m_θ − m_{θ₀})` on the ball (population term).
  have hpop_conton : ContinuousOn
      (fun θ : EuclideanSpace ℝ (Fin d) => ∫ ω, (m θ ω - m θ₀ ω) ∂P)
      (Metric.closedBall θ₀ ρ) :=
    popMeanDiff_continuous' P m θ₀ hm_meas menv hmenv ρ hρ hLip
  -- Continuity of `p' ↦ 𝔾ₙ(inc_{p'.1.1} − inc_{p'.1.2})` on the pair-subtype.
  have hemp_cont : ∀ ξ : Ξ, Continuous
      (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
          p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => scaledIncrement m θ₀ n p'.1.1 ω - scaledIncrement m θ₀ n p'.1.2 ω)) := by
    intro ξ
    have hinc1 : ∀ x : Ω, Continuous
        (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
          scaledIncrement m θ₀ n p'.1.1 x) := by
      intro x
      simp only [scaledIncrement]
      exact continuous_const.mul
        (((hm_conton x).comp_continuous hg1_cont hg1_mem).sub continuous_const)
    have hinc2 : ∀ x : Ω, Continuous
        (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
          scaledIncrement m θ₀ n p'.1.2 x) := by
      intro x
      simp only [scaledIncrement]
      exact continuous_const.mul
        (((hm_conton x).comp_continuous hg2_cont hg2_mem).sub continuous_const)
    have hsum : Continuous
        (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
          ∑ i : Fin n, (scaledIncrement m θ₀ n p'.1.1 (X i.val ξ)
            - scaledIncrement m θ₀ n p'.1.2 (X i.val ξ))) :=
      continuous_finset_sum Finset.univ (fun i _ =>
        (hinc1 (X i.val ξ)).sub (hinc2 (X i.val ξ)))
    have hint : Continuous
        (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
          ∫ ω, (scaledIncrement m θ₀ n p'.1.1 ω - scaledIncrement m θ₀ n p'.1.2 ω) ∂P) := by
      have heq2 : (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
              ∫ ω, (scaledIncrement m θ₀ n p'.1.1 ω - scaledIncrement m θ₀ n p'.1.2 ω) ∂P)
          = fun p' => (∫ ω, scaledIncrement m θ₀ n p'.1.1 ω ∂P)
              - (∫ ω, scaledIncrement m θ₀ n p'.1.2 ω ∂P) := by
        funext p'
        rw [integral_sub (hInc_int p'.1.1 p'.2.1) (hInc_int p'.1.2 p'.2.2.1)]
      rw [heq2]
      have hpop1 : Continuous
          (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
            ∫ ω, scaledIncrement m θ₀ n p'.1.1 ω ∂P) := by
        have he : (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
                ∫ ω, scaledIncrement m θ₀ n p'.1.1 ω ∂P)
            = fun p' => Real.sqrt n
                * ∫ ω, (m (θ₀ + (Real.sqrt n)⁻¹ • p'.1.1) ω - m θ₀ ω) ∂P := by
          funext p'; unfold scaledIncrement; rw [integral_const_mul]
        rw [he]
        exact continuous_const.mul (hpop_conton.comp_continuous hg1_cont hg1_mem)
      have hpop2 : Continuous
          (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
            ∫ ω, scaledIncrement m θ₀ n p'.1.2 ω ∂P) := by
        have he : (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
                ∫ ω, scaledIncrement m θ₀ n p'.1.2 ω ∂P)
            = fun p' => Real.sqrt n
                * ∫ ω, (m (θ₀ + (Real.sqrt n)⁻¹ • p'.1.2) ω - m θ₀ ω) ∂P := by
          funext p'; unfold scaledIncrement; rw [integral_const_mul]
        rw [he]
        exact continuous_const.mul (hpop_conton.comp_continuous hg2_cont hg2_mem)
      exact hpop1.sub hpop2
    exact (((hsum.const_mul ((n : ℝ)⁻¹)).sub hint).const_mul (Real.sqrt n))
  -- Measurability of each fixed-pair slice `ξ ↦ ofReal|𝔾ₙ(inc_a − inc_b)|`.
  have hmeas_perp : ∀ a b : EuclideanSpace ℝ (Fin d),
      Measurable (fun ξ : Ξ => ENNReal.ofReal
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => scaledIncrement m θ₀ n a ω - scaledIncrement m θ₀ n b ω)|) := by
    intro a b
    have hg : Measurable (fun ω => scaledIncrement m θ₀ n a ω - scaledIncrement m θ₀ n b ω) :=
      (hInc_meas a).sub (hInc_meas b)
    have hE : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => scaledIncrement m θ₀ n a ω - scaledIncrement m θ₀ n b ω)) := by
      unfold empiricalProcess empiricalAvg
      refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum Finset.univ (fun i _ => hg.comp (hX_meas i.val))
    exact hE.abs.ennreal_ofReal
  refine Measurable.aemeasurable ?_
  by_cases hSne : Nonempty {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ}
  · -- Nonempty pair-region: reduce to a countable sup over a dense sequence.
    obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq
      {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
        p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ}
    have hkey : (fun ξ : Ξ => supNormOver
          {g : Ω → ℝ | ∃ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ ∧
            g = fun ω => scaledIncrement m θ₀ n p.1 ω - scaledIncrement m θ₀ n p.2 ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        = fun ξ : Ξ => ⨆ j : ℕ, ENNReal.ofReal
            |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => scaledIncrement m θ₀ n (q j).1.1 ω
                - scaledIncrement m θ₀ n (q j).1.2 ω)| := by
      funext ξ
      apply le_antisymm
      · simp only [supNormOver]
        refine iSup₂_le ?_
        rintro f ⟨p, hp1, hp2, hp3, rfl⟩
        have hΨcont : Continuous
            (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
                p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
              ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => scaledIncrement m θ₀ n p'.1.1 ω
                  - scaledIncrement m θ₀ n p'.1.2 ω)|) :=
          ENNReal.continuous_ofReal.comp (continuous_abs.comp (hemp_cont ξ))
        have hmem : (⟨p, hp1, hp2, hp3⟩ :
            {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ})
            ∈ closure (Set.range q) := hq _
        rw [mem_closure_iff_seq_limit] at hmem
        obtain ⟨y, hy_mem, hy_lim⟩ := hmem
        refine le_of_tendsto ((hΨcont.tendsto ⟨p, hp1, hp2, hp3⟩).comp hy_lim)
          (Eventually.of_forall (fun k => ?_))
        obtain ⟨j, hj⟩ := hy_mem k
        simp only [Function.comp_apply]
        rw [← hj]
        exact le_iSup (fun j : ℕ => ENNReal.ofReal
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => scaledIncrement m θ₀ n (q j).1.1 ω
              - scaledIncrement m θ₀ n (q j).1.2 ω)|) j
      · refine iSup_le (fun j => ?_)
        exact le_supNormOver ⟨(q j).1, (q j).2.1, (q j).2.2.1, (q j).2.2.2, rfl⟩
    rw [hkey]
    exact Measurable.iSup (fun j => hmeas_perp (q j).1.1 (q j).1.2)
  · -- Empty pair-region: the class is empty, so the modulus is identically `0`.
    have hconst : (fun ξ : Ξ => supNormOver
          {g : Ω → ℝ | ∃ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ ∧
            g = fun ω => scaledIncrement m θ₀ n p.1 ω - scaledIncrement m θ₀ n p.2 ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        = fun _ => (0 : ℝ≥0∞) := by
      funext ξ
      refine le_antisymm ?_ (zero_le)
      simp only [supNormOver]
      refine iSup₂_le (fun f hf => ?_)
      obtain ⟨p, hp1, hp2, hp3, -⟩ := hf
      exact absurd ⟨⟨p, hp1, hp2, hp3⟩⟩ hSne
    rw [hconst]
    exact measurable_const

/-- Aemeasurability of the parameter-constrained difference modulus for an arbitrary positive
local rate. -/
private theorem scaledDiffModulusAt_aemeasurable
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
      |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (r : ℕ → ℝ) (n : ℕ) (hrn : 0 < r n)
    (R δ : ℝ) (hRρ : R ≤ ρ * r n) :
    AEMeasurable (fun ξ : Ξ => supNormOver
      {g : Ω → ℝ | ∃ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
        p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ ∧
        g = fun ω => scaledIncrementAt r m θ₀ n p.1 ω - scaledIncrementAt r m θ₀ n p.2 ω}
      (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) μ := by
  classical
  have hm_conton : ∀ x : Ω,
      ContinuousOn (fun θ : EuclideanSpace ℝ (Fin d) => m θ x) (Metric.closedBall θ₀ ρ) := by
    intro x
    refine (LipschitzOnWith.of_dist_le_mul
      (K := Real.toNNReal |menv x|) (fun θ hθ θ' hθ' => ?_)).continuousOn
    rw [Real.dist_eq, Real.coe_toNNReal _ (abs_nonneg _), dist_eq_norm]
    calc |m θ x - m θ' x| ≤ menv x * ‖θ - θ'‖ := hLip θ hθ θ' hθ' x
      _ ≤ |menv x| * ‖θ - θ'‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have hInc_meas : ∀ θ, Measurable (scaledIncrementAt r m θ₀ n θ) :=
    fun θ => scaledIncrementAt_measurable r m θ₀ n hm_meas θ
  have hg1_cont : Continuous
      (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
          p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
        θ₀ + (r n)⁻¹ • p'.1.1) :=
    continuous_const.add ((continuous_fst.comp continuous_subtype_val).fun_const_smul _)
  have hg2_cont : Continuous
      (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
          p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
        θ₀ + (r n)⁻¹ • p'.1.2) :=
    continuous_const.add ((continuous_snd.comp continuous_subtype_val).fun_const_smul _)
  have hmem_ball : ∀ (v : EuclideanSpace ℝ (Fin d)), v ∈ Metric.ball 0 R →
      θ₀ + (r n)⁻¹ • v ∈ Metric.closedBall θ₀ ρ := by
    intro v hv
    have hnorm : ‖v‖ < R := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hv
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hrn), inv_mul_eq_div, div_le_iff₀ hrn]
    exact le_of_lt (lt_of_lt_of_le hnorm hRρ)
  have hg1_mem : ∀ p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ},
      θ₀ + (r n)⁻¹ • p'.1.1 ∈ Metric.closedBall θ₀ ρ :=
    fun p' => hmem_ball p'.1.1 p'.2.1
  have hg2_mem : ∀ p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ},
      θ₀ + (r n)⁻¹ • p'.1.2 ∈ Metric.closedBall θ₀ ρ :=
    fun p' => hmem_ball p'.1.2 p'.2.2.1
  have hmenv_int : Integrable menv P := hmenv.integrable one_le_two
  have hInc_int : ∀ v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R,
      Integrable (scaledIncrementAt r m θ₀ n v) P := by
    intro v hv
    have hmemv : θ₀ + (r n)⁻¹ • v ∈ Metric.closedBall θ₀ ρ := hmem_ball v hv
    have hdiff : Integrable (fun ω => m (θ₀ + (r n)⁻¹ • v) ω - m θ₀ ω) P := by
      refine Integrable.mono' (hmenv_int.abs.mul_const ‖θ₀ + (r n)⁻¹ • v - θ₀‖)
        (((hm_meas _).sub (hm_meas θ₀)).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      calc |m (θ₀ + (r n)⁻¹ • v) ω - m θ₀ ω|
          ≤ menv ω * ‖θ₀ + (r n)⁻¹ • v - θ₀‖ :=
            hLip _ hmemv _ (Metric.mem_closedBall_self hρ.le) ω
        _ ≤ |menv ω| * ‖θ₀ + (r n)⁻¹ • v - θ₀‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    unfold scaledIncrementAt
    exact hdiff.const_mul (r n)
  have hpop_conton : ContinuousOn
      (fun θ : EuclideanSpace ℝ (Fin d) => ∫ ω, (m θ ω - m θ₀ ω) ∂P)
      (Metric.closedBall θ₀ ρ) :=
    popMeanDiff_continuous' P m θ₀ hm_meas menv hmenv ρ hρ hLip
  have hemp_cont : ∀ ξ : Ξ, Continuous
      (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
          p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => scaledIncrementAt r m θ₀ n p'.1.1 ω -
            scaledIncrementAt r m θ₀ n p'.1.2 ω)) := by
    intro ξ
    have hinc1 : ∀ x : Ω, Continuous
        (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
          scaledIncrementAt r m θ₀ n p'.1.1 x) := by
      intro x
      simp only [scaledIncrementAt]
      exact continuous_const.mul
        (((hm_conton x).comp_continuous hg1_cont hg1_mem).sub continuous_const)
    have hinc2 : ∀ x : Ω, Continuous
        (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
          scaledIncrementAt r m θ₀ n p'.1.2 x) := by
      intro x
      simp only [scaledIncrementAt]
      exact continuous_const.mul
        (((hm_conton x).comp_continuous hg2_cont hg2_mem).sub continuous_const)
    have hsum : Continuous
        (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
          ∑ i : Fin n, (scaledIncrementAt r m θ₀ n p'.1.1 (X i.val ξ) -
            scaledIncrementAt r m θ₀ n p'.1.2 (X i.val ξ))) :=
      continuous_finset_sum Finset.univ (fun i _ =>
        (hinc1 (X i.val ξ)).sub (hinc2 (X i.val ξ)))
    have hint : Continuous
        (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
          ∫ ω, (scaledIncrementAt r m θ₀ n p'.1.1 ω -
            scaledIncrementAt r m θ₀ n p'.1.2 ω) ∂P) := by
      have heq2 : (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
              ∫ ω, (scaledIncrementAt r m θ₀ n p'.1.1 ω -
                scaledIncrementAt r m θ₀ n p'.1.2 ω) ∂P)
          = fun p' => (∫ ω, scaledIncrementAt r m θ₀ n p'.1.1 ω ∂P) -
              (∫ ω, scaledIncrementAt r m θ₀ n p'.1.2 ω ∂P) := by
        funext p'
        rw [integral_sub (hInc_int p'.1.1 p'.2.1) (hInc_int p'.1.2 p'.2.2.1)]
      rw [heq2]
      have hpop1 : Continuous
          (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
            ∫ ω, scaledIncrementAt r m θ₀ n p'.1.1 ω ∂P) := by
        have he : (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
                ∫ ω, scaledIncrementAt r m θ₀ n p'.1.1 ω ∂P)
            = fun p' => r n * ∫ ω, (m (θ₀ + (r n)⁻¹ • p'.1.1) ω - m θ₀ ω) ∂P := by
          funext p'; unfold scaledIncrementAt; rw [integral_const_mul]
        rw [he]
        exact continuous_const.mul (hpop_conton.comp_continuous hg1_cont hg1_mem)
      have hpop2 : Continuous
          (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
            ∫ ω, scaledIncrementAt r m θ₀ n p'.1.2 ω ∂P) := by
        have he : (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
                ∫ ω, scaledIncrementAt r m θ₀ n p'.1.2 ω ∂P)
            = fun p' => r n * ∫ ω, (m (θ₀ + (r n)⁻¹ • p'.1.2) ω - m θ₀ ω) ∂P := by
          funext p'; unfold scaledIncrementAt; rw [integral_const_mul]
        rw [he]
        exact continuous_const.mul (hpop_conton.comp_continuous hg2_cont hg2_mem)
      exact hpop1.sub hpop2
    exact (((hsum.const_mul ((n : ℝ)⁻¹)).sub hint).const_mul (Real.sqrt n))
  have hmeas_perp : ∀ a b : EuclideanSpace ℝ (Fin d),
      Measurable (fun ξ : Ξ => ENNReal.ofReal
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => scaledIncrementAt r m θ₀ n a ω - scaledIncrementAt r m θ₀ n b ω)|) := by
    intro a b
    have hg : Measurable (fun ω => scaledIncrementAt r m θ₀ n a ω -
        scaledIncrementAt r m θ₀ n b ω) := (hInc_meas a).sub (hInc_meas b)
    have hE : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => scaledIncrementAt r m θ₀ n a ω - scaledIncrementAt r m θ₀ n b ω)) := by
      unfold empiricalProcess empiricalAvg
      refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum Finset.univ (fun i _ => hg.comp (hX_meas i.val))
    exact hE.abs.ennreal_ofReal
  refine Measurable.aemeasurable ?_
  by_cases hSne : Nonempty {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ}
  · obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq
      {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
        p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ}
    have hkey : (fun ξ : Ξ => supNormOver
          {g : Ω → ℝ | ∃ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ ∧
            g = fun ω => scaledIncrementAt r m θ₀ n p.1 ω - scaledIncrementAt r m θ₀ n p.2 ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        = fun ξ : Ξ => ⨆ j : ℕ, ENNReal.ofReal
            |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => scaledIncrementAt r m θ₀ n (q j).1.1 ω -
                scaledIncrementAt r m θ₀ n (q j).1.2 ω)| := by
      funext ξ
      apply le_antisymm
      · simp only [supNormOver]
        refine iSup₂_le ?_
        rintro f ⟨p, hp1, hp2, hp3, rfl⟩
        have hΨcont : Continuous
            (fun p' : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
                p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ} =>
              ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => scaledIncrementAt r m θ₀ n p'.1.1 ω -
                  scaledIncrementAt r m θ₀ n p'.1.2 ω)|) :=
          ENNReal.continuous_ofReal.comp (continuous_abs.comp (hemp_cont ξ))
        have hmem : (⟨p, hp1, hp2, hp3⟩ :
            {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ})
            ∈ closure (Set.range q) := hq _
        rw [mem_closure_iff_seq_limit] at hmem
        obtain ⟨y, hy_mem, hy_lim⟩ := hmem
        refine le_of_tendsto ((hΨcont.tendsto ⟨p, hp1, hp2, hp3⟩).comp hy_lim)
          (Eventually.of_forall (fun k => ?_))
        obtain ⟨j, hj⟩ := hy_mem k
        simp only [Function.comp_apply]
        rw [← hj]
        exact le_iSup (fun j : ℕ => ENNReal.ofReal
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => scaledIncrementAt r m θ₀ n (q j).1.1 ω -
              scaledIncrementAt r m θ₀ n (q j).1.2 ω)|) j
      · refine iSup_le (fun j => ?_)
        exact le_supNormOver ⟨(q j).1, (q j).2.1, (q j).2.2.1, (q j).2.2.2, rfl⟩
    rw [hkey]
    exact Measurable.iSup (fun j => hmeas_perp (q j).1.1 (q j).1.2)
  · have hconst : (fun ξ : Ξ => supNormOver
          {g : Ω → ℝ | ∃ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ ∧
            g = fun ω => scaledIncrementAt r m θ₀ n p.1 ω - scaledIncrementAt r m θ₀ n p.2 ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        = fun _ => (0 : ℝ≥0∞) := by
      funext ξ
      refine le_antisymm ?_ (zero_le)
      simp only [supNormOver]
      refine iSup₂_le (fun f hf => ?_)
      obtain ⟨p, hp1, hp2, hp3, -⟩ := hf
      exact absurd ⟨⟨p, hp1, hp2, hp3⟩⟩ hSne
    rw [hconst]
    exact measurable_const

/-! ### The scaled-shell modulus -/

-- The `limsup` argument identifies two copies of the pair-oscillation event,
-- whose defeq check exceeds the default heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- **The √n-scaled shell/linearization modulus vanishes**
(vdV Lemma 19.34 and Theorem 19.28).

Exactly the conclusion of `LinearizationEquicontinuity.sqrtScaled_shell_modulus_tendstoZero`
in the form required by the bracketing argument. The envelope is assumed measurable. -/
theorem sqrtScaled_shell_modulus_bound
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
    (hX_law : μ.map (X 0) = P)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      limsup (fun n => μ.outerMeasureStar
        {ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}, ‖h₁.1 - h₂.1‖ < δ ∧
          ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|})
        atTop ≤ ENNReal.ofReal η := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- `d = 0`: `EuclideanSpace ℝ (Fin 0)` is a subsingleton ⇒ `h₁.1 = h₂.1` ⇒ oscillation `0`.
    subst hd0
    intro ε hε η hη
    refine ⟨1, one_pos, ?_⟩
    refine Filter.limsup_le_of_le isCobounded_le_of_bot (Eventually.of_forall fun n => ?_)
    refine le_trans (outerMeasureStar_mono μ (show _ ⊆ (∅ : Set Ξ) from ?_)) ?_
    · rintro ξ ⟨h₁, h₂, _, hosc⟩
      have hh : h₁.1 = h₂.1 := Subsingleton.elim _ _
      rw [hh] at hosc
      simp only [sub_self, abs_zero] at hosc
      exact absurd hosc (not_lt.mpr hε.le)
    · rw [outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
      exact zero_le
  · intro ε hε η hη
    rcases eq_or_lt_of_le hM with hM0 | hM'
    · -- `M = 0`: `‖h‖ ≤ 0` ⇒ `h = 0` ⇒ `h₁.1 = h₂.1`.
      refine ⟨1, one_pos, ?_⟩
      refine Filter.limsup_le_of_le isCobounded_le_of_bot (Eventually.of_forall fun n => ?_)
      refine le_trans (outerMeasureStar_mono μ (show _ ⊆ (∅ : Set Ξ) from ?_)) ?_
      · rintro ξ ⟨h₁, h₂, _, hosc⟩
        have hh1 : h₁.1 = 0 := norm_le_zero_iff.mp (hM0 ▸ h₁.2)
        have hh2 : h₂.1 = 0 := norm_le_zero_iff.mp (hM0 ▸ h₂.2)
        rw [hh1, hh2] at hosc
        simp only [sub_self, abs_zero] at hosc
        exact absurd hosc (not_lt.mpr hε.le)
      · rw [outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
        exact zero_le
    · -- The scaled-shell argument for `0 < M`.
      -- Constants.
      set Kmenv : ℝ := (eLpNorm menv 2 P).toReal + 1 with hKmenv_def
      have hKmenv_pos : 0 < Kmenv := by
        have := ENNReal.toReal_nonneg (a := eLpNorm menv 2 P); rw [hKmenv_def]; linarith
      set R : ℝ := 2 * M with hR_def
      have hR_pos : 0 < R := by rw [hR_def]; linarith
      -- **Small-`n` threshold `N₀ := ⌈(R/ρ)²⌉`**: for `n ≥ N₀` the scaled shell of radius `R`
      -- lies in `closedBall θ₀ ρ` (i.e. `R ≤ ρ·√n`), so the local `hLip` applies.  The final
      -- `limsup` ignores the finite prefix `n < N₀`.
      set N₀ : ℕ := ⌈(R / ρ) ^ 2⌉₊ with hN₀_def
      have hN₀ : ∀ n : ℕ, N₀ ≤ n → R ≤ ρ * Real.sqrt n := by
        intro n hn
        have h1 : (R / ρ) ^ 2 ≤ (n : ℝ) := by
          have hc : (R / ρ) ^ 2 ≤ (N₀ : ℝ) := by rw [hN₀_def]; exact Nat.le_ceil _
          exact hc.trans (by exact_mod_cast hn)
        have h2 : R / ρ ≤ Real.sqrt n := by
          rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ R / ρ)]
          exact Real.sqrt_le_sqrt h1
        rw [div_le_iff₀ hρ] at h2
        exact h2.trans_eq (mul_comm _ _)
      -- Chaining at radius `R = 2M` (so the closed `M`-ball lies in the open `R`-ball).
      obtain ⟨c, hc_pos, hChain⟩ :=
        scaledShell_localizedChainBound_freeS hd P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
          μ X hX_meas hX_indep hX_id hX_law R hR_pos
      -- Entropy bound, centred at `0`.
      obtain ⟨Cent, hCent_pos, hEnt⟩ :=
        shell_bracketingEntropyIntegral_freeS P (0 : EuclideanSpace ℝ (Fin d)) menv hmenv hmenv_meas
      -- `δ ↦ c·bd(Kmenv·δ) → 0`; choose `δ` small.
      have hminpos : (0 : ℝ) < min R (1 / 4) := lt_min hR_pos (by norm_num)
      have hηε_pos : (0 : ℝ) < η * ε := mul_pos hη hε
      have hmul0 : Tendsto (fun δ' : ℝ => Kmenv * δ') (𝓝[>] 0) (𝓝 0) := by
        have h : Tendsto (fun δ' : ℝ => Kmenv * δ') (𝓝 0) (𝓝 (Kmenv * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        rw [mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      have hKδ : Tendsto (fun δ' : ℝ => Kmenv * δ') (𝓝[>] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hmul0, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with δ' hδ'
        simp only [Set.mem_Ioi] at hδ' ⊢
        exact mul_pos hKmenv_pos hδ'
      have hbd_tendsto : Tendsto (fun δ' : ℝ => c * (2 * Real.sqrt (Real.log 2
            + d * |Real.log (2 * Cent * R / (Kmenv * δ'))| + d) * (Kmenv * δ')))
          (𝓝[>] 0) (𝓝 0) := by
        have h0 := (entropyScaleBound_tendsto_zero (d := d) Cent R hCent_pos hR_pos).comp hKδ
        have h1 := h0.const_mul c
        simpa using h1
      have hev : ∀ᶠ δ' in 𝓝[>] (0 : ℝ), 0 < δ' ∧ Kmenv * δ' ≤ min R (1 / 4) ∧
          c * (2 * Real.sqrt (Real.log 2 + d * |Real.log (2 * Cent * R / (Kmenv * δ'))| + d)
              * (Kmenv * δ')) ≤ η * ε := by
        filter_upwards [self_mem_nhdsWithin, hmul0.eventually (Iio_mem_nhds hminpos),
          hbd_tendsto.eventually (Iio_mem_nhds hηε_pos)] with δ' hδ'pos hδ'A hδ'B
        exact ⟨hδ'pos, hδ'A.le, hδ'B.le⟩
      obtain ⟨δ, hδ_pos, hδ_leR4, hδ_bd⟩ := hev.exists
      refine ⟨δ, hδ_pos, ?_⟩
      set s : ℝ := Kmenv * δ with hs_def
      have hs_pos : 0 < s := mul_pos hKmenv_pos hδ_pos
      have hs_leR4 : s ≤ min R (1 / 4) := hδ_leR4
      have hs_le_R : s ≤ R := le_trans hs_leR4 (min_le_left _ _)
      set bdval : ℝ :=
        2 * Real.sqrt (Real.log 2 + d * |Real.log (2 * Cent * R / s)| + d) * s with hbdval_def
      have hbdval_nn : 0 ≤ bdval := by rw [hbdval_def]; positivity
      -- Apply the chaining bound at scale `s`.
      obtain ⟨cM, hcM_pos, hEng⟩ := hChain s hs_pos hs_leR4
      -- The tail envelope `Φ = shellDiffEnvelope menv R = 2R|menv|`.
      have hΦ_meas : Measurable (shellDiffEnvelope menv R) := by
        unfold shellDiffEnvelope; exact hmenv_meas.norm.const_mul _
      have hΦ_L2 : MemLp (shellDiffEnvelope menv R) 2 P := by
        have hEq : shellDiffEnvelope menv R = fun ω => (2 * R) * ‖menv ω‖ := rfl
        rw [hEq]; exact hmenv.norm.const_mul' (2 * R)
      have hεE_ne : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
      have hεE_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
      -- Integrability / Lipschitz of the scaled increment (needs `1 ≤ n`).
      have hmenv_int : Integrable menv P := hmenv.integrable one_le_two
      have hInc_int : ∀ (n : ℕ), M ≤ ρ * Real.sqrt n →
          ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ M →
          Integrable (scaledIncrement m θ₀ n θ) P := by
        intro n hnM θ hθM
        have hsqrt_pos : 0 < Real.sqrt n := by
          rcases lt_or_eq_of_le (Real.sqrt_nonneg (n : ℝ)) with h | h
          · exact h
          · exfalso; rw [← h, mul_zero] at hnM; linarith
        have hmemθ : θ₀ + (Real.sqrt n)⁻¹ • θ ∈ Metric.closedBall θ₀ ρ := by
          rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt_pos), inv_mul_eq_div,
            div_le_iff₀ hsqrt_pos]
          exact hθM.trans hnM
        have hdiff : Integrable (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • θ) ω - m θ₀ ω) P := by
          refine Integrable.mono' (hmenv_int.abs.mul_const ‖θ₀ + (Real.sqrt n)⁻¹ • θ - θ₀‖)
            (((hm_meas _).sub (hm_meas θ₀)).aestronglyMeasurable)
            (Eventually.of_forall fun ω => ?_)
          rw [Real.norm_eq_abs]
          calc |m (θ₀ + (Real.sqrt n)⁻¹ • θ) ω - m θ₀ ω|
              ≤ menv ω * ‖θ₀ + (Real.sqrt n)⁻¹ • θ - θ₀‖ :=
                hLip _ hmemθ _ (Metric.mem_closedBall_self hρ.le) ω
            _ ≤ |menv ω| * ‖θ₀ + (Real.sqrt n)⁻¹ • θ - θ₀‖ :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        unfold scaledIncrement
        exact hdiff.const_mul (Real.sqrt n)
      -- The per-`n` outer-measure bound (for `n ≥ N₀`, where the local `hLip` covers the shell).
      have hkey : ∀ n : ℕ, N₀ ≤ n → μ.outerMeasureStar
          {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}, ‖h₁.1 - h₂.1‖ < δ ∧
            ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|}
          ≤ (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε
            + (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|)
                    * Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                        1 ω ∂P)) / ENNReal.ofReal ε := by
        intro n hn_ge
        rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
        · -- `n = 0`: the empirical process ≡ 0 ⇒ the event is empty.
          subst hn0
          refine le_trans (outerMeasureStar_mono μ (show _ ⊆ (∅ : Set Ξ) from ?_)) ?_
          · rintro ξ ⟨h₁, h₂, _, hosc⟩
            simp only [empiricalProcess_zero, sub_self, abs_zero] at hosc
            exact absurd hosc (not_lt.mpr hε.le)
          · rw [outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
            exact zero_le
        · -- `n ≥ 1`: the Markov chain.  `n ≥ N₀` gives `R ≤ ρ·√n`, so `hLip` covers the shell.
          have hn1 : 1 ≤ n := hn_pos
          have hRρ : R ≤ ρ * Real.sqrt n := hN₀ n hn_ge
          have hMρ : M ≤ ρ * Real.sqrt n := le_trans (by rw [hR_def]; linarith) hRρ
          have hcbguard : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
              ‖v‖ ≤ ρ * Real.sqrt n := by
            intro v hv
            have hvR : ‖v‖ ≤ R := by rw [← dist_zero_right]; exact Metric.mem_closedBall.mp hv
            exact hvR.trans hRρ
          obtain ⟨Mc, hMc_lb, hMc_pos, hEng_bound⟩ := hEng n hn1 hRρ
          -- The parameter-constrained scaled-difference class `Cn`.
          set Cn : Set (Ω → ℝ) :=
            {g : Ω → ℝ | ∃ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
              p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ ∧
              g = fun ω => scaledIncrement m θ₀ n p.1 ω - scaledIncrement m θ₀ n p.2 ω}
            with hCn_def
          -- `inc_θ = shellPsi (scaledIncrement m θ₀ n) 0 θ ⟨0,hd⟩`.
          have hshell : ∀ θ : EuclideanSpace ℝ (Fin d),
              shellPsi (scaledIncrement m θ₀ n) 0 θ ⟨0, hd⟩
                = fun ω => scaledIncrement m θ₀ n θ ω := by
            intro θ; funext ω
            simp only [shellPsi, scaledIncrement_apply_zero, Pi.zero_apply, sub_zero]
          -- `Cn ⊆ localizedDifferenceClass F_n P s`.
          have hCn_loc : Cn ⊆ localizedDifferenceClass
              (paramClass (shellPsi (scaledIncrement m θ₀ n) 0) (Metric.ball 0 R)) P s := by
            rintro g ⟨p, hp1, hp2, hp3, rfl⟩
            have hf : (fun ω => scaledIncrement m θ₀ n p.1 ω)
                ∈ paramClass (shellPsi (scaledIncrement m θ₀ n) 0) (Metric.ball 0 R) :=
              ⟨p.1, hp1, ⟨0, hd⟩, (hshell p.1).symm⟩
            have hg' : (fun ω => scaledIncrement m θ₀ n p.2 ω)
                ∈ paramClass (shellPsi (scaledIncrement m θ₀ n) 0) (Metric.ball 0 R) :=
              ⟨p.2, hp2, ⟨0, hd⟩, (hshell p.2).symm⟩
            have hrad : eLpNorm
                (fun ω => scaledIncrement m θ₀ n p.1 ω - scaledIncrement m θ₀ n p.2 ω) 2 P
                ≤ ENNReal.ofReal s := by
              have hpt : eLpNorm
                  (fun ω => scaledIncrement m θ₀ n p.1 ω - scaledIncrement m θ₀ n p.2 ω) 2 P
                  ≤ eLpNorm (fun ω => δ * menv ω) 2 P := by
                apply eLpNorm_mono
                intro ω
                simp only [Real.norm_eq_abs, abs_mul]
                calc |scaledIncrement m θ₀ n p.1 ω - scaledIncrement m θ₀ n p.2 ω|
                    ≤ menv ω * ‖p.1 - p.2‖ :=
                      scaledIncrement_lipschitz m θ₀ menv ρ hρ hLip hn1 p.1 p.2
                        (hcbguard p.1 (Metric.ball_subset_closedBall hp1))
                        (hcbguard p.2 (Metric.ball_subset_closedBall hp2)) ω
                  _ ≤ |menv ω| * ‖p.1 - p.2‖ :=
                      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
                  _ ≤ |menv ω| * δ := mul_le_mul_of_nonneg_left hp3.le (abs_nonneg _)
                  _ = |δ| * |menv ω| := by rw [abs_of_pos hδ_pos]; ring
              refine le_trans hpt ?_
              have hsmul : (fun ω => δ * menv ω) = δ • menv := by
                funext ω; simp [Pi.smul_apply, smul_eq_mul]
              rw [hsmul, eLpNorm_const_smul]
              have hmenv_ne : eLpNorm menv 2 P ≠ ⊤ := hmenv.eLpNorm_lt_top.ne
              have hnn : 0 ≤ (eLpNorm menv 2 P).toReal := ENNReal.toReal_nonneg
              calc ‖δ‖ₑ * eLpNorm menv 2 P
                  = ENNReal.ofReal δ * ENNReal.ofReal (eLpNorm menv 2 P).toReal := by
                    rw [ENNReal.ofReal_toReal hmenv_ne, Real.enorm_eq_ofReal_abs,
                      abs_of_pos hδ_pos]
                _ = ENNReal.ofReal (δ * (eLpNorm menv 2 P).toReal) :=
                    (ENNReal.ofReal_mul hδ_pos.le).symm
                _ ≤ ENNReal.ofReal s := by
                    apply ENNReal.ofReal_le_ofReal
                    rw [hs_def, hKmenv_def]; nlinarith [hnn, hδ_pos.le]
            exact mem_localizedDifferenceClass hf hg' hrad
          -- Embedding: the event lands in the measurable super-level set of `supNormOver Cn`.
          have hsub : {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
              ‖h₁.1 - h₂.1‖ < δ ∧
              ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                    - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|}
              ⊆ {ξ : Ξ | ENNReal.ofReal ε ≤ supNormOver Cn
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)} := by
            rintro ξ ⟨h₁, h₂, hclose, hosc⟩
            have hp1 : (h₁.1 : EuclideanSpace ℝ (Fin d)) ∈ Metric.ball 0 R := by
              rw [Metric.mem_ball, dist_zero_right]
              exact lt_of_le_of_lt h₁.2 (by rw [hR_def]; linarith)
            have hp2 : (h₂.1 : EuclideanSpace ℝ (Fin d)) ∈ Metric.ball 0 R := by
              rw [Metric.mem_ball, dist_zero_right]
              exact lt_of_le_of_lt h₂.2 (by rw [hR_def]; linarith)
            have hg_mem :
                (fun ω => scaledIncrement m θ₀ n h₁.1 ω - scaledIncrement m θ₀ n h₂.1 ω) ∈ Cn :=
              ⟨(h₁.1, h₂.1), hp1, hp2, hclose, rfl⟩
            have hlin : empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => scaledIncrement m θ₀ n h₁.1 ω - scaledIncrement m θ₀ n h₂.1 ω)
                = empiricalProcess P n (fun i : Fin n => X i.val ξ) (scaledIncrement m θ₀ n h₁.1)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (scaledIncrement m θ₀ n h₂.1) :=
              empiricalProcess_sub P n _ _ _ (hInc_int n hMρ h₁.1 h₁.2) (hInc_int n hMρ h₂.1 h₂.2)
            have hosc' : ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => scaledIncrement m θ₀ n h₁.1 ω - scaledIncrement m θ₀ n h₂.1 ω)| := by
              rw [hlin]; exact hosc
            calc ENNReal.ofReal ε
                ≤ ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => scaledIncrement m θ₀ n h₁.1 ω - scaledIncrement m θ₀ n h₂.1 ω)| :=
                  ENNReal.ofReal_le_ofReal hosc'.le
              _ ≤ supNormOver Cn (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) :=
                  le_supNormOver hg_mem
          -- Aemeasurability of `ξ ↦ supNormOver Cn 𝔾ₙ`.
          have haem : AEMeasurable (fun ξ : Ξ => supNormOver Cn
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) μ := by
            rw [hCn_def]
            exact scaledDiffModulus_aemeasurable P m θ₀ hm_meas menv hmenv ρ hρ hLip μ X hX_meas
              n R δ hRρ
          -- The Markov chain.
          calc μ.outerMeasureStar
                {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}, ‖h₁.1 - h₂.1‖ < δ ∧
                  ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                        - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|}
              ≤ μ.outerMeasureStar {ξ : Ξ | ENNReal.ofReal ε ≤ supNormOver Cn
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)} :=
                outerMeasureStar_mono μ hsub
            _ ≤ μ {ξ : Ξ | ENNReal.ofReal ε ≤ supNormOver Cn
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)} :=
                outerMeasureStar_le_measure' μ _
            _ ≤ (∫⁻ ξ, supNormOver Cn
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ)
                  / ENNReal.ofReal ε := meas_ge_le_lintegral_div haem hεE_ne hεE_ne_top
            _ ≤ (∫⁻ ξ, supNormOver
                  (localizedDifferenceClass
                    (paramClass (shellPsi (scaledIncrement m θ₀ n) 0) (Metric.ball 0 R)) P s)
                  (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ)
                  / ENNReal.ofReal ε :=
                ENNReal.div_le_div_right (lintegral_mono fun ξ => supNormOver_mono hCn_loc _) _
            _ ≤ (ENNReal.ofReal c
                    * bracketingEntropyIntegral s
                        (paramClass (shellPsi (scaledIncrement m θ₀ n) 0) (Metric.ball 0 R)) P
                  + ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                      * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|)
                          * Set.indicator {x | Real.sqrt n * Mc < |shellDiffEnvelope menv R x|}
                              1 ω ∂P)) / ENNReal.ofReal ε :=
                ENNReal.div_le_div_right hEng_bound _
            _ ≤ (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε
                + (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|)
                        * Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                            1 ω ∂P)) / ENNReal.ofReal ε := by
                rw [ENNReal.add_div]
                refine add_le_add (ENNReal.div_le_div_right ?_ _)
                  (ENNReal.div_le_div_right ?_ _)
                · -- Entropy term: `J(s, F_n) ≤ ofReal bdval`, uniformly in `n`.
                  refine mul_le_mul_right ?_ _
                  have hJ := hEnt (scaledIncrement m θ₀ n)
                    (fun θ => scaledIncrement_measurable m θ₀ n hm_meas θ)
                    R hR_pos
                    (fun θ₁ hθ₁ θ₂ hθ₂ ω => scaledIncrement_lipschitz m θ₀ menv ρ hρ hLip hn1
                      θ₁ θ₂ (hcbguard θ₁ hθ₁) (hcbguard θ₂ hθ₂) ω)
                    s hs_pos hs_le_R
                  rw [← hbdval_def] at hJ
                  exact hJ
                · -- tail term: `Mc ≥ cM·s` shrinks the indicator set.
                  refine mul_le_mul_right (mul_le_mul_right ?_ _) _
                  refine lintegral_mono fun ω => mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact Set.indicator_le_indicator_of_subset
                    (fun x hx => lt_of_le_of_lt
                      (mul_le_mul_of_nonneg_left hMc_lb (Real.sqrt_nonneg _)) hx)
                    (fun _ => zero_le) ω
      -- Assemble the `limsup`.
      have hVf_tendsto : Tendsto (fun n : ℕ =>
          (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|)
                * Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                    1 ω ∂P)) / ENNReal.ofReal ε) atTop (𝓝 0) := by
        have hT := envelopeTail_vanishes (shellDiffEnvelope menv R) hΦ_L2 hΦ_meas
          (mul_pos hcM_pos hs_pos)
        have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|)
                * Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                    1 ω ∂P)) atTop (𝓝 0) := by
          have h := ENNReal.Tendsto.const_mul hT (Or.inr (ENNReal.ofReal_ne_top (r := c)))
          rwa [mul_zero] at h
        have h2 := ENNReal.Tendsto.div_const h1 (Or.inr hεE_ne)
        rwa [ENNReal.zero_div] at h2
      have hUf_le : (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε
          ≤ ENNReal.ofReal η := by
        rw [ENNReal.div_le_iff hεE_ne hεE_ne_top, ← ENNReal.ofReal_mul hc_pos.le,
          ← ENNReal.ofReal_mul hη.le]
        exact ENNReal.ofReal_le_ofReal hδ_bd
      calc limsup (fun n => μ.outerMeasureStar
              {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}, ‖h₁.1 - h₂.1‖ < δ ∧
                ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                      - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|})
            atTop
          ≤ limsup (fun n : ℕ => (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε
              + (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|)
                      * Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                          1 ω ∂P)) / ENNReal.ofReal ε) atTop :=
            limsup_le_limsup (Filter.eventually_atTop.mpr ⟨N₀, hkey⟩) isCobounded_le_of_bot
              (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
        _ ≤ (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε :=
            limsup_add_tendsto_zero_le
              (fun _ => (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε)
              (fun n => (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|)
                    * Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                        1 ω ∂P)) / ENNReal.ofReal ε)
              _ (le_of_eq (limsup_const _)) hVf_tendsto
        _ ≤ ENNReal.ofReal η := hUf_le

set_option maxHeartbeats 1000000 in
-- Outer Markov bounds compare the two pair events.
/-- The arbitrary-rate shell modulus vanishes while the empirical process retains its `√n`
normalization. -/
theorem scaledAt_shell_modulus_bound
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
    (hX_law : μ.map (X 0) = P)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      limsup (fun n => μ.outerMeasureStar
        {ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}, ‖h₁.1 - h₂.1‖ < δ ∧
          ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (scaledIncrementAt r m θ₀ n h₁.1) -
              empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (scaledIncrementAt r m θ₀ n h₂.1)|})
        atTop ≤ ENNReal.ofReal η := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    intro ε hε η hη
    refine ⟨1, one_pos, ?_⟩
    refine Filter.limsup_le_of_le isCobounded_le_of_bot (Eventually.of_forall fun n => ?_)
    refine le_trans (outerMeasureStar_mono μ (show _ ⊆ (∅ : Set Ξ) from ?_)) ?_
    · rintro ξ ⟨h₁, h₂, _, hosc⟩
      have hh : h₁.1 = h₂.1 := Subsingleton.elim _ _
      rw [hh] at hosc
      exact absurd hosc (by simp [hε.le])
    · rw [outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
      exact zero_le
  · intro ε hε η hη
    rcases eq_or_lt_of_le hM with hM0 | hM'
    · refine ⟨1, one_pos, ?_⟩
      refine Filter.limsup_le_of_le isCobounded_le_of_bot (Eventually.of_forall fun n => ?_)
      refine le_trans (outerMeasureStar_mono μ (show _ ⊆ (∅ : Set Ξ) from ?_)) ?_
      · rintro ξ ⟨h₁, h₂, _, hosc⟩
        have hh1 : h₁.1 = 0 := norm_le_zero_iff.mp (hM0 ▸ h₁.2)
        have hh2 : h₂.1 = 0 := norm_le_zero_iff.mp (hM0 ▸ h₂.2)
        rw [hh1, hh2] at hosc
        exact absurd hosc (by simp [hε.le])
      · rw [outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
        exact zero_le
    · set Kmenv : ℝ := (eLpNorm menv 2 P).toReal + 1 with hKmenv_def
      have hKmenv_pos : 0 < Kmenv := by
        have := ENNReal.toReal_nonneg (a := eLpNorm menv 2 P)
        rw [hKmenv_def]
        linarith
      set R : ℝ := 2 * M with hR_def
      have hR_pos : 0 < R := by rw [hR_def]; linarith
      obtain ⟨c, hc_pos, hChain⟩ :=
        scaledShellAt_localizedChainBound_freeS hd P m θ₀ hm_meas menv hmenv hmenv_meas ρ
          hLip μ X hX_meas hX_indep hX_id hX_law r R hR_pos
      obtain ⟨Cent, hCent_pos, hEnt⟩ :=
        shell_bracketingEntropyIntegral_freeS P (0 : EuclideanSpace ℝ (Fin d)) menv hmenv
          hmenv_meas
      have hminpos : (0 : ℝ) < min R (1 / 4) := lt_min hR_pos (by norm_num)
      have hηε_pos : (0 : ℝ) < η * ε := mul_pos hη hε
      have hmul0 : Tendsto (fun δ' : ℝ => Kmenv * δ') (𝓝[>] 0) (𝓝 0) := by
        have h : Tendsto (fun δ' : ℝ => Kmenv * δ') (𝓝 0) (𝓝 (Kmenv * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        rw [mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      have hKδ : Tendsto (fun δ' : ℝ => Kmenv * δ') (𝓝[>] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hmul0, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with δ' hδ'
        exact mul_pos hKmenv_pos hδ'
      have hbd_tendsto : Tendsto (fun δ' : ℝ => c * (2 * Real.sqrt (Real.log 2
            + d * |Real.log (2 * Cent * R / (Kmenv * δ'))| + d) * (Kmenv * δ')))
          (𝓝[>] 0) (𝓝 0) := by
        have h0 := (entropyScaleBound_tendsto_zero (d := d) Cent R hCent_pos hR_pos).comp hKδ
        simpa using h0.const_mul c
      have hev : ∀ᶠ δ' in 𝓝[>] (0 : ℝ), 0 < δ' ∧ Kmenv * δ' ≤ min R (1 / 4) ∧
          c * (2 * Real.sqrt (Real.log 2 + d * |Real.log (2 * Cent * R / (Kmenv * δ'))| + d)
            * (Kmenv * δ')) ≤ η * ε := by
        filter_upwards [self_mem_nhdsWithin, hmul0.eventually (Iio_mem_nhds hminpos),
          hbd_tendsto.eventually (Iio_mem_nhds hηε_pos)] with δ' hδ' hA hB
        exact ⟨hδ', hA.le, hB.le⟩
      obtain ⟨δ, hδ_pos, hδ_leR4, hδ_bd⟩ := hev.exists
      refine ⟨δ, hδ_pos, ?_⟩
      set s : ℝ := Kmenv * δ with hs_def
      have hs_pos : 0 < s := mul_pos hKmenv_pos hδ_pos
      have hs_leR4 : s ≤ min R (1 / 4) := hδ_leR4
      have hs_le_R : s ≤ R := hs_leR4.trans (min_le_left _ _)
      set bdval : ℝ :=
        2 * Real.sqrt (Real.log 2 + d * |Real.log (2 * Cent * R / s)| + d) * s with hbdval_def
      have hbdval_nn : 0 ≤ bdval := by rw [hbdval_def]; positivity
      obtain ⟨cM, hcM_pos, hEng⟩ := hChain s hs_pos hs_leR4
      have hΦ_meas : Measurable (shellDiffEnvelope menv R) := by
        unfold shellDiffEnvelope
        exact hmenv_meas.norm.const_mul _
      have hΦ_L2 : MemLp (shellDiffEnvelope menv R) 2 P := by
        have hEq : shellDiffEnvelope menv R = fun ω => (2 * R) * ‖menv ω‖ := rfl
        rw [hEq]
        exact hmenv.norm.const_mul' (2 * R)
      have hεE_ne : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
      have hεE_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
      have hmenv_int : Integrable menv P := hmenv.integrable one_le_two
      have hInc_int : ∀ n : ℕ, 0 < r n → M ≤ ρ * r n →
          ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ M →
          Integrable (scaledIncrementAt r m θ₀ n θ) P := by
        intro n hrn hnM θ hθM
        have hmemθ : θ₀ + (r n)⁻¹ • θ ∈ Metric.closedBall θ₀ ρ := by
          rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrn), inv_mul_eq_div, div_le_iff₀ hrn]
          exact hθM.trans hnM
        have hdiff : Integrable (fun ω => m (θ₀ + (r n)⁻¹ • θ) ω - m θ₀ ω) P := by
          refine Integrable.mono' (hmenv_int.abs.mul_const ‖θ₀ + (r n)⁻¹ • θ - θ₀‖)
            (((hm_meas _).sub (hm_meas θ₀)).aestronglyMeasurable)
            (Eventually.of_forall fun ω => ?_)
          rw [Real.norm_eq_abs]
          calc |m (θ₀ + (r n)⁻¹ • θ) ω - m θ₀ ω|
              ≤ menv ω * ‖θ₀ + (r n)⁻¹ • θ - θ₀‖ :=
                hLip _ hmemθ _ (Metric.mem_closedBall_self hρ.le) ω
            _ ≤ |menv ω| * ‖θ₀ + (r n)⁻¹ • θ - θ₀‖ :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        unfold scaledIncrementAt
        exact hdiff.const_mul (r n)
      have hkey : ∀ᶠ n in atTop, μ.outerMeasureStar
          {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ ∧ ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (scaledIncrementAt r m θ₀ n h₁.1) - empiricalProcess P n
                (fun i : Fin n => X i.val ξ) (scaledIncrementAt r m θ₀ n h₂.1)|}
          ≤ (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε
            + (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n) *
              ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|) *
                Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                  1 ω ∂P)) / ENNReal.ofReal ε := by
        filter_upwards [eventually_ge_atTop 1, hr.eventually (eventually_gt_atTop 0),
          (Filter.Tendsto.const_mul_atTop hρ hr).eventually (eventually_ge_atTop R)]
          with n hn1 hrn hRρ
        have hMρ : M ≤ ρ * r n := (by rw [hR_def]; linarith : M ≤ R).trans hRρ
        have hcbguard : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
            ‖v‖ ≤ ρ * r n := by
          intro v hv
          exact (by rw [← dist_zero_right]; exact Metric.mem_closedBall.mp hv : ‖v‖ ≤ R).trans hRρ
        obtain ⟨Mc, hMc_lb, hMc_pos, hEng_bound⟩ := hEng n hn1 hrn hRρ
        set Cn : Set (Ω → ℝ) :=
          {g : Ω → ℝ | ∃ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
            p.1 ∈ Metric.ball 0 R ∧ p.2 ∈ Metric.ball 0 R ∧ ‖p.1 - p.2‖ < δ ∧
            g = fun ω => scaledIncrementAt r m θ₀ n p.1 ω -
              scaledIncrementAt r m θ₀ n p.2 ω} with hCn_def
        have hshell : ∀ θ : EuclideanSpace ℝ (Fin d),
            shellPsi (scaledIncrementAt r m θ₀ n) 0 θ ⟨0, hd⟩ =
              fun ω => scaledIncrementAt r m θ₀ n θ ω := by
          intro θ
          funext ω
          simp only [shellPsi, scaledIncrementAt_apply_zero, sub_zero]
        have hCn_loc : Cn ⊆ localizedDifferenceClass
            (paramClass (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 R)) P s := by
          rintro g ⟨p, hp1, hp2, hp3, rfl⟩
          have hf : (fun ω => scaledIncrementAt r m θ₀ n p.1 ω) ∈
              paramClass (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 R) :=
            ⟨p.1, hp1, ⟨0, hd⟩, (hshell p.1).symm⟩
          have hg' : (fun ω => scaledIncrementAt r m θ₀ n p.2 ω) ∈
              paramClass (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 R) :=
            ⟨p.2, hp2, ⟨0, hd⟩, (hshell p.2).symm⟩
          have hpt : eLpNorm
              (fun ω => scaledIncrementAt r m θ₀ n p.1 ω - scaledIncrementAt r m θ₀ n p.2 ω)
              2 P ≤ eLpNorm (fun ω => δ * menv ω) 2 P := by
            apply eLpNorm_mono
            intro ω
            simp only [Real.norm_eq_abs, abs_mul]
            calc |scaledIncrementAt r m θ₀ n p.1 ω - scaledIncrementAt r m θ₀ n p.2 ω|
                ≤ menv ω * ‖p.1 - p.2‖ := scaledIncrementAt_lipschitz r m θ₀ menv ρ hLip
                  hrn p.1 p.2 (hcbguard p.1 (Metric.ball_subset_closedBall hp1))
                  (hcbguard p.2 (Metric.ball_subset_closedBall hp2)) ω
              _ ≤ |menv ω| * ‖p.1 - p.2‖ :=
                  mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
              _ ≤ |menv ω| * δ := mul_le_mul_of_nonneg_left hp3.le (abs_nonneg _)
              _ = |δ| * |menv ω| := by rw [abs_of_pos hδ_pos]; ring
          have hrad : eLpNorm
              (fun ω => scaledIncrementAt r m θ₀ n p.1 ω - scaledIncrementAt r m θ₀ n p.2 ω)
              2 P ≤ ENNReal.ofReal s := hpt.trans (by
            have hsmul : (fun ω => δ * menv ω) = δ • menv := by
              funext ω; simp [Pi.smul_apply, smul_eq_mul]
            rw [hsmul, eLpNorm_const_smul]
            have hmenv_ne : eLpNorm menv 2 P ≠ ⊤ := hmenv.eLpNorm_lt_top.ne
            have hnn : 0 ≤ (eLpNorm menv 2 P).toReal := ENNReal.toReal_nonneg
            calc ‖δ‖ₑ * eLpNorm menv 2 P
                = ENNReal.ofReal δ * ENNReal.ofReal (eLpNorm menv 2 P).toReal := by
                  rw [ENNReal.ofReal_toReal hmenv_ne, Real.enorm_eq_ofReal_abs, abs_of_pos hδ_pos]
              _ = ENNReal.ofReal (δ * (eLpNorm menv 2 P).toReal) :=
                  (ENNReal.ofReal_mul hδ_pos.le).symm
              _ ≤ ENNReal.ofReal s := by
                  apply ENNReal.ofReal_le_ofReal
                  rw [hs_def, hKmenv_def]
                  nlinarith [hnn, hδ_pos.le])
          exact mem_localizedDifferenceClass hf hg' hrad
        have hsub : {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ ∧ ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (scaledIncrementAt r m θ₀ n h₁.1) - empiricalProcess P n
                (fun i : Fin n => X i.val ξ) (scaledIncrementAt r m θ₀ n h₂.1)|}
            ⊆ {ξ : Ξ | ENNReal.ofReal ε ≤ supNormOver Cn
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)} := by
          rintro ξ ⟨h₁, h₂, hclose, hosc⟩
          have hp1 : h₁.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R := by
            rw [Metric.mem_ball, dist_zero_right]
            exact lt_of_le_of_lt h₁.2 (by rw [hR_def]; linarith)
          have hp2 : h₂.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R := by
            rw [Metric.mem_ball, dist_zero_right]
            exact lt_of_le_of_lt h₂.2 (by rw [hR_def]; linarith)
          have hg_mem : (fun ω => scaledIncrementAt r m θ₀ n h₁.1 ω -
              scaledIncrementAt r m θ₀ n h₂.1 ω) ∈ Cn :=
            ⟨(h₁.1, h₂.1), hp1, hp2, hclose, rfl⟩
          have hlin := empiricalProcess_sub P n (fun i : Fin n => X i.val ξ)
            (scaledIncrementAt r m θ₀ n h₁.1) (scaledIncrementAt r m θ₀ n h₂.1)
            (hInc_int n hrn hMρ h₁.1 h₁.2) (hInc_int n hrn hMρ h₂.1 h₂.2)
          have hosc' : ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => scaledIncrementAt r m θ₀ n h₁.1 ω -
                scaledIncrementAt r m θ₀ n h₂.1 ω)| := by
            rw [hlin]
            exact hosc
          exact (ENNReal.ofReal_le_ofReal hosc'.le).trans (le_supNormOver hg_mem)
        have haem : AEMeasurable (fun ξ : Ξ => supNormOver Cn
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) μ := by
          rw [hCn_def]
          exact scaledDiffModulusAt_aemeasurable P m θ₀ hm_meas menv hmenv ρ hρ hLip μ X
            hX_meas r n hrn R δ hRρ
        calc μ.outerMeasureStar
              {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
                ‖h₁.1 - h₂.1‖ < δ ∧ ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (scaledIncrementAt r m θ₀ n h₁.1) - empiricalProcess P n
                    (fun i : Fin n => X i.val ξ) (scaledIncrementAt r m θ₀ n h₂.1)|}
            ≤ μ.outerMeasureStar {ξ : Ξ | ENNReal.ofReal ε ≤ supNormOver Cn
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)} :=
              outerMeasureStar_mono μ hsub
          _ ≤ μ {ξ : Ξ | ENNReal.ofReal ε ≤ supNormOver Cn
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)} :=
              outerMeasureStar_le_measure' μ _
          _ ≤ (∫⁻ ξ, supNormOver Cn
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ) /
                ENNReal.ofReal ε := meas_ge_le_lintegral_div haem hεE_ne hεE_ne_top
          _ ≤ (∫⁻ ξ, supNormOver
                (localizedDifferenceClass
                  (paramClass (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 R)) P s)
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ) /
                ENNReal.ofReal ε :=
              ENNReal.div_le_div_right (lintegral_mono fun ξ => supNormOver_mono hCn_loc _) _
          _ ≤ (ENNReal.ofReal c * bracketingEntropyIntegral s
                (paramClass (shellPsi (scaledIncrementAt r m θ₀ n) 0) (Metric.ball 0 R)) P
              + ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n) *
                ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|) *
                  Set.indicator {x | Real.sqrt n * Mc < |shellDiffEnvelope menv R x|} 1 ω ∂P)) /
                ENNReal.ofReal ε := ENNReal.div_le_div_right hEng_bound _
          _ ≤ (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε +
              (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n) *
                ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|) *
                  Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                    1 ω ∂P)) / ENNReal.ofReal ε := by
            rw [ENNReal.add_div]
            refine add_le_add (ENNReal.div_le_div_right ?_ _)
              (ENNReal.div_le_div_right ?_ _)
            · refine mul_le_mul_right ?_ _
              have hJ := hEnt (scaledIncrementAt r m θ₀ n)
                (fun θ => scaledIncrementAt_measurable r m θ₀ n hm_meas θ) R hR_pos
                (fun θ₁ hθ₁ θ₂ hθ₂ ω => scaledIncrementAt_lipschitz r m θ₀ menv ρ hLip
                  hrn θ₁ θ₂ (hcbguard θ₁ hθ₁) (hcbguard θ₂ hθ₂) ω)
                s hs_pos hs_le_R
              rw [← hbdval_def] at hJ
              exact hJ
            · refine mul_le_mul_right (mul_le_mul_right ?_ _) _
              refine lintegral_mono fun ω => mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact Set.indicator_le_indicator_of_subset
                (fun x hx => lt_of_le_of_lt
                  (mul_le_mul_of_nonneg_left hMc_lb (Real.sqrt_nonneg _)) hx)
                (fun _ => zero_le) ω
      have hVf_tendsto : Tendsto (fun n : ℕ =>
          (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n) *
            ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|) *
              Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                1 ω ∂P)) / ENNReal.ofReal ε) atTop (𝓝 0) := by
        have hT := envelopeTail_vanishes (shellDiffEnvelope menv R) hΦ_L2 hΦ_meas
          (mul_pos hcM_pos hs_pos)
        have h1 := ENNReal.Tendsto.const_mul hT (Or.inr (ENNReal.ofReal_ne_top (r := c)))
        rw [mul_zero] at h1
        have h2 := ENNReal.Tendsto.div_const h1 (Or.inr hεE_ne)
        rwa [ENNReal.zero_div] at h2
      have hUf_le : (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε ≤
          ENNReal.ofReal η := by
        rw [ENNReal.div_le_iff hεE_ne hεE_ne_top, ← ENNReal.ofReal_mul hc_pos.le,
          ← ENNReal.ofReal_mul hη.le]
        exact ENNReal.ofReal_le_ofReal hδ_bd
      calc limsup (fun n => μ.outerMeasureStar
              {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
                ‖h₁.1 - h₂.1‖ < δ ∧ ε < |empiricalProcess P n
                  (fun i : Fin n => X i.val ξ) (scaledIncrementAt r m θ₀ n h₁.1) -
                    empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (scaledIncrementAt r m θ₀ n h₂.1)|}) atTop
          ≤ limsup (fun n : ℕ => (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε +
              (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n) *
                ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|) *
                  Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                    1 ω ∂P)) / ENNReal.ofReal ε) atTop :=
            limsup_le_limsup hkey isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
        _ ≤ (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε :=
            limsup_add_tendsto_zero_le
              (fun _ => (ENNReal.ofReal c * ENNReal.ofReal bdval) / ENNReal.ofReal ε)
              (fun n => (ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n) *
                ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv R ω|) *
                  Set.indicator {x | Real.sqrt n * (cM * s) < |shellDiffEnvelope menv R x|}
                    1 ω ∂P)) / ENNReal.ofReal ε)
              _ (le_of_eq (limsup_const _)) hVf_tendsto
        _ ≤ ENNReal.ofReal η := hUf_le

/-! ### Lemma 19.31 input — score integrability derived from the local envelope -/

/-- The a.e. derivative appearing in vdV Lemma 19.31 belongs to `L²(P)` whenever the
criterion is locally Lipschitz with an `L²(P)` envelope.  No measurability or integrability
certificate for `mdot` is assumed: its coordinates are a.e. limits of measurable directional
difference quotients, and the derivative norm is bounded by the envelope norm.

The conclusion is deliberately `MemLp`, hence carries a.e. strong measurability.  Literal
measurability of the supplied representative cannot be derived from an a.e. derivative
hypothesis, since that representative may be changed arbitrarily on a null set. -/
theorem psiVec_memLp_two_of_ae_hasFDerivAt_lipschitz
    (P : Measure Ω)
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ,
      ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
        |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀) :
    MemLp (psiVec
      (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) 2 P := by
  have hmdot_ae : ∀ i, AEMeasurable (mdot i) P := by
    intro i
    let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
    let q : ℕ → Ω → ℝ := fun n ω =>
      (((n : ℝ) + 1)⁻¹)⁻¹ *
        (m (θ₀ + ((n : ℝ) + 1)⁻¹ • e) ω - m θ₀ ω)
    have hq_meas : ∀ n, Measurable (q n) := by
      intro n
      exact ((hm_meas _).sub (hm_meas θ₀)).const_mul _
    refine aemeasurable_of_tendsto_metrizable_ae'
      (fun n => (hq_meas n).aemeasurable) ?_
    filter_upwards [hderiv] with ω hd
    have hcoord :
        (innerSL ℝ (psiVec
          (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) e = mdot i ω := by
      rw [innerSL_apply_apply]
      simp only [e]
      rw [real_inner_comm]
      simpa [psiVec] using
        (EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ)
          (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω))
    have hγ : HasDerivAt (fun s : ℝ => θ₀ + s • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add θ₀
    have hline : HasDerivAt (fun s : ℝ => m (θ₀ + s • e) ω) (mdot i ω) 0 := by
      have hF : HasFDerivAt (fun θ => m θ ω)
          (innerSL ℝ (psiVec
            (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω))
          (θ₀ + (0 : ℝ) • e) := by
        simpa using hd
      have hcomp := hF.comp_hasDerivAt (0 : ℝ) hγ
      change HasDerivAt (fun s : ℝ => m (θ₀ + s • e) ω)
        ((innerSL ℝ (psiVec
          (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) e) 0 at hcomp
      rwa [hcoord] at hcomp
    have hseq : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨by simpa only [one_div] using
          tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ), ?_⟩
      exact Filter.Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        positivity
    simpa [q, Function.comp_def, smul_eq_mul] using
      hline.tendsto_slope_zero.comp hseq
  have hcoords : AEMeasurable (fun ω i => mdot i ω) P :=
    aemeasurable_pi_iff.mpr hmdot_ae
  have hpsi_ae : AEMeasurable
      (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) P :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable' hcoords
  refine hmenv.norm.mono' hpsi_ae.aestronglyMeasurable ?_
  filter_upwards [hderiv] with ω hd
  have hlipω : LipschitzOnWith (Real.nnabs (menv ω))
      (fun θ => m θ ω) (Metric.closedBall θ₀ ρ) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro θ₁ hθ₁ θ₂ hθ₂
    rw [Real.dist_eq, dist_eq_norm, Real.coe_nnabs]
    calc
      |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖ :=
        hLip θ₁ hθ₁ θ₂ hθ₂ ω
      _ ≤ |menv ω| * ‖θ₁ - θ₂‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have hnorm_le :=
    hd.le_of_lipschitzOn (Metric.closedBall_mem_nhds θ₀ hρ) hlipω
  rw [innerSL_apply_norm] at hnorm_le
  rwa [Real.coe_nnabs, ← Real.norm_eq_abs] at hnorm_le

/-! ### Lemma 19.31 fixed-direction linearization at an arbitrary rate -/

section

open scoped RealInnerProductSpace

omit [MeasurableSpace Ω] in
/-- The fixed-direction linearization residual at a deterministic local rate.

This is the integrand in equation (19.30) of vdV Lemma 19.31.
The definition is total at indices where `r n = 0`; convergence arguments use only the
eventual positive-rate tail supplied by `r → +∞`. -/
noncomputable def linResidAt
    (r : ℕ → ℝ) (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (n : ℕ) : EuclideanSpace ℝ (Fin d) → Ω → ℝ :=
  fun h ω => scaledIncrementAt r m θ₀ n h ω -
      ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫

/-- For every fixed direction, the arbitrary-rate criterion increment converges in
`L²(P)` to its derivative readout.  Positivity of `r n` and containment of the shifted
parameter in the local Lipschitz ball are derived eventually from `r → +∞`; no
all-index guard or measurability certificate for the supplied derivative representative is
required. -/
theorem linearization_distL2_tendstoZero_atRate
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ,
      ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
        |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (h : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => distL2 P (scaledIncrementAt r m θ₀ n h)
      (fun ω => ⟪h, psiVec
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) atTop (𝓝 0) := by
  classical
  have hscore : MemLp
      (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) 2 P :=
    psiVec_memLp_two_of_ae_hasFDerivAt_lipschitz
      P m mdot θ₀ hm_meas menv hmenv ρ hρ hLip hderiv
  let Good : ℕ → Prop := fun n => 0 < r n ∧ ‖h‖ ≤ ρ * r n
  have hr_pos : ∀ᶠ n in atTop, 0 < r n :=
    hr.eventually (eventually_gt_atTop 0)
  have hball : ∀ᶠ n in atTop, ‖h‖ ≤ ρ * r n :=
    (Filter.Tendsto.const_mul_atTop hρ hr).eventually (eventually_ge_atTop ‖h‖)
  have hGood : ∀ᶠ n in atTop, Good n := by
    filter_upwards [hr_pos, hball] with n hn hnh
    exact ⟨hn, hnh⟩
  let f : ℕ → Ω → ℝ := fun n ω =>
    if Good n then linResidAt r m mdot θ₀ n h ω else 0
  let D : Ω → ℝ := fun ω =>
    ‖h‖ * (‖menv ω‖ +
      ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖)
  have hD_memLp : MemLp D 2 P :=
    (hmenv.norm.add hscore.norm).const_mul ‖h‖
  have hD_nonneg : ∀ ω, 0 ≤ D ω := fun ω => by
    dsimp only [D]
    positivity
  have hresid_aesm : ∀ n,
      AEStronglyMeasurable (linResidAt r m mdot θ₀ n h) P := by
    intro n
    unfold linResidAt
    exact (scaledIncrementAt_measurable r m θ₀ n hm_meas h).aestronglyMeasurable.sub
      (aestronglyMeasurable_const.inner hscore.aestronglyMeasurable)
  have hresid_le : ∀ n, Good n → ∀ ω,
      |linResidAt r m mdot θ₀ n h ω| ≤ D ω := by
    intro n hn ω
    have hzero : ‖(0 : EuclideanSpace ℝ (Fin d))‖ ≤ ρ * r n := by
      simpa using (norm_nonneg h).trans hn.2
    have hinc : |scaledIncrementAt r m θ₀ n h ω| ≤ ‖menv ω‖ * ‖h‖ := by
      calc
        |scaledIncrementAt r m θ₀ n h ω| =
            |scaledIncrementAt r m θ₀ n h ω -
              scaledIncrementAt r m θ₀ n 0 ω| := by simp
        _ ≤ menv ω * ‖h - 0‖ :=
          scaledIncrementAt_lipschitz r m θ₀ menv ρ hLip hn.1 h 0 hn.2 hzero ω
        _ ≤ ‖menv ω‖ * ‖h‖ := by
          rw [sub_zero]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg h)
    have hinner :
        |(⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ)| ≤
          ‖h‖ * ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖ :=
      abs_real_inner_le_norm _ _
    unfold linResidAt
    calc
      |scaledIncrementAt r m θ₀ n h ω -
          ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫|
          ≤ |scaledIncrementAt r m θ₀ n h ω| +
              |(⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ)| :=
            abs_sub _ _
      _ ≤ ‖menv ω‖ * ‖h‖ + ‖h‖ *
          ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖ :=
        add_le_add hinc hinner
      _ = D ω := by dsimp only [D]; ring
  have hf_aesm : ∀ n, AEStronglyMeasurable (f n) P := by
    intro n
    by_cases hn : Good n
    · simpa only [f, if_pos hn] using hresid_aesm n
    · simp only [f, if_neg hn]
      exact aestronglyMeasurable_const
  have hf_le_D : ∀ n ω, ‖f n ω‖ ≤ D ω := by
    intro n ω
    by_cases hn : Good n
    · simp only [f, if_pos hn, Real.norm_eq_abs]
      exact hresid_le n hn ω
    · simp only [f, if_neg hn, norm_zero]
      exact hD_nonneg ω
  have hf_tendsto_ae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
    filter_upwards [hderiv] with ω hω
    have hγ : HasDerivAt (fun s : ℝ => θ₀ + s • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add θ₀
    have hline : HasDerivAt (fun s : ℝ => m (θ₀ + s • h) ω)
        (⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ) 0 := by
      have hF : HasFDerivAt (fun θ => m θ ω)
          (innerSL ℝ (psiVec
            (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω))
          (θ₀ + (0 : ℝ) • h) := by
        simpa using hω
      have hcomp := hF.comp_hasDerivAt (0 : ℝ) hγ
      change HasDerivAt (fun s : ℝ => m (θ₀ + s • h) ω)
        ((innerSL ℝ (psiVec
          (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) h) 0 at hcomp
      rw [innerSL_apply_apply, real_inner_comm] at hcomp
      exact hcomp
    have hseq : Tendsto (fun n => (r n)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_inv_atTop_zero.comp hr, ?_⟩
      filter_upwards [hr_pos] with n hn
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]
      exact hn.ne'
    have hslope := (hline.tendsto_slope_zero.comp hseq).sub_const
      (⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ)
    have hresid : Tendsto (fun n => linResidAt r m mdot θ₀ n h ω) atTop (𝓝 0) := by
      simpa [linResidAt, scaledIncrementAt, Function.comp_def, smul_eq_mul] using hslope
    refine hresid.congr' ?_
    filter_upwards [hGood] with n hn
    simp only [f, if_pos hn]
  have hUI : UnifIntegrable f 2 P := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ :=
      hD_memLp.eLpNorm_indicator_le one_le_two (by norm_num) hε
    refine ⟨δ, hδpos, fun n s hs hμs => le_trans ?_ (hδ s hs hμs)⟩
    refine eLpNorm_mono_real (fun ω => ?_)
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω]
      exact hf_le_D n ω
    · simp only [Set.indicator_of_notMem hω, norm_zero, le_refl]
  have hLp : Tendsto (fun n => eLpNorm (f n) 2 P) atTop (𝓝 0) := by
    have h := tendsto_Lp_finite_of_tendsto_ae (p := 2) one_le_two (by norm_num)
      hf_aesm MemLp.zero hUI hf_tendsto_ae
    simpa using h
  have hLp_real : Tendsto (fun n => (eLpNorm (f n) 2 P).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞)).comp hLp
    simpa using! h
  refine hLp_real.congr' ?_
  filter_upwards [hGood] with n hn
  rw [distL2]
  apply congrArg ENNReal.toReal
  apply congrArg (fun g : Ω → ℝ => eLpNorm g 2 P)
  funext ω
  simp only [f, if_pos hn, linResidAt, Pi.sub_apply]

/-- For every fixed direction, the empirical process of the arbitrary-rate linearization
residual converges to zero in probability.  The local rate guards and residual `L²`
membership are derived only on an eventual tail from `r → +∞`. -/
theorem linearization_marginal_tendstoInProbZero_atRate
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ,
      ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
        |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (h : EuclideanSpace ℝ (Fin d)) :
    TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (linResidAt r m mdot θ₀ n h)) := by
  intro ε hε
  have hscore : MemLp
      (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) 2 P :=
    psiVec_memLp_two_of_ae_hasFDerivAt_lipschitz
      P m mdot θ₀ hm_meas menv hmenv ρ hρ hLip hderiv
  have hdist : Tendsto (fun n => distL2 P (scaledIncrementAt r m θ₀ n h)
      (fun ω => ⟪h, psiVec
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) atTop (𝓝 0) :=
    linearization_distL2_tendstoZero_atRate
      P m mdot θ₀ hm_meas menv hmenv ρ hρ hLip hderiv r hr h
  have hr_pos : ∀ᶠ n in atTop, 0 < r n :=
    hr.eventually (eventually_gt_atTop 0)
  have hball : ∀ᶠ n in atTop, ‖h‖ ≤ ρ * r n :=
    (Filter.Tendsto.const_mul_atTop hρ hr).eventually (eventually_ge_atTop ‖h‖)
  have hf_L2 : ∀ᶠ n in atTop, MemLp (linResidAt r m mdot θ₀ n h) 2 P := by
    filter_upwards [hr_pos, hball] with n hrn hhn
    have hdom : MemLp (fun ω => ‖h‖ *
        (‖menv ω‖ +
          ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖)) 2 P :=
      (hmenv.norm.add hscore.norm).const_mul ‖h‖
    refine MemLp.mono' hdom ?_ ?_
    · unfold linResidAt
      exact (scaledIncrementAt_measurable r m θ₀ n hm_meas h).aestronglyMeasurable.sub
        (aestronglyMeasurable_const.inner hscore.aestronglyMeasurable)
    · filter_upwards with ω
      have hzero : ‖(0 : EuclideanSpace ℝ (Fin d))‖ ≤ ρ * r n := by
        simpa using (norm_nonneg h).trans hhn
      have hinc : |scaledIncrementAt r m θ₀ n h ω| ≤ ‖menv ω‖ * ‖h‖ := by
        calc
          |scaledIncrementAt r m θ₀ n h ω| =
              |scaledIncrementAt r m θ₀ n h ω -
                scaledIncrementAt r m θ₀ n 0 ω| := by simp
          _ ≤ menv ω * ‖h - 0‖ :=
            scaledIncrementAt_lipschitz r m θ₀ menv ρ hLip
              hrn h 0 hhn hzero ω
          _ ≤ ‖menv ω‖ * ‖h‖ := by
            rw [sub_zero]
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg h)
      have hinner :
          |(⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ)| ≤
            ‖h‖ * ‖psiVec
              (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖ :=
        abs_real_inner_le_norm _ _
      rw [Real.norm_eq_abs]
      unfold linResidAt
      calc
        |scaledIncrementAt r m θ₀ n h ω -
            ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫|
            ≤ |scaledIncrementAt r m θ₀ n h ω| +
                |(⟪h, psiVec
                  (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ)| :=
              abs_sub _ _
        _ ≤ ‖menv ω‖ * ‖h‖ + ‖h‖ *
            ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖ :=
          add_le_add hinc hinner
        _ = ‖h‖ * (‖menv ω‖ +
            ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖) := by ring
  have hint_le : ∀ n : ℕ, (∫ x, (linResidAt r m mdot θ₀ n h x) ^ 2 ∂P) ≤
      (distL2 P (scaledIncrementAt r m θ₀ n h)
        (fun ω => ⟪h, psiVec
          (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2 := by
    intro n
    set I : ℝ := ∫ x, (linResidAt r m mdot θ₀ n h x) ^ 2 ∂P with hI
    have hI_nonneg : 0 ≤ I := by
      rw [hI]
      exact integral_nonneg fun _ => sq_nonneg _
    have hle : Real.sqrt I ≤ distL2 P (scaledIncrementAt r m θ₀ n h)
        (fun ω => ⟪h, psiVec
          (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) := by
      apply le_distL2_of_integral_sq_ge
      rw [Real.sq_sqrt hI_nonneg, hI]
      rfl
    calc
      I = Real.sqrt I ^ 2 := (Real.sq_sqrt hI_nonneg).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  set gseq : ℕ → ℝ := fun n =>
    (distL2 P (scaledIncrementAt r m θ₀ n h)
      (fun ω => ⟪h, psiVec
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2 / ε ^ 2 with hgseq
  have hgseq_tendsto : Tendsto gseq atTop (𝓝 0) := by
    rw [hgseq]
    simpa using (hdist.pow 2).div_const (ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgseq_tendsto
    (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_
  filter_upwards [hf_L2] with n hn
  have htail := empiricalProcess_chebyshev_tail P μ X hX_meas hX_indep hX_id hX_law n
    (linResidAt r m mdot θ₀ n h) hn hε
  have hInn : 0 ≤ (∫ x, (linResidAt r m mdot θ₀ n h x) ^ 2 ∂P) / ε ^ 2 :=
    div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by positivity)
  simp only [Real.norm_eq_abs]
  rw [hgseq]
  calc
    (μ {ξ | ε ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (linResidAt r m mdot θ₀ n h)|}).toReal
        ≤ (ENNReal.ofReal ((∫ x, (linResidAt r m mdot θ₀ n h x) ^ 2 ∂P) /
          ε ^ 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
    _ = (∫ x, (linResidAt r m mdot θ₀ n h x) ^ 2 ∂P) / ε ^ 2 :=
      ENNReal.toReal_ofReal hInn
    _ ≤ (distL2 P (scaledIncrementAt r m θ₀ n h)
        (fun ω => ⟪h, psiVec
          (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2 / ε ^ 2 := by
      gcongr
      exact hint_le n

end

end AsymptoticStatistics.EmpiricalProcess
