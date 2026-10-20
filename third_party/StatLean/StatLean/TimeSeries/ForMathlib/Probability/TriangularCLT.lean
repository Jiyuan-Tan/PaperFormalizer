module
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The Lindeberg CLT for triangular (double) arrays

Row-wise independent triangular array `X_{n,1}, …, X_{n,k_n}` with zero means: if the
row variances converge (`Σᵢ Var X_{n,i} → σ²`) and the **Lindeberg condition** holds
(`∀ ε > 0, Σᵢ E[X_{n,i}² 1_{|X_{n,i}| ≥ ε}] → 0`), then the row sums are asymptotically
`N(0, σ²)` — stated through pointwise characteristic-function convergence
(Lévy-equivalent to convergence in distribution).

This is the "double-array" CLT that FY cites (Serfling 1980, p. 31) in the proof of
Theorem 2.14(i), and the assembly engine of the Bernstein-block CLTs (FY Theorems
2.21(ii) and 2.22). Mathlib (pin `5e932f97`) has the iid CLT
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) but no triangular-array
Lindeberg CLT, so we build it: the classical characteristic-function proof —
independence factorizes the row charFun into a product; second-order Taylor control of
each factor (`|E e^{iuX} − (1 − u²·Var X/2)| ≤ E min(|uX|³, 2(uX)²)`, split at `ε` by
Lindeberg); logarithm/product comparison against `e^{−u²σ²/2}`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003 — used for
Thm 2.14(i) (§2.7.6, citing R. J. Serfling, *Approximation Theorems of Mathematical
Statistics*, Wiley 1980, §1.9.3) and inside §2.7.7. (`FY §2.7.6`.)

**Bibliographic comments.** The Lindeberg condition and proof scheme are J. W. Lindeberg
(1922); the triangular-array formulation is standard from Loève and Billingsley
(*Probability and Measure*, Thm 27.2). The characteristic-function route implemented
here follows Billingsley's proof, replacing weak-convergence bookkeeping by pointwise
charFun convergence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open Complex in
/-- **Uniform third-order remainder bound for `e^{iy}`.** The pointwise estimate driving
Lindeberg's swapping argument:
`‖exp (I y) − (1 + I y − y²/2)‖ ≤ min (|y|³/6) (y²)`.
Both halves are elementary: the cubic one by integrating the exponential's remainder three
times, the quadratic one from `‖exp (I y) − 1 − I y‖ ≤ y²/2` and the triangle inequality.
Mathlib only provides the non-uniform `taylor_charFun_two`, so this is proved from
scratch. -/
private lemma norm_cexp_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ min (|y| ^ 3 / 6) (y ^ 2) := by
  -- Derivative of `u ↦ exp (I u)` (as a function of a real variable).
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  have hnorme : ∀ u : ℝ, ‖Complex.exp (I * ↑u)‖ = 1 := by
    intro u; rw [Complex.norm_exp]; simp
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  have hcontI : Continuous (fun u : ℝ => Complex.exp (I * ↑u) * I) := by fun_prop
  have hcont1 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1) * I) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u) * I) := by fun_prop
  -- Level 0: `‖exp (I z) − 1‖ ≤ z` for `z ≥ 0`.
  have hL0 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1‖ ≤ z := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I) = Complex.exp (I * ↑z) - 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u)
        (hcontI.intervalIntegrable 0 z)]
      simp
    rw [← hInt]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (C := 1) (f := fun u => Complex.exp (I * ↑u) * I)
      (fun u _ => by rw [norm_mul, Complex.norm_I, mul_one]; exact le_of_eq (hnorme u))
    calc ‖∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I‖ ≤ 1 * |z - 0| := hbnd
      _ = z := by rw [sub_zero, abs_of_nonneg hz, one_mul]
  have hd1 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w)
      ((Complex.exp (I * ↑u) - 1) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1) * I = Complex.exp (I * ↑u) * I - 0 - I := by ring
    rw [heq]
    exact ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
  -- Level 1: `‖exp (I z) − 1 − I z‖ ≤ z²/2` for `z ≥ 0`.
  have hL1 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ z ^ 2 / 2 := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1) * I)
        = Complex.exp (I * ↑z) - 1 - I * ↑z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd1 u)
        (hcont1.intervalIntegrable 0 z)]
      simp
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ ∫ u in (0:ℝ)..z, u := by
      rw [← hInt]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        (continuous_id.intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL0 u hu.1.le
    rw [integral_id] at hb
    simpa using hb
  have hsq : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w * ↑w / 2 : ℂ)) (↑u : ℂ) u := by
    intro u
    have hof : HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
      simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
    have heq : (↑u : ℂ) = (1 * ↑u + ↑u * 1) / 2 := by ring
    rw [heq]
    exact (hof.mul hof).div_const 2
  have hd2 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + ↑w * ↑w / 2)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1 - I * ↑u) * I
        = (Complex.exp (I * ↑u) - 1) * I + ↑u := by
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(↑u : ℂ)) * hI2
    rw [heq]
    exact (hd1 u).add (hsq u)
  have hA2z : ∀ z : ℝ, (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd2 u)
      (hcont2.intervalIntegrable 0 z)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  -- The `y ≥ 0` case of the goal.
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖ ≤ min (z ^ 3 / 6) (z ^ 2) := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖
        ≤ ∫ u in (0:ℝ)..z, u ^ 2 / 2 := by
      rw [← hA2z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL1 u hu.1.le
    have hintval : (∫ u in (0:ℝ)..z, u ^ 2 / 2) = z ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    refine le_min (hb.trans (le_of_eq hintval)) ?_
    have h1 := hL1 z hz
    have hcast : (↑z * ↑z / 2 : ℂ) = ((z * z / 2 : ℝ) : ℂ) := by push_cast; ring
    have hz2 : ‖(↑z * ↑z / 2 : ℂ)‖ = z ^ 2 / 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hsplit : Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2
        = (Complex.exp (I * ↑z) - 1 - I * ↑z) + ↑z * ↑z / 2 := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hz2]; linarith
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2 := by ring
  rw [hEq]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · -- Reflect to `−y ≥ 0` via conjugation.
    have hz : (0:ℝ) ≤ -y := by linarith
    have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have hconj : (starRingEnd ℂ) (Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2)
        = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2 := by
      simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hexp, Complex.ofReal_neg]
      ring
    have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2‖
        = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2‖ := by
      rw [← hconj, Complex.norm_conj]
    rw [hnn, abs_of_neg hy, show (y : ℝ) ^ 2 = (-y) ^ 2 from by ring]
    exact key (-y) hz

/-- Telescoping product bound: for factors of modulus `≤ 1`, the difference of the products
is bounded by the sum of the differences. -/
private lemma norm_prod_sub_prod_le {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] (s : Finset ι)
    (f g : ι → 𝕜) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have key : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hpg : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun i _ => norm_nonneg _) hg'
    have h1 : ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ :=
      calc ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖
            ≤ 1 * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
              mul_le_mul_of_nonneg_right hfa (norm_nonneg _)
        _ = ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := one_mul _
        _ ≤ ∑ i ∈ s, ‖f i - g i‖ := ih hf' hg'
    have h2 : ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ ≤ ‖f a - g a‖ :=
      calc ‖f a - g a‖ * ‖∏ i ∈ s, g i‖
            ≤ ‖f a - g a‖ * 1 := mul_le_mul_of_nonneg_left hpg (norm_nonneg _)
        _ = ‖f a - g a‖ := mul_one _
    linarith

/-- Real quadratic remainder for `exp (−u)` on `|u| ≤ 1`. -/
private lemma abs_exp_neg_sub_one_sub_le {u : ℝ} (hu : |u| ≤ 1) :
    |Real.exp (-u) - (1 - u)| ≤ (3 / 4) * u ^ 2 := by
  have h := Real.exp_bound (x := -u) (by rwa [abs_neg]) (n := 2) (by norm_num)
  have hs : ∑ m ∈ Finset.range 2, (-u) ^ m / (m.factorial : ℝ) = 1 - u := by
    simp [Finset.sum_range_succ]; ring
  rw [hs, abs_neg, sq_abs] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]
  ring

/-- Diagonal `Tendsto`-to-zero criterion: eventually nonnegative and eventually below every
positive level. -/
private lemma tendsto_zero_of_eventually_le {F : ℕ → ℝ}
    (hF : ∀ᶠ n in atTop, 0 ≤ F n) (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, F n ≤ δ) :
    Tendsto F atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hF] with n hn using lt_of_lt_of_le hb hn
  · filter_upwards [h (b / 2) (by linarith)] with n hn using lt_of_le_of_lt hn (by linarith)

open Complex in
/-- **The analytic core of the Lindeberg CLT.** Under the Lindeberg hypotheses (stated with
the *open* truncation sets `{ε < |X|}`, the weaker form at each fixed `ε`) the product of
the row characteristic functions converges pointwise to `t ↦ exp(−σ² t²/2)`.

Lindeberg's swapping/telescoping estimate on top of `norm_cexp_sub_taylor_le`: telescope
the two products, bound each factor's difference by `E[min(|t Xₙᵢ|³/6, t² Xₙᵢ²)]`, split at
the level `ε` (the large part is the Lindeberg sum), and match
`∏ᵢ (1 − t²σₙᵢ²/2) → exp(−t²σ²/2)`. -/
private lemma tendsto_prod_charFun_lindeberg [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    (hmeas : ∀ n i, Measurable (X n i))
    (hL2 : ∀ n i, MemLp (X n i) 2 μ)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    {σ2 : ℝ} (hσ0 : 0 ≤ σ2)
    (hvar : Tendsto (fun n => ∑ i, variance (X n i) μ) atTop (𝓝 σ2))
    (hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => ∏ i, charFun (μ.map (X n i)) t) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) t)) := by
  -- The Gaussian characteristic function as a genuine real exponential.
  have hσc : ((Real.toNNReal σ2 : NNReal) : ℝ) = σ2 := Real.coe_toNNReal σ2 hσ0
  have hc : charFun (gaussianReal 0 (Real.toNNReal σ2)) t
      = ((Real.exp (-(t ^ 2 * σ2 / 2)) : ℝ) : ℂ) := by
    rw [charFun_gaussianReal, Complex.ofReal_exp]
    congr 1
    have hcast : ((Real.toNNReal σ2 : NNReal) : ℂ) = ((σ2 : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hσc
    rw [hcast]
    push_cast
    ring
  -- The `t = 0` case is `∏ 1 → 1`; handle it first, then assume `t ≠ 0`.
  rcases eq_or_ne t 0 with rfl | ht
  · have hone : ∀ n i, charFun (μ.map (X n i)) 0 = 1 := by
      intro n i
      haveI : IsProbabilityMeasure (μ.map (X n i)) :=
        Measure.isProbabilityMeasure_map (hmeas n i).aemeasurable
      rw [charFun_zero, probReal_univ, Complex.ofReal_one]
    have hR : charFun (gaussianReal 0 (Real.toNNReal σ2)) 0 = 1 := by
      rw [charFun_zero, probReal_univ, Complex.ofReal_one]
    simp only [hone, Finset.prod_const_one, hR]
    exact tendsto_const_nhds
  -- Basic facts about the row entries.
  have hvnn : ∀ n i, (0:ℝ) ≤ variance (X n i) μ := fun n i => variance_nonneg _ _
  have hunn : ∀ n i, (0:ℝ) ≤ t ^ 2 * variance (X n i) μ / 2 :=
    fun n i => div_nonneg (mul_nonneg (sq_nonneg t) (hvnn n i)) (by norm_num)
  have hI2 : ∀ n i, Integrable (fun ω => (X n i ω) ^ 2) μ := fun n i => (hL2 n i).integrable_sq
  have hI1 : ∀ n i, Integrable (X n i) μ := fun n i => (hL2 n i).integrable one_le_two
  have hVeq : ∀ n i, variance (X n i) μ = ∫ ω, (X n i ω) ^ 2 ∂μ :=
    fun n i => variance_of_integral_eq_zero (hmeas n i).aemeasurable (hmean n i)
  have hset : ∀ ε n i, MeasurableSet {ω | ε < |X n i ω|} := fun ε n i =>
    measurableSet_lt measurable_const (hmeas n i).abs
  have hLnn : ∀ ε n i, 0 ≤ ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ :=
    fun ε n i => setIntegral_nonneg (hset ε n i) fun ω _ => sq_nonneg _
  -- CENTRAL per-term estimate (crux of the swapping argument).
  have hterm : ∀ ε : ℝ, 0 < ε → ∀ n i,
      ‖charFun (μ.map (X n i)) t - ((1 - t ^ 2 * variance (X n i) μ / 2 : ℝ) : ℂ)‖
        ≤ |t| ^ 3 * ε / 6 * variance (X n i) μ
          + t ^ 2 * ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ := by
    intro ε hε n i
    have hsm := hset ε n i
    have hIsecond : Integrable (fun ω => Complex.I * (↑(t * X n i ω) : ℂ)) μ :=
      (((hI1 n i).const_mul t).ofReal).const_mul Complex.I
    have hIrp : Integrable (fun ω => ((1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) : ℂ)) μ :=
      ((integrable_const (1 : ℝ)).sub (((hI2 n i).const_mul (t ^ 2)).div_const 2)).ofReal
    have hItX2 : Integrable (fun ω => (t * X n i ω) ^ 2) μ := by
      simpa [mul_pow] using (hI2 n i).const_mul (t ^ 2)
    have hIthird : Integrable (fun ω => ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) μ := by
      have he : (fun ω => ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)
          = fun ω => (↑((t * X n i ω) ^ 2) : ℂ) / 2 := by ext ω; rw [← Complex.ofReal_pow]
      rw [he]; exact (hItX2.ofReal).div_const (2 : ℂ)
    have hFmeas : Measurable (fun ω => Complex.exp (Complex.I * ↑(t * X n i ω))) :=
      Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.comp ((hmeas n i).const_mul t)).const_mul Complex.I)
    have hIF : Integrable (fun ω => Complex.exp (Complex.I * ↑(t * X n i ω))) μ :=
      (integrable_const (1 : ℝ)).mono' hFmeas.aestronglyMeasurable
        (ae_of_all _ fun ω => le_of_eq (by rw [Complex.norm_exp]; simp))
    have hIG : Integrable (fun ω => 1 + Complex.I * ↑(t * X n i ω)
        - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) μ :=
      ((integrable_const (1 : ℂ)).add hIsecond).sub hIthird
    have hFcf : charFun (μ.map (X n i)) t
        = ∫ ω, Complex.exp (Complex.I * ↑(t * X n i ω)) ∂μ := by
      rw [charFun_apply_real, integral_map (hmeas n i).aemeasurable
        (Continuous.aestronglyMeasurable (by fun_prop))]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      push_cast; ring_nf
    have hRp : ∫ ω, (1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) ∂μ
        = 1 - t ^ 2 * variance (X n i) μ / 2 := by
      rw [integral_sub (integrable_const 1) (((hI2 n i).const_mul (t ^ 2)).div_const 2),
        integral_const, probReal_univ, smul_eq_mul, mul_one, integral_div]
      simp only [integral_const_mul]
      rw [← hVeq n i]
    have hTX : ∫ ω, t * X n i ω ∂μ = 0 := by
      rw [integral_const_mul t (X n i), hmean n i, mul_zero]
    have hImC : ∫ ω, Complex.I * ((t * X n i ω : ℝ) : ℂ) ∂μ = 0 := by
      have key : ∫ ω, Complex.I * ((t * X n i ω : ℝ) : ℂ) ∂μ
          = Complex.I * ∫ ω, ((t * X n i ω : ℝ) : ℂ) ∂μ := integral_const_mul _ _
      rw [key, integral_complex_ofReal, hTX, Complex.ofReal_zero, mul_zero]
    have hGint : ∫ ω, (1 + Complex.I * ↑(t * X n i ω)
        - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) ∂μ
          = ((1 - t ^ 2 * variance (X n i) μ / 2 : ℝ) : ℂ) := by
      have hEq : (fun ω => 1 + Complex.I * (↑(t * X n i ω) : ℂ) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)
          = fun ω => ((1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) : ℂ)
              + Complex.I * ((t * X n i ω : ℝ) : ℂ) := by
        ext ω; push_cast; ring
      rw [hEq, integral_add hIrp hIsecond, integral_complex_ofReal, hRp, hImC, add_zero]
    have hab : charFun (μ.map (X n i)) t - ((1 - t ^ 2 * variance (X n i) μ / 2 : ℝ) : ℂ)
        = ∫ ω, (Complex.exp (Complex.I * ↑(t * X n i ω))
            - (1 + Complex.I * ↑(t * X n i ω) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)) ∂μ := by
      rw [integral_sub hIF hIG, ← hFcf, hGint]
    set g : Ω → ℝ := fun ω => |t| ^ 3 * ε / 6 * (X n i ω) ^ 2
        + t ^ 2 * Set.indicator {ω | ε < |X n i ω|} (fun ω => (X n i ω) ^ 2) ω with hgdef
    have hbound : ∀ ω, ‖Complex.exp (Complex.I * ↑(t * X n i ω))
        - (1 + Complex.I * ↑(t * X n i ω) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)‖ ≤ g ω := by
      intro ω
      refine (norm_cexp_sub_taylor_le (t * X n i ω)).trans ?_
      have hnn0 : (0:ℝ) ≤ |t| ^ 3 * ε / 6 * (X n i ω) ^ 2 :=
        mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) 3) hε.le) (by norm_num))
          (sq_nonneg _)
      by_cases hω : ε < |X n i ω|
      · have hωm : ω ∈ {ω | ε < |X n i ω|} := hω
        simp only [hgdef, Set.indicator_of_mem hωm]
        refine (min_le_right _ _).trans ?_
        have h2 : (t * X n i ω) ^ 2 = t ^ 2 * (X n i ω) ^ 2 := by ring
        rw [h2]; linarith [hnn0]
      · have hωm : ω ∉ {ω | ε < |X n i ω|} := hω
        simp only [hgdef, Set.indicator_of_notMem hωm, mul_zero, add_zero]
        refine (min_le_left _ _).trans ?_
        have habs : |t * X n i ω| ^ 3 = |t| ^ 3 * |X n i ω| ^ 3 := by rw [abs_mul, mul_pow]
        have hcube : |X n i ω| ^ 3 ≤ ε * (X n i ω) ^ 2 := by
          have he : |X n i ω| ^ 3 = |X n i ω| * (X n i ω) ^ 2 := by rw [← sq_abs]; ring
          rw [he]; exact mul_le_mul_of_nonneg_right (not_lt.1 hω) (sq_nonneg _)
        rw [habs]; nlinarith [hcube, pow_nonneg (abs_nonneg t) 3]
    have hbint : Integrable g μ := by
      rw [hgdef]
      exact ((hI2 n i).const_mul _).add (((hI2 n i).indicator hsm).const_mul _)
    have hg_int : ∫ ω, g ω ∂μ
        = |t| ^ 3 * ε / 6 * variance (X n i) μ
          + t ^ 2 * ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ := by
      rw [hgdef, integral_add ((hI2 n i).const_mul _) (((hI2 n i).indicator hsm).const_mul _)]
      simp only [integral_const_mul, integral_indicator hsm]
      rw [← hVeq n i]
    rw [hab]
    exact (norm_integral_le_of_norm_le hbint (ae_of_all _ hbound)).trans (le_of_eq hg_int)
  -- Uniform asymptotic negligibility of the row variances.
  have hsmall : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ∀ i, variance (X n i) μ ≤ c := by
    intro c hc'
    have hεpos : (0:ℝ) < Real.sqrt (c / 2) := Real.sqrt_pos.2 (by linarith)
    have hε2 : Real.sqrt (c / 2) ^ 2 = c / 2 := Real.sq_sqrt (by linarith)
    set ε := Real.sqrt (c / 2) with hεdef
    have hSlt : ∀ᶠ n in atTop,
        ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ ≤ c / 2 :=
      (hlin ε hεpos).eventually_le_const (show (0:ℝ) < c / 2 by linarith)
    filter_upwards [hSlt] with n hn i
    have hsm := hset ε n i
    have hdecomp : variance (X n i) μ
        = ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ
          + ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂μ := by
      rw [hVeq n i]; exact (integral_add_compl hsm (hI2 n i)).symm
    have hpart1 : ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ ≤ c / 2 :=
      le_trans (Finset.single_le_sum (fun j _ => hLnn ε n j) (Finset.mem_univ i)) hn
    have hpart2 : ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂μ ≤ c / 2 := by
      rw [← hε2]
      calc ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂μ
          ≤ ∫ ω in {ω | ε < |X n i ω|}ᶜ, ε ^ 2 ∂μ := by
            refine setIntegral_mono_on ((hI2 n i).integrableOn) integrableOn_const hsm.compl
              (fun ω hω => ?_)
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
            rw [← sq_abs (X n i ω)]
            exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        _ ≤ ∫ _ω, ε ^ 2 ∂μ :=
            setIntegral_le_integral (integrable_const _) (ae_of_all _ fun _ => by positivity)
        _ = ε ^ 2 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hdecomp]; linarith
  have ht2 : (0:ℝ) < t ^ 2 := by positivity
  -- Eventually every row term satisfies `uᵢ = t²σᵢ²/2 ≤ 1`.
  have hev1 : ∀ᶠ n in atTop, ∀ i, t ^ 2 * variance (X n i) μ / 2 ≤ 1 := by
    filter_upwards [hsmall (2 / t ^ 2) (by positivity)] with n hn i
    have hb := (le_div_iff₀ ht2).1 (hn i)
    have hcomm : t ^ 2 * variance (X n i) μ = variance (X n i) μ * t ^ 2 := mul_comm _ _
    linarith
  -- Abbreviations for the two products (`A` characteristic, `B` its quadratic surrogate).
  set A : ℕ → ℂ := fun n => ∏ i, charFun (μ.map (X n i)) t with hA
  set B : ℕ → ℂ := fun n => ∏ i, ((1 - t ^ 2 * variance (X n i) μ / 2 : ℝ) : ℂ) with hB
  -- `∑ᵢ uᵢ → t²σ²/2`.
  have hsum : Tendsto (fun n => ∑ i, t ^ 2 * variance (X n i) μ / 2) atTop
      (𝓝 (t ^ 2 * σ2 / 2)) := by
    have h := hvar.const_mul (t ^ 2 / 2)
    have he : ∀ n, ∑ i, t ^ 2 * variance (X n i) μ / 2
        = t ^ 2 / 2 * ∑ i, variance (X n i) μ := by
      intro n; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    have hgoal : t ^ 2 / 2 * σ2 = t ^ 2 * σ2 / 2 := by ring
    simpa [he, hgoal] using h
  have hSnn : (0:ℝ) ≤ t ^ 2 * σ2 / 2 :=
    div_nonneg (mul_nonneg (sq_nonneg t) hσ0) (by norm_num)
  ------------------------------------------------------------------
  -- Claim G : `∑ᵢ uᵢ² → 0`.
  ------------------------------------------------------------------
  have hGsq : Tendsto (fun n => ∑ i, (t ^ 2 * variance (X n i) μ / 2) ^ 2) atTop (𝓝 0) := by
    refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => sq_nonneg _) (fun δ hδ => ?_)
    have hden : (0:ℝ) < t ^ 2 * σ2 / 2 + 2 := by linarith
    set M : ℝ := δ / (t ^ 2 * σ2 / 2 + 2) with hMdef
    have hMpos : 0 < M := by rw [hMdef]; exact div_pos hδ hden
    have hsmallM := hsmall (2 * M / t ^ 2) (div_pos (mul_pos (by norm_num) hMpos) ht2)
    have hsumlt : ∀ᶠ n in atTop, ∑ i, t ^ 2 * variance (X n i) μ / 2 < t ^ 2 * σ2 / 2 + 1 :=
      hsum.eventually_lt_const (by linarith)
    filter_upwards [hsmallM, hsumlt] with n hnM hnsum
    have huM : ∀ i, t ^ 2 * variance (X n i) μ / 2 ≤ M := by
      intro i
      have hb := (le_div_iff₀ ht2).1 (hnM i)
      have hcomm : t ^ 2 * variance (X n i) μ = variance (X n i) μ * t ^ 2 := mul_comm _ _
      linarith
    calc ∑ i, (t ^ 2 * variance (X n i) μ / 2) ^ 2
        ≤ ∑ i, M * (t ^ 2 * variance (X n i) μ / 2) := by
          apply Finset.sum_le_sum; intro i _
          rw [sq]; exact mul_le_mul_of_nonneg_right (huM i) (hunn n i)
      _ = M * ∑ i, t ^ 2 * variance (X n i) μ / 2 := by rw [Finset.mul_sum]
      _ ≤ M * (t ^ 2 * σ2 / 2 + 1) := by
          apply mul_le_mul_of_nonneg_left hnsum.le hMpos.le
      _ ≤ δ := by
          rw [hMdef, div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith [hδ.le]
  ------------------------------------------------------------------
  -- T2 : `B n → charFun gaussian`.
  ------------------------------------------------------------------
  have T2 : Tendsto B atTop (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) t)) := by
    rw [hc, hB]
    have hBreal : (fun n => ∏ i, ((1 - t ^ 2 * variance (X n i) μ / 2 : ℝ) : ℂ))
        = fun n => ((∏ i, (1 - t ^ 2 * variance (X n i) μ / 2) : ℝ) : ℂ) := by
      ext n; rw [Complex.ofReal_prod]
    rw [hBreal]
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    have hprodexp : ∀ n, ∏ i, Real.exp (-(t ^ 2 * variance (X n i) μ / 2))
        = Real.exp (-(∑ i, t ^ 2 * variance (X n i) μ / 2)) := by
      intro n; rw [← Real.exp_sum]; rw [← Finset.sum_neg_distrib]
    have hEprod : Tendsto (fun n => ∏ i, Real.exp (-(t ^ 2 * variance (X n i) μ / 2))) atTop
        (𝓝 (Real.exp (-(t ^ 2 * σ2 / 2)))) := by
      simp_rw [hprodexp]
      exact (Real.continuous_exp.tendsto _).comp hsum.neg
    have hdiff : Tendsto (fun n => (∏ i, (1 - t ^ 2 * variance (X n i) μ / 2))
        - ∏ i, Real.exp (-(t ^ 2 * variance (X n i) μ / 2))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n => norm_nonneg _)
        (fun δ hδ => ?_)
      have hsqlt : ∀ᶠ n in atTop, (3 / 4) * ∑ i, (t ^ 2 * variance (X n i) μ / 2) ^ 2 < δ := by
        have hlim : Tendsto (fun n => (3 / 4) * ∑ i, (t ^ 2 * variance (X n i) μ / 2) ^ 2) atTop
            (𝓝 0) := by simpa using hGsq.const_mul (3 / 4)
        exact hlim.eventually_lt_const (by linarith)
      filter_upwards [hev1, hsqlt] with n hn1 hn2
      have htel := norm_prod_sub_prod_le (𝕜 := ℝ) Finset.univ
        (fun i => 1 - t ^ 2 * variance (X n i) μ / 2)
        (fun i => Real.exp (-(t ^ 2 * variance (X n i) μ / 2)))
        (fun i _ => by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [hn1 i, hunn n i], by linarith [hunn n i]⟩)
        (fun i _ => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact (Real.exp_le_one_iff).2 (by linarith [hunn n i]))
      refine htel.trans (le_of_lt (lt_of_le_of_lt ?_ hn2))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h2 := abs_exp_neg_sub_one_sub_le (u := t ^ 2 * variance (X n i) μ / 2)
        (by rw [abs_le]; exact ⟨by linarith [hunn n i], hn1 i⟩)
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact h2
    have hRealP1 : Tendsto (fun n => ∏ i, (1 - t ^ 2 * variance (X n i) μ / 2)) atTop
        (𝓝 (Real.exp (-(t ^ 2 * σ2 / 2)))) := by
      have := hdiff.add hEprod
      simpa using this
    exact hRealP1
  ------------------------------------------------------------------
  -- T1 : `A n - B n → 0`.
  ------------------------------------------------------------------
  have T1 : Tendsto (fun n => A n - B n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n => norm_nonneg _)
      (fun δ hδ => ?_)
    have hKnn : (0:ℝ) ≤ |t| ^ 3 * (σ2 + 1) :=
      mul_nonneg (pow_nonneg (abs_nonneg t) 3) (by linarith)
    have hKd : (0:ℝ) < |t| ^ 3 * (σ2 + 1) + 1 := by linarith
    set ε : ℝ := δ / (|t| ^ 3 * (σ2 + 1) + 1) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hδ hKd
    have hVarlt : ∀ᶠ n in atTop, ∑ i, variance (X n i) μ ≤ σ2 + 1 :=
      (hvar.eventually_lt_const (lt_add_one σ2)).mono fun n h => h.le
    have hLinlt : ∀ᶠ n in atTop,
        t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ < δ / 3 := by
      have hlim : Tendsto (fun n => t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ)
          atTop (𝓝 0) := by simpa using (hlin ε hεpos).const_mul (t ^ 2)
      exact hlim.eventually_lt_const (by linarith)
    filter_upwards [hev1, hVarlt, hLinlt] with n hn1 hn2 hn3
    have hpm : ∀ i, IsProbabilityMeasure (μ.map (X n i)) := fun i =>
      Measure.isProbabilityMeasure_map (hmeas n i).aemeasurable
    have htel := norm_prod_sub_prod_le (𝕜 := ℂ) Finset.univ
      (fun i => charFun (μ.map (X n i)) t)
      (fun i => ((1 - t ^ 2 * variance (X n i) μ / 2 : ℝ) : ℂ))
      (fun i _ => norm_charFun_le_one _)
      (fun i _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hn1 i], by linarith [hunn n i]⟩)
    refine htel.trans ?_
    have hsum2 : ∑ i, ‖charFun (μ.map (X n i)) t
          - ((1 - t ^ 2 * variance (X n i) μ / 2 : ℝ) : ℂ)‖
        ≤ |t| ^ 3 * ε / 6 * ∑ i, variance (X n i) μ
          + t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hterm ε hεpos n i
    refine hsum2.trans ?_
    have hterm1 : |t| ^ 3 * ε / 6 * ∑ i, variance (X n i) μ ≤ δ / 3 := by
      have hnn : (0:ℝ) ≤ |t| ^ 3 * ε / 6 := by positivity
      have hstep : |t| ^ 3 * ε / 6 * ∑ i, variance (X n i) μ
          ≤ |t| ^ 3 * ε / 6 * (σ2 + 1) := mul_le_mul_of_nonneg_left hn2 hnn
      refine hstep.trans ?_
      have hval : |t| ^ 3 * ε / 6 * (σ2 + 1)
          = (|t| ^ 3 * (σ2 + 1)) * δ / (6 * (|t| ^ 3 * (σ2 + 1) + 1)) := by
        rw [hεdef]; field_simp
      rw [hval, div_le_iff₀ (by linarith)]
      nlinarith [hδ.le, hKnn, mul_nonneg hKnn hδ.le]
    linarith [hn3]
  ------------------------------------------------------------------
  -- Combine.
  ------------------------------------------------------------------
  have hcomb := T1.add T2
  simpa using hcomb

/-- **Lindeberg CLT for triangular arrays** (row-wise independent, zero-mean; charFun
form). The Lindeberg sums use the set-integral over `{ε ≤ |X|}`. -/
theorem tendsto_charFun_rowSum_gaussian_of_lindeberg [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    (hmeas : ∀ n i, Measurable (X n i))
    -- USER-INPUT: row-wise independence; Lindeberg CLT
    (hindep : ∀ n, iIndepFun (X n) μ)
    -- USER-INPUT: zero means; Lindeberg CLT
    (hmean : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    (hL2 : ∀ n i, MemLp (X n i) 2 μ)
    {σ2 : ℝ}
    -- USER-INPUT: row-variance convergence; Lindeberg CLT
    (hvar : Tendsto (fun n => ∑ i, variance (X n i) μ) atTop (𝓝 σ2))
    -- USER-INPUT: the Lindeberg condition; Lindeberg CLT
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ)
        atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map fun ω => ∑ i, X n i ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  -- The limit variance is nonnegative (limit of sums of variances).
  have hσ0 : 0 ≤ σ2 :=
    ge_of_tendsto hvar (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => variance_nonneg _ _)
  -- Pass from the closed truncation sets `{ε ≤ |X|}` to the open ones `{ε < |X|}`
  -- (a smaller set with a nonnegative integrand).
  have hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    intro ε hε
    refine squeeze_zero (fun n => Finset.sum_nonneg fun i _ =>
      setIntegral_nonneg (measurableSet_lt measurable_const (hmeas n i).abs)
        fun ω _ => sq_nonneg _) (fun n => Finset.sum_le_sum fun i _ => ?_) (hlind ε hε)
    have hI2 : Integrable (fun ω => (X n i ω) ^ 2) μ := (hL2 n i).integrable_sq
    refine setIntegral_mono_set hI2.integrableOn
      (ae_of_all _ fun ω => sq_nonneg _) (ae_of_all _ fun ω hω => ?_)
    exact le_of_lt hω
  -- Independence turns the row-sum charFun into the product of the entry charFuns.
  have hcf : ∀ n, charFun (μ.map fun ω => ∑ i, X n i ω) u
      = ∏ i, charFun (μ.map (X n i)) u := fun n => by
    rw [iIndepFun.charFun_map_fun_sum_eq_prod (fun i => (hmeas n i).aemeasurable) (hindep n),
      Finset.prod_apply]
  simpa [hcf] using
    tendsto_prod_charFun_lindeberg hmeas hL2 hmean hσ0 hvar hlin u

/-- Convenience corollary: a **uniformly negligible bounded** array (max bound → 0)
with converging row variances satisfies Lindeberg vacuously (eventually the Lindeberg
sets are empty) — the form used in the degenerate-Lindeberg step of FY §2.7.7. -/
theorem tendsto_charFun_rowSum_gaussian_of_uniformly_small [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    (hmeas : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) μ)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    (hL2 : ∀ n i, MemLp (X n i) 2 μ)
    {b : ℕ → ℝ}
    -- USER-INPUT: uniform envelope tending to zero; FY §2.7.7 degenerate Lindeberg
    (hbdd : ∀ n i, ∀ᵐ ω ∂μ, |X n i ω| ≤ b n)
    (hb0 : Tendsto b atTop (𝓝 0))
    {σ2 : ℝ}
    (hvar : Tendsto (fun n => ∑ i, variance (X n i) μ) atTop (𝓝 σ2))
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map fun ω => ∑ i, X n i ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  refine tendsto_charFun_rowSum_gaussian_of_lindeberg hmeas hindep hmean hL2 hvar
    (fun ε hε => ?_) u
  -- Once `b n < ε` the truncation sets are `μ`-null, so the Lindeberg sums vanish.
  have key : ∀ᶠ n in atTop,
      (∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ) = 0 := by
    filter_upwards [hb0.eventually (eventually_lt_nhds hε)] with n hn
    refine Finset.sum_eq_zero fun i _ => ?_
    have hnull : μ {ω | ε ≤ |X n i ω|} = 0 := by
      have h0 : ∀ᵐ ω ∂μ, ω ∉ {ω | ε ≤ |X n i ω|} := by
        filter_upwards [hbdd n i] with ω hω
        simp only [not_le]
        exact lt_of_le_of_lt hω hn
      simpa using ae_iff.1 h0
    rw [show μ.restrict {ω | ε ≤ |X n i ω|} = 0 from Measure.restrict_eq_zero.2 hnull,
      integral_zero_measure]
  exact tendsto_const_nhds.congr' (key.mono fun n hn => hn.symm)

end StatLean.TimeSeries
