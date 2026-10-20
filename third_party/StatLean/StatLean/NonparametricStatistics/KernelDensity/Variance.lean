module
public import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Pointwise variance of the kernel density estimator

For an i.i.d. sample from a density bounded by `pmax` and a square-integrable kernel:
$$ \sigma^2(x_0) \;\le\; \frac{C_1}{n h}, \qquad C_1 = p_{\max}\int K^2(u)\,du, $$
for **any** `x₀`, `h > 0`, `n` — a fully non-asymptotic bound. Also provided: the estimator is
square-integrable under these hypotheses, and the exact bias–variance decomposition of the
pointwise mean squared error.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.1, Proposition 1.1 (pointwise variance
bound, constant $C_1 = p_{\max}\int K^2$).

**Proof formalization notes.** Write `p̂ₙ(x₀) = (nh)⁻¹ ∑ ηᵢ + E` with
`ηᵢ = K((Xᵢ−x₀)/h) − E K((Xᵢ−x₀)/h)` i.i.d. centered; independence gives
`Var(p̂ₙ(x₀)) = (nh²)⁻¹·n⁻¹·…` — concretely `Mathlib`'s `IndepFun.variance_sum` after
establishing `MemLp 2` of each summand from
`E K² = ∫ K²((z−x₀)/h)·p(z) dz ≤ pmax·h·∫K²` (law transfer + change of variables). The `ℝ≥0∞`
definition `kdeVarianceAt` matches the Bochner variance under `MemLp 2`
(`kdeVarianceAt_eq_ofReal_variance`); the decomposition needs the same `MemLp 2`.
Degenerate `n = 0` makes the estimator `0` and both sides vacuous-but-true.

**Bibliographic comments.** The variance computation is the classical opening move of kernel
density estimation: M. Rosenblatt, *Ann. Math. Statist.* **27** (1956), 832–837; E. Parzen,
*Ann. Math. Statist.* **33** (1962), 1065–1076.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Affine change of variables `z = x + u·h` on the whole line (`h > 0`). -/
private lemma integral_scale_shift' (F : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (∫ z, F z) = h * ∫ u, F (x + u * h) := by
  have hstep : (∫ u, F (x + u * h)) = |h⁻¹| • ∫ y, F (x + y) :=
    Measure.integral_comp_mul_right (fun y => F (x + y)) h
  rw [hstep, integral_add_left_eq_self F x, smul_eq_mul, abs_of_pos (inv_pos.2 hh),
    ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

/-- Integrability transfer under the affine map `z ↦ (z - x)/h` (`h > 0`). -/
private lemma integrable_affine {h : ℝ} (hh : 0 < h) (x : ℝ) {H : ℝ → ℝ}
    (hH : Integrable H) : Integrable (fun z => H ((z - x) / h)) := by
  have hQ : Integrable (fun y => H (((x + y) - x) / h)) := by
    have hrw : H = fun u => (fun y => H (((x + y) - x) / h)) (u * h) := by
      funext u; simp only [add_sub_cancel_left, mul_div_cancel_right₀ _ hh.ne']
    rw [hrw] at hH
    exact (integrable_comp_mul_right_iff (fun y => H (((x + y) - x) / h)) hh.ne').mp hH
  exact ((measurePreserving_add_left (volume : Measure ℝ) x).integrable_comp_emb
    (measurableEmbedding_addLeft x) (g := fun z => H ((z - x) / h))).mp hQ

/-- Integrability transfer along the law: `g·p` integrable ⇒ `g ∘ X` integrable under `P`. -/
private lemma integrable_comp_law' {X : Ω → ℝ} {p g : ℝ → ℝ}
    (hX : HasLaw X (densityMeasure p) P) (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (hg : Measurable g) (hint : Integrable fun z => g z * p z) :
    Integrable (fun ω => g (X ω)) P := by
  have h2 : Integrable g (densityMeasure p) := by
    rw [densityMeasure, integrable_withDensity_iff hp.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    exact hint.congr (ae_of_all _ fun z => by simp only [ENNReal.toReal_ofReal (h0 z)])
  have h3 := integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable
  rw [hX.map_eq] at h3
  exact h3.mp h2

/-- Each kernel summand `ω ↦ K((Xᵢ ω − x)/h)` is square-integrable. -/
private lemma kernel_summand_memLp {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ}
    {h pmax x : ℝ} (hh : 0 < h) (hs : IsIIDSample P X (densityMeasure p))
    (hX : ∀ i, Measurable (X i)) (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (hbdd : ∀ x, p x ≤ pmax) (hK : Measurable K) (hK2 : Integrable fun u => (K u) ^ 2)
    (i : Fin n) : MemLp (fun ω => K ((X i ω - x) / h)) 2 P := by
  have haesm : AEStronglyMeasurable (fun ω => K ((X i ω - x) / h)) P :=
    (hK.comp (((hX i).sub_const x).div_const h)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq haesm]
  have IntG : Integrable (fun z => (K ((z - x) / h)) ^ 2) volume :=
    integrable_affine hh x (H := fun u => (K u) ^ 2) hK2
  have IntGp : Integrable (fun z => (K ((z - x) / h)) ^ 2 * p z) volume :=
    IntG.mul_bdd hp.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact hbdd z)
  exact integrable_comp_law' (g := fun z => (K ((z - x) / h)) ^ 2) (hs.law i) hp h0
    ((hK.comp ((measurable_id.sub_const x).div_const h)).pow_const 2) IntGp

/-- Second-moment bound for a kernel summand: `E[K((Xᵢ−x)/h)²] ≤ pmax·h·∫K²`. -/
private lemma kernel_summand_sq_le {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ}
    {h pmax x : ℝ} (hh : 0 < h) (hs : IsIIDSample P X (densityMeasure p))
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (hbdd : ∀ x, p x ≤ pmax) (hK : Measurable K)
    (hK2 : Integrable fun u => (K u) ^ 2) (i : Fin n) :
    ∫ ω, (K ((X i ω - x) / h)) ^ 2 ∂P ≤ pmax * (h * ∫ u, (K u) ^ 2) := by
  have hGmeas : Measurable (fun z => (K ((z - x) / h)) ^ 2) :=
    (hK.comp ((measurable_id.sub_const x).div_const h)).pow_const 2
  have IntG : Integrable (fun z => (K ((z - x) / h)) ^ 2) volume :=
    integrable_affine hh x (H := fun u => (K u) ^ 2) hK2
  have IntGp : Integrable (fun z => (K ((z - x) / h)) ^ 2 * p z) volume :=
    IntG.mul_bdd hp.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact hbdd z)
  have htrans : ∫ ω, (K ((X i ω - x) / h)) ^ 2 ∂P = ∫ z, (K ((z - x) / h)) ^ 2 * p z :=
    integral_comp_law_densityMeasure (g := fun z => (K ((z - x) / h)) ^ 2)
      (hs.law i) hp h0 hGmeas IntGp
  rw [htrans]
  calc ∫ z, (K ((z - x) / h)) ^ 2 * p z
      ≤ ∫ z, (K ((z - x) / h)) ^ 2 * pmax := by
        refine integral_mono IntGp (IntG.mul_const pmax) (fun z => ?_)
        exact mul_le_mul_of_nonneg_left (hbdd z) (sq_nonneg _)
    _ = pmax * ∫ z, (K ((z - x) / h)) ^ 2 := by rw [integral_mul_const, mul_comm]
    _ = pmax * (h * ∫ u, (K u) ^ 2) := by
        rw [integral_scale_shift' (fun z => (K ((z - x) / h)) ^ 2) hh x]
        congr 2
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only [add_sub_cancel_left, mul_div_cancel_right₀ _ hh.ne']

/-- The kernel estimator at a point is square-integrable when the sampled density is bounded
and the kernel is measurable and square-integrable. -/
theorem kde_memLp_two {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h pmax : ℝ} {x : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    -- USER-INPUT: the density is bounded by `pmax`; classical variance-bound input
    (hbdd : ∀ x, p x ≤ pmax)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hK : Measurable K)
    -- USER-INPUT: square-integrable kernel; classical variance-bound input
    (hK2 : Integrable fun u => (K u) ^ 2) :
    MemLp (fun ω => kde X K h ω x) 2 P := by
  have hmem : ∀ i, MemLp (fun ω => K ((X i ω - x) / h)) 2 P :=
    fun i => kernel_summand_memLp hh hs hX hp h0 hbdd hK hK2 i
  have hfun : (∑ i : Fin n, fun ω => K ((X i ω - x) / h))
      = fun ω => ∑ i, K ((X i ω - x) / h) := by
    funext ω; simp only [Finset.sum_apply]
  have hsum : MemLp (fun ω => ∑ i, K ((X i ω - x) / h)) 2 P := by
    rw [← hfun]; exact memLp_finset_sum' _ (fun i _ => hmem i)
  exact hsum.const_mul ((n : ℝ) * h)⁻¹

/-- Under square-integrability, the `ℝ≥0∞`-valued variance functional is the Bochner
variance. -/
theorem kdeVarianceAt_eq_ofReal_variance {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ → ℝ}
    {h : ℝ} {x : ℝ}
    (hL2 : MemLp (fun ω => kde X K h ω x) 2 P) :
    kdeVarianceAt P X K h x
      = ENNReal.ofReal (variance (fun ω => kde X K h ω x) P) := by
  have h1 : kdeVarianceAt P X K h x = evariance (fun ω => kde X K h ω x) P := by
    rw [evariance_eq_lintegral_ofReal]; rfl
  rw [h1]
  exact (ENNReal.ofReal_toReal (evariance_ne_top hL2)).symm

/-- **Bias–variance decomposition of the pointwise MSE** (exact, under square-integrability):
`MSE(x) = b(x)² + σ²(x)`. -/
theorem kdeMseAt_eq_bias_sq_add_variance {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ → ℝ}
    {h : ℝ} {p : ℝ → ℝ} {x : ℝ}
    (hL2 : MemLp (fun ω => kde X K h ω x) 2 P) :
    kdeMseAt P X K h p x
      = ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2) + kdeVarianceAt P X K h x := by
  have hInt2 : Integrable (fun ω => kde X K h ω x) P := hL2.integrable (by norm_num)
  have hb : kdeBiasAt P X K h p x = kdeMeanAt P X K h x - p x := rfl
  have hcenter : ∫ ω, (kde X K h ω x - kdeMeanAt P X K h x) ∂P = 0 := by
    rw [integral_sub hInt2 (integrable_const _), integral_const, probReal_univ, one_smul]
    exact sub_self _
  have hV : Integrable (fun ω => (kde X K h ω x - kdeMeanAt P X K h x) ^ 2) P :=
    (hL2.sub (memLp_const _)).integrable_sq
  have hC : Integrable (fun ω => kde X K h ω x - kdeMeanAt P X K h x) P :=
    hInt2.sub (integrable_const _)
  have hsqint : Integrable (fun ω => (kde X K h ω x - p x) ^ 2) P :=
    (hL2.sub (memLp_const _)).integrable_sq
  have hexp : ∀ ω, (kde X K h ω x - p x) ^ 2 - (kde X K h ω x - kdeMeanAt P X K h x) ^ 2
      = (2 * kdeBiasAt P X K h p x) * (kde X K h ω x - kdeMeanAt P X K h x)
        + (kdeBiasAt P X K h p x) ^ 2 := fun ω => by rw [hb]; ring
  have hstep : ∫ ω, ((kde X K h ω x - p x) ^ 2
      - (kde X K h ω x - kdeMeanAt P X K h x) ^ 2) ∂P = (kdeBiasAt P X K h p x) ^ 2 := by
    rw [integral_congr_ae (ae_of_all _ hexp),
      integral_add (hC.const_mul (2 * kdeBiasAt P X K h p x)) (integrable_const _),
      integral_const_mul, hcenter, integral_const, probReal_univ]
    simp
  have hkey : ∫ ω, (kde X K h ω x - p x) ^ 2 ∂P
      = (kdeBiasAt P X K h p x) ^ 2 + ∫ ω, (kde X K h ω x - kdeMeanAt P X K h x) ^ 2 ∂P := by
    rw [← hstep, integral_sub hsqint hV]; ring
  unfold kdeMseAt
  rw [← ofReal_integral_eq_lintegral_ofReal hsqint (ae_of_all _ fun ω => sq_nonneg _),
    hkey, ENNReal.ofReal_add (sq_nonneg _) (integral_nonneg fun ω => sq_nonneg _)]
  congr 1
  unfold kdeVarianceAt
  rw [← ofReal_integral_eq_lintegral_ofReal hV (ae_of_all _ fun ω => sq_nonneg _)]

/-- **Pointwise variance bound for the kernel density estimator**: for any `x₀`, `h > 0`, `n`,
`σ²(x₀) ≤ C₁/(n·h)` with the explicit constant `C₁ = pmax·∫K²`. -/
theorem kde_variance_le {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h pmax : ℝ} {x₀ : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    -- USER-INPUT: the density is bounded by `pmax`; classical variance-bound input
    (hbdd : ∀ x, p x ≤ pmax)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hK : Measurable K)
    -- USER-INPUT: square-integrable kernel; classical variance-bound input
    (hK2 : Integrable fun u => (K u) ^ 2) :
    kdeVarianceAt P X K h x₀
      ≤ ENNReal.ofReal (kdeVarianceConst K pmax / ((n : ℝ) * h)) := by
  have hL2 : MemLp (fun ω => kde X K h ω x₀) 2 P :=
    kde_memLp_two hh hs hX hp h0 hbdd hK hK2
  rw [kdeVarianceAt_eq_ofReal_variance hL2]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : (fun ω => kde X K h ω x₀) = (0 : Ω → ℝ) := by
      funext ω; simp [kde, kdeData]
    rw [hz, variance_zero]
    simp
  · have hmemP : ∀ i, MemLp (fun ω => K ((X i ω - x₀) / h)) 2 P :=
      fun i => kernel_summand_memLp hh hs hX hp h0 hbdd hK hK2 i
    have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)))
        (fun i j => (fun ω => K ((X i ω - x₀) / h)) ⟂ᵢ[P] (fun ω => K ((X j ω - x₀) / h))) := by
      intro i _ j _ hij
      exact (hs.indep.indepFun hij).comp (hK.comp ((measurable_id.sub_const x₀).div_const h))
        (hK.comp ((measurable_id.sub_const x₀).div_const h))
    have hvarsum : variance (fun ω => ∑ i, K ((X i ω - x₀) / h)) P
        = ∑ i, variance (fun ω => K ((X i ω - x₀) / h)) P := by
      rw [show (fun ω => ∑ i, K ((X i ω - x₀) / h))
          = ∑ i : Fin n, (fun ω => K ((X i ω - x₀) / h)) from by
            funext ω; simp only [Finset.sum_apply]]
      exact IndepFun.variance_sum (fun i _ => hmemP i) hpair
    have hvar : variance (fun ω => kde X K h ω x₀) P
        = (((n : ℝ) * h)⁻¹) ^ 2 * ∑ i, variance (fun ω => K ((X i ω - x₀) / h)) P := by
      have hrfl : (fun ω => kde X K h ω x₀)
          = fun ω => ((n : ℝ) * h)⁻¹ * ∑ i, K ((X i ω - x₀) / h) := rfl
      rw [hrfl, variance_const_mul, hvarsum]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [hvar]
    have hvle : ∑ i, variance (fun ω => K ((X i ω - x₀) / h)) P
        ≤ (n : ℝ) * (pmax * (h * ∫ u, (K u) ^ 2)) := by
      calc ∑ i, variance (fun ω => K ((X i ω - x₀) / h)) P
          ≤ ∑ _i : Fin n, pmax * (h * ∫ u, (K u) ^ 2) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            exact (variance_le_expectation_sq (hmemP i).aestronglyMeasurable).trans
              (kernel_summand_sq_le hh hs hp h0 hbdd hK hK2 i)
        _ = (n : ℝ) * (pmax * (h * ∫ u, (K u) ^ 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine (mul_le_mul_of_nonneg_left hvle (sq_nonneg _)).trans (le_of_eq ?_)
    have hh' : h ≠ 0 := hh.ne'
    rw [kdeVarianceConst]
    field_simp

end StatLean.NonparametricStatistics
