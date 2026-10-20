module
public import StatLean.NonparametricStatistics.KernelDensity.Variance
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-!
# Integrated variance of the kernel density estimator

For **any** probability density `p` (no smoothness, no boundedness) and any square-integrable
kernel:
$$ \int \sigma^2(x)\,dx \;\le\; \frac{1}{nh}\int K^2(u)\,du. $$

The striking feature — emphasized in the classical treatment — is that no condition on `p`
whatsoever is required: integrating the pointwise second moment in `x` and applying
Tonelli–Fubini turns the density into its total mass `∫ p = 1`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.3, Proposition 1.4 (integrated variance
bound $(nh)^{-1}\int K^2$, valid for any density).

**Proof formalization notes.** `σ²(x) ≤ (nh²)⁻¹·E K²((X₁−x)/h)`; integrate in `x`, swap by
Tonelli (`lintegral_lintegral_swap`), and change variables `u = (z−x)/h` at fixed `z`
(translation invariance + scaling of Lebesgue measure), yielding
`(nh²)⁻¹·h·∫K²·∫p = (nh)⁻¹·∫K²`. Everything stays in `∫⁻`, so no integrability side
conditions arise.

**Bibliographic comments.** Classical mean-integrated-squared-error analysis: M. Rosenblatt,
*Ann. Math. Statist.* **27** (1956), 832–837; the exact-`L²` viewpoint was developed by
G. S. Watson and M. R. Leadbetter, "On the estimation of the probability density, I," *Ann.
Math. Statist.* **34** (1963), 480–491.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- Integrability transfer along the law (replica of the `Variance.lean` private helper):
`g·p` integrable ⇒ `g ∘ X` integrable under `P`. -/
private lemma integrable_comp_law_iv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p g : ℝ → ℝ}
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

/-- Affine (reflect–scale) change of variables in the lower Lebesgue integral: for `h > 0`,
`∫⁻ x, F ((z − x)/h) dx = h · ∫⁻ y, F y dy`. -/
private lemma lintegral_kernel_shift {F : ℝ → ℝ≥0∞} (hF : Measurable F) {h : ℝ} (hh : 0 < h)
    (z : ℝ) : ∫⁻ x, F ((z - x) / h) = ENNReal.ofReal h * ∫⁻ y, F y := by
  have hSmeas : Measurable (fun x : ℝ => (z - x) / h) :=
    (measurable_const.sub measurable_id).div_const h
  have hmap : Measure.map (fun x : ℝ => (z - x) / h) volume = ENNReal.ofReal h • volume := by
    have hcomp : (fun x : ℝ => (z - x) / h)
        = (fun y : ℝ => y + z / h) ∘ (fun x : ℝ => x * (-h⁻¹)) := by
      funext x; simp only [Function.comp_apply]; field_simp; ring
    rw [hcomp, ← Measure.map_map (show Measurable (fun y : ℝ => y + z / h) by fun_prop)
      (show Measurable (fun x : ℝ => x * (-h⁻¹)) by fun_prop),
      Real.map_volume_mul_right (neg_ne_zero.2 (inv_ne_zero hh.ne')),
      Measure.map_smul, map_add_right_eq_self]
    congr 1
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos hh]
  calc ∫⁻ x, F ((z - x) / h)
      = ∫⁻ y, F y ∂(Measure.map (fun x : ℝ => (z - x) / h) volume) :=
        (lintegral_map hF hSmeas).symm
    _ = ENNReal.ofReal h * ∫⁻ y, F y := by rw [hmap, lintegral_smul_measure, smul_eq_mul]

/-- **Integrated variance bound**: for any density `p` and square-integrable kernel,
`∫ σ²(x) dx ≤ (n·h)⁻¹·∫K²`. -/
theorem kde_integrated_variance_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- LEAN-ONLY: measurability of the density; standard regularity (no other condition on
    -- `p` is needed — the classical point of this bound)
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hK : Measurable K)
    -- USER-INPUT: square-integrable kernel; classical input
    (hK2 : Integrable fun u => (K u) ^ 2) :
    (∫⁻ x, kdeVarianceAt P X K h x)
      ≤ ENNReal.ofReal (((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- Degenerate: `n = 0` makes the estimator identically `0`, so the variance vanishes.
    have hk : ∀ x ω, kde X K h ω x = 0 := by intro x ω; simp [kde, kdeData]
    have hzero : ∀ x, kdeVarianceAt P X K h x = 0 := by
      intro x
      simp only [kdeVarianceAt, kdeMeanAt, hk, integral_zero, sub_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero, lintegral_zero]
    rw [lintegral_congr hzero, lintegral_zero]
    exact zero_le
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hh' : h ≠ 0 := hh.ne'
  -- The density integrates to one at the `∫⁻` level.
  have hprob : IsProbabilityMeasure (densityMeasure p) := by
    rw [← (hs.law ⟨0, hn⟩).map_eq]
    exact Measure.isProbabilityMeasure_map (hs.law ⟨0, hn⟩).aemeasurable
  have hmass : (∫⁻ z, ENNReal.ofReal (p z)) = 1 := by
    have h := hprob.measure_univ
    rwa [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  -- Joint measurability of the kernel `(x, z) ↦ ofReal(K((z−x)/h)²)·ofReal(p z)`.
  have hΦmeas : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal ((K ((q.2 - q.1) / h)) ^ 2) * ENNReal.ofReal (p q.2)) :=
    (((hK.comp ((measurable_snd.sub measurable_fst).div_const h)).pow_const 2).ennreal_ofReal).mul
      ((hp.comp measurable_snd).ennreal_ofReal)
  have hGℓmeas : Measurable fun x => ∫⁻ z,
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) :=
    hΦmeas.lintegral_prod_right'
  -- The total double integral: `∫∫ = h · ∫K²`.
  have hD : (∫⁻ x, ∫⁻ z, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z))
      = ENNReal.ofReal h * ENNReal.ofReal (∫ u, (K u) ^ 2) := by
    rw [lintegral_lintegral_swap (f := fun x z =>
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z)) hΦmeas.aemeasurable]
    have hinner : ∀ z, (∫⁻ x, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z))
        = ENNReal.ofReal h * ENNReal.ofReal (∫ u, (K u) ^ 2) * ENNReal.ofReal (p z) := by
      intro z
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      congr 1
      rw [lintegral_kernel_shift ((hK.pow_const 2).ennreal_ofReal) hh z]
      congr 1
      exact (ofReal_integral_eq_lintegral_ofReal hK2 (ae_of_all _ fun u => sq_nonneg _)).symm
    rw [lintegral_congr hinner,
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      hmass, mul_one]
  -- A.e. finiteness of the per-`x` second moment `Gℓ x`.
  have hGℓfin : ∀ᵐ x, (∫⁻ z,
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z)) < ⊤ := by
    refine ae_lt_top hGℓmeas ?_
    rw [hD]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- The per-`x` variance bound at points where `Gℓ x < ∞`.
  have hae : ∀ᵐ x, kdeVarianceAt P X K h x
      ≤ ENNReal.ofReal (((n : ℝ) * h ^ 2)⁻¹) * ∫⁻ z,
        ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) := by
    filter_upwards [hGℓfin] with x hx
    have hGmeas : Measurable (fun z => (K ((z - x) / h)) ^ 2) :=
      (hK.comp ((measurable_id.sub_const x).div_const h)).pow_const 2
    have hnn : 0 ≤ᵐ[volume] fun z => (K ((z - x) / h)) ^ 2 * p z :=
      ae_of_all _ fun z => mul_nonneg (sq_nonneg _) (h0 z)
    -- Integrability of the second-moment integrand from finiteness of `Gℓ x`.
    have hIntGp : Integrable (fun z => (K ((z - x) / h)) ^ 2 * p z) volume := by
      refine ⟨(hGmeas.mul hp).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnn]
      have hcongr : (fun z => ENNReal.ofReal ((K ((z - x) / h)) ^ 2 * p z))
          = fun z => ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) := by
        funext z; rw [ENNReal.ofReal_mul (sq_nonneg _)]
      rw [hcongr]; exact hx
    -- Each summand is `L²`, with equal second moments `Greal x`.
    have hmemP : ∀ i, MemLp (fun ω => K ((X i ω - x) / h)) 2 P := by
      intro i
      have haesm : AEStronglyMeasurable (fun ω => K ((X i ω - x) / h)) P :=
        (hK.comp (((hX i).sub_const x).div_const h)).aestronglyMeasurable
      rw [memLp_two_iff_integrable_sq haesm]
      exact integrable_comp_law_iv (g := fun z => (K ((z - x) / h)) ^ 2)
        (hs.law i) hp h0 hGmeas hIntGp
    have hEsq : ∀ i, ∫ ω, (K ((X i ω - x) / h)) ^ 2 ∂P
        = ∫ z, (K ((z - x) / h)) ^ 2 * p z :=
      fun i => integral_comp_law_densityMeasure (g := fun z => (K ((z - x) / h)) ^ 2)
        (hs.law i) hp h0 hGmeas hIntGp
    -- Assemble the variance of the estimator from independence.
    have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)))
        (fun i j => (fun ω => K ((X i ω - x) / h)) ⟂ᵢ[P] (fun ω => K ((X j ω - x) / h))) := by
      intro i _ j _ hij
      exact (hs.indep.indepFun hij).comp (hK.comp ((measurable_id.sub_const x).div_const h))
        (hK.comp ((measurable_id.sub_const x).div_const h))
    have hvarsum : variance (fun ω => ∑ i, K ((X i ω - x) / h)) P
        = ∑ i, variance (fun ω => K ((X i ω - x) / h)) P := by
      rw [show (fun ω => ∑ i, K ((X i ω - x) / h))
          = ∑ i : Fin n, (fun ω => K ((X i ω - x) / h)) from by
            funext ω; simp only [Finset.sum_apply]]
      exact IndepFun.variance_sum (fun i _ => hmemP i) hpair
    have hvar : variance (fun ω => kde X K h ω x) P
        = (((n : ℝ) * h)⁻¹) ^ 2 * ∑ i, variance (fun ω => K ((X i ω - x) / h)) P := by
      have hrfl : (fun ω => kde X K h ω x)
          = fun ω => ((n : ℝ) * h)⁻¹ * ∑ i, K ((X i ω - x) / h) := rfl
      rw [hrfl, variance_const_mul, hvarsum]
    have hvle : ∑ i, variance (fun ω => K ((X i ω - x) / h)) P
        ≤ (n : ℝ) * ∫ z, (K ((z - x) / h)) ^ 2 * p z := by
      calc ∑ i, variance (fun ω => K ((X i ω - x) / h)) P
          ≤ ∑ _i : Fin n, ∫ z, (K ((z - x) / h)) ^ 2 * p z := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            exact (variance_le_expectation_sq (hmemP i).aestronglyMeasurable).trans
              (le_of_eq (hEsq i))
        _ = (n : ℝ) * ∫ z, (K ((z - x) / h)) ^ 2 * p z := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hvarle : variance (fun ω => kde X K h ω x) P
        ≤ ((n : ℝ) * h ^ 2)⁻¹ * ∫ z, (K ((z - x) / h)) ^ 2 * p z := by
      rw [hvar]
      refine (mul_le_mul_of_nonneg_left hvle (sq_nonneg _)).trans (le_of_eq ?_)
      field_simp
    -- `L²` membership of the estimator, so `kdeVarianceAt = ofReal(variance)`.
    have hfun : (∑ i : Fin n, fun ω => K ((X i ω - x) / h))
        = fun ω => ∑ i, K ((X i ω - x) / h) := by funext ω; simp only [Finset.sum_apply]
    have hsum : MemLp (fun ω => ∑ i, K ((X i ω - x) / h)) 2 P := by
      rw [← hfun]; exact memLp_finset_sum' _ (fun i _ => hmemP i)
    have hL2 : MemLp (fun ω => kde X K h ω x) 2 P := hsum.const_mul ((n : ℝ) * h)⁻¹
    have hofReal : ENNReal.ofReal (∫ z, (K ((z - x) / h)) ^ 2 * p z)
        = ∫⁻ z, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) := by
      rw [ofReal_integral_eq_lintegral_ofReal hIntGp hnn]
      exact lintegral_congr fun z => by rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [kdeVarianceAt_eq_ofReal_variance hL2]
    calc ENNReal.ofReal (variance (fun ω => kde X K h ω x) P)
        ≤ ENNReal.ofReal (((n : ℝ) * h ^ 2)⁻¹ * ∫ z, (K ((z - x) / h)) ^ 2 * p z) :=
          ENNReal.ofReal_le_ofReal hvarle
      _ = ENNReal.ofReal (((n : ℝ) * h ^ 2)⁻¹)
            * ENNReal.ofReal (∫ z, (K ((z - x) / h)) ^ 2 * p z) :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (((n : ℝ) * h ^ 2)⁻¹) * ∫⁻ z,
            ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) := by rw [hofReal]
  -- Integrate the per-`x` bound and evaluate the total mass.
  calc ∫⁻ x, kdeVarianceAt P X K h x
      ≤ ∫⁻ x, ENNReal.ofReal (((n : ℝ) * h ^ 2)⁻¹) * ∫⁻ z,
          ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) :=
        lintegral_mono_ae hae
    _ = ENNReal.ofReal (((n : ℝ) * h ^ 2)⁻¹)
          * ∫⁻ x, ∫⁻ z, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (((n : ℝ) * h ^ 2)⁻¹)
          * (ENNReal.ofReal h * ENNReal.ofReal (∫ u, (K u) ^ 2)) := by rw [hD]
    _ = ENNReal.ofReal (((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((n : ℝ) * h ^ 2)⁻¹),
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hh.le)]
        congr 1
        field_simp

end StatLean.NonparametricStatistics
