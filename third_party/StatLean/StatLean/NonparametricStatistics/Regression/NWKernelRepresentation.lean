module
public import StatLean.NonparametricStatistics.Regression.Defs
public import StatLean.NonparametricStatistics.KernelDensity.Defs
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section

/-!
# The kernel regression estimator as a ratio of density estimates

For a kernel of order `1` (so `∫K = 1` and `∫uK = 0`), the kernel regression estimator is the
plug-in conditional-mean formula built from kernel density estimates:
$$ f_n(x) \;=\; \frac{\int y\,\hat p_n(x, y)\,dy}{\hat p_n(x)} \qquad
   \text{whenever } \hat p_n(x) \ne 0, $$
where `p̂ₙ(x, y)` is the bivariate product-kernel estimate from the pairs `(Xᵢ, Yᵢ)` and
`p̂ₙ(x)` the marginal estimate from the `Xᵢ`. This identifies the locally-weighted average as
the natural estimator of `E[Y | X = x] = ∫y·p(x,y)dy / p(x)`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.5, Proposition 1.10 (the Nadaraya–Watson
estimator as a ratio of kernel density estimators).

**Proof formalization notes.** A purely algebraic/deterministic identity in the data vectors
(no probability): compute
`∫ y·K((Yᵢ−y)/h) dy = h·(Yᵢ·∫K − h·∫uK) = h·Yᵢ` by the change of variables `y = Yᵢ − hu`
(order-1 moments), then swap the finite sum with the integral and cancel the normalizations.
Integrability of `y ↦ y·K((Yᵢ−y)/h)` comes from the kernel's order-`1` integrability
(`integrable_pow` at `j = 0, 1`) via the same change of variables.

**Bibliographic comments.** E. A. Nadaraya, "On estimating regression," *Theory Probab. Appl.*
**9** (1964), 141–142; G. S. Watson, "Smooth regression analysis," *Sankhyā Ser. A* **26**
(1964), 359–372.
-/

open MeasureTheory

namespace StatLean.NonparametricStatistics

/-- Reflection–scaling change of variables `y = c − u·h` on the whole line (`h > 0`). -/
private lemma integral_reflect_scale (F : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (c : ℝ) :
    (∫ y, F y) = h * ∫ u, F (c - u * h) := by
  have h1 : (∫ u, F (c + u * (-h))) = |(-h)⁻¹| • ∫ y, F (c + y) :=
    Measure.integral_comp_mul_right (fun y => F (c + y)) (-h)
  have hcong : (fun u => F (c - u * h)) = fun u => F (c + u * (-h)) := by
    funext u; rw [mul_neg, ← sub_eq_add_neg]
  rw [hcong, h1, integral_add_left_eq_self F c, smul_eq_mul, inv_neg, abs_neg,
    abs_of_pos (inv_pos.2 hh), ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

/-- The order-`1` moment identity `∫ y·K((c − y)/h) dy = h·c`. -/
private lemma integral_ykernel {K : ℝ → ℝ} (hK : IsKernelOfOrder K 1) {h : ℝ} (hh : 0 < h)
    (c : ℝ) : ∫ y, y * K ((c - y) / h) = h * c := by
  have hIK : Integrable K := by have := hK.integrable_pow 0 (by norm_num); simpa using this
  have hIuK : Integrable fun u => u ^ 1 * K u := hK.integrable_pow 1 le_rfl
  rw [integral_reflect_scale (fun y => y * K ((c - y) / h)) hh c]
  have hcong : (fun u => (fun y => y * K ((c - y) / h)) (c - u * h))
      = fun u => c * K u - h * (u ^ 1 * K u) := by
    funext u
    have ha : c - (c - u * h) = u * h := by ring
    simp only [ha, mul_div_cancel_right₀ _ hh.ne', pow_one]
    ring
  rw [hcong, integral_sub (hIK.const_mul c) (hIuK.const_mul h), integral_const_mul,
    integral_const_mul, hK.integral_eq_one, hK.moment_eq_zero 1 le_rfl le_rfl]
  ring

/-- Integrability of `y ↦ y·K((c − y)/h)` from the order-`1` integrability of `K`. -/
private lemma integrable_ykernel {K : ℝ → ℝ} (hIK : Integrable K)
    (hIuK : Integrable fun u => u * K u) {h : ℝ} (hh : 0 < h) (c : ℝ) :
    Integrable (fun y => y * K ((c - y) / h)) := by
  have hP0 : Integrable (fun u => (fun y => y * K ((c - y) / h)) (c + u * (-h))) := by
    have heq : (fun u => (fun y => y * K ((c - y) / h)) (c + u * (-h)))
        = fun u => c * K u - h * (u * K u) := by
      funext u
      have ha : c + u * (-h) = c - u * h := by ring
      simp only [ha, sub_sub_cancel, mul_div_cancel_right₀ _ hh.ne']
      ring
    rw [heq]; exact (hIK.const_mul c).sub (hIuK.const_mul h)
  have hscale := (integrable_comp_mul_right_iff
    (fun y => (fun y => y * K ((c - y) / h)) (c + y)) (neg_ne_zero.2 hh.ne')).mp hP0
  exact ((measurePreserving_add_left (volume : Measure ℝ) c).integrable_comp_emb
    (measurableEmbedding_addLeft c) (g := fun y => y * K ((c - y) / h))).mp hscale

/-- **Kernel regression as a ratio of kernel density estimates**: for a kernel of order `1`,
positive bandwidth, and nonvanishing marginal estimate at `x`,
`nadarayaWatson xdat ydat K h x = (∫ y, y·p̂ₙ(x,y) dy) / p̂ₙ(x)`. -/
theorem nadarayaWatson_eq_kde_ratio {n : ℕ} (xdat ydat : Fin n → ℝ) {K : ℝ → ℝ}
    -- USER-INPUT: `K` is a kernel of order 1 (`∫K = 1`, `∫uK = 0`); the classical hypothesis
    -- making the bivariate plug-in formula collapse to the weighted average
    (hK : IsKernelOfOrder K 1)
    {h : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    {x : ℝ}
    -- USER-INPUT: nonvanishing marginal density estimate at `x`; the classical proviso of
    -- the ratio formula
    (hden : kdeData xdat K h x ≠ 0) :
    nadarayaWatson xdat ydat K h x
      = (∫ y, y * kde2Data xdat ydat K h x y) / kdeData xdat K h x := by
  have hIK : Integrable K := by
    have := hK.integrable_pow 0 (by norm_num); simpa using this
  have hIuK : Integrable fun u => u * K u := by
    have := hK.integrable_pow 1 le_rfl; simpa using this
  have hden' : ((n : ℝ) * h)⁻¹ * (∑ i, K ((xdat i - x) / h)) ≠ 0 := hden
  obtain ⟨hnh, hS⟩ := mul_ne_zero_iff.1 hden'
  have hnh0 : (n : ℝ) * h ≠ 0 := fun hc => hnh (by rw [hc, inv_zero])
  have hn0 : (n : ℝ) ≠ 0 := left_ne_zero_of_mul hnh0
  have hh0 : h ≠ 0 := hh.ne'
  have hval : ∀ i, ∫ y, y * K ((ydat i - y) / h) = h * ydat i :=
    fun i => integral_ykernel hK hh (ydat i)
  have hintg : ∀ i, Integrable (fun y => y * K ((ydat i - y) / h)) :=
    fun i => integrable_ykernel hIK hIuK hh (ydat i)
  have hnum : ∫ y, y * kde2Data xdat ydat K h x y
      = ((n : ℝ) * h)⁻¹ * ∑ i, ydat i * K ((xdat i - x) / h) := by
    have hpt : ∀ y, y * kde2Data xdat ydat K h x y
        = ∑ i, ((n : ℝ) * h ^ 2)⁻¹
            * (K ((xdat i - x) / h) * (y * K ((ydat i - y) / h))) := by
      intro y
      unfold kde2Data
      rw [Finset.mul_sum, mul_comm, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    calc ∫ y, y * kde2Data xdat ydat K h x y
        = ∑ i, ((n : ℝ) * h ^ 2)⁻¹ * (K ((xdat i - x) / h) * (h * ydat i)) := by
          rw [integral_congr_ae (ae_of_all _ hpt),
            integral_finset_sum _ (fun i _ =>
              ((hintg i).const_mul (K ((xdat i - x) / h))).const_mul ((n : ℝ) * h ^ 2)⁻¹)]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [integral_const_mul, integral_const_mul, hval i]
      _ = ((n : ℝ) * h)⁻¹ * ∑ i, ydat i * K ((xdat i - x) / h) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          field_simp
  rw [nadarayaWatson, if_neg hS, hnum]
  unfold kdeData
  rw [mul_div_mul_left _ _ hnh]

end StatLean.NonparametricStatistics
