module
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
Asymptotic Statistics — pure L² / integral utility lemmas.

Theorem-agnostic real-analysis facts reused across the formalisation. These
live in `ForMathlib/` because they depend only on Mathlib and are candidates
for eventual upstreaming.

## Contents

* `integral_sq_nonneg`                   — `0 ≤ ∫ f² dμ`.
* `sq_add_le_two_mul_sq`                 — pointwise `(a + b)² ≤ 2a² + 2b²`.
* `sq_sub_le_two_mul_sq`                 — pointwise `(a − b)² ≤ 2a² + 2b²`.
* `abs_integral_mul_le_sqrt_integral_sq` — Cauchy–Schwarz on real integrals.
* `integrable_mul_of_memLp_two`          — `L² × L² → L¹` for real functions.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
open scoped ENNReal

namespace AsymptoticStatistics
namespace L2Utils

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-! ## Pointwise and integral inequalities -/

/-- The integral of a square is non-negative. -/
lemma integral_sq_nonneg (μ : Measure 𝓧) (f : 𝓧 → ℝ) :
    0 ≤ ∫ x, (f x) ^ 2 ∂μ :=
  MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)

/-- Pointwise inequality: `(a + b)² ≤ 2 a² + 2 b²`.  Follows from
`(a − b)² ≥ 0 ⇒ a² + b² ≥ 2ab ⇒ (a+b)² = a² + 2ab + b² ≤ 2(a² + b²)`. -/
lemma sq_add_le_two_mul_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Pointwise inequality: `(a - b)² ≤ 2 a² + 2 b²`.  Symmetric. -/
lemma sq_sub_le_two_mul_sq (a b : ℝ) :
    (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-! ## Cauchy–Schwarz and Hölder specialisations -/

/-- **Cauchy–Schwarz for real-valued integrals**:
`|∫ f·g dμ| ≤ √(∫ f² dμ) · √(∫ g² dμ)` for `f, g ∈ L²(μ)`.

Proof: lift `f, g` to `Lp ℝ 2 μ`, apply the abstract Cauchy–Schwarz
`real_inner_mul_inner_self_le`, and translate the inner products back to
integrals via `MeasureTheory.L2.inner_def`. -/
lemma abs_integral_mul_le_sqrt_integral_sq
    (μ : Measure 𝓧) {f g : 𝓧 → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ|
      ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  set F : Lp ℝ 2 μ := hf.toLp f with hF_def
  set G : Lp ℝ 2 μ := hg.toLp g with hG_def
  have hF_ae : (F : 𝓧 → ℝ) =ᵐ[μ] f := MemLp.coeFn_toLp hf
  have hG_ae : (G : 𝓧 → ℝ) =ᵐ[μ] g := MemLp.coeFn_toLp hg
  have hFG_eq : ∫ x, F x * G x ∂μ = ∫ x, f x * g x ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hF_ae, hG_ae] with x hxF hxG
    rw [hxF, hxG]
  have hFF_eq : ∫ x, (F x) ^ 2 ∂μ = ∫ x, (f x) ^ 2 ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hF_ae] with x hxF
    rw [hxF]
  have hGG_eq : ∫ x, (G x) ^ 2 ∂μ = ∫ x, (g x) ^ 2 ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hG_ae] with x hxG
    rw [hxG]
  have h_cs : ⟪F, G⟫ * ⟪F, G⟫ ≤ ⟪F, F⟫ * ⟪G, G⟫ :=
    real_inner_mul_inner_self_le F G
  have hFG_inner : (⟪F, G⟫ : ℝ) = ∫ x, F x * G x ∂μ := by
    rw [MeasureTheory.L2.inner_def F G]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact mul_comm _ _
  have hFF_inner : (⟪F, F⟫ : ℝ) = ∫ x, (F x) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def F F]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [sq]
  have hGG_inner : (⟪G, G⟫ : ℝ) = ∫ x, (G x) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def G G]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [sq]
  rw [hFG_inner, hFF_inner, hGG_inner, hFG_eq, hFF_eq, hGG_eq] at h_cs
  have h_lhs_sq :
      (∫ x, f x * g x ∂μ) * (∫ x, f x * g x ∂μ) = |∫ x, f x * g x ∂μ| ^ 2 := by
    rw [sq_abs]; ring
  rw [h_lhs_sq] at h_cs
  have hF_sq_nn : 0 ≤ ∫ x, (f x) ^ 2 ∂μ := integral_sq_nonneg μ f
  have h_abs_nn : 0 ≤ |∫ x, f x * g x ∂μ| := abs_nonneg _
  have h_sqrt_le := Real.sqrt_le_sqrt h_cs
  rw [Real.sqrt_sq h_abs_nn, Real.sqrt_mul hF_sq_nn] at h_sqrt_le
  exact h_sqrt_le

/-- Specialised `L² × L² → L¹` for real-valued functions. -/
lemma integrable_mul_of_memLp_two
    (μ : Measure 𝓧) {f g : 𝓧 → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * g x) μ := by
  simpa using! hf.integrable_mul hg

/-- **L² norm-square convergence from L²-difference convergence.**

If `g ∈ L²(μ)` and `∫(f_n − g)² dμ → 0`, then `∫f_n² dμ → ∫g² dμ`.

Proof. `f_n² = (f_n − g)² + 2(f_n − g)·g + g²` pointwise. Integrate:
`∫f_n² = ∫(f_n − g)² + 2∫(f_n − g)·g + ∫g²`. The first → 0 by hypothesis;
the second → 0 by Cauchy–Schwarz `|∫(f_n − g)·g| ≤ √(∫(f_n − g)²)·√(∫g²) → 0`;
the third is constant. -/
lemma tendsto_integral_sq_of_tendsto_integral_diff_sq
    (μ : Measure 𝓧) {f : ℕ → 𝓧 → ℝ} {g : 𝓧 → ℝ}
    (hg_memLp : MemLp g 2 μ)
    (hf_diff_memLp : ∀ᶠ n in Filter.atTop, MemLp (fun x => f n x - g x) 2 μ)
    (h_diff_tendsto :
      Filter.Tendsto (fun n : ℕ => ∫ x, (f n x - g x) ^ 2 ∂μ)
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n : ℕ => ∫ x, (f n x) ^ 2 ∂μ)
      Filter.atTop (𝓝 (∫ x, (g x) ^ 2 ∂μ)) := by
  -- Set up integrability ingredients.
  have hg_sq_int : Integrable (fun x => (g x) ^ 2) μ := hg_memLp.integrable_sq
  have hg_sq_nn : 0 ≤ ∫ x, (g x) ^ 2 ∂μ := integral_sq_nonneg μ g
  -- The cross term tends to 0 by Cauchy–Schwarz.
  have h_cross_tendsto :
      Filter.Tendsto (fun n : ℕ => ∫ x, (f n x - g x) * g x ∂μ)
        Filter.atTop (𝓝 0) := by
    -- Bound: `|∫(f_n - g)·g dμ| ≤ √(∫(f_n - g)²) · √(∫g²)`.
    have h_bound : ∀ᶠ n in Filter.atTop,
        |∫ x, (f n x - g x) * g x ∂μ| ≤
          Real.sqrt (∫ x, (f n x - g x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
      filter_upwards [hf_diff_memLp] with n hn_diff_memLp
      exact abs_integral_mul_le_sqrt_integral_sq μ hn_diff_memLp hg_memLp
    -- `√(∫(f_n - g)²) → 0` from `h_diff_tendsto`.
    have h_sqrt_diff : Filter.Tendsto
        (fun n : ℕ => Real.sqrt (∫ x, (f n x - g x) ^ 2 ∂μ))
        Filter.atTop (𝓝 0) := by
      have := h_diff_tendsto
      have h_cont : Continuous Real.sqrt := Real.continuous_sqrt
      have h_at_zero : Real.sqrt 0 = 0 := Real.sqrt_zero
      have := (h_cont.tendsto 0).comp h_diff_tendsto
      simpa [h_at_zero] using! this
    -- Multiply by the constant `√(∫g²)`.
    have h_const : Tendsto (fun _ : ℕ => Real.sqrt (∫ x, (g x) ^ 2 ∂μ))
        atTop (𝓝 (Real.sqrt (∫ x, (g x) ^ 2 ∂μ))) := tendsto_const_nhds
    have h_prod := h_sqrt_diff.mul h_const
    simp only [zero_mul] at h_prod
    -- Sandwich `0 ≤ |∫(f_n - g)·g| ≤ √(...)·√(...) → 0` to get `|∫(f_n - g)·g| → 0`.
    have h_abs_tendsto :
        Filter.Tendsto (fun n : ℕ => |∫ x, (f n x - g x) * g x ∂μ|)
          Filter.atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (b := Filter.atTop)
        (g := fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds h_prod
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) h_bound
    -- Convert `|·| → 0` to `· → 0`.
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h_abs_tendsto
  -- Pointwise expansion: `(f_n)² = (f_n - g)² + 2(f_n - g)·g + g²`.
  have h_pt_expand : ∀ n x, (f n x) ^ 2 =
      (f n x - g x) ^ 2 + 2 * ((f n x - g x) * g x) + (g x) ^ 2 := by
    intro n x; ring
  -- Integrate the expansion (eventually, for n with f_n - g ∈ L²).
  have h_int_eq : ∀ᶠ n in Filter.atTop,
      ∫ x, (f n x) ^ 2 ∂μ =
        (∫ x, (f n x - g x) ^ 2 ∂μ) +
        2 * (∫ x, (f n x - g x) * g x ∂μ) +
        (∫ x, (g x) ^ 2 ∂μ) := by
    filter_upwards [hf_diff_memLp] with n hn_diff_memLp
    have h_diff_sq_int : Integrable (fun x => (f n x - g x) ^ 2) μ :=
      hn_diff_memLp.integrable_sq
    have h_cross_int : Integrable (fun x => (f n x - g x) * g x) μ :=
      integrable_mul_of_memLp_two μ hn_diff_memLp hg_memLp
    have h_2cross_int : Integrable (fun x => 2 * ((f n x - g x) * g x)) μ :=
      h_cross_int.const_mul 2
    calc ∫ x, (f n x) ^ 2 ∂μ
        = ∫ x, ((f n x - g x) ^ 2 + 2 * ((f n x - g x) * g x) + (g x) ^ 2) ∂μ := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x; exact h_pt_expand n x
      _ = (∫ x, ((f n x - g x) ^ 2 + 2 * ((f n x - g x) * g x)) ∂μ) +
            ∫ x, (g x) ^ 2 ∂μ :=
          MeasureTheory.integral_add (h_diff_sq_int.add h_2cross_int) hg_sq_int
      _ = (∫ x, (f n x - g x) ^ 2 ∂μ) + (∫ x, 2 * ((f n x - g x) * g x) ∂μ) +
            ∫ x, (g x) ^ 2 ∂μ := by
          rw [MeasureTheory.integral_add h_diff_sq_int h_2cross_int]
      _ = (∫ x, (f n x - g x) ^ 2 ∂μ) + 2 * (∫ x, (f n x - g x) * g x ∂μ) +
            ∫ x, (g x) ^ 2 ∂μ := by
          rw [MeasureTheory.integral_const_mul]
  -- Combine: each piece tendsto to its limit.
  have h_combined :
      Filter.Tendsto (fun n : ℕ =>
        (∫ x, (f n x - g x) ^ 2 ∂μ) +
        2 * (∫ x, (f n x - g x) * g x ∂μ) +
        (∫ x, (g x) ^ 2 ∂μ)) Filter.atTop
        (𝓝 (0 + 2 * 0 + ∫ x, (g x) ^ 2 ∂μ)) :=
    ((h_diff_tendsto.add (h_cross_tendsto.const_mul 2)).add tendsto_const_nhds)
  simp only [zero_add, mul_zero] at h_combined
  exact h_combined.congr' (h_int_eq.mono (fun n hn => hn.symm))

/-- **Converse of `.toReal²/t² → 0` ⇒ `ℝ≥0∞`-quotient → 0**.
If each `F t` is eventually in `L²(μ)` near `0` and
`(eLpNorm (F t) 2 μ).toReal² / t² → 0`, then the `ℝ≥0∞`-quotient
`eLpNorm (F t) 2 μ / ENNReal.ofReal |t| → 0`. This is the converse direction of
`Core/QMDPath.QMDPath.qmd_limit_toReal_sq`, used to repackage the coarsened QMD
residual bound into the `ℝ≥0∞`-form `qmd_limit` field. -/
theorem tendsto_eLpNorm_div_ofReal_of_toReal_sq
    {μ : Measure 𝓧} {F : ℝ → 𝓧 → ℝ}
    (h_mem : ∀ᶠ t in 𝓝[≠] (0 : ℝ), MemLp (F t) 2 μ)
    (h_sq : Tendsto (fun t => (eLpNorm (F t) 2 μ).toReal ^ 2 / t ^ 2)
      (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun t => eLpNorm (F t) 2 μ / ENNReal.ofReal |t|)
      (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := by
  -- Step 1: the ℝ-valued quotient `(eLpNorm).toReal / |t| → 0`.
  -- From `h_sq`, `((eLpNorm).toReal / |t|)² → 0` (since `t² = |t|²`); take
  -- `Real.sqrt` (continuous) and use `√(x²) = x` for the nonneg quotient.
  have h_q : Tendsto (fun t => (eLpNorm (F t) 2 μ).toReal / |t|)
      (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have h_sq' : Tendsto (fun t => ((eLpNorm (F t) 2 μ).toReal / |t|) ^ 2)
        (𝓝[≠] 0) (𝓝 0) := by
      have h_eq : (fun t => (eLpNorm (F t) 2 μ).toReal ^ 2 / t ^ 2)
          = (fun t => ((eLpNorm (F t) 2 μ).toReal / |t|) ^ 2) := by
        funext t; rw [div_pow, sq_abs]
      rwa [h_eq] at h_sq
    have hcont := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h_sq'
    rw [Real.sqrt_zero] at hcont
    refine hcont.congr (fun t => ?_)
    exact Real.sqrt_sq (div_nonneg ENNReal.toReal_nonneg (abs_nonneg t))
  -- Step 2: push through `ENNReal.ofReal` (continuous at `0`).
  have h_ofReal :
      Tendsto (fun t => ENNReal.ofReal ((eLpNorm (F t) 2 μ).toReal / |t|))
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := by
    have := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h_q
    rwa [ENNReal.ofReal_zero] at this
  -- Step 3: eventual equality with the `ℝ≥0∞`-quotient (finiteness + `|t|>0`).
  have h_eq_ev :
      (fun t => ENNReal.ofReal ((eLpNorm (F t) 2 μ).toReal / |t|))
        =ᶠ[𝓝[≠] (0 : ℝ)] (fun t => eLpNorm (F t) 2 μ / ENNReal.ofReal |t|) := by
    have h_self_ne : {x : ℝ | x ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := self_mem_nhdsWithin
    filter_upwards [h_mem, h_self_ne] with t ht_mem ht_ne
    have habs : 0 < |t| := abs_pos.mpr ht_ne
    rw [ENNReal.ofReal_div_of_pos habs,
      ENNReal.ofReal_toReal ht_mem.eLpNorm_ne_top]
  exact h_ofReal.congr' h_eq_ev

end L2Utils
end AsymptoticStatistics
