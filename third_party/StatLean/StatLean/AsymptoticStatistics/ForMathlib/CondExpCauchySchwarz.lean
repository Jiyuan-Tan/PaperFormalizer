module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Conditional Cauchy–Schwarz and a conditional support lemma

Two `ForMathlib` bricks for the coarsening QMD proof (vdV Lem 25.34-I):

* **`condExp_sq_le_condExp_mul_condExp`**: the conditional Cauchy–Schwarz
  inequality `(E[f·g | m])² ≤ E[f² | m]·E[g² | m]` a.e., for `f, g ∈ L²(μ)`.
  For every rational `q`, `0 ≤ᵐ E[(f − q·g)² | m]` by
  `condExp_nonneg` on the expanded square; take `ae_all_iff` over `ℚ`; the
  pointwise quadratic discriminant `(∀ q : ℚ, 0 ≤ a − 2qb + q²c) → b² ≤ a·c`
  closes it.

* **`ae_eq_zero_on_of_condExp_eq_zero`**: if `f ≥ 0` a.e. and its
  conditional expectation vanishes a.e. on an `m`-measurable set `G`, then `f`
  itself vanishes a.e. on `G`. The proof uses `setIntegral_condExp` to transfer the
  vanishing integral to `f`, then `integral_eq_zero_iff_of_nonneg`.

Both are theorem-agnostic and candidates for upstreaming.

Headline declarations: `condExp_sq_le_condExp_mul_condExp`,
`ae_eq_zero_on_of_condExp_eq_zero`.
-/

open MeasureTheory Filter Topology Set

namespace AsymptoticStatistics.ForMathlib.CondExpCauchySchwarz

variable {Ω : Type*} {m m0 : MeasurableSpace Ω}

/-- Pointwise quadratic discriminant. If the real quadratic `t ↦ a − 2tb + t²c`
is nonnegative at every **rational** `t` and `c ≥ 0`, then `b² ≤ a·c`. The
proof upgrades "nonnegative at every rational" to "nonnegative at every real"
by density (the nonnegativity set is closed), then evaluates at the vertex. -/
private lemma discrim_of_rat_nonneg {a b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ q : ℚ, 0 ≤ a - 2 * (q : ℝ) * b + (q : ℝ) ^ 2 * c) :
    b ^ 2 ≤ a * c := by
  -- Upgrade to all real `t` by density of `ℚ` in `ℝ`.
  have hall : ∀ t : ℝ, 0 ≤ a - 2 * t * b + t ^ 2 * c := by
    have hclosed : IsClosed {t : ℝ | 0 ≤ a - 2 * t * b + t ^ 2 * c} :=
      isClosed_le continuous_const (by fun_prop)
    have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {t : ℝ | 0 ≤ a - 2 * t * b + t ^ 2 * c} := by
      rintro _ ⟨q, rfl⟩; exact h q
    have hclo : closure (Set.range ((↑) : ℚ → ℝ)) ⊆
        {t : ℝ | 0 ≤ a - 2 * t * b + t ^ 2 * c} := closure_minimal hsub hclosed
    rw [(Rat.denseRange_cast (𝕜 := ℝ)).closure_range] at hclo
    intro t; exact hclo (Set.mem_univ t)
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- `c = 0`: the linear inequality at `t = (a+1)/(2b)` forces `b = 0`.
    have hc0' : c = 0 := hc0.symm
    subst hc0'
    have hb : b = 0 := by
      by_contra hbne
      have hval := hall ((a + 1) / (2 * b))
      rw [mul_zero, add_zero] at hval
      have hcancel : 2 * ((a + 1) / (2 * b)) * b = a + 1 := by
        field_simp
      rw [hcancel] at hval
      linarith
    subst hb; simp
  · -- `c > 0`: evaluate at the vertex `t = b/c`.
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have hval := hall (b / c)
    have hcancel : a - 2 * (b / c) * b + (b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp; ring
    rw [hcancel, sub_nonneg] at hval
    calc b ^ 2 = b ^ 2 / c * c := by field_simp
      _ ≤ a * c := mul_le_mul_of_nonneg_right hval hcpos.le

/-- **Conditional Cauchy–Schwarz.** For `f, g ∈ L²(μ)` and a sub-σ-algebra
`m ≤ m0` with `μ.trim hm` σ-finite,
`(E[f·g | m])² ≤ E[f² | m]·E[g² | m]` holds `μ`-a.e. -/
theorem condExp_sq_le_condExp_mul_condExp
    (hm : m ≤ m0) {μ : Measure Ω} [SigmaFinite (μ.trim hm)]
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (fun ω => (μ[fun ω => f ω * g ω | m] ω) ^ 2)
      ≤ᵐ[μ] fun ω => μ[fun ω => f ω ^ 2 | m] ω * μ[fun ω => g ω ^ 2 | m] ω := by
  have hf2 : Integrable (fun ω => f ω ^ 2) μ := hf.integrable_sq
  have hg2 : Integrable (fun ω => g ω ^ 2) μ := hg.integrable_sq
  have hfg : Integrable (fun ω => f ω * g ω) μ := hf.integrable_mul hg
  -- For each rational `q`, the conditional expectation of `(f − q·g)²` is ≥ 0,
  -- and expands linearly to `E[f²|m] − 2q·E[fg|m] + q²·E[g²|m]`.
  have hstep : ∀ q : ℚ, ∀ᵐ ω ∂μ, (0 : ℝ) ≤
      μ[fun ω => f ω ^ 2 | m] ω - 2 * (q : ℝ) * μ[fun ω => f ω * g ω | m] ω
        + (q : ℝ) ^ 2 * μ[fun ω => g ω ^ 2 | m] ω := by
    intro q
    have hs : Integrable (fun ω => 2 * (q : ℝ) * (f ω * g ω)) μ := hfg.const_mul _
    have ht : Integrable (fun ω => (q : ℝ) ^ 2 * g ω ^ 2) μ := hg2.const_mul _
    have hfs : Integrable (fun ω => f ω ^ 2 - 2 * (q : ℝ) * (f ω * g ω)) μ := hf2.sub hs
    -- nonnegativity of the conditional square
    have hnn : (0 : Ω → ℝ) ≤ᵐ[μ]
        μ[fun ω => f ω ^ 2 - 2 * (q : ℝ) * (f ω * g ω) + (q : ℝ) ^ 2 * g ω ^ 2 | m] := by
      apply condExp_nonneg
      filter_upwards with ω
      change (0 : ℝ) ≤ f ω ^ 2 - 2 * (q : ℝ) * (f ω * g ω) + (q : ℝ) ^ 2 * g ω ^ 2
      nlinarith [sq_nonneg (f ω - (q : ℝ) * g ω)]
    -- linearity of the conditional expectation
    have e_add : μ[fun ω => f ω ^ 2 - 2 * (q : ℝ) * (f ω * g ω) + (q : ℝ) ^ 2 * g ω ^ 2 | m]
        =ᵐ[μ] fun ω => μ[fun ω => f ω ^ 2 - 2 * (q : ℝ) * (f ω * g ω) | m] ω
          + μ[fun ω => (q : ℝ) ^ 2 * g ω ^ 2 | m] ω := by
      filter_upwards [condExp_add hfs ht m] with ω hω; simpa using! hω
    have e_sub : μ[fun ω => f ω ^ 2 - 2 * (q : ℝ) * (f ω * g ω) | m]
        =ᵐ[μ] fun ω => μ[fun ω => f ω ^ 2 | m] ω
          - μ[fun ω => 2 * (q : ℝ) * (f ω * g ω) | m] ω := by
      filter_upwards [condExp_sub hf2 hs m] with ω hω; simpa using! hω
    have e_smul1 : μ[fun ω => 2 * (q : ℝ) * (f ω * g ω) | m]
        =ᵐ[μ] fun ω => 2 * (q : ℝ) * μ[fun ω => f ω * g ω | m] ω := by
      filter_upwards [condExp_smul (2 * (q : ℝ)) (fun ω => f ω * g ω) m] with ω hω
      simpa [smul_eq_mul] using! hω
    have e_smul2 : μ[fun ω => (q : ℝ) ^ 2 * g ω ^ 2 | m]
        =ᵐ[μ] fun ω => (q : ℝ) ^ 2 * μ[fun ω => g ω ^ 2 | m] ω := by
      filter_upwards [condExp_smul ((q : ℝ) ^ 2) (fun ω => g ω ^ 2) m] with ω hω
      simpa [smul_eq_mul] using! hω
    have hexp : μ[fun ω => f ω ^ 2 - 2 * (q : ℝ) * (f ω * g ω) + (q : ℝ) ^ 2 * g ω ^ 2 | m]
        =ᵐ[μ] fun ω => μ[fun ω => f ω ^ 2 | m] ω
          - 2 * (q : ℝ) * μ[fun ω => f ω * g ω | m] ω
          + (q : ℝ) ^ 2 * μ[fun ω => g ω ^ 2 | m] ω := by
      filter_upwards [e_add, e_sub, e_smul1, e_smul2] with ω h1 h2 h3 h4
      rw [h1, h2, h3, h4]
    filter_upwards [hnn, hexp] with ω hn he
    rw [he] at hn; simpa using hn
  -- combine over all rationals
  have hall : ∀ᵐ ω ∂μ, ∀ q : ℚ, (0 : ℝ) ≤
      μ[fun ω => f ω ^ 2 | m] ω - 2 * (q : ℝ) * μ[fun ω => f ω * g ω | m] ω
        + (q : ℝ) ^ 2 * μ[fun ω => g ω ^ 2 | m] ω := ae_all_iff.mpr hstep
  have hCnn : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ μ[fun ω => g ω ^ 2 | m] ω := by
    filter_upwards [condExp_nonneg (m := m)
      (show (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => g ω ^ 2 from
        Eventually.of_forall fun ω => sq_nonneg (g ω))] with ω hω
    exact hω
  filter_upwards [hall, hCnn] with ω hq hc
  exact discrim_of_rat_nonneg hc hq

/-- **Conditional support lemma.** If `f ≥ 0` a.e. and `E[f | m] = 0` a.e.
on an `m`-measurable set `G`, then `f = 0` a.e. on `G`. -/
theorem ae_eq_zero_on_of_condExp_eq_zero
    (hm : m ≤ m0) {μ : Measure Ω} [SigmaFinite (μ.trim hm)]
    {f : Ω → ℝ} (hf_int : Integrable f μ) (hf_nn : 0 ≤ᵐ[μ] f)
    {G : Set Ω} (hG : MeasurableSet[m] G)
    (h0 : ∀ᵐ ω ∂μ.restrict G, μ[f | m] ω = 0) :
    ∀ᵐ ω ∂μ.restrict G, f ω = 0 := by
  -- `∫_G f = ∫_G E[f|m] = 0`, and `f ≥ 0` a.e. on `G`, so `f = 0` a.e. on `G`.
  have hint : ∫ x in G, f x ∂μ = 0 := by
    rw [← setIntegral_condExp hm hf_int hG]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0] with ω hω; simpa using hω
  have hnn : 0 ≤ᵐ[μ.restrict G] f := ae_restrict_of_ae hf_nn
  have hi : Integrable f (μ.restrict G) := hf_int.restrict
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hint] with ω hω
  simpa using hω

end AsymptoticStatistics.ForMathlib.CondExpCauchySchwarz
