module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The Laplace (double-exponential) distribution `Laplace(0, b)`

The centered Laplace distribution with scale `b > 0`, a standard probability brick that the pinned
Mathlib lacks (it has the Gaussian and Gamma laws but not the double-exponential). Density
`f(x) = (2b)⁻¹ exp(−|x|/b)`, measure `Laplace(0, b) = volume.withDensity f`, and the symmetric-tail
identity `P(|X| > δ) = exp(−δ/b)` used to compute the Dirichlet–Laplace marginal tail.

**Reference.** Standard Laplace-distribution facts (e.g. Kotz–Kozubowski–Podgórski, *The Laplace
Distribution and Generalizations*, Birkhäuser, 2001, §2.1). A **standard Laplace-distribution brick**:
it carries no Dirichlet–Laplace-specific content of its own, but is consumed by the scale mixture
`θ | ψ ~ Laplace(ψ)`, `ψ ~ Gamma(a, 1/2)` of Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace
priors for optimal shrinkage* (arXiv:1401.5398), eq. (10).

**Proof formalization notes.** `laplacePDFReal` keeps the raw prefactor `(2b)⁻¹`, so for `b ≤ 0` the
prefactor is `≤ 0` and `ENNReal.ofReal` collapses the density to `0`; hence `laplaceMeasure b = 0`
for `b ≤ 0` (a junk guard mirroring the Gaussian/Gamma conventions, keeping the object usable at
degenerate scale indices). The total-mass and tail computations reduce to `∫ exp(−x/b) dx` over a
half-line; the **tail identity** `laplaceMeasure b {δ < |x|} = exp(−δ/b)` is the Laplace
conditional-tail formula — the two symmetric exponential tails each contribute `(1/2)exp(−δ/b)`.

**Bibliographic comments.** The double-exponential law is Laplace's *first* law of errors (1774),
predating the Gaussian second law; in Bayesian shrinkage it is the prior behind the Bayesian lasso
(Park–Casella, *J. Amer. Statist. Assoc.* 103 (2008), 681–686).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- **Centered Laplace density** `f(x) = (2b)⁻¹ exp(−|x|/b)` (scale `b`, location `0`), as a real
number. For `b ≤ 0` the prefactor `(2b)⁻¹` is `≤ 0`, so downstream `ENNReal.ofReal` reads the density
as `0` (junk guard; all content lemmas assume `0 < b`). -/
noncomputable def laplacePDFReal (b x : ℝ) : ℝ := (2 * b)⁻¹ * Real.exp (-|x| / b)

/-- **Centered Laplace density** as an extended nonnegative real, `ENNReal.ofReal` of
`laplacePDFReal`. Equals `0` for `b ≤ 0` (nonpositive prefactor). -/
noncomputable def laplacePDF (b x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (laplacePDFReal b x)

/-- The Laplace density in `x` is measurable, at every fixed scale `b`. -/
lemma measurable_laplacePDF (b : ℝ) : Measurable (laplacePDF b) := by
  unfold laplacePDF laplacePDFReal
  fun_prop

/-- **Joint measurability** of `(b, x) ↦ laplacePDF b x`, the input needed to form the
Gamma–Laplace scale-mixture `bind` (see `Measure.bind_withDensity`). -/
lemma measurable_laplacePDF_uncurry : Measurable (Function.uncurry laplacePDF) := by
  unfold Function.uncurry laplacePDF laplacePDFReal
  fun_prop

/-- Right-tail half-integral: `∫⁻_{Ioi c} (2b)⁻¹ e^{−|x|/b} = (1/2) e^{−c/b}` for `c ≥ 0` (on
`Ioi c` we have `|x| = x`, and `∫_{Ioi c} e^{−x/b} = b e^{−c/b}`). -/
private theorem lintegral_laplacePDF_Ioi_ge {b : ℝ} (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ x in Set.Ioi c, laplacePDF b x ∂volume = ENNReal.ofReal (1 / 2 * Real.exp (-c / b)) := by
  have hne : -b⁻¹ < 0 := neg_lt_zero.mpr (by positivity)
  have hcong : Set.EqOn (laplacePDF b)
      (fun x => ENNReal.ofReal ((2 * b)⁻¹ * Real.exp (-b⁻¹ * x))) (Set.Ioi c) := by
    intro x hx
    have hxpos : 0 < x := lt_of_le_of_lt hc hx
    simp only [laplacePDF, laplacePDFReal, abs_of_pos hxpos]
    rw [show (-x / b : ℝ) = -b⁻¹ * x from by ring]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcong,
    ← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_exp_mul_Ioi hne c).const_mul _)
      (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  rw [integral_const_mul, integral_exp_mul_Ioi hne c,
    show (-b⁻¹ * c : ℝ) = -c / b from by ring]
  field_simp

/-- Left-tail half-integral: `∫⁻_{Iic c} (2b)⁻¹ e^{−|x|/b} = (1/2) e^{c/b}` for `c ≤ 0` (on
`Iic c` we have `|x| = -x`, and `∫_{Iic c} e^{x/b} = b e^{c/b}`). -/
private theorem lintegral_laplacePDF_Iic_le {b : ℝ} (hb : 0 < b) {c : ℝ} (hc : c ≤ 0) :
    ∫⁻ x in Set.Iic c, laplacePDF b x ∂volume = ENNReal.ofReal (1 / 2 * Real.exp (c / b)) := by
  have hpos : (0 : ℝ) < b⁻¹ := by positivity
  have hcong : Set.EqOn (laplacePDF b)
      (fun x => ENNReal.ofReal ((2 * b)⁻¹ * Real.exp (b⁻¹ * x))) (Set.Iic c) := by
    intro x hx
    have hxnp : x ≤ 0 := le_trans hx hc
    simp only [laplacePDF, laplacePDFReal, abs_of_nonpos hxnp]
    rw [show (-(-x) / b : ℝ) = b⁻¹ * x from by ring]
  rw [setLIntegral_congr_fun measurableSet_Iic hcong,
    ← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_exp_mul_Iic hpos c).const_mul _)
      (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  rw [integral_const_mul, integral_exp_mul_Iic hpos c,
    show (b⁻¹ * c : ℝ) = c / b from by ring]
  field_simp

/-- The Laplace density integrates to `1` against Lebesgue measure (total probability mass), for
positive scale. -/
lemma lintegral_laplacePDF_eq_one {b : ℝ}
    -- LEAN-ONLY: positive scale; the normalization (2b)⁻¹ gives total mass 1 only for b > 0
    (hb : 0 < b) :
    ∫⁻ x, laplacePDF b x ∂volume = 1 := by
  rw [← lintegral_add_compl (laplacePDF b) (measurableSet_Iic (a := (0 : ℝ))), Set.compl_Iic,
    lintegral_laplacePDF_Iic_le hb (le_refl 0), lintegral_laplacePDF_Ioi_ge hb (le_refl 0)]
  rw [show (0 : ℝ) / b = 0 by simp, show (-0 : ℝ) / b = 0 by simp, Real.exp_zero,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- **Laplace measure** `Laplace(0, b) = volume.withDensity ((2b)⁻¹ exp(−|·|/b))`. For `b ≤ 0` the
density vanishes, so this is the zero measure (junk guard; it is a probability measure iff `0 < b`). -/
noncomputable def laplaceMeasure (b : ℝ) : Measure ℝ := volume.withDensity (laplacePDF b)

/-- `Laplace(0, b)` is a probability measure for positive scale. -/
theorem isProbabilityMeasure_laplaceMeasure {b : ℝ}
    -- LEAN-ONLY: positive scale; Laplace(0,b) is a probability measure only for b > 0
    (hb : 0 < b) :
    IsProbabilityMeasure (laplaceMeasure b) := by
  constructor
  rw [laplaceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_laplacePDF_eq_one hb]

/-- For nonpositive scale the Laplace measure degenerates to `0` (the density is identically `0`). -/
theorem laplaceMeasure_of_nonpos {b : ℝ}
    -- LEAN-ONLY: nonpositive scale is the junk branch; the density collapses to 0
    (hb : b ≤ 0) :
    laplaceMeasure b = 0 := by
  rw [laplaceMeasure]
  have hz : laplacePDF b = 0 := by
    funext x
    simp only [laplacePDF, laplacePDFReal, Pi.zero_apply, ENNReal.ofReal_eq_zero]
    have h2b : (2 * b)⁻¹ ≤ 0 := inv_nonpos.mpr (by linarith)
    exact mul_nonpos_of_nonpos_of_nonneg h2b (Real.exp_pos _).le
  rw [hz, withDensity_zero]

/-- **Laplace tail identity** `P(|X| > δ) = exp(−δ/b)` — the symmetric double-exponential tail, for
positive scale `b` and nonnegative threshold `δ`. This is the marginal-tail input to the
Dirichlet–Laplace mixture analysis. -/
theorem laplaceMeasure_abs_gt {b δ : ℝ}
    -- LEAN-ONLY: positive scale; the tail identity holds for the genuine Laplace law (b > 0)
    (hb : 0 < b)
    -- LEAN-ONLY: nonnegative threshold; for δ < 0 the event is all of ℝ and exp(−δ/b) > 1 fails
    (hδ : 0 ≤ δ) :
    laplaceMeasure b {x : ℝ | δ < |x|} = ENNReal.ofReal (Real.exp (-δ / b)) := by
  have hmeas : MeasurableSet {x : ℝ | δ < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hset : {x : ℝ | δ < |x|} = Set.Iio (-δ) ∪ Set.Ioi δ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  rw [laplaceMeasure, withDensity_apply _ hmeas, hset,
    lintegral_union measurableSet_Ioi
      ((Set.Iic_disjoint_Ioi (by linarith : (-δ : ℝ) ≤ δ)).mono Set.Iio_subset_Iic_self le_rfl),
    setLIntegral_congr (Iio_ae_eq_Iic (a := (-δ : ℝ))),
    lintegral_laplacePDF_Iic_le hb (by linarith : (-δ : ℝ) ≤ 0),
    lintegral_laplacePDF_Ioi_ge hb hδ,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring_nf

/-- Measurability of `b ↦ laplaceMeasure b s` for a fixed measurable set `s` (kernel measurability,
needed to form the Gamma–Laplace scale-mixture `bind`). -/
lemma measurable_laplaceMeasure_apply {s : Set ℝ}
    -- LEAN-ONLY: the evaluation set is measurable (regularity)
    (hs : MeasurableSet s) :
    Measurable (fun b => laplaceMeasure b s) := by
  have hfun : (fun b => laplaceMeasure b s) = fun b => ∫⁻ x in s, laplacePDF b x ∂volume := by
    funext b; rw [laplaceMeasure, withDensity_apply _ hs]
  rw [hfun]
  exact Measurable.lintegral_prod_right (ν := volume.restrict s) measurable_laplacePDF_uncurry

end StatLean.Bayesian
