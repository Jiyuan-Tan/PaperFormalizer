module
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

@[expose] public section

/-!
# Fourier coefficients of finite measures on the circle `AddCircle (2π)`

For a finite measure `F` on `AddCircle (2π)` we define
`measureFourierCoeff F n = ∫ e^{inz} dF(z)` — with Mathlib's `fourier n` at `T = 2π`
being exactly `z ↦ e^{inz}`, so the book's transform convention
`γ(τ) = ∫_{−π}^{π} e^{iτω} dF(ω)` (FY eqs. (2.33)–(2.35), no `2π` factor in the forward
transform) is `measureFourierCoeff F τ` verbatim.

Bricks stated here:

* mass and norm bounds (`measureFourierCoeff_zero`, `norm_measureFourierCoeff_le`);
* **uniqueness**: a finite measure on the circle is determined by its Fourier
  coefficients (`ext_of_measureFourierCoeff`) — the uniqueness half that FY Theorem 2.10
  leaves unstated; via Stone–Weierstrass density of trigonometric polynomials
  (`span_fourier_closure_eq_top`);
* **weak-convergence of coefficients**: coefficients pass to weak limits of probability
  measures (`tendsto_measureFourierCoeff_of_tendsto`) — the Helly–Bray step of FY §2.7.4;
* negation invariance (`NegInvariant`) and its coefficient symmetry — the "symmetric
  distribution" bookkeeping of FY Theorem 2.10.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.1–§2.3.2
(eqs. (2.33)–(2.35)) and §2.7.4 (pp. 80–81). (`FY §2.3.2 Thm 2.10; §2.7.4`.)

**Proof formalization notes.** The interval `[−π, π]` with endpoints identified *is*
`AddCircle (2π)`; atoms at `±π` (a real possibility for spectral distributions, e.g.
white-noise-with-period-2 components) are handled by the circle picture with no endpoint
conventions. Uniqueness reduces to equality of the integrals of all continuous functions
(Riesz-type argument via density of `span (fourier '' univ)` in `C(AddCircle (2π), ℂ)`).

**Bibliographic comments.** That trigonometric moments determine a measure on the circle
is classical (Herglotz 1911, F. Riesz); the weak-convergence step is the Helly–Bray
theorem (E. Helly 1912; H. E. Bray 1919).
-/

open MeasureTheory Filter
open scoped Real Topology

namespace StatLean.TimeSeries

/-- **Fourier coefficient of a measure** on `AddCircle (2π)`:
`measureFourierCoeff F n = ∫ e^{inz} dF(z)` (FY forward-transform convention,
eqs. (2.33)–(2.35): no `2π` factor). -/
noncomputable def measureFourierCoeff (F : Measure (AddCircle (2 * π))) (n : ℤ) : ℂ :=
  ∫ z, fourier n z ∂F

/-- The zeroth coefficient is the total mass. -/
theorem measureFourierCoeff_zero (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F] :
    measureFourierCoeff F 0 = ((F Set.univ).toReal : ℂ) := by
  have h1 : ∀ z : AddCircle (2 * π), fourier (T := 2 * π) 0 z = ((1 : ℝ) : ℂ) := by
    intro z; rw [fourier_zero]; norm_num
  rw [measureFourierCoeff, integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_complex_ofReal, integral_const, smul_eq_mul, mul_one]
  rfl

/-- Coefficients are bounded by the total mass (`‖fourier n z‖ = 1`). -/
theorem norm_measureFourierCoeff_le (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (n : ℤ) : ‖measureFourierCoeff F n‖ ≤ (F Set.univ).toReal := by
  have hnorm : ∀ z : AddCircle (2 * π), ‖fourier (T := 2 * π) n z‖ = 1 := by
    intro z; rw [fourier_apply]; exact Circle.norm_coe _
  calc ‖measureFourierCoeff F n‖ ≤ ∫ z, ‖fourier (T := 2 * π) n z‖ ∂F :=
        norm_integral_le_integral_norm _
    _ = ∫ _z : AddCircle (2 * π), (1 : ℝ) ∂F :=
        integral_congr_ae (Filter.Eventually.of_forall hnorm)
    _ = (F Set.univ).toReal := by rw [integral_const, smul_eq_mul, mul_one]; rfl

/-- **Uniqueness**: a finite measure on the circle is determined by its Fourier
coefficients. (The uniqueness half of the Herglotz correspondence, which FY Theorem 2.10
does not state; needed to speak of *the* spectral distribution.) -/
theorem ext_of_measureFourierCoeff (F G : Measure (AddCircle (2 * π)))
    [IsFiniteMeasure F] [IsFiniteMeasure G]
    (h : ∀ n, measureFourierCoeff F n = measureFourierCoeff G n) : F = G := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  -- every continuous function on the (compact) circle is bounded, and bounded continuous
  -- functions are integrable against a finite measure
  have hmk : ∀ φ : C(AddCircle (2 * π), ℂ),
      BoundedContinuousFunction.toContinuousMapStarₐ ℂ
        (BoundedContinuousFunction.mkOfCompact φ) = φ := by
    intro φ; ext x; rfl
  have hintF : ∀ φ : C(AddCircle (2 * π), ℂ), Integrable (fun z => φ z) F := fun φ =>
    (BoundedContinuousFunction.mkOfCompact φ).integrable F
  have hintG : ∀ φ : C(AddCircle (2 * π), ℂ), Integrable (fun z => φ z) G := fun φ =>
    (BoundedContinuousFunction.mkOfCompact φ).integrable G
  -- the hypothesis propagates from the monomials `fourier n` to their linear span, by
  -- linearity of the integral
  have key : ∀ φ ∈ Submodule.span ℂ (Set.range (fourier (T := 2 * π))),
      ∫ z, φ z ∂F = ∫ z, φ z ∂G := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨n, rfl⟩ := hx; exact h n
    | zero => simp
    | add x y _ _ hx hy =>
        have e1 : ∫ z, (x + y) z ∂F = (∫ z, x z ∂F) + ∫ z, y z ∂F := by
          simp only [ContinuousMap.add_apply]; exact integral_add (hintF x) (hintF y)
        have e2 : ∫ z, (x + y) z ∂G = (∫ z, x z ∂G) + ∫ z, y z ∂G := by
          simp only [ContinuousMap.add_apply]; exact integral_add (hintG x) (hintG y)
        rw [e1, e2, hx, hy]
    | smul c x _ hx =>
        have e1 : ∫ z, (c • x) z ∂F = c • ∫ z, x z ∂F := by
          simp only [ContinuousMap.smul_apply]; exact integral_smul c _
        have e2 : ∫ z, (c • x) z ∂G = c • ∫ z, x z ∂G := by
          simp only [ContinuousMap.smul_apply]; exact integral_smul c _
        rw [e1, e2, hx]
  -- transport Mathlib's `fourierSubalgebra` (which separates points, Stone–Weierstrass) to a
  -- star subalgebra of the *bounded* continuous functions, as the extensionality engine wants
  set A : StarSubalgebra ℂ (BoundedContinuousFunction (AddCircle (2 * π)) ℂ) :=
    (fourierSubalgebra (T := 2 * π)).comap
      (BoundedContinuousFunction.toContinuousMapStarₐ ℂ) with hAdef
  have hmemA : ∀ φ : C(AddCircle (2 * π), ℂ), φ ∈ fourierSubalgebra (T := 2 * π) →
      φ ∈ A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ) := fun φ hφ =>
    ⟨BoundedContinuousFunction.mkOfCompact φ, by simpa [hAdef, hmk φ] using hφ, hmk φ⟩
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hfxy⟩ := fourierSubalgebra_separatesPoints (T := 2 * π) hxy
    obtain ⟨φ, hφ, rfl⟩ := hf
    exact ⟨_, ⟨φ, hmemA φ hφ, rfl⟩, hfxy⟩
  refine ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep ?_
  intro g hg
  have hgmem : BoundedContinuousFunction.toContinuousMapStarₐ ℂ g
      ∈ fourierSubalgebra (T := 2 * π) := hg
  have hspan : (BoundedContinuousFunction.toContinuousMapStarₐ ℂ g)
      ∈ Submodule.span ℂ (Set.range (fourier (T := 2 * π))) := by
    rw [← fourierSubalgebra_coe]
    exact hgmem
  exact key _ hspan

/-- **Helly–Bray step**: Fourier coefficients pass to weak limits of probability
measures on the circle. -/
theorem tendsto_measureFourierCoeff_of_tendsto
    {Fs : ℕ → ProbabilityMeasure (AddCircle (2 * π))}
    {F : ProbabilityMeasure (AddCircle (2 * π))}
    (h : Tendsto Fs atTop (𝓝 F)) (n : ℤ) :
    Tendsto (fun k => measureFourierCoeff (Fs k : Measure (AddCircle (2 * π))) n) atTop
      (𝓝 (measureFourierCoeff (F : Measure (AddCircle (2 * π))) n)) := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h
    (BoundedContinuousFunction.mkOfCompact (fourier (T := 2 * π) n))

/-- A measure on the circle is **negation-invariant** ("symmetric" in FY Theorem 2.10's
sense) when it is preserved by `z ↦ −z`. -/
def NegInvariant (F : Measure (AddCircle (2 * π))) : Prop :=
  F.map (fun z => -z) = F

/-- For a negation-invariant finite measure the Fourier coefficients are even in `n`. -/
theorem measureFourierCoeff_neg (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (hF : NegInvariant F) (n : ℤ) :
    measureFourierCoeff F (-n) = measureFourierCoeff F n := by
  have hpt : ∀ z : AddCircle (2 * π),
      fourier (T := 2 * π) (-n) z = fourier (T := 2 * π) n (-z) := by
    intro z
    rw [fourier_apply, fourier_apply, neg_zsmul, zsmul_neg]
  rw [measureFourierCoeff, measureFourierCoeff]
  conv_rhs => rw [← hF]
  rw [integral_map (measurable_neg.aemeasurable)
    ((map_continuous (fourier (T := 2 * π) n)).aestronglyMeasurable)]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- For a negation-invariant finite measure the Fourier coefficients are real. -/
theorem measureFourierCoeff_im (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (hF : NegInvariant F) (n : ℤ) :
    (measureFourierCoeff F n).im = 0 := by
  refine Complex.conj_eq_iff_im.mp ?_
  have hconj : (starRingEnd ℂ) (measureFourierCoeff F n) = measureFourierCoeff F (-n) := by
    have h1 : (starRingEnd ℂ) (∫ z, fourier (T := 2 * π) n z ∂F)
        = ∫ z, (starRingEnd ℂ) (fourier (T := 2 * π) n z) ∂F := integral_conj.symm
    rw [measureFourierCoeff, measureFourierCoeff, h1]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun z => fourier_neg)).symm
  rw [hconj, measureFourierCoeff_neg F hF n]

end StatLean.TimeSeries
