module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-!
Convolution extraction from a characteristic-function factorisation.

Given a probability measure `L` on `ℝ` and a candidate "mixing" probability
measure `M` on `ℝ` whose characteristic function `charFun M` factorises
`charFun L` against the Gaussian factor `charFun (gaussianReal 0 σ²)`, we
recover the measure-level convolution identity `L = N(0, σ²) ⋆ M`.

This packages the standard "char-fn factorisation → measure factorisation"
step: the convolution of measures becomes the product of their
characteristic functions (`charFun_conv`), and a finite measure on `ℝ` is
determined by its characteristic function (`Measure.ext_of_charFun`).

Used by `AsymptoticStatistics.LowerBounds.LeCamThirdAndCharFn` to discharge
the post-identity-theorem "extract `M`" step in `lecam_third_convolution`.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal

namespace AsymptoticStatistics.ForMathlib.CharFnConvolution

/-- *Convolution extraction from a characteristic-function factorisation.*

If a probability measure `L` on `ℝ` and a probability measure `M` on `ℝ`
satisfy the pointwise characteristic-function identity
  `charFun L u = charFun (N(0, σ²)) u · charFun M u`,
then `L = N(0, σ²) ⋆ M` as measures.

This is the textbook "char-fn factorisation determines the measure"
step. The proof uses `Measure.ext_of_charFun` (a finite measure on `ℝ`
is determined by its char-fn) plus `charFun_conv` (the char-fn of a
convolution is the product of the char-fns).

In the Le Cam third lemma synthesis (vdV §25.3), `M` is the law of
`S − A_m Δ` produced by Bochner's theorem (or directly from the limit
random variable), and the user discharges the char-fn identity by
evaluating the joint MGF identity at imaginary arguments. -/
theorem convolution_extraction_from_charFn
    (L M : Measure ℝ) [IsProbabilityMeasure L] [IsProbabilityMeasure M]
    (σSq : ℝ≥0)
    (hCharFn : ∀ u : ℝ,
      charFun L u =
        charFun (ProbabilityTheory.gaussianReal 0 σSq) u * charFun M u) :
    L = (ProbabilityTheory.gaussianReal 0 σSq) ∗ M := by
  refine Measure.ext_of_charFun ?_
  ext u
  rw [charFun_conv]
  exact hCharFn u

end AsymptoticStatistics.ForMathlib.CharFnConvolution
