module
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.LocalExtr

@[expose] public section

/-!
# Gradient at an extremum

Theorem-agnostic brick (`ForMathlib` layer): at an interior local (hence at a
global) minimizer of a differentiable function, the gradient vanishes.

This bridges Mathlib's Fermat-type `IsLocalMin.fderiv_eq_zero` to the
Riesz-representation `gradient`, giving the `∇f(x*) = 0` fact used in the
unconstrained gradient-descent analysis (Junwei Lu, *Big Data Analysis*,
Springer Nature Switzerland, 2025 (ISBN 978-3-032-03160-0), Ch. 13
(Gradient Descent), §13.1; the gradient-vanishing brick behind
Theorem 13.1 (Convergence of Gradient Descent)).
-/

namespace StatLean.Optimization

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- At a global minimizer of a differentiable function, the gradient is zero. -/
theorem gradient_eq_zero_of_forall_le
    {f : E → ℝ} (hdiff : Differentiable ℝ f) {x : E} (hmin : ∀ y, f x ≤ f y) :
    gradient f x = 0 := by
  have hMinOn : IsMinOn f Set.univ x := isMinOn_univ_iff.mpr hmin
  have hLocalMin : IsLocalMin f x := hMinOn.isLocalMin Filter.univ_mem
  have hfderiv : fderiv ℝ f x = 0 := hLocalMin.fderiv_eq_zero
  have hfd : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) (gradient f x)) x :=
    hasGradientAt_iff_hasFDerivAt.mp (hdiff x).hasGradientAt
  have hEq : (InnerProductSpace.toDual ℝ E) (gradient f x) = 0 := by
    rw [← hfd.fderiv, hfderiv]
  exact (InnerProductSpace.toDual ℝ E).map_eq_zero_iff.mp hEq

end StatLean.Optimization
