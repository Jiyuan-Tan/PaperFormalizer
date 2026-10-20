module
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# L-smoothness (quadratic upper bound)

A function $f : E \to \mathbb{R}$ on a real inner product space is **$L$-smooth** if
it lies below its quadratic model around every point: for all $x, y$,
$$ f(y) \;\le\; f(x) + \langle \nabla f(x),\, y - x\rangle + \frac{L}{2}\,\lVert x - y\rVert^2. $$
For a continuously differentiable function this is equivalent to the gradient
$\nabla f$ being $L$-Lipschitz; here we take the quadratic upper bound itself as
the definition, since that is exactly the inequality consumed by the descent
analyses (gradient descent, Frank–Wolfe, proximal gradient).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 13 (Gradient Descent), §13.1 (Gradient Descent),
Definition 13.1 (L-Smooth). The book states the
quadratic upper bound as the primary definition and records its equivalence, for
$C^1$ functions, with $L$-Lipschitz continuity of the gradient.

**Proof formalization notes.** This is a concept-layer definition, so there is no
proof to outline. Two formalization choices to record:

* We take the quadratic upper bound as *the* definition rather than the
  $L$-Lipschitz-gradient form, because it is the inequality directly consumed by
  the descent analyses, so no separate "descent lemma" is needed to derive it.
* `gradient f x` is Mathlib's Riesz-representation gradient, which is `0` wherever
  `f` is not differentiable. Downstream theorems therefore carry differentiability
  of `f` explicitly whenever they need `gradient f x` to be the genuine derivative.

**Bibliographic comments.** $L$-smoothness via the quadratic upper bound is
classical folklore of smooth convex optimization with no single seminal origin;
the modern treatment is Y. Nesterov, *Lectures on Convex Optimization*,
2nd ed., Springer, 2018 (and the earlier *Introductory Lectures on Convex
Optimization*, Kluwer, 2004), where the equivalence between Lipschitz-continuous
gradient and the quadratic bound appears as the standard "descent lemma."
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `IsLSmooth f L`: the function `f : E → ℝ` is `L`-smooth, i.e. it lies below
the quadratic model around every point,
`f y ≤ f x + ⟪∇f x, y - x⟫ + (L/2)‖x - y‖²` for all `x y` (Lu-BDA §13.1,
Definition 13.1 (L-Smooth)). `gradient f x` is the Riesz gradient. -/
def IsLSmooth (f : E → ℝ) (L : ℝ) : Prop :=
  ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + (L / 2) * ‖x - y‖ ^ 2

end StatLean.Optimization
