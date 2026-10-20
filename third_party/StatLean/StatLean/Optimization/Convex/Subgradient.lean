module
public import StatLean.Optimization.Convex.Defs
public import StatLean.Optimization.ForMathlib.FirstOrderConvex

@[expose] public section

/-!
# Subgradient API: the gradient is a subgradient

Let $f : E \to \mathbb{R}$ be a convex, differentiable function on a real
inner-product space $E$. Then at every point $x$ the gradient $\nabla f(x)$ is a
subgradient of $f$ at $x$; that is, $\nabla f(x) \in \partial f(x)$, where the
subdifferential is the set of all vectors $g$ satisfying
$$ f(y) \ \ge\ f(x) + \langle g,\, y - x\rangle \qquad \text{for all } y \in E. $$
Equivalently, the gradient witnesses the supporting-hyperplane inequality that
defines a subgradient.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland,
2025 (ISBN 978-3-032-03160-0), Chapter 12 (Convexity and Subgradient), §12.2,
Definition 12.3 (Subgradient) ("When $f$ is differentiable and convex,
$\nabla f(x) \in \partial f(x)$").

**Proof formalization notes.** Immediate from the first-order convexity
inequality: for convex differentiable $f$ one has
$\langle \nabla f(x),\, y - x\rangle \le f(y) - f(x)$ (the lemma
`inner_gradient_le_sub_of_convexOn`), and rearranging gives the subgradient
inequality $f(y) \ge f(x) + \langle \nabla f(x),\, y - x\rangle$, which is the
membership condition `mem_subdifferential` unfolds to. No constants or extra
hypotheses are added relative to the book statement; convexity is taken on
`Set.univ` (the whole space).

**Bibliographic comments.** This is classical, folklore convex analysis with no
single seminal origin. The standard reference is R. T. Rockafellar, *Convex
Analysis*, Princeton University Press, 1970 — the equivalence between
differentiability and the gradient being the unique subgradient is Theorem 25.1
there, building on the basic subgradient inequality of §23. The result is
also standard material in, e.g., Boyd & Vandenberghe, *Convex
Optimization* (Cambridge, 2004), §3.1.3.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- For convex differentiable `f`, the gradient is a subgradient:
`∇f x ∈ ∂f x` (Lu-BDA §12.2, Definition 12.3). -/
theorem gradient_mem_subdifferential
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f) (x : E) :
    gradient f x ∈ subdifferential f x := by
  rw [mem_subdifferential]
  intro y
  have h := inner_gradient_le_sub_of_convexOn hf hdiff x y
  linarith

end StatLean.Optimization
