module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Function

@[expose] public section

/-!
# Subgradient and subdifferential

Concept-layer definitions for the `Optimization` area. A vector $g$ is a
**subgradient** of a function $f : E \to \mathbb{R}$ at a point $x$ if the
supporting-hyperplane inequality
$$ f(y) - f(x) \ge \langle g,\, y - x \rangle \qquad \text{for all } y \in E $$
holds. The **subdifferential** $\partial f(x)$ is the set of all such
subgradients $g$. For a differentiable convex $f$ the gradient $\nabla f(x)$ is
the canonical element of $\partial f(x)$; for nonconvex $f$ the set may be empty,
while for convex $f$ it is nonempty.

The book states the definition over a convex domain $\mathcal{X}$; we formalize
the unconstrained case $\mathcal{X} = E$ (the whole inner product space), which
is what the targeted results (local-minimum-is-global, the proximal pillar
lemma) require.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 12 (Convexity and Subgradient), §12.2
(Subgradient), Definition 12.3 (Subgradient).

**Proof formalization notes.** These are definitions, so there is no proof
obligation here. Convexity of sets/functions is reused directly from Mathlib
(`Convex`, `ConvexOn`); this file only adds the subgradient notion, which
Mathlib lacks for multivariate functions. `IsSubgradient f x g` packages the
defining inequality; `subdifferential f x` is its comprehension set, with
`mem_subdifferential` the definitional membership `simp` lemma. The Lean
inequality is stated as `⟪g, y - x⟫_ℝ ≤ f y - f x`, which is exactly the book's
$f(y) - f(x) \ge \langle g, y - x\rangle$.

**Bibliographic comments.** The subgradient and subdifferential of a convex
function are foundational notions of convex analysis with no single seminal
origin; they are folklore traceable to the development of
convex analysis in the 1960s. The standard reference is R. T. Rockafellar,
*Convex Analysis*, Princeton Mathematical Series 28, Princeton University Press,
1970 (see §23, "Subgradients"), which fixed the now-standard definition
$\partial f(x) = \{\, g : f(y) \ge f(x) + \langle g, y - x\rangle\ \forall y\,\}$
and the inclusion $\nabla f(x) \in \partial f(x)$ in the differentiable case.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `IsSubgradient f x g`: `g` is a subgradient of `f : E → ℝ` at `x`, i.e. the
supporting-hyperplane inequality `f y - f x ≥ ⟪g, y - x⟫` holds for every `y`
(Lu-BDA §12.2, Definition 12.3 (Subgradient), specialized to the unconstrained domain `𝒳 = E`).
For differentiable convex `f` the gradient `∇f x` is the canonical subgradient. -/
def IsSubgradient (f : E → ℝ) (x g : E) : Prop :=
  ∀ y, ⟪g, y - x⟫_ℝ ≤ f y - f x

/-- The subdifferential `∂f(x)`: the set of all subgradients of `f` at `x`
(Lu-BDA §12.2, Definition 12.3 (Subgradient)). May be empty for nonconvex `f`;
for convex `f` it is nonempty. -/
def subdifferential (f : E → ℝ) (x : E) : Set E :=
  {g | IsSubgradient f x g}

@[simp] theorem mem_subdifferential {f : E → ℝ} {x g : E} :
    g ∈ subdifferential f x ↔ IsSubgradient f x g := Iff.rfl

end StatLean.Optimization
