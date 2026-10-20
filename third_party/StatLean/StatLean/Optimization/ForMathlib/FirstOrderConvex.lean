module
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.AffineMap

@[expose] public section

/-!
# First-order characterization of convexity (gradient inequality)

Theorem-agnostic brick (`ForMathlib` layer): a convex differentiable function on
a real inner-product space lies above each of its tangent hyperplanes. For all
points $x, y$,
$$ f(x) + \langle \nabla f(x),\, y - x\rangle \le f(y). $$
Geometrically, the first-order Taylor approximation at $x$ underestimates $f$
everywhere — the graph of $f$ never dips below any of its tangents. This is the
differentiable specialization of the subgradient inequality: when $f$ is
differentiable, the unique subgradient at $x$ is the gradient $\nabla f(x)$.

The Lean statement specializes the book's setting to a complete real
inner-product space $E$ and assumes global convexity on the whole space
(`Set.univ`) together with global differentiability of $f$; under these
hypotheses the inequality holds for every pair of points, with no further
regularity conditions or constant adjustments relative to the book.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland,
2025 (ISBN 978-3-032-03160-0), Chapter 12 (Convexity and Subgradient), §12.2,
Definition 12.3 (Subgradient). The book
derives the inequality by taking $\gamma \to 0$ in the convexity inequality
$f(x + \gamma(y - x)) \le (1-\gamma) f(x) + \gamma f(y)$.

**Proof formalization notes.** Mathlib has the 1-D `deriv` version of the
first-order convexity inequality but not the inner-product-space gradient form;
we prove it here for reuse across the gradient-descent, Frank–Wolfe, and proximal
analyses. The proof restricts $f$ to the line through $x$ and $y$ via
$L = \mathrm{lineMap}\,x\,y$ (so $L(0) = x$, $L(1) = y$), notes that $f \circ L$ is
convex on $\mathbb{R}$ (preimage of `univ` under an affine map is `univ`), and
applies the 1-D inequality `ConvexOn.le_slope_of_hasDerivAt`: the derivative of
$f \circ L$ at $0$ is bounded by the slope over $[0,1]$. The chain rule gives
that derivative as $(\mathrm{D}f(x))(y - x)$, the slope equals $f(y) - f(x)$, and
the Riesz bridge `inner_gradient_left` identifies $(\mathrm{D}f(x))(y-x)$ with
$\langle \nabla f(x), y - x\rangle$.

**Bibliographic comments.** This is classical convex-analysis folklore with no
single seminal origin; it predates and underlies the modern theory of
subdifferentials. The standard reference is R. T. Rockafellar, *Convex Analysis*,
Princeton University Press, 1970 — the differentiable case is the specialization
of the subgradient inequality $f(z) \ge f(x) + \langle x^\ast, z - x\rangle$ for
$x^\ast \in \partial f(x)$ (Rockafellar, Thm 23.5 / §23), using that for a
differentiable convex function the subdifferential is the singleton
$\{\nabla f(x)\}$ (Rockafellar, Thm 25.1). The inequality is a staple
appearing in essentially all convex-optimization references (e.g. Boyd &
Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, §3.1.3,
Eq. (3.2)); we do not attribute it to a single research paper.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Gradient inequality for convex differentiable functions:
`f x + ⟪∇f x, y - x⟫ ≤ f y` for all `x y` (Lu-BDA §12.2). -/
theorem inner_gradient_le_sub_of_convexOn
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (x y : E) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  -- Restrict `f` to the line through `x` and `y` via `L = lineMap x y`.
  set L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y with hLdef
  have hL0 : (L : ℝ → E) 0 = x := by rw [hLdef]; exact AffineMap.lineMap_apply_zero x y
  have hL1 : (L : ℝ → E) 1 = y := by rw [hLdef]; exact AffineMap.lineMap_apply_one x y
  -- `f ∘ L` is convex on `Set.univ` (preimage of univ under L is univ).
  have hφconv : ConvexOn ℝ Set.univ (f ∘ ⇑L) := by
    have h : ConvexOn ℝ (⇑L ⁻¹' Set.univ) (f ∘ ⇑L) := ConvexOn.comp_affineMap L hf
    simpa using h
  -- Chain rule: derivative of `L` is `y - x`; derivative of `f ∘ L` at `0` is
  -- `(fderiv ℝ f x) (y - x) = ⟪∇f x, y - x⟫`.
  have hLderiv : HasDerivAt (⇑L : ℝ → E) (y - x) 0 := by
    rw [hLdef]; exact AffineMap.hasDerivAt_lineMap
  have hfderiv : HasFDerivAt f (fderiv ℝ f x) ((L : ℝ → E) 0) := by
    rw [hL0]; exact (hdiff x).hasFDerivAt
  have hφderiv : HasDerivAt (f ∘ ⇑L) ((fderiv ℝ f x) (y - x)) 0 :=
    hfderiv.comp_hasDerivAt 0 hLderiv
  -- Apply the 1-D first-order convexity inequality: `f' ≤ slope` for `0 < 1`.
  have hslope : (fderiv ℝ f x) (y - x) ≤ slope (f ∘ ⇑L) 0 1 :=
    hφconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hφderiv
  have hsl : slope (f ∘ ⇑L) 0 1 = f y - f x := by
    rw [slope_def_field]
    show ((f ∘ ⇑L) 1 - (f ∘ ⇑L) 0) / (1 - 0) = f y - f x
    rw [Function.comp_apply, Function.comp_apply, hL0, hL1]
    norm_num
  rw [hsl] at hslope
  -- Riesz bridge: `⟪∇f x, v⟫ = fderiv f x v`.
  have hinner : ⟪gradient f x, y - x⟫_ℝ = (fderiv ℝ f x) (y - x) :=
    inner_gradient_left
  linarith

end StatLean.Optimization
