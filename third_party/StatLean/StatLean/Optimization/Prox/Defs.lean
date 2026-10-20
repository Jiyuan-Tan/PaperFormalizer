module
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Proximal operator

For a function $h : E \to \mathbb{R}$ on a real inner product space $E$ and a
point $x \in E$, the **proximal operator** of $h$ at $x$ is the minimizer of the
regularized objective
$$\operatorname{prox}_h(x) = \arg\min_{z \in E}\Big\{ \tfrac{1}{2}\|z - x\|^2 + h(z) \Big\}.$$
This file provides the concept-layer definitions for the `Optimization` area:
the proximal objective $z \mapsto \tfrac{1}{2}\|z - x\|^2 + h(z)$ and the
predicate characterizing a point $z$ as attaining this minimum (i.e. as being a
value of $\operatorname{prox}_h(x)$).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland,
2025 (ISBN 978-3-032-03160-0). Chapter 14 (Proximal Gradient Descent), §14.1,
proximal operator definition.

**Proof formalization notes.** The book defines $\operatorname{prox}_h(x)$ as
the $\arg\min$ of $\tfrac{1}{2}\|z - x\|^2 + h(z)$. Rather than construct the
minimizer as an element (which would require properness / lower semicontinuity /
coercivity of $h$ to guarantee existence and uniqueness), we expose the
minimization *property* as a predicate `IsProxMinimizer h x z`, asserting that
$z$ attains the global minimum of the proximal objective. The proximal
algorithms then take "this iterate is a prox step of the previous point" as an
oracle hypothesis — the legitimate external input describing what the algorithm
computes, mirroring the book's algorithm definition. `proxObj` is
`noncomputable` because it uses real division.

**Bibliographic comments.** The proximal mapping ("proximité") was introduced by
J.-J. Moreau, *Proximité et dualité dans un espace hilbertien*, Bulletin de la
Société Mathématique de France, vol. 93, pp. 273–299, 1965, where the associated
infimal-convolution regularization is now called the Moreau envelope. The notion
underpins modern proximal-gradient and splitting methods; the
presentation here is standard.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The proximal objective `proxObj h x z = ½‖z - x‖² + h z`, whose minimizer
over `z` defines `prox_h(x)` (Lu-BDA §14.1). `noncomputable` as it uses real
division. -/
noncomputable def proxObj (h : E → ℝ) (x z : E) : ℝ := (1 / 2) * ‖z - x‖ ^ 2 + h z

/-- `IsProxMinimizer h x z`: `z` attains the minimum of `proxObj h x`, i.e.
`z = prox_h(x)` (Lu-BDA §14.1). Characterizing the prox point by its
minimization property avoids committing to an existence theorem for the
minimizer. -/
def IsProxMinimizer (h : E → ℝ) (x z : E) : Prop :=
  ∀ w, proxObj h x z ≤ proxObj h x w

end StatLean.Optimization
