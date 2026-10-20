module
public import StatLean.Optimization.Convex.Defs
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# Local minima are global minima; first-order optimality for convex functions

Let $f : E \to \mathbb{R}$ be a function on a real inner product space $E$. Two
companion facts of unconstrained convex optimization:

* **(First-order optimality.)** A point $x^\star$ is a global minimizer of $f$,
  i.e. $f(x^\star) \le f(y)$ for all $y$, if and only if the zero vector belongs
  to the subdifferential of $f$ at $x^\star$, written $0 \in \partial f(x^\star)$.
  Here $\partial f(x^\star) = \{\, g : \langle g,\, y - x^\star\rangle \le f(y) -
  f(x^\star)\ \text{for all } y \,\}$ is the set of subgradients, so the
  equivalence holds for an *arbitrary* function $f$ (no convexity needed): it is
  essentially the definition of subgradient specialized to $g = 0$.

* **(Local $\Rightarrow$ global.)** If $f$ is convex on the whole space and
  $x^\star$ is a *local* minimizer, then $x^\star$ is in fact a global minimizer:
  $f(x^\star) \le f(y)$ for every $y$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 12 (Convexity and Subgradient), §12.2
(Subgradient), Proposition 12.1 (Local Minima Are Global Minima).

**Proof formalization notes.** The first-order optimality statement is essentially
definitional via the subdifferential: $0 \in \partial f(x^\star)$ unfolds to
$\langle 0,\, y - x^\star\rangle \le f(y) - f(x^\star)$ for all $y$, and the left
side is $0$, giving $f(x^\star) \le f(y)$ directly; this requires no convexity.
The local-to-global direction argues by contradiction: if some $y$ had
$f(y) < f(x^\star)$, pick a convex-combination point
$z = x^\star + \gamma\,(y - x^\star) = (1-\gamma)\,x^\star + \gamma\,y$ with
$\gamma \in (0,1]$ small enough that $z$ lies in the $\varepsilon$-ball on which
the local-minimum property holds; then $f(x^\star) \le f(z)$, while convexity
gives $f(z) \le (1-\gamma)\,f(x^\star) + \gamma\,f(y)$, and since $\gamma > 0$ and
$f(y) < f(x^\star)$ these two bounds contradict each other.

**Bibliographic comments.** This is folklore in convex analysis with no single
seminal origin. The canonical treatment is R. T. Rockafellar, *Convex
Analysis*, Princeton University Press, 1970: the first-order optimality
characterization $0 \in \partial f(x^\star)$ is Theorem 27.1 there, and "every
local minimum of a convex function is a global minimum" follows from the
convexity inequality (cf. §27). The facts are standard across convex-optimization
references (e.g. Boyd & Vandenberghe, *Convex Optimization*, Cambridge University
Press, 2004, §4.2.3 and §3.1.7).
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lu-BDA Proposition 12.2 (First-Order Optimality Condition, unconstrained): `x*`
is a global minimizer of `f` iff `0 ∈ ∂f(x*)`. -/
theorem isGlobalMin_iff_zero_mem_subdifferential (f : E → ℝ) (xstar : E) :
    (∀ y, f xstar ≤ f y) ↔ (0 : E) ∈ subdifferential f xstar := by
  constructor
  · intro h y
    show ⟪(0 : E), y - xstar⟫_ℝ ≤ f y - f xstar
    rw [inner_zero_left]
    linarith [h y]
  · intro h y
    have hy : ⟪(0 : E), y - xstar⟫_ℝ ≤ f y - f xstar := h y
    rw [inner_zero_left] at hy
    linarith

/-- Lu-BDA Proposition 12.1 (Local Minima Are Global Minima): for convex `f`, any
local minimizer is a global minimizer. -/
theorem forall_le_of_isLocalMin
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {xstar : E}
    (hloc : IsLocalMin f xstar) (y : E) :
    f xstar ≤ f y := by
  by_contra hlt
  push_neg at hlt
  -- Reach the metric ε-form of the local-min property.
  have hloc_ev : ∀ᶠ z in 𝓝 xstar, f xstar ≤ f z := hloc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hloc_ev
  -- Pick `γ ∈ (0, 1]` with `γ * ‖y - xstar‖ < ε`.
  have hd_pos : 0 < ‖y - xstar‖ + 1 := by positivity
  have hε_d : 0 < ε / (‖y - xstar‖ + 1) := div_pos hε hd_pos
  set γ : ℝ := min 1 (ε / (‖y - xstar‖ + 1)) with hγ_def
  have hγ_pos : 0 < γ := lt_min one_pos hε_d
  have hγ_le1 : γ ≤ 1 := min_le_left _ _
  have hγ_le : γ ≤ ε / (‖y - xstar‖ + 1) := min_le_right _ _
  -- The convex-combination point `z = xstar + γ • (y - xstar) = (1-γ)•xstar + γ•y`.
  set z : E := xstar + γ • (y - xstar) with hz_def
  have hzx : z - xstar = γ • (y - xstar) := by rw [hz_def]; abel
  -- (1) `z` lies in the ε-ball around `xstar`, hence `f xstar ≤ f z`.
  have hdist : dist z xstar < ε := by
    rw [dist_eq_norm, hzx, norm_smul, Real.norm_eq_abs, abs_of_pos hγ_pos]
    have h1 : γ * ‖y - xstar‖ ≤ ε / (‖y - xstar‖ + 1) * ‖y - xstar‖ :=
      mul_le_mul_of_nonneg_right hγ_le (norm_nonneg _)
    have h2 : ε / (‖y - xstar‖ + 1) * ‖y - xstar‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hd_pos]
      nlinarith [norm_nonneg (y - xstar)]
    linarith
  have hfz : f xstar ≤ f z := hball hdist
  -- (2) Convexity: `f z ≤ (1-γ) * f xstar + γ * f y`.
  have hz_alg : z = (1 - γ) • xstar + γ • y := by
    rw [hz_def, sub_smul, one_smul, smul_sub]; abel
  have hconv : f z ≤ (1 - γ) • f xstar + γ • f y := by
    rw [hz_alg]
    exact hf.2 (Set.mem_univ xstar) (Set.mem_univ y)
      (by linarith) hγ_pos.le (by ring)
  simp only [smul_eq_mul] at hconv
  -- (3) Combine: with `γ > 0` and `f y < f xstar`, we contradict `f xstar ≤ f z ≤ ...`.
  have hcomb : f xstar ≤ (1 - γ) * f xstar + γ * f y := le_trans hfz hconv
  nlinarith [hcomb, hlt, hγ_pos]

end StatLean.Optimization
