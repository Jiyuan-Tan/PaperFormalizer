module
public import StatLean.Optimization.AcceleratedProximal

@[expose] public section

/-!
# Convergence of Nesterov's accelerated gradient descent (O(1/t²) rate)

Let $f$ be convex and $L$-smooth on a real inner product space, and let $x^\*$ be a
minimizer of $f$. Run **Nesterov's accelerated gradient descent** (AGD) from
$x_0 = y_0$ with fixed step size $\eta = 1/L$ and momentum schedule
$\lambda_0 = 1$, $\lambda_{t+1} = \tfrac{1 + \sqrt{1 + 4\lambda_t^2}}{2}$:
$$
x_{t+1} = y_t - \tfrac{1}{L}\,\nabla f(y_t),
\qquad
y_{t+1} = x_{t+1} + \frac{\lambda_t - 1}{\lambda_{t+1}}\,(x_{t+1} - x_t).
$$
The first update is a plain gradient step; the second mixes in the history term
$x_{t+1} - x_t$ to smooth the trajectory. Then for every $t \ge 1$,
$$
f(x_t) - f(x^\*) \;\le\; \frac{2L\,\lVert x_0 - x^\*\rVert^2}{(t+1)^2},
$$
i.e. AGD attains the accelerated $O(1/t^2)$ rate, faster than the $O(1/t)$ rate of
plain gradient descent.

The book states the bound for all $t$; the Lean statement restricts to $t \ge 1$,
inherited from the accelerated proximal gradient theorem it specializes (the
$t = 0$ case is the trivial $f(x_0) - f(x^\*) \le 2L\lVert x_0 - x^\*\rVert^2/1$,
not part of the formalized claim).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 13 (Gradient Descent), §13.3 (Accelerated
Gradient Descent), Theorem 13.3 (Convergence of AGD).

**Proof formalization notes.** This is the `h = 0` special case of accelerated
proximal gradient descent (Theorem 14.2, `acceleratedProximalGradient_rate`): the
proximal operator of the zero penalty is the identity, so the prox step
`prox_{(1/L)·0}(y_t - (1/L)∇f(y_t))` reduces to exactly the gradient step
`y_t - (1/L)∇f(y_t)`. We obtain the theorem as a direct corollary, per the book's
remark following Theorem 14.2.

**Bibliographic comments.** The algorithm and its $O(1/k^2)$ convergence rate are
due to Y. E. Nesterov, "A method for solving the convex programming problem with
convergence rate $O(1/k^2)$", *Doklady Akademii Nauk SSSR* **269** (3), 543–547,
1983 (in Russian). This is the seminal result establishing that, for convex
$L$-smooth objectives, first-order methods can accelerate the gradient-descent
$O(1/k)$ rate to the optimal $O(1/k^2)$ rate; the momentum schedule
$\lambda_{t+1} = (1 + \sqrt{1 + 4\lambda_t^2})/2$ originates there. The proof
technique formalized here (via an estimate-sequence / proximal argument) follows
the modern textbook treatment rather than Nesterov's original presentation.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lu-BDA Theorem 13.3 (Convergence of AGD). For convex `L`-smooth `f`
(`0 < L`) with step `1/L`, Nesterov's accelerated gradient descent satisfies
`f(x_t) - f(x*) ≤ 2L‖x_0 - x*‖²/(t+1)²`. Stated for `t ≥ 1` (inherited from
Theorem 14.2). Proved as the `h = 0` specialization of
`acceleratedProximalGradient_rate`. -/
theorem acceleratedGradientDescent_rate
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    (x y : ℕ → E) (lam : ℕ → ℝ)
    (hxy0 : y 0 = x 0) (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2)
    (hxrec : ∀ t, x (t + 1) = y t - (1 / L) • gradient f (y t))
    (hyrec : ∀ t, y (t + 1) = x (t + 1) + ((lam t - 1) / lam (t + 1)) • (x (t + 1) - x t))
    {xstar : E} (hmin : ∀ z, f xstar ≤ f z)
    (t : ℕ) (ht : 1 ≤ t) :
    f (x t) - f xstar ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / ((t : ℝ) + 1) ^ 2 := by
  -- the zero penalty is convex, and its prox step is the gradient step
  have hh0 : ConvexOn ℝ Set.univ (fun _ : E => (0 : ℝ)) := convexOn_const 0 convex_univ
  have hprox : ∀ t, IsProxMinimizer ((1 / L) • (fun _ : E => (0 : ℝ)))
      (y t - (1 / L) • gradient f (y t)) (x (t + 1)) := by
    intro t w
    rw [hxrec t]
    simp only [proxObj, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, sub_self, norm_zero]
    nlinarith [sq_nonneg ‖w - (y t - (1 / L) • gradient f (y t))‖]
  have hmin0 : ∀ z, f xstar + (fun _ : E => (0 : ℝ)) xstar ≤ f z + (fun _ : E => (0 : ℝ)) z :=
    fun z => by simpa using hmin z
  have key := acceleratedProximalGradient_rate hf hdiff hL hsmooth hh0 x y lam hxy0 hlam0
    hlamrec hprox hyrec hmin0 t ht
  simpa using key

end StatLean.Optimization
