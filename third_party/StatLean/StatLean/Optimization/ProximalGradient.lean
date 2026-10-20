module
public import StatLean.Optimization.Prox.Pillar

@[expose] public section

/-!
# Convergence of proximal gradient descent (O(1/t) rate)

Let $F = f + h$ be a composite objective on a real Hilbert space, where $f$ is
convex and $L$-smooth (its gradient is $L$-Lipschitz, with $L > 0$) and $h$ is
convex. Starting from $x_0$, the proximal-gradient method with constant step
$1/L$ generates the iterates
$$ x_{t+1} \;=\; \operatorname{prox}_{(1/L)\,h}\!\bigl(x_t - \tfrac{1}{L}\nabla f(x_t)\bigr), $$
where $\operatorname{prox}_{(1/L)h}(z) = \arg\min_y \bigl\{ \tfrac1L h(y) + \tfrac12\|y - z\|^2 \bigr\}$.
Then for every minimizer $x^\star$ of $F$ and every $t \ge 1$,
$$ F(x_t) - F(x^\star) \;\le\; \frac{L\,\|x_0 - x^\star\|^2}{2\,t}, $$
i.e. the objective gap decays at the $O(1/t)$ rate.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 14 (Proximal Gradient Descent), §14.1,
Theorem 14.1 (Convergence Rate of Proximal Gradient Descent).

**Proof formalization notes.** Each iterate is supplied as a prox minimizer
(hypothesis `hrec`), rather than evaluating the `prox` operator explicitly; this
is the defining variational characterization of the step. The proof applies the
pillar inequality (Lemma 14.1) twice: once with `x = y = x_t` to obtain monotone
descent `F(x_{t+1}) ≤ F(x_t)`, and once with `x = x*`, `y = x_t` to obtain a
per-step telescoping bound
`F(x_{t+1}) - F(x*) ≤ (L/2)‖x* - x_t‖² - (L/2)‖x* - x_{t+1}‖²`.
Summing the telescoping bound over `s = 0,…,t-1` collapses to `(L/2)‖x_0 - x*‖²`,
and antitonicity of the gap gives `t · (F(x_t) - F(x*)) ≤ ∑_s (F(x_{s+1}) - F(x*))`,
which combine to the stated `O(1/t)` rate. Constants match the book exactly.

**Bibliographic comments.** The proximal-gradient (forward–backward splitting)
method originates with P. L. Lions and B. Mercier, "Splitting algorithms for the
sum of two nonlinear operators", *SIAM J. Numer. Anal.* 16 (1979), 964–979, and
its modern signal-processing form is developed by P. L. Combettes and V. R. Wajs,
"Signal recovery by proximal forward–backward splitting", *Multiscale Model.
Simul.* 4 (2005), 1168–1200. The explicit $O(1/t)$ objective-gap bound
$F(x_t) - F(x^\star) \le L\|x_0 - x^\star\|^2/(2t)$ formalized here is Theorem 3.1
of A. Beck and M. Teboulle, "A fast iterative shrinkage-thresholding algorithm
for linear inverse problems", *SIAM J. Imaging Sci.* 2 (2009), 183–202 (where it
is stated for the ISTA instance; the accelerated FISTA variant in the same paper
achieves $O(1/t^2)$).
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lu-BDA Theorem 14.1 (Convergence Rate of Proximal Gradient Descent). `f` convex `L`-smooth
(`0 < L`), `h` convex, `F = f + h`, step `1/L`:
`F(x_t) - F(x*) ≤ L‖x_0 - x*‖² / (2t)`. -/
theorem proximalGradient_rate
    {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h)
    (x : ℕ → E)
    (hrec : ∀ t, IsProxMinimizer ((1 / L) • h)
        (x t - (1 / L) • gradient f (x t)) (x (t + 1)))
    {xstar : E} (hmin : ∀ y, f xstar + h xstar ≤ f y + h y)
    {t : ℕ} (ht : 0 < t) :
    (f (x t) + h (x t)) - (f xstar + h xstar) ≤ L * ‖x 0 - xstar‖ ^ 2 / (2 * (t : ℝ)) := by
  -- Monotone descent (pillar with `x = y = x_s`).
  have hdesc : ∀ s, f (x (s + 1)) + h (x (s + 1)) ≤ f (x s) + h (x s) := by
    intro s
    have hp := pillar hf hdiff hL hsmooth hh (x := x s) (hrec s)
    have h0 : ‖x s - x s‖ ^ 2 = 0 := by rw [sub_self, norm_zero]; ring
    rw [h0] at hp
    nlinarith [hp, sq_nonneg ‖x s - x (s + 1)‖, hL]
  have hanti : Antitone (fun s => f (x s) + h (x s) - (f xstar + h xstar)) :=
    antitone_nat_of_succ_le (fun s => by linarith [hdesc s])
  -- Telescoping step (pillar with `x = x*`, `y = x_s`).
  have hstep : ∀ s, f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar)
      ≤ L / 2 * ‖xstar - x s‖ ^ 2 - L / 2 * ‖xstar - x (s + 1)‖ ^ 2 :=
    fun s => pillar hf hdiff hL hsmooth hh (x := xstar) (hrec s)
  -- Sum the telescoping bound.
  have hsum : ∑ s ∈ Finset.range t, (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar))
      ≤ L / 2 * ‖x 0 - xstar‖ ^ 2 := by
    calc ∑ s ∈ Finset.range t, (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar))
        ≤ ∑ s ∈ Finset.range t,
            (L / 2 * ‖xstar - x s‖ ^ 2 - L / 2 * ‖xstar - x (s + 1)‖ ^ 2) :=
          Finset.sum_le_sum (fun s _ => hstep s)
      _ = L / 2 * ‖xstar - x 0‖ ^ 2 - L / 2 * ‖xstar - x t‖ ^ 2 :=
          Finset.sum_range_sub' (fun s => L / 2 * ‖xstar - x s‖ ^ 2) t
      _ ≤ L / 2 * ‖xstar - x 0‖ ^ 2 := by nlinarith [sq_nonneg ‖xstar - x t‖, hL]
      _ = L / 2 * ‖x 0 - xstar‖ ^ 2 := by rw [norm_sub_rev]
  -- `t · δ_t ≤ ∑ δ_{s+1}` by antitonicity.
  have hlb : (t : ℝ) * (f (x t) + h (x t) - (f xstar + h xstar))
      ≤ ∑ s ∈ Finset.range t, (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar)) := by
    calc (t : ℝ) * (f (x t) + h (x t) - (f xstar + h xstar))
        = ∑ _s ∈ Finset.range t, (f (x t) + h (x t) - (f xstar + h xstar)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ s ∈ Finset.range t, (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar)) :=
          Finset.sum_le_sum fun s hs =>
            hanti (Nat.succ_le_of_lt (Finset.mem_range.mp hs))
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (t : ℝ))]
  nlinarith [hlb, hsum]

end StatLean.Optimization
