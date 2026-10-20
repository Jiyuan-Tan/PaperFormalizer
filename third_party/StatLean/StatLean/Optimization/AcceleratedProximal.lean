module
public import StatLean.Optimization.Prox.Pillar
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Convergence of accelerated proximal gradient descent (FISTA, $O(1/t^2)$ rate)

Consider the composite minimization of $F = f + h$, where $f$ is convex and
$L$-smooth (its gradient is $L$-Lipschitz, $L > 0$) and $h$ is convex (possibly
nonsmooth). The accelerated proximal-gradient method (FISTA) generates iterates
with the constant step $1/L$ and Nesterov momentum: starting from
$x_0 = y_0$, $\lambda_0 = 1$, and the extrapolation sequence
$\lambda_{t+1} = \tfrac{1}{2}\bigl(1 + \sqrt{1 + 4\lambda_t^2}\bigr)$,
$$
x_{t+1} = \operatorname{prox}_{(1/L)h}\!\bigl(y_t - \tfrac1L \nabla f(y_t)\bigr),
\qquad
y_{t+1} = x_{t+1} + \frac{\lambda_t - 1}{\lambda_{t+1}}\,(x_{t+1} - x_t).
$$
Then for any minimizer $x^\star$ of $F$ the optimality gap decays at the
accelerated rate
$$
F(x_t) - F(x^\star) \;\le\; \frac{2L\,\lVert x_0 - x^\star\rVert^2}{(t+1)^2}.
$$
This is faster than the $O(1/t)$ rate of the (non-accelerated) proximal gradient
method.

*Deviation from the book.* The Lean statement is proved for $t \ge 1$; the
$t = 0$ case is the trivial initial gap and is excluded, per CLAUDE.md §1
(documented constant/scope deviation).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 14 (Proximal Gradient Descent), §14.2
(Accelerated Proximal Gradient Descent), Theorem 14.2 (Convergence Rate of
Accelerated Proximal Gradient Descent).

**Proof formalization notes.** The proof is *not* monotone in $F$. It combines:
* the pillar inequality (Lemma 14.1, `pillar`), which controls one proximal step;
* a Lyapunov energy $L_t = \lVert u_t\rVert^2 + \tfrac2L \lambda_{t-1}^2\,(F(x_t) - F(x^\star))$
  (Lemma 14.2 (Lyapunov Function) below) shown to be non-increasing — in the Lean code this is the
  `Φ`/`hΦdec` antitone-energy argument, with `Φ s` equal to $L/2$ times the book
  $L_{s+1}$ (division-free) and `u s` the book $u_{s+1}$;
* the Nesterov-sequence lower bound $\lambda_t \ge (t+2)/2$
  (`nesterov_lambda_lower`) and the identity
  $\lambda_{s+1}^2 - \lambda_{s+1} = \lambda_s^2$ (`lam_sq_sub`, from
  $(2\lambda_{s+1} - 1)^2 = 1 + 4\lambda_s^2$),
which together turn the telescoped energy bound into the stated $O(1/t^2)$ rate.

**Bibliographic comments.** The algorithm and its $O(1/t^2)$ convergence rate are
due to A. Beck and M. Teboulle, "A Fast Iterative Shrinkage-Thresholding
Algorithm for Linear Inverse Problems," *SIAM Journal on Imaging Sciences*
**2**(1):183–202, 2009. The momentum recursion
$\lambda_{t+1} = \tfrac12(1 + \sqrt{1 + 4\lambda_t^2})$ appears as Eq. (4.1)–(4.2)
there, and the rate bound $F(x_t) - F(x^\star) \le 2L\lVert x_0 - x^\star\rVert^2/(t+1)^2$
is their Theorem 4.4. The construction builds on Nesterov's accelerated
gradient method (Yu. Nesterov, "A method for solving the convex programming
problem with convergence rate $O(1/k^2)$," *Soviet Math. Dokl.* **27**:372–376,
1983), extending the optimal first-order rate to the composite (nonsmooth $h$)
setting via the proximal operator.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Nesterov extrapolation sequence `λ_0 = 1`,
`λ_{t+1} = (1 + √(1 + 4λ_t²))/2` satisfies `λ_t ≥ (t+2)/2` (Lu-BDA §14.2). -/
theorem nesterov_lambda_lower
    (lam : ℕ → ℝ) (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2)
    (t : ℕ) :
    ((t : ℝ) + 2) / 2 ≤ lam t := by
  induction t with
  | zero => rw [hlam0]; norm_num
  | succ k ih =>
    have hk_nonneg : (0 : ℝ) ≤ lam k := le_trans (by positivity) ih
    rw [hlamrec k]
    have hsqrt : ((k : ℝ) + 2) ≤ Real.sqrt (1 + 4 * lam k ^ 2) := by
      rw [show ((k : ℝ) + 2) = Real.sqrt (((k : ℝ) + 2) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h2 : (k : ℝ) + 2 ≤ 2 * lam k := by linarith [ih]
      have hsq : ((k : ℝ) + 2) ^ 2 ≤ (2 * lam k) ^ 2 :=
        sq_le_sq' (by linarith [hk_nonneg, hk0]) h2
      nlinarith [hsq]
    push_cast
    linarith [hsqrt]

/-- The Nesterov sequence is strictly positive. -/
private theorem lam_pos (lam : ℕ → ℝ) (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2) (s : ℕ) :
    0 < lam s := by
  have h := nesterov_lambda_lower lam hlam0 hlamrec s
  have : (0 : ℝ) < ((s : ℝ) + 2) / 2 := by positivity
  linarith

/-- The Nesterov-sequence identity `λ_{s+1}² - λ_{s+1} = λ_s²` (Lu-BDA §14.2,
from `(2λ_{s+1} - 1)² = 1 + 4λ_s²`). -/
private theorem lam_sq_sub (lam : ℕ → ℝ)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2) (s : ℕ) :
    lam (s + 1) ^ 2 - lam (s + 1) = lam s ^ 2 := by
  have hsq : Real.sqrt (1 + 4 * lam s ^ 2) ^ 2 = 1 + 4 * lam s ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [hlamrec s]
  linear_combination (1 / 4 : ℝ) * hsq

/-- Lu-BDA Theorem 14.2 (Convergence Rate of Accelerated Proximal Gradient Descent). `f` convex
`L`-smooth (`0 < L`), `h` convex, `F = f + h`, step `1/L`, Nesterov momentum:
`F(x_t) - F(x*) ≤ 2L‖x_0 - x*‖² / (t+1)²`. Stated for `t ≥ 1` (the `t = 0` case
is the trivial initial gap), per CLAUDE.md §1 documented deviation. -/
theorem acceleratedProximalGradient_rate
    {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h)
    (x y : ℕ → E) (lam : ℕ → ℝ)
    (hxy0 : y 0 = x 0)
    (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2)
    (hxrec : ∀ t, IsProxMinimizer ((1 / L) • h)
        (y t - (1 / L) • gradient f (y t)) (x (t + 1)))
    (hyrec : ∀ t, y (t + 1) = x (t + 1) + ((lam t - 1) / lam (t + 1)) • (x (t + 1) - x t))
    {xstar : E} (hmin : ∀ z, f xstar + h xstar ≤ f z + h z)
    (t : ℕ) (ht : 1 ≤ t) :
    (f (x t) + h (x t)) - (f xstar + h xstar)
      ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / ((t : ℝ) + 1) ^ 2 := by
  have hLpos : (0 : ℝ) < L := hL
  have hFconv : ConvexOn ℝ Set.univ (fun z => f z + h z) := hf.add hh
  have hlampos : ∀ s, (0 : ℝ) < lam s := fun s => lam_pos lam hlam0 hlamrec s
  -- `u s` = book `u_{s+1}`; `Φ s` = `(L/2)·` book Lyapunov `L_{s+1}` (division-free).
  set u : ℕ → E := fun s => lam s • x (s + 1) - (xstar + (lam s - 1) • x s) with hu
  set Φ : ℕ → ℝ := fun s =>
      L / 2 * ‖u s‖ ^ 2 + lam s ^ 2 *
        (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar)) with hΦ
  -- Lyapunov monotonicity (Lemma 14.2).
  have hΦdec : ∀ s, Φ (s + 1) ≤ Φ s := by
    intro s
    have hpos1 : (0 : ℝ) < lam (s + 1) := hlampos (s + 1)
    have hne1 : lam (s + 1) ≠ 0 := ne_of_gt hpos1
    have hpos2 : (0 : ℝ) < lam (s + 1) ^ 2 := by positivity
    have hge1 : (1 : ℝ) ≤ lam (s + 1) := by
      have hnl := nesterov_lambda_lower lam hlam0 hlamrec (s + 1)
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
      push_cast at hnl; linarith
    set xc : E := (lam (s + 1))⁻¹ • xstar + (1 - (lam (s + 1))⁻¹) • x (s + 1) with hxc
    have hmom : lam (s + 1) • y (s + 1) - (xstar + (lam (s + 1) - 1) • x (s + 1)) = u s := by
      simp only [hu, hyrec s]; match_scalars <;> field_simp <;> ring
    have hlamxc : lam (s + 1) • xc = xstar + (lam (s + 1) - 1) • x (s + 1) := by
      simp only [hxc]; match_scalars <;> field_simp
    have hsc_y : lam (s + 1) • (xc - y (s + 1)) = -u s := by
      rw [smul_sub, hlamxc, ← hmom]; abel
    have hsc_x : lam (s + 1) • (xc - x (s + 2)) = -u (s + 1) := by
      rw [smul_sub, hlamxc]; simp only [hu]; abel
    have hnorm_y : lam (s + 1) ^ 2 * ‖xc - y (s + 1)‖ ^ 2 = ‖u s‖ ^ 2 := by
      have hcg := congrArg (fun z => ‖z‖ ^ 2) hsc_y
      simpa [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using hcg
    have hnorm_x : lam (s + 1) ^ 2 * ‖xc - x (s + 2)‖ ^ 2 = ‖u (s + 1)‖ ^ 2 := by
      have hcg := congrArg (fun z => ‖z‖ ^ 2) hsc_x
      simpa [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using hcg
    have hconv : f xc + h xc
        ≤ (lam (s + 1))⁻¹ * (f xstar + h xstar)
          + (1 - (lam (s + 1))⁻¹) * (f (x (s + 1)) + h (x (s + 1))) := by
      have hw1 : (0 : ℝ) ≤ 1 - (lam (s + 1))⁻¹ := by
        have : (lam (s + 1))⁻¹ ≤ 1 := (inv_le_one₀ hpos1).mpr hge1
        linarith
      have ha0 : (0 : ℝ) ≤ (lam (s + 1))⁻¹ := by positivity
      have hab1 : (lam (s + 1))⁻¹ + (1 - (lam (s + 1))⁻¹) = 1 := by ring
      have hcv := hFconv.2 (Set.mem_univ xstar) (Set.mem_univ (x (s + 1))) ha0 hw1 hab1
      simpa [hxc] using hcv
    have hp := pillar hf hdiff hL hsmooth hh (x := xc) (hxrec (s + 1))
    have hlamsq := lam_sq_sub lam hlamrec s
    -- the book inequality, with the λ_{s+1}²-scaled pillar and the norm identities
    have hpil : lam (s + 1) ^ 2 * (f (x (s + 2)) + h (x (s + 2)) - (f xc + h xc))
        ≤ L / 2 * ‖u s‖ ^ 2 - L / 2 * ‖u (s + 1)‖ ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hp hpos2.le
      rw [← hnorm_y, ← hnorm_x]; nlinarith [hm]
    have hcv2 : lam (s + 1) ^ 2 * (f xc + h xc)
        ≤ lam (s + 1) * (f xstar + h xstar) + lam s ^ 2 * (f (x (s + 1)) + h (x (s + 1))) := by
      have hm := mul_le_mul_of_nonneg_left hconv hpos2.le
      have he : lam (s + 1) ^ 2 * ((lam (s + 1))⁻¹ * (f xstar + h xstar)
            + (1 - (lam (s + 1))⁻¹) * (f (x (s + 1)) + h (x (s + 1))))
          = lam (s + 1) * (f xstar + h xstar)
            + (lam (s + 1) ^ 2 - lam (s + 1)) * (f (x (s + 1)) + h (x (s + 1))) := by
        field_simp
      rw [he, hlamsq] at hm
      exact hm
    have hlsF : (lam (s + 1) ^ 2 - lam (s + 1)) * (f xstar + h xstar)
        = lam s ^ 2 * (f xstar + h xstar) := by rw [hlamsq]
    simp only [hΦ]
    nlinarith [hpil, hcv2, hlsF]
  have hΦanti : Antitone Φ := antitone_nat_of_succ_le hΦdec
  have hΦ0 : Φ 0 ≤ L / 2 * ‖x 0 - xstar‖ ^ 2 := by
    have hp0 := pillar hf hdiff hL hsmooth hh (x := xstar) (hxrec 0)
    rw [hxy0] at hp0
    have hu0 : u 0 = x 1 - xstar := by simp only [hu, hlam0]; module
    simp only [hΦ, hu0, hlam0]
    have e1 : ‖xstar - x 0‖ ^ 2 = ‖x 0 - xstar‖ ^ 2 := by rw [norm_sub_rev]
    have e2 : ‖xstar - x 1‖ ^ 2 = ‖x 1 - xstar‖ ^ 2 := by rw [norm_sub_rev]
    nlinarith [hp0, e1, e2, hLpos]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hΦm := le_trans (hΦanti (Nat.zero_le m)) hΦ0
  simp only [hΦ] at hΦm
  have hlb : ((m : ℝ) + 2) / 2 ≤ lam m := nesterov_lambda_lower lam hlam0 hlamrec m
  have hmpos : (0 : ℝ) < lam m := hlampos m
  have hgap : (0 : ℝ) ≤ f (x (m + 1)) + h (x (m + 1)) - (f xstar + h xstar) := by
    linarith [hmin (x (m + 1))]
  have hmsq : ((m : ℝ) + 2) ^ 2 / 4 ≤ lam m ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((m : ℝ) + 2) / 2 := by positivity
    nlinarith [mul_le_mul hlb hlb h0 hmpos.le]
  push_cast
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1 + 1) ^ 2)]
  nlinarith [hΦm, mul_le_mul_of_nonneg_right hmsq hgap, hgap, hLpos, sq_nonneg ‖u m‖]

end StatLean.Optimization
