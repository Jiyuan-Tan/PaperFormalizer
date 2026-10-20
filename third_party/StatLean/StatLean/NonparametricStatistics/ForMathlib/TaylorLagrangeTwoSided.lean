module
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# Taylor's theorem with Lagrange remainder, two-sided global form

For a globally `C^ℓ` function `f : ℝ → ℝ` (`ℓ ≥ 1`), expansion of order `ℓ − 1` around `x₀`
with the mean-value (Lagrange) form of the remainder, valid for increments of *either* sign:
$$ f(x_0 + t) = \sum_{j=0}^{\ell-1} \frac{f^{(j)}(x_0)}{j!} t^j
   + \frac{f^{(\ell)}(x_0 + \tau t)}{\ell!}\,t^\ell, \qquad \tau \in (0,1). $$

This is the exact shape consumed by the pointwise bias analysis of kernel smoothers over
Hölder classes: the remainder features the `ℓ`-th derivative at an intermediate point, to be
compared with its value at `x₀` via the Hölder condition.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.1 (Taylor–Lagrange tooling for the bias
bound of Proposition 1.2).

**Proof formalization notes.** Mathlib's `taylor_mean_remainder_lagrange` is one-sided
(`x₀ < x`, sets phrased with `Icc x₀ x` and `iteratedDerivWithin`); this file upgrades it to
the two-sided global form by working on `uIcc` (or by reflecting `f`), and converts
`iteratedDerivWithin` on the interval to global `iteratedDeriv` using `ContDiff` and unique
differentiability of intervals. The intermediate point is reported as `x₀ + τ·t`, `τ ∈ (0,1)`,
which covers both signs of `t` uniformly.

**Bibliographic comments.** B. Taylor, *Methodus incrementorum directa et inversa* (London,
1715); the mean-value remainder form is due to J.-L. Lagrange, *Théorie des fonctions
analytiques* (Paris, 1797).
-/

open scoped Nat

namespace StatLean.NonparametricStatistics

open Set in
/-- One-sided (positive increment) form of Taylor–Lagrange, obtained directly from Mathlib's
`taylor_mean_remainder_lagrange_iteratedDeriv` on `Icc x₀ (x₀ + t)`. -/
private lemma taylor_lagrange_pos {f : ℝ → ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hf : ContDiff ℝ ℓ f) (x₀ t : ℝ) (ht : 0 < t) :
    ∃ τ ∈ Set.Ioo (0 : ℝ) 1,
      f (x₀ + t)
        = (∑ j ∈ Finset.range ℓ, iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ))
          + iteratedDeriv ℓ f (x₀ + τ * t) * t ^ ℓ / (Nat.factorial ℓ : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos hℓ).symm⟩
  obtain ⟨x', h1, h2⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (x := x₀ + t) (x₀ := x₀) (n := n)
      (by linarith) hf.contDiffOn
  rw [Set.uIoo_of_le (by linarith)] at h1
  rw [Set.uIcc_of_le (by linarith)] at h2
  -- Convert the Taylor polynomial to the explicit sum with global iterated derivatives.
  have hsum : taylorWithinEval f n (Set.Icc x₀ (x₀ + t)) x₀ (x₀ + t)
      = ∑ j ∈ Finset.range (n + 1),
          iteratedDeriv j f x₀ * ((x₀ + t) - x₀) ^ j / (Nat.factorial j : ℝ) := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
        (hf.contDiffAt.of_le (by exact_mod_cast (Finset.mem_range.mp hk).le))
        (Set.left_mem_Icc.mpr (by linarith)), smul_eq_mul]
    ring
  -- The intermediate point `x'` is `x₀ + τ·t` with `τ ∈ (0,1)`.
  set τ := (x' - x₀) / t with hτdef
  have htne : t ≠ 0 := ne_of_gt ht
  have hτ0 : 0 < τ := div_pos (by linarith [h1.1]) ht
  have hτ1 : τ < 1 := by rw [hτdef, div_lt_one ht]; linarith [h1.2]
  have hpt : x₀ + τ * t = x' := by rw [hτdef, div_mul_cancel₀ _ htne]; ring
  refine ⟨τ, ⟨hτ0, hτ1⟩, ?_⟩
  rw [hsum, ← hpt] at h2
  simp only [add_sub_cancel_left] at h2
  linarith [h2]

/-- **Taylor–Lagrange, two-sided global form.** If `f` is `C^ℓ` on `ℝ` with `ℓ ≥ 1` and
`t ≠ 0`, then for some `τ ∈ (0,1)`:
`f (x₀ + t) = ∑_{j<ℓ} f⁽ʲ⁾(x₀)·tʲ/j! + f⁽ℓ⁾(x₀ + τ·t)·tℓ/ℓ!`. -/
theorem taylor_lagrange_global {f : ℝ → ℝ} {ℓ : ℕ}
    -- LEAN-ONLY: order at least one so the remainder term is a genuine derivative; the
    -- degenerate `ℓ = 0` case is handled separately by consumers
    (hℓ : 1 ≤ ℓ)
    -- USER-INPUT: `f` is `ℓ` times continuously differentiable on `ℝ`; classical smoothness
    -- input of Taylor's theorem
    (hf : ContDiff ℝ ℓ f)
    (x₀ t : ℝ)
    -- LEAN-ONLY: nonzero increment; at `t = 0` both sides are `f x₀` and no intermediate
    -- point is needed
    (ht : t ≠ 0) :
    ∃ τ ∈ Set.Ioo (0 : ℝ) 1,
      f (x₀ + t)
        = (∑ j ∈ Finset.range ℓ, iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ))
          + iteratedDeriv ℓ f (x₀ + τ * t) * t ^ ℓ / (Nat.factorial ℓ : ℝ) := by
  rcases lt_trichotomy t 0 with ht' | rfl | ht'
  · -- Negative increment: reflect through `x₀` and apply the positive-increment lemma.
    set g : ℝ → ℝ := fun z => f (2 * x₀ - z) with hg
    have hgC : ContDiff ℝ ℓ g := by rw [hg]; fun_prop
    have hpow : ∀ j : ℕ, (-1 : ℝ) ^ j * (-t) ^ j = t ^ j := fun j => by
      rw [← mul_pow, neg_one_mul, neg_neg]
    have hrefl : ∀ (k : ℕ) (y : ℝ),
        iteratedDeriv k g y = (-1 : ℝ) ^ k * iteratedDeriv k f (2 * x₀ - y) := by
      intro k y
      simp only [hg, iteratedDeriv_comp_const_sub, smul_eq_mul]
    obtain ⟨τ, hτ, heq⟩ := taylor_lagrange_pos hℓ hgC x₀ (-t) (by linarith)
    refine ⟨τ, hτ, ?_⟩
    have hL : g (x₀ + -t) = f (x₀ + t) := by
      simp only [hg, show (2 : ℝ) * x₀ - (x₀ + -t) = x₀ + t from by ring]
    have hterm : ∀ j : ℕ,
        iteratedDeriv j g x₀ * (-t) ^ j / (Nat.factorial j : ℝ)
          = iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ) := by
      intro j
      rw [hrefl j x₀, show (2 : ℝ) * x₀ - x₀ = x₀ from by ring]
      conv_rhs => rw [← hpow j]
      ring
    have hrem :
        iteratedDeriv ℓ g (x₀ + τ * -t) * (-t) ^ ℓ / (Nat.factorial ℓ : ℝ)
          = iteratedDeriv ℓ f (x₀ + τ * t) * t ^ ℓ / (Nat.factorial ℓ : ℝ) := by
      rw [hrefl ℓ (x₀ + τ * -t), show (2 : ℝ) * x₀ - (x₀ + τ * -t) = x₀ + τ * t from by ring]
      conv_rhs => rw [← hpow ℓ]
      ring
    rw [← hL, heq, hrem]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  · exact (ht rfl).elim
  · -- Positive increment: direct.
    exact taylor_lagrange_pos hℓ hf x₀ t ht'

end StatLean.NonparametricStatistics
