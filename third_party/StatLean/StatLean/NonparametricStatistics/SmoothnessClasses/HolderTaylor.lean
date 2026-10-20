module
public import StatLean.NonparametricStatistics.SmoothnessClasses.Defs
public import StatLean.NonparametricStatistics.ForMathlib.TaylorLagrangeTwoSided
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

/-!
# Taylor remainder bounds over Hölder classes

The one inequality that drives every pointwise bias bound in this area: for `f` in the Hölder
class `Σ(β, L)` and `ℓ = holderIndex β`,
$$ \Bigl|f(x_0+t) - \sum_{j=0}^{\ell} \frac{f^{(j)}(x_0)}{j!}t^j\Bigr|
   \;\le\; \frac{L}{\ell!}\,|t|^{\beta}. $$
(The sum includes the `ℓ`-th term; Taylor–Lagrange leaves the remainder
`(f^{(ℓ)}(x₀+τt) − f^{(ℓ)}(x₀))·t^ℓ/ℓ!`, which the Hölder condition bounds by
`(L/ℓ!)·|τt|^{β−ℓ}·|t|^ℓ ≤ (L/ℓ!)·|t|^β`.)

Provided in a global form (class on `ℝ`, for kernel density bias) and an interval form (class
on `Icc a b`, for local polynomial bias), plus a polynomial-growth envelope used to derive
integrability of kernel-weighted compositions.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.1 (Taylor-remainder control on the Hölder
class $\Sigma(\beta, L)$, as used in the proof of Proposition 1.2).

**Proof formalization notes.** The `ℓ = 0` case is the Hölder condition itself (no Taylor
step). For `ℓ ≥ 1`, the global form uses `taylor_lagrange_global`; the interval form uses
Mathlib's `taylor_mean_remainder_lagrange` on `uIcc x₀ x` together with
`iteratedDerivWithin`-monotonicity lemmas to move between `uIcc x₀ x ⊆ Icc a b`. The exponent
algebra `|t|^ℓ·|t|^{β−ℓ} = |t|^β` is `Real.rpow_natCast`/`rpow_add` (with `t = 0` handled
separately).

**Bibliographic comments.** This bias-controlling inequality is the classical smoothness
computation of kernel estimation, in the form used since E. Parzen, *Ann. Math. Statist.*
**33** (1962), 1065–1076.
-/

open scoped Nat

namespace StatLean.NonparametricStatistics

/-- For `0 < β`, the ceiling `⌈β⌉₊` is at least one, so `holderIndex β = ⌈β⌉₊ - 1` is honest. -/
private lemma one_le_ceil {β : ℝ} (hβ : 0 < β) : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr hβ

/-- The smoothness index is strictly below `β`: `(holderIndex β : ℝ) < β`. -/
private lemma holderIndex_lt_self {β : ℝ} (hβ : 0 < β) : (holderIndex β : ℝ) < β := by
  have h1 : 1 ≤ ⌈β⌉₊ := one_le_ceil hβ
  unfold holderIndex
  rw [Nat.cast_sub h1, Nat.cast_one]
  have h2 : (⌈β⌉₊ : ℝ) < β + 1 := Nat.ceil_lt_add_one hβ.le
  linarith

/-- The fractional exponent `β − holderIndex β` is positive. -/
private lemma sub_holderIndex_pos {β : ℝ} (hβ : 0 < β) : 0 < β - (holderIndex β : ℝ) :=
  sub_pos.mpr (holderIndex_lt_self hβ)

/-- Exponent splitter: `|t|^ℓ · |t|^(β−ℓ) = |t|^β` for `t ≠ 0` (natural power times rpow). -/
private lemma abs_rpow_split {β : ℝ} {t : ℝ} (ht : t ≠ 0) (ℓ : ℕ) :
    |t| ^ ℓ * |t| ^ (β - (ℓ : ℝ)) = |t| ^ β := by
  rw [← Real.rpow_natCast |t| ℓ, ← Real.rpow_add (abs_pos.mpr ht)]
  congr 1; ring

/-- Global Hölder classes see through `iteratedDerivWithin univ = iteratedDeriv`: the top
derivative satisfies the Hölder bound globally. -/
theorem MemHolder.iteratedDeriv_holder {β L : ℝ} {f : ℝ → ℝ} (hf : MemHolder β L f)
    (x y : ℝ) :
    |iteratedDeriv (holderIndex β) f x - iteratedDeriv (holderIndex β) f y|
      ≤ L * |x - y| ^ (β - (holderIndex β : ℝ)) := by
  have h := MemHolderOn.deriv_holder hf x (Set.mem_univ x) y (Set.mem_univ y)
  simpa only [iteratedDerivWithin_univ] using h

/-- **Taylor remainder bound over a global Hölder class**: for `f ∈ Σ(β, L)` on `ℝ`,
`|f(x₀+t) − ∑_{j≤ℓ} f⁽ʲ⁾(x₀)tʲ/j!| ≤ (L/ℓ!)·|t|^β` with `ℓ = holderIndex β`. -/
theorem MemHolder.taylor_remainder_abs_le {β L : ℝ}
    -- USER-INPUT: positive smoothness and Hölder constant; classical class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemHolder β L f) (x₀ t : ℝ) :
    |f (x₀ + t) - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ)|
      ≤ L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
  rcases Nat.eq_zero_or_pos (holderIndex β) with hℓ0 | hℓpos
  · -- `ℓ = 0`: the bound is the Hölder condition itself.
    have hsum : (∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ)) = f x₀ := by
      rw [hℓ0, zero_add, Finset.sum_range_one]; simp
    rw [hsum, hℓ0]
    have hh := hf.iteratedDeriv_holder (x₀ + t) x₀
    rw [hℓ0] at hh
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, add_sub_cancel_left,
      Nat.factorial_zero, Nat.cast_one, div_one] at hh ⊢
    exact hh
  rcases eq_or_ne t 0 with rfl | ht
  · -- `ℓ ≥ 1`, `t = 0`: both sides vanish.
    have hsum : (∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x₀ * (0 : ℝ) ^ j / (Nat.factorial j : ℝ)) = f x₀ := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj; simp [zero_pow hj]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
    rw [add_zero, hsum, sub_self]
    simp [Real.zero_rpow hβ.ne']
  · -- `ℓ ≥ 1`, `t ≠ 0`: Taylor–Lagrange leaves a top-derivative difference; bound by Hölder.
    obtain ⟨τ, hτ, heq⟩ :=
      taylor_lagrange_global hℓpos (contDiffOn_univ.mp (MemHolderOn.contDiffOn hf)) x₀ t ht
    have hdiff : f (x₀ + t) - ∑ j ∈ Finset.range (holderIndex β + 1),
          iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ)
        = (iteratedDeriv (holderIndex β) f (x₀ + τ * t)
              - iteratedDeriv (holderIndex β) f x₀)
            * t ^ (holderIndex β) / (Nat.factorial (holderIndex β) : ℝ) := by
      rw [Finset.sum_range_succ, heq]; ring
    have hfac : (0 : ℝ) < (Nat.factorial (holderIndex β) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hA : |iteratedDeriv (holderIndex β) f (x₀ + τ * t)
          - iteratedDeriv (holderIndex β) f x₀|
        ≤ L * |t| ^ (β - (holderIndex β : ℝ)) := by
      have h1 := hf.iteratedDeriv_holder (x₀ + τ * t) x₀
      rw [add_sub_cancel_left] at h1
      refine h1.trans ?_
      apply mul_le_mul_of_nonneg_left _ hL
      apply Real.rpow_le_rpow (abs_nonneg _) _ (le_of_lt (sub_holderIndex_pos hβ))
      rw [abs_mul]
      have hτle : |τ| ≤ 1 := by rw [abs_of_pos hτ.1]; exact le_of_lt hτ.2
      calc |τ| * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hτle (abs_nonneg _)
        _ = |t| := one_mul _
    rw [hdiff, abs_div, abs_mul, abs_pow, abs_of_pos hfac]
    calc |iteratedDeriv (holderIndex β) f (x₀ + τ * t) - iteratedDeriv (holderIndex β) f x₀|
            * |t| ^ (holderIndex β) / (Nat.factorial (holderIndex β) : ℝ)
        ≤ (L * |t| ^ (β - (holderIndex β : ℝ))) * |t| ^ (holderIndex β)
            / (Nat.factorial (holderIndex β) : ℝ) := by gcongr
      _ = L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
          have hsplit : |t| ^ (holderIndex β) * |t| ^ (β - (holderIndex β : ℝ)) = |t| ^ β :=
            abs_rpow_split ht (holderIndex β)
          rw [← hsplit]; ring

set_option maxHeartbeats 800000 in
-- The Cauchy mean-value setup (`taylorWithinEval` continuity/derivative side goals and the two
-- `linear_combination` closings) is elaboration-heavy; the default heartbeat budget is tight.
/-- **Two-sided Taylor–Lagrange over a closed interval.** For `f ∈ C^{n+1}(Icc a b)`, expansion
around any `x₀ ∈ Icc a b`, evaluated at any `x ∈ Icc a b` (either side), leaves the Lagrange
remainder with the `(n+1)`-th derivative *within `Icc a b`* at an intermediate point. Proved by
Cauchy's mean value theorem applied to `taylorWithinEval f n (Icc a b) · x` over the ordered
interval `[min x₀ x, max x₀ x] ⊆ Icc a b` (so the intermediate point is interior). -/
private lemma taylorWithin_Icc_lagrange {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f (Set.Icc a b)) {x₀ x : ℝ}
    (hx₀ : x₀ ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b) (hne : x₀ ≠ x) :
    ∃ ξ ∈ Set.Ioo (min x₀ x) (max x₀ x),
      f x - taylorWithinEval f n (Set.Icc a b) x₀ x
        = iteratedDerivWithin (n + 1) f (Set.Icc a b) ξ * (x - x₀) ^ (n + 1)
            / (Nat.factorial (n + 1) : ℝ) := by
  have hsub : Set.Icc (min x₀ x) (max x₀ x) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc (le_min hx₀.1 hx.1) (max_le hx₀.2 hx.2)
  have hlt : min x₀ x < max x₀ x := by
    rcases lt_or_gt_of_ne hne with h | h
    · rwa [min_eq_left h.le, max_eq_right h.le]
    · rwa [min_eq_right h.le, max_eq_left h.le]
  have hIoo : Set.Ioo (min x₀ x) (max x₀ x) ⊆ Set.Ioo a b := fun c hc =>
    ⟨lt_of_le_of_lt (le_min hx₀.1 hx.1) hc.1, lt_of_lt_of_le hc.2 (max_le hx₀.2 hx.2)⟩
  have hu : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hfn : ContDiffOn ℝ n f (Set.Icc a b) := hf.of_le (by exact_mod_cast n.le_succ)
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.Icc a b)) (Set.Ioo a b) :=
    (hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast n.lt_succ_self) hu).mono
      Set.Ioo_subset_Icc_self
  set F : ℝ → ℝ := fun c => taylorWithinEval f n (Set.Icc a b) c x with hFdef
  set F' : ℝ → ℝ :=
    fun c => ((Nat.factorial n : ℝ)⁻¹ * (x - c) ^ n) • iteratedDerivWithin (n + 1) f (Set.Icc a b) c
    with hF'def
  set G : ℝ → ℝ := fun c => (x - c) ^ (n + 1) with hGdef
  set G' : ℝ → ℝ := fun c => -((n : ℝ) + 1) * (x - c) ^ n with hG'def
  have hFcont : ContinuousOn F (Set.Icc (min x₀ x) (max x₀ x)) :=
    (continuousOn_taylorWithinEval hu hfn).mono hsub
  have hFderiv : ∀ c ∈ Set.Ioo (min x₀ x) (max x₀ x), HasDerivAt F (F' c) c :=
    fun c hc => taylorWithinEval_hasDerivAt_Ioo x hab (hIoo hc) hfn hf'
  have hGcont : ContinuousOn G (Set.Icc (min x₀ x) (max x₀ x)) := by
    apply Continuous.continuousOn; fun_prop
  have hGderiv : ∀ c ∈ Set.Ioo (min x₀ x) (max x₀ x), HasDerivAt G (G' c) c := by
    intro c _
    have h := ((hasDerivAt_id c).const_sub x).pow (n + 1)
    simp only [id_eq, Nat.add_sub_cancel] at h
    rw [hGdef, hG'def]; convert! h using 1; push_cast; ring
  obtain ⟨ξ, hξ, hmvt⟩ :=
    exists_ratio_hasDerivAt_eq_ratio_slope F F' hlt hFcont hFderiv G G' hGcont hGderiv
  refine ⟨ξ, hξ, ?_⟩
  have hξx : ξ ≠ x := by
    rcases le_or_gt x₀ x with h | h
    · rw [max_eq_right h] at hξ; exact ne_of_lt hξ.2
    · rw [min_eq_right h.le] at hξ; exact (ne_of_lt hξ.1).symm
  have hpne : (x - ξ) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hξx))
  have hnf : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfac : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * Nat.factorial n := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hkey : (f x - taylorWithinEval f n (Set.Icc a b) x₀ x) * ((n : ℝ) + 1)
      = (x - x₀) ^ (n + 1) * ((Nat.factorial n : ℝ))⁻¹
          * iteratedDerivWithin (n + 1) f (Set.Icc a b) ξ := by
    apply mul_left_cancel₀ hpne
    rcases le_or_gt x₀ x with h | h
    · simp only [hFdef, hF'def, hGdef, hG'def, max_eq_right h, min_eq_left h, sub_self,
        zero_pow (Nat.succ_ne_zero n), taylorWithinEval_self, smul_eq_mul] at hmvt
      linear_combination hmvt
    · simp only [hFdef, hF'def, hGdef, hG'def, max_eq_left h.le, min_eq_right h.le, sub_self,
        zero_pow (Nat.succ_ne_zero n), taylorWithinEval_self, smul_eq_mul] at hmvt
      linear_combination -hmvt
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), hfac]
  have hk := hkey
  field_simp at hk
  linear_combination hk

/-- **Taylor remainder bound over a Hölder class on an interval**: for `f ∈ Σ(β, L)` on
`[a, b]` and `x, y ∈ [a, b]`,
`|f(y) − ∑_{j≤ℓ} f⁽ʲ⁾(x)(y−x)ʲ/j!| ≤ (L/ℓ!)·|y−x|^β` (derivatives within `[a, b]`). -/
theorem MemHolderOn.taylor_remainder_abs_le_Icc {β L a b : ℝ}
    -- LEAN-ONLY: nondegenerate interval, so `Icc a b` has unique differentiability
    (hab : a < b)
    -- USER-INPUT: positive smoothness and Hölder constant; classical class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemHolderOn β L f (Set.Icc a b))
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |f y - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDerivWithin j f (Set.Icc a b) x * (y - x) ^ j / (Nat.factorial j : ℝ)|
      ≤ L / (Nat.factorial (holderIndex β) : ℝ) * |y - x| ^ β := by
  rcases eq_or_ne y x with rfl | hyx
  · -- `y = x`: both sides vanish.
    have hsum : (∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDerivWithin j f (Set.Icc a b) y * (y - y) ^ j / (Nat.factorial j : ℝ)) = f y := by
      rw [Finset.sum_eq_single 0]
      · simp [iteratedDerivWithin_zero]
      · intro j _ hj; rw [sub_self]; simp [zero_pow hj]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
    rw [hsum, sub_self, abs_zero]
    exact mul_nonneg (div_nonneg hL (by positivity)) (Real.rpow_nonneg (abs_nonneg _) _)
  rcases Nat.eq_zero_or_pos (holderIndex β) with hℓ0 | hℓpos
  · -- `ℓ = 0`: the interval Hölder condition itself.
    have hsum : (∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDerivWithin j f (Set.Icc a b) x * (y - x) ^ j / (Nat.factorial j : ℝ)) = f x := by
      rw [hℓ0, zero_add, Finset.sum_range_one]; simp [iteratedDerivWithin_zero]
    rw [hsum, hℓ0]
    have hh := hf.deriv_holder y hy x hx
    rw [hℓ0] at hh
    simp only [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero, Nat.factorial_zero,
      Nat.cast_one, div_one] at hh ⊢
    exact hh
  · -- `ℓ ≥ 1`, `y ≠ x`: two-sided Taylor–Lagrange, then the Hölder bound.
    obtain ⟨m, hm⟩ : ∃ m, holderIndex β = m + 1 :=
      ⟨holderIndex β - 1, (Nat.succ_pred_eq_of_pos hℓpos).symm⟩
    have hfC : ContDiffOn ℝ (m + 1) f (Set.Icc a b) := by
      have h := hf.contDiffOn; rw [hm] at h; exact_mod_cast h
    obtain ⟨ξ, hξ, hid⟩ := taylorWithin_Icc_lagrange hab hfC hx hy (Ne.symm hyx)
    have hξab : ξ ∈ Set.Icc a b := ⟨le_of_lt (lt_of_le_of_lt (le_min hx.1 hy.1) hξ.1),
      le_of_lt (lt_of_lt_of_le hξ.2 (max_le hx.2 hy.2))⟩
    have hξIcc1 : min x y ≤ ξ := le_of_lt hξ.1
    have hξIcc2 : ξ ≤ max x y := le_of_lt hξ.2
    have hdist : |ξ - x| ≤ |y - x| := by
      have hyxdist : |y - x| = max x y - min x y := by
        rcases le_or_gt x y with h | h
        · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (by linarith)]
        · rw [max_eq_left h.le, min_eq_right h.le, abs_of_nonpos (by linarith)]; ring
      rw [hyxdist, abs_le]
      exact ⟨by linarith [min_le_left x y, le_max_left x y],
             by linarith [min_le_left x y, le_max_left x y]⟩
    have hbridge : (∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDerivWithin j f (Set.Icc a b) x * (y - x) ^ j / (Nat.factorial j : ℝ))
        = taylorWithinEval f m (Set.Icc a b) x y
          + iteratedDerivWithin (m + 1) f (Set.Icc a b) x * (y - x) ^ (m + 1)
              / (Nat.factorial (m + 1) : ℝ) := by
      rw [hm, Finset.sum_range_succ, taylor_within_apply f m (Set.Icc a b) x y]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_eq_mul]; ring
    have hdiff : f y - (∑ j ∈ Finset.range (holderIndex β + 1),
          iteratedDerivWithin j f (Set.Icc a b) x * (y - x) ^ j / (Nat.factorial j : ℝ))
        = (iteratedDerivWithin (m + 1) f (Set.Icc a b) ξ
              - iteratedDerivWithin (m + 1) f (Set.Icc a b) x)
            * (y - x) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
      rw [hbridge]; linear_combination hid
    have hexp : (0 : ℝ) < β - ((m : ℝ) + 1) := by
      have h := sub_holderIndex_pos hβ; rw [hm] at h; push_cast at h; exact h
    have hA : |iteratedDerivWithin (m + 1) f (Set.Icc a b) ξ
          - iteratedDerivWithin (m + 1) f (Set.Icc a b) x|
        ≤ L * |y - x| ^ (β - ((m : ℝ) + 1)) := by
      have hh := hf.deriv_holder ξ hξab x hx
      rw [hm] at hh; push_cast at hh
      refine hh.trans ?_
      apply mul_le_mul_of_nonneg_left _ hL
      exact Real.rpow_le_rpow (abs_nonneg _) hdist (le_of_lt hexp)
    have hfacpos : (0 : ℝ) < (Nat.factorial (m + 1) : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hne0 : y - x ≠ 0 := sub_ne_zero.mpr hyx
    rw [hdiff, abs_div, abs_mul, abs_pow, abs_of_pos hfacpos, hm]
    calc |iteratedDerivWithin (m + 1) f (Set.Icc a b) ξ
              - iteratedDerivWithin (m + 1) f (Set.Icc a b) x|
            * |y - x| ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)
        ≤ (L * |y - x| ^ (β - ((m : ℝ) + 1))) * |y - x| ^ (m + 1)
            / (Nat.factorial (m + 1) : ℝ) := by gcongr
      _ = L / (Nat.factorial (m + 1) : ℝ) * |y - x| ^ β := by
          have hsplit : |y - x| ^ (m + 1) * |y - x| ^ (β - ((m : ℝ) + 1)) = |y - x| ^ β := by
            have h := abs_rpow_split (β := β) hne0 (m + 1); push_cast at h; exact h
          rw [← hsplit]; ring

/-- **Polynomial-growth envelope of a global Hölder function**: with `ℓ = holderIndex β`,
`|f(x₀+t)| ≤ ∑_{j≤ℓ} |f⁽ʲ⁾(x₀)|·|t|ʲ/j! + (L/ℓ!)·|t|^β`. Used to derive integrability of
kernel-weighted compositions `u ↦ K(u)·f(x₀+uh)` from the kernel's moment integrability. -/
theorem MemHolder.abs_le_growth {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemHolder β L f) (x₀ t : ℝ) :
    |f (x₀ + t)| ≤ (∑ j ∈ Finset.range (holderIndex β + 1),
        |iteratedDeriv j f x₀| * |t| ^ j / (Nat.factorial j : ℝ))
      + L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
  set S := ∑ j ∈ Finset.range (holderIndex β + 1),
      iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ) with hS
  have h1 : |f (x₀ + t) - S| ≤ L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β :=
    hf.taylor_remainder_abs_le hβ hL x₀ t
  have h2 : |S| ≤ ∑ j ∈ Finset.range (holderIndex β + 1),
      |iteratedDeriv j f x₀| * |t| ^ j / (Nat.factorial j : ℝ) := by
    rw [hS]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl (fun j _ => ?_))
    rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
  calc |f (x₀ + t)| = |(f (x₀ + t) - S) + S| := by congr 1; ring
    _ ≤ |f (x₀ + t) - S| + |S| := abs_add_le _ _
    _ ≤ (∑ j ∈ Finset.range (holderIndex β + 1),
          |iteratedDeriv j f x₀| * |t| ^ j / (Nat.factorial j : ℝ))
        + L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
        rw [add_comm (|f (x₀ + t) - S|)]; exact add_le_add h2 h1

end StatLean.NonparametricStatistics
