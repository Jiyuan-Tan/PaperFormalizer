module
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Gilbert–Varshamov packing of the binary hypercube

A Chapter-5 metric-entropy prerequisite for the local-packing minimax lower bounds: the binary
hypercube $\{0,1\}^m$ contains a subset $T$ that is $1/4$-separated in the rescaled Hamming
metric and has exponentially large cardinality. Concretely, there exists $T \subseteq \{0,1\}^m$
whose elements are pairwise at Hamming distance at least $m/4$ and with
$$\log |T| \;\ge\; \tfrac{m}{10},$$
equivalently $\log M_H(1/4;\{0,1\}^m) \ge m/10$ for the $1/4$-packing number $M_H$. This is the
Gilbert–Varshamov bound. It underlies the local packings used in Examples 15.11 and 15.15.

The constant $1/10$ in the cardinality lower bound is the *provable slack* version of the bound;
the textbook's Eq. (5.3) states the qualitative claim that the log-packing number grows linearly
in $m$, and the binary-entropy heart of the argument is captured here through an explicit,
machine-checkable constant rather than the asymptotic $H_2(1/4)$ form.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.3, Eq. (5.3)
(used in Chapter 15, §15.2.2 / §15.3.3, Examples 15.11 and 15.15).

**Proof formalization notes.** The argument is assembled from one combinatorial volume bound plus a
maximal-set covering argument:

* *Hamming-ball volume bound* (`hamming_ball_card_le`): the number of points of $\{0,1\}^m$ within
  Hamming distance $< m/4$ of a fixed center is at most $\exp\!\big(\tfrac{59}{100}\,m\big)$. The
  proof is a Chernoff bound on the binomial volume: with $k = \lfloor m/4\rfloor$, every point $y$
  of the ball satisfies $1 \le 3^k (1/3)^{d_H(t,y)}$, and summing the right-hand side over the
  whole cube factorises over coordinates to $3^k(1+1/3)^m = 3^k(4/3)^m$. The numeric bound
  $3^k(4/3)^m \le \exp(\tfrac{59}{100} m)$ reduces, after taking logs, to
  $2\log 2 - \tfrac34\log 3 \le \tfrac{59}{100}$, which holds since $\log 3 \ge \tfrac{23}{15}\log 2$
  (from $2^{23} \le 3^{15}$) and $\log 2 \le 0.6931471808$. The constant $59/100$ is a provable
  slack above the true binary entropy $H_2(1/4) \approx 0.5623$ nats.
* *Covering / counting* (`gilbert_varshamov`, exported as `exists_hamming_packing`): take a
  *maximal* $m/4$-separated subset $T$. By maximality its radius-$m/4$ Hamming balls cover the cube,
  so $2^m \le |T|\cdot \mathrm{vol(ball)}$. Combined with the volume bound and $2^m = \exp(m\log 2)$
  with $\log 2 \ge 69/100 = 1/10 + 59/100$, this yields $\exp(m/10) \le |T|$, hence
  $m/10 \le \log|T|$. The $m=0$ edge case is handled separately with the singleton cube.

The whole argument is discharged with no `sorry`; the only constant that deviates from the book is
the explicit $1/10$ rate (vs. the book's asymptotic statement), chosen for machine-checkable
numerics.

**Bibliographic comments.** The bound originates independently with E. N. Gilbert, "A comparison of
signalling alphabets", *Bell System Technical Journal* **31** (1952), 504–522, and R. R. Varshamov,
"Estimate of the number of signals in error correcting codes", *Doklady Akademii Nauk SSSR* **117**
(1957), 739–741. Gilbert proved the existence of codes meeting the volume (sphere-covering) lower
bound on the size of a code with prescribed minimum distance; Varshamov sharpened the construction
to linear codes via a parity-check argument. The greedy/maximal-packing form used here (a maximal
separated set whose balls cover the space) is the standard textbook rendering of Gilbert's covering
argument; Wainwright's Example 5.3 specializes it to the rescaled Hamming metric on $\{0,1\}^m$ for
use in minimax lower bounds.
-/

open scoped ENNReal

open Finset

namespace StatLean.Minimaxity

/-- **Binary-entropy Hamming-ball volume bound** (the genuine combinatorial heart of
Gilbert–Varshamov, Wainwright Ex 5.3). The number of points of `{0,1}^m` within Hamming distance
`< m/4` of a fixed center `t` is at most `exp((59/100)·m)`. The constant `59/100` is a provable
slack above the true binary entropy `H₂(1/4) ≈ 0.5623` (in nats).

Proof is a Chernoff bound on the binomial volume: with `k = ⌊m/4⌋`, every point `y` of the ball
has `hammingDist t y ≤ k`, so `1 ≤ 3^k · (1/3)^{hammingDist t y}`, and summing the right-hand side
over the *whole* cube factorises (over coordinates) to `3^k · (1 + 1/3)^m = 3^k (4/3)^m`. The
numeric bound `3^k (4/3)^m ≤ exp((59/100)m)` reduces, after taking logs, to
`2·log 2 − (3/4)·log 3 ≤ 59/100`, which holds since `log 3 ≥ (23/15)·log 2` (from `2^23 ≤ 3^15`)
and `log 2 ≤ 0.6931471808`. -/
private theorem hamming_ball_card_le (m : ℕ) (t : Fin m → Bool) :
    ((univ.filter (fun y : Fin m → Bool => 4 * hammingDist t y < m)).card : ℝ)
      ≤ Real.exp ((59 / 100 : ℝ) * m) := by
  classical
  set k := m / 4 with hk
  -- The cube sum of `(1/3)^{hammingDist t y}` factorises over coordinates to `(4/3)^m`.
  have hfact : ∑ y : Fin m → Bool, (1 / 3 : ℝ) ^ (hammingDist t y) = (4 / 3 : ℝ) ^ m := by
    have hpt : ∀ y : Fin m → Bool, (1 / 3 : ℝ) ^ (hammingDist t y)
        = ∏ i : Fin m, (1 / 3 : ℝ) ^ (if t i ≠ y i then 1 else 0) := by
      intro y
      rw [Finset.prod_pow_eq_pow_sum, ← Finset.card_filter]; rfl
    simp_rw [hpt]
    rw [show (univ : Finset (Fin m → Bool)) = Fintype.piFinset (fun _ => univ) from
          (Fintype.piFinset_univ).symm,
      ← Finset.prod_univ_sum (fun _ => (univ : Finset Bool))
          (fun (i : Fin m) (b : Bool) => (1 / 3 : ℝ) ^ (if t i ≠ b then 1 else 0))]
    have hinner : ∀ i : Fin m,
        ∑ b : Bool, (1 / 3 : ℝ) ^ (if t i ≠ b then 1 else 0) = 4 / 3 := by
      intro i; cases t i <;> simp <;> norm_num
    rw [Finset.prod_congr rfl (fun i _ => hinner i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  -- Bound the ball cardinality by the cube sum of `3^k (1/3)^{hammingDist t y}`.
  have hcard_le : ((univ.filter (fun y : Fin m → Bool => 4 * hammingDist t y < m)).card : ℝ)
      ≤ ∑ y : Fin m → Bool, (3 : ℝ) ^ k * (1 / 3 : ℝ) ^ (hammingDist t y) := by
    have h1 : ((univ.filter (fun y : Fin m → Bool => 4 * hammingDist t y < m)).card : ℝ)
        = ∑ _y ∈ univ.filter (fun y : Fin m → Bool => 4 * hammingDist t y < m), (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones]; push_cast; rfl
    rw [h1]
    refine le_trans (Finset.sum_le_sum (fun y hy => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun y _ _ => by positivity))
    rw [Finset.mem_filter] at hy
    have hhdk : hammingDist t y ≤ k := by
      rw [hk, Nat.le_div_iff_mul_le (by norm_num)]; omega
    have h3 : (3 : ℝ) ^ (hammingDist t y) ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hhdk
    have hpos : (0 : ℝ) < 3 ^ (hammingDist t y) := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    exact (one_le_div₀ hpos).2 h3
  -- Numeric tail: `3^k (4/3)^m ≤ exp((59/100) m)`.
  have hnum : (3 : ℝ) ^ k * (4 / 3) ^ m ≤ Real.exp ((59 / 100 : ℝ) * m) := by
    rw [← Real.exp_log (show (0 : ℝ) < 3 ^ k * (4 / 3) ^ m by positivity)]
    apply Real.exp_le_exp.2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hlog43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [hlog43]
    have hlog3lb : (23 / 15 : ℝ) * Real.log 2 ≤ Real.log 3 := by
      have h : (2 : ℝ) ^ 23 ≤ 3 ^ 15 := by norm_num
      have hh := Real.log_le_log (by positivity) h
      rw [Real.log_pow, Real.log_pow] at hh; push_cast at hh; linarith
    have hlog2ub : Real.log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
    have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hk4 : (k : ℝ) * 4 ≤ m := by
      have := Nat.div_mul_le_self m 4; rw [← hk] at this; exact_mod_cast this
    have hmk : (0 : ℝ) ≤ (m : ℝ) - k := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hm4k : (0 : ℝ) ≤ (m : ℝ) - 4 * k := by linarith
    have hl3 : (0 : ℝ) ≤ Real.log 3 - (23 / 15) * Real.log 2 := by linarith
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hmk hl3, mul_nonneg hm4k hlog2nn, mul_nonneg hmnn hlog2nn,
      mul_le_mul_of_nonneg_left hlog2ub hmnn]
  calc ((univ.filter (fun y : Fin m → Bool => 4 * hammingDist t y < m)).card : ℝ)
      ≤ ∑ y : Fin m → Bool, (3 : ℝ) ^ k * (1 / 3 : ℝ) ^ (hammingDist t y) := hcard_le
    _ = (3 : ℝ) ^ k * (4 / 3) ^ m := by rw [← Finset.mul_sum, hfact]
    _ ≤ Real.exp ((59 / 100 : ℝ) * m) := hnum

/-- Gilbert–Varshamov / binary-entropy volume bound (Wainwright Ex 5.3, Eq. (5.3)).
Take a *maximal* `m/4`-separated subset `T ⊆ {0,1}^m`. By maximality its radius-`m/4` Hamming balls
cover the cube, so `2^m ≤ |T| · vol(ball)`. The binary-entropy volume bound
`hamming_ball_card_le` gives `vol(ball) ≤ exp((59/100)·m)`, and since `2^m = exp(m·log 2)` with
`log 2 ≥ 69/100 = 1/10 + 59/100`, we get `exp(m/10) ≤ |T|`, hence `m/10 ≤ log |T|`. The entire
argument is discharged here modulo the single named volume debt `hamming_ball_card_le`. -/
private theorem gilbert_varshamov (m : ℕ) :
    ∃ T : Finset (Fin m → Bool),
      (m / 10 : ℝ) ≤ Real.log T.card ∧
      ∀ α ∈ T, ∀ β ∈ T, α ≠ β → (m / 4 : ℝ) ≤ (hammingDist α β : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `m = 0`: the singleton cube `{()}` works; `m/10 = 0 = log 1`, separation is vacuous.
    subst hm0
    refine ⟨univ, ?_, ?_⟩
    · have h1 : (univ : Finset (Fin 0 → Bool)).card = 1 := by simp
      rw [h1]; simp
    · intro a _ b _ hab; exact absurd (funext fun i => i.elim0) hab
  · -- `m ≥ 1`: a maximal `m/4`-separated subset of the cube.
    obtain ⟨T, hT, hTmax⟩ := Finset.exists_max_image
      ((univ : Finset (Fin m → Bool)).powerset.filter
        (fun S => ∀ a ∈ S, ∀ b ∈ S, a ≠ b → m ≤ 4 * hammingDist a b))
      Finset.card ⟨∅, by simp⟩
    obtain ⟨_, hTsep⟩ := Finset.mem_filter.1 hT
    -- Covering: maximality forces every point within Hamming distance `< m/4` of some `t ∈ T`.
    have hcover : ∀ x : Fin m → Bool, ∃ t ∈ T, 4 * hammingDist x t < m := by
      intro x
      by_cases hx : x ∈ T
      · exact ⟨x, hx, by simpa [hammingDist_self] using hmpos⟩
      · have hins_card : (insert x T).card = T.card + 1 := Finset.card_insert_of_notMem hx
        have hnotsep : ¬ (∀ a ∈ insert x T, ∀ b ∈ insert x T, a ≠ b → m ≤ 4 * hammingDist a b) := by
          intro hsep'
          have hmem : (insert x T) ∈ (univ : Finset (Fin m → Bool)).powerset.filter
              (fun S => ∀ a ∈ S, ∀ b ∈ S, a ≠ b → m ≤ 4 * hammingDist a b) :=
            Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (by simp), hsep'⟩
          have := hTmax _ hmem
          rw [hins_card] at this; omega
        simp only [not_forall, not_le, exists_prop] at hnotsep
        obtain ⟨a, ha, b, hb, hab, hlt⟩ := hnotsep
        rcases Finset.mem_insert.1 ha with rfl | haT
        · rcases Finset.mem_insert.1 hb with rfl | hbT
          · exact absurd rfl hab
          · exact ⟨b, hbT, hlt⟩
        · rcases Finset.mem_insert.1 hb with rfl | hbT
          · exact ⟨a, haT, by rwa [hammingDist_comm] at hlt⟩
          · have := hTsep a haT b hbT hab; omega
    -- Covering inclusion of the cube by the Hamming balls around `T`.
    have hsub : (univ : Finset (Fin m → Bool)) ⊆
        T.biUnion (fun t => univ.filter (fun y => 4 * hammingDist t y < m)) := by
      intro x _
      obtain ⟨t, htT, hxt⟩ := hcover x
      rw [Finset.mem_biUnion]
      exact ⟨t, htT, Finset.mem_filter.2 ⟨Finset.mem_univ x, by rwa [hammingDist_comm] at hxt⟩⟩
    -- Counting: `2^m = |cube| ≤ |T| · exp((59/100)m)`.
    have hcardcube : Fintype.card (Fin m → Bool) = 2 ^ m := by
      simp [Fintype.card_fin]
    have hcount : (2 : ℝ) ^ m ≤ T.card * Real.exp ((59 / 100 : ℝ) * m) := by
      have hnat : Fintype.card (Fin m → Bool)
          ≤ ∑ t ∈ T, (univ.filter (fun y : Fin m → Bool => 4 * hammingDist t y < m)).card := by
        rw [← Finset.card_univ]
        exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
      calc (2 : ℝ) ^ m = (Fintype.card (Fin m → Bool) : ℝ) := by rw [hcardcube]; norm_cast
        _ ≤ (∑ t ∈ T,
              (univ.filter (fun y : Fin m → Bool => 4 * hammingDist t y < m)).card : ℕ) := by
              exact_mod_cast hnat
        _ = ∑ t ∈ T,
              ((univ.filter (fun y : Fin m → Bool => 4 * hammingDist t y < m)).card : ℝ) := by
              push_cast; rfl
        _ ≤ ∑ _t ∈ T, Real.exp ((59 / 100 : ℝ) * m) :=
              Finset.sum_le_sum (fun t _ => hamming_ball_card_le m t)
        _ = T.card * Real.exp ((59 / 100 : ℝ) * m) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    refine ⟨T, ?_, ?_⟩
    · -- `exp(m/10) ≤ |T|`, hence `m/10 ≤ log |T|`.
      have hexp_pos : (0 : ℝ) < Real.exp ((59 / 100 : ℝ) * m) := Real.exp_pos _
      have h2 : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hsplit : Real.exp ((m : ℝ) / 10) * Real.exp ((59 / 100 : ℝ) * m) ≤ (2 : ℝ) ^ m := by
        rw [← Real.exp_add, h2]
        apply Real.exp_le_exp.2
        nlinarith [Real.log_two_gt_d9, Nat.cast_nonneg (α := ℝ) m]
      have hmul : Real.exp ((m : ℝ) / 10) * Real.exp ((59 / 100 : ℝ) * m)
          ≤ (T.card : ℝ) * Real.exp ((59 / 100 : ℝ) * m) := le_trans hsplit hcount
      have hkey : Real.exp ((m : ℝ) / 10) ≤ (T.card : ℝ) :=
        le_of_mul_le_mul_right hmul hexp_pos
      have := Real.log_le_log (Real.exp_pos _) hkey
      rwa [Real.log_exp] at this
    · -- Separation in the rescaled metric.
      intro α hα β hβ hαβ
      have h := hTsep α hα β hβ hαβ
      have hcast : (m : ℝ) ≤ 4 * (hammingDist α β : ℝ) := by exact_mod_cast h
      linarith

/-- **Gilbert–Varshamov bound** (Wainwright Example 5.3, Eq. (5.3)): for every `m`, the binary
hypercube `{0,1}^m` contains a `1/4`-separated set (in the rescaled Hamming metric) of cardinality
at least `e^{m/10}` — equivalently a set `T` with `log |T| ≥ m/10` whose elements are pairwise at
Hamming distance `≥ m/4`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses),
Example 5.3, Eq. (5.3). -/
theorem exists_hamming_packing (m : ℕ) :
    ∃ T : Finset (Fin m → Bool),
      (m / 10 : ℝ) ≤ Real.log T.card ∧
      ∀ α ∈ T, ∀ β ∈ T, α ≠ β → (m / 4 : ℝ) ≤ (hammingDist α β : ℝ) :=
  gilbert_varshamov m

end StatLean.Minimaxity
