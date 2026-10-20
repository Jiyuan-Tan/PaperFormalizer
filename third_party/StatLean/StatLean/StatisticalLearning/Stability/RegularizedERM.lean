module
public import StatLean.StatisticalLearning.Stability.Generalization

@[expose] public section

/-!
# Tikhonov regularization is a stabilizer

The Lipschitz track of SSBD §13.3–§13.4: strong convexity of the Tikhonov
objective (SSBD Lemma 13.5, parts 1–3), the RLM sensitivity bound
`‖A(S^{(i)}) − A(S)‖ ≤ 2ρ/(λn)` (SSBD Eqs. (13.7)–(13.11)), the pointwise and
on-average stability rate `2ρ²/(λn)` (SSBD Corollary 13.6), the oracle
inequality `E[L_D(A(S))] ≤ L_D(wStar) + λ‖wStar‖² + 2ρ²/(λn)` (SSBD Corollary
13.8), and the tuned rate `ρB√(8/n)` at `λ = √(2ρ²/(B²n))` for
convex-Lipschitz-bounded problems (SSBD Corollary 13.9).

**Reference.** SSBD Ch. 13 (Definitions 13.3/13.4, Lemma 13.5, Corollaries
13.6, 13.8, 13.9); Ch. 12 (Definition 12.12). Transcriptions:
`notes/statistical_learning/book_statements/ch12-13.md`.

**Formalization notes.** The smooth-loss track (Corollaries 13.7/13.10/13.11,
the `48β` constants) is excluded from Round 1. Hypotheses are `W` a real
inner-product space, loss convex in `w` for each `z` (`ConvexOn ℝ univ`) and
globally `ρ`-Lipschitz in `w`; the RLM selector is data (`IsRLMMin` per
sample). Lemma 13.5(1) is the exact inner-product identity
`‖aw + bu‖² = a‖w‖² + b‖u‖² − ab‖w − u‖²` (`a + b = 1`); 13.5(3) needs no
limits — instantiate the strong-convexity inequality and let `a ↓ 0` via
`le_of_forall_pos_le_add`-style bookkeeping.
-/

open MeasureTheory
open scoped ENNReal BigOperators RealInnerProductSpace

namespace StatLean.StatisticalLearning

variable {Z : Type*} [MeasurableSpace Z] {W : Type*} [NormedAddCommGroup W]
  [InnerProductSpace ℝ W] {n : ℕ} {ℓ : W → Z → ℝ} {lam ρ : ℝ}

/-- **SSBD Lemma 13.5(1)**: `w ↦ λ‖w‖²` is `2λ`-strongly convex (an exact
inner-product identity, no inequality slack). -/
theorem stronglyConvexWith_smul_norm_sq (hlam : 0 ≤ lam) :
    StronglyConvexWith (2 * lam) (fun w : W => lam * ‖w‖ ^ 2) := by
  intro w u a b ha hb hab
  -- the exact parallelogram-type identity for a convex combination
  have hexp : ‖a • w + b • u‖ ^ 2
      = a ^ 2 * ‖w‖ ^ 2 + 2 * (a * b) * ⟪w, u⟫ + b ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hsub : ‖w - u‖ ^ 2 = ‖w‖ ^ 2 - 2 * ⟪w, u⟫ + ‖u‖ ^ 2 := norm_sub_sq_real w u
  have hid : ‖a • w + b • u‖ ^ 2
      = a * ‖w‖ ^ 2 + b * ‖u‖ ^ 2 - a * b * ‖w - u‖ ^ 2 := by
    rw [hexp, hsub]
    have ha' : a = 1 - b := by linarith
    rw [ha']
    ring
  show lam * ‖a • w + b • u‖ ^ 2 ≤
    a * (lam * ‖w‖ ^ 2) + b * (lam * ‖u‖ ^ 2) - 2 * lam / 2 * (a * b) * ‖w - u‖ ^ 2
  rw [hid]
  have hring : lam * (a * ‖w‖ ^ 2 + b * ‖u‖ ^ 2 - a * b * ‖w - u‖ ^ 2)
      = a * (lam * ‖w‖ ^ 2) + b * (lam * ‖u‖ ^ 2) -
        2 * lam / 2 * (a * b) * ‖w - u‖ ^ 2 := by ring
  linarith

/-- **SSBD Lemma 13.5(2)**: adding a convex function preserves `λ`-strong
convexity. -/
theorem StronglyConvexWith.add_convexOn {f g : W → ℝ}
    (hf : StronglyConvexWith lam f)
    -- USER-INPUT: `g` convex; SSBD Lemma 13.5(2)
    (hg : ConvexOn ℝ Set.univ g) :
    StronglyConvexWith lam (fun w => f w + g w) := by
  intro w u a b ha hb hab
  have h1 := hf w u a b ha hb hab
  have h2 := hg.2 (Set.mem_univ w) (Set.mem_univ u) ha hb hab
  simp only [smul_eq_mul] at h2
  show f (a • w + b • u) + g (a • w + b • u) ≤
    a * (f w + g w) + b * (f u + g u) - lam / 2 * (a * b) * ‖w - u‖ ^ 2
  nlinarith [h1, h2]

/-- **SSBD Lemma 13.5(3)** (quadratic growth at a minimizer): if `f` is
`λ`-strongly convex and `u` is a global minimizer, then
`f(w) − f(u) ≥ (λ/2)‖w − u‖²`. -/
theorem StronglyConvexWith.quadratic_growth {f : W → ℝ} {u : W}
    (hf : StronglyConvexWith lam f)
    -- USER-INPUT: `u` minimizes `f`; SSBD Lemma 13.5(3)
    (hu : ∀ v, f u ≤ f v) (w : W) :
    lam / 2 * ‖w - u‖ ^ 2 ≤ f w - f u := by
  have hQ0 : (0 : ℝ) ≤ ‖w - u‖ ^ 2 := by positivity
  have hM : 0 ≤ f w - f u := by linarith [hu w]
  rcases le_or_gt lam 0 with hlam | hlam
  · nlinarith
  rcases eq_or_lt_of_le hQ0 with hq | hq
  · rw [← hq]; simpa using hM
  -- the one-parameter family of inequalities obtained from minimality at
  -- `t • w + (1 - t) • u`
  have step : ∀ t : ℝ, 0 < t → t < 1 →
      lam / 2 * ‖w - u‖ ^ 2 - t * (lam / 2 * ‖w - u‖ ^ 2) ≤ f w - f u := by
    intro t ht0 ht1
    have h := hf w u t (1 - t) ht0.le (by linarith) (by ring)
    have hmin := hu (t • w + (1 - t) • u)
    have hkey : t * (lam / 2 * (1 - t) * ‖w - u‖ ^ 2 - (f w - f u)) ≤ 0 := by
      nlinarith [h, hmin]
    have h4 : lam / 2 * (1 - t) * ‖w - u‖ ^ 2 - (f w - f u) ≤ 0 := by
      by_contra hcc
      push_neg at hcc
      nlinarith [hkey, ht0, hcc]
    nlinarith [h4]
  -- let `t ↓ 0`
  by_contra hcon
  push_neg at hcon
  set C := lam / 2 * ‖w - u‖ ^ 2 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  set M := f w - f u with hMdef
  have hd : 0 < C - M := by linarith
  have ht0 : 0 < min (1 / 2 : ℝ) ((C - M) / (2 * C)) :=
    lt_min (by norm_num) (by positivity)
  have ht1 : min (1 / 2 : ℝ) ((C - M) / (2 * C)) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hs := step _ ht0 ht1
  have hb : min (1 / 2 : ℝ) ((C - M) / (2 * C)) * C ≤ (C - M) / 2 := by
    have h1 : min (1 / 2 : ℝ) ((C - M) / (2 * C)) ≤ (C - M) / (2 * C) :=
      min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 hCpos.le
    have h3 : (C - M) / (2 * C) * C = (C - M) / 2 := by
      field_simp
    linarith [h2, h3]
  nlinarith [hs, hb]

/-- The Tikhonov objective is `2λ`-strongly convex for a convex loss
(SSBD Eq. (13.7) setup, via Lemma 13.5(1)–(2) and convexity of `L_S`). -/
theorem stronglyConvexWith_rlmObjective {s : Sample Z n}
    -- USER-INPUT: convex loss in `w`; SSBD Cor. 13.6 hypothesis
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    -- USER-INPUT: `λ > 0`; SSBD Eq. (13.2)
    (hlam : 0 < lam) :
    StronglyConvexWith (2 * lam) (rlmObjective ℓ lam s) := by
  intro w u a b ha hb hab
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  -- the empirical risk is convex: a nonnegative average of convex losses
  have hle : ∑ i, ℓ (a • w + b • u) (s i) ≤ ∑ i, (a * ℓ w (s i) + b * ℓ u (s i)) :=
    Finset.sum_le_sum fun i _ => by
      simpa [smul_eq_mul] using
        (hconv (s i)).2 (Set.mem_univ w) (Set.mem_univ u) ha hb hab
  have h2 := mul_le_mul_of_nonneg_left hle hninv
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  have hsum : empRisk ℓ s (a • w + b • u) ≤
      a * empRisk ℓ s w + b * empRisk ℓ s u := by
    simp only [empRisk]
    linarith [h2]
  -- the Tikhonov term is `2λ`-strongly convex
  have hquad := stronglyConvexWith_smul_norm_sq (W := W) hlam.le w u a b ha hb hab
  dsimp only at hquad
  show empRisk ℓ s (a • w + b • u) + lam * ‖a • w + b • u‖ ^ 2 ≤
    a * (empRisk ℓ s w + lam * ‖w‖ ^ 2) + b * (empRisk ℓ s u + lam * ‖u‖ ^ 2) -
      2 * lam / 2 * (a * b) * ‖w - u‖ ^ 2
  nlinarith [hsum, hquad]

/-- LEAN-ONLY: a Lipschitz constant is nonnegative as soon as the parameter
space has two points (SSBD Def. 12.6 takes `ρ ≥ 0` for granted). -/
private theorem lipschitz_const_nonneg [Nontrivial W] (z : Z)
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖) : 0 ≤ ρ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  have hpos : 0 < ‖a - b‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hab
  have h0 : 0 ≤ ρ * ‖a - b‖ := le_trans (abs_nonneg _) (hlip z a b)
  nlinarith

/-- LEAN-ONLY: SSBD Eq. (13.8) — the empirical risks of `S` and `S^{(i)}`
differ only through the `i`-th example. -/
private theorem empRisk_replaceOne_sub {s : Sample Z n} {i : Fin n} {z' : Z}
    (v : W) :
    (n : ℝ) * (empRisk ℓ s v - empRisk ℓ (replaceOne s i z') v) =
      ℓ v (s i) - ℓ v z' := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd i.2 (by simp [h])
    · exact Nat.cast_ne_zero.2 (by omega)
  have h1 : (fun j => ℓ v (replaceOne s i z' j))
      = Function.update (fun j => ℓ v (s j)) i (ℓ v z') := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [replaceOne]
    · simp [replaceOne, Function.update_of_ne hj]
  have e1 : ∑ j, ℓ v (replaceOne s i z' j)
      = ℓ v z' + ∑ j ∈ Finset.univ \ {i}, ℓ v (s j) := by
    rw [show (∑ j, ℓ v (replaceOne s i z' j))
        = ∑ j, Function.update (fun j => ℓ v (s j)) i (ℓ v z') j from by rw [h1]]
    exact Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => ℓ v (s j)) (ℓ v z')
  have e2 : ∑ j, ℓ v (s j) = ℓ v (s i) + ∑ j ∈ Finset.univ \ {i}, ℓ v (s j) := by
    have h2 := Finset.sum_update_of_mem (Finset.mem_univ i)
      (fun j => ℓ v (s j)) (ℓ v (s i))
    rwa [Function.update_eq_self] at h2
  simp only [empRisk]
  rw [← mul_sub, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul, e1, e2]
  ring

/-- LEAN-ONLY: the RLM sensitivity bound, with the nonnegativity of the
Lipschitz constant supplied explicitly (see `rlm_replaceOne_dist_le`). -/
private theorem rlm_replaceOne_dist_le_aux {s : Sample Z n} {i : Fin n} {z' : Z}
    {w w' : W}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    (hρ : 0 ≤ ρ) (hlam : 0 < lam)
    (hw : IsRLMMin ℓ lam s w) (hw' : IsRLMMin ℓ lam (replaceOne s i z') w')
    (hn : 1 ≤ n) :
    ‖w' - w‖ ≤ 2 * ρ / (lam * n) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- (13.7): quadratic growth of the objective at its minimizer
  have hsc : StronglyConvexWith (2 * lam) (rlmObjective ℓ lam s) :=
    stronglyConvexWith_rlmObjective hconv hlam
  have hqg : lam * ‖w' - w‖ ^ 2 ≤
      rlmObjective ℓ lam s w' - rlmObjective ℓ lam s w := by
    have := hsc.quadratic_growth hw w'
    linarith
  -- (13.8): the two objectives differ only through the `i`-th example
  have hA : (n : ℝ) * (rlmObjective ℓ lam s w' -
      rlmObjective ℓ lam (replaceOne s i z') w') = ℓ w' (s i) - ℓ w' z' := by
    rw [show rlmObjective ℓ lam s w' - rlmObjective ℓ lam (replaceOne s i z') w'
        = empRisk ℓ s w' - empRisk ℓ (replaceOne s i z') w' from by
      simp only [rlmObjective]; ring]
    exact empRisk_replaceOne_sub w'
  have hB : (n : ℝ) * (rlmObjective ℓ lam s w -
      rlmObjective ℓ lam (replaceOne s i z') w) = ℓ w (s i) - ℓ w z' := by
    rw [show rlmObjective ℓ lam s w - rlmObjective ℓ lam (replaceOne s i z') w
        = empRisk ℓ s w - empRisk ℓ (replaceOne s i z') w from by
      simp only [rlmObjective]; ring]
    exact empRisk_replaceOne_sub w
  -- (13.9): `w'` minimizes the replaced objective
  have hC : rlmObjective ℓ lam (replaceOne s i z') w' ≤
      rlmObjective ℓ lam (replaceOne s i z') w := hw' w
  -- (13.10): the Lipschitz bounds
  have hL1 : ℓ w' (s i) - ℓ w (s i) ≤ ρ * ‖w' - w‖ :=
    le_of_abs_le (hlip (s i) w' w)
  have hL2 : ℓ w z' - ℓ w' z' ≤ ρ * ‖w' - w‖ := by
    have := le_of_abs_le (hlip z' w w')
    rwa [norm_sub_rev] at this
  -- assemble (13.11)
  have i1 : (n : ℝ) * (lam * ‖w' - w‖ ^ 2) ≤
      (n : ℝ) * (rlmObjective ℓ lam s w' - rlmObjective ℓ lam s w) :=
    mul_le_mul_of_nonneg_left hqg hn0
  have i2 : (n : ℝ) * (rlmObjective ℓ lam (replaceOne s i z') w' -
      rlmObjective ℓ lam (replaceOne s i z') w) ≤ 0 := by
    nlinarith [hC, hn0]
  have i3 : (n : ℝ) * (rlmObjective ℓ lam s w' - rlmObjective ℓ lam s w)
      = ((n : ℝ) * (rlmObjective ℓ lam s w' -
            rlmObjective ℓ lam (replaceOne s i z') w'))
        - ((n : ℝ) * (rlmObjective ℓ lam s w -
            rlmObjective ℓ lam (replaceOne s i z') w))
        + ((n : ℝ) * (rlmObjective ℓ lam (replaceOne s i z') w' -
            rlmObjective ℓ lam (replaceOne s i z') w)) := by ring
  rw [hA, hB] at i3
  have hmain : (n : ℝ) * (lam * ‖w' - w‖ ^ 2) ≤ 2 * ρ * ‖w' - w‖ := by
    linarith [i1, i2, i3, hL1, hL2]
  -- divide by `‖w' - w‖`
  rcases eq_or_lt_of_le (norm_nonneg (w' - w)) with hx | hx
  · rw [← hx]
    positivity
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < lam * n)]
    nlinarith [hmain, hx]

/-- **RLM sensitivity** (SSBD Eqs. (13.7)–(13.11)): for a convex `ρ`-Lipschitz
loss, replace-one RLM minimizers are `2ρ/(λn)`-close.

The hypothesis `0 ≤ ρ` was added at the verification gate (statement repair,
2026-08-10): without it the statement is false on a trivial (subsingleton) `W`,
where `hlip` degenerates to `0 ≤ ρ·0` and carries no sign information while the
goal still asserts `0 ≤ 2ρ/(λn)` — witness `W := EuclideanSpace ℝ (Fin 0)`,
`ℓ := 0`, `ρ := -1`, `lam := 1`, `n := 1`. The book's `ρ` (SSBD Def. 12.6) is a
Lipschitz constant, hence implicitly nonnegative. -/
theorem rlm_replaceOne_dist_le {s : Sample Z n} {i : Fin n} {z' : Z}
    {w w' : W}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    -- USER-INPUT: `ρ`-Lipschitz loss in `w`; SSBD Cor. 13.6 hypothesis
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    -- USER-INPUT: `ρ ≥ 0`; SSBD Def. 12.6 (a Lipschitz constant — see
    -- docstring for why this cannot be derived from `hlip` alone)
    (hρ : 0 ≤ ρ)
    (hlam : 0 < lam)
    -- USER-INPUT: `w` is RLM on `s`, `w'` is RLM on `s^{(i)}`; SSBD §13.3
    (hw : IsRLMMin ℓ lam s w) (hw' : IsRLMMin ℓ lam (replaceOne s i z') w')
    -- USER-INPUT: at least one example; SSBD §13.2 (implicit)
    (hn : 1 ≤ n) :
    ‖w' - w‖ ≤ 2 * ρ / (lam * n) :=
  rlm_replaceOne_dist_le_aux hconv hlip hρ hlam hw hw' hn

/-- **SSBD Corollary 13.6, pointwise form**: the replace-one loss increment of
RLM is at most `2ρ²/(λn)` at every sample, index, and replacement point. -/
theorem rlm_pointwise_stability {s : Sample Z n} {i : Fin n} {z' : Z}
    {w w' : W} {z : Z}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    (hlam : 0 < lam)
    (hw : IsRLMMin ℓ lam s w) (hw' : IsRLMMin ℓ lam (replaceOne s i z') w')
    (hn : 1 ≤ n) :
    ℓ w' z - ℓ w z ≤ 2 * ρ ^ 2 / (lam * n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rcases subsingleton_or_nontrivial W with hW | hW
  · have hww : w' = w := Subsingleton.elim _ _
    rw [hww, sub_self]
    positivity
  · have hρ : 0 ≤ ρ := lipschitz_const_nonneg z hlip
    have hd := rlm_replaceOne_dist_le_aux hconv hlip hρ hlam hw hw' hn
    calc ℓ w' z - ℓ w z ≤ ρ * ‖w' - w‖ := le_of_abs_le (hlip z w' w)
      _ ≤ ρ * (2 * ρ / (lam * n)) := mul_le_mul_of_nonneg_left hd hρ
      _ = 2 * ρ ^ 2 / (lam * n) := by ring

/-- **SSBD Corollary 13.6** (Tikhonov stability): an RLM selector is
on-average-replace-one stable with rate `2ρ²/(λn)`; combined with Theorem 13.2
its expected overfitting gap obeys the same bound. Stated at fixed `n` via the
`stabilityGap`. -/
theorem rlm_stabilityGap_le (D : Measure Z) [IsProbabilityMeasure D]
    {A : Sample Z n → W}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    -- USER-INPUT: `ρ ≥ 0`; SSBD Def. 12.6 (Lipschitz constant)
    (hρ : 0 ≤ ρ)
    (hlam : 0 < lam)
    -- USER-INPUT: `A` is an RLM selector; SSBD Eq. (13.2) (argmin is data)
    (hA : ∀ s : Sample Z n, IsRLMMin ℓ lam s (A s))
    -- LEAN-ONLY: integrability of the replace-one increments (the book's
    -- expectation presupposes it)
    (hint : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z =>
        ℓ (A (replaceOne p.1 i p.2)) (p.1 i) - ℓ (A p.1) (p.1 i))
      ((sampleLaw D n).prod D))
    (hn : 1 ≤ n) :
    stabilityGap D ℓ A ≤ 2 * ρ ^ 2 / (lam * n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- each replace-one increment is pointwise below the rate
  have hbound : ∀ i : Fin n,
      ∫ p : Sample Z n × Z,
          (ℓ (A (replaceOne p.1 i p.2)) (p.1 i) - ℓ (A p.1) (p.1 i))
          ∂((sampleLaw D n).prod D) ≤ 2 * ρ ^ 2 / (lam * n) := by
    intro i
    have h1 := integral_mono (hint i) (integrable_const (2 * ρ ^ 2 / (lam * n)))
      (fun p => rlm_pointwise_stability hconv hlip hlam (hA p.1)
        (hA (replaceOne p.1 i p.2)) hn)
    simpa using h1
  have hle := Finset.sum_le_sum fun (i : Fin n) (_ : i ∈ Finset.univ) => hbound i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  have hmul := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
  simp only [stabilityGap]
  refine le_trans hmul (le_of_eq ?_)
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnpos), one_mul]

/-- **SSBD Corollary 13.8** (oracle inequality for RLM): for every competitor
`wStar`, `E_S[L_D(A(S))] ≤ L_D(wStar) + λ‖wStar‖² + 2ρ²/(λn)`. -/
theorem rlm_oracle (D : Measure Z) [IsProbabilityMeasure D]
    {A : Sample Z n → W} (wStar : W)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    (hρ : 0 ≤ ρ)
    (hlam : 0 < lam)
    (hA : ∀ s : Sample Z n, IsRLMMin ℓ lam s (A s))
    -- USER-INPUT: integrable competitor loss; SSBD Remark 3.1
    (hwStarInt : Integrable (ℓ wStar) D)
    -- LEAN-ONLY: integrability bundle for Theorem 13.2 and Eq. (13.16)
    (hint₁ : Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) p.2) ((sampleLaw D n).prod D))
    (hint₂ : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z => ℓ (A (replaceOne p.1 i p.2)) (p.1 i))
      ((sampleLaw D n).prod D))
    (hint₃ : ∀ i : Fin n, Integrable
      (fun s : Sample Z n => ℓ (A s) (s i)) (sampleLaw D n))
    (hint₄ : Integrable
      (fun s : Sample Z n => empRisk ℓ s (A s)) (sampleLaw D n))
    (hn : 1 ≤ n) :
    ∫ s, risk D ℓ (A s) ∂(sampleLaw D n) ≤
      risk D ℓ wStar + lam * ‖wStar‖ ^ 2 + 2 * ρ ^ 2 / (lam * n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfst : MeasurePreserving (Prod.fst : Sample Z n × Z → Sample Z n)
      ((sampleLaw D n).prod D) (sampleLaw D n) := measurePreserving_fst
  have hint₃' : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) (p.1 i)) ((sampleLaw D n).prod D) := by
    intro i
    simpa [Function.comp_def] using hfst.integrable_comp_of_integrable (hint₃ i)
  -- Corollary 13.6 bounds the stability gap
  have hgap : stabilityGap D ℓ A ≤ 2 * ρ ^ 2 / (lam * n) :=
    rlm_stabilityGap_le D hconv hlip hρ hlam hA
      (fun i => (hint₂ i).sub (hint₃' i)) hn
  -- (13.15): Theorem 13.2 turns the gap into the overfitting term
  have hrisk : Integrable (fun s => risk D ℓ (A s)) (sampleLaw D n) :=
    hint₁.integral_prod_left
  have h132 := integral_risk_sub_empRisk_eq_stabilityGap A hint₁ hint₂ hint₃ hn
  rw [integral_sub hrisk hint₄] at h132
  -- (13.16): the RLM objective dominates the empirical risk
  have hev : ∀ i : Fin n,
      Integrable (fun s : Sample Z n => ℓ wStar (s i)) (sampleLaw D n) := by
    intro i
    have h := (MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin n => D) i).integrable_comp_of_integrable hwStarInt
    simpa [Function.comp_def, Function.eval, sampleLaw] using h
  have hempStar : Integrable (fun s : Sample Z n => empRisk ℓ s wStar)
      (sampleLaw D n) := by
    simp only [empRisk]
    exact (integrable_finset_sum _ fun i _ => hev i).const_mul _
  have hpt : ∀ s : Sample Z n,
      empRisk ℓ s (A s) ≤ empRisk ℓ s wStar + lam * ‖wStar‖ ^ 2 := by
    intro s
    have h1 := hA s wStar
    have h2 : 0 ≤ lam * ‖A s‖ ^ 2 := by positivity
    simp only [rlmObjective] at h1
    linarith
  have hInt2 : Integrable
      (fun s : Sample Z n => empRisk ℓ s wStar + lam * ‖wStar‖ ^ 2)
      (sampleLaw D n) := by exact hempStar.add (integrable_const _)
  have hval : ∫ s, (empRisk ℓ s wStar + lam * ‖wStar‖ ^ 2) ∂(sampleLaw D n)
      = risk D ℓ wStar + lam * ‖wStar‖ ^ 2 := by
    rw [integral_add hempStar (integrable_const _), integral_empRisk hwStarInt hn,
      integral_const]
    simp
  have hmono := integral_mono hint₄ hInt2 hpt
  rw [hval] at hmono
  linarith

/-- **SSBD Corollary 13.9** (convex-Lipschitz-bounded learnability via RLM):
with `λ = √(2ρ²/(B²n))`, the RLM rule satisfies
`E_S[L_D(A(S))] ≤ inf_{‖w‖≤B} L_D(w) + ρB√(8/n)`. -/
theorem rlm_tuned_excess_risk (D : Measure Z) [IsProbabilityMeasure D]
    {A : Sample Z n → W} {B : ℝ}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    -- USER-INPUT: `ρ > 0`, `B > 0`; SSBD Def. 12.12 parameters
    (hρ : 0 < ρ) (hB : 0 < B)
    -- USER-INPUT: `A` is the RLM selector at the tuned
    -- `λ = √(2ρ²/(B²n))`; SSBD Cor. 13.9
    (hA : ∀ s : Sample Z n,
      IsRLMMin ℓ (Real.sqrt (2 * ρ ^ 2 / (B ^ 2 * n))) s (A s))
    -- USER-INPUT: integrable losses on the comparison ball; SSBD Remark 3.1
    (hint : ∀ w : W, ‖w‖ ≤ B → Integrable (ℓ w) D)
    -- LEAN-ONLY: integrability bundle as in `rlm_oracle`
    (hint₁ : Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) p.2) ((sampleLaw D n).prod D))
    (hint₂ : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z => ℓ (A (replaceOne p.1 i p.2)) (p.1 i))
      ((sampleLaw D n).prod D))
    (hint₃ : ∀ i : Fin n, Integrable
      (fun s : Sample Z n => ℓ (A s) (s i)) (sampleLaw D n))
    (hint₄ : Integrable
      (fun s : Sample Z n => empRisk ℓ s (A s)) (sampleLaw D n))
    -- LEAN-ONLY: bounded-below risk image on the ball
    (hbdd : BddBelow (risk D ℓ '' {w : W | ‖w‖ ≤ B}))
    (hn : 1 ≤ n) :
    ∫ s, risk D ℓ (A s) ∂(sampleLaw D n) ≤
      bestRisk D {w : W | ‖w‖ ≤ B} ℓ + ρ * B * Real.sqrt (8 / n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set lam₀ := Real.sqrt (2 * ρ ^ 2 / (B ^ 2 * n)) with hlam₀
  have hquot : 0 < 2 * ρ ^ 2 / (B ^ 2 * n) := by positivity
  have hlam : 0 < lam₀ := Real.sqrt_pos.mpr hquot
  have hsq : lam₀ ^ 2 = 2 * ρ ^ 2 / (B ^ 2 * n) := Real.sq_sqrt hquot.le
  -- the tuned parameter balances the two terms of the oracle inequality
  have h2r : 2 * ρ ^ 2 = lam₀ ^ 2 * (B ^ 2 * n) := by
    rw [hsq]; field_simp
  have hstep : 2 * ρ ^ 2 / (lam₀ * n) = lam₀ * B ^ 2 := by
    rw [h2r]; field_simp
  have hsq8 : Real.sqrt (8 / n) ^ 2 = 8 / n := Real.sq_sqrt (by positivity)
  have hfinal : lam₀ * B ^ 2 + lam₀ * B ^ 2 = ρ * B * Real.sqrt (8 / n) := by
    have hnn1 : (0 : ℝ) ≤ lam₀ * B ^ 2 + lam₀ * B ^ 2 := by positivity
    have hnn2 : (0 : ℝ) ≤ ρ * B * Real.sqrt (8 / n) := by positivity
    refine (sq_eq_sq₀ hnn1 hnn2).mp ?_
    have e1 : (lam₀ * B ^ 2 + lam₀ * B ^ 2) ^ 2 = 4 * lam₀ ^ 2 * B ^ 4 := by ring
    have e2 : (ρ * B * Real.sqrt (8 / n)) ^ 2 = ρ ^ 2 * B ^ 2 * (8 / n) := by
      rw [mul_pow, mul_pow, hsq8]
    rw [e1, e2, hsq]
    field_simp
    ring
  -- the oracle inequality at every competitor in the ball
  have hbound : ∀ w : W, ‖w‖ ≤ B →
      (∫ s, risk D ℓ (A s) ∂(sampleLaw D n)) - ρ * B * Real.sqrt (8 / n) ≤
        risk D ℓ w := by
    intro w hw
    have h1 := rlm_oracle D w hconv hlip hρ.le hlam hA (hint w hw) hint₁ hint₂
      hint₃ hint₄ hn
    have h2 : lam₀ * ‖w‖ ^ 2 ≤ lam₀ * B ^ 2 := by
      have : ‖w‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg w]
      exact mul_le_mul_of_nonneg_left this hlam.le
    rw [hstep] at h1
    linarith
  -- the ball is nonempty, so the infimum is a genuine lower bound
  have hne : (risk D ℓ '' {w : W | ‖w‖ ≤ B}).Nonempty :=
    ⟨risk D ℓ 0, ⟨0, by simp [hB.le], rfl⟩⟩
  have hinf := le_csInf hne (by
    rintro b ⟨w, hw, rfl⟩
    exact hbound w hw)
  simp only [bestRisk]
  linarith

end StatLean.StatisticalLearning
