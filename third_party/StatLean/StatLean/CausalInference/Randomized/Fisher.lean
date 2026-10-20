module
public import StatLean.CausalInference.Core.FinitePopulation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# The Fisher randomization test — finite-sample validity

Under the sharp null every potential outcome is known once the experiment is run, so the
statistic can be recomputed at every assignment the design could have produced. The
resulting p-value

$$p(z)=\Pr_{Z^\ast}\bigl\{T(Z^\ast)\ge T(z)\bigr\}$$

is **super-uniform** under any design: `Pr(p ≤ α) ≤ α` for every `α ≥ 0`. This is exact in
finite samples and needs no distributional assumption whatsoever — only that the design
draws uniformly from its support.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §3.2: the sharp null hypothesis
`H₀ : Yᵢ(1) = Yᵢ(0)` for all `i`, the randomization p-value eq. (3.2), and the validity
statement eq. (3.3) `Pr(p ≤ u) ≤ u` (stated as a display; the proof is left as Problem
3.1). (`Ding §3.2, eqs. (3.2)–(3.3)`.) The same test is developed in G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*,
Cambridge University Press, 2015, ch. 5. (`IR ch. 5`.)

**Proof formalization notes.**

* Validity is proved for an **arbitrary design** and an arbitrary real-valued function `g`
  of the assignment, which is stronger and simpler than the CRE-only statement: the
  argument is that `{z | p(z) ≤ α}` is an upper set for `g`, so it is contained in
  `{z | g z₀ ≤ g z}` for a `g`-minimal element `z₀` of it, and that set has probability
  exactly `p(z₀) ≤ α`. Stratified and matched-pair designs therefore inherit validity with
  no extra work.
* `0 ≤ α` is genuinely needed: for `α < 0` the event is empty and the claim would read
  `0 ≤ α`.
* The sharp null enters only through `SharpNull.observed_eq`: it makes the observed
  outcome vector — and hence the statistic value function `g` — independent of which
  assignment was realized. That step is isolated in `sharpNull_statistic_eq`.
* StatLean already has a measure-theoretic randomization test for group-invariant laws
  (`StatLean.HypothesisTesting.superUniform_randPValue`, over a `MulAction` of a finite
  group). This file is the *design-based* counterpart on a finite population; it is
  deliberately independent of that concept-layer development.

**Bibliographic comments.** R. A. Fisher, *The Design of Experiments*, Oliver & Boyd,
Edinburgh, 1935 (the lady-tasting-tea experiment). The super-uniformity argument for
discrete randomization distributions is standard; see also E. L. Lehmann and
J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer, 2005, ch. 15.
-/

namespace StatLean.CausalInference

variable {n : ℕ}

/-! ### Counting toolkit for `Design.prob`

`Design.prob` is a normalized sum of indicators over the support, so every statement below
reduces to a pointwise comparison of indicators on the support together with positivity of
the normalizing constant `(card support)⁻¹`. -/

/-- The support of a design has positive cardinality. -/
private theorem card_support_pos (D : Design n) : (0 : ℝ) < (D.support.card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr D.support_nonempty

/-- An indicator of a set at a value `1` is between `0` and `1`. -/
private theorem indicator_mem_Icc (s : Set (Assignment n)) (z : Assignment n) :
    0 ≤ Set.indicator s (fun _ => (1 : ℝ)) z ∧ Set.indicator s (fun _ => (1 : ℝ)) z ≤ 1 := by
  by_cases hz : z ∈ s
  · rw [Set.indicator_of_mem hz]; norm_num
  · rw [Set.indicator_of_notMem hz]; norm_num

/-- Probabilities are nonnegative. -/
private theorem prob_nonneg' (D : Design n) (s : Set (Assignment n)) : 0 ≤ D.prob s := by
  unfold Design.prob Design.expect
  refine mul_nonneg (le_of_lt (inv_pos.mpr (card_support_pos D)))
    (Finset.sum_nonneg fun z _ => (indicator_mem_Icc s z).1)

/-- Probabilities are at most one. -/
private theorem prob_le_one' (D : Design n) (s : Set (Assignment n)) : D.prob s ≤ 1 := by
  have hN := card_support_pos D
  unfold Design.prob Design.expect
  have hsum : ∑ z ∈ D.support, Set.indicator s (fun _ => (1 : ℝ)) z ≤ (D.support.card : ℝ) := by
    calc ∑ z ∈ D.support, Set.indicator s (fun _ => (1 : ℝ)) z
        ≤ ∑ _z ∈ D.support, (1 : ℝ) :=
          Finset.sum_le_sum fun z _ => (indicator_mem_Icc s z).2
      _ = (D.support.card : ℝ) := by simp
  calc (D.support.card : ℝ)⁻¹ * ∑ z ∈ D.support, Set.indicator s (fun _ => (1 : ℝ)) z
      ≤ (D.support.card : ℝ)⁻¹ * (D.support.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hN))
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hN)

/-- Monotonicity of `Design.prob`: only the behaviour of the two sets **on the support**
matters, since off-support assignments contribute nothing to the sum. -/
private theorem prob_mono_on_support (D : Design n) {s t : Set (Assignment n)}
    (h : ∀ z ∈ D.support, z ∈ s → z ∈ t) : D.prob s ≤ D.prob t := by
  unfold Design.prob Design.expect
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_)
    (le_of_lt (inv_pos.mpr (card_support_pos D)))
  intro z hz
  by_cases hzs : z ∈ s
  · rw [Set.indicator_of_mem hzs, Set.indicator_of_mem (h z hz hzs)]
  · rw [Set.indicator_of_notMem hzs]
    exact (indicator_mem_Icc t z).1

/-- A support element belonging to `s` forces `0 < D.prob s`. -/
private theorem prob_pos_of_mem (D : Design n) {s : Set (Assignment n)} {z : Assignment n}
    (hz : z ∈ D.support) (hzs : z ∈ s) : 0 < D.prob s := by
  have hN := card_support_pos D
  unfold Design.prob Design.expect
  refine mul_pos (inv_pos.mpr hN) ?_
  have hone : Set.indicator s (fun _ => (1 : ℝ)) z = 1 := Set.indicator_of_mem hzs _
  have hle : Set.indicator s (fun _ => (1 : ℝ)) z
      ≤ ∑ w ∈ D.support, Set.indicator s (fun _ => (1 : ℝ)) w :=
    Finset.single_le_sum (f := fun w => Set.indicator s (fun _ => (1 : ℝ)) w)
      (fun w _ => (indicator_mem_Icc s w).1) hz
  exact lt_of_lt_of_le zero_lt_one (le_trans (le_of_eq hone.symm) hle)

/-! ### Elementary properties of the p-value -/

/-- The randomization p-value is nonnegative. -/
theorem fisherPValue_nonneg (D : Design n) (g : Assignment n → ℝ) (z : Assignment n) :
    0 ≤ fisherPValue D g z :=
  prob_nonneg' D _

/-- The randomization p-value is at most one. -/
theorem fisherPValue_le_one (D : Design n) (g : Assignment n → ℝ) (z : Assignment n) :
    fisherPValue D g z ≤ 1 :=
  prob_le_one' D _

/-- The p-value at an assignment attaining the maximum statistic value is the probability
of the "at least as extreme" set, which always contains that assignment; in particular the
p-value is strictly positive on the support. -/
theorem fisherPValue_pos (D : Design n) (g : Assignment n → ℝ) {z : Assignment n}
    (hz : z ∈ D.support) :
    0 < fisherPValue D g z :=
  prob_pos_of_mem D hz (Set.mem_setOf_eq ▸ le_refl (g z))

/-- Monotonicity: a larger statistic value gives a smaller p-value. -/
theorem fisherPValue_antitone (D : Design n) (g : Assignment n → ℝ) {z z' : Assignment n}
    (h : g z ≤ g z') :
    fisherPValue D g z' ≤ fisherPValue D g z :=
  prob_mono_on_support D fun _ _ hw => le_trans h hw

/-- **Validity of the randomization test** (Ding eq. (3.3)): under any design, the
randomization p-value is super-uniform, `Pr(p ≤ α) ≤ α`. Consequently the test that
rejects when `p ≤ α` has size at most `α`, exactly, in finite samples. -/
theorem prob_fisherPValue_le (D : Design n) (g : Assignment n → ℝ) {α : ℝ}
    -- LEAN-ONLY: a nonnegative level (for `α < 0` the event is empty and the claim is false)
    (hα : 0 ≤ α) :
    D.prob {z | fisherPValue D g z ≤ α} ≤ α := by
  classical
  set T : Finset (Assignment n) := D.support.filter (fun z => fisherPValue D g z ≤ α) with hTdef
  rcases T.eq_empty_or_nonempty with hT | hT
  · -- No possible assignment is rejected: the event has probability `0 ≤ α`.
    have hzero : D.prob {z | fisherPValue D g z ≤ α} = 0 := by
      unfold Design.prob Design.expect
      have hpt : ∀ z ∈ D.support,
          Set.indicator {z | fisherPValue D g z ≤ α} (fun _ => (1 : ℝ)) z = 0 := by
        intro z hz
        have hnot : ¬ fisherPValue D g z ≤ α := by
          intro hle
          have hzT : z ∈ T := by rw [hTdef]; exact Finset.mem_filter.mpr ⟨hz, hle⟩
          rw [hT] at hzT
          simp at hzT
        exact Set.indicator_of_notMem (s := {z | fisherPValue D g z ≤ α}) hnot (fun _ => (1 : ℝ))
      rw [Finset.sum_congr rfl hpt]
      simp
    rw [hzero]
    exact hα
  · -- Otherwise the rejection event is, on the support, an upper set for `g`; a `g`-minimal
    -- rejected assignment `z₀` dominates it, and its own p-value is at most `α`.
    obtain ⟨z₀, hz₀T, hmin⟩ := T.exists_min_image g hT
    obtain ⟨-, hz₀α⟩ : z₀ ∈ D.support ∧ fisherPValue D g z₀ ≤ α := by
      rw [hTdef] at hz₀T; exact Finset.mem_filter.mp hz₀T
    calc D.prob {z | fisherPValue D g z ≤ α}
        ≤ D.prob {z' | g z₀ ≤ g z'} := by
          refine prob_mono_on_support D fun z hz hzA => ?_
          exact hmin z (by rw [hTdef]; exact Finset.mem_filter.mpr ⟨hz, hzA⟩)
      _ = fisherPValue D g z₀ := rfl
      _ ≤ α := hz₀α

/-- Under the sharp null the statistic recomputed at a hypothetical assignment does not
depend on the realized assignment: the observed outcome vector is the same whatever was
assigned (Ding §3.2). This is what makes the randomization distribution computable. -/
theorem sharpNull_statistic_eq (S : ScienceTable n) (hS : S.SharpNull)
    (T : Assignment n → (Fin n → ℝ) → ℝ) (z z' : Assignment n) :
    T z' (S.observed z) = T z' S.y0 :=
  congrArg (T z') (funext fun i => by simp [ScienceTable.observed, hS i])

/-- **The Fisher randomization test is valid** (Ding §3.2, eqs. (3.2)–(3.3)): under the
sharp null, for any test statistic `T` and any design, the probability that the
randomization p-value falls below the level `α` is at most `α`. -/
theorem sharpNull_prob_fisherPValue_le (D : Design n) (S : ScienceTable n)
    -- USER-INPUT: Fisher's sharp null `Yᵢ(1) = Yᵢ(0)` for every unit; Ding §3.2
    (hS : S.SharpNull)
    -- USER-INPUT: the test statistic, a function of the assignment and the observed vector
    (T : Assignment n → (Fin n → ℝ) → ℝ) {α : ℝ}
    -- LEAN-ONLY: a nonnegative level; no scope change
    (hα : 0 ≤ α) :
    D.prob {z | fisherPValue D (fun z' => T z' (S.observed z')) z ≤ α} ≤ α := by
  have hg : (fun z' => T z' (S.observed z')) = fun z' => T z' S.y0 :=
    funext fun z' => sharpNull_statistic_eq S hS T z' z'
  rw [hg]
  exact prob_fisherPValue_le D _ hα

end StatLean.CausalInference
