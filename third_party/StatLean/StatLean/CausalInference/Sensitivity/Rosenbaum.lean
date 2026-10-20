module
public import StatLean.CausalInference.Randomized.MatchedPairs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Rosenbaum's sensitivity model for matched observational studies

In a matched observational study the assignment within a pair is *not* a fair coin: hidden
confounding can tilt it. Rosenbaum's model bounds the tilt by a single parameter `Γ ≥ 1`,

$$\frac1{1+\Gamma}\ \le\ \pi_i\ \le\ \frac{\Gamma}{1+\Gamma},$$

where `π_i` is the probability that the first unit of pair `i` is the treated one. For a
sign-score statistic `T = ∑_i S_i q_i` with nonnegative scores `q_i`, the worst case over
the whole model is attained at the *extreme* tilt `π_i ≡ Γ/(1+Γ)`; so a p-value computed
under that extreme is valid for every law in the model, and it degrades monotonically as
`Γ` grows. Reporting the `Γ` at which significance is lost is the standard sensitivity
summary.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). ch. 19 (*Rosenbaum-Style p-Values for Matched
Observational Studies with Unmeasured Confounding*): **Assumption 19.1** (§19.1, p. 258:
the odds-ratio bound `1/(1+Γ) ≤ π_{i1} ≤ Γ/(1+Γ)`); §19.2 (pp. 258–259: for
`T = ∑ᵢSᵢqᵢ` with `qᵢ ≥ 0`, the largest p-value under Assumption 19.1 is attained at
`Sᵢ` i.i.d. `Bernoulli(Γ/(1+Γ))`, with the stated worst-case moments — this is running
text, with no theorem number). (`Ding Assumption 19.1; §19.2`.) Sensitivity analysis and
bounds are ch. 22 of G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics,
Social, and Biomedical Sciences*, Cambridge University Press, 2015. (`IR ch. 22`.)

**Scope.** The book's §19.2 asserts the worst case *and then* passes to a normal
approximation for the p-value. Formalized here is the exact finite-sample core — the
stochastic-dominance statement that makes the worst case worst — plus the monotonicity of
the resulting bound in `Γ`. The normal approximation is not formalized (it would need a
Lindeberg-type CLT for weighted Bernoulli sums and is an approximation, not an identity).

**Proof formalization notes.** The model is a product measure on sign patterns
`Fin m → Bool` with per-pair success probabilities `π : Fin m → ℝ` (each in `[0,1]`);
`biasedProb π c` is the product weight and `biasedExpect` the induced expectation. The
worst-case claim is stochastic dominance of the score sum under coordinatewise increase of
`π`, proved by a **one-coordinate-at-a-time** exchange argument: changing a single `πⱼ`
upward can only increase `P(T ≥ t)` because, conditionally on the other coordinates, the
statistic is monotone in `Sⱼ` (the score `qⱼ ≥ 0`). Iterating over the `m` coordinates
(`Finset.induction` over the set of coordinates already replaced) gives the full
comparison. This is the same hybrid-argument structure used elsewhere in StatLean for
coordinatewise comparisons.

**Bibliographic comments.** P. R. Rosenbaum, *Observational Studies*, 2nd ed., Springer,
2002, ch. 4; the sign-score family covers the sign test, the paired `t`-statistic and
Wilcoxon's signed-rank statistic.
-/

namespace StatLean.CausalInference

variable {m : ℕ}

/-- The **per-pair treatment probability vector** of a matched observational study: `π j`
is the probability that pair `j`'s first unit is the treated one. -/
def SignProbs (m : ℕ) : Type := Fin m → ℝ

/-- **Rosenbaum's sensitivity model** (Ding Assumption 19.1): every pair's assignment
probability lies within the odds-ratio band determined by `Γ`. -/
def RosenbaumModel (π : Fin m → ℝ) (Γ : ℝ) : Prop :=
  ∀ j, 1 / (1 + Γ) ≤ π j ∧ π j ≤ Γ / (1 + Γ)

/-- The **product weight** of a sign pattern under per-pair probabilities `π`. -/
noncomputable def biasedProb (π : Fin m → ℝ) (c : Fin m → Bool) : ℝ :=
  ∏ j, if c j then π j else 1 - π j

/-- The **expectation** of a statistic under the biased (confounded) assignment law. -/
noncomputable def biasedExpect (π : Fin m → ℝ) (f : (Fin m → Bool) → ℝ) : ℝ :=
  ∑ c : Fin m → Bool, biasedProb π c * f c

/-- The **sign-score statistic** `T = ∑ⱼ Sⱼqⱼ` (Ding §19.2), covering the sign test, the
paired `t` statistic and Wilcoxon's signed-rank statistic by choice of scores `q`. -/
noncomputable def signScore (q : Fin m → ℝ) (c : Fin m → Bool) : ℝ :=
  ∑ j, if c j then q j else 0

/-- The **upper-tail probability** of the sign-score statistic under the biased law. -/
noncomputable def biasedTail (π : Fin m → ℝ) (q : Fin m → ℝ) (t : ℝ) : ℝ :=
  biasedExpect π fun c => if t ≤ signScore q c then 1 else 0

/-! ### The coordinate-splitting device

The exchange argument needs to isolate a single pair `j`: a sign pattern is the value at `j`
together with the pattern off `j`, and the product weight factors accordingly, with the
off-`j` factor free of `π j`. -/

/-- Splitting a sign pattern at the coordinate `j`: the sign of pair `j` together with the
signs of all the other pairs. -/
private def rbSplit (j : Fin m) : (Bool × ({i : Fin m // i ≠ j} → Bool)) ≃ (Fin m → Bool) where
  toFun p := fun i => if h : i = j then p.1 else p.2 ⟨i, h⟩
  invFun c := (c j, fun i => c i.1)
  left_inv := by
    rintro ⟨b, r⟩
    refine Prod.ext ?_ ?_
    · simp
    · funext i
      simp [i.2]
  right_inv := by
    intro c
    funext i
    by_cases h : i = j <;> simp [h]

/-- The two extensions of an off-`j` pattern differ by an update at `j`. -/
private lemma rbSplit_apply_eq (j : Fin m) (b : Bool) (r : {i : Fin m // i ≠ j} → Bool) :
    rbSplit j (b, r) = Function.update (rbSplit j (false, r)) j b := by
  funext i
  by_cases h : i = j
  · subst h; simp [rbSplit]
  · simp [rbSplit, h]

/-- The product weight factors into the pair-`j` factor and an off-`j` factor. -/
private lemma biasedProb_split (π : Fin m → ℝ) (j : Fin m) (b : Bool)
    (r : {i : Fin m // i ≠ j} → Bool) :
    biasedProb π (rbSplit j (b, r))
      = (if b then π j else 1 - π j) *
          ∏ i : {i : Fin m // i ≠ j}, (if r i then π i.1 else 1 - π i.1) := by
  unfold biasedProb
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  congr 1
  · simp [rbSplit]
  · rw [Finset.prod_subtype (p := fun i => i ≠ j) _ (by simp)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [rbSplit, i.2]

/-- Conditioning on the signs off `j`: the expectation is an average over the off-`j`
pattern of a two-point average in the sign of pair `j`, whose weights are the only place
`π j` appears. -/
private lemma biasedExpect_split (π : Fin m → ℝ) (j : Fin m) (f : (Fin m → Bool) → ℝ) :
    biasedExpect π f
      = ∑ r : {i : Fin m // i ≠ j} → Bool,
          (∏ i : {i : Fin m // i ≠ j}, (if r i then π i.1 else 1 - π i.1)) *
            (π j * f (rbSplit j (true, r)) + (1 - π j) * f (rbSplit j (false, r))) := by
  unfold biasedExpect
  rw [← Equiv.sum_comp (rbSplit j)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [biasedProb_split, biasedProb_split]
  norm_num
  ring

/-- The biased weights are a probability distribution on sign patterns. -/
theorem sum_biasedProb {π : Fin m → ℝ}
    -- USER-INPUT: each coordinate probability is a probability; Ding Assumption 19.1
    (hπ : ∀ j, π j ∈ Set.Icc (0 : ℝ) 1) :
    ∑ c : Fin m → Bool, biasedProb π c = 1 := by
  have key : (∏ j : Fin m, ∑ b : Bool, (if b then π j else 1 - π j))
      = ∑ c : Fin m → Bool, biasedProb π c := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp [biasedProb]
  rw [← key]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [Fintype.sum_bool]
  norm_num

/-- The fair-coin case recovers the matched-pair design of `Randomized.MatchedPairs`:
`Γ = 1` gives `π ≡ 1/2` and the biased expectation is the uniform average. -/
theorem biasedExpect_half (f : (Fin m → Bool) → ℝ) :
    biasedExpect (fun _ => (1 : ℝ) / 2) f = pairExpect f := by
  unfold biasedExpect pairExpect biasedProb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have h : ∀ j : Fin m, (if c j then (1:ℝ)/2 else 1 - 1/2) = 1/2 := by
    intro j; cases c j <;> norm_num
  rw [Finset.prod_congr rfl (fun j _ => h j)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [one_div, inv_pow]

/-- **The sign-score statistic is monotone in each sign** when the scores are nonnegative:
flipping a pair's sign from `false` to `true` can only increase `T`. This is the
monotonicity that drives the worst-case argument. -/
theorem signScore_le_of_update {q : Fin m → ℝ}
    -- USER-INPUT: nonnegative scores; Ding §19.2
    (hq : ∀ j, 0 ≤ q j) (c : Fin m → Bool) (j : Fin m) :
    signScore q (Function.update c j false) ≤ signScore q (Function.update c j true) := by
  unfold signScore
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : i = j
  · subst h; simp [hq i]
  · simp [Function.update_of_ne h]

/-- **One-coordinate stochastic dominance**: raising a single pair's treatment probability
raises the upper-tail probability of the sign-score statistic. -/
theorem biasedTail_mono_single {π π' : Fin m → ℝ} {q : Fin m → ℝ} {t : ℝ} {j : Fin m}
    (hq : ∀ i, 0 ≤ q i)
    (hπ : ∀ i, π i ∈ Set.Icc (0 : ℝ) 1) (hπ' : ∀ i, π' i ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the two vectors differ only at `j`, where `π'` is larger
    (heq : ∀ i, i ≠ j → π i = π' i) (hle : π j ≤ π' j) :
    biasedTail π q t ≤ biasedTail π' q t := by
  unfold biasedTail
  rw [biasedExpect_split π j, biasedExpect_split π' j]
  refine Finset.sum_le_sum fun r _ => ?_
  have hRe : (∏ i : {i : Fin m // i ≠ j}, (if r i then π i.1 else 1 - π i.1))
      = ∏ i : {i : Fin m // i ≠ j}, (if r i then π' i.1 else 1 - π' i.1) :=
    Finset.prod_congr rfl fun i _ => by rw [heq i.1 i.2]
  rw [← hRe]
  have hR : (0:ℝ) ≤ ∏ i : {i : Fin m // i ≠ j}, (if r i then π i.1 else 1 - π i.1) := by
    refine Finset.prod_nonneg fun i _ => ?_
    cases hb : r i
    · simpa using (hπ i.1).2
    · simpa using (hπ i.1).1
  refine mul_le_mul_of_nonneg_left ?_ hR
  set A : ℝ := if t ≤ signScore q (rbSplit j (true, r)) then 1 else 0 with hA
  set B : ℝ := if t ≤ signScore q (rbSplit j (false, r)) then 1 else 0 with hB
  have hmono : signScore q (rbSplit j (false, r)) ≤ signScore q (rbSplit j (true, r)) := by
    have := signScore_le_of_update hq (rbSplit j (false, r)) j
    rwa [← rbSplit_apply_eq j false r, ← rbSplit_apply_eq j true r] at this
  have hBA : B ≤ A := by
    rw [hA, hB]
    by_cases h1 : t ≤ signScore q (rbSplit j (false, r))
    · rw [if_pos h1, if_pos (h1.trans hmono)]
    · rw [if_neg h1]
      split_ifs <;> norm_num
  have hB0 : 0 ≤ B := by rw [hB]; split_ifs <;> norm_num
  nlinarith [mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hBA)]

/-- **Stochastic dominance under the model** (Ding §19.2): raising every pair's treatment
probability raises the tail probability of the sign-score statistic. Iterating the
one-coordinate comparison. -/
theorem biasedTail_mono {π π' : Fin m → ℝ} {q : Fin m → ℝ} {t : ℝ}
    (hq : ∀ i, 0 ≤ q i)
    (hπ : ∀ i, π i ∈ Set.Icc (0 : ℝ) 1) (hπ' : ∀ i, π' i ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: coordinatewise domination
    (hle : ∀ i, π i ≤ π' i) :
    biasedTail π q t ≤ biasedTail π' q t := by
  classical
  have hyb : ∀ s : Finset (Fin m), ∀ i, (if i ∈ s then π' i else π i) ∈ Set.Icc (0:ℝ) 1 := by
    intro s i; by_cases h : i ∈ s <;> simp [h, hπ i, hπ' i]
  have H : ∀ s : Finset (Fin m),
      biasedTail π q t ≤ biasedTail (fun i => if i ∈ s then π' i else π i) q t := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      refine ih.trans ?_
      refine biasedTail_mono_single (j := j) hq (hyb s) (hyb (insert j s)) ?_ ?_
      · intro i hi
        by_cases h : i ∈ s <;> simp [h, Finset.mem_insert, hi]
      · simp [hj, hle j]
  have := H Finset.univ
  simpa using this

/-- **The worst case is the extreme tilt** (Ding §19.2): under Rosenbaum's model with
parameter `Γ`, the tail probability of any nonnegative sign-score statistic is bounded by
its value at the extreme assignment law `π ≡ Γ/(1+Γ)`. Hence the p-value computed at that
extreme is valid for the whole model. -/
theorem biasedTail_le_extreme {π : Fin m → ℝ} {q : Fin m → ℝ} {t Γ : ℝ}
    -- USER-INPUT: nonnegative scores; Ding §19.2
    (hq : ∀ i, 0 ≤ q i)
    -- USER-INPUT: Rosenbaum's sensitivity model; Ding Assumption 19.1
    (hmodel : RosenbaumModel π Γ)
    -- USER-INPUT: a genuine sensitivity parameter; Ding Assumption 19.1
    (hΓ : 1 ≤ Γ) :
    biasedTail π q t ≤ biasedTail (fun _ => Γ / (1 + Γ)) q t := by
  have hpos : (0:ℝ) < 1 + Γ := by linarith
  have hle1 : Γ / (1 + Γ) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  have hnn : (0:ℝ) ≤ Γ / (1 + Γ) := div_nonneg (by linarith) (by linarith)
  refine biasedTail_mono hq ?_ (fun _ => ⟨hnn, hle1⟩) ?_
  · intro i
    exact ⟨le_trans (div_nonneg zero_le_one hpos.le) (hmodel i).1, le_trans (hmodel i).2 hle1⟩
  · intro i; exact (hmodel i).2

/-- **The worst-case bound degrades monotonically in `Γ`** (Ding §19.2): a larger allowance
for hidden bias gives a larger worst-case p-value, which is why one reports the `Γ` at
which significance is lost. -/
theorem biasedTail_extreme_mono {q : Fin m → ℝ} {t Γ Γ' : ℝ} (hq : ∀ i, 0 ≤ q i)
    (hΓ : 1 ≤ Γ) (hle : Γ ≤ Γ') :
    biasedTail (fun _ => Γ / (1 + Γ)) q t ≤ biasedTail (fun _ => Γ' / (1 + Γ')) q t := by
  have hpos : (0:ℝ) < 1 + Γ := by linarith
  have hpos' : (0:ℝ) < 1 + Γ' := by linarith
  have hstep : Γ / (1 + Γ) ≤ Γ' / (1 + Γ') := by
    rw [← sub_nonneg]
    have hid : Γ' / (1 + Γ') - Γ / (1 + Γ) = (Γ' - Γ) / ((1 + Γ') * (1 + Γ)) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (by linarith) (by positivity)
  refine biasedTail_mono hq (fun _ => ⟨div_nonneg (by linarith) hpos.le, ?_⟩)
    (fun _ => ⟨div_nonneg (by linarith) hpos'.le, ?_⟩) (fun _ => hstep)
  · rw [div_le_one hpos]; linarith
  · rw [div_le_one hpos']; linarith

/-- **`Γ = 1` is the randomized case**: with no allowance for hidden bias the worst-case law
is the fair coin, so Rosenbaum's procedure reduces to the matched-pair randomization test
of `Randomized.MatchedPairs` (Ding §19.1). -/
theorem rosenbaumModel_one_iff {π : Fin m → ℝ} :
    RosenbaumModel π 1 ↔ ∀ j, π j = 1 / 2 := by
  unfold RosenbaumModel
  constructor
  · intro h j
    have := h j
    norm_num at this
    linarith [this.1, this.2]
  · intro h j
    rw [h j]
    norm_num

end StatLean.CausalInference
