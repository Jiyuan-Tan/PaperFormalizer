module
public import StatLean.CausalInference.Core.FiniteDefs
public import StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments

@[expose] public section

/-!
# Complete randomization — the assignment moments

Under complete randomization the treatment vector is a uniform draw from the assignment
vectors with exactly `n₁` ones, i.e. a simple random sample of `n₁` of the `n` units. This
file bridges `completeDesign` to the sampling-without-replacement moments already
formalized in `StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments` and records
the three classical identities

$$\mathbb E[Z_i]=\frac{n_1}{n},\qquad
  \operatorname{Var}(Z_i)=\frac{n_1n_0}{n^2},\qquad
  \operatorname{Cov}(Z_i,Z_j)=-\frac{n_1n_0}{n^2(n-1)}\ (i\neq j).$$

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Definition 3.1 (the completely randomized
experiment) and Lemma C.1 (§C.1, p. 433: the first two moments of the inclusion
indicators of a simple random sample), applied to the CRE via Definition C.1.
(`Ding Definition 3.1; Lemma C.1`.) The corresponding design in G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*,
Cambridge University Press, 2015, is the completely randomized assignment mechanism of
Part II. (`IR Part II`.)

**Proof formalization notes.**

* The bridge `expect_completeDesign_eq` transports an expectation over
  `completeSupport n n₁` to one over `SubsetsOfCard n n₁` along
  `z ↦ {i | zᵢ = 1}` / `s ↦ (i ↦ i ∈ s)`, which is a bijection. Every moment identity is
  then a restatement of `expect_weight`, `expect_weight_pair` and `cov_weight`.
* This is a **cross-area import of another area's `ForMathlib/` layer**, which the project
  layering rules permit (`CLAUDE.md` §3): `HypergeometricMoments` is Mathlib-only and
  theorem-agnostic. Nothing from the `HypothesisTesting` concept layer is used.
-/

namespace StatLean.CausalInference

open StatLean.HypothesisTesting

variable {n n₁ : ℕ}

/-! ### Private helpers: the raw finset-indexed assignment and `Design.expect` algebra -/

/-- The assignment treating exactly the units of `t`. The un-bundled form of `ofSubset`,
used for the bijection with `Finset.powersetCard`. -/
private def ofFinset (t : Finset (Fin n)) : Assignment n := fun i => decide (i ∈ t)

/-- The treated set of `ofFinset t` is `t`. -/
private lemma armIdx_ofFinset (t : Finset (Fin n)) : armIdx (ofFinset t) true = t := by
  ext i; simp [armIdx, ofFinset]

/-- `ofFinset` inverts `z ↦ {i | zᵢ = 1}`. -/
private lemma ofFinset_armIdx (z : Assignment n) : ofFinset (armIdx z true) = z := by
  funext i; simp [ofFinset, armIdx]

/-- Membership in the complete-randomization support, unfolded. -/
private lemma mem_completeSupport_iff {z : Assignment n} :
    z ∈ completeSupport n n₁ ↔ (armIdx z true).card = n₁ := by
  rw [completeSupport, Finset.mem_filter]; simp [numTreated]

/-- The support of complete randomization is in bijection with the `n₁`-subsets of the
units. Stated privately so that `expect_completeDesign_eq`, which precedes the public
`card_completeSupport`, can use it. -/
private lemma card_completeSupport' : (completeSupport n n₁).card = n.choose n₁ := by
  have hp : (Finset.powersetCard n₁ (Finset.univ : Finset (Fin n))).card = n.choose n₁ := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hp]
  refine Finset.card_nbij' (fun z => armIdx z true) ofFinset ?_ ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, mem_completeSupport_iff.mp hz⟩
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_powersetCard] at ht
    exact mem_completeSupport_iff.mpr (by rw [armIdx_ofFinset]; exact ht.2)
  · intro z _
    exact ofFinset_armIdx z
  · intro t _
    exact armIdx_ofFinset t

/-- `Var(f) = E[f²] - (E f)²` under any design. -/
private lemma dvar_eq (D : Design n) (f : Assignment n → ℝ) :
    D.var f = D.expect (fun z => f z ^ 2) - (D.expect f) ^ 2 := by
  have hc : ((D.support.card : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr D.support_nonempty).ne'
  simp only [Design.var, Design.expect, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  field_simp
  ring

/-! ### The bijection with `n₁`-subsets -/

/-- The map from an `n₁`-subset of units to the assignment vector treating exactly that
subset. -/
def ofSubset (s : SubsetsOfCard n n₁) : Assignment n := fun i => decide (i ∈ s.val)

/-- Assignments in the complete-randomization support are exactly the images of
`n₁`-subsets: `ofSubset` is a bijection onto `completeSupport n n₁`. -/
theorem ofSubset_mem_completeSupport (s : SubsetsOfCard n n₁) :
    ofSubset s ∈ completeSupport n n₁ :=
  mem_completeSupport_iff.mpr (by
    change (armIdx (ofFinset s.val) true).card = n₁
    rw [armIdx_ofFinset]; exact s.2)

/-- The treated set of `ofSubset s` is `s`. -/
theorem armIdx_ofSubset_true (s : SubsetsOfCard n n₁) : armIdx (ofSubset s) true = s.val :=
  armIdx_ofFinset s.val

/-- The inclusion weight of `HypergeometricMoments` is the treatment indicator. -/
theorem ind_ofSubset (i : Fin n) (s : SubsetsOfCard n n₁) :
    ind (ofSubset s i) = weight i s := by
  simp only [ind, ofSubset, weight, decide_eq_true_eq]

/-- **The bridge**: expectations under complete randomization are uniform averages over
`n₁`-subsets. -/
theorem expect_completeDesign_eq (h : n₁ ≤ n) (f : Assignment n → ℝ) :
    (completeDesign n n₁ h).expect f = expect (fun s : SubsetsOfCard n n₁ => f (ofSubset s)) := by
  have hsub : ∑ t ∈ Finset.powersetCard n₁ (Finset.univ : Finset (Fin n)), f (ofFinset t)
      = ∑ s : SubsetsOfCard n n₁, f (ofFinset s.val) :=
    Finset.sum_subtype _ (fun t => by simp [Finset.mem_powersetCard]) _
  have hre : ∑ z ∈ completeSupport n n₁, f z
      = ∑ t ∈ Finset.powersetCard n₁ (Finset.univ : Finset (Fin n)), f (ofFinset t) := by
    refine Finset.sum_nbij' (fun z => armIdx z true) ofFinset ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, mem_completeSupport_iff.mp hz⟩
    · intro t ht
      rw [Finset.mem_powersetCard] at ht
      exact mem_completeSupport_iff.mpr (by rw [armIdx_ofFinset]; exact ht.2)
    · intro z _; exact ofFinset_armIdx z
    · intro t _; exact armIdx_ofFinset t
    · intro z _; rw [ofFinset_armIdx]
  change ((completeSupport n n₁).card : ℝ)⁻¹ * ∑ z ∈ completeSupport n n₁, f z = _
  rw [card_completeSupport', hre, hsub]
  unfold StatLean.HypothesisTesting.expect
  congr 1
  simp

/-- The support of complete randomization has `C(n, n₁)` elements
(Ding Definition 3.1). -/
theorem card_completeSupport (h : n₁ ≤ n) : (completeSupport n n₁).card = n.choose n₁ :=
  card_completeSupport'

/-- Every assignment in the support treats exactly `n₁` units. -/
theorem card_armIdx_true (h : n₁ ≤ n) {z : Assignment n} (hz : z ∈ completeSupport n n₁) :
    (armIdx z true).card = n₁ := mem_completeSupport_iff.mp hz

/-- Every assignment in the support leaves exactly `n - n₁` units untreated. -/
theorem card_armIdx_false (h : n₁ ≤ n) {z : Assignment n} (hz : z ∈ completeSupport n n₁) :
    (armIdx z false).card = n - n₁ := by
  have h1 : (armIdx z true).card = n₁ := card_armIdx_true h hz
  have h2 : (armIdx z true).card + (armIdx z false).card = n := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => z i = true)
    simpa [armIdx, Bool.not_eq_true] using this
  omega

/-- **First moment** (Ding Lemma C.1): `E[Zᵢ] = n₁/n`. -/
theorem completeDesign_expect_ind (h : n₁ ≤ n) (i : Fin n) :
    (completeDesign n n₁ h).expect (fun z => ind (z i)) = (n₁ : ℝ) / (n : ℝ) := by
  rw [expect_completeDesign_eq h]
  simp only [ind_ofSubset]
  exact expect_weight h i

/-- **Second cross moment** (Ding Lemma C.1): `E[ZᵢZⱼ] = n₁(n₁-1)/(n(n-1))` for `i ≠ j`. -/
theorem completeDesign_expect_ind_mul (h : n₁ ≤ n) {i j : Fin n}
    -- USER-INPUT: two distinct units; Ding Lemma C.1
    (hij : i ≠ j) :
    (completeDesign n n₁ h).expect (fun z => ind (z i) * ind (z j))
      = ((n₁ : ℝ) * ((n₁ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [expect_completeDesign_eq h]
  simp only [ind_ofSubset]
  exact expect_weight_pair h hij

/-- **Variance of an inclusion indicator** (Ding Lemma C.1): `Var(Zᵢ) = n₁n₀/n²`. -/
theorem completeDesign_var_ind (h : n₁ ≤ n) (i : Fin n) :
    (completeDesign n n₁ h).var (fun z => ind (z i))
      = ((n₁ : ℝ) * ((n : ℝ) - (n₁ : ℝ))) / (n : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Fin.pos i
  have hsq : (fun z : Assignment n => ind (z i) ^ 2) = fun z => ind (z i) := by
    funext z; cases hzi : z i <;> simp [ind]
  rw [dvar_eq, hsq, completeDesign_expect_ind h i]
  field_simp

/-- **Covariance of two inclusion indicators** (Ding Lemma C.1):
`Cov(Zᵢ, Zⱼ) = -n₁n₀/(n²(n-1))` for `i ≠ j`. The negative sign is the
sampling-without-replacement effect. -/
theorem completeDesign_cov_ind (h : n₁ ≤ n) {i j : Fin n}
    -- USER-INPUT: two distinct units; Ding Lemma C.1
    (hij : i ≠ j) :
    (completeDesign n n₁ h).expect (fun z => ind (z i) * ind (z j))
        - (completeDesign n n₁ h).expect (fun z => ind (z i))
          * (completeDesign n n₁ h).expect (fun z => ind (z j))
      = -((n₁ : ℝ) * ((n : ℝ) - (n₁ : ℝ))) / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
  rw [expect_completeDesign_eq h, expect_completeDesign_eq h, expect_completeDesign_eq h]
  simp only [ind_ofSubset]
  exact cov_weight h hij

/-- **Variance of a linear statistic in the assignment** (Ding Lemma C.2, in the form of
`HypergeometricMoments.var_linear`): for deterministic coefficients `c`,
`Var(∑ᵢ cᵢZᵢ) = n₁n₀/(n(n-1)) · ∑ᵢ(cᵢ - c̄)²`. This is the engine behind Neyman's
variance formula. -/
theorem completeDesign_var_linear (h : n₁ ≤ n)
    -- USER-INPUT: at least two units (the factor `n - 1` is a denominator); Ding Lemma C.2
    (hn : 2 ≤ n) (c : Fin n → ℝ) :
    (completeDesign n n₁ h).var (fun z => ∑ i, c i * ind (z i))
      = ((n₁ : ℝ) * ((n : ℝ) - (n₁ : ℝ))) / ((n : ℝ) * ((n : ℝ) - 1))
          * ∑ i, (c i - popMean c) ^ 2 := by
  have hE : (completeDesign n n₁ h).expect (fun z => ∑ i, c i * ind (z i))
      = expect (fun s : SubsetsOfCard n n₁ => ∑ i, c i * weight i s) := by
    rw [expect_completeDesign_eq h]
    simp only [ind_ofSubset]
  simp only [Design.var, popMean]
  rw [hE, expect_completeDesign_eq h]
  simp only [ind_ofSubset]
  exact var_linear h hn c

end StatLean.CausalInference
