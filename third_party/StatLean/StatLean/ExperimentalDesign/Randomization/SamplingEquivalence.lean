module
public import StatLean.ExperimentalDesign.Randomization.CompleteRandomization
public import StatLean.ExperimentalDesign.SurveySampling.SimpleRandomSampling

@[expose] public section

/-!
# Each arm of a completely randomised design is a simple random sample

The organising theorem of the finite randomisation machinery: under the completely
randomised design with replications `r`, the arm of any fixed treatment `t` is
distributed exactly as a simple random sample of size `r t` — the pushforward
identity
$$(\operatorname{arm}_t)_* D_r = \operatorname{SRS}(r_t).$$
Consequently every arm-statistic moment is inherited from the sampling theory: the
arm mean of a deterministic population quantity `y` is design-unbiased for the
population mean, with the exact finite-population variance
$$\mathbb E[\bar y_t] = \bar y, \qquad
  \operatorname{Var}(\bar y_t)
    = \Bigl(1 - \frac{r_t}{N}\Bigr)\frac{S_y^2}{r_t}.$$
These statements deliberately do not mention potential outcomes: the causal
randomised-experiment theorems are obtained downstream by instantiating `y` at each
potential-outcome function.

## Main results

* `completeRandomization_map_arm` — the pushforward identity.
* `expect_armMean` — design unbiasedness of the arm mean.
* `var_armMean` — exact arm-mean variance with finite-population correction.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988, §9.2 and §9.6: "the
random allocation may be achieved either by allocating units to treatments or by
selecting a unit for a particular treatment" — selecting the units for one treatment
uniformly (as in Example 9.3, four mice of twenty) *is* simple random sampling; the
equal-probability requirement of §9.6 is the marginal of the present identity.
(`Mead §9.2`, `Mead §9.6`, `Mead §9.3`.)

**Proof formalization notes.**
* Route for the pushforward identity: both sides are uniform laws.  The map
  `arm t : 𝒜_r → {S : |S| = r_t}` intertwines the permutation actions
  (`arm t (a ∘ σ⁻¹) = σ '' arm t a`), the source law is permutation invariant
  (`completeRandomization_map_precomp`), the action on `r_t`-subsets is transitive,
  and an invariant PMF under a transitive action on a finite set is uniform on it.
  Alternatively, count fibers directly: allocations with `arm t a = S` biject with
  valid allocations of `r` restricted to `U \ S` over `T \ {t}`, a count independent
  of `S`.
* The moment corollaries are three-line transfers:
  `armMean_eq_sampleMean_arm` + `pmfExpect_map` + the SRS moment theorems.
-/

open scoped ENNReal

namespace StatLean.ExperimentalDesign

variable {U T : Type*} [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T]

/-! ### Private machinery: permutation transport of arms, fibers and uniform laws -/

/-- Precomposition with a permutation pulls each arm back along the permutation. -/
private lemma arm_precomp (t : T) (π : Equiv.Perm U) (a : Allocation U T) :
    arm t (fun i => a (π i)) = (arm t a).image (π.symm : U → U) := by
  ext i
  simp only [mem_arm_iff, Finset.mem_image]
  constructor
  · intro h
    exact ⟨π i, h, Equiv.symm_apply_apply π i⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

/-- Precomposition with a permutation preserves validity of an allocation. -/
private lemma precomp_mem_validAllocations {r : T → ℕ} (π : Equiv.Perm U)
    {a : Allocation U T} (ha : a ∈ validAllocations (U := U) r) :
    (fun i => a (π i)) ∈ validAllocations (U := U) r := by
  rw [mem_validAllocations] at ha ⊢
  intro s
  rw [arm_precomp s π a,
    Finset.card_image_of_injective _ (Equiv.injective π.symm)]
  exact ha s

/-- Precomposition with a permutation is injective on allocations. -/
private lemma precomp_injective (σ : Equiv.Perm U) :
    Function.Injective fun (a : Allocation U T) => fun i => a (σ i) := by
  intro a₁ a₂ h
  funext i
  have := congrFun h (σ.symm i)
  simpa using this

/-- The fiber count of `arm t` over a subset is invariant under relabelling the
subset by a permutation. -/
private lemma card_filter_arm_image (r : T → ℕ) (t : T) (σ : Equiv.Perm U)
    (X : Finset U) :
    ((validAllocations (U := U) r).filter
        fun a => arm t a = X.image (σ : U → U)).card
      = ((validAllocations (U := U) r).filter fun a => arm t a = X).card := by
  classical
  have himg : ((validAllocations (U := U) r).filter fun a => arm t a = X).image
        (fun a => fun i => a (σ.symm i))
      = (validAllocations (U := U) r).filter
          fun a => arm t a = X.image (σ : U → U) := by
    ext a'
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨hav, haX⟩, rfl⟩
      refine ⟨precomp_mem_validAllocations σ.symm hav, ?_⟩
      rw [arm_precomp t σ.symm a, Equiv.symm_symm, haX]
    · rintro ⟨hav, haX⟩
      refine ⟨fun i => a' (σ i), ⟨precomp_mem_validAllocations σ hav, ?_⟩, ?_⟩
      · rw [arm_precomp t σ a', haX, Finset.image_image]
        have hid : ((σ.symm : U → U) ∘ (σ : U → U)) = id := by
          funext i; simp
        rw [hid, Finset.image_id]
      · funext i
        simp
  rw [← himg, Finset.card_image_of_injective _ (precomp_injective σ.symm)]

/-- Application of `Equiv.subtypeCongr` at a point satisfying the predicate. -/
private lemma subtypeCongr_apply_mem {p q : U → Prop} [DecidablePred p]
    [DecidablePred q] (e : { x // p x } ≃ { x // q x })
    (f : { x // ¬p x } ≃ { x // ¬q x }) {x : U} (hx : p x) :
    Equiv.subtypeCongr e f x = (e ⟨x, hx⟩ : U) := by
  have h1 : (Equiv.sumCompl p).symm x = Sum.inl ⟨x, hx⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  simp [Equiv.subtypeCongr, Equiv.trans_apply, h1]

/-- Any two subsets of the same size are related by a permutation of the ambient
finite type. -/
private lemma exists_perm_image_eq {S S' : Finset U} (h : S.card = S'.card) :
    ∃ σ : Equiv.Perm U, S.image (σ : U → U) = S' := by
  classical
  have hA : Fintype.card { x // x ∈ S } = Fintype.card { x // x ∈ S' } := by
    simpa [Fintype.card_coe] using h
  have hB : Fintype.card { x // ¬x ∈ S } = Fintype.card { x // ¬x ∈ S' } := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hA]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq hA) (Fintype.equivOfCardEq hB), ?_⟩
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [subtypeCongr_apply_mem (Fintype.equivOfCardEq hA) (Fintype.equivOfCardEq hB) hx]
    exact ((Fintype.equivOfCardEq hA) ⟨x, hx⟩).2
  · rw [Finset.card_image_of_injective _
      (Equiv.injective (Equiv.subtypeCongr (Fintype.equivOfCardEq hA)
        (Fintype.equivOfCardEq hB)))]
    exact le_of_eq h.symm

/-- A PMF vanishing off a finset and constant on it is the uniform law on that
finset. -/
private lemma eq_uniformOfFinset_of_constant {α : Type*} [Fintype α]
    (p : PMF α) (s : Finset α) (hs : s.Nonempty)
    (hoff : ∀ a ∉ s, p a = 0)
    (hconst : ∀ a ∈ s, ∀ b ∈ s, p a = p b) :
    p = PMF.uniformOfFinset s hs := by
  classical
  obtain ⟨a₀, ha₀⟩ := id hs
  have hcard0 : ((s.card : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨a₀, ha₀⟩).ne'
  have hmass : (s.card : ℝ≥0∞) * p a₀ = 1 := by
    have h1 : ∑ a, p a = 1 := by
      rw [← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe]
    calc (s.card : ℝ≥0∞) * p a₀ = ∑ _a ∈ s, p a₀ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ a ∈ s, p a := Finset.sum_congr rfl fun a ha => hconst a₀ ha₀ a ha
      _ = ∑ a, p a := Finset.sum_subset (Finset.subset_univ s)
          fun a _ ha => hoff a ha
      _ = 1 := h1
  have hval : p a₀ = (s.card : ℝ≥0∞)⁻¹ := by
    have h2 := congrArg (fun x => (s.card : ℝ≥0∞)⁻¹ * x) hmass
    simpa [← mul_assoc, ENNReal.inv_mul_cancel hcard0 (ENNReal.natCast_ne_top _)]
      using h2
  ext a
  rw [PMF.uniformOfFinset_apply]
  by_cases ha : a ∈ s
  · rw [if_pos ha, ← hval]
    exact hconst a ha a₀ ha₀
  · rw [if_neg ha]
    exact hoff a ha

/-- The mass the pushed-forward design gives a subset is the normalised fiber
count. -/
private lemma map_arm_apply (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U)
    (t : T) (X : Finset U) :
    ((completeRandomization r hr).map (arm t)) X
      = (((validAllocations (U := U) r).filter fun a => arm t a = X).card : ℝ≥0∞)
        * ((validAllocations (U := U) r).card : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  trans ∑ a : Allocation U T,
      (if a ∈ (validAllocations (U := U) r).filter (fun a => arm t a = X)
        then ((validAllocations (U := U) r).card : ℝ≥0∞)⁻¹ else 0)
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h1 : X = arm t a <;> by_cases h2 : a ∈ validAllocations (U := U) r <;>
      simp [completeRandomization, PMF.uniformOfFinset_apply, Finset.mem_filter,
        h1, h2, eq_comm]
  calc ∑ a : Allocation U T,
          (if a ∈ (validAllocations (U := U) r).filter (fun a => arm t a = X)
            then ((validAllocations (U := U) r).card : ℝ≥0∞)⁻¹ else 0)
      = ∑ a ∈ (validAllocations (U := U) r).filter (fun a => arm t a = X),
          (if a ∈ (validAllocations (U := U) r).filter (fun a => arm t a = X)
            then ((validAllocations (U := U) r).card : ℝ≥0∞)⁻¹ else 0) :=
        (Finset.sum_subset (Finset.subset_univ _)
          fun a _ ha => if_neg ha).symm
    _ = ∑ a ∈ (validAllocations (U := U) r).filter (fun a => arm t a = X),
          ((validAllocations (U := U) r).card : ℝ≥0∞)⁻¹ :=
        Finset.sum_congr rfl fun a ha => if_pos ha
    _ = (((validAllocations (U := U) r).filter fun a => arm t a = X).card : ℝ≥0∞)
        * ((validAllocations (U := U) r).card : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Variance transports along a pushforward exactly as the expectation does. -/
private lemma pmfVar_map {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (D : PMF Ω)
    (g : Ω → Ω') (f : Ω' → ℝ) :
    pmfVar (D.map g) f = pmfVar D fun ω => f (g ω) := by
  unfold pmfVar
  rw [pmfExpect_map, pmfExpect_map]

/-- **Arms of a completely randomised design are simple random samples**: the
pushforward of the design under `a ↦ arm t a` is SRSWOR of size `r t`
(`Mead §9.2`/`§9.6`). -/
theorem completeRandomization_map_arm (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) (t : T) :
    (completeRandomization r hr).map (arm t)
      = simpleRandomSampling (r t) (replication_le_card r hr t) := by
  classical
  have hoff : ∀ X ∉ Finset.powersetCard (r t) (Finset.univ : Finset U),
      ((completeRandomization r hr).map (arm t)) X = 0 := by
    intro X hX
    rw [PMF.apply_eq_zero_iff]
    intro hmem
    rw [PMF.support_map] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    have hcard := (mem_support_completeRandomization.mp ha) t
    exact hX (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)
  have hconst : ∀ X₁ ∈ Finset.powersetCard (r t) (Finset.univ : Finset U),
      ∀ X₂ ∈ Finset.powersetCard (r t) (Finset.univ : Finset U),
      ((completeRandomization r hr).map (arm t)) X₁
        = ((completeRandomization r hr).map (arm t)) X₂ := by
    intro X₁ h₁ X₂ h₂
    have hcards : X₁.card = X₂.card := by
      rw [(Finset.mem_powersetCard.mp h₁).2, (Finset.mem_powersetCard.mp h₂).2]
    obtain ⟨σ, hσ⟩ := exists_perm_image_eq hcards
    rw [map_arm_apply, map_arm_apply, ← hσ, card_filter_arm_image]
  exact eq_uniformOfFinset_of_constant _ _
    (samplesOfCard_nonempty (replication_le_card r hr t)) hoff hconst

/-- **Design unbiasedness of the arm mean**: for a treatment with positive
replication, the arm mean of a deterministic quantity `y` has design expectation the
population mean (`Mead §9.4`, the finite model; no potential outcomes involved). -/
theorem expect_armMean (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U) (t : T)
    -- USER-INPUT: positive replication of the arm, so its mean is well defined; Mead §6.2
    (ht : r t ≠ 0) (y : U → ℝ) :
    pmfExpect (completeRandomization r hr) (armMean y t) = populationMean y := by
  have h1 : pmfExpect (completeRandomization r hr) (armMean y t)
      = pmfExpect ((completeRandomization r hr).map (arm t)) (sampleMean y) := by
    rw [pmfExpect_map]
    exact congrArg _ (funext fun a => armMean_eq_sampleMean_arm y t a)
  rw [h1, completeRandomization_map_arm]
  exact srs_sampleMean_unbiased (r t) (replication_le_card r hr t) ht y

/-- **Exact design variance of the arm mean with finite-population correction**:
`Var(ȳ_t) = (1 − r_t/N) S²_y / r_t` (`Mead §9.4`; the completely-randomised analogue
of Mead's blocked variance computation). -/
theorem var_armMean (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U) (t : T)
    -- USER-INPUT: positive replication of the arm, so its mean is well defined; Mead §6.2
    (ht : r t ≠ 0) (y : U → ℝ) :
    pmfVar (completeRandomization r hr) (armMean y t)
      = (1 - (r t : ℝ) / (Fintype.card U : ℝ)) * populationVariance y / (r t : ℝ) := by
  have h1 : pmfVar (completeRandomization r hr) (armMean y t)
      = pmfVar ((completeRandomization r hr).map (arm t)) (sampleMean y) := by
    rw [pmfVar_map]
    exact congrArg _ (funext fun a => armMean_eq_sampleMean_arm y t a)
  rw [h1, completeRandomization_map_arm]
  exact srs_sampleMean_variance (r t) (replication_le_card r hr t) ht y

end StatLean.ExperimentalDesign
