module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import StatLean.AsymptoticStatistics.EmpiricalProcess.VCClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyStructural

@[expose] public section

/-!
# Sharp packing for VC-subgraph classes

A decomposition of the Chazelle--Haussler unit-distance,
random-deletion, and strict-subgraph layer-cake argument used in van der
Vaart Lemma 19.15.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, pp.275--276.
-/

namespace AsymptoticStatistics.EmpiricalProcess

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

universe u

variable {α Ω : Type*}

/-- The set family represented by a finite family of finite subsets.

This is the finite carrier used in the Chazelle--Haussler argument. Edge
behavior: the empty finset represents the empty set family, rather than the
singleton family containing the empty set. -/
noncomputable def finsetSetFamily (𝒜 : Finset (Finset α)) : Set (Set α) := by
  classical
  exact {A | ∃ a ∈ 𝒜, A = (a : Set α)}

/-- Hamming distance between two finite sets, i.e. the cardinality of their
symmetric difference in the finite VC packing argument.

Edge behavior: it is zero exactly on equal finite sets. -/
def finsetHammingDistance (A B : Finset α) : ℕ := by
  classical
  exact ((A \ B) ∪ (B \ A)).card

/-- The unit-distance graph of a finite set family in the
Chazelle--Haussler packing proof.

Vertices are members of `𝒜`; two distinct vertices are adjacent exactly when
their Hamming distance is one. Edge behavior: an empty or singleton family
has no edges. -/
noncomputable def unitDistanceGraph (𝒜 : Finset (Finset α)) :
    SimpleGraph (↥𝒜) := by
  classical
  exact SimpleGraph.fromRel fun A B ↦
    finsetHammingDistance A.1 B.1 = 1

/-- The number of unoriented edges of the unit-distance graph.

Edge behavior: it is zero when the family has fewer than two members. The
definition is total and does not require a decidability assumption in theorem
statements. -/
noncomputable def unitDistanceEdgeCount (𝒜 : Finset (Finset α)) : ℕ := by
  classical
  exact ∑ B ∈ 𝒜, (B.filter fun x ↦ B.erase x ∈ 𝒜).card

/-- The minimum-endpoint weighted edge sum in the unit-distance graph.

This is the weighted degeneracy quantity in the sharp packing proof. Edge
behavior: an edgeless graph has sum zero; negative vertex weights are allowed
by the definition but excluded by the theorem using it. -/
noncomputable def edgeMinWeightSumRaw (𝒜 : Finset (Finset α))
    (W : Finset α → ℝ) : ℝ := by
  classical
  exact ∑ B ∈ 𝒜, ∑ x ∈ B,
    if B.erase x ∈ 𝒜 then min (W B) (W (B.erase x)) else 0

noncomputable def extendSubtypeWeight (𝒜 : Finset (Finset α))
    (w : ↥𝒜 → ℝ) (B : Finset α) : ℝ := by
  classical
  exact if h : B ∈ 𝒜 then w ⟨B, h⟩ else 0

noncomputable def edgeMinWeightSum (𝒜 : Finset (Finset α))
    (w : ↥𝒜 → ℝ) : ℝ := by
  exact edgeMinWeightSumRaw 𝒜 (extendSubtypeWeight 𝒜 w)

section UnitIncidence

local instance : DecidableEq α := Classical.decEq α

private noncomputable def unitIncidences (𝒜 : Finset (Finset α)) :
    Finset (↥𝒜 × α) := by
  classical
  exact (𝒜.attach.sigma fun B ↦ B.1.filter fun x ↦ B.1.erase x ∈ 𝒜).map
    (Equiv.sigmaEquivProd ↥𝒜 α).toEmbedding

private lemma mem_unitIncidences
    (𝒜 : Finset (Finset α)) (p : ↥𝒜 × α) :
    p ∈ unitIncidences 𝒜 ↔ p.2 ∈ p.1.1 ∧ p.1.1.erase p.2 ∈ 𝒜 := by
  classical
  simp [unitIncidences]

private lemma card_unitIncidences (𝒜 : Finset (Finset α)) :
    (unitIncidences 𝒜).card = unitDistanceEdgeCount 𝒜 := by
  classical
  rw [unitIncidences, Finset.card_map, Finset.card_sigma, unitDistanceEdgeCount]
  exact Finset.sum_attach 𝒜 fun B ↦
    (B.filter fun x ↦ B.erase x ∈ 𝒜).card

private def incidenceIsLowered (𝒜 : Finset (Finset α)) (a : α)
    (p : ↥𝒜 × α) : Prop :=
  a ∈ p.1.1 ∧ p.2 ≠ a ∧
    ¬ (p.1.1.erase a ∈ 𝒜 ∧ (p.1.1.erase p.2).erase a ∈ 𝒜)

private noncomputable def compressedIncidenceLarge
    (𝒜 : Finset (Finset α)) (a : α) (p : ↥𝒜 × α) : Finset α := by
  classical
  exact if incidenceIsLowered 𝒜 a p then p.1.1.erase a else p.1.1

private lemma compressedIncidenceLarge_mem
    (𝒜 : Finset (Finset α)) (a : α) (p : ↥(unitIncidences 𝒜)) :
    compressedIncidenceLarge 𝒜 a p.1 ∈ Down.compression a 𝒜 := by
  have hp := (mem_unitIncidences 𝒜 p.1).mp p.2
  rw [compressedIncidenceLarge]
  split_ifs with hlower
  · exact Down.erase_mem_compression p.1.1.2
  · rw [Down.mem_compression]
    left
    refine ⟨p.1.1.2, ?_⟩
    by_cases ha : a ∈ p.1.1.1
    · by_cases hxa : p.1.2 = a
      · simpa only [hxa] using hp.2
      · have hboth : p.1.1.1.erase a ∈ 𝒜 ∧
            (p.1.1.1.erase p.1.2).erase a ∈ 𝒜 := by
          by_contra h
          exact hlower ⟨ha, hxa, h⟩
        exact hboth.1
    · simpa only [Finset.erase_eq_of_notMem ha] using p.1.1.2

private lemma compressedIncidence_coordinate_mem
    (𝒜 : Finset (Finset α)) (a : α) (p : ↥(unitIncidences 𝒜)) :
    p.1.2 ∈ compressedIncidenceLarge 𝒜 a p.1 := by
  have hp := (mem_unitIncidences 𝒜 p.1).mp p.2
  rw [compressedIncidenceLarge]
  split_ifs with hlower
  · exact Finset.mem_erase.mpr ⟨hlower.2.1, hp.1⟩
  · exact hp.1

private lemma compressedIncidence_erase_mem
    (𝒜 : Finset (Finset α)) (a : α) (p : ↥(unitIncidences 𝒜)) :
    (compressedIncidenceLarge 𝒜 a p.1).erase p.1.2 ∈
      Down.compression a 𝒜 := by
  have hp := (mem_unitIncidences 𝒜 p.1).mp p.2
  rw [compressedIncidenceLarge]
  split_ifs with hlower
  · rw [Finset.erase_right_comm]
    exact Down.erase_mem_compression hp.2
  · rw [Down.mem_compression]
    left
    refine ⟨hp.2, ?_⟩
    by_cases ha : a ∈ p.1.1.1
    · by_cases hxa : p.1.2 = a
      · simpa only [hxa, Finset.erase_idem] using hp.2
      · have hboth : p.1.1.1.erase a ∈ 𝒜 ∧
            (p.1.1.1.erase p.1.2).erase a ∈ 𝒜 := by
          by_contra h
          exact hlower ⟨ha, hxa, h⟩
        exact hboth.2
    · have hnot : a ∉ p.1.1.1.erase p.1.2 := fun h ↦ ha (Finset.mem_of_mem_erase h)
      simpa only [Finset.erase_eq_of_notMem hnot] using hp.2

private noncomputable def compressedIncidenceMap
    (𝒜 : Finset (Finset α)) (a : α) :
    ↥(unitIncidences 𝒜) → ↥(unitIncidences (Down.compression a 𝒜)) :=
  fun p ↦
    ⟨⟨⟨compressedIncidenceLarge 𝒜 a p.1,
      compressedIncidenceLarge_mem 𝒜 a p⟩, p.1.2⟩,
      (mem_unitIncidences _ _).mpr ⟨compressedIncidence_coordinate_mem 𝒜 a p,
        compressedIncidence_erase_mem 𝒜 a p⟩⟩

private lemma compressedIncidenceMap_injective
    (𝒜 : Finset (Finset α)) (a : α) :
    Function.Injective (compressedIncidenceMap 𝒜 a) := by
  intro p q hpq
  have hx : p.1.2 = q.1.2 := congrArg (fun z ↦ z.1.2) hpq
  have hlarge : compressedIncidenceLarge 𝒜 a p.1 =
      compressedIncidenceLarge 𝒜 a q.1 :=
    congrArg (fun z ↦ z.1.1.1) hpq
  have hpinc := (mem_unitIncidences 𝒜 p.1).mp p.2
  have hqinc := (mem_unitIncidences 𝒜 q.1).mp q.2
  have hset : p.1.1.1 = q.1.1.1 := by
    by_cases hpL : incidenceIsLowered 𝒜 a p.1
    · by_cases hqL : incidenceIsLowered 𝒜 a q.1
      · have herase : p.1.1.1.erase a = q.1.1.1.erase a := by
          simpa only [compressedIncidenceLarge, if_pos hpL, if_pos hqL] using hlarge
        rw [← Finset.insert_erase hpL.1, ← Finset.insert_erase hqL.1, herase]
      · have herase : p.1.1.1.erase a = q.1.1.1 := by
          simpa only [compressedIncidenceLarge, if_pos hpL, if_neg hqL] using hlarge
        have hfirst : p.1.1.1.erase a ∈ 𝒜 := by
          rw [herase]
          exact q.1.1.2
        have hsecond : (p.1.1.1.erase p.1.2).erase a ∈ 𝒜 := by
          rw [Finset.erase_right_comm, herase, hx]
          exact hqinc.2
        exact (hpL.2.2 ⟨hfirst, hsecond⟩).elim
    · by_cases hqL : incidenceIsLowered 𝒜 a q.1
      · have herase : p.1.1.1 = q.1.1.1.erase a := by
          simpa only [compressedIncidenceLarge, if_neg hpL, if_pos hqL] using hlarge
        have hfirst : q.1.1.1.erase a ∈ 𝒜 := by
          rw [← herase]
          exact p.1.1.2
        have hsecond : (q.1.1.1.erase q.1.2).erase a ∈ 𝒜 := by
          rw [Finset.erase_right_comm, ← hx, ← herase]
          exact hpinc.2
        exact (hqL.2.2 ⟨hfirst, hsecond⟩).elim
      · simpa only [compressedIncidenceLarge, if_neg hpL, if_neg hqL] using hlarge
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hset
  · exact hx

private lemma unitDistanceEdgeCount_compression_le
    (𝒜 : Finset (Finset α)) (a : α) :
    unitDistanceEdgeCount 𝒜 ≤ unitDistanceEdgeCount (Down.compression a 𝒜) := by
  classical
  rw [← card_unitIncidences 𝒜, ← card_unitIncidences (Down.compression a 𝒜)]
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (compressedIncidenceMap 𝒜 a)
      (compressedIncidenceMap_injective 𝒜 a)

end UnitIncidence

private noncomputable def finiteFamilyMass (𝒜 : Finset (Finset α)) : ℕ := by
  classical
  exact ∑ A ∈ 𝒜, A.card

private noncomputable def downCompressedVertex
    (𝒜 : Finset (Finset α)) (a : α) (A : Finset α) : Finset α := by
  classical
  exact if A.erase a ∈ 𝒜 then A else A.erase a

section CompressionMass

local instance : DecidableEq α := Classical.decEq α

private lemma image_downCompressedVertex
    (𝒜 : Finset (Finset α)) (a : α) :
    𝒜.image (downCompressedVertex 𝒜 a) = Down.compression a 𝒜 := by
  ext A
  rw [Finset.mem_image, Down.mem_compression]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [downCompressedVertex]
    split_ifs with herase
    · exact Or.inl ⟨hB, herase⟩
    · by_cases ha : a ∈ B
      · exact Or.inr ⟨herase, by simpa only [Finset.insert_erase ha] using hB⟩
      · rw [Finset.erase_eq_of_notMem ha]
        exact Or.inl ⟨hB, by simpa only [Finset.erase_eq_of_notMem ha] using hB⟩
  · rintro (h | h)
    · exact ⟨A, h.1, by simp [downCompressedVertex, h.2]⟩
    · obtain ⟨hAnot, hins⟩ := h
      have haA : a ∉ A := by
        intro ha
        apply hAnot
        simpa only [Finset.insert_eq_self.mpr ha] using hins
      refine ⟨insert a A, hins, ?_⟩
      rw [downCompressedVertex, Finset.erase_insert haA, if_neg hAnot]

private lemma downCompressedVertex_injOn
    (𝒜 : Finset (Finset α)) (a : α) :
    Set.InjOn (downCompressedVertex 𝒜 a) 𝒜 := by
  intro A hA B hB hAB
  by_cases hAe : A.erase a ∈ 𝒜
  · by_cases hBe : B.erase a ∈ 𝒜
    · simpa only [downCompressedVertex, if_pos hAe, if_pos hBe] using hAB
    · have hEq : A = B.erase a := by
        simpa only [downCompressedVertex, if_pos hAe, if_neg hBe] using hAB
      exact (hBe (hEq ▸ hA)).elim
  · by_cases hBe : B.erase a ∈ 𝒜
    · have hEq : A.erase a = B := by
        simpa only [downCompressedVertex, if_neg hAe, if_pos hBe] using hAB
      exact (hAe (hEq ▸ hB)).elim
    · have hEq : A.erase a = B.erase a := by
        simpa only [downCompressedVertex, if_neg hAe, if_neg hBe] using hAB
      have haA : a ∈ A := by
        by_contra ha
        exact hAe (by simpa only [Finset.erase_eq_of_notMem ha] using! hA)
      have haB : a ∈ B := by
        by_contra ha
        exact hBe (by simpa only [Finset.erase_eq_of_notMem ha] using! hB)
      rw [← Finset.insert_erase haA, ← Finset.insert_erase haB, hEq]

private lemma finiteFamilyMass_compression_lt
    (𝒜 : Finset (Finset α)) (a : α)
    (hmove : ∃ A ∈ 𝒜, a ∈ A ∧ A.erase a ∉ 𝒜) :
    finiteFamilyMass (Down.compression a 𝒜) < finiteFamilyMass 𝒜 := by
  unfold finiteFamilyMass
  rw [← image_downCompressedVertex 𝒜 a,
    Finset.sum_image (downCompressedVertex_injOn 𝒜 a)]
  apply Finset.sum_lt_sum
  · intro A hA
    rw [downCompressedVertex]
    split_ifs
    · exact le_rfl
    · exact Finset.card_erase_le
  · obtain ⟨A, hA, ha, herase⟩ := hmove
    refine ⟨A, hA, ?_⟩
    rw [downCompressedVertex, if_neg herase, Finset.card_erase_of_mem ha]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega

private lemma setFamilyShatters_finsetSetFamily_iff
    (𝒜 : Finset (Finset α)) (s : Finset α) :
    SetFamilyShatters (finsetSetFamily 𝒜) s ↔ 𝒜.Shatters s := by
  constructor
  · intro h t ht
    obtain ⟨A, ⟨u, hu, rfl⟩, hA⟩ := h t ht
    refine ⟨u, hu, ?_⟩
    ext x
    by_cases hx : x ∈ s
    · simpa only [Finset.mem_inter, hx, true_and] using! (hA x hx).symm
    · have hxt : x ∉ t := fun hxt ↦ hx (ht hxt)
      simp only [Finset.mem_inter, hx, false_and, hxt]
  · intro h t ht
    obtain ⟨u, hu, hut⟩ := h ht
    refine ⟨(u : Set α), ⟨u, hu, rfl⟩, fun x hx ↦ ?_⟩
    have := Finset.ext_iff.mp hut x
    simpa only [Finset.mem_inter, hx, true_and] using! this.symm

private lemma vcIndexLE_downCompression
    (𝒜 : Finset (Finset α)) (a : α) (V : ℕ)
    (hVC : VCIndexLE (finsetSetFamily 𝒜) V) :
    VCIndexLE (finsetSetFamily (Down.compression a 𝒜)) V := by
  intro s hs hsh
  apply hVC s hs
  rw [setFamilyShatters_finsetSetFamily_iff] at hsh ⊢
  exact hsh.of_compression

end CompressionMass

section EraseClosed

local instance : DecidableEq α := Classical.decEq α

private lemma mem_of_subset_of_erase_closed
    (𝒜 : Finset (Finset α))
    (hclosed : ∀ A ∈ 𝒜, ∀ a ∈ A, A.erase a ∈ 𝒜)
    {A B : Finset α} (hA : A ∈ 𝒜) (hBA : B ⊆ A) : B ∈ 𝒜 := by
  classical
  induction hdiff : A.card - B.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
      by_cases hEq : B = A
      · simpa only [hEq] using hA
      · have hnot : ¬ A ⊆ B := fun hAB ↦ hEq (Finset.Subset.antisymm hBA hAB)
        simp only [Finset.subset_iff, not_forall] at hnot
        obtain ⟨a, haA, haB⟩ := hnot
        have hBerase : B ⊆ A.erase a := by
          intro x hxB
          exact Finset.mem_erase.mpr ⟨fun hxa ↦ haB (hxa ▸ hxB), hBA hxB⟩
        have hAerase := hclosed A hA a haA
        apply ih ((A.erase a).card - B.card)
        · rw [← hdiff]
          apply Nat.sub_lt_sub_right (Finset.card_le_card hBerase)
          rw [Finset.card_erase_of_mem haA]
          have hpos : 0 < A.card := Finset.card_pos.mpr ⟨a, haA⟩
          omega
        · exact hAerase
        · exact hBerase
        · rfl

private lemma card_lt_of_erase_closed_vc
    (𝒜 : Finset (Finset α)) (V : ℕ)
    (hclosed : ∀ A ∈ 𝒜, ∀ a ∈ A, A.erase a ∈ 𝒜)
    (hVC : VCIndexLE (finsetSetFamily 𝒜) V)
    (A : Finset α) (hA : A ∈ 𝒜) : A.card < V := by
  by_contra hnot
  apply hVC A (Nat.le_of_not_gt hnot)
  rw [setFamilyShatters_finsetSetFamily_iff]
  intro B hBA
  exact ⟨B, mem_of_subset_of_erase_closed 𝒜 hclosed hA hBA,
    Finset.inter_eq_right.mpr hBA⟩

end EraseClosed

private lemma vcIndexLE_finset_mono
    {A B : Finset (Finset α)} {V : ℕ} (hBA : B ⊆ A)
    (hVC : VCIndexLE (finsetSetFamily A) V) :
    VCIndexLE (finsetSetFamily B) V := by
  intro s hs hsh
  apply hVC s hs
  intro t ht
  obtain ⟨C, ⟨D, hD, rfl⟩, hCt⟩ := hsh t ht
  exact ⟨(D : Set α), ⟨D, hBA hD, rfl⟩, hCt⟩

section WeightedRaw

local instance : DecidableEq α := Classical.decEq α

private lemma edgeMinWeightSumRaw_sub_min
    (𝒜 : Finset (Finset α)) (W : Finset α → ℝ) (c : ℝ) :
    edgeMinWeightSumRaw 𝒜 W =
      c * unitDistanceEdgeCount 𝒜 +
        edgeMinWeightSumRaw 𝒜 (fun A ↦ W A - c) := by
  classical
  unfold edgeMinWeightSumRaw unitDistanceEdgeCount
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases herase : A.erase x ∈ 𝒜
  · simp only [herase, if_true]
    rw [min_sub_sub_right]
    ring
  · simp only [herase, if_false, add_zero]

private lemma edgeMinWeightSumRaw_erase_zero
    (𝒜 : Finset (Finset α)) (W : Finset α → ℝ)
    (hw : ∀ A ∈ 𝒜, 0 ≤ W A) (A₀ : Finset α) (hA₀ : A₀ ∈ 𝒜)
    (hzero : W A₀ = 0) :
    edgeMinWeightSumRaw 𝒜 W = edgeMinWeightSumRaw (𝒜.erase A₀) W := by
  classical
  unfold edgeMinWeightSumRaw
  have hterm : (∑ x ∈ A₀,
      if A₀.erase x ∈ 𝒜 then min (W A₀) (W (A₀.erase x)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases herase : A₀.erase x ∈ 𝒜
    · simp [herase, hzero, hw _ herase]
    · simp [herase]
  rw [← Finset.sum_erase 𝒜 hterm]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro x hx
  by_cases herase : A.erase x ∈ 𝒜
  · by_cases heq : A.erase x = A₀
    · have hAne : A ≠ A₀ := by
        intro h
        subst A
        exact (Finset.erase_ne_self.mpr hx) heq
      have hwA : 0 ≤ W A := hw A (Finset.mem_of_mem_erase hA)
      simp only [hA₀, if_true, Finset.mem_erase, heq, ne_eq,
        not_true_eq_false, false_and, if_false, hzero]
      exact min_eq_right hwA
    · have hAne : A ≠ A₀ := Finset.mem_erase.mp hA |>.1
      have herase' : A.erase x ∈ 𝒜.erase A₀ := Finset.mem_erase.mpr ⟨heq, herase⟩
      simp only [herase, herase', if_true]
  · have herase' : A.erase x ∉ 𝒜.erase A₀ := fun h ↦ herase (Finset.mem_of_mem_erase h)
    simp [herase, herase']

private lemma sum_sub_min
    (𝒜 : Finset (Finset α)) (W : Finset α → ℝ) (c : ℝ) :
    (∑ A ∈ 𝒜, W A) =
      c * 𝒜.card + ∑ A ∈ 𝒜, (W A - c) := by
  rw [Finset.sum_sub_distrib]
  simp [mul_comm]

private lemma sum_erase_zero
    (𝒜 : Finset (Finset α)) (W : Finset α → ℝ)
    (A₀ : Finset α) (hzero : W A₀ = 0) :
    (∑ A ∈ 𝒜.erase A₀, W A) = ∑ A ∈ 𝒜, W A := by
  exact Finset.sum_erase 𝒜 (by simp only [hzero])

end WeightedRaw

/-- The unit-distance graph of a family of book VC index at most `V` has
at most `(V - 1) * |𝒜|` edges. The truncated subtraction simultaneously
encodes the `V = 0` and `V = 1` boundary cases. -/
theorem unitDistance_edge_card_le
    (𝒜 : Finset (Finset α)) (V : ℕ)
    -- finite encoding of the pure VC premise.
    (hVC : VCIndexLE (finsetSetFamily 𝒜) V) :
    unitDistanceEdgeCount 𝒜 ≤ (V - 1) * 𝒜.card := by
  classical
  induction hmass : finiteFamilyMass 𝒜 using Nat.strong_induction_on generalizing 𝒜 with
  | h n ih =>
      by_cases hclosed : ∀ A ∈ 𝒜, ∀ a ∈ A, A.erase a ∈ 𝒜
      · unfold unitDistanceEdgeCount
        calc
          (∑ A ∈ 𝒜, (A.filter fun a ↦ A.erase a ∈ 𝒜).card) ≤
              ∑ A ∈ 𝒜, A.card := by
            apply Finset.sum_le_sum
            intro A _hA
            exact Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ ∑ _A ∈ 𝒜, (V - 1) := by
            apply Finset.sum_le_sum
            intro A hA
            have hlt := card_lt_of_erase_closed_vc 𝒜 V hclosed hVC A hA
            omega
          _ = (V - 1) * 𝒜.card := by simp [Nat.mul_comm]
      · simp only [not_forall] at hclosed
        obtain ⟨A, hA, a, ha, herase⟩ := hclosed
        let 𝒜' := Down.compression a 𝒜
        have hmasslt : finiteFamilyMass 𝒜' < n := by
          rw [← hmass]
          exact finiteFamilyMass_compression_lt 𝒜 a ⟨A, hA, ha, herase⟩
        have hVC' : VCIndexLE (finsetSetFamily 𝒜') V :=
          vcIndexLE_downCompression 𝒜 a V hVC
        calc
          unitDistanceEdgeCount 𝒜 ≤ unitDistanceEdgeCount 𝒜' :=
            unitDistanceEdgeCount_compression_le 𝒜 a
          _ ≤ (V - 1) * 𝒜'.card := ih _ hmasslt 𝒜' hVC' rfl
          _ = (V - 1) * 𝒜.card := by
            simp only [𝒜', Down.card_compression]

section WeightedRawBound

local instance : DecidableEq α := Classical.decEq α

private theorem edgeMinWeightSumRaw_le
    (𝒜 : Finset (Finset α)) (V : ℕ)
    (hVC : VCIndexLE (finsetSetFamily 𝒜) V)
    (W : Finset α → ℝ) (hw : ∀ A ∈ 𝒜, 0 ≤ W A) :
    edgeMinWeightSumRaw 𝒜 W ≤ (V - 1 : ℕ) * ∑ A ∈ 𝒜, W A := by
  classical
  induction hcard : 𝒜.card using Nat.strong_induction_on generalizing 𝒜 W with
  | h n ih =>
      by_cases hempty : 𝒜 = ∅
      · subst 𝒜
        simp [edgeMinWeightSumRaw]
      · have hnon : 𝒜.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        have hattach : 𝒜.attach.Nonempty := by
          rcases hnon with ⟨A, hA⟩
          exact ⟨⟨A, hA⟩, by simp⟩
        obtain ⟨A₀, _hA₀attach, hmin⟩ :=
          Finset.exists_min_image 𝒜.attach (fun A ↦ W A.1) hattach
        let c := W A₀.1
        let W' : Finset α → ℝ := fun A ↦ W A - c
        let 𝒜' := 𝒜.erase A₀.1
        have hc0 : 0 ≤ c := hw A₀.1 A₀.2
        have hc : ∀ A ∈ 𝒜, c ≤ W A := by
          intro A hA
          exact hmin ⟨A, hA⟩ (by simp)
        have hw' : ∀ A ∈ 𝒜, 0 ≤ W' A := by
          intro A hA
          exact sub_nonneg.mpr (hc A hA)
        have hzero : W' A₀.1 = 0 := by simp [W', c]
        have hcardlt : 𝒜'.card < n := by
          dsimp only [𝒜']
          rw [Finset.card_erase_of_mem A₀.2, hcard]
          have hpos : 0 < n := by simpa only [← hcard] using Finset.card_pos.mpr hnon
          omega
        have hVC' : VCIndexLE (finsetSetFamily 𝒜') V :=
          vcIndexLE_finset_mono (Finset.erase_subset _ _) hVC
        have hih : edgeMinWeightSumRaw 𝒜' W' ≤
            (V - 1 : ℕ) * ∑ A ∈ 𝒜', W' A :=
          ih _ hcardlt 𝒜' hVC' W' (fun A hA ↦ hw' A (Finset.mem_of_mem_erase hA)) rfl
        rw [sum_erase_zero 𝒜 W' A₀.1 hzero] at hih
        have hedgeNat := unitDistance_edge_card_le 𝒜 V hVC
        have hedgeReal : (unitDistanceEdgeCount 𝒜 : ℝ) ≤
            ((V - 1 : ℕ) : ℝ) * (𝒜.card : ℝ) := by exact_mod_cast hedgeNat
        have hedgeWeighted : c * (unitDistanceEdgeCount 𝒜 : ℝ) ≤
            ((V - 1 : ℕ) : ℝ) * (c * (𝒜.card : ℝ)) := by
          nlinarith
        rw [edgeMinWeightSumRaw_sub_min 𝒜 W c,
          edgeMinWeightSumRaw_erase_zero 𝒜 W' hw' A₀.1 A₀.2 hzero,
          sum_sub_min 𝒜 W c]
        calc
          c * (unitDistanceEdgeCount 𝒜 : ℝ) + edgeMinWeightSumRaw 𝒜' W' ≤
              ((V - 1 : ℕ) : ℝ) * (c * (𝒜.card : ℝ)) +
                ((V - 1 : ℕ) : ℝ) * ∑ A ∈ 𝒜, W' A :=
            add_le_add hedgeWeighted hih
          _ = ((V - 1 : ℕ) : ℝ) *
                (c * (𝒜.card : ℝ) + ∑ A ∈ 𝒜, (W A - c)) := by
            dsimp only [W']
            ring

end WeightedRawBound

/-- Sharp weighted unit-distance/degeneracy estimate. Each unoriented
edge contributes the smaller endpoint weight, with no extraneous factor two. -/
theorem weightedUnitDistance_le
    (𝒜 : Finset (Finset α)) (V : ℕ)
    -- finite encoding of the pure VC premise.
    (hVC : VCIndexLE (finsetSetFamily 𝒜) V)
    (w : ↥𝒜 → ℝ)
    -- positivity required by the weighted counting argument.
    (hw : ∀ A, 0 ≤ w A) :
    edgeMinWeightSum 𝒜 w ≤ (V - 1 : ℕ) * ∑ A, w A := by
  classical
  unfold edgeMinWeightSum
  have hraw := edgeMinWeightSumRaw_le 𝒜 V hVC
    (extendSubtypeWeight 𝒜 w) (by
      intro A hA
      simpa only [extendSubtypeWeight, hA, dite_true] using hw ⟨A, hA⟩)
  have hsum : (∑ A : ↥𝒜, w A) =
      ∑ A ∈ 𝒜, extendSubtypeWeight 𝒜 w A := by
    symm
    rw [Finset.sum_subtype 𝒜 (fun _ ↦ Iff.rfl)]
    apply Finset.sum_congr rfl
    intro A _hA
    rw [extendSubtypeWeight, dif_pos A.2]
  rw [hsum]
  exact hraw

/-- Delete one carrier coordinate from every member of a finite set family.

This is the deterministic outcome underlying uniform random coordinate
deletion. Duplicate images are collapsed by `Finset.image`. Edge behavior:
deleting a coordinate absent from every member leaves the family unchanged. -/
noncomputable def coordinateDeletionFamily (𝒜 : Finset (Finset α)) (x : α) :
    Finset (Finset α) := by
  classical
  exact 𝒜.image fun A ↦ A.erase x

private noncomputable def verticalEdgeCount
    (𝒜 : Finset (Finset α)) (x : α) : ℕ := by
  classical
  exact (𝒜.filter fun A ↦ x ∈ A ∧ A.erase x ∈ 𝒜).card

section VerticalEdges

local instance : DecidableEq α := Classical.decEq α

private lemma image_erase_verticalFamily
    (𝒜 : Finset (Finset α)) (x : α) :
    (𝒜.filter fun A ↦ x ∈ A ∧ A.erase x ∈ 𝒜).image (·.erase x) =
      𝒜.memberSubfamily x ∩ 𝒜.nonMemberSubfamily x := by
  classical
  ext B
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_memberSubfamily, Finset.mem_nonMemberSubfamily]
  constructor
  · rintro ⟨A, ⟨hA, hxA, herase⟩, rfl⟩
    refine ⟨⟨?_, Finset.notMem_erase _ _⟩, herase, Finset.notMem_erase _ _⟩
    simpa only [Finset.insert_erase hxA] using hA
  · rintro ⟨⟨hins, hxB⟩, hB, -⟩
    refine ⟨insert x B, ⟨hins, Finset.mem_insert_self _ _, ?_⟩, ?_⟩
    · simpa [Finset.erase_insert hxB] using hB
    · exact Finset.erase_insert hxB

private lemma verticalEdgeCount_eq_card_inter
    (𝒜 : Finset (Finset α)) (x : α) :
    verticalEdgeCount 𝒜 x =
      (𝒜.memberSubfamily x ∩ 𝒜.nonMemberSubfamily x).card := by
  classical
  rw [verticalEdgeCount, ← image_erase_verticalFamily 𝒜 x]
  symm
  apply Finset.card_image_of_injOn
  apply (Finset.erase_injOn' x).mono
  intro A hA
  exact (Finset.mem_filter.mp hA).2.1

private lemma coordinateDeletion_card_add_verticalEdgeCount
    (𝒜 : Finset (Finset α)) (x : α) :
    (coordinateDeletionFamily 𝒜 x).card + verticalEdgeCount 𝒜 x = 𝒜.card := by
  classical
  rw [coordinateDeletionFamily, ← Finset.memberSubfamily_union_nonMemberSubfamily,
    verticalEdgeCount_eq_card_inter, Finset.card_union_add_card_inter,
    Finset.card_memberSubfamily_add_card_nonMemberSubfamily]

private lemma unitDistanceEdgeCount_eq_sum_vertical
    (𝒜 : Finset (Finset α)) (t : Finset α)
    (hₜ : ∀ A ∈ 𝒜, A ⊆ t) :
    unitDistanceEdgeCount 𝒜 = ∑ x ∈ t, verticalEdgeCount 𝒜 x := by
  classical
  unfold unitDistanceEdgeCount verticalEdgeCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ B ∈ 𝒜, ∑ x ∈ B, if B.erase x ∈ 𝒜 then 1 else 0) =
        ∑ B ∈ 𝒜, ∑ x ∈ t,
          if x ∈ B ∧ B.erase x ∈ 𝒜 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      calc
        (∑ x ∈ B, if B.erase x ∈ 𝒜 then 1 else 0) =
            ∑ x ∈ B, if x ∈ B ∧ B.erase x ∈ 𝒜 then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x hxB
          simp only [hxB, true_and]
        _ = ∑ x ∈ t, if x ∈ B ∧ B.erase x ∈ 𝒜 then 1 else 0 :=
          Finset.sum_subset (hₜ B hB) fun y _ hyB ↦ by simp [hyB]
    _ = ∑ x ∈ t, ∑ B ∈ 𝒜,
          if x ∈ B ∧ B.erase x ∈ 𝒜 then 1 else 0 := Finset.sum_comm

end VerticalEdges

/-- Restrict every member of a finite set family to a sampled coordinate set.

This is the trace family seen by a random finite subset in the deletion
double count. Duplicate traces are collapsed. Edge behavior: restriction to
the empty sample is empty for an empty family and `{∅}` otherwise. -/
noncomputable def restrictionFamily (𝒜 : Finset (Finset α)) (t : Finset α) :
    Finset (Finset α) := by
  classical
  exact 𝒜.image fun A ↦ A ∩ t

/-- Unweighted deletion identity in inequality form. After summing over all
`n`-coordinate subsets, coordinate-deletion losses dominate the total number
of unit-distance edges in the induced trace families. -/
theorem randomDeletion_edgeCount_le_cardinalityLoss
    (𝒜 : Finset (Finset α)) (s : Finset α) (n : ℕ) :
    (∑ t ∈ s.powersetCard n, unitDistanceEdgeCount (restrictionFamily 𝒜 t)) ≤
      ∑ t ∈ s.powersetCard n, ∑ x ∈ t,
        ((restrictionFamily 𝒜 t).card -
          (coordinateDeletionFamily (restrictionFamily 𝒜 t) x).card) := by
  classical
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro t _ht
  rw [unitDistanceEdgeCount_eq_sum_vertical]
  · apply Finset.sum_congr rfl
    intro x _hx
    have hcard := coordinateDeletion_card_add_verticalEdgeCount
      (restrictionFamily 𝒜 t) x
    omega
  · intro B hB
    simp only [restrictionFamily, Finset.mem_image] at hB
    obtain ⟨A, _hA, rfl⟩ := hB
    exact Finset.inter_subset_right

/-- Multiplicity of a trace after restricting the original packing to `t`.

This is the vertex weight in the weighted Chazelle--Haussler graph: it counts
original packing members producing the given trace. Edge behavior: every
vertex of the restriction family has positive multiplicity; multiplicities
sum to the cardinality of the original packing. -/
noncomputable def restrictionMultiplicity (P : Finset (Finset α))
    (t : Finset α) (B : ↥(restrictionFamily P t)) : ℝ := by
  classical
  exact ((P.filter fun A ↦ A ∩ t = B.1).card : ℝ)

section RestrictionMultiplicity

local instance : DecidableEq α := Classical.decEq α

private noncomputable def traceFiber
    (P : Finset (Finset α)) (t B : Finset α) : Finset (Finset α) := by
  classical
  exact P.filter fun A ↦ A ∩ t = B

private noncomputable def traceFiberOn
    (P : Finset (Finset α)) (t B : Finset α) (x : α) : Finset (Finset α) := by
  classical
  exact (traceFiber P t B).filter fun A ↦ x ∈ A

private noncomputable def traceFiberOff
    (P : Finset (Finset α)) (t B : Finset α) (x : α) : Finset (Finset α) := by
  classical
  exact (traceFiber P t B).filter fun A ↦ x ∉ A

private lemma pairCrossingSum
    (Q : Finset (Finset α)) (x : α) :
    (∑ A ∈ Q, ∑ B ∈ Q,
      if (x ∈ A ↔ x ∉ B) then (1 : ℝ) else 0) =
      2 * ((Q.filter fun A ↦ x ∈ A).card : ℝ) *
        ((Q.filter fun A ↦ x ∉ A).card : ℝ) := by
  classical
  have hinner (A : Finset α) :
      (∑ B ∈ Q, if (x ∈ A ↔ x ∉ B) then (1 : ℝ) else 0) =
        if x ∈ A then (Q.filter fun B ↦ x ∉ B).card
        else (Q.filter fun B ↦ x ∈ B).card := by
    by_cases hxA : x ∈ A
    · rw [if_pos hxA]
      simpa only [hxA, true_iff] using
        (Finset.sum_boole (fun B ↦ x ∉ B) Q :
          (∑ B ∈ Q, if x ∉ B then (1 : ℝ) else 0) = _)
    · rw [if_neg hxA]
      simpa only [hxA, false_iff, not_not] using
        (Finset.sum_boole (fun B ↦ x ∈ B) Q :
          (∑ B ∈ Q, if x ∈ B then (1 : ℝ) else 0) = _)
  simp_rw [hinner, Nat.cast_ite]
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun A ↦ x ∈ A)
    (fun A ↦ if x ∈ A then ((Q.filter fun B ↦ x ∉ B).card : ℝ)
      else ((Q.filter fun B ↦ x ∈ B).card : ℝ))]
  have h₁ :
      (∑ A ∈ Q.filter (fun A ↦ x ∈ A),
        if x ∈ A then ((Q.filter fun B ↦ x ∉ B).card : ℝ)
        else ((Q.filter fun B ↦ x ∈ B).card : ℝ)) =
      ∑ _A ∈ Q.filter (fun A ↦ x ∈ A),
        ((Q.filter fun B ↦ x ∉ B).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro A hA
    rw [if_pos (Finset.mem_filter.mp hA).2]
  have h₂ :
      (∑ A ∈ Q.filter (fun A ↦ x ∉ A),
        if x ∈ A then ((Q.filter fun B ↦ x ∉ B).card : ℝ)
        else ((Q.filter fun B ↦ x ∈ B).card : ℝ)) =
      ∑ _A ∈ Q.filter (fun A ↦ x ∉ A),
        ((Q.filter fun B ↦ x ∈ B).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro A hA
    rw [if_neg (Finset.mem_filter.mp hA).2]
  rw [h₁, h₂]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

private lemma hammingDistance_eq_crossingSum
    (s A B : Finset α) (hA : A ⊆ s) (hB : B ⊆ s) :
    (finsetHammingDistance A B : ℝ) =
      ∑ x ∈ s, if (x ∈ A ↔ x ∉ B) then (1 : ℝ) else 0 := by
  have hsub : (A \ B) ∪ (B \ A) ⊆ s := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hA (Finset.mem_sdiff.mp hx).1
    · exact hB (Finset.mem_sdiff.mp hx).1
  change ((((A \ B) ∪ (B \ A)).card : ℕ) : ℝ) = _
  rw [Finset.card_eq_sum_ones]
  push_cast
  calc
    (∑ _x ∈ (A \ B) ∪ (B \ A), (1 : ℝ)) =
        ∑ x ∈ (A \ B) ∪ (B \ A),
          if (x ∈ A ↔ x ∉ B) then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_union, Finset.mem_sdiff] at hx
      rcases hx with ⟨hxA, hxB⟩ | ⟨hxB, hxA⟩
      · rw [if_pos ⟨fun _ ↦ hxB, fun _ ↦ hxA⟩]
      · rw [if_pos ⟨fun h ↦ False.elim (hxA h),
          fun h ↦ False.elim (h hxB)⟩]
    _ = ∑ x ∈ s, if (x ∈ A ↔ x ∉ B) then (1 : ℝ) else 0 := by
      apply Finset.sum_subset hsub
      intro x _hx hnot
      rw [if_neg]
      intro hxor
      by_cases hxA : x ∈ A
      · exact hnot (Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨hxA, hxor.mp hxA⟩))
      · have hxB : x ∈ B := Classical.byContradiction fun hnB ↦ hxA (hxor.mpr hnB)
        exact hnot (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hxB, hxA⟩))

private lemma orderedHammingSum_eq_crossingSum
    (Q : Finset (Finset α)) (s : Finset α)
    (hsupp : ∀ A ∈ Q, A ⊆ s) :
    (∑ A ∈ Q, ∑ B ∈ Q, (finsetHammingDistance A B : ℝ)) =
      ∑ x ∈ s, 2 * ((Q.filter fun A ↦ x ∈ A).card : ℝ) *
        ((Q.filter fun A ↦ x ∉ A).card : ℝ) := by
  calc
    (∑ A ∈ Q, ∑ B ∈ Q, (finsetHammingDistance A B : ℝ)) =
        ∑ A ∈ Q, ∑ B ∈ Q, ∑ x ∈ s,
          if (x ∈ A ↔ x ∉ B) then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro B hB
      exact hammingDistance_eq_crossingSum s A B (hsupp A hA) (hsupp B hB)
    _ = ∑ A ∈ Q, ∑ x ∈ s, ∑ B ∈ Q,
          if (x ∈ A ↔ x ∉ B) then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.sum_comm]
    _ = ∑ x ∈ s, ∑ A ∈ Q, ∑ B ∈ Q,
          if (x ∈ A ↔ x ∉ B) then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact pairCrossingSum Q x

private lemma orderedHammingSum_lower
    (Q : Finset (Finset α)) (s : Finset α) (δ : ℝ)
    (hsep : ∀ A ∈ Q, ∀ B ∈ Q, A ≠ B →
      δ * s.card < finsetHammingDistance A B) :
    δ * s.card * (Q.card : ℝ) * ((Q.card - 1 : ℕ) : ℝ) ≤
      ∑ A ∈ Q, ∑ B ∈ Q, (finsetHammingDistance A B : ℝ) := by
  calc
    δ * s.card * (Q.card : ℝ) * ((Q.card - 1 : ℕ) : ℝ) =
        ∑ A ∈ Q, δ * s.card * ((Q.card - 1 : ℕ) : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ A ∈ Q, ∑ B ∈ Q, (finsetHammingDistance A B : ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      calc
        δ * s.card * ((Q.card - 1 : ℕ) : ℝ) =
            ∑ _B ∈ Q.erase A, δ * s.card := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            Finset.card_erase_of_mem hA]
          ring
        _ ≤ ∑ B ∈ Q.erase A, (finsetHammingDistance A B : ℝ) := by
          apply Finset.sum_le_sum
          intro B hB
          have hB' := Finset.mem_of_mem_erase hB
          have hne := Finset.ne_of_mem_erase hB
          exact (hsep A hA B hB' hne.symm).le
        _ = ∑ B ∈ Q, (finsetHammingDistance A B : ℝ) := by
          rw [← Finset.sum_erase_add _ _ hA]
          simp [finsetHammingDistance]

private lemma crossingProduct_le_card_mul_min
    (Q : Finset (Finset α)) (x : α) :
    ((Q.filter fun A ↦ x ∈ A).card : ℝ) *
        ((Q.filter fun A ↦ x ∉ A).card : ℝ) ≤
      Q.card * min ((Q.filter fun A ↦ x ∈ A).card : ℝ)
        ((Q.filter fun A ↦ x ∉ A).card : ℝ) := by
  have hon : (Q.filter fun A ↦ x ∈ A).card ≤ Q.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hoff : (Q.filter fun A ↦ x ∉ A).card ≤ Q.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hon' : ((Q.filter fun A ↦ x ∈ A).card : ℝ) ≤ Q.card := by exact_mod_cast hon
  have hoff' : ((Q.filter fun A ↦ x ∉ A).card : ℝ) ≤ Q.card := by exact_mod_cast hoff
  have hon0 : 0 ≤ ((Q.filter fun A ↦ x ∈ A).card : ℝ) := by positivity
  have hoff0 : 0 ≤ ((Q.filter fun A ↦ x ∉ A).card : ℝ) := by positivity
  by_cases hle : (Q.filter fun A ↦ x ∈ A).card ≤
      (Q.filter fun A ↦ x ∉ A).card
  · rw [min_eq_left (by exact_mod_cast hle)]
    nlinarith
  · have hle' : (Q.filter fun A ↦ x ∉ A).card ≤
        (Q.filter fun A ↦ x ∈ A).card := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    rw [min_eq_right (by exact_mod_cast hle')]
    nlinarith

private lemma fiberSplit_lower
    (Q : Finset (Finset α)) (s : Finset α) (δ : ℝ)
    (hQ : Q.Nonempty) (hsupp : ∀ A ∈ Q, A ⊆ s)
    (hsep : ∀ A ∈ Q, ∀ B ∈ Q, A ≠ B →
      δ * s.card < finsetHammingDistance A B) :
    (δ * s.card / 2) * ((Q.card - 1 : ℕ) : ℝ) ≤
      ∑ x ∈ s, min ((Q.filter fun A ↦ x ∈ A).card : ℝ)
        ((Q.filter fun A ↦ x ∉ A).card : ℝ) := by
  have hlower := orderedHammingSum_lower Q s δ hsep
  rw [orderedHammingSum_eq_crossingSum Q s hsupp] at hlower
  have hupper :
      (∑ x ∈ s, 2 * ((Q.filter fun A ↦ x ∈ A).card : ℝ) *
        ((Q.filter fun A ↦ x ∉ A).card : ℝ)) ≤
      2 * (Q.card : ℝ) *
        ∑ x ∈ s, min ((Q.filter fun A ↦ x ∈ A).card : ℝ)
          ((Q.filter fun A ↦ x ∉ A).card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ s, 2 * (Q.card : ℝ) *
          min ((Q.filter fun A ↦ x ∈ A).card : ℝ)
            ((Q.filter fun A ↦ x ∉ A).card : ℝ) := by
        apply Finset.sum_le_sum
        intro x _hx
        nlinarith [crossingProduct_le_card_mul_min Q x]
      _ = _ := by
        rw [← Finset.mul_sum]
  have hk : 0 < (Q.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hQ
  nlinarith

private lemma vcIndexLE_restrictionFamily
    (P : Finset (Finset α)) (t : Finset α) (V : ℕ)
    (hVC : VCIndexLE (finsetSetFamily P) V) :
    VCIndexLE (finsetSetFamily (restrictionFamily P t)) V := by
  intro q hV hsh
  apply hVC q hV
  have hqt : q ⊆ t := by
    obtain ⟨B, hB, hqB⟩ := hsh q (Finset.Subset.rfl)
    simp only [finsetSetFamily, Set.mem_setOf_eq] at hB
    obtain ⟨B', hB', rfl⟩ := hB
    simp only [restrictionFamily, Finset.mem_image] at hB'
    obtain ⟨A, _hA, rfl⟩ := hB'
    intro x hx
    have hxinter : x ∈ A ∩ t := (hqB x hx).mp hx
    exact Finset.mem_inter.mp hxinter |>.2
  intro r hr
  obtain ⟨B, hB, hrB⟩ := hsh r hr
  simp only [finsetSetFamily, Set.mem_setOf_eq] at hB
  obtain ⟨B', hB', rfl⟩ := hB
  simp only [restrictionFamily, Finset.mem_image] at hB'
  obtain ⟨A, hA, rfl⟩ := hB'
  refine ⟨(A : Set α), ?_, ?_⟩
  · exact ⟨A, hA, rfl⟩
  · intro x hxq
    rw [hrB x hxq]
    constructor
    · intro hx
      exact (Finset.mem_inter.mp hx).1
    · intro hx
      exact Finset.mem_inter.mpr ⟨hx, hqt hxq⟩

private lemma sum_restrictionMultiplicity
    (P : Finset (Finset α)) (t : Finset α) :
    ∑ B : ↥(restrictionFamily P t), restrictionMultiplicity P t B = P.card := by
  classical
  have hmaps : (P : Set (Finset α)).MapsTo (fun A ↦ A ∩ t)
      (restrictionFamily P t : Set (Finset α)) := by
    intro A hA
    exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
  have hcard : P.card = ∑ B ∈ restrictionFamily P t,
      (P.filter fun A ↦ A ∩ t = B).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  calc
    ∑ B : ↥(restrictionFamily P t), restrictionMultiplicity P t B =
        ∑ B ∈ restrictionFamily P t,
          ((P.filter fun A ↦ A ∩ t = B).card : ℝ) := by
      symm
      rw [Finset.sum_subtype (restrictionFamily P t) (fun _ ↦ Iff.rfl)]
      apply Finset.sum_congr rfl
      intro B _hB
      simp only [restrictionMultiplicity]
    _ = P.card := by exact_mod_cast hcard.symm

private lemma traceFiber_nonempty
    (P : Finset (Finset α)) (t B : Finset α)
    (hB : B ∈ restrictionFamily P t) :
    (traceFiber P t B).Nonempty := by
  simp only [restrictionFamily, Finset.mem_image] at hB
  obtain ⟨A, hA, hAt⟩ := hB
  refine ⟨A, ?_⟩
  simp only [traceFiber, Finset.mem_filter]
  exact ⟨hA, hAt⟩

private lemma restriction_cardinalityLoss_eq_sum
    (P : Finset (Finset α)) (t : Finset α) :
    P.card - (restrictionFamily P t).card =
      ∑ B ∈ restrictionFamily P t, ((traceFiber P t B).card - 1) := by
  classical
  have hmaps : (P : Set (Finset α)).MapsTo (fun A ↦ A ∩ t)
      (restrictionFamily P t : Set (Finset α)) := by
    intro A hA
    exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
  have hcard : P.card = ∑ B ∈ restrictionFamily P t,
      (traceFiber P t B).card := by
    simpa only [traceFiber] using Finset.card_eq_sum_card_fiberwise hmaps
  calc
    P.card - (restrictionFamily P t).card =
        (∑ B ∈ restrictionFamily P t, (traceFiber P t B).card) -
          ∑ _B ∈ restrictionFamily P t, 1 := by
      rw [← hcard]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
    _ = ∑ B ∈ restrictionFamily P t, ((traceFiber P t B).card - 1) := by
      exact (Finset.sum_tsub_distrib (restrictionFamily P t)
        (f := fun B ↦ (traceFiber P t B).card) (g := fun _ ↦ 1)
        (fun B hB ↦ Finset.one_le_card.mpr
          (traceFiber_nonempty P t B hB))).symm

private lemma traceFiber_support
    (P : Finset (Finset α)) (s t B : Finset α)
    (hsupp : ∀ A ∈ P, A ⊆ s) :
    ∀ A ∈ traceFiber P t B, A ⊆ s := by
  intro A hA
  exact hsupp A (Finset.mem_filter.mp hA).1

private lemma traceFiber_separated
    (P : Finset (Finset α)) (s t B : Finset α) (δ : ℝ)
    (hsep : ∀ A ∈ P, ∀ C ∈ P, A ≠ C →
      δ * s.card < finsetHammingDistance A C) :
    ∀ A ∈ traceFiber P t B, ∀ C ∈ traceFiber P t B, A ≠ C →
      δ * s.card < finsetHammingDistance A C := by
  intro A hA C hC hne
  exact hsep A (Finset.mem_filter.mp hA).1 C (Finset.mem_filter.mp hC).1 hne

private lemma fixedRestriction_split_zero
    (P : Finset (Finset α)) (t B : Finset α) (x : α)
    (hx : x ∈ t) :
    min ((traceFiberOn P t B x).card : ℝ)
      ((traceFiberOff P t B x).card : ℝ) = 0 := by
  by_cases hxB : x ∈ B
  · have hoff : traceFiberOff P t B x = ∅ := by
      ext A
      constructor
      · intro hA
        exfalso
        simp only [traceFiberOff, traceFiber, Finset.mem_filter] at hA
        rcases hA with ⟨⟨_hA, hAt⟩, hxA⟩
        have hi := congrArg (fun C : Finset α ↦ x ∈ C) hAt
        have hxAt : x ∈ A ∩ t := hi.symm.mp hxB
        exact hxA (Finset.mem_inter.mp hxAt).1
      · intro hA
        simp at hA
    simp [hoff]
  · have hon : traceFiberOn P t B x = ∅ := by
      ext A
      constructor
      · intro hA
        exfalso
        simp only [traceFiberOn, traceFiber, Finset.mem_filter] at hA
        rcases hA with ⟨⟨_hA, hAt⟩, hxA⟩
        apply hxB
        have hi := congrArg (fun C : Finset α ↦ x ∈ C) hAt
        exact hi.mp (Finset.mem_inter.mpr ⟨hxA, hx⟩)
      · intro hA
        simp at hA
    simp [hon]

private lemma fiberSplit_lower_off_sample
    (P : Finset (Finset α)) (s t B : Finset α) (δ : ℝ)
    (hsupp : ∀ A ∈ P, A ⊆ s)
    (hsep : ∀ A ∈ P, ∀ C ∈ P, A ≠ C →
      δ * s.card < finsetHammingDistance A C)
    (hB : B ∈ restrictionFamily P t) :
    (δ * s.card / 2) * (((traceFiber P t B).card - 1 : ℕ) : ℝ) ≤
      ∑ x ∈ s.filter (fun x ↦ x ∉ t),
        min ((traceFiberOn P t B x).card : ℝ)
          ((traceFiberOff P t B x).card : ℝ) := by
  have h := fiberSplit_lower (traceFiber P t B) s δ
    (traceFiber_nonempty P t B hB)
    (traceFiber_support P s t B hsupp)
    (traceFiber_separated P s t B δ hsep)
  calc
    _ ≤ ∑ x ∈ s, min ((traceFiber P t B).filter (fun A ↦ x ∈ A) |>.card : ℝ)
          ((traceFiber P t B).filter (fun A ↦ x ∉ A) |>.card : ℝ) := h
    _ = ∑ x ∈ s.filter (fun x ↦ x ∉ t),
        min ((traceFiberOn P t B x).card : ℝ)
          ((traceFiberOff P t B x).card : ℝ) := by
      change (∑ x ∈ s, min ((traceFiberOn P t B x).card : ℝ)
          ((traceFiberOff P t B x).card : ℝ)) = _
      rw [← Finset.sum_filter_add_sum_filter_not s (fun x ↦ x ∉ t)
        (fun x ↦ min ((traceFiberOn P t B x).card : ℝ)
          ((traceFiberOff P t B x).card : ℝ))]
      simp only [not_not]
      have hzero : (∑ x ∈ s.filter (fun x ↦ x ∈ t),
          min ((traceFiberOn P t B x).card : ℝ)
            ((traceFiberOff P t B x).card : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        exact fixedRestriction_split_zero P t B x (Finset.mem_filter.mp hx).2
      rw [hzero, add_zero]

private lemma restrictionLoss_lower_splitSum
    (P : Finset (Finset α)) (s t : Finset α) (δ : ℝ)
    (hsupp : ∀ A ∈ P, A ⊆ s)
    (hsep : ∀ A ∈ P, ∀ C ∈ P, A ≠ C →
      δ * s.card < finsetHammingDistance A C) :
    (δ * s.card / 2) *
        ((P.card - (restrictionFamily P t).card : ℕ) : ℝ) ≤
      ∑ B ∈ restrictionFamily P t,
        ∑ x ∈ s.filter (fun x ↦ x ∉ t),
          min ((traceFiberOn P t B x).card : ℝ)
            ((traceFiberOff P t B x).card : ℝ) := by
  rw [restriction_cardinalityLoss_eq_sum]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  exact fiberSplit_lower_off_sample P s t B δ hsupp hsep hB

private lemma extensionDeletion_sum
    (s : Finset α) (m : ℕ) (F : Finset α → α → ℝ) :
    (∑ t ∈ s.powersetCard m, ∑ x ∈ s.filter (fun x ↦ x ∉ t), F t x) =
      ∑ u ∈ s.powersetCard (m + 1), ∑ x ∈ u, F (u.erase x) x := by
  classical
  let S := ((s.powersetCard m).product s).filter fun p ↦ p.2 ∉ p.1
  let T := ((s.powersetCard (m + 1)).product s).filter fun p ↦ p.2 ∈ p.1
  have hS : (∑ t ∈ s.powersetCard m,
      ∑ x ∈ s.filter (fun x ↦ x ∉ t), F t x) =
      ∑ p ∈ S, F p.1 p.2 := by
    simp only [S, Finset.sum_filter]
    exact (Finset.sum_product ((s.powersetCard m)) s
      (fun p ↦ if p.2 ∉ p.1 then F p.1 p.2 else 0)).symm
  have hT : (∑ u ∈ s.powersetCard (m + 1), ∑ x ∈ u, F (u.erase x) x) =
      ∑ p ∈ T, F (p.1.erase p.2) p.2 := by
    simp only [T, Finset.sum_filter]
    calc
      (∑ u ∈ s.powersetCard (m + 1), ∑ x ∈ u, F (u.erase x) x) =
          ∑ u ∈ s.powersetCard (m + 1), ∑ x ∈ s,
            if x ∈ u then F (u.erase x) x else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        have hus := (Finset.mem_powersetCard.mp hu).1
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hus]
      _ = ∑ p ∈ (s.powersetCard (m + 1)).product s,
          if p.2 ∈ p.1 then F (p.1.erase p.2) p.2 else 0 :=
        (Finset.sum_product ((s.powersetCard (m + 1))) s
          (fun p ↦ if p.2 ∈ p.1 then F (p.1.erase p.2) p.2 else 0)).symm
  rw [hS, hT]
  apply Finset.sum_nbij'
      (fun p ↦ (insert p.2 p.1, p.2))
      (fun p ↦ (p.1.erase p.2, p.2))
  · intro p hp
    simp only [S, Finset.mem_filter] at hp
    obtain ⟨hprod, hxt⟩ := hp
    obtain ⟨ht, hxs⟩ := Finset.mem_product.mp hprod
    obtain ⟨hts, hcard⟩ := Finset.mem_powersetCard.mp ht
    simp only [T, Finset.mem_filter]
    apply And.intro
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, hxs⟩
      · exact Finset.insert_subset hxs hts
      · simp [hxt, hcard]
    · exact Finset.mem_insert_self _ _
  · intro p hp
    simp only [T, Finset.mem_filter] at hp
    obtain ⟨hprod, hxu⟩ := hp
    obtain ⟨hu, hxs⟩ := Finset.mem_product.mp hprod
    obtain ⟨hus, hcard⟩ := Finset.mem_powersetCard.mp hu
    simp only [S, Finset.mem_filter]
    apply And.intro
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨
        (Finset.erase_subset _ _).trans hus, ?_⟩, hxs⟩
      rw [Finset.card_erase_of_mem hxu, hcard]
      omega
    · intro hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
  · intro p hp
    simp only [S, Finset.mem_filter] at hp
    rcases hp with ⟨_hp, hnot⟩
    simp [Finset.erase_insert hnot]
  · intro p hp
    simp only [T, Finset.mem_filter] at hp
    rcases hp with ⟨_hp, hmem⟩
    simp [Finset.insert_erase hmem]
  · intro p hp
    simp only [S, Finset.mem_filter] at hp
    exact congrArg (fun t ↦ F t p.2) (Finset.erase_insert hp.2).symm

private lemma traceFiberOn_eq_traceFiber
    (P : Finset (Finset α)) (u B : Finset α) (x : α)
    (hx : x ∈ u) (hxB : x ∉ B) :
    traceFiberOn P (u.erase x) B x = traceFiber P u (insert x B) := by
  ext A
  simp only [traceFiberOn, traceFiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hA, hAt⟩, hxA⟩
    refine ⟨hA, ?_⟩
    ext y
    by_cases hyx : y = x
    · subst y
      simp [hx, hxB, hxA]
    · have hAt' := congrArg (fun C : Finset α ↦ y ∈ C) hAt
      simpa [Finset.mem_inter, Finset.mem_erase, hyx] using hAt'
  · rintro ⟨hA, hAu⟩
    refine ⟨⟨hA, ?_⟩, ?_⟩
    · ext y
      have hAu' := congrArg (fun C : Finset α ↦ y ∈ C) hAu
      by_cases hyx : y = x
      · subst y
        simp [hxB]
      · simpa [Finset.mem_inter, Finset.mem_erase, hyx] using hAu'
    · have hAu' := congrArg (fun C : Finset α ↦ x ∈ C) hAu
      simpa [hx, hxB] using hAu'

private lemma traceFiberOff_eq_traceFiber
    (P : Finset (Finset α)) (u B : Finset α) (x : α)
    (hx : x ∈ u) (hxB : x ∉ B) :
    traceFiberOff P (u.erase x) B x = traceFiber P u B := by
  ext A
  simp only [traceFiberOff, traceFiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hA, hAt⟩, hxA⟩
    refine ⟨hA, ?_⟩
    ext y
    by_cases hyx : y = x
    · subst y
      simp [hxB, hxA]
    · have hAt' := congrArg (fun C : Finset α ↦ y ∈ C) hAt
      simpa [Finset.mem_inter, Finset.mem_erase, hyx] using hAt'
  · rintro ⟨hA, hAu⟩
    refine ⟨⟨hA, ?_⟩, ?_⟩
    · ext y
      have hAu' := congrArg (fun C : Finset α ↦ y ∈ C) hAu
      by_cases hyx : y = x
      · subst y
        simp [hxB]
      · simpa [Finset.mem_inter, Finset.mem_erase, hyx] using hAu'
    · intro hxA
      have hAu' := congrArg (fun C : Finset α ↦ x ∈ C) hAu
      have : x ∈ B := hAu'.mp (Finset.mem_inter.mpr ⟨hxA, hx⟩)
      exact hxB this

private lemma restrictionMultiplicity_eq_traceFiber_card
    (P : Finset (Finset α)) (u B : Finset α)
    (hB : B ∈ restrictionFamily P u) :
    restrictionMultiplicity P u ⟨B, hB⟩ = (traceFiber P u B).card := by
  simp only [restrictionMultiplicity, traceFiber]

private lemma restrictionFamily_erase_image
    (P : Finset (Finset α)) (u : Finset α) (x : α) :
    restrictionFamily P (u.erase x) =
      (restrictionFamily P u).image (fun B ↦ B.erase x) := by
  ext B
  simp only [restrictionFamily, Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A ∩ u, ⟨A, hA, rfl⟩, ?_⟩
    ext y
    simp [Finset.mem_inter, Finset.mem_erase]
    aesop
  · rintro ⟨C, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨A, hA, ?_⟩
    ext y
    simp [Finset.mem_inter, Finset.mem_erase]
    aesop

private noncomputable def coordinateTraceEdgeWeight
    (P : Finset (Finset α)) (u : Finset α) (x : α) : ℝ := by
  classical
  exact ∑ C ∈ restrictionFamily P u,
    if x ∈ C ∧ C.erase x ∈ restrictionFamily P u then
      min ((traceFiber P u C).card : ℝ)
        ((traceFiber P u (C.erase x)).card : ℝ)
    else 0

private lemma restrictionFamily_member_subset
    (P : Finset (Finset α)) (u B : Finset α)
    (hB : B ∈ restrictionFamily P u) : B ⊆ u := by
  simp only [restrictionFamily, Finset.mem_image] at hB
  obtain ⟨A, _hA, rfl⟩ := hB
  exact Finset.inter_subset_right

private lemma traceFiber_nonempty_iff
    (P : Finset (Finset α)) (u B : Finset α) :
    (traceFiber P u B).Nonempty ↔ B ∈ restrictionFamily P u := by
  constructor
  · rintro ⟨A, hA⟩
    simp only [traceFiber, Finset.mem_filter] at hA
    exact Finset.mem_image.mpr ⟨A, hA.1, hA.2⟩
  · exact traceFiber_nonempty P u B

private lemma traceSplit_min_eq_edgeTerm
    (P : Finset (Finset α)) (u B : Finset α) (x : α)
    (hx : x ∈ u) (hB : B ∈ restrictionFamily P (u.erase x)) :
    min ((traceFiberOn P (u.erase x) B x).card : ℝ)
        ((traceFiberOff P (u.erase x) B x).card : ℝ) =
      if insert x B ∈ restrictionFamily P u ∧ B ∈ restrictionFamily P u then
        min ((traceFiber P u (insert x B)).card : ℝ)
          ((traceFiber P u B).card : ℝ)
      else 0 := by
  have hxB : x ∉ B := by
    have hsub := restrictionFamily_member_subset P (u.erase x) B hB
    intro hxmem
    exact (Finset.mem_erase.mp (hsub hxmem)).1 rfl
  rw [traceFiberOn_eq_traceFiber P u B x hx hxB,
    traceFiberOff_eq_traceFiber P u B x hx hxB]
  by_cases hon : insert x B ∈ restrictionFamily P u
  · by_cases hoff : B ∈ restrictionFamily P u
    · rw [if_pos ⟨hon, hoff⟩]
    · rw [if_neg (fun h ↦ hoff h.2)]
      have hemp : traceFiber P u B = ∅ := by
        exact Finset.not_nonempty_iff_eq_empty.mp
          (fun hn ↦ hoff ((traceFiber_nonempty_iff P u B).mp hn))
      simp [hemp]
  · rw [if_neg (fun h ↦ hon h.1)]
    have hemp : traceFiber P u (insert x B) = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp
        (fun hn ↦ hon ((traceFiber_nonempty_iff P u (insert x B)).mp hn))
    simp [hemp]

private lemma traceSplit_sum_eq_coordinateTraceEdgeWeight
    (P : Finset (Finset α)) (u : Finset α) (x : α) (hx : x ∈ u) :
    (∑ B ∈ restrictionFamily P (u.erase x),
        min ((traceFiberOn P (u.erase x) B x).card : ℝ)
          ((traceFiberOff P (u.erase x) B x).card : ℝ)) =
      coordinateTraceEdgeWeight P u x := by
  classical
  let R₀ := restrictionFamily P (u.erase x)
  let R := restrictionFamily P u
  let S := R₀.filter fun B ↦ insert x B ∈ R ∧ B ∈ R
  let T := R.filter fun C ↦ x ∈ C ∧ C.erase x ∈ R
  calc
    (∑ B ∈ R₀,
        min ((traceFiberOn P (u.erase x) B x).card : ℝ)
          ((traceFiberOff P (u.erase x) B x).card : ℝ)) =
        ∑ B ∈ R₀, if insert x B ∈ R ∧ B ∈ R then
          min ((traceFiber P u (insert x B)).card : ℝ)
            ((traceFiber P u B).card : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      exact traceSplit_min_eq_edgeTerm P u B x hx hB
    _ = ∑ B ∈ S, min ((traceFiber P u (insert x B)).card : ℝ)
          ((traceFiber P u B).card : ℝ) := by
      simp only [S, Finset.sum_filter]
    _ = ∑ C ∈ T, min ((traceFiber P u C).card : ℝ)
          ((traceFiber P u (C.erase x)).card : ℝ) := by
      apply Finset.sum_nbij'
          (fun B ↦ insert x B) (fun C ↦ C.erase x)
      · intro B hBS
        simp only [S, Finset.mem_filter] at hBS
        obtain ⟨hBR₀, hon, hoff⟩ := hBS
        have hxB : x ∉ B := by
          have hsub := restrictionFamily_member_subset P (u.erase x) B hBR₀
          intro hxmem
          exact (Finset.mem_erase.mp (hsub hxmem)).1 rfl
        simp only [T, Finset.mem_filter]
        exact ⟨hon, Finset.mem_insert_self _ _, by simpa [Finset.erase_insert hxB]⟩
      · intro C hCT
        simp only [T, Finset.mem_filter] at hCT
        obtain ⟨hCR, hxC, herase⟩ := hCT
        have hR₀ : C.erase x ∈ R₀ := by
          dsimp only [R₀]
          rw [restrictionFamily_erase_image P u x]
          exact Finset.mem_image.mpr ⟨C, hCR, rfl⟩
        simp only [S, Finset.mem_filter]
        exact ⟨hR₀, by simpa [Finset.insert_erase hxC], herase⟩
      · intro B hBS
        simp only [S, Finset.mem_filter] at hBS
        have hxB : x ∉ B := by
          have hsub := restrictionFamily_member_subset P (u.erase x) B hBS.1
          intro hxmem
          exact (Finset.mem_erase.mp (hsub hxmem)).1 rfl
        exact Finset.erase_insert hxB
      · intro C hCT
        simp only [T, Finset.mem_filter] at hCT
        exact Finset.insert_erase hCT.2.1
      · intro B hBS
        simp only [S, Finset.mem_filter] at hBS
        have hxB : x ∉ B := by
          have hsub := restrictionFamily_member_subset P (u.erase x) B hBS.1
          intro hxmem
          exact (Finset.mem_erase.mp (hsub hxmem)).1 rfl
        simp [Finset.erase_insert hxB]
    _ = coordinateTraceEdgeWeight P u x := by
      dsimp only [T, R, coordinateTraceEdgeWeight]
      rw [Finset.sum_filter]

private lemma edgeMinWeightSum_restriction_eq_sum_coordinate
    (P : Finset (Finset α)) (u : Finset α) :
    edgeMinWeightSum (restrictionFamily P u) (restrictionMultiplicity P u) =
      ∑ x ∈ u, coordinateTraceEdgeWeight P u x := by
  classical
  unfold edgeMinWeightSum edgeMinWeightSumRaw coordinateTraceEdgeWeight
  calc
    (∑ C ∈ restrictionFamily P u, ∑ x ∈ C,
        if C.erase x ∈ restrictionFamily P u then
          min (extendSubtypeWeight (restrictionFamily P u)
              (restrictionMultiplicity P u) C)
            (extendSubtypeWeight (restrictionFamily P u)
              (restrictionMultiplicity P u) (C.erase x))
        else 0) =
      ∑ C ∈ restrictionFamily P u, ∑ x ∈ u,
        if x ∈ C ∧ C.erase x ∈ restrictionFamily P u then
          min ((traceFiber P u C).card : ℝ)
            ((traceFiber P u (C.erase x)).card : ℝ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro C hC
      have hCu : C ⊆ u := by
        simp only [restrictionFamily, Finset.mem_image] at hC
        obtain ⟨A, _hA, rfl⟩ := hC
        exact Finset.inter_subset_right
      calc
        (∑ x ∈ C,
            if C.erase x ∈ restrictionFamily P u then
              min (extendSubtypeWeight (restrictionFamily P u)
                  (restrictionMultiplicity P u) C)
                (extendSubtypeWeight (restrictionFamily P u)
                  (restrictionMultiplicity P u) (C.erase x))
            else 0) =
            ∑ x ∈ C,
              if x ∈ C ∧ C.erase x ∈ restrictionFamily P u then
                min ((traceFiber P u C).card : ℝ)
                  ((traceFiber P u (C.erase x)).card : ℝ)
              else 0 := by
          apply Finset.sum_congr rfl
          intro x hxC
          by_cases herase : C.erase x ∈ restrictionFamily P u
          · rw [if_pos herase, if_pos ⟨hxC, herase⟩]
            rw [extendSubtypeWeight, dif_pos hC,
              extendSubtypeWeight, dif_pos herase,
              restrictionMultiplicity_eq_traceFiber_card,
              restrictionMultiplicity_eq_traceFiber_card]
          · rw [if_neg herase, if_neg (fun h ↦ herase h.2)]
        _ = ∑ x ∈ u,
              if x ∈ C ∧ C.erase x ∈ restrictionFamily P u then
                min ((traceFiber P u C).card : ℝ)
                  ((traceFiber P u (C.erase x)).card : ℝ)
              else 0 := by
          apply Finset.sum_subset hCu
          intro x _hxu hxC
          rw [if_neg]
          exact fun h ↦ hxC h.1
    _ = ∑ x ∈ u, ∑ C ∈ restrictionFamily P u,
        if x ∈ C ∧ C.erase x ∈ restrictionFamily P u then
          min ((traceFiber P u C).card : ℝ)
            ((traceFiber P u (C.erase x)).card : ℝ)
        else 0 := Finset.sum_comm

private theorem randomDeletion_incidence_lower_bound
    (P : Finset (Finset α)) (s : Finset α) (m : ℕ) (δ : ℝ)
    (hsupp : ∀ A ∈ P, A ⊆ s)
    (hsep : ∀ A ∈ P, ∀ B ∈ P, A ≠ B →
      δ * s.card < finsetHammingDistance A B) :
    (δ * s.card / 2) *
          (∑ t ∈ s.powersetCard m,
            ((P.card - (restrictionFamily P t).card : ℕ) : ℝ)) ≤
        ∑ u ∈ s.powersetCard (m + 1),
          edgeMinWeightSum (restrictionFamily P u)
            (restrictionMultiplicity P u) := by
  calc
    (δ * s.card / 2) *
          (∑ t ∈ s.powersetCard m,
            ((P.card - (restrictionFamily P t).card : ℕ) : ℝ)) =
        ∑ t ∈ s.powersetCard m, (δ * s.card / 2) *
          ((P.card - (restrictionFamily P t).card : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ s.powersetCard m,
        ∑ B ∈ restrictionFamily P t,
          ∑ x ∈ s.filter (fun x ↦ x ∉ t),
            min ((traceFiberOn P t B x).card : ℝ)
              ((traceFiberOff P t B x).card : ℝ) := by
      apply Finset.sum_le_sum
      intro t _ht
      exact restrictionLoss_lower_splitSum P s t δ hsupp hsep
    _ = ∑ t ∈ s.powersetCard m,
        ∑ x ∈ s.filter (fun x ↦ x ∉ t),
          ∑ B ∈ restrictionFamily P t,
            min ((traceFiberOn P t B x).card : ℝ)
              ((traceFiberOff P t B x).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.sum_comm]
    _ = ∑ u ∈ s.powersetCard (m + 1), ∑ x ∈ u,
          ∑ B ∈ restrictionFamily P (u.erase x),
            min ((traceFiberOn P (u.erase x) B x).card : ℝ)
              ((traceFiberOff P (u.erase x) B x).card : ℝ) := by
      exact extensionDeletion_sum s m (fun t x ↦
        ∑ B ∈ restrictionFamily P t,
          min ((traceFiberOn P t B x).card : ℝ)
            ((traceFiberOff P t B x).card : ℝ))
    _ = ∑ u ∈ s.powersetCard (m + 1),
          edgeMinWeightSum (restrictionFamily P u)
            (restrictionMultiplicity P u) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [edgeMinWeightSum_restriction_eq_sum_coordinate]
      apply Finset.sum_congr rfl
      intro x hx
      exact traceSplit_sum_eq_coordinateTraceEdgeWeight P u x hx
private lemma restrictionMultiplicity_nonneg
    (P : Finset (Finset α)) (t : Finset α)
    (B : ↥(restrictionFamily P t)) :
    0 ≤ restrictionMultiplicity P t B := by
  simp only [restrictionMultiplicity]
  positivity

private theorem randomDeletion_incidence_upper
    (P : Finset (Finset α)) (s : Finset α) (V m : ℕ)
    (hVC : VCIndexLE (finsetSetFamily P) V) :
    (∑ u ∈ s.powersetCard (m + 1),
        edgeMinWeightSum (restrictionFamily P u)
          (restrictionMultiplicity P u)) ≤
      (s.powersetCard (m + 1)).card * (V - 1 : ℕ) * P.card := by
  calc
    (∑ u ∈ s.powersetCard (m + 1),
        edgeMinWeightSum (restrictionFamily P u)
          (restrictionMultiplicity P u)) ≤
        ∑ u ∈ s.powersetCard (m + 1),
          (V - 1 : ℕ) *
            ∑ B, restrictionMultiplicity P u B := by
      apply Finset.sum_le_sum
      intro u _hu
      exact weightedUnitDistance_le (restrictionFamily P u) V
        (vcIndexLE_restrictionFamily P u V hVC)
        (restrictionMultiplicity P u)
        (restrictionMultiplicity_nonneg P u)
    _ = (s.powersetCard (m + 1)).card * (V - 1 : ℕ) * P.card := by
      simp only [sum_restrictionMultiplicity]
      simp [mul_assoc, mul_comm]

end RestrictionMultiplicity

/-- Weighted random-subset deletion double count for the sharp packing bound.

For every sampling level `m`, pairwise `δ`-separation makes the average loss
of original packing multiplicity under restriction no larger than the
weighted unit-edge incidence on `(m+1)`-coordinate traces. Each such trace is
partitioned by the unique coordinate on which the endpoints differ, so no
extra deletion multiplicity appears. The weighted unit-distance estimate then
bounds that same middle quantity by `(V-1)|P|` per sampled trace. Thus the two
displayed inequalities compose
directly into the sharp packing recurrence, without an intermediate
unweighted/weighted conversion or an extraneous combinatorial factor. -/
theorem randomDeletion_incidence_lower
    (P : Finset (Finset α)) (s : Finset α) (V m : ℕ) (δ : ℝ)
    -- realizes the finite carrier of the packing.
    (hsupp : ∀ A ∈ P, A ⊆ s)
    -- finite representation of the book VC-index condition.
    (hVC : VCIndexLE (finsetSetFamily P) V)
    -- strict normalized Hamming packing convention.
    (hsep : ∀ A ∈ P, ∀ B ∈ P, A ≠ B →
      δ * s.card < finsetHammingDistance A B) :
    (δ * s.card / 2) *
          (∑ t ∈ s.powersetCard m,
            ((P.card - (restrictionFamily P t).card : ℕ) : ℝ)) ≤
        ∑ u ∈ s.powersetCard (m + 1),
          edgeMinWeightSum (restrictionFamily P u)
            (restrictionMultiplicity P u) ∧
      (∑ u ∈ s.powersetCard (m + 1),
          edgeMinWeightSum (restrictionFamily P u)
            (restrictionMultiplicity P u)) ≤
        (s.powersetCard (m + 1)).card * (V - 1 : ℕ) * P.card := by
  exact ⟨randomDeletion_incidence_lower_bound P s m δ hsupp hsep,
    randomDeletion_incidence_upper P s V m hVC⟩

section FinitePackingBound

local instance : DecidableEq α := Classical.decEq α

private lemma restrictionFamily_eq_finiteTrace
    (P : Finset (Finset α)) (t : Finset α) :
    restrictionFamily P t = finiteTrace (finsetSetFamily P) t := by
  ext B
  unfold restrictionFamily finiteTrace finsetSetFamily
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Finset.inter_subset_right, (A : Set α), ⟨A, hA, rfl⟩, ?_⟩
    intro x hx
    constructor
    · intro h
      exact (Finset.mem_inter.mp h).1
    · intro h
      exact Finset.mem_inter.mpr ⟨h, hx⟩
  · rintro ⟨hBt, Aset, ⟨A, hA, hAset⟩, hBA⟩
    refine ⟨A, hA, ?_⟩
    ext x
    constructor
    · intro hx
      have hxAset : x ∈ Aset := by simpa [hAset] using (Finset.mem_inter.mp hx).1
      exact (hBA x (Finset.mem_inter.mp hx).2).mpr hxAset
    · intro hx
      have hxB := (hBA x (hBt hx)).mp hx
      exact Finset.mem_inter.mpr ⟨by simpa [hAset] using hxB, hBt hx⟩

private lemma restrictionFamily_card_le_sauer
    (P : Finset (Finset α)) (t : Finset α) (V : ℕ)
    (hVC : VCIndexLE (finsetSetFamily P) V) :
    (restrictionFamily P t).card ≤
      ∑ j ∈ Finset.range V, t.card.choose j := by
  rw [restrictionFamily_eq_finiteTrace]
  exact sauer_shelah_finiteTrace_bound hVC t

private lemma restrictionFamily_self_card
    (P : Finset (Finset α)) (s : Finset α)
    (hsupp : ∀ A ∈ P, A ⊆ s) :
    (restrictionFamily P s).card = P.card := by
  unfold restrictionFamily
  apply Finset.card_image_of_injOn
  intro A hA B hB hEq
  simpa only [Finset.inter_eq_left.mpr (hsupp A hA),
    Finset.inter_eq_left.mpr (hsupp B hB)] using hEq

private lemma card_le_one_of_vcIndexLE_one
    (P : Finset (Finset α)) (hVC : VCIndexLE (finsetSetFamily P) 1) :
    P.card ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ P.card := by omega
  obtain ⟨A, hA, B, hB, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  have hsymm : ((A \ B) ∪ (B \ A)).Nonempty := by
    by_contra hempty
    have : (A \ B) ∪ (B \ A) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hne
    ext x
    by_contra hxor
    have hx : x ∈ (A \ B) ∪ (B \ A) := by
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    simp [this] at hx
  obtain ⟨x, hx⟩ := hsymm
  apply hVC {x} (by simp)
  intro q hq
  simp only [Finset.subset_singleton_iff] at hq
  rcases hq with rfl | rfl
  · rcases Finset.mem_union.mp hx with hxAB | hxBA
    · refine ⟨(B : Set α), ⟨B, hB, rfl⟩, ?_⟩
      intro y hy
      have hyx : y = x := Finset.mem_singleton.mp hy
      subst y
      simpa using (Finset.mem_sdiff.mp hxAB).2
    · refine ⟨(A : Set α), ⟨A, hA, rfl⟩, ?_⟩
      intro y hy
      have hyx : y = x := Finset.mem_singleton.mp hy
      subst y
      simpa using (Finset.mem_sdiff.mp hxBA).2
  · rcases Finset.mem_union.mp hx with hxAB | hxBA
    · refine ⟨(A : Set α), ⟨A, hA, rfl⟩, ?_⟩
      intro y hy
      have hyx : y = x := Finset.mem_singleton.mp hy
      subst y
      simpa using (Finset.mem_sdiff.mp hxAB).1
    · refine ⟨(B : Set α), ⟨B, hB, rfl⟩, ?_⟩
      intro y hy
      have hyx : y = x := Finset.mem_singleton.mp hy
      subst y
      simpa using (Finset.mem_sdiff.mp hxBA).1

private lemma choose_mono_up_to
    (m d j : ℕ) (hjd : j ≤ d) (hdm : 2 * d ≤ m) :
    m.choose j ≤ m.choose d := by
  induction d generalizing j with
  | zero =>
      have : j = 0 := by omega
      subst j
      exact le_rfl
  | succ k ih =>
      by_cases hj : j = k + 1
      · subst j
        exact le_rfl
      · have hjk : j ≤ k := by omega
        exact (ih j hjk (by omega)).trans
          (Nat.choose_le_succ_of_lt_half_left (by omega))

private lemma sauerSum_le_card_mul_choose
    (m d : ℕ) (hdm : 2 * d ≤ m) :
    ∑ j ∈ Finset.range (d + 1), m.choose j ≤ (d + 1) * m.choose d := by
  calc
    (∑ j ∈ Finset.range (d + 1), m.choose j) ≤
        ∑ _j ∈ Finset.range (d + 1), m.choose d := by
      apply Finset.sum_le_sum
      intro j hj
      exact choose_mono_up_to m d j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hdm
    _ = (d + 1) * m.choose d := by simp [Nat.mul_comm]

private lemma factorial_lower_exp (d : ℕ) (hd : 1 ≤ d) :
    ((d : ℝ) / Real.exp 1) ^ d ≤ (d.factorial : ℝ) := by
  have hstirling := Stirling.le_factorial_stirling d
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * d) := by
    rw [Real.one_le_sqrt]
    have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    nlinarith [show (1 : ℝ) ≤ d by exact_mod_cast hd]
  have hpow : 0 ≤ ((d : ℝ) / Real.exp 1) ^ d := by positivity
  nlinarith

private lemma choose_le_exp_ratio_pow
    (m d : ℕ) (hd : 1 ≤ d) :
    (m.choose d : ℝ) ≤ (Real.exp 1 * m / d) ^ d := by
  have hchoose := Nat.choose_le_pow_div (α := ℝ) d m
  have hfac := factorial_lower_exp d hd
  have hbase : 0 < (d : ℝ) / Real.exp 1 := div_pos (by positivity) (Real.exp_pos 1)
  have hfacpos : 0 < (d.factorial : ℝ) := by positivity
  have hdenpos : 0 < ((d : ℝ) / Real.exp 1) ^ d := pow_pos hbase d
  calc
    (m.choose d : ℝ) ≤ (m : ℝ) ^ d / (d.factorial : ℝ) := hchoose
    _ ≤ (m : ℝ) ^ d / (((d : ℝ) / Real.exp 1) ^ d) := by
      exact div_le_div_of_nonneg_left (by positivity) hdenpos hfac
    _ = (Real.exp 1 * m / d) ^ d := by
      have hdne : (d : ℝ) ≠ 0 := by positivity
      rw [div_pow, div_pow, mul_pow]
      field_simp [hdne, Real.exp_ne_zero]

private lemma sauerSum_real_le_exp_ratio_pow
    (m d : ℕ) (hd : 1 ≤ d) (hdm : 2 * d ≤ m) :
    ((∑ j ∈ Finset.range (d + 1), m.choose j : ℕ) : ℝ) ≤
      (d + 1 : ℕ) * (Real.exp 1 * m / d) ^ d := by
  have hsum := sauerSum_le_card_mul_choose m d hdm
  have hchoose := choose_le_exp_ratio_pow m d hd
  have hsumReal :
      ((∑ j ∈ Finset.range (d + 1), m.choose j : ℕ) : ℝ) ≤
        ((d + 1 : ℕ) : ℝ) * (m.choose d : ℝ) := by exact_mod_cast hsum
  exact hsumReal.trans (mul_le_mul_of_nonneg_left hchoose (by positivity))

private lemma restrictionLoss_sum_lower
    (P : Finset (Finset α)) (s : Finset α) (m E : ℕ)
    (htrace : ∀ t ∈ s.powersetCard m, (restrictionFamily P t).card ≤ E) :
    (s.card.choose m) * (P.card - E) ≤
      ∑ t ∈ s.powersetCard m,
        (P.card - (restrictionFamily P t).card) := by
  rw [← Finset.card_powersetCard]
  calc
    (s.powersetCard m).card * (P.card - E) =
        ∑ _t ∈ s.powersetCard m, (P.card - E) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.sub_le_sub_left (htrace t ht) P.card

set_option maxHeartbeats 800000 in
-- The weighted deletion recurrence contains several large nested Finset sums.
private lemma randomDeletion_card_le_two_sauer
    (P : Finset (Finset α)) (s : Finset α) (d m : ℕ) (δ : ℝ)
    (hsupp : ∀ A ∈ P, A ⊆ s)
    (hVC : VCIndexLE (finsetSetFamily P) (d + 1))
    (hδ : 0 < δ)
    (hsep : ∀ A ∈ P, ∀ B ∈ P, A ≠ B →
      δ * s.card < finsetHammingDistance A B)
    (hd : 1 ≤ d) (hmN : m < s.card)
    (hscale : 4 * d < δ * (m + 1 : ℕ)) :
    P.card ≤ 2 * (∑ j ∈ Finset.range (d + 1), m.choose j) := by
  let E := ∑ j ∈ Finset.range (d + 1), m.choose j
  by_contra hbound
  have hME : 2 * E < P.card := Nat.lt_of_not_ge hbound
  have hE : E ≤ P.card := by omega
  have htrace : ∀ t ∈ s.powersetCard m,
      (restrictionFamily P t).card ≤ E := by
    intro t ht
    have htcard : t.card = m := (Finset.mem_powersetCard.mp ht).2
    simpa only [E, htcard] using
      restrictionFamily_card_le_sauer P t (d + 1) hVC
  have hlossNat := restrictionLoss_sum_lower P s m E htrace
  have hloss : (s.card.choose m : ℝ) * ((P.card - E : ℕ) : ℝ) ≤
      ∑ t ∈ s.powersetCard m,
        ((P.card - (restrictionFamily P t).card : ℕ) : ℝ) := by
    exact_mod_cast hlossNat
  have hp3 := randomDeletion_incidence_lower P s (d + 1) m δ
    hsupp hVC hsep
  have hcombined := hp3.1.trans hp3.2
  have ha0 : 0 ≤ δ * (s.card : ℝ) / 2 := by positivity
  have hlower := mul_le_mul_of_nonneg_left hloss ha0
  have hmain : (δ * (s.card : ℝ) / 2) *
      ((s.card.choose m : ℝ) * ((P.card - E : ℕ) : ℝ)) ≤
      ((s.powersetCard (m + 1)).card : ℝ) * d * P.card := by
    calc
      _ ≤ (δ * s.card / 2) *
          (∑ t ∈ s.powersetCard m,
            ((P.card - (restrictionFamily P t).card : ℕ) : ℝ)) := hlower
      _ ≤ _ := by simpa using hcombined
  rw [Finset.card_powersetCard] at hmain
  have hchooseNat := Nat.choose_succ_right_eq s.card m
  have hchoose : (s.card.choose (m + 1) : ℝ) * (m + 1 : ℝ) =
      (s.card.choose m : ℝ) * (s.card - m : ℕ) := by
    exact_mod_cast hchooseNat
  have hchoosePos : 0 < (s.card.choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos hmN.le
  have hNpos : 0 < (s.card : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hmN)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hMpos : 0 < (P.card : ℝ) := by
    have : 0 < P.card := by omega
    exact_mod_cast this
  have hMEreal : (P.card : ℝ) > 2 * E := by exact_mod_cast hME
  have hsubcast : ((P.card - E : ℕ) : ℝ) = P.card - E := by
    rw [Nat.cast_sub hE]
  have hNm : ((s.card - m : ℕ) : ℝ) ≤ s.card := by
    exact_mod_cast Nat.sub_le _ _
  have hscale' : 4 * (d : ℝ) < δ * (m + 1 : ℝ) := by exact_mod_cast hscale
  have hmul := mul_le_mul_of_nonneg_right hmain (show 0 ≤ (m + 1 : ℝ) by positivity)
  rw [hsubcast] at hmul
  have hrec : (s.card.choose m : ℝ) *
        ((δ * (s.card : ℝ) / 2) * ((P.card : ℝ) - E) * (m + 1 : ℝ)) ≤
      (s.card.choose m : ℝ) *
        (((s.card - m : ℕ) : ℝ) * (d : ℝ) * (P.card : ℝ)) := by
    calc
      _ = (δ * (s.card : ℝ) / 2) *
          ((s.card.choose m : ℝ) * ((P.card : ℝ) - E)) * (m + 1 : ℝ) := by ring
      _ ≤ (s.card.choose (m + 1) : ℝ) * (d : ℝ) *
          (P.card : ℝ) * (m + 1 : ℝ) := hmul
      _ = _ := by
        calc
          _ = ((s.card.choose (m + 1) : ℝ) * (m + 1 : ℝ)) *
              ((d : ℝ) * (P.card : ℝ)) := by ring
          _ = ((s.card.choose m : ℝ) * ((s.card - m : ℕ) : ℝ)) *
              ((d : ℝ) * (P.card : ℝ)) := by rw [hchoose]
          _ = _ := by ring
  have hrec' := le_of_mul_le_mul_left hrec hchoosePos
  have hMEhalf : (P.card : ℝ) < 2 * ((P.card : ℝ) - E) := by nlinarith
  have hdNpos : 0 < (d : ℝ) * (s.card : ℝ) := mul_pos hdpos hNpos
  have hfirst : (d : ℝ) * (s.card : ℝ) * (P.card : ℝ) <
      2 * (d : ℝ) * (s.card : ℝ) * ((P.card : ℝ) - E) := by
    nlinarith [mul_lt_mul_of_pos_left hMEhalf hdNpos]
  have hMEpos : 0 < (P.card : ℝ) - E := by nlinarith
  have hsecond : 2 * (d : ℝ) * (s.card : ℝ) * ((P.card : ℝ) - E) <
      (δ * (m + 1 : ℝ) / 2) * (s.card : ℝ) * ((P.card : ℝ) - E) := by
    have hs : 2 * (d : ℝ) < δ * (m + 1 : ℝ) / 2 := by nlinarith
    exact mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right hs hNpos) hMEpos
  have hright : ((s.card - m : ℕ) : ℝ) * (d : ℝ) * (P.card : ℝ) ≤
      (s.card : ℝ) * (d : ℝ) * (P.card : ℝ) := by
    gcongr
  nlinarith [hfirst, hsecond, hright]

set_option maxHeartbeats 800000 in
-- The three carrier-size branches elaborate the sharp constant in one declaration.
private lemma finitePacking_intermediate
    (P : Finset (Finset α)) (s : Finset α) (d : ℕ) (δ : ℝ)
    (hsupp : ∀ A ∈ P, A ⊆ s)
    (hVC : VCIndexLE (finsetSetFamily P) (d + 1))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ A ∈ P, ∀ B ∈ P, A ≠ B →
      δ * s.card < finsetHammingDistance A B)
    (hd : 1 ≤ d) :
    (P.card : ℝ) ≤ 2 * (d + 1 : ℕ) *
      (4 * Real.exp 1 / δ) ^ d := by
  let m : ℕ := ⌊4 * (d : ℝ) / δ⌋₊
  have hx0 : 0 ≤ 4 * (d : ℝ) / δ := by positivity
  have hmle : (m : ℝ) ≤ 4 * (d : ℝ) / δ := by
    exact Nat.floor_le hx0
  have hfourle : (4 * d : ℕ) ≤ m := by
    apply Nat.le_floor
    push_cast
    apply (le_div_iff₀ hδ0).2
    have hdreal : 0 ≤ (d : ℝ) := by positivity
    nlinarith
  have hdm : 2 * d ≤ m := by omega
  have hscale : 4 * (d : ℝ) < δ * (m + 1 : ℕ) := by
    have hfloor := Nat.lt_floor_add_one (4 * (d : ℝ) / δ)
    have := (div_lt_iff₀ hδ0).mp hfloor
    simpa only [m, Nat.cast_add, Nat.cast_one, mul_comm] using this
  have hbase : Real.exp 1 * (m : ℝ) / d ≤ 4 * Real.exp 1 / δ := by
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
    calc
      Real.exp 1 * (m : ℝ) / d ≤
          Real.exp 1 * (4 * (d : ℝ) / δ) / d := by gcongr
      _ = 4 * Real.exp 1 / δ := by
        field_simp [ne_of_gt hdpos, ne_of_gt hδ0]
  by_cases hmN : m < s.card
  · have hcard := randomDeletion_card_le_two_sauer P s d m δ hsupp hVC hδ0 hsep hd hmN hscale
    have hsauer := sauerSum_real_le_exp_ratio_pow m d hd hdm
    calc
      (P.card : ℝ) ≤ 2 *
          ((∑ j ∈ Finset.range (d + 1), m.choose j : ℕ) : ℝ) := by
        exact_mod_cast hcard
      _ ≤ 2 * ((d + 1 : ℕ) * (Real.exp 1 * m / d) ^ d) := by
        gcongr
      _ ≤ 2 * (d + 1 : ℕ) * (4 * Real.exp 1 / δ) ^ d := by
        have hp := pow_le_pow_left₀ (by positivity) hbase d
        nlinarith
  · have hNm : s.card ≤ m := Nat.le_of_not_gt hmN
    have hself := restrictionFamily_self_card P s hsupp
    have hsauerNat := restrictionFamily_card_le_sauer P s (d + 1) hVC
    rw [hself] at hsauerNat
    by_cases hlarge : 2 * d ≤ s.card
    · have hsauer := sauerSum_real_le_exp_ratio_pow s.card d hd hlarge
      have hNmreal : (s.card : ℝ) ≤ m := by exact_mod_cast hNm
      have hbaseN : Real.exp 1 * (s.card : ℝ) / d ≤ 4 * Real.exp 1 / δ := by
        calc
          Real.exp 1 * (s.card : ℝ) / d ≤ Real.exp 1 * (m : ℝ) / d := by
            gcongr
          _ ≤ _ := hbase
      calc
        (P.card : ℝ) ≤
            ((∑ j ∈ Finset.range (d + 1), s.card.choose j : ℕ) : ℝ) := by
          exact_mod_cast hsauerNat
        _ ≤ (d + 1 : ℕ) * (Real.exp 1 * s.card / d) ^ d := hsauer
        _ ≤ 2 * (d + 1 : ℕ) * (4 * Real.exp 1 / δ) ^ d := by
          have hp := pow_le_pow_left₀ (by positivity) hbaseN d
          have hnon : 0 ≤ ((d + 1 : ℕ) : ℝ) := by positivity
          have hpow : 0 ≤ (4 * Real.exp 1 / δ) ^ d := by positivity
          nlinarith
    · have hNsmall : s.card ≤ 2 * d := by omega
      have hsub : restrictionFamily P s ⊆ s.powerset := by
        intro B hB
        exact Finset.mem_powerset.mpr (restrictionFamily_member_subset P s B hB)
      have hpowNat : P.card ≤ 2 ^ s.card := by
        rw [← hself]
        exact (Finset.card_le_card hsub).trans_eq (Finset.card_powerset s)
      have hpowN : (2 : ℝ) ^ s.card ≤ 4 ^ d := by
        calc
          (2 : ℝ) ^ s.card ≤ 2 ^ (2 * d) := by
            exact pow_le_pow_right₀ (by norm_num) hNsmall
          _ = 4 ^ d := by rw [pow_mul]; norm_num
      have hfourbase : (4 : ℝ) ≤ 4 * Real.exp 1 / δ := by
        rw [le_div_iff₀ hδ0]
        have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        nlinarith
      have hpowbase : (4 : ℝ) ^ d ≤ (4 * Real.exp 1 / δ) ^ d := by gcongr
      have hfactor : 1 ≤ 2 * ((d + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * (d + 1) by omega)
      calc
        (P.card : ℝ) ≤ (2 : ℝ) ^ s.card := by exact_mod_cast hpowNat
        _ ≤ 4 ^ d := hpowN
        _ ≤ (4 * Real.exp 1 / δ) ^ d := hpowbase
        _ ≤ 2 * (d + 1 : ℕ) * (4 * Real.exp 1 / δ) ^ d := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor
            (show 0 ≤ (4 * Real.exp 1 / δ) ^ d by positivity)

end FinitePackingBound

/-- Sharp finite Chazelle--Haussler packing bound in the book-index
convention. Pairwise separation is normalized Hamming distance on `s`.

The displayed constant and exponent are exact: no `2V`/`21V` exponent or
arbitrary exponential base is substituted. Truncated `V - 1` handles
`V = 0,1`; the VC premise forces the corresponding degenerate families. -/
theorem finite_chazelleHaussler_packing
    (𝒜 : Finset (Finset α)) (s : Finset α) (V : ℕ) (δ : ℝ)
    -- carrier for normalized Hamming distance.
    (hsupp : ∀ A ∈ 𝒜, A ⊆ s)
    -- finite representation of the book VC-index condition.
    (hVC : VCIndexLE (finsetSetFamily 𝒜) V)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) -- packing scale.
    -- strict normalized finite packing convention.
    (hsep : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B →
      δ * s.card < finsetHammingDistance A B) :
    (𝒜.card : ℝ) ≤
      (1 / (2 * Real.sqrt (Real.exp 1))) * V * (4 * Real.exp 1) ^ V *
        δ ^ (-(V - 1 : ℕ) : ℝ) := by
  by_cases hV0 : V = 0
  · subst V
    have hPempty : 𝒜 = ∅ := by
      by_contra hne
      obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      apply hVC ∅ (by simp)
      intro t ht
      have ht0 : t = ∅ := Finset.subset_empty.mp ht
      subst t
      exact ⟨(A : Set α), ⟨A, hA, rfl⟩, by simp⟩
    simp [hPempty]
  · by_cases hV1 : V = 1
    · subst V
      have hcard := card_le_one_of_vcIndexLE_one 𝒜 hVC
      have hsqrtOne : 1 ≤ Real.sqrt (Real.exp 1) := by
        rw [Real.one_le_sqrt]
        exact Real.one_le_exp (by norm_num)
      have hcoef : (1 : ℝ) ≤
          (1 / (2 * Real.sqrt (Real.exp 1))) * (4 * Real.exp 1) := by
        have hsqrtpos : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos 1)
        have hsqrtSq : Real.sqrt (Real.exp 1) ^ 2 = Real.exp 1 :=
          Real.sq_sqrt (Real.exp_pos 1).le
        field_simp [ne_of_gt hsqrtpos]
        nlinarith [hsqrtSq]
      norm_num only [Nat.cast_one, Nat.sub_self, Nat.cast_zero, neg_zero,
        Real.rpow_zero, pow_one, mul_one]
      exact (by exact_mod_cast hcard : (𝒜.card : ℝ) ≤ 1).trans hcoef
    · have hV2 : 2 ≤ V := by omega
      let d := V - 1
      have hd : 1 ≤ d := by omega
      have hV : d + 1 = V := by omega
      have hinter := finitePacking_intermediate 𝒜 s d δ hsupp
        (by simpa only [hV] using hVC) hδ0 hδ1 hsep hd
      have hsqrtpos : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos 1)
      have hepos : 0 < Real.exp 1 := Real.exp_pos 1
      have hδpos : 0 < δ := hδ0
      have hδrpow : δ ^ (-(d : ℕ) : ℝ) = (δ ^ d)⁻¹ := by
        rw [Real.rpow_neg hδ0.le, Real.rpow_natCast]
      rw [hδrpow]
      have hδne : δ ^ d ≠ 0 := pow_ne_zero _ (ne_of_gt hδ0)
      have hsqrtSq : Real.sqrt (Real.exp 1) ^ 2 = Real.exp 1 :=
        Real.sq_sqrt hepos.le
      have hsqrtOne : 1 ≤ Real.sqrt (Real.exp 1) := by
        rw [Real.one_le_sqrt]
        exact Real.one_le_exp (by norm_num)
      have hconstant :
          2 * ((d + 1 : ℕ) : ℝ) * (4 * Real.exp 1 / δ) ^ d ≤
            (1 / (2 * Real.sqrt (Real.exp 1))) * ((d + 1 : ℕ) : ℝ) *
              (4 * Real.exp 1) ^ (d + 1) * (δ ^ d)⁻¹ := by
        have hd1pos : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
        rw [div_pow, pow_succ]
        field_simp [hδne, ne_of_gt hsqrtpos]
        nlinarith [hsqrtSq]
      calc
        (𝒜.card : ℝ) ≤ 2 * (d + 1 : ℕ) * (4 * Real.exp 1 / δ) ^ d := hinter
        _ ≤ (1 / (2 * Real.sqrt (Real.exp 1))) * (d + 1 : ℕ) *
            (4 * Real.exp 1) ^ (d + 1) * (δ ^ d)⁻¹ := hconstant
        _ = (1 / (2 * Real.sqrt (Real.exp 1))) * V *
            (4 * Real.exp 1) ^ V * (δ ^ d)⁻¹ := by rw [hV]

/-- The weighted empirical `Lʳ` norm on a finite carrier.

This is the finite-discrete norm used in the layer-cake transfer to function
classes. Edge behavior: the empty carrier gives zero; `r = 0` uses Lean's
totalized reciprocal exponent, while book-facing results assume `1 ≤ r`.
Weights are not normalized or clipped by the definition. -/
noncomputable def empiricalLpNorm (s : Finset Ω) (w : Ω → ℝ)
    (f : Ω → ℝ) (r : ℝ) : ℝ := by
  classical
  exact (∑ x ∈ s, w x * |f x| ^ r) ^ r⁻¹

end

end AsymptoticStatistics.EmpiricalProcess
