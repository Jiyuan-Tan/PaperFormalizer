module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringRademacher

@[expose] public section

namespace AsymptoticStatistics.EmpiricalProcess
open scoped ENNReal NNReal

noncomputable def empiricalDyadicLinkRadius {Ω : Type*}
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (q : ℕ) : ℝ :=
  (empiricalDyadicRadius F Φ n X (q + 1) +
      empiricalDyadicRadius F Φ n X q) *
    empiricalL2Seminorm n X Φ

namespace FiniteEmpiricalDyadicNets

noncomputable def projectedRademacherSup
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (q : ℕ) (ε : Fin n → Bool) : ℝ≥0∞ :=
  rademacherSup (Set.range (B.proj q)) n X ε

noncomputable def conditionalProjectedRademacherSup
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (q : ℕ) : ℝ≥0∞ :=
  conditionalRademacherSup (Set.range (B.proj q)) n X

theorem projectedRademacherSup_le_head_add_sum_links
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (ε : Fin n → Bool) :
    B.projectedRademacherSup L ε ≤
      rademacherSup (B.net 0 : Set (Ω → ℝ)) n X ε +
        ∑ q ∈ Finset.range L,
          rademacherSup
            (empiricalClosePairDifferences n X
              (B.net (q + 1)) (B.net q)
              (empiricalDyadicLinkRadius F Φ n X q) :
                Set (Ω → ℝ))
            n X ε := by
  classical
  unfold projectedRademacherSup rademacherSup supNormOver
  refine iSup_le fun g => iSup_le fun hg => ?_
  obtain ⟨f, rfl⟩ := hg
  change ENNReal.ofReal |rademacherAverage n X ε (B.proj L f)| ≤ _
  rw [B.rademacherAverage_proj_eq_head_add_sum_links ε f]
  have hsum :
      ENNReal.ofReal
          |∑ q ∈ Finset.range L,
            rademacherAverage n X ε (B.link q f)| ≤
        ∑ q ∈ Finset.range L,
          ENNReal.ofReal |rademacherAverage n X ε (B.link q f)| := by
    generalize Finset.range L = s
    induction s using Finset.induction with
    | empty => simp
    | @insert q s hq ih =>
        rw [Finset.sum_insert hq, Finset.sum_insert hq]
        calc
          ENNReal.ofReal
              |rademacherAverage n X ε (B.link q f) +
                ∑ k ∈ s, rademacherAverage n X ε (B.link k f)| ≤
              ENNReal.ofReal |rademacherAverage n X ε (B.link q f)| +
                ENNReal.ofReal
                  |∑ k ∈ s, rademacherAverage n X ε (B.link k f)| :=
            le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _))
              ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal |rademacherAverage n X ε (B.link q f)| +
                ∑ k ∈ s,
                  ENNReal.ofReal |rademacherAverage n X ε (B.link k f)| :=
            add_le_add le_rfl ih
  calc
    ENNReal.ofReal
        |rademacherAverage n X ε (B.head f) +
          ∑ q ∈ Finset.range L,
            rademacherAverage n X ε (B.link q f)| ≤
        ENNReal.ofReal |rademacherAverage n X ε (B.head f)| +
          ENNReal.ofReal
            |∑ q ∈ Finset.range L,
              rademacherAverage n X ε (B.link q f)| :=
      le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _))
        ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal |rademacherAverage n X ε (B.head f)| +
          ∑ q ∈ Finset.range L,
            ENNReal.ofReal |rademacherAverage n X ε (B.link q f)| :=
      add_le_add le_rfl hsum
    _ ≤ (⨆ g ∈ (B.net 0 : Set (Ω → ℝ)),
            ENNReal.ofReal |rademacherAverage n X ε g|) +
          ∑ q ∈ Finset.range L,
            ⨆ g ∈ (empiricalClosePairDifferences n X
                (B.net (q + 1)) (B.net q)
                (empiricalDyadicLinkRadius F Φ n X q) : Set (Ω → ℝ)),
              ENNReal.ofReal |rademacherAverage n X ε g| := by
      apply add_le_add
      · exact le_iSup₂ (f := fun g _ =>
          ENNReal.ofReal |rademacherAverage n X ε g|)
          (B.head f) (B.head_mem f)
      · apply Finset.sum_le_sum
        intro q hq
        exact le_iSup₂ (f := fun g _ =>
          ENNReal.ofReal |rademacherAverage n X ε g|)
          (B.link q f)
          (B.link_mem_closePairDifferences q (by simpa using hq) f)

theorem positive_radius_and_seminorm_of_nonempty
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (hF : F.Nonempty) :
    0 < empiricalRelativeRadiusReal F Φ n X ∧
      0 < empiricalL2Seminorm n X Φ := by
  obtain ⟨f, hf⟩ := hF
  let f' : F := ⟨f, hf⟩
  have hprod : 0 < empiricalRelativeRadiusReal F Φ n X *
      empiricalL2Seminorm n X Φ := by
    calc
      0 ≤ empiricalL2Dist n X f' (B.proj 0 f') :=
        empiricalL2Dist_nonneg n X f' (B.proj 0 f')
      _ < empiricalRelativeRadiusReal F Φ n X *
          empiricalL2Seminorm n X Φ := by
        simpa using B.proj_dist_lt 0 (Nat.zero_le L) f'
  have hRnonneg : 0 ≤ empiricalRelativeRadiusReal F Φ n X :=
    ENNReal.toReal_nonneg
  have hDnonneg : 0 ≤ empiricalL2Seminorm n X Φ :=
    empiricalL2Seminorm_nonneg n X Φ
  constructor <;> nlinarith

theorem conditionalProjectedRademacherSup_le_entropy_sum
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (hΦ : IsEnvelope F Φ) :
    B.conditionalProjectedRademacherSup L ≤
      2 * ENNReal.ofReal
          ((empiricalRelativeRadiusReal F Φ n X +
              empiricalDyadicRadius F Φ n X 0) *
            empiricalL2Seminorm n X Φ) *
        entropyWeight
          (uniformL2CoveringNumber F Φ
            (empiricalDyadicRadius F Φ n X 0)) +
      ∑ q ∈ Finset.range L,
        2 * ENNReal.ofReal
            (empiricalDyadicLinkRadius F Φ n X q) *
          entropyWeight
            (uniformL2CoveringNumber F Φ
                (empiricalDyadicRadius F Φ n X (q + 1)) *
              uniformL2CoveringNumber F Φ
                (empiricalDyadicRadius F Φ n X q)) := by
  classical
  rcases F.eq_empty_or_nonempty with hF | hF
  · have hrange : Set.range (B.proj L) = ∅ := by
      ext g
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨f, rfl⟩
      simpa [hF] using f.property
    simp [conditionalProjectedRademacherSup, hrange, hF,
      empiricalDyadicLinkRadius, empiricalDyadicRadius]
  · obtain ⟨hR, hD⟩ := B.positive_radius_and_seminorm_of_nonempty hF
    have hdyadic : ∀ q : ℕ, 0 < empiricalDyadicRadius F Φ n X q := by
      intro q
      exact mul_pos (by positivity) hR
    have hlink : ∀ q : ℕ, 0 < empiricalDyadicLinkRadius F Φ n X q := by
      intro q
      exact mul_pos (add_pos (hdyadic (q + 1)) (hdyadic q)) hD
    have hhead : conditionalRademacherSup (B.net 0 : Set (Ω → ℝ)) n X ≤
        2 * ENNReal.ofReal
            ((empiricalRelativeRadiusReal F Φ n X +
                empiricalDyadicRadius F Φ n X 0) *
              empiricalL2Seminorm n X Φ) *
          entropyWeight
            (uniformL2CoveringNumber F Φ
              (empiricalDyadicRadius F Φ n X 0)) := by
      apply conditionalRademacherSup_usedAmbientCover_le F Φ n X hΦ
        (B.net 0) (empiricalDyadicRadius F Φ n X 0)
        (hdyadic 0) hD.ne'
      · intro g hg
        obtain ⟨f, hfg⟩ := B.net_used 0 (Nat.zero_le L) g hg
        exact ⟨f, f.property, hfg⟩
      · exact B.card_le 0 (Nat.zero_le L)
    have hlinks : ∀ q ∈ Finset.range L,
        conditionalRademacherSup
            (empiricalClosePairDifferences n X
              (B.net (q + 1)) (B.net q)
              (empiricalDyadicLinkRadius F Φ n X q) : Set (Ω → ℝ)) n X ≤
          2 * ENNReal.ofReal (empiricalDyadicLinkRadius F Φ n X q) *
            entropyWeight
              (uniformL2CoveringNumber F Φ
                  (empiricalDyadicRadius F Φ n X (q + 1)) *
                uniformL2CoveringNumber F Φ
                  (empiricalDyadicRadius F Φ n X q)) := by
      intro q hq
      apply conditionalRademacherSup_closePairDifferences_le n X
        (B.net (q + 1)) (B.net q)
        (empiricalDyadicLinkRadius F Φ n X q) (hlink q)
      · exact B.card_le (q + 1) (by simpa using hq)
      · exact B.card_le q (Finset.mem_range.mp hq).le
    calc
      B.conditionalProjectedRademacherSup L =
          ∫⁻ ε, B.projectedRademacherSup L ε
            ∂ProbabilityTheory.rademacherCube n := rfl
      _ ≤ ∫⁻ ε,
          rademacherSup (B.net 0 : Set (Ω → ℝ)) n X ε +
            ∑ q ∈ Finset.range L,
              rademacherSup
                (empiricalClosePairDifferences n X
                  (B.net (q + 1)) (B.net q)
                  (empiricalDyadicLinkRadius F Φ n X q) : Set (Ω → ℝ))
                n X ε ∂ProbabilityTheory.rademacherCube n :=
        MeasureTheory.lintegral_mono fun ε =>
          B.projectedRademacherSup_le_head_add_sum_links ε
      _ = conditionalRademacherSup (B.net 0 : Set (Ω → ℝ)) n X +
          ∑ q ∈ Finset.range L,
            conditionalRademacherSup
              (empiricalClosePairDifferences n X
                (B.net (q + 1)) (B.net q)
                (empiricalDyadicLinkRadius F Φ n X q) : Set (Ω → ℝ))
              n X := by
        rw [MeasureTheory.lintegral_add_left
          (measurable_rademacherSup (B.net 0 : Set (Ω → ℝ)) n X)]
        rw [MeasureTheory.lintegral_finset_sum (Finset.range L)
          (fun q _ => measurable_rademacherSup
            (empiricalClosePairDifferences n X
              (B.net (q + 1)) (B.net q)
              (empiricalDyadicLinkRadius F Φ n X q) : Set (Ω → ℝ)) n X)]
        rfl
      _ ≤ _ := add_le_add hhead (Finset.sum_le_sum hlinks)

theorem conditionalProjectedRademacherSup_le_entropyIntegral
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (hΦ : IsEnvelope F Φ) :
    B.conditionalProjectedRademacherSup L ≤
      26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
        uniformCoveringEntropyIntegral
          (empiricalRelativeRadiusReal F Φ n X) F Φ := by
  classical
  rcases F.eq_empty_or_nonempty with hF | hF
  · have hrange : Set.range (B.proj L) = ∅ := by
      ext g
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨f, rfl⟩
      simpa [hF] using f.property
    simp [conditionalProjectedRademacherSup, hrange]
  · obtain ⟨hθ, hD⟩ := B.positive_radius_and_seminorm_of_nonempty hF
    let θ := empiricalRelativeRadiusReal F Φ n X
    let D := empiricalL2Seminorm n X Φ
    let a : ℕ → ℝ := fun q => (1 / 2 : ℝ) ^ q * θ
    let N : ℕ → ℕ∞ := fun q => uniformL2CoveringNumber F Φ (a q)
    let T : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal (a q) * entropyWeight (N q)
    let U : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal (a q) * entropyWeight (N (q + 1))
    let S : ℝ≥0∞ := ∑' q : ℕ, T q
    have ha : ∀ q, 0 ≤ a q := fun q => by
      simp only [a]
      positivity
    have ha_succ : ∀ q, a (q + 1) = (1 / 2 : ℝ) * a q := fun q => by
      simp only [a]
      ring
    have ha_split : ∀ q, ENNReal.ofReal (a q) =
        2 * ENNReal.ofReal (a (q + 1)) := by
      intro q
      rw [ha_succ, ← ENNReal.ofReal_ofNat (n := 2),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    have hU : (∑' q : ℕ, U q) ≤ 2 * S := by
      have hUeq : ∀ q, U q = 2 * T (q + 1) := by
        intro q
        simp only [U, T]
        rw [ha_split]
        ring
      simp_rw [hUeq]
      rw [ENNReal.tsum_mul_left]
      gcongr
      exact ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective T
    have hhead :
        2 * ENNReal.ofReal ((θ + a 0) * D) * entropyWeight (N 0) ≤
          4 * ENNReal.ofReal D * S := by
      have hT0 : T 0 ≤ S := by exact ENNReal.le_tsum 0
      calc
        2 * ENNReal.ofReal ((θ + a 0) * D) * entropyWeight (N 0) =
            4 * ENNReal.ofReal D * T 0 := by
          rw [ENNReal.ofReal_mul (add_nonneg hθ.le (ha 0)),
            ENNReal.ofReal_add hθ.le (ha 0)]
          simp [a, T, θ]
          ring
        _ ≤ 4 * ENNReal.ofReal D * S := by gcongr
    have hlink : ∀ q,
        2 * ENNReal.ofReal ((a (q + 1) + a q) * D) *
            entropyWeight (N (q + 1) * N q) ≤
          3 * ENNReal.ofReal D * (U q + T q) := by
      intro q
      calc
        2 * ENNReal.ofReal ((a (q + 1) + a q) * D) *
            entropyWeight (N (q + 1) * N q) ≤
          2 * ENNReal.ofReal ((a (q + 1) + a q) * D) *
            (entropyWeight (N (q + 1)) + entropyWeight (N q)) := by
          gcongr
          exact entropyWeight_mul_le _ _
        _ = 3 * ENNReal.ofReal D * (U q + T q) := by
          rw [ENNReal.ofReal_mul (add_nonneg (ha (q + 1)) (ha q)),
            ENNReal.ofReal_add (ha (q + 1)) (ha q)]
          simp only [U, T]
          rw [ha_split q]
          ring
    have hsum :
        ∑ q ∈ Finset.range L,
            2 * ENNReal.ofReal ((a (q + 1) + a q) * D) *
              entropyWeight (N (q + 1) * N q) ≤
          9 * ENNReal.ofReal D * S := by
      calc
        ∑ q ∈ Finset.range L,
            2 * ENNReal.ofReal ((a (q + 1) + a q) * D) *
              entropyWeight (N (q + 1) * N q) ≤
          ∑ q ∈ Finset.range L,
            3 * ENNReal.ofReal D * (U q + T q) :=
          Finset.sum_le_sum fun q _ => hlink q
        _ ≤ ∑' q : ℕ, 3 * ENNReal.ofReal D * (U q + T q) :=
          ENNReal.sum_le_tsum _
        _ = 3 * ENNReal.ofReal D * ((∑' q : ℕ, U q) + S) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        _ ≤ 3 * ENNReal.ofReal D * (2 * S + S) := by gcongr
        _ = 9 * ENNReal.ofReal D * S := by ring
    have hraw := B.conditionalProjectedRademacherSup_le_entropy_sum hΦ
    have hraw' : B.conditionalProjectedRademacherSup L ≤
        2 * ENNReal.ofReal ((θ + a 0) * D) * entropyWeight (N 0) +
          ∑ q ∈ Finset.range L,
            2 * ENNReal.ofReal ((a (q + 1) + a q) * D) *
              entropyWeight (N (q + 1) * N q) := by
      simpa [θ, D, a, N, empiricalDyadicRadius, empiricalDyadicLinkRadius]
        using hraw
    have hseries : B.conditionalProjectedRademacherSup L ≤
        13 * ENNReal.ofReal D * S := by
      calc
        B.conditionalProjectedRademacherSup L ≤ _ := hraw'
        _ ≤ 4 * ENNReal.ofReal D * S + 9 * ENNReal.ofReal D * S :=
          add_le_add hhead hsum
        _ = 13 * ENNReal.ofReal D * S := by ring
    calc
      B.conditionalProjectedRademacherSup L ≤
          13 * ENNReal.ofReal D * S := hseries
      _ ≤ 13 * ENNReal.ofReal D *
          (2 * uniformCoveringEntropyIntegral θ F Φ) := by
        gcongr
        exact uniformCovering_dyadic_sum_le_entropyIntegral F Φ hθ
      _ = 26 * ENNReal.ofReal D *
          uniformCoveringEntropyIntegral θ F Φ := by ring
      _ = _ := rfl

theorem conditionalProjectedRademacherSup_le_unitEntropyIntegral
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (hΦ : IsEnvelope F Φ) :
    B.conditionalProjectedRademacherSup L ≤
      26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
        uniformCoveringEntropyIntegral 1 F Φ := by
  refine B.conditionalProjectedRademacherSup_le_entropyIntegral hΦ |>.trans ?_
  gcongr
  apply uniformCoveringEntropyIntegral_mono_delta
  rw [← ENNReal.ofReal_le_one]
  rw [ofReal_empiricalRelativeRadiusReal_of_isEnvelope F Φ n X hΦ]
  exact empiricalRelativeRadius_le_one_of_isEnvelope F Φ n X hΦ

theorem rademacherSup_le_projected_add_terminal
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (ε : Fin n → Bool) :
    rademacherSup F n X ε ≤
      B.projectedRademacherSup L ε +
        ENNReal.ofReal
          (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
            empiricalL2Seminorm n X Φ) := by
  classical
  unfold rademacherSup supNormOver
  refine iSup_le fun f => iSup_le fun hf => ?_
  let f' : F := ⟨f, hf⟩
  let g := B.proj L f'
  have hsplit : rademacherAverage n X ε f =
      rademacherAverage n X ε g +
        rademacherAverage n X ε (f - g) := by
    rw [rademacherAverage_sub]
    ring
  have herr : |rademacherAverage n X ε (f - g)| ≤
      Real.sqrt n * empiricalDyadicRadius F Φ n X L *
        empiricalL2Seminorm n X Φ := by
    calc
      |rademacherAverage n X ε (f - g)| ≤
          Real.sqrt n * empiricalL2Seminorm n X (f - g) :=
        abs_rademacherAverage_le_sqrt_mul_empiricalL2Seminorm n X ε (f - g)
      _ = Real.sqrt n * empiricalL2Dist n X f g := rfl
      _ ≤ Real.sqrt n *
          (empiricalDyadicRadius F Φ n X L *
            empiricalL2Seminorm n X Φ) :=
        mul_le_mul_of_nonneg_left (B.proj_dist_lt L le_rfl f').le
          (Real.sqrt_nonneg n)
      _ = _ := by ring
  have hg : ENNReal.ofReal |rademacherAverage n X ε g| ≤
      B.projectedRademacherSup L ε := by
    unfold projectedRademacherSup rademacherSup supNormOver
    exact le_iSup₂ (f := fun h _ =>
      ENNReal.ofReal |rademacherAverage n X ε h|) g ⟨f', rfl⟩
  change ENNReal.ofReal |rademacherAverage n X ε f| ≤ _
  rw [hsplit]
  calc
    ENNReal.ofReal
        |rademacherAverage n X ε g +
          rademacherAverage n X ε (f - g)| ≤
        ENNReal.ofReal |rademacherAverage n X ε g| +
          ENNReal.ofReal |rademacherAverage n X ε (f - g)| :=
      le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _))
        ENNReal.ofReal_add_le
    _ ≤ B.projectedRademacherSup L ε +
          ENNReal.ofReal
            (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
              empiricalL2Seminorm n X Φ) :=
      add_le_add hg (ENNReal.ofReal_le_ofReal herr)

theorem conditionalRademacherSup_le_projected_add_terminal
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L) :
    conditionalRademacherSup F n X ≤
      B.conditionalProjectedRademacherSup L +
        ENNReal.ofReal
          (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
            empiricalL2Seminorm n X Φ) := by
  unfold conditionalRademacherSup conditionalProjectedRademacherSup
  calc
    (∫⁻ ε, rademacherSup F n X ε
        ∂ProbabilityTheory.rademacherCube n) ≤
        ∫⁻ ε, B.projectedRademacherSup L ε +
          ENNReal.ofReal
            (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
              empiricalL2Seminorm n X Φ)
          ∂ProbabilityTheory.rademacherCube n :=
      MeasureTheory.lintegral_mono fun ε =>
        B.rademacherSup_le_projected_add_terminal ε
    _ = (∫⁻ ε, B.projectedRademacherSup L ε
          ∂ProbabilityTheory.rademacherCube n) +
        ∫⁻ _ε, ENNReal.ofReal
          (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
            empiricalL2Seminorm n X Φ)
          ∂ProbabilityTheory.rademacherCube n := by
      rw [MeasureTheory.lintegral_add_left]
      exact measurable_rademacherSup (Set.range (B.proj L)) n X
    _ = (∫⁻ ε, rademacherSup (Set.range (B.proj L)) n X ε
          ∂ProbabilityTheory.rademacherCube n) +
        ENNReal.ofReal
          (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
            empiricalL2Seminorm n X Φ) := by
      simp [projectedRademacherSup]

theorem conditionalRademacherSup_le_entropyIntegral_add_terminal
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (hΦ : IsEnvelope F Φ) :
    conditionalRademacherSup F n X ≤
      26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
          uniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal F Φ n X) F Φ +
        ENNReal.ofReal
          (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
            empiricalL2Seminorm n X Φ) := by
  exact B.conditionalRademacherSup_le_projected_add_terminal.trans
    (add_le_add
      (B.conditionalProjectedRademacherSup_le_entropyIntegral hΦ) le_rfl)

end FiniteEmpiricalDyadicNets

theorem tendsto_ofReal_sqrt_mul_empiricalDyadicRadius_mul
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) :
    Filter.Tendsto
      (fun L : ℕ =>
        ENNReal.ofReal
          (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
            empiricalL2Seminorm n X Φ))
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun L : ℕ => (1 / 2 : ℝ) ^ L)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hreal : Filter.Tendsto
      (fun L : ℕ =>
        Real.sqrt n * ((1 / 2 : ℝ) ^ L *
          empiricalRelativeRadiusReal F Φ n X) *
          empiricalL2Seminorm n X Φ)
      Filter.atTop (nhds 0) := by
    simpa [mul_assoc] using
      ((hpow.const_mul (Real.sqrt n)).mul_const
        (empiricalRelativeRadiusReal F Φ n X)).mul_const
          (empiricalL2Seminorm n X Φ)
  simpa [empiricalDyadicRadius] using ENNReal.tendsto_ofReal hreal

theorem conditionalRademacherSup_le_uniformCoveringEntropyIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ) :
    conditionalRademacherSup F n X ≤
      26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
        uniformCoveringEntropyIntegral
          (empiricalRelativeRadiusReal F Φ n X) F Φ := by
  classical
  have hzero_of (hfzero : ∀ f ∈ F, empiricalL2Seminorm n X f = 0) :
      conditionalRademacherSup F n X = 0 := by
    have hsup : ∀ ε : Fin n → Bool, rademacherSup F n X ε = 0 := by
      intro ε
      apply le_antisymm
      · unfold rademacherSup supNormOver
        refine iSup_le fun f => iSup_le fun hf => ?_
        have havg :=
          abs_rademacherAverage_le_sqrt_mul_empiricalL2Seminorm n X ε f
        rw [hfzero f hf, mul_zero] at havg
        have habs : |rademacherAverage n X ε f| = 0 :=
          le_antisymm havg (abs_nonneg _)
        simp [habs]
      · exact bot_le
    unfold conditionalRademacherSup
    simp_rw [hsup]
    simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  by_cases hD : empiricalL2Seminorm n X Φ = 0
  · rw [hzero_of fun f hf => le_antisymm
        ((empiricalL2Seminorm_le_envelope F Φ n X hΦ f hf).trans hD.le)
        (empiricalL2Seminorm_nonneg n X f)]
    exact bot_le
  by_cases hθ : empiricalRelativeRadiusReal F Φ n X = 0
  · rw [hzero_of fun f hf => le_antisymm
        ((empiricalL2Seminorm_le_relativeRadiusReal_mul F Φ n X hΦ f hf).trans
          (by rw [hθ, zero_mul]))
        (empiricalL2Seminorm_nonneg n X f)]
    exact bot_le
  by_cases hJ : uniformCoveringEntropyIntegral
      (empiricalRelativeRadiusReal F Φ n X) F Φ = ⊤
  · have hDpos : 0 < empiricalL2Seminorm n X Φ :=
      lt_of_le_of_ne (empiricalL2Seminorm_nonneg n X Φ) (Ne.symm hD)
    have hcoeff :
        26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) ≠ 0 := by
      positivity
    rw [hJ, ENNReal.mul_top hcoeff]
    exact le_top
  · have hθpos : 0 < empiricalRelativeRadiusReal F Φ n X :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hθ)
    letI : NeZero n := ⟨hn⟩
    have hU : ∀ q : ℕ,
        uniformL2CoveringNumber F Φ
          (empiricalDyadicRadius F Φ n X q) ≠ ⊤ := by
      intro q
      simpa [empiricalDyadicRadius] using
        uniformL2CoveringNumber_dyadic_ne_top_of_entropyIntegral_ne_top
          F Φ hθpos hJ q
    let B : (L : ℕ) → FiniteEmpiricalDyadicNets F Φ n X L := fun L =>
      Classical.choice
        (finiteEmpiricalDyadicNets_nonempty X F Φ L hD
          (fun q _ => hU q))
    have hbound : ∀ L : ℕ,
        conditionalRademacherSup F n X ≤
          26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
              uniformCoveringEntropyIntegral
                (empiricalRelativeRadiusReal F Φ n X) F Φ +
            ENNReal.ofReal
              (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
                empiricalL2Seminorm n X Φ) := fun L =>
      (B L).conditionalRademacherSup_le_entropyIntegral_add_terminal hΦ
    have hlim : Filter.Tendsto
        (fun L : ℕ =>
          26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
              uniformCoveringEntropyIntegral
                (empiricalRelativeRadiusReal F Φ n X) F Φ +
            ENNReal.ofReal
              (Real.sqrt n * empiricalDyadicRadius F Φ n X L *
                empiricalL2Seminorm n X Φ))
        Filter.atTop
        (nhds (26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
          uniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal F Φ n X) F Φ)) := by
      simpa using tendsto_const_nhds.add
        (tendsto_ofReal_sqrt_mul_empiricalDyadicRadius_mul F Φ n X)
    apply ge_of_tendsto' hlim
    exact hbound

theorem conditionalRademacherSup_le_unitUniformCoveringEntropyIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ) :
    conditionalRademacherSup F n X ≤
      26 * ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
        uniformCoveringEntropyIntegral 1 F Φ := by
  refine (conditionalRademacherSup_le_uniformCoveringEntropyIntegral
    F Φ n X hΦ).trans ?_
  gcongr
  exact uniformCoveringEntropyIntegral_mono_delta F Φ
    (empiricalRelativeRadiusReal_le_one_of_isEnvelope F Φ n X hΦ)

end AsymptoticStatistics.EmpiricalProcess
