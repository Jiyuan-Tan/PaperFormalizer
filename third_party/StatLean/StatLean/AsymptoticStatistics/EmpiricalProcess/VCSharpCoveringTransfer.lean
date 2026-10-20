module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.VCSharpFiniteCovering
public import Mathlib.Topology.MetricSpace.CoveringNumbers

@[expose] public section

/-!
# Supporting transfers for sharp VC covers

This file proves the measure-theoretic and metric-space lemmas that transfer
finite VC packing bounds to strict covers.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

universe u

open UniformEntropyStructural

variable {Ω : Type u} [MeasurableSpace Ω]

/-- For an a.e.-measurable real function and a positive finite exponent, the
outer `Lʳ` norm agrees with Mathlib's `eLpNorm`. -/
theorem outerLpNorm_eq_eLpNorm_of_aemeasurable
    {Q : Measure Ω} {f : Ω → ℝ} {r : ℝ}
    (hr : 0 < r) (hf : AEMeasurable f Q) :
    outerLpNorm Q f r = eLpNorm f (ENNReal.ofReal r) Q := by
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hpow : AEMeasurable (fun x => ENNReal.ofReal |f x| ^ r) Q := by
    fun_prop
  have houter :
      outerExpectation Q (fun x => ENNReal.ofReal |f x| ^ r) =
        ∫⁻ x, ENNReal.ofReal |f x| ^ r ∂Q := by
    calc
      outerExpectation Q (fun x => ENNReal.ofReal |f x| ^ r) =
          outerExpectation Q (hpow.mk fun x => ENNReal.ofReal |f x| ^ r) :=
        outerExpectation_congr_ae hpow.ae_eq_mk
      _ = ∫⁻ x, hpow.mk (fun x => ENNReal.ofReal |f x| ^ r) x ∂Q :=
        outerExpectation_eq_lintegral hpow.measurable_mk
      _ = ∫⁻ x, ENNReal.ofReal |f x| ^ r ∂Q :=
        lintegral_congr_ae hpow.ae_eq_mk.symm
  rw [outerLpNorm, houter,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hr.le, one_div, Real.enorm_eq_ofReal_abs]

/-- A uniform bound on finite separated subsets produces a finite closed
cover at the same radius. -/
theorem finite_closedCover_of_finset_separated_card_le
    {X : Type*} [PseudoMetricSpace X] {A : Set X} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε)
    (hpack : ∀ S : Finset X, (↑S : Set X) ⊆ A →
      Metric.IsSeparated (ENNReal.ofReal ε) (↑S : Set X) → S.card ≤ N) :
    ∃ C : Finset X, C.card ≤ N ∧
      ∀ x ∈ A, ∃ c ∈ C, dist x c ≤ ε := by
  classical
  let epsNN : ℝ≥0 := ⟨ε, hε.le⟩
  have hepsNN : (epsNN : ℝ≥0∞) = ENNReal.ofReal ε := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  have hpacking : Metric.packingNumber epsNN A ≤ (N : ℕ∞) := by
    unfold Metric.packingNumber
    refine iSup_le fun S => iSup_le fun hSA => iSup_le fun hSsep => ?_
    rw [Set.encard_le_coe_iff_finite_ncard_le]
    have hSfinite : S.Finite := by
      by_contra hSfinite
      have hSinfinite : S.Infinite := by
        intro h
        exact hSfinite h
      obtain ⟨T, hTS, hTfinite, hTcard⟩ :=
        hSinfinite.exists_subset_ncard_eq (N + 1)
      have hTbound : hTfinite.toFinset.card ≤ N := by
        apply hpack hTfinite.toFinset
        · simpa only [hTfinite.coe_toFinset] using hTS.trans hSA
        · rw [← hepsNN]
          simpa only [hTfinite.coe_toFinset] using
            Metric.IsSeparated.subset hTS hSsep
      rw [← Set.ncard_eq_toFinset_card T hTfinite, hTcard] at hTbound
      exact (Nat.not_succ_le_self N) hTbound
    refine ⟨hSfinite, ?_⟩
    have hSbound : hSfinite.toFinset.card ≤ N := by
      apply hpack hSfinite.toFinset
      · simpa only [hSfinite.coe_toFinset] using hSA
      · rw [← hepsNN]
        simpa only [hSfinite.coe_toFinset] using hSsep
    simpa only [Set.ncard_eq_toFinset_card S hSfinite] using hSbound
  have hpacking_top : Metric.packingNumber epsNN A ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top N) hpacking
  let Cset : Set X := Metric.maximalSeparatedSet epsNN A
  have hCfinite : Cset.Finite := by
    apply Set.encard_ne_top_iff.mp
    rw [Metric.encard_maximalSeparatedSet hpacking_top]
    exact hpacking_top
  let C : Finset X := hCfinite.toFinset
  refine ⟨C, ?_, ?_⟩
  · have hCencard : Cset.encard ≤ (N : ℕ∞) := by
      rw [Metric.encard_maximalSeparatedSet hpacking_top]
      exact hpacking
    rw [Set.encard_le_coe_iff_finite_ncard_le] at hCencard
    simpa only [C, Set.ncard_eq_toFinset_card Cset hCfinite] using hCencard.2
  · intro x hxA
    obtain ⟨c, hcCset, hxc⟩ := Metric.isCover_maximalSeparatedSet hpacking_top hxA
    refine ⟨c, ?_, ?_⟩
    · simpa only [C, hCfinite.mem_toFinset] using hcCset
    · rw [← ENNReal.ofReal_le_ofReal_iff hε.le, ← hepsNN, ← edist_dist]
      exact hxc

/-- A uniform cardinality bound on finite `ε`-separated subsets produces a
finite strict cover at radius `2ε`.

Mathlib's separated-set API uses extended distances, so the hypothesis spells
the real radius as `ENNReal.ofReal ε`; the conclusion returns to `dist`. -/
theorem finite_strictCover_two_mul_of_finset_separated_card_le
    {X : Type*} [PseudoMetricSpace X] {A : Set X} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε)
    (hpack : ∀ S : Finset X, (↑S : Set X) ⊆ A →
      Metric.IsSeparated (ENNReal.ofReal ε) (↑S : Set X) → S.card ≤ N) :
    ∃ C : Finset X, C.card ≤ N ∧
      ∀ x ∈ A, ∃ c ∈ C, dist x c < 2 * ε := by
  obtain ⟨C, hCcard, hCcover⟩ :=
    finite_closedCover_of_finset_separated_card_le hε hpack
  refine ⟨C, hCcard, ?_⟩
  intro x hx
  obtain ⟨c, hc, hxc⟩ := hCcover x hx
  exact ⟨c, hc, by linarith⟩

/-- The sharp finite VC packing estimate transfers to a strict
cover at twice the relative radius, without changing the cardinal bound. -/
theorem exists_universalVCAdmissibleStrictTwoRadiusCoverConstant :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω)
        (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : ℕ)
        (Q : Measure Ω) (r ε : ℝ),
        @IsVCSubgraphClass Ω mΩ F V →
        @UniformEntropyStructural.IsEnvelope Ω F G →
        @UniformEntropyStructural.IsAdmissibleMeasure Ω mΩ G r Q →
        1 ≤ r → 0 < ε → ε < 1 →
        ∃ C : Finset (Ω → ℝ),
          @UniformEntropyStructural.IsStrictFiniteLpCover Ω mΩ
            F G Q r (2 * ε) C ∧
          (C.card : ℝ) ≤ K * V * (16 * Real.exp 1) ^ V *
            (1 / ε) ^ (r * (V - 1 : ℕ)) := by
  obtain ⟨K, hK, hKpack⟩ := exists_universalVCFiniteLpPackingConstant
  refine ⟨K, hK, ?_⟩
  intro Ω mΩ F G V Q r ε hVC hG hQ hr hε₀ hε₁
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure Q := hQ.1
  classical
  have hr₀ : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let p : ℝ≥0∞ := ENNReal.ofReal r
  have hp : 1 ≤ p := by
    simpa only [p, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr
  letI : Fact (1 ≤ p) := ⟨hp⟩
  have hfmem (f : Ω → ℝ) (hf : f ∈ F) : MemLp f p Q := by
    have hfm := hVC.1 f hf
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [← outerLpNorm_eq_eLpNorm_of_aemeasurable hr₀ hfm.aemeasurable]
    refine (show outerLpNorm Q f r ≤ outerLpNorm Q G r from ?_).trans_lt hQ.2.2
    unfold outerLpNorm
    apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hr₀.le)
    apply outerExpectation_mono
    intro x
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (by
        simpa only [abs_of_nonneg (hG.1 x)] using hG.2 f hf x)) hr₀.le
  let liftF : {f // f ∈ F} → Lp ℝ p Q :=
    fun f ↦ (hfmem f f.2).toLp f
  let A : Set (Lp ℝ p Q) := Set.range liftF
  let B : ℝ → ℝ := fun t ↦ K * V * (16 * Real.exp 1) ^ V *
    (1 / t) ^ (r * (V - 1 : ℕ))
  let N : ℕ := ⌊B ε⌋₊
  have hBε₀ : 0 ≤ B ε := by
    dsimp only [B]
    positivity
  have hBlt : B ε < (N + 1 : ℕ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (B ε)
  have hBcont : ContinuousAt B ε := by
    dsimp only [B]
    have hdiv : ContinuousAt (fun t : ℝ ↦ 1 / t) ε :=
      continuousAt_const.div continuousAt_id hε₀.ne'
    have hexp : 0 ≤ r * (V - 1 : ℕ) :=
      mul_nonneg hr₀.le (Nat.cast_nonneg _)
    exact continuousAt_const.mul (hdiv.rpow_const (Or.inr hexp))
  have hnear : ∀ᶠ t in 𝓝 ε, B t < (N + 1 : ℕ) :=
    hBcont.tendsto.eventually_lt_const hBlt
  obtain ⟨a, b, ha, hb⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  obtain ⟨η, hηlo, hηε⟩ := exists_between (show max 0 a < ε by
    exact max_lt hε₀ ha.1)
  have hη₀ : 0 < η := lt_of_le_of_lt (le_max_left 0 a) hηlo
  have hηa : a < η := lt_of_le_of_lt (le_max_right 0 a) hηlo
  have hBηlt : B η < (N + 1 : ℕ) := hb ⟨hηa, hηε.trans ha.2⟩
  have hη₁ : η < 1 := hηε.trans hε₁
  let scale : ℝ≥0∞ := ENNReal.ofReal (2 * η) * outerLpNorm Q G r
  have hscale₀ : 0 < scale := ENNReal.mul_pos
    (ENNReal.ofReal_pos.mpr (by positivity)).ne' hQ.2.1.ne'
  have hscale_top : scale ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQ.2.2.ne
  let d : ℝ := scale.toReal
  have hd₀ : 0 < d := ENNReal.toReal_pos hscale₀.ne' hscale_top
  have hdscale : ENNReal.ofReal d = scale := ENNReal.ofReal_toReal hscale_top
  have hpack : ∀ S : Finset (Lp ℝ p Q), (↑S : Set (Lp ℝ p Q)) ⊆ A →
      Metric.IsSeparated (ENNReal.ofReal d) (↑S : Set (Lp ℝ p Q)) → S.card ≤ N := by
    intro S hSA hSsep
    have hex (x : ↥S) : ∃ f : {f // f ∈ F}, liftF f = x := by
      simpa only [A, Set.mem_range] using hSA x.2
    choose rep hrep using hex
    let R : Finset (Ω → ℝ) := Finset.univ.image fun x : ↥S ↦ (rep x : Ω → ℝ)
    have hrep_inj : Function.Injective (fun x : ↥S ↦ (rep x : Ω → ℝ)) := by
      intro x y hxy
      apply Subtype.ext
      calc
        (x : Lp ℝ p Q) = liftF (rep x) := (hrep x).symm
        _ = liftF (rep y) := congrArg liftF (Subtype.ext hxy)
        _ = y := hrep y
    have hRcard : R.card = S.card := by
      simpa only [R, Finset.card_univ, Fintype.card_coe] using
        Finset.card_image_of_injective Finset.univ hrep_inj
    have hRbound : (R.card : ℝ) ≤ B η := by
      apply hKpack Ω mΩ F G V Q R r η hVC hG hQ.1 hQ.2.2
      · intro f hf
        simp only [R, Finset.mem_image, Finset.mem_univ, true_and] at hf
        obtain ⟨x, rfl⟩ := hf
        exact (rep x).2
      · exact hr
      · exact hη₀
      · exact hη₁
      · intro f hf g hg hfg
        simp only [R, Finset.mem_image, Finset.mem_univ, true_and] at hf hg
        obtain ⟨x, rfl⟩ := hf
        obtain ⟨y, rfl⟩ := hg
        have hxy : x ≠ y := fun h ↦ hfg (congrArg (fun z ↦ (rep z : Ω → ℝ)) h)
        have hxy' : (x : Lp ℝ p Q) ≠ y := fun h ↦ hxy (Subtype.ext h)
        have hsep := hSsep x.2 y.2 hxy'
        calc
          ENNReal.ofReal (2 * η) * outerLpNorm Q G r = ENNReal.ofReal d :=
            hdscale.symm
          _ < edist (x : Lp ℝ p Q) (y : Lp ℝ p Q) := hsep
          _ = edist (liftF (rep x)) (liftF (rep y)) := by rw [hrep x, hrep y]
          _ = eLpNorm ((rep x : Ω → ℝ) - (rep y : Ω → ℝ)) p Q :=
            Lp.edist_toLp_toLp _ _ (hfmem _ (rep x).2) (hfmem _ (rep y).2)
          _ = outerLpNorm Q ((rep x : Ω → ℝ) - (rep y : Ω → ℝ)) r :=
            (outerLpNorm_eq_eLpNorm_of_aemeasurable hr₀
              ((hVC.1 _ (rep x).2).sub (hVC.1 _ (rep y).2)).aemeasurable).symm
    have hRlt : R.card < N + 1 := by
      exact_mod_cast lt_of_le_of_lt hRbound hBηlt
    simpa only [hRcard, Nat.lt_add_one_iff] using hRlt
  obtain ⟨C, hCcard, hCcover⟩ :=
    finite_closedCover_of_finset_separated_card_le hd₀ hpack
  let D : Finset (Ω → ℝ) := C.image fun c : Lp ℝ p Q ↦ (c : Ω → ℝ)
  refine ⟨D, ?_, ?_⟩
  · constructor
    · intro g hg
      simp only [D, Finset.mem_image] at hg
      obtain ⟨c, _, rfl⟩ := hg
      exact Lp.memLp c
    · intro f hf
      obtain ⟨c, hc, hfc⟩ := hCcover (liftF ⟨f, hf⟩) ⟨⟨f, hf⟩, rfl⟩
      refine ⟨(c : Ω → ℝ), Finset.mem_image.mpr ⟨c, hc, rfl⟩, ?_⟩
      have hedist : edist (liftF ⟨f, hf⟩) c ≤ scale := by
        rw [Lp.edist_dist, ← hdscale]
        exact ENNReal.ofReal_le_ofReal hfc
      have hout : outerLpNorm Q (f - (c : Ω → ℝ)) r =
          edist (liftF ⟨f, hf⟩) c := by
        have hsubm : AEMeasurable (f - (c : Ω → ℝ)) Q :=
          (hVC.1 f hf).aemeasurable.sub (Lp.aestronglyMeasurable c).aemeasurable
        rw [outerLpNorm_eq_eLpNorm_of_aemeasurable hr₀ hsubm, Lp.edist_def]
        apply eLpNorm_congr_ae
        exact ((hfmem f hf).coeFn_toLp.sub EventuallyEq.rfl).symm
      rw [hout]
      refine hedist.trans_lt ?_
      exact ENNReal.mul_lt_mul_left hQ.2.1.ne' hQ.2.2.ne
        ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * ε)).2 (by linarith))
  · calc
      (D.card : ℝ) ≤ C.card := by
        have hDC : D.card ≤ C.card := by
          dsimp only [D]
          exact Finset.card_image_le
        exact_mod_cast hDC
      _ ≤ N := by exact_mod_cast hCcard
      _ ≤ B ε := Nat.floor_le hBε₀
      _ = K * V * (16 * Real.exp 1) ^ V *
          (1 / ε) ^ (r * (V - 1 : ℕ)) := rfl

end AsymptoticStatistics.EmpiricalProcess
