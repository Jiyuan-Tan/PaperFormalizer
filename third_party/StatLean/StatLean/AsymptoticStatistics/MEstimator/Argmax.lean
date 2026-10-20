module
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterProcessMapping

@[expose] public section

/-!
# The argmax theorem

Shared closed-set core and the book-facing statement of van der Vaart Theorem
5.56. The theorem assumes the
near-maximizer, well-separated maximum, compact containment, and pair-process
outer weak convergence assumptions.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.MEstimator

/-- The shared closed-set argmax core used by Theorem 5.56 and Corollary 5.58.

The input `hcomparison` is the one-sided supremum-event inequality obtained
either from pair weak convergence (Theorem 5.56) or from the refined local
`ℓ∞(K)` changing-set comparison (Corollary 5.58).  The conclusion is constructed
here; argmax convergence is not present in any hypothesis or bundle.

Each `p ∈ 𝓛` carries a sample/numerator set `p.1` and a possibly different
limit-denominator set `p.2`.  Their geometric properties are supplied only by
the theorem-specific containment and comparison arguments. Theorem 5.56
uses diagonal pairs, while Corollary 5.58 uses a closed ball paired with its
interior. -/
theorem argmax_closed_limsup
    {Ω Ωlim D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
    [MeasurableSpace D] [MetricSpace D] [OpensMeasurableSpace D]
    {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)]
    {μlim : Measure Ωlim} [IsProbabilityMeasure μlim]
    (Mn : ℕ → Ω → D → ℝ) (M : Ωlim → D → ℝ)
    (Hn : ℕ → Set D) (H : Set D) (𝓛 : Set (Set D × Set D))
    (hhatn : ℕ → Ω → D) (hhat : Ωlim → D) (hhmeas : Measurable hhat)
    (hmemn : ∀ n ω, hhatn n ω ∈ Hn n)
    (hmem : ∀ᵐ ω ∂μlim, hhat ω ∈ H)
    (r : ℕ → Ω → ℝ)
    (hnear : ∀ n ω h, h ∈ Hn n →
      Mn n ω h ≤ Mn n ω (hhatn n ω) + r n ω)
    (hsep : ∀ (G : Set D), IsOpen G → ∀ p ∈ 𝓛,
      ∀ᵐ ω ∂μlim, hhat ω ∈ G →
        ForMathlib.setSupEReal (M ω) (Gᶜ ∩ p.1 ∩ H)
          < (M ω (hhat ω) : EReal))
    (hcontain : ∀ ε : ℝ, 0 < ε → ∃ p ∈ 𝓛,
      (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) < ENNReal.ofReal ε ∧
      μlim {ω | hhat ω ∉ p.2} < ENNReal.ofReal ε)
    (hcomparison : ∀ (F : Set D) (p : Set D × Set D), IsClosed F → p ∈ 𝓛 →
      limsup (fun n => (μ n).outerMeasureStar {ω |
          ForMathlib.setSupEReal (Mn n ω) (p.1 ∩ Hn n)
            ≤ (r n ω : EReal) +
              ForMathlib.setSupEReal (Mn n ω) (F ∩ p.1 ∩ Hn n)}) atTop
        ≤ μlim {ω |
          ForMathlib.setSupEReal (M ω) (p.2 ∩ H)
            ≤ ForMathlib.setSupEReal (M ω) (F ∩ p.1 ∩ H)}) :
    WeakConvergesOuter μ hhatn (μlim.map hhat) := by
  have hinside : ∀ (F : Set D) (p : Set D × Set D), ∀ n,
      (μ n).outerMeasureStar (hhatn n ⁻¹' (F ∩ p.1)) ≤
        (μ n).outerMeasureStar {ω |
          ForMathlib.setSupEReal (Mn n ω) (p.1 ∩ Hn n) ≤
            (r n ω : EReal) +
              ForMathlib.setSupEReal (Mn n ω) (F ∩ p.1 ∩ Hn n)} := by
    intro F p n
    refine outerMeasureStar_mono_processMapping (μ n) fun ω hω => ?_
    rcases hω with ⟨hωF, hωK⟩
    unfold ForMathlib.setSupEReal
    refine iSup_le (α := EReal) fun h : {h : D // h ∈ p.1 ∩ Hn n} => ?_
    have hhat_le : (Mn n ω (hhatn n ω) : EReal) ≤
        ⨆ q : {q : D // q ∈ F ∩ p.1 ∩ Hn n}, (Mn n ω q : EReal) :=
      le_iSup (fun q : {q : D // q ∈ F ∩ p.1 ∩ Hn n} =>
        (Mn n ω q : EReal))
        ⟨hhatn n ω, ⟨⟨hωF, hωK⟩, hmemn n ω⟩⟩
    calc
      (Mn n ω h : EReal) ≤ (Mn n ω (hhatn n ω) + r n ω : ℝ) :=
        EReal.coe_le_coe_iff.mpr (hnear n ω h h.2.2)
      _ = (r n ω : EReal) + (Mn n ω (hhatn n ω) : EReal) := by
        rw [EReal.coe_add]
        exact add_comm _ _
      _ ≤ (r n ω : EReal) +
          ⨆ q : {q : D // q ∈ F ∩ p.1 ∩ Hn n}, (Mn n ω q : EReal) :=
        add_le_add_right hhat_le _
  letI : IsProbabilityMeasure (μlim.map hhat) :=
    Measure.isProbabilityMeasure_map hhmeas.aemeasurable
  refine weakConvergesOuter_of_closedSet_limsup ?_
  intro F hF
  rw [Measure.map_apply hhmeas hF.measurableSet]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let δ : ℝ := (ε : ℝ) / 2
  have hδ : 0 < δ := by simp [δ, hε]
  obtain ⟨p, hp, hpSample, hpLimit⟩ := hcontain δ hδ
  have hsample :
      limsup (fun n => (μ n).outerMeasureStar (hhatn n ⁻¹' F)) atTop ≤
        limsup (fun n => (μ n).outerMeasureStar {ω |
          ForMathlib.setSupEReal (Mn n ω) (p.1 ∩ Hn n) ≤
            (r n ω : EReal) +
              ForMathlib.setSupEReal (Mn n ω) (F ∩ p.1 ∩ Hn n)}) atTop +
          (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) := by
    calc
      limsup (fun n => (μ n).outerMeasureStar (hhatn n ⁻¹' F)) atTop ≤
          limsup (fun n =>
            (μ n).outerMeasureStar (hhatn n ⁻¹' (F ∩ p.1)) +
              (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) atTop := by
        refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
        apply (outerMeasureStar_mono_processMapping (μ n) (B :=
          hhatn n ⁻¹' (F ∩ p.1) ∪ {ω | hhatn n ω ∉ p.1}) ?_).trans
        · exact outerMeasureStar_union_le_processMapping (μ n) _ _
        · intro ω hω
          by_cases hωK : hhatn n ω ∈ p.1
          · exact Or.inl ⟨hω, hωK⟩
          · exact Or.inr hωK
      _ ≤ limsup (fun n => (μ n).outerMeasureStar {ω |
            ForMathlib.setSupEReal (Mn n ω) (p.1 ∩ Hn n) ≤
              (r n ω : EReal) +
                ForMathlib.setSupEReal (Mn n ω) (F ∩ p.1 ∩ Hn n)} +
              (⨆ m, (μ m).outerMeasureStar {ω | hhatn m ω ∉ p.1})) atTop := by
        refine limsup_le_limsup (Eventually.of_forall fun n =>
          add_le_add (hinside F p n) ?_)
        exact le_iSup (fun m => (μ m).outerMeasureStar {ω | hhatn m ω ∉ p.1}) n
      _ = limsup (fun n => (μ n).outerMeasureStar {ω |
            ForMathlib.setSupEReal (Mn n ω) (p.1 ∩ Hn n) ≤
              (r n ω : EReal) +
                ForMathlib.setSupEReal (Mn n ω) (F ∩ p.1 ∩ Hn n)}) atTop +
            (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) := by
        apply limsup_add_const
        · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
        · exact isCobounded_le_of_bot
  have hlimitEvent :
      μlim {ω |
          ForMathlib.setSupEReal (M ω) (p.2 ∩ H) ≤
            ForMathlib.setSupEReal (M ω) (F ∩ p.1 ∩ H)} ≤
        μlim (hhat ⁻¹' F) + μlim {ω | hhat ω ∉ p.2} := by
    calc
      μlim {ω |
          ForMathlib.setSupEReal (M ω) (p.2 ∩ H) ≤
            ForMathlib.setSupEReal (M ω) (F ∩ p.1 ∩ H)} ≤
          μlim (hhat ⁻¹' F ∪ {ω | hhat ω ∉ p.2}) := by
        apply measure_mono_ae
        filter_upwards [hmem, hsep Fᶜ hF.isOpen_compl p hp] with ω hmemω hsepω hω
        by_cases hωF : hhat ω ∈ F
        · exact Or.inl hωF
        · by_cases hωL : hhat ω ∈ p.2
          · exfalso
            have hhat_le : (M ω (hhat ω) : EReal) ≤
                ForMathlib.setSupEReal (M ω) (p.2 ∩ H) := by
              unfold ForMathlib.setSupEReal
              exact le_iSup (fun q : {q : D // q ∈ p.2 ∩ H} => (M ω q : EReal))
                ⟨hhat ω, hωL, hmemω⟩
            have hstrict : ForMathlib.setSupEReal (M ω) (F ∩ p.1 ∩ H) <
                (M ω (hhat ω) : EReal) := by
              simpa only [compl_compl] using hsepω hωF
            exact (not_le_of_gt hstrict) (hhat_le.trans hω)
          · exact Or.inr hωL
      _ ≤ μlim (hhat ⁻¹' F) + μlim {ω | hhat ω ∉ p.2} := measure_union_le _ _
  have herr : μlim {ω | hhat ω ∉ p.2} +
      (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) ≤
        (ε : ℝ≥0∞) := by
    calc
      μlim {ω | hhat ω ∉ p.2} +
          (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) ≤
          ENNReal.ofReal δ + ENNReal.ofReal δ :=
        add_le_add hpLimit.le hpSample.le
      _ = (ε : ℝ≥0∞) := by
        simp [δ, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    limsup (fun n => (μ n).outerMeasureStar (hhatn n ⁻¹' F)) atTop ≤
        limsup (fun n => (μ n).outerMeasureStar {ω |
          ForMathlib.setSupEReal (Mn n ω) (p.1 ∩ Hn n) ≤
            (r n ω : EReal) +
              ForMathlib.setSupEReal (Mn n ω) (F ∩ p.1 ∩ Hn n)}) atTop +
          (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) := hsample
    _ ≤ μlim {ω |
          ForMathlib.setSupEReal (M ω) (p.2 ∩ H) ≤
            ForMathlib.setSupEReal (M ω) (F ∩ p.1 ∩ H)} +
          (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) :=
      add_le_add (hcomparison F p hF hp) le_rfl
    _ ≤ (μlim (hhat ⁻¹' F) + μlim {ω | hhat ω ∉ p.2}) +
          (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1}) :=
      add_le_add hlimitEvent le_rfl
    _ = μlim (hhat ⁻¹' F) +
          (μlim {ω | hhat ω ∉ p.2} +
            (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ p.1})) := add_assoc _ _ _
    _ ≤ μlim (hhat ⁻¹' F) + (ε : ℝ≥0∞) := add_le_add_right herr _

/-- **van der Vaart Theorem 5.56 (Argmax theorem).**

For stochastic processes indexed by changing sets, pair outer weak convergence
of the localized closed-set and full-set suprema, almost-sure well separation,
near-maximization up to `oP(1)`, and uniform compact containment imply outer weak
convergence of the argmax estimators.  Suprema are `EReal`-valued to retain the
book's empty/unbounded edge cases without subtraction. -/
theorem argmax_theorem
    {Ω Ωlim D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
    [MeasurableSpace D] [MetricSpace D] [OpensMeasurableSpace D]
    {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)]
    {μlim : Measure Ωlim} [IsProbabilityMeasure μlim]
    (Mn : ℕ → Ω → D → ℝ) (M : Ωlim → D → ℝ)
    (Hn : ℕ → Set D) (H : Set D) (𝒦 : Set (Set D))
    (hhatn : ℕ → Ω → D) (hhat : Ωlim → D)
    -- LEAN-ONLY: measurability of the limiting argmax.
    (hhmeas : Measurable hhat)
    -- USER-INPUT: the sample and limiting argmaxes lie in their index sets;
    -- vdV Theorem 5.56.
    (hmemn : ∀ n ω, hhatn n ω ∈ Hn n)
    (hmem : ∀ᵐ ω ∂μlim, hhat ω ∈ H)
    (r : ℕ → Ω → ℝ)
    -- LEAN-ONLY: the approximation remainder is represented as nonnegative.
    (hrnonneg : ∀ n ω, 0 ≤ r n ω)
    -- USER-INPUT: near-maximization with an `o_P(1)` remainder;
    -- vdV Theorem 5.56.
    (hr : TendstoInOuterProbabilityZero μ r)
    (hnear : ∀ n ω h, h ∈ Hn n →
      Mn n ω h ≤ Mn n ω (hhatn n ω) + r n ω)
    -- USER-INPUT: well separation and uniform compact containment;
    -- vdV Theorem 5.56.
    (hsep : ∀ (G : Set D), IsOpen G → ∀ K ∈ 𝒦,
      ∀ᵐ ω ∂μlim, hhat ω ∈ G →
        ForMathlib.setSupEReal (M ω) (Gᶜ ∩ K ∩ H)
          < (M ω (hhat ω) : EReal))
    (hcontain : ∀ ε : ℝ, 0 < ε → ∃ K ∈ 𝒦,
      (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ K}) < ENNReal.ofReal ε ∧
      μlim {ω | hhat ω ∉ K} < ENNReal.ofReal ε)
    -- LEAN-ONLY: measurability of the paired limiting suprema.
    (hpairMeas : PairSupLimitMeasurable M H 𝒦)
    -- USER-INPUT: joint outer weak convergence of localized process suprema;
    -- vdV Theorem 5.56.
    (hpair : PairSupConvergesOuter μ μlim Mn M Hn H 𝒦) :
    WeakConvergesOuter μ hhatn (μlim.map hhat) := by
  let 𝓛 : Set (Set D × Set D) := {p | p.1 = p.2 ∧ p.1 ∈ 𝒦}
  refine argmax_closed_limsup Mn M Hn H 𝓛 hhatn hhat hhmeas hmemn hmem
    r hnear ?_ ?_ ?_
  · intro G hG p hp
    exact hsep G hG p.1 hp.2
  · intro ε hε
    obtain ⟨K, hK, hsample, hlimit⟩ := hcontain ε hε
    exact ⟨(K, K), ⟨rfl, hK⟩, hsample, hlimit⟩
  · rintro F p hF ⟨hpEq, hpK⟩
    have hpEq' : p.2 = p.1 := hpEq.symm
    simpa only [hpEq'] using
      (outer_supComparison_limsup_of_pair_weakConvergence
        (fun n ω =>
          (ForMathlib.setSupEReal (Mn n ω) (F ∩ p.1 ∩ Hn n),
            ForMathlib.setSupEReal (Mn n ω) (p.1 ∩ Hn n)))
        (fun ω =>
          (ForMathlib.setSupEReal (M ω) (F ∩ p.1 ∩ H),
            ForMathlib.setSupEReal (M ω) (p.1 ∩ H)))
        (hpairMeas F p.1 hF hpK) (hpair F p.1 hF hpK)
        r hrnonneg hr)

end AsymptoticStatistics.MEstimator
