module
public import StatLean.StatisticalLearning.Core.SampleLaw

@[expose] public section

/-!
# Finite classes are PAC learnable in the realizable case

SSBD Ch. 2: under realizability, a hypothesis with true error `> ε` survives
with zero empirical error only with probability `≤ (1−ε)ⁿ ≤ e^{−εn}`
(SSBD Eqs. (2.8)–(2.9)); a union bound over the bad hypotheses gives
`P(∃ ERM h_S with L_{D,f}(h_S) > ε) ≤ |𝓗| e^{−εn}` (SSBD Cor. 2.3, no factor
2, no ceiling), hence PAC learnability with `m(ε,δ) ≤ ⌈log(|𝓗|/δ)/ε⌉`
(SSBD Cor. 3.2, ceiling explicit).

**Reference.** SSBD §2.3, Corollary 2.3; §3.1, Corollary 3.2. Transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.** `{s | ∀ i, h (s i) = f (s i)}` is a product cylinder,
so its `sampleLaw` mass is `(D.real {x | h x = f x})^n` exactly (`Measure.pi`
on a product set); `1 − ε ≤ e^{−ε}` finishes Eq. (2.9). The realizability
witness `h⋆` has `L_S(h⋆) = 0` a.s. (SSBD footnote 3, p. 17), which is why
every ERM hypothesis has zero empirical risk a.s. — the a.s. qualifier the
book elides is carried explicitly through the event algebra here.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {X : Type*} [MeasurableSpace X] {D : Measure X}
  [IsProbabilityMeasure D] {n : ℕ} {f : X → Bool}

/-- **Survival probability of a bad hypothesis** (SSBD Eqs. (2.8)–(2.9)): if
`L_{D,f}(h) > ε` then `h` is consistent with the labeled sample with
probability at most `(1−ε)ⁿ ≤ e^{−εn}`. -/
theorem measure_consistent_le_of_errProb_gt {h : X → Bool} {ε : ℝ}
    -- USER-INPUT: measurable disagreement set; SSBD Remark 3.1
    (hmeas : MeasurableSet {x | h x ≠ f x})
    -- USER-INPUT: `h` is `ε`-bad; SSBD p. 18 (`h ∈ 𝓗_B`)
    (hbad : ε < errProb D f h)
    -- USER-INPUT: `ε > 0`; SSBD Cor. 2.3
    (hε : 0 < ε) :
    sampleLaw D n {s | ∀ i, h (s i) = f (s i)} ≤
      ENNReal.ofReal (Real.exp (-ε * n)) := by
  -- the consistency event is the product cylinder over the agreement set
  have hagree : {x | h x = f x} = {x | h x ≠ f x}ᶜ := by ext x; simp
  have hareal : D.real {x | h x = f x} = 1 - errProb D f h := by
    rw [hagree]; exact probReal_compl_eq_one_sub hmeas
  have hpi : {s : Sample X n | ∀ i, h (s i) = f (s i)}
      = Set.univ.pi (fun _ : Fin n => {x | h x = f x}) := by
    ext s; simp [Set.mem_pi]
  have hDA : D {x | h x = f x} = ENNReal.ofReal (1 - errProb D f h) := by
    rw [← hareal, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- the real-valued estimate `(1 − L_{D,f}(h))ⁿ ≤ (1 − ε)ⁿ ≤ e^{−εn}` (SSBD Eq. (2.9))
  have h0 : (0 : ℝ) ≤ 1 - errProb D f h := by rw [← hareal]; exact measureReal_nonneg
  have h1 : 1 - errProb D f h ≤ Real.exp (-ε) := by
    have := Real.add_one_le_exp (-ε)
    linarith
  have hreal : (1 - errProb D f h) ^ n ≤ Real.exp (-ε * n) := by
    calc (1 - errProb D f h) ^ n ≤ (Real.exp (-ε)) ^ n := by gcongr
      _ = Real.exp (-ε * n) := by rw [← Real.exp_nat_mul]; ring_nf
  rw [hpi, sampleLaw, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hDA]
  rw [← ENNReal.ofReal_pow h0]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **SSBD Corollary 2.3** (finite classes generalize, realizable case): for
`m ≥ log(|𝓗|/δ)/ε`, with probability `≥ 1 − δ` every consistent hypothesis —
in particular every ERM hypothesis, since realizability makes some `h⋆ ∈ 𝓗`
consistent a.s. — has true error `≤ ε`. Stated as the book does via the bad
event: `P(∃ h ∈ 𝓗 consistent with L_{D,f}(h) > ε) ≤ |𝓗| e^{−εm} ≤ δ`. -/
theorem finiteClass_realizable_uniform (𝓗 : Finset (X → Bool)) {ε δ : ℝ}
    -- USER-INPUT: measurable disagreement sets; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, MeasurableSet {x | h x ≠ f x})
    -- USER-INPUT: `ε > 0`; SSBD Cor. 2.3
    (hε : 0 < ε)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD Cor. 2.3
    (hδ : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: sample size `m ≥ log(|𝓗|/δ)/ε` (no ceiling — the book's
    -- "any integer satisfying"); SSBD Cor. 2.3
    (hn : Real.log (𝓗.card / δ) / ε ≤ n) :
    sampleLaw D n
        {s | ∃ h ∈ 𝓗, (∀ i, h (s i) = f (s i)) ∧ ε < errProb D f h} ≤
      ENNReal.ofReal δ := by
  classical
  rcases Finset.eq_empty_or_nonempty 𝓗 with rfl | h𝓗
  · simp
  -- the bad event is the union over the `ε`-bad hypotheses of their consistency events
  have hset : {s : Sample X n | ∃ h ∈ 𝓗, (∀ i, h (s i) = f (s i)) ∧ ε < errProb D f h}
      = ⋃ h ∈ 𝓗.filter (fun h => ε < errProb D f h),
          {s : Sample X n | ∀ i, h (s i) = f (s i)} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨h, hh, hc, hb⟩; exact ⟨h, ⟨hh, hb⟩, hc⟩
    · rintro ⟨h, ⟨hh, hb⟩, hc⟩; exact ⟨h, hh, hc, hb⟩
  have hN1 : (1 : ℝ) ≤ (𝓗.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h𝓗
  have hNpos : (0 : ℝ) < (𝓗.card : ℝ) := by linarith
  -- the book's arithmetic: `|𝓗| e^{−εm} ≤ δ`
  have hlog_le : Real.log ((𝓗.card : ℝ) / δ) ≤ ε * n := by
    rw [div_le_iff₀ hε] at hn; linarith
  have hexp : Real.exp (-ε * n) ≤ ((𝓗.card : ℝ) / δ)⁻¹ := by
    rw [← Real.exp_log (show (0:ℝ) < (𝓗.card : ℝ) / δ by positivity), ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbound : (𝓗.card : ℝ) * Real.exp (-ε * n) ≤ δ := by
    calc (𝓗.card : ℝ) * Real.exp (-ε * n)
        ≤ (𝓗.card : ℝ) * ((𝓗.card : ℝ) / δ)⁻¹ :=
          mul_le_mul_of_nonneg_left hexp hNpos.le
      _ = δ := by field_simp
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun h hh =>
    measure_consistent_le_of_errProb_gt (hmeas h (Finset.mem_filter.mp hh).1)
      (Finset.mem_filter.mp hh).2 hε)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((𝓗.filter (fun h => ε < errProb D f h)).card : ℝ≥0∞) ≤ (𝓗.card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_filter_le _ _
  calc ((𝓗.filter (fun h => ε < errProb D f h)).card : ℝ≥0∞)
        * ENNReal.ofReal (Real.exp (-ε * n))
      ≤ (𝓗.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-ε * n)) := by gcongr
    _ = ENNReal.ofReal ((𝓗.card : ℝ) * Real.exp (-ε * n)) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hbound

/-- **SSBD Corollary 3.2** (finite classes are PAC learnable): any ERM selector
PAC-learns a finite class with sample complexity `⌈log(|𝓗|/δ)/ε⌉` (ceiling
explicit, as in the book's restatement of Cor. 2.3). -/
theorem finiteClass_isPACLearnerWith (𝓗 : Finset (X → Bool))
    {A : ∀ m : ℕ, Sample (X × Bool) m → (X → Bool)}
    -- USER-INPUT: nonempty class; SSBD §2.3 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: measurable disagreement sets against every target;
    -- SSBD Remark 3.1 (0–1-loss instantiation)
    (hmeas : ∀ (g : X → Bool), ∀ h ∈ 𝓗, MeasurableSet {x | h x ≠ g x})
    -- USER-INPUT: `A` is an ERM selector for the 0–1 loss; SSBD §2.3
    (hA : ∀ (m : ℕ) (s : Sample (X × Bool) m),
      IsERM (↑𝓗 : Set (X → Bool)) zeroOneLoss s (A m s)) :
    IsPACLearnerWith (↑𝓗 : Set (X → Bool)) A
      (fun ε δ => ⌈Real.log (𝓗.card / δ) / ε⌉₊) := by
  classical
  intro D hD f hreal ε δ hε hδ hδ1 n hn
  haveI := hD
  have hN1 : (1 : ℝ) ≤ (𝓗.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h𝓗
  have hlogpos : 0 < Real.log ((𝓗.card : ℝ) / δ) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hδ]; nlinarith
  have hquot : 0 < Real.log ((𝓗.card : ℝ) / δ) / ε := by positivity
  -- the ceiling is at least one, so the sample is nonempty
  have hn1 : 1 ≤ n := le_trans (Nat.ceil_pos.mpr hquot) hn
  have hnR : Real.log ((𝓗.card : ℝ) / δ) / ε ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  -- the realizability witness `g₀` and its full-measure consistency event
  obtain ⟨g₀, hg₀H, hg₀0⟩ := hreal
  have hg₀H' : g₀ ∈ 𝓗 := Finset.mem_coe.mp hg₀H
  have hGnull : sampleLaw D n {s : Sample X n | ∀ i, g₀ (s i) = f (s i)}ᶜ = 0 := by
    have hsub : {s : Sample X n | ∀ i, g₀ (s i) = f (s i)}ᶜ ⊆
        ⋃ i : Fin n, (fun s : Sample X n => s i) ⁻¹' {x | g₀ x ≠ f x} := by
      intro s hsc
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hsc
      obtain ⟨i, hi⟩ := hsc
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    rw [(measurePreserving_eval_sampleLaw (D := D) (n := n) i).measure_preimage
      (hmeas f g₀ hg₀H').nullMeasurableSet]
    exact hg₀0
  -- the bad event of SSBD Cor. 2.3
  have hBadle : sampleLaw D n
      {s : Sample X n | ∃ h ∈ 𝓗, (∀ i, h (s i) = f (s i)) ∧ ε < errProb D f h}
      ≤ ENNReal.ofReal δ :=
    finiteClass_realizable_uniform 𝓗 (fun h hh => hmeas f h hh) hε hδ hδ1 hnR
  -- off the bad event and on the witness's consistency event, the ERM output is `ε`-good
  have hincl : {s : Sample X n | errProb D f (A n (labeledBy f s)) ≤ ε}ᶜ ⊆
      {s : Sample X n | ∀ i, g₀ (s i) = f (s i)}ᶜ ∪
        {s : Sample X n | ∃ h ∈ 𝓗, (∀ i, h (s i) = f (s i)) ∧ ε < errProb D f h} := by
    intro s hsT
    by_contra hcon
    have hcons₀ : ∀ i, g₀ (s i) = f (s i) := by
      by_contra hne
      exact hcon (Set.mem_union_left _ hne)
    have hsB : s ∉ {s : Sample X n |
        ∃ h ∈ 𝓗, (∀ i, h (s i) = f (s i)) ∧ ε < errProb D f h} :=
      fun hb => hcon (Set.mem_union_right _ hb)
    set g : X → Bool := A n (labeledBy f s) with hgdef
    have hERM := hA n (labeledBy f s)
    -- the witness has zero empirical risk on a consistent sample (SSBD footnote 3, p. 17)
    have hstar0 : empRisk zeroOneLoss (labeledBy f s) g₀ = 0 := by
      have hz : ∀ i : Fin n, zeroOneLoss g₀ (labeledBy f s i) = 0 := by
        intro i; simp [zeroOneLoss, labeledBy, hcons₀ i]
      simp [empRisk, hz]
    have hnn : ∀ (u : X → Bool) (i : Fin n), (0 : ℝ) ≤ zeroOneLoss u (labeledBy f s i) := by
      intro u i; simp only [zeroOneLoss]; split <;> norm_num
    have hle0 : empRisk zeroOneLoss (labeledBy f s) g ≤ 0 := by
      have h := hERM.2 g₀ hg₀H
      rw [hstar0] at h; exact h
    have hge0 : (0 : ℝ) ≤ empRisk zeroOneLoss (labeledBy f s) g := by
      rw [empRisk]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hnn g i)
    -- a zero average of `{0,1}`-terms forces every term to vanish: `g` is consistent
    have hsum0 : ∑ i, zeroOneLoss g (labeledBy f s i) = 0 := by
      have heq : (n : ℝ)⁻¹ * ∑ i, zeroOneLoss g (labeledBy f s i) = 0 := by
        rw [← empRisk]; linarith
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hninv : (n : ℝ)⁻¹ ≠ 0 := ne_of_gt (inv_pos.mpr hnpos)
      exact (mul_eq_zero.mp heq).resolve_left hninv
    have hcons : ∀ i, g (s i) = f (s i) := by
      intro i
      have hzi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => hnn g i)).mp hsum0 i (Finset.mem_univ i)
      by_contra hne
      simp [zeroOneLoss, labeledBy, hne] at hzi
    have hgH : g ∈ 𝓗 := Finset.mem_coe.mp hERM.1
    have hnot : ¬ (ε < errProb D f g) := fun hlt => hsB ⟨g, hgH, hcons, hlt⟩
    exact hsT (not_lt.mp hnot)
  have hTc : sampleLaw D n {s : Sample X n | errProb D f (A n (labeledBy f s)) ≤ ε}ᶜ
      ≤ ENNReal.ofReal δ := by
    refine (measure_mono hincl).trans ?_
    refine (measure_union_le _ _).trans ?_
    rw [hGnull, zero_add]
    exact hBadle
  have hcover : (1 : ℝ≥0∞) ≤
      sampleLaw D n {s : Sample X n | errProb D f (A n (labeledBy f s)) ≤ ε} +
        sampleLaw D n {s : Sample X n | errProb D f (A n (labeledBy f s)) ≤ ε}ᶜ := by
    have h := measure_union_le (μ := sampleLaw D n)
      {s : Sample X n | errProb D f (A n (labeledBy f s)) ≤ ε}
      {s : Sample X n | errProb D f (A n (labeledBy f s)) ≤ ε}ᶜ
    rwa [Set.union_compl_self, measure_univ] at h
  rw [ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one]
  refine tsub_le_iff_right.mpr ?_
  refine hcover.trans ?_
  gcongr

end StatLean.StatisticalLearning
