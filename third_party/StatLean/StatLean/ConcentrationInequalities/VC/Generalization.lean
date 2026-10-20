module
public import StatLean.ConcentrationInequalities.VC.LawOfLargeNumbersCountable
public import Mathlib.Order.SymmDiff

@[expose] public section

/-!
# VC generalization bound for empirical risk minimization

Boolean learning: target `T = 𝟙_Θ`, hypotheses `f = 𝟙_S` for `S` in a class
$\mathcal{C}$ with $\mathrm{vc}(\mathcal{C}) \le d$. The risk is
$R(f) = \mathbb{E}(f(X) - T(X))^2 = \mu(S \,\Delta\, \Theta)$ and the
empirical risk is $R_n(f) = \mu_n(S \,\Delta\, \Theta)$. For the empirical
risk minimizer $f^*_n$,
$$ \mathbb{E}\, R(f^*_n) \;\le\; \inf_{f \in \mathcal{F}} R(f)
   \;+\; 10800 \sqrt{d/n}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.4.3, Theorem 8.4.5; Exercise 8.29 (invariance
of VC dimension under the loss transformation); Eq. (8.40) (excess-risk
bound).

**Proof formalization notes.** For Boolean `f, T`: `(f − T)² = 𝟙_{S ∆ Θ}`
pointwise, so the loss class is the symmetric-difference image
`(· ∆ Θ) '' 𝒞` — Exercise 8.29 (we prove it: shattering is preserved under
the labeling bijection `T ↦ T ∆ (Λ ∩ Θ)`). Frozen numeral
`10800 = 2 × 5400` (Eq. (8.40) excess risk ≤ 2·sup-deviation, then
`vc_lln_countable` on the loss class at the same `d`). Hypothesis notes:
`hERM` (the minimizer property) and `Sn` are **data** (USER-INPUT — the
book's Definition 8.4.3 presupposes an ERM); `hRmeas` is LEAN-ONLY
selection regularity (the book's `E R(f*_n)` silently assumes the risk of
the selected hypothesis is measurable in the sample); `Countable 𝒞` is
LEAN-ONLY per the batch sup policy. Work-item single named-sorry fallback:
`vcDim_symmDiff_image` (Exercise 8.29); the excess-risk chain
(`excess_risk_le_two_mul_sup`) and the integral assembly must close.

**Bibliographic comments.** Theorem 8.4.5 is the classical
Vapnik–Chervonenkis generalization bound in in-expectation form; the
reduction of Boolean squared loss to symmetric differences is folklore.
-/

open MeasureTheory ProbabilityTheory symmDiff
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*}

/-- Shattering is invariant under symmetric difference with a fixed target
(HDP Exercise 8.29 core): the labeling bijection `T ↦ T ∆ (Λ ∩ Θ)` matches
traces of `C` with traces of `(· ∆ Θ) '' C`. -/
theorem shatters_symmDiff_image {C : Set (Set Ω)} (Θ : Set Ω)
    (Λ : Finset Ω) :
    Shatters ((· ∆ Θ) '' C) Λ ↔ Shatters C Λ := by
  classical
  have hdistrib : ∀ (A B E : Set Ω), A ∩ (B ∆ E) = (A ∩ B) ∆ (A ∩ E) :=
    fun A B E => inf_symmDiff_distrib_left A B E
  -- shattering is preserved by `· ∆ Θ` for an arbitrary class `D`.
  have himp : ∀ (D : Set (Set Ω)), Shatters D Λ → Shatters ((· ∆ Θ) '' D) Λ := by
    intro D hD T hT
    have hsub : (↑T : Set Ω) ∆ ((↑Λ : Set Ω) ∩ Θ) ⊆ ↑Λ :=
      symmDiff_le_sup.trans (sup_le (Finset.coe_subset.mpr hT) Set.inter_subset_left)
    obtain ⟨T₀, hT₀sub, hT₀eq⟩ := exists_finset_coe_of_subset_coe hsub
    obtain ⟨S, hS, hSeq⟩ := hD T₀ hT₀sub
    refine ⟨S ∆ Θ, ⟨S, hS, rfl⟩, ?_⟩
    rw [hdistrib, hSeq, hT₀eq]
    exact symmDiff_symmDiff_cancel_right _ _
  constructor
  · intro h
    have himg := himp ((· ∆ Θ) '' C) h
    have hinv : (· ∆ Θ) '' ((· ∆ Θ) '' C) = C := by
      rw [Set.image_image]
      simp only [symmDiff_symmDiff_cancel_right, Set.image_id']
    rwa [hinv] at himg
  · exact himp C


/-- **Exercise 8.29** (HDP §8.4.3, we prove it): the loss class of a Boolean
class has the same VC dimension, `vc({(f − T)² : f ∈ ℱ}) = vc(ℱ)`. This
work item's single named-sorry fallback. -/
theorem vcDim_symmDiff_image {C : Set (Set Ω)} (Θ : Set Ω) :
    vcDim ((· ∆ Θ) '' C) = vcDim C := by
  unfold vcDim
  simp only [shatters_symmDiff_image]

/-- Pointwise excess-risk bound (HDP §8.4.3, Eq. (8.40)):
`R(f*_n) ≤ R(f₀) + 2 sup_{f ∈ ℱ} |R_n(f) − R(f)|` for any ERM `Sn` and any
competitor `S₀`, at a fixed sample. -/
lemma excess_risk_le_two_mul_sup [MeasurableSpace Ω] {C : Set (Set Ω)}
    -- LEAN-ONLY: nonempty class so the sup is genuine
    (hCne : C.Nonempty)
    {Θ Sn S₀ : Set Ω}
    -- USER-INPUT: the selected hypothesis lies in the class; HDP Def 8.4.3
    (hSn : Sn ∈ C)
    -- USER-INPUT: the competitor lies in the class; HDP Thm 8.4.5
    (hS₀ : S₀ ∈ C)
    {n : ℕ} (x : Fin n → Ω) {μ : Measure Ω} [IsProbabilityMeasure μ]
    -- USER-INPUT: empirical-risk minimality of Sn at this sample;
    -- HDP Definition 8.4.3 (ERM is data)
    (hERM : ∀ S ∈ C, empFrac x (Sn ∆ Θ) ≤ empFrac x (S ∆ Θ)) :
    μ.real (Sn ∆ Θ) ≤ μ.real (S₀ ∆ Θ) +
      2 * ⨆ S ∈ C, |empFrac x (S ∆ Θ) - μ.real (S ∆ Θ)| := by
  classical
  have hd1 : ∀ S : Set Ω, |empFrac x (S ∆ Θ) - μ.real (S ∆ Θ)| ≤ 1 := by
    intro S
    rw [abs_le]
    have ha := empFrac_nonneg x (S ∆ Θ)
    have hb := empFrac_le_one x (S ∆ Θ)
    have hc : (0 : ℝ) ≤ μ.real (S ∆ Θ) := measureReal_nonneg
    have he : μ.real (S ∆ Θ) ≤ 1 := measureReal_le_one
    constructor <;> linarith
  have hbdd : BddAbove (Set.range (fun S => ⨆ (_ : S ∈ C),
      |empFrac x (S ∆ Θ) - μ.real (S ∆ Θ)|)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨S, rfl⟩
    dsimp only
    by_cases hS : S ∈ C
    · rw [ciSup_pos hS]; exact hd1 S
    · rw [ciSup_neg hS, Real.sSup_empty]; exact zero_le_one
  set dS := ⨆ S ∈ C, |empFrac x (S ∆ Θ) - μ.real (S ∆ Θ)| with hdS
  have hdev : ∀ S ∈ C, |empFrac x (S ∆ Θ) - μ.real (S ∆ Θ)| ≤ dS := by
    intro S hS
    rw [hdS]
    have heq : (⨆ (_ : S ∈ C), |empFrac x (S ∆ Θ) - μ.real (S ∆ Θ)|)
        = |empFrac x (S ∆ Θ) - μ.real (S ∆ Θ)| := ciSup_pos hS
    exact le_ciSup_of_le hbdd S heq.ge
  have h1 := (abs_le.mp (hdev Sn hSn)).1
  have h2 := (abs_le.mp (hdev S₀ hS₀)).2
  have h3 := hERM S₀ hS₀
  linarith

/-- The CDF-style deviation `|μ_n(S) − μ(S)|` is bounded by `1`. -/
private lemma abs_empFrac_sub_le_one_gen [MeasurableSpace Ω] {n : ℕ} (x : Fin n → Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω) :
    |empFrac x S - μ.real S| ≤ 1 := by
  rw [abs_le]
  have ha := empFrac_nonneg x S
  have hb := empFrac_le_one x S
  have hc : (0 : ℝ) ≤ μ.real S := measureReal_nonneg
  have he : μ.real S ≤ 1 := measureReal_le_one
  constructor <;> linarith

/-- Integrability of a countable-class expected sup (LEAN-ONLY: enumerate the
class and dominate the monotone net maxima by `1`; mirrors the engine of
`integral_biSup_le_of_forall_finset`). -/
private lemma integrable_biSup_of_countable {Ξ : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace Ω] {P : Measure Ξ} [IsProbabilityMeasure P]
    {C : Set (Set Ω)} (hCc : C.Countable) (hCne : C.Nonempty)
    {g : Set Ω → Ξ → ℝ}
    (hg0 : ∀ S ξ, 0 ≤ g S ξ) (hg1 : ∀ S ξ, g S ξ ≤ 1)
    (hgmeas : ∀ S ∈ C, Measurable (g S)) :
    Integrable (fun ξ => ⨆ S ∈ C, g S ξ) P := by
  classical
  obtain ⟨e, rfl⟩ := hCc.exists_eq_range hCne
  set Fm : ℕ → Finset (Set Ω) := fun m => (Finset.range (m + 1)).image e with hFm_def
  have hFm_ne : ∀ m, (Fm m).Nonempty := fun m =>
    ⟨e 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos m), rfl⟩⟩
  have hFm_sub : ∀ m, ↑(Fm m) ⊆ Set.range e := by
    intro m S hS
    rw [Finset.mem_coe, Finset.mem_image] at hS
    obtain ⟨k, _, rfl⟩ := hS; exact ⟨k, rfl⟩
  set netMax : ℕ → Ξ → ℝ := fun m ξ => (Fm m).sup' (hFm_ne m) (fun S => g S ξ)
    with hnet_def
  have hnet0 : ∀ m ξ, 0 ≤ netMax m ξ := by
    intro m ξ; obtain ⟨S, hS⟩ := hFm_ne m
    exact le_trans (hg0 S ξ) (Finset.le_sup' (fun S => g S ξ) hS)
  have hnet1 : ∀ m ξ, netMax m ξ ≤ 1 := fun m ξ =>
    Finset.sup'_le (hFm_ne m) _ (fun S _ => hg1 S ξ)
  have hbdd : ∀ ξ, BddAbove (Set.range (fun m => netMax m ξ)) :=
    fun ξ => ⟨1, by rintro y ⟨m, rfl⟩; exact hnet1 m ξ⟩
  have he_mem : ∀ k, e k ∈ Set.range e := fun k => ⟨k, rfl⟩
  have hsup_eq : ∀ ξ, (⨆ S ∈ Set.range e, g S ξ) = ⨆ m, netMax m ξ := by
    intro ξ
    have hle_seq : ∀ k, g (e k) ξ ≤ ⨆ m, netMax m ξ := by
      intro k
      refine le_ciSup_of_le (hbdd ξ) k ?_
      exact Finset.le_sup' (fun S => g S ξ)
        (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩)
    have hinner_bound : ∀ S, (⨆ (_ : S ∈ Set.range e), g S ξ) ≤ 1 := by
      intro S; by_cases hSm : S ∈ Set.range e
      · rw [ciSup_pos hSm]; exact hg1 S ξ
      · rw [ciSup_neg hSm, Real.sSup_empty]; exact zero_le_one
    have hbdd_biSup : BddAbove (Set.range (fun S => ⨆ (_ : S ∈ Set.range e), g S ξ)) :=
      ⟨1, by rintro y ⟨S, rfl⟩; exact hinner_bound S⟩
    apply le_antisymm
    · refine ciSup_le ?_
      intro S; by_cases hSm : S ∈ Set.range e
      · rw [ciSup_pos hSm]; obtain ⟨k, rfl⟩ := hSm; exact hle_seq k
      · rw [ciSup_neg hSm, Real.sSup_empty]
        exact le_ciSup_of_le (hbdd ξ) 0 (hnet0 0 ξ)
    · refine ciSup_le ?_
      intro m
      refine Finset.sup'_le (hFm_ne m) _ ?_
      intro S hS
      rw [Finset.mem_image] at hS
      obtain ⟨k, _, rfl⟩ := hS
      refine le_ciSup_of_le hbdd_biSup (e k) ?_
      rw [ciSup_pos (he_mem k)]
  have hnet_meas : ∀ m, Measurable (netMax m) := by
    intro m
    have hgeq : (fun ξ => (Fm m).sup' (hFm_ne m) (fun S => g S ξ))
        = (Fm m).sup' (hFm_ne m) (fun S => fun ξ => g S ξ) := by
      funext ξ; rw [Finset.sup'_apply]
    show Measurable (fun ξ => (Fm m).sup' (hFm_ne m) (fun S => g S ξ))
    rw [hgeq]
    exact Finset.measurable_sup' (hFm_ne m) (fun S hS => hgmeas S (hFm_sub m hS))
  have hlim_aem : AEMeasurable (fun ξ => ⨆ m, netMax m ξ) P :=
    AEMeasurable.iSup (fun m => (hnet_meas m).aemeasurable)
  have heqfun : (fun ξ => ⨆ S ∈ Set.range e, g S ξ) = fun ξ => ⨆ m, netMax m ξ := by
    funext ξ; exact hsup_eq ξ
  rw [heqfun]
  refine Integrable.mono' (integrable_const (1 : ℝ)) hlim_aem.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (le_ciSup_of_le (hbdd ξ) 0 (hnet0 0 ξ))]
  exact ciSup_le (fun m => hnet1 m ξ)

/-- The image-class expected sup equals the composed sup over the base class
(LEAN-ONLY reindexing over the image; junk `sSup ∅ = 0` handled by
nonnegativity). -/
private lemma biSup_symmDiff_image_eq {C : Set (Set Ω)} (Θ : Set Ω)
    {f : Set Ω → ℝ} (hne : C.Nonempty)
    (h0 : ∀ S, 0 ≤ f S) (h1 : ∀ S, f S ≤ 1) :
    (⨆ S' ∈ (· ∆ Θ) '' C, f S') = ⨆ S ∈ C, f (S ∆ Θ) := by
  classical
  obtain ⟨S₀, hS₀⟩ := hne
  have hFbd : BddAbove (Set.range (fun S' => ⨆ (_ : S' ∈ (· ∆ Θ) '' C), f S')) := by
    refine ⟨1, ?_⟩; rintro y ⟨S', rfl⟩
    dsimp only
    by_cases h : S' ∈ (· ∆ Θ) '' C
    · rw [ciSup_pos h]; exact h1 S'
    · rw [ciSup_neg h, Real.sSup_empty]; exact zero_le_one
  have hGbd : BddAbove (Set.range (fun S => ⨆ (_ : S ∈ C), f (S ∆ Θ))) := by
    refine ⟨1, ?_⟩; rintro y ⟨S, rfl⟩
    dsimp only
    by_cases h : S ∈ C
    · rw [ciSup_pos h]; exact h1 _
    · rw [ciSup_neg h, Real.sSup_empty]; exact zero_le_one
  have hF0 : 0 ≤ ⨆ S' ∈ (· ∆ Θ) '' C, f S' := by
    have hmem : S₀ ∆ Θ ∈ (· ∆ Θ) '' C := ⟨S₀, hS₀, rfl⟩
    refine le_ciSup_of_le hFbd (S₀ ∆ Θ) ?_
    have heq : (⨆ (_ : (S₀ ∆ Θ) ∈ (· ∆ Θ) '' C), f (S₀ ∆ Θ)) = f (S₀ ∆ Θ) :=
      ciSup_pos hmem
    rw [heq]; exact h0 _
  have hG0 : 0 ≤ ⨆ S ∈ C, f (S ∆ Θ) := by
    refine le_ciSup_of_le hGbd S₀ ?_
    have heq : (⨆ (_ : S₀ ∈ C), f (S₀ ∆ Θ)) = f (S₀ ∆ Θ) := ciSup_pos hS₀
    rw [heq]; exact h0 _
  apply le_antisymm
  · refine ciSup_le fun S' => ?_
    by_cases h : S' ∈ (· ∆ Θ) '' C
    · rw [ciSup_pos h]
      obtain ⟨S, hS, rfl⟩ := h
      have heq : (⨆ (_ : S ∈ C), f (S ∆ Θ)) = f (S ∆ Θ) := ciSup_pos hS
      exact le_ciSup_of_le hGbd S heq.ge
    · rw [ciSup_neg h, Real.sSup_empty]; exact hG0
  · refine ciSup_le fun S => ?_
    by_cases h : S ∈ C
    · rw [ciSup_pos h]
      have hmem : S ∆ Θ ∈ (· ∆ Θ) '' C := ⟨S, h, rfl⟩
      have heq : (⨆ (_ : (S ∆ Θ) ∈ (· ∆ Θ) '' C), f (S ∆ Θ)) = f (S ∆ Θ) :=
        ciSup_pos hmem
      exact le_ciSup_of_le hFbd (S ∆ Θ) heq.ge
    · rw [ciSup_neg h, Real.sSup_empty]; exact hF0

/-- **Theorem 8.4.5 (VC generalization bound)** (HDP §8.4.3; frozen numeral
`10800 = 2 × 5400`, formula in the module notes): the expected risk of the
empirical risk minimizer is within `10800·√d/√n` of the best risk in the
class. -/
theorem vc_generalization {Ξ : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: jointly independent sample; HDP Thm 8.4.5
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP Thm 8.4.5 (map form)
    (hlaw : ∀ i, P.map (X i) = μ)
    {C : Set (Set Ω)}
    -- LEAN-ONLY: countable class per the batch sup policy (documented)
    (hCc : C.Countable)
    -- LEAN-ONLY: nonempty class
    (hCne : C.Nonempty)
    -- LEAN-ONLY: measurable members
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {Θ : Set Ω}
    -- USER-INPUT: measurable Boolean target; HDP §8.4 setting
    (hΘ : MeasurableSet Θ)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound on the hypothesis class; HDP Thm 8.4.5
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.4.3
    (hd1 : 1 ≤ d)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.4.3 (implicit)
    (hn : 1 ≤ n)
    (Sn : Ξ → Set Ω)
    -- USER-INPUT: the learner's output lies in the class; HDP Def 8.4.3
    (hSn_mem : ∀ ξ, Sn ξ ∈ C)
    -- USER-INPUT: empirical-risk minimality (ERM is data); HDP Def 8.4.3
    (hERM : ∀ ξ, ∀ S ∈ C, empFrac (fun i : Fin n => X i ξ) (Sn ξ ∆ Θ) ≤
      empFrac (fun i : Fin n => X i ξ) (S ∆ Θ))
    -- LEAN-ONLY: selection regularity — the sample-indexed risk of the
    -- chosen hypothesis is a.e.-strongly-measurable (the book's E R(f*_n)
    -- presupposes this); no scope change
    (hRmeas : MeasureTheory.AEStronglyMeasurable
      (fun ξ => μ.real (Sn ξ ∆ Θ)) P)
    {S₀ : Set Ω}
    -- USER-INPUT: competitor hypothesis realizing (or approximating) the
    -- best risk; HDP Thm 8.4.5
    (hS₀ : S₀ ∈ C) :
    ∫ ξ, μ.real (Sn ξ ∆ Θ) ∂P ≤
      μ.real (S₀ ∆ Θ) + 10800 * Real.sqrt d / Real.sqrt n := by
  classical
  -- the symmetric-difference (loss) image class has the same VC dimension.
  have hDc : ((· ∆ Θ) '' C).Countable := hCc.image _
  have hDne : ((· ∆ Θ) '' C).Nonempty := hCne.image _
  have hDmeas : ∀ S' ∈ (· ∆ Θ) '' C, MeasurableSet S' := by
    intro S' hS'
    obtain ⟨S, hS, rfl⟩ := hS'
    exact (hCmeas S hS).symmDiff hΘ
  have hDd : vcDim ((· ∆ Θ) '' C) ≤ (d : ℕ∞) := by
    rw [vcDim_symmDiff_image]; exact hd
  -- LLN on the loss class.
  have key := vc_lln_countable (Ξ := Ξ) (P := P) (μ := μ) (X := X)
    hXmeas hindep hlaw hDc hDne hDmeas hDd hd1 hn
  -- integrability of the loss-class expected sup.
  have hI : Integrable (fun ξ => ⨆ S' ∈ (· ∆ Θ) '' C,
      |empFrac (fun i : Fin n => X i ξ) S' - μ.real S'|) P := by
    refine integrable_biSup_of_countable hDc hDne
      (fun S ξ => abs_nonneg _)
      (fun S ξ => abs_empFrac_sub_le_one_gen (fun i : Fin n => X i ξ) μ S) ?_
    intro S' hS'
    exact ((measurable_empFrac hXmeas (hDmeas S' hS')).sub measurable_const).abs
  -- risk of the ERM output is integrable (bounded by `1`).
  have hf_int : Integrable (fun ξ => μ.real (Sn ξ ∆ Θ)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hRmeas
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  -- pointwise excess-risk bound, rewritten onto the loss class.
  have hpt : ∀ ξ, μ.real (Sn ξ ∆ Θ) ≤ μ.real (S₀ ∆ Θ) + 2 *
      ⨆ S' ∈ (· ∆ Θ) '' C, |empFrac (fun i : Fin n => X i ξ) S' - μ.real S'| := by
    intro ξ
    have he := excess_risk_le_two_mul_sup (μ := μ) hCne (hSn_mem ξ) hS₀
      (fun i : Fin n => X i ξ) (hERM ξ)
    rw [biSup_symmDiff_image_eq Θ hCne
      (fun S => abs_nonneg _)
      (fun S => abs_empFrac_sub_le_one_gen (fun i : Fin n => X i ξ) μ S)]
    exact he
  -- integrate.
  have hg_int : Integrable (fun ξ => μ.real (S₀ ∆ Θ) + 2 *
      ⨆ S' ∈ (· ∆ Θ) '' C,
        |empFrac (fun i : Fin n => X i ξ) S' - μ.real S'|) P :=
    (integrable_const _).add (hI.const_mul 2)
  calc ∫ ξ, μ.real (Sn ξ ∆ Θ) ∂P
      ≤ ∫ ξ, (μ.real (S₀ ∆ Θ) + 2 *
          ⨆ S' ∈ (· ∆ Θ) '' C,
            |empFrac (fun i : Fin n => X i ξ) S' - μ.real S'|) ∂P :=
        integral_mono hf_int hg_int hpt
    _ = μ.real (S₀ ∆ Θ) + 2 * ∫ ξ, ⨆ S' ∈ (· ∆ Θ) '' C,
          |empFrac (fun i : Fin n => X i ξ) S' - μ.real S'| ∂P := by
        rw [integral_add (integrable_const _) (hI.const_mul 2), integral_const,
          integral_const_mul, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ μ.real (S₀ ∆ Θ) + 2 * (5400 * Real.sqrt d / Real.sqrt n) := by
        have hk := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ = μ.real (S₀ ∆ Θ) + 10800 * Real.sqrt d / Real.sqrt n := by ring

end StatLean.ConcentrationInequalities
