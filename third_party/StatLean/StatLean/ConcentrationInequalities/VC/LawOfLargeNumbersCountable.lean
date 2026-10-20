module
public import StatLean.ConcentrationInequalities.VC.LawOfLargeNumbers

@[expose] public section

/-!
# VC law of large numbers — countable-class lift

The finite-class core `vc_lln_finset` (Theorem 8.3.15, finite `F`) is lifted
to a countable class $\mathcal{C}$ by monotone exhaustion through finite
subfamilies and dominated convergence (constant dominant $1$, since every
integrand is bounded by $\max(\mu_n(S), \mu(S)) \le 1$):
$$ \mathbb{E} \sup_{S \in \mathcal{C}} |\mu_n(S) - \mu(S)|
   \;\le\; 5400 \sqrt{\mathrm{vc}(\mathcal{C})/n}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.6, Theorem 8.3.15.

**Proof formalization notes.** `Countable 𝒞` is LEAN-ONLY regularity per the
batch sup policy (the book ignores measurability of the uncountable
supremum; a countable class makes `⨆ S ∈ C` a genuine measurable countable
sup). The lift adds **no constant**: frozen numeral `5400` inherited from
`vc_lln_finset` (formula `2 × 40 × √6 × 27 = 2160√6 ≈ 5290.9 ≤ 5400`,
documented there). This work item's single named-sorry fallback is
`integral_biSup_le_of_forall_finset` (the dominated-convergence exhaustion
engine); `vc_lln_countable` itself is a short assembly over it and must
close.

**Bibliographic comments.** The exhaustion argument is folklore measure
theory; the uniform LLN over VC classes is Vapnik–Chervonenkis (1971),
formalized here in the in-expectation form.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*}

/-- Countable-sup lift engine (LEAN-ONLY, batch sup policy): if every finite
subfamily's expected sup obeys a bound `B`, so does the countable class's
expected sup — monotone exhaustion + dominated convergence with constant
dominant `1`. This work item's single named-sorry fallback. -/
lemma integral_biSup_le_of_forall_finset {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {C : Set (Set Ω)}
    -- LEAN-ONLY: countable class per the batch sup policy
    (hCc : C.Countable)
    -- LEAN-ONLY: nonempty class so the sup is genuine
    (hCne : C.Nonempty)
    {g : Set Ω → Ξ → ℝ}
    -- LEAN-ONLY: nonneg integrand (holds for |μ_n − μ|); monotone limits
    (hg0 : ∀ S ξ, 0 ≤ g S ξ)
    -- LEAN-ONLY: uniform bound 1 (dominant for dominated convergence)
    (hg1 : ∀ S ξ, g S ξ ≤ 1)
    -- LEAN-ONLY: measurability of each member's integrand
    (hgmeas : ∀ S ∈ C, Measurable (g S))
    {B : ℝ}
    -- LEAN-ONLY: the finite-subfamily bound being lifted
    (hB : ∀ (F : Finset (Set Ω)) (hFne : F.Nonempty), ↑F ⊆ C →
      ∫ ξ, F.sup' hFne (fun S => g S ξ) ∂P ≤ B) :
    ∫ ξ, ⨆ S ∈ C, g S ξ ∂P ≤ B := by
  classical
  -- Enumerate the countable class as `C = range e`.
  obtain ⟨e, rfl⟩ := hCc.exists_eq_range hCne
  -- Prefix Finsets exhausting `range e`.
  set Fm : ℕ → Finset (Set Ω) := fun m => (Finset.range (m + 1)).image e with hFm_def
  have he_mem : ∀ k, e k ∈ Set.range e := fun k => ⟨k, rfl⟩
  have hFm_ne : ∀ m, (Fm m).Nonempty := by
    intro m
    exact ⟨e 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos m), rfl⟩⟩
  have hFm_sub : ∀ m, ↑(Fm m) ⊆ Set.range e := by
    intro m S hS
    rw [Finset.mem_coe, Finset.mem_image] at hS
    obtain ⟨k, _, rfl⟩ := hS
    exact he_mem k
  -- Finite net maxima.
  set netMax : ℕ → Ξ → ℝ := fun m ξ => (Fm m).sup' (hFm_ne m) (fun S => g S ξ) with hnet_def
  -- Uniform bounds.
  have hnet0 : ∀ m ξ, 0 ≤ netMax m ξ := by
    intro m ξ
    obtain ⟨S, hS⟩ := hFm_ne m
    exact le_trans (hg0 S ξ) (Finset.le_sup' (fun S => g S ξ) hS)
  have hnet1 : ∀ m ξ, netMax m ξ ≤ 1 := by
    intro m ξ
    exact Finset.sup'_le (hFm_ne m) _ (fun S _ => hg1 S ξ)
  -- Monotone in `m`.
  have hFm_mono : Monotone Fm := by
    intro m m' hmm
    apply Finset.image_subset_image
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (Nat.succ_le_succ hmm)
  have hnet_mono : ∀ ξ, Monotone (fun m => netMax m ξ) := by
    intro ξ m m' hmm
    exact Finset.sup'_mono _ (hFm_mono hmm) (hFm_ne m)
  have hbdd : ∀ ξ, BddAbove (Set.range (fun m => netMax m ξ)) := by
    intro ξ
    exact ⟨1, by rintro y ⟨m, rfl⟩; exact hnet1 m ξ⟩
  -- Pointwise limit equals the countable sup.
  have hsup_eq : ∀ ξ, (⨆ S ∈ Set.range e, g S ξ) = ⨆ m, netMax m ξ := by
    intro ξ
    have hle_seq : ∀ k, g (e k) ξ ≤ ⨆ m, netMax m ξ := by
      intro k
      refine le_ciSup_of_le (hbdd ξ) k ?_
      exact Finset.le_sup' (fun S => g S ξ)
        (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩)
    -- The inner prop-sup `⨆ (_ : S ∈ range e), g S ξ` is `g S ξ` when `S ∈ range e`
    -- and the real junk value `sSup ∅ = 0` otherwise; in both cases it is in `[0,1]`.
    have hinner_bound : ∀ S, (⨆ (_ : S ∈ Set.range e), g S ξ) ≤ 1 := by
      intro S
      by_cases hSm : S ∈ Set.range e
      · rw [ciSup_pos hSm]; exact hg1 S ξ
      · rw [ciSup_neg hSm, Real.sSup_empty]; exact zero_le_one
    have hinner_nonneg : ∀ S, 0 ≤ ⨆ (_ : S ∈ Set.range e), g S ξ := by
      intro S
      by_cases hSm : S ∈ Set.range e
      · rw [ciSup_pos hSm]; exact hg0 S ξ
      · rw [ciSup_neg hSm, Real.sSup_empty]
    have hbdd_biSup : BddAbove (Set.range (fun S => ⨆ (_ : S ∈ Set.range e), g S ξ)) :=
      ⟨1, by rintro y ⟨S, rfl⟩; exact hinner_bound S⟩
    apply le_antisymm
    · refine ciSup_le ?_
      intro S
      by_cases hSm : S ∈ Set.range e
      · rw [ciSup_pos hSm]
        obtain ⟨k, rfl⟩ := hSm
        exact hle_seq k
      · rw [ciSup_neg hSm, Real.sSup_empty]
        exact le_ciSup_of_le (hbdd ξ) 0 (hnet0 0 ξ)
    · refine ciSup_le ?_
      intro m
      refine Finset.sup'_le (hFm_ne m) _ ?_
      intro S hS
      rw [Finset.mem_image] at hS
      obtain ⟨k, _, rfl⟩ := hS
      -- `g (e k) ξ ≤ ⨆ S ∈ range e, g S ξ`
      refine le_ciSup_of_le hbdd_biSup (e k) ?_
      rw [ciSup_pos (he_mem k)]
  -- Measurability / integrability of each net max and of the limit.
  have hnet_meas : ∀ m, Measurable (netMax m) := by
    intro m
    have : netMax m = fun ξ => (Fm m).sup' (hFm_ne m) (fun S => g S ξ) := rfl
    rw [this]
    have hgeq : (fun ξ => (Fm m).sup' (hFm_ne m) (fun S => g S ξ))
        = (Fm m).sup' (hFm_ne m) (fun S => fun ξ => g S ξ) := by
      funext ξ; rw [Finset.sup'_apply]
    rw [hgeq]
    exact Finset.measurable_sup' (hFm_ne m) (fun S hS => hgmeas S (hFm_sub m hS))
  have hnet_int : ∀ m, Integrable (netMax m) P := by
    intro m
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (hnet_meas m).aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnet0 m ξ)]
    exact hnet1 m ξ
  have hlim_aem : AEMeasurable (fun ξ => ⨆ m, netMax m ξ) P :=
    AEMeasurable.iSup (fun m => (hnet_meas m).aemeasurable)
  have hlim_int : Integrable (fun ξ => ⨆ m, netMax m ξ) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hlim_aem.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (le_ciSup_of_le (hbdd ξ) 0 (hnet0 0 ξ))]
    exact ciSup_le (fun m => hnet1 m ξ)
  -- Pointwise convergence.
  have hnet_tendsto : ∀ ξ, Filter.Tendsto (fun m => netMax m ξ) Filter.atTop
      (nhds (⨆ m, netMax m ξ)) :=
    fun ξ => tendsto_atTop_ciSup (hnet_mono ξ) (hbdd ξ)
  -- MCT for the integrals.
  have hint_tendsto : Filter.Tendsto (fun m => ∫ ξ, netMax m ξ ∂P) Filter.atTop
      (nhds (∫ ξ, (⨆ m, netMax m ξ) ∂P)) :=
    integral_tendsto_of_tendsto_of_monotone hnet_int hlim_int
      (Filter.Eventually.of_forall hnet_mono) (Filter.Eventually.of_forall hnet_tendsto)
  -- Limit inherits the per-`m` bound `B`.
  have hle : ∫ ξ, (⨆ m, netMax m ξ) ∂P ≤ B :=
    le_of_tendsto hint_tendsto
      (Filter.Eventually.of_forall (fun m => hB (Fm m) (hFm_ne m) (hFm_sub m)))
  -- Rewrite the target countable sup via the pointwise identity.
  have hrw : (fun ξ => ⨆ S ∈ Set.range e, g S ξ) = fun ξ => ⨆ m, netMax m ξ := by
    funext ξ; exact hsup_eq ξ
  rw [hrw]
  exact hle

/-- **Theorem 8.3.15 (VC law of large numbers), countable class** (HDP
§8.3.6; frozen numeral `5400`, inherited — formula in
`VC/LawOfLargeNumbers.lean`): `E sup_{S ∈ 𝒞} |μ_n(S) − μ(S)| ≤ 5400·√d/√n`
for `vc(𝒞) ≤ d`. `Countable 𝒞` is LEAN-ONLY regularity per the sup
policy. -/
theorem vc_lln_countable {Ξ : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: jointly independent sample; HDP Thm 8.3.15
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP Thm 8.3.15 (map form)
    (hlaw : ∀ i, P.map (X i) = μ)
    {C : Set (Set Ω)}
    -- LEAN-ONLY: countable class per the batch sup policy (documented)
    (hCc : C.Countable)
    -- LEAN-ONLY: nonempty class
    (hCne : C.Nonempty)
    -- LEAN-ONLY: measurable members (implicit in the book's setting)
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP Thm 8.3.15
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.6
    (hd1 : 1 ≤ d)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.6 (implicit)
    (hn : 1 ≤ n) :
    ∫ ξ, ⨆ S ∈ C, |empFrac (fun i : Fin n => X i ξ) S - μ.real S| ∂P ≤
      5400 * Real.sqrt d / Real.sqrt n := by
  refine integral_biSup_le_of_forall_finset hCc hCne
    (g := fun S ξ => |empFrac (fun i : Fin n => X i ξ) S - μ.real S|)
    (fun S ξ => abs_nonneg _) ?_ ?_ ?_
  · -- uniform bound `≤ 1`
    intro S ξ
    rw [abs_le]
    have h1 := empFrac_nonneg (fun i : Fin n => X i ξ) S
    have h2 := empFrac_le_one (fun i : Fin n => X i ξ) S
    have h3 : (0 : ℝ) ≤ μ.real S := measureReal_nonneg
    have h4 : μ.real S ≤ 1 := measureReal_le_one
    constructor <;> linarith
  · -- measurability of each member's integrand
    intro S hS
    exact ((measurable_empFrac hXmeas (hCmeas S hS)).sub measurable_const).abs
  · -- finite-subfamily bound = `vc_lln_finset`
    intro F hFne hFC
    have hFmeas : ∀ S ∈ F, MeasurableSet S := fun S hS =>
      hCmeas S (hFC (Finset.mem_coe.mpr hS))
    have hd' : vcDim (↑F : Set (Set Ω)) ≤ (d : ℕ∞) := (vcDim_mono hFC).trans hd
    exact vc_lln_finset hXmeas hindep hlaw F hFne hFmeas hd' hd1 hn

end StatLean.ConcentrationInequalities
