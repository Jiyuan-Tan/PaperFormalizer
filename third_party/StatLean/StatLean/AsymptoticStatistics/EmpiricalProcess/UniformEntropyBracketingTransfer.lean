module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyStructural
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section

/-!
# Uniform covering to finite bracketing by localization

The pairwise-separation argument used in van der Vaart Theorem 19.13. A
measurable majorant localizes the class on
`{V ≤ M}`.  Uniform relative `L¹` covering is converted there to an
absolute all-law cover with one uniform cardinal bound, hence to finite gamma
dimension and finite bracketing.  A measurable tail expands the localized
brackets back to the original class.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, p.274.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped BigOperators ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

open UniformEntropyStructural

/-! ### Gamma dimension and Boolean coding -/

/-- A finite carrier is gamma-shattered when one threshold vector realizes
every Boolean labeling with margin `γ` on the corresponding side.

Edge behavior: the empty carrier is shattered exactly when `E` is nonempty.
Nonpositive margins use the same total formula, while all consumers require
`0 < γ`. -/
def GammaShatters (E : Set (Ω → ℝ)) (γ : ℝ) (S : Finset Ω) : Prop :=
  ∃ threshold : ↑S → ℝ, ∀ label : ↑S → Bool, ∃ f ∈ E, ∀ x : ↑S,
    (label x = true → threshold x + γ ≤ f x) ∧
    (label x = false → f x ≤ threshold x - γ)

/-- Gamma dimension as the supremum, in `ℕ∞`, of cardinalities of finite
gamma-shattered carriers.

Edge behavior: if no finite carrier is shattered, every summand is zero and
the dimension is zero. -/
noncomputable def gammaDimension (E : Set (Ω → ℝ)) (γ : ℝ) : ℕ∞ := by
  classical
  exact ⨆ S : Finset Ω, if GammaShatters E γ S then (S.card : ℕ∞) else 0

/-- Fixed-scale finite gamma dimension.

This abbreviation states the `ℕ∞` finiteness claim directly. -/
def HasFiniteGammaDimension (E : Set (Ω → ℝ)) (γ : ℝ) : Prop :=
  gammaDimension E γ < ⊤

/-- Real-valued Hamming distance on a finite Boolean cube.

Edge behavior: the empty cube has distance zero. -/
def hammingDist {n : ℕ} (a b : Fin n → Bool) : ℝ :=
  ((Finset.univ.filter fun i ↦ a i ≠ b i).card : ℝ)

/-- Boolean threshold independence, written separately for the Assouad
double-counting argument.

Edge behavior agrees with `GammaShatters`: the empty carrier only asks for a
realizing member of the class. -/
def BooleanIndependent (E : Set (Ω → ℝ)) (γ : ℝ) (S : Finset Ω) : Prop :=
  ∃ threshold : ↑S → ℝ, ∀ label : ↑S → Bool, ∃ f ∈ E, ∀ x : ↑S,
    (label x = true → threshold x + γ ≤ f x) ∧
    (label x = false → f x ≤ threshold x - γ)

omit [MeasurableSpace Ω] in
/-- Gamma shattering and Boolean threshold independence are the two names for
the same finite labeling condition. -/
theorem gammaShatters_iff_booleanIndependent
    (E : Set (Ω → ℝ)) (γ : ℝ) (S : Finset Ω) :
    GammaShatters E γ S ↔ BooleanIndependent E γ S := by
  rfl

private theorem three_pow_le_two_pow_codingExponent (n : ℕ) :
    3 ^ n ≤ 2 ^ (2 * n - n / 4 - n / 8) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 8
    · interval_cases n <;> norm_num
    · let m := n - 8
      have hm : m < n := by omega
      have hn_eq : n = m + 8 := by omega
      have hdiv4 : (m + 8) / 4 = m / 4 + 2 := by omega
      have hdiv8 : (m + 8) / 8 = m / 8 + 1 := by omega
      rw [hn_eq, pow_add]
      calc
        3 ^ m * 3 ^ 8 ≤ 2 ^ (2 * m - m / 4 - m / 8) * 2 ^ 13 :=
          Nat.mul_le_mul (ih m hm) (by norm_num)
        _ = 2 ^ (2 * (m + 8) - (m + 8) / 4 - (m + 8) / 8) := by
          rw [← pow_add, hdiv4, hdiv8]
          congr 2
          omega

private theorem boolean_hammingVolume_le (n : ℕ) :
    (∑ k ∈ Finset.range (n / 4 + 1), n.choose k) ≤ 2 ^ (n - n / 8) := by
  have hR : n / 4 ≤ n := Nat.div_le_self _ _
  have hrange : Finset.range (n / 4 + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (Nat.add_le_add_right hR 1)
  have hweighted :
      2 ^ (n - n / 4) * (∑ k ∈ Finset.range (n / 4 + 1), n.choose k)
        ≤ 3 ^ n := by
    calc
      2 ^ (n - n / 4) * (∑ k ∈ Finset.range (n / 4 + 1), n.choose k)
          = ∑ k ∈ Finset.range (n / 4 + 1),
              2 ^ (n - n / 4) * n.choose k := by rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range (n / 4 + 1),
              2 ^ (n - k) * n.choose k := by
            apply Finset.sum_le_sum
            intro k hk
            apply Nat.mul_le_mul_right
            apply Nat.pow_le_pow_right (by omega)
            have hkR : k ≤ n / 4 := by simpa using Finset.mem_range.mp hk
            omega
      _ ≤ ∑ k ∈ Finset.range (n + 1),
              2 ^ (n - k) * n.choose k := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦ by positivity)
      _ = 3 ^ n := by
            have h := add_pow (1 : ℕ) 2 n
            simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.symm
  have htotal :
      2 ^ (n - n / 4) * (∑ k ∈ Finset.range (n / 4 + 1), n.choose k)
        ≤ 2 ^ (n - n / 4) * 2 ^ (n - n / 8) := by
    calc
      _ ≤ 3 ^ n := hweighted
      _ ≤ 2 ^ (2 * n - n / 4 - n / 8) :=
        three_pow_le_two_pow_codingExponent n
      _ = 2 ^ (n - n / 4) * 2 ^ (n - n / 8) := by
        rw [← pow_add]
        congr 2
        omega
  exact Nat.le_of_mul_le_mul_left htotal (by positivity)

private def booleanHammingNat {n : ℕ} (a b : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ a i ≠ b i).card

private theorem booleanHammingNat_comm {n : ℕ} (a b : Fin n → Bool) :
    booleanHammingNat a b = booleanHammingNat b a := by
  simp only [booleanHammingNat, ne_comm]

/-- A finite Boolean cube has an exponentially large separated code.  The
coarse constants suffice for the gamma-dimension contradiction and totalize
the low-dimensional boundary through natural-number division. -/
theorem exists_booleanCode_halfDistance (n : ℕ) :
    ∃ C : Finset (Fin n → Bool),
      2 ^ (n / 8) ≤ C.card ∧
      ∀ a ∈ C, ∀ b ∈ C, a ≠ b → (n : ℝ) / 4 ≤ hammingDist a b := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨{fun _ ↦ false}, by simp, ?_⟩
    intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    exact (hab (ha.trans hb.symm)).elim
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let all : Finset (Fin n → Bool) := Finset.univ
  let Good : Finset (Fin n → Bool) → Prop := fun C ↦
    ∀ a ∈ C, ∀ b ∈ C, a ≠ b →
      n ≤ 4 * booleanHammingNat a b
  let families := all.powerset.filter Good
  have hfamilies : families.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    intro a ha
    simp at ha
  obtain ⟨C, hCmax⟩ := families.exists_maximal hfamilies
  rw [maximal_iff] at hCmax
  have hCmem := hCmax.1
  rw [Finset.mem_filter, Finset.mem_powerset] at hCmem
  have hC_all : C ⊆ all := hCmem.1
  have hCgood : Good C := hCmem.2
  let ball : (Fin n → Bool) → Finset (Fin n → Bool) := fun b ↦
    all.filter fun a ↦ 4 * booleanHammingNat a b < n
  have hball_card : ∀ b, (ball b).card ≤ 2 ^ (n - n / 8) := by
    intro b
    let D : (Fin n → Bool) → Finset (Fin n) := fun a ↦
      Finset.univ.filter fun i ↦ a i ≠ b i
    have hDcard (a : Fin n → Bool) : (D a).card = booleanHammingNat a b := by
      rfl
    have hDinj : Function.Injective D := by
      intro a c hac
      funext i
      have hi : (a i ≠ b i) ↔ (c i ≠ b i) := by
        have := Finset.ext_iff.mp hac i
        simpa [D] using this
      by_cases hab : a i = b i
      · have hcb : c i = b i := by
          apply not_ne_iff.mp
          intro hcb
          exact (hi.mpr hcb) hab
        exact hab.trans hcb.symm
      · have hcb : c i ≠ b i := hi.mp hab
        have hna : a i = !(b i) := Bool.eq_not_iff.mpr hab
        have hnc : c i = !(b i) := Bool.eq_not_iff.mpr hcb
        exact hna.trans hnc.symm
    let smallSets : Finset (Finset (Fin n)) :=
      (Finset.range (n / 4 + 1)).biUnion fun k ↦ Finset.univ.powersetCard k
    have himage : (ball b).image D ⊆ smallSets := by
      intro T hT
      rw [Finset.mem_image] at hT
      obtain ⟨a, ha, rfl⟩ := hT
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_biUnion]
      refine ⟨(D a).card, ?_, ?_⟩
      · rw [Finset.mem_range]
        rw [hDcard]
        omega
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, rfl⟩
    calc
      (ball b).card = ((ball b).image D).card :=
        (Finset.card_image_of_injective _ hDinj).symm
      _ ≤ smallSets.card := Finset.card_le_card himage
      _ ≤ ∑ k ∈ Finset.range (n / 4 + 1),
            (Finset.univ.powersetCard k : Finset (Finset (Fin n))).card :=
        Finset.card_biUnion_le
      _ = ∑ k ∈ Finset.range (n / 4 + 1), n.choose k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      _ ≤ 2 ^ (n - n / 8) := boolean_hammingVolume_le n
  have hcovered : all ⊆ C.biUnion ball := by
    intro a ha
    by_contra hnot
    rw [Finset.mem_biUnion] at hnot
    push Not at hnot
    have haC : a ∉ C := by
      intro haC
      exact hnot a haC (by simp [ball, ha, booleanHammingNat, hnpos])
    have hinsert_good : Good (insert a C) := by
      intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hxC <;> rcases hy with rfl | hyC
      · exact (hxy rfl).elim
      · apply Nat.le_of_not_gt
        intro hlt
        apply hnot y hyC
        change x ∈ all.filter fun z ↦ 4 * booleanHammingNat z y < n
        exact Finset.mem_filter.mpr ⟨ha, hlt⟩
      · rw [booleanHammingNat_comm]
        apply Nat.le_of_not_gt
        intro hlt
        apply hnot x hxC
        change y ∈ all.filter fun z ↦ 4 * booleanHammingNat z x < n
        exact Finset.mem_filter.mpr ⟨ha, hlt⟩
      · exact hCgood x hxC y hyC hxy
    have hinsert_all : insert a C ⊆ all := Finset.insert_subset ha hC_all
    have hinsert_fam : insert a C ∈ families := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hinsert_all, hinsert_good⟩
    have heq : C = insert a C := hCmax.2 hinsert_fam (Finset.subset_insert a C)
    exact haC (heq.symm ▸ Finset.mem_insert_self a C)
  have hall_card : all.card = 2 ^ n := by
    simp [all]
  have hcube : 2 ^ n ≤ C.card * 2 ^ (n - n / 8) := by
    calc
      2 ^ n = all.card := hall_card.symm
      _ ≤ (C.biUnion ball).card := Finset.card_le_card hcovered
      _ ≤ ∑ b ∈ C, (ball b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ C, 2 ^ (n - n / 8) :=
        Finset.sum_le_sum fun b hb ↦ hball_card b
      _ = C.card * 2 ^ (n - n / 8) := by simp
  have hrate : 2 ^ (n / 8) ≤ C.card := by
    apply Nat.le_of_mul_le_mul_right (c := 2 ^ (n - n / 8))
    · calc
        2 ^ (n / 8) * 2 ^ (n - n / 8) = 2 ^ n := by
          rw [← pow_add]
          congr 2
          omega
        _ ≤ C.card * 2 ^ (n - n / 8) := hcube
    · positivity
  refine ⟨C, hrate, ?_⟩
  intro a ha b hb hab
  have hsep := hCgood a ha b hb hab
  change (n : ℝ) / 4 ≤
    ((Finset.univ.filter fun i ↦ a i ≠ b i).card : ℝ)
  have hsep' : (n : ℝ) ≤ 4 *
      ((Finset.univ.filter fun i ↦ a i ≠ b i).card : ℝ) := by
    exact_mod_cast hsep
  linarith

/-! ### Concrete localization and conditioning -/

/-- Localize a function to a measurable or nonmeasurable set by setting it to
zero off the set.

Edge behavior: localization to `∅` is zero and localization to `univ` is the
original function. -/
noncomputable def localizedFunction (A : Set Ω) (f : Ω → ℝ) : Ω → ℝ :=
  A.indicator f

/-- Image of a function class under localization to `A`.

Edge behavior: the localized empty class is empty. -/
noncomputable def localizedClass (F : Set (Ω → ℝ)) (A : Set Ω) : Set (Ω → ℝ) :=
  localizedFunction A '' F

/-- Conditional probability measure obtained by restricting to `A` and
normalizing by `Q A`.

Edge behavior: if `Q A = 0`, ENNReal inverse totalization is used; theorem
consumers require `0 < Q A` and `Q A < ⊤`. -/
noncomputable def conditionOn (Q : Measure Ω) (A : Set Ω) : Measure Ω :=
  (Q A)⁻¹ • Q.restrict A

/-- Conditioning a probability law on a positive-measure set again gives a
probability law. -/
theorem conditionOn_isProbabilityMeasure
    (Q : Measure Ω) [IsProbabilityMeasure Q] (A : Set Ω)
    (hA : MeasurableSet A) -- restriction evaluation.
    (hApos : 0 < Q A) -- nondegenerate conditioning event.
    : IsProbabilityMeasure (conditionOn Q A) := by
  refine ⟨?_⟩
  rw [conditionOn, Measure.smul_apply, Measure.restrict_apply' hA]
  simp only [Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hApos.ne' (measure_ne_top Q A)

/-- `L¹` norm under a conditional law is the restricted `L¹` norm scaled by
the reciprocal event probability. -/
theorem eLpNorm_one_conditionOn
    (Q : Measure Ω) [IsProbabilityMeasure Q] (A : Set Ω) (f : Ω → ℝ)
    : eLpNorm f 1 (conditionOn Q A) = (Q A)⁻¹ * eLpNorm f 1 (Q.restrict A) := by
  rw [conditionOn, eLpNorm_one_smul_measure]

/-- Localization preserves measurability on a measurable set. -/
theorem measurable_localizedFunction
    (A : Set Ω) (f : Ω → ℝ)
    (hA : MeasurableSet A) -- measurable localization event.
    (hf : Measurable f) -- measurable class member.
    : Measurable (localizedFunction A f) := by
  exact hf.indicator hA

omit [MeasurableSpace Ω] in
/-- Localization preserves pointwise measurability of a class. -/
theorem pointwiseMeasurable_localizedClass
    (F : Set (Ω → ℝ)) (A : Set Ω)
    (hPM : IsPointwiseMeasurable F) -- vdV suitable measurability.
    : IsPointwiseMeasurable (localizedClass F A) := by
  rcases hPM with ⟨F₀, hF₀_countable, hF₀_sub, hF₀_dense⟩
  refine ⟨localizedFunction A '' F₀, hF₀_countable.image _, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f, hF₀_sub hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg_mem, hg_lim⟩ := hF₀_dense f hf
    refine ⟨fun n ↦ localizedFunction A (g n), ?_, ?_⟩
    · intro n
      exact ⟨g n, hg_mem n, rfl⟩
    · intro x
      by_cases hx : x ∈ A
      · simpa [localizedFunction, hx] using hg_lim x
      · simp [localizedFunction, hx]

omit [MeasurableSpace Ω] in
/-- On `{V ≤ M}`, localization converts the majorant into the constant
pointwise bound `M`. -/
theorem localizedClass_uniformBound
    (F : Set (Ω → ℝ)) (V : Ω → ℝ≥0∞) (H : Ω → ℝ) (M : ℝ)
    (hEnv : UniformEntropyStructural.IsEnvelope F H)
      -- measurable real-envelope witness.
    (hHV : ∀ x, ENNReal.ofReal |H x| ≤ V x)
      -- domination by the outer-integral majorant.
    (hM : 0 < M) -- positive localization level.
    : ∀ f ∈ localizedClass F {x | V x ≤ ENNReal.ofReal M}, ∀ x, |f x| ≤ M := by
  rintro _ ⟨f, hf, rfl⟩ x
  by_cases hx : x ∈ {x | V x ≤ ENNReal.ofReal M}
  · have hHM_ofReal : ENNReal.ofReal |H x| ≤ ENNReal.ofReal M :=
      (hHV x).trans hx
    have hHM : |H x| ≤ M := (ENNReal.ofReal_le_ofReal_iff hM.le).mp hHM_ofReal
    have hH_nonneg : 0 ≤ H x := hEnv.1 x
    simpa [localizedFunction, hx] using
      (hEnv.2 f hf x).trans ((abs_of_nonneg hH_nonneg).symm ▸ hHM)
  · simp [localizedFunction, hx, hM.le]

omit [MeasurableSpace Ω] in
/-- Localization preserves an envelope after both are restricted to the same
set. -/
theorem isEnvelope_localizedClass
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (A : Set Ω)
    (hEnv : UniformEntropyStructural.IsEnvelope F G) -- original envelope.
    : UniformEntropyStructural.IsEnvelope
        (localizedClass F A) (localizedFunction A G) := by
  constructor
  · intro x
    by_cases hx : x ∈ A <;> simp [localizedFunction, hx, hEnv.1 x]
  · rintro _ ⟨f, hf, rfl⟩ x
    by_cases hx : x ∈ A
    · simpa [localizedFunction, hx] using hEnv.2 f hf x
    · simp [localizedFunction, hx]

/-! ### From relative covering to finite gamma dimension -/

/-- Finiteness of the `ℕ∞` covering number yields a concrete strict finite
cover. No attainment or minimal-cardinality claim is made. -/
theorem exists_strictFiniteLpCover_of_finiteLpCoveringNumber_lt_top
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {Q : Measure Ω} {r ε : ℝ}
    (hfinite : finiteLpCoveringNumber F G Q r ε < ⊤) -- finiteness to unpack.
    : ∃ S : Finset (Ω → ℝ), IsStrictFiniteLpCover F G Q r ε S := by
  by_contra hnone
  have h_all : ∀ S : Finset (Ω → ℝ), ¬ IsStrictFiniteLpCover F G Q r ε S := by
    simpa only [not_exists] using hnone
  have htop : finiteLpCoveringNumber F G Q r ε = ⊤ := by
    apply le_antisymm le_top
    unfold finiteLpCoveringNumber
    refine le_iInf fun S ↦ le_iInf fun hS ↦ ?_
    exact (h_all S hS).elim
  rw [htop] at hfinite
  exact (lt_irrefl _ hfinite)

/-- Two compatible measurable majorants extracted from a possibly
nonmeasurable outer envelope. `V` is the `ℝ≥0∞` majorant supplied by outer
integration; `H` is the measurable real envelope used for pointwise brackets.
Both are produced internally from the pointwise skeleton. -/
theorem exists_localizingMajorants
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω)
    (hFmeas : ∀ f ∈ F, Measurable f) -- measurable class members.
    (hPM : IsPointwiseMeasurable F) -- vdV suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- possibly nonmeasurable outer envelope.
    (hG1 : outerLpNorm P G 1 < ⊤) -- finite outer first moment.
    : ∃ (V : Ω → ℝ≥0∞) (H : Ω → ℝ),
      Measurable V ∧
      (∀ x, ENNReal.ofReal |G x| ≤ V x) ∧
      (∫⁻ x, V x ∂P) < ⊤ ∧
      Measurable H ∧
      UniformEntropyStructural.IsEnvelope F H ∧
      Integrable H P ∧
      ∀ x, ENNReal.ofReal |H x| ≤ V x := by
  have houter : outerExpectation P (fun x ↦ ENNReal.ofReal |G x|) < ⊤ := by
    simpa [outerLpNorm] using hG1
  let Majorants := {U : Ω → ℝ≥0∞ //
    Measurable U ∧ (fun x ↦ ENNReal.ofReal |G x|) ≤ U}
  have hU_exists : ∃ U : Majorants, (∫⁻ x, (U : Ω → ℝ≥0∞) x ∂P) < ⊤ := by
    by_contra hnone
    have h_all : ∀ U : Majorants, (∫⁻ x, (U : Ω → ℝ≥0∞) x ∂P) = ⊤ := by
      intro U
      exact top_unique (not_lt.mp ((not_exists.mp hnone) U))
    have htop : outerExpectation P (fun x ↦ ENNReal.ofReal |G x|) = ⊤ := by
      unfold outerExpectation
      apply top_unique
      refine le_iInf fun U ↦ ?_
      rw [h_all U]
    rw [htop] at houter
    exact lt_irrefl _ houter
  obtain ⟨U, hUint⟩ := hU_exists
  obtain ⟨F₀, hF₀_countable, hF₀_sub, hF₀_dense⟩ := hPM
  letI : Countable (↥F₀) := hF₀_countable
  let W : Ω → ℝ≥0∞ := fun x ↦ ⨆ f : ↥F₀, ENNReal.ofReal |(f : Ω → ℝ) x|
  have hWmeas : Measurable W := by
    apply Measurable.iSup
    intro f
    exact (continuous_abs.measurable.comp
      (hFmeas f (hF₀_sub f.property))).ennreal_ofReal
  have hWG : ∀ x, W x ≤ ENNReal.ofReal |G x| := by
    intro x
    refine iSup_le fun f ↦ ?_
    simpa [abs_of_nonneg (hEnv.1 x)] using
      ENNReal.ofReal_le_ofReal (hEnv.2 f (hF₀_sub f.property) x)
  have hWtop : ∀ x, W x ≠ ⊤ := by
    intro x htop
    have := hWG x
    rw [htop] at this
    exact ENNReal.ofReal_ne_top (top_le_iff.mp this)
  let V : Ω → ℝ≥0∞ := U
  let H : Ω → ℝ := fun x ↦ (W x).toReal
  have hHmeas : Measurable H := hWmeas.ennreal_toReal
  have hHnonneg : ∀ x, 0 ≤ H x := fun x ↦ ENNReal.toReal_nonneg
  have hHenv : UniformEntropyStructural.IsEnvelope F H := by
    refine ⟨hHnonneg, ?_⟩
    intro f hf x
    obtain ⟨g, hg_mem, hg_lim⟩ := hF₀_dense f hf
    have hbound : ∀ n, |g n x| ≤ H x := by
      intro n
      have hn : ENNReal.ofReal |g n x| ≤ W x :=
        le_iSup (fun f : ↥F₀ ↦ ENNReal.ofReal |(f : Ω → ℝ) x|) ⟨g n, hg_mem n⟩
      rw [← ENNReal.ofReal_toReal (hWtop x)] at hn
      exact (ENNReal.ofReal_le_ofReal_iff (hHnonneg x)).mp hn
    exact le_of_tendsto' ((continuous_abs.tendsto (f x)).comp (hg_lim x)) hbound
  have hWV : ∀ x, W x ≤ V x := by
    intro x
    exact (hWG x).trans (U.2.2 x)
  have hHV : ∀ x, ENNReal.ofReal |H x| ≤ V x := by
    intro x
    rw [abs_of_nonneg (hHnonneg x), ENNReal.ofReal_toReal (hWtop x)]
    exact hWV x
  have hHint : Integrable H P := by
    refine ⟨hHmeas.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    calc
      (∫⁻ x, ‖H x‖ₑ ∂P) ≤ ∫⁻ x, V x ∂P := by
        refine lintegral_mono fun x ↦ ?_
        rw [Real.enorm_eq_ofReal_abs]
        exact hHV x
      _ < ⊤ := hUint
  refine ⟨V, H, U.2.1, U.2.2, hUint, hHmeas, hHenv, hHint, hHV⟩

/-! The next two identities are the outer-integral counterparts of
`lintegral_indicator` and `lintegral_smul_measure`.  They are stated locally
because the functions being covered need not be measurable. -/

theorem outerExpectation_indicator_eq_restrict
    (Q : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (X : Ω → ℝ≥0∞) :
    outerExpectation Q (A.indicator X) = outerExpectation (Q.restrict A) X := by
  classical
  apply le_antisymm
  · unfold outerExpectation
    refine le_iInf fun U ↦ ?_
    let W : Ω → ℝ≥0∞ := A.indicator (U : Ω → ℝ≥0∞)
    have hWmeas : Measurable W := U.2.1.indicator hA
    have hWmaj : A.indicator X ≤ W := by
      intro x
      by_cases hx : x ∈ A
      · simpa [W, hx] using U.2.2 x
      · simp [W, hx]
    calc
      (⨅ W : {W : Ω → ℝ≥0∞ // Measurable W ∧ A.indicator X ≤ W},
          ∫⁻ x, (W : Ω → ℝ≥0∞) x ∂Q)
          ≤ ∫⁻ x, W x ∂Q := iInf_le _
            (⟨W, hWmeas, hWmaj⟩ :
              {W : Ω → ℝ≥0∞ // Measurable W ∧ A.indicator X ≤ W})
      _ = ∫⁻ x, (U : Ω → ℝ≥0∞) x ∂(Q.restrict A) := by
        change (∫⁻ x, A.indicator (U : Ω → ℝ≥0∞) x ∂Q) = _
        rw [lintegral_indicator hA]
  · unfold outerExpectation
    refine le_iInf fun U ↦ ?_
    let W : Ω → ℝ≥0∞ := fun x ↦
      if x ∈ A then (U : Ω → ℝ≥0∞) x else ⊤
    have hWmeas : Measurable W := by
      change Measurable (A.piecewise (U : Ω → ℝ≥0∞) (fun _ ↦ ⊤))
      exact U.2.1.piecewise hA measurable_const
    have hWmaj : X ≤ W := by
      intro x
      by_cases hx : x ∈ A
      · have hxmaj := U.2.2 x
        simpa [W, hx] using hxmaj
      · simp [W, hx]
    calc
      (⨅ W : {W : Ω → ℝ≥0∞ // Measurable W ∧ X ≤ W},
          ∫⁻ x, (W : Ω → ℝ≥0∞) x ∂(Q.restrict A))
          ≤ ∫⁻ x, W x ∂(Q.restrict A) := iInf_le _
            (⟨W, hWmeas, hWmaj⟩ :
              {W : Ω → ℝ≥0∞ // Measurable W ∧ X ≤ W})
      _ ≤ ∫⁻ x, (U : Ω → ℝ≥0∞) x ∂Q := by
        rw [← lintegral_indicator hA]
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ A <;> simp [W, hx]

theorem outerExpectation_smul_measure
    (Q : Measure Ω) (c : ℝ≥0∞) (hc : c ≠ ⊤) (X : Ω → ℝ≥0∞) :
    outerExpectation (c • Q) X = c * outerExpectation Q X := by
  unfold outerExpectation
  rw [ENNReal.mul_iInf (fun h ↦ absurd h hc)]
  congr 1
  funext U
  rw [lintegral_smul_measure, smul_eq_mul]

theorem outerLpNorm_one_indicator_eq_restrict
    (Q : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (f : Ω → ℝ) :
    outerLpNorm Q (A.indicator f) 1 = outerLpNorm (Q.restrict A) f 1 := by
  simp only [outerLpNorm, inv_one, ENNReal.rpow_one]
  rw [show (fun x ↦ ENNReal.ofReal |A.indicator f x|) =
      A.indicator (fun x ↦ ENNReal.ofReal |f x|) by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]]
  exact outerExpectation_indicator_eq_restrict Q A hA _

theorem outerLpNorm_one_smul_measure
    (Q : Measure Ω) (c : ℝ≥0∞) (hc : c ≠ ⊤) (f : Ω → ℝ) :
    outerLpNorm (c • Q) f 1 = c * outerLpNorm Q f 1 := by
  simp only [outerLpNorm, inv_one, ENNReal.rpow_one]
  exact outerExpectation_smul_measure Q c hc _

/-- The weighted conditioning argument converts the original relative cover
into an absolute unit-envelope cover of a localized class. Crucially, one
natural number `N` works for every probability law `Q`; this is stronger than
the insufficient pointwise assertion `∀ Q, ∃ S` with no uniform cardinality. -/
theorem localized_absoluteCover
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : Ω → ℝ≥0∞)
    (hVmeas : Measurable V) -- outer-integral majorant witness.
    (hGV : ∀ x, ENNReal.ofReal |G x| ≤ V x)
      -- outer-envelope domination by `V`.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- original relative envelope.
    (hcover : ∀ ε : ℝ, 0 < ε → uniformLpCoveringNumber F G 1 ε < ⊤)
      -- vdV 19.13 all-Q relative covering.
    (M : ℝ) (hM : 0 < M) -- positive localization level.
    : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (Q : Measure Ω),
      IsProbabilityMeasure Q → ∃ S : Finset (Ω → ℝ),
        S.card ≤ N ∧
        IsStrictFiniteLpCover (localizedClass F {x | V x ≤ ENNReal.ofReal M})
          (fun _ ↦ (1 : ℝ)) Q 1 ε S := by
  classical
  intro ε hε
  let A : Set Ω := {x | V x ≤ ENNReal.ofReal M}
  have hA : MeasurableSet A := measurableSet_Iic.preimage hVmeas
  let δ : ℝ := ε / M
  have hδ : 0 < δ := div_pos hε hM
  let K : ℕ∞ := uniformLpCoveringNumber F G 1 δ
  have hKtop : K < ⊤ := hcover δ hδ
  let N : ℕ := K.toNat + 1
  refine ⟨N, ?_⟩
  intro Q hQ
  letI : IsProbabilityMeasure Q := hQ
  by_cases hQA0 : Q A = 0
  · refine ⟨{0}, by simp [N], ?_⟩
    constructor
    · intro g hg
      simp only [Finset.mem_singleton] at hg
      subst g
      exact MemLp.zero
    · rintro _ ⟨f, hf, rfl⟩
      refine ⟨0, by simp, ?_⟩
      have hQr : Q.restrict A = 0 := Measure.restrict_eq_zero.mpr hQA0
      have hzero : outerLpNorm Q (localizedFunction A f - 0) 1 = 0 := by
        rw [sub_zero]
        change outerLpNorm Q (A.indicator f) 1 = 0
        rw [outerLpNorm_one_indicator_eq_restrict Q A hA f, hQr]
        simp only [outerLpNorm, inv_one, ENNReal.rpow_one]
        rw [show (0 : Measure Ω) = (0 : ℝ≥0∞) • Q by simp]
        exact (outerExpectation_smul_measure Q 0 ENNReal.zero_ne_top _).trans (zero_mul _)
      rw [hzero]
      have hone : outerLpNorm Q (fun _ ↦ (1 : ℝ)) 1 = 1 := by
        simp [outerLpNorm, outerExpectation_const]
      rw [hone, mul_one]
      exact ENNReal.ofReal_pos.mpr hε
  · have hQApos : 0 < Q A := pos_iff_ne_zero.mpr hQA0
    have hQAtop : Q A ≠ ⊤ := measure_ne_top Q A
    let R : Measure Ω := conditionOn Q A
    have hRprob : IsProbabilityMeasure R := conditionOn_isProbabilityMeasure Q A hA hQApos
    letI : IsProbabilityMeasure R := hRprob
    have hRA : ∀ᵐ x ∂R, x ∈ A := by
      change ∀ᵐ x ∂(Q A)⁻¹ • Q.restrict A, x ∈ A
      exact Measure.ae_smul_measure
        ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall fun _ hx ↦ hx)) _
    have hGbound : outerLpNorm R G 1 ≤ ENNReal.ofReal M := by
      simp only [outerLpNorm, inv_one, ENNReal.rpow_one]
      calc
        outerExpectation R (fun x ↦ ENNReal.ofReal |G x|)
            = outerExpectation R (A.indicator fun x ↦ ENNReal.ofReal |G x|) := by
              apply outerExpectation_congr_ae
              filter_upwards [hRA] with x hx
              simp [hx]
        _ ≤ outerExpectation R (fun _ ↦ ENNReal.ofReal M) := by
          apply outerExpectation_mono
          intro x
          by_cases hx : x ∈ A
          · simp only [Set.indicator_of_mem hx]
            exact (hGV x).trans hx
          · simp [hx]
        _ = ENNReal.ofReal M := by
          rw [outerExpectation_const, measure_univ, mul_one]
    have hRQ : Q.restrict A = Q A • R := by
      change Q.restrict A = Q A • ((Q A)⁻¹ • Q.restrict A)
      rw [smul_smul, ENNReal.mul_inv_cancel hQA0 hQAtop, one_smul]
    have hlocal_norm (k : Ω → ℝ) :
        outerLpNorm Q (localizedFunction A k) 1 = Q A * outerLpNorm R k 1 := by
      change outerLpNorm Q (A.indicator k) 1 = _
      rw [outerLpNorm_one_indicator_eq_restrict Q A hA k, hRQ,
        outerLpNorm_one_smul_measure R (Q A) hQAtop k]
    have hQA_le_one : Q A ≤ 1 := by
      calc
        Q A ≤ Q Set.univ := measure_mono (Set.subset_univ A)
        _ = 1 := measure_univ
    have hKcoe : K = (K.toNat : ℕ∞) := (ENat.coe_toNat hKtop.ne).symm
    have hNcoe : K < (N : ℕ∞) := by
      rw [hKcoe]
      exact_mod_cast Nat.lt_succ_self K.toNat
    have hscale : ENNReal.ofReal δ * ENNReal.ofReal M = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hδ.le]
      congr 1
      dsimp [δ]
      field_simp
    by_cases hGzero : outerLpNorm R G 1 = 0
    · refine ⟨{0}, by simp [N], ?_⟩
      constructor
      · intro g hg
        simp only [Finset.mem_singleton] at hg
        subst g
        exact MemLp.zero
      · rintro _ ⟨f, hf, rfl⟩
        refine ⟨0, by simp, ?_⟩
        have hfR : outerLpNorm R f 1 = 0 := by
          apply le_antisymm
          · rw [← hGzero]
            simp only [outerLpNorm, inv_one, ENNReal.rpow_one]
            apply outerExpectation_mono
            intro x
            exact ENNReal.ofReal_le_ofReal ((hEnv.2 f hf x).trans_eq
              (abs_of_nonneg (hEnv.1 x)).symm)
          · exact bot_le
        have hsub : localizedFunction A f - 0 = localizedFunction A f := sub_zero _
        rw [hsub, hlocal_norm, hfR, mul_zero]
        have hone : outerLpNorm Q (fun _ ↦ (1 : ℝ)) 1 = 1 := by
          simp [outerLpNorm, outerExpectation_const]
        rw [hone, mul_one]
        exact ENNReal.ofReal_pos.mpr hε
    · have hGpos : 0 < outerLpNorm R G 1 := pos_iff_ne_zero.mpr hGzero
      have hGtop : outerLpNorm R G 1 < ⊤ := hGbound.trans_lt ENNReal.ofReal_lt_top
      have hRadm : IsAdmissibleMeasure G 1 R := ⟨hRprob, hGpos, hGtop⟩
      have hnum_le : finiteLpCoveringNumber F G R 1 δ ≤ K := by
        dsimp [K]
        unfold uniformLpCoveringNumber
        exact le_iSup_of_le R (le_iSup_of_le hRadm le_rfl)
      have hnum_lt : finiteLpCoveringNumber F G R 1 δ < (N : ℕ∞) :=
        hnum_le.trans_lt hNcoe
      unfold finiteLpCoveringNumber at hnum_lt
      rw [iInf_lt_iff] at hnum_lt
      obtain ⟨T, hT⟩ := hnum_lt
      rw [iInf_lt_iff] at hT
      obtain ⟨hTcover, hTcard⟩ := hT
      let S : Finset (Ω → ℝ) := T.image (localizedFunction A)
      refine ⟨S, ?_, ?_⟩
      · exact (Finset.card_image_le.trans (ENat.coe_lt_coe.mp hTcard).le)
      · constructor
        · intro g hgS
          rw [Finset.mem_image] at hgS
          obtain ⟨k, hkT, rfl⟩ := hgS
          change MemLp (A.indicator k) (ENNReal.ofReal 1) Q
          rw [memLp_indicator_iff_restrict hA]
          rw [hRQ]
          exact (hTcover.1 k hkT).smul_measure hQAtop
        · rintro _ ⟨f, hf, rfl⟩
          obtain ⟨g, hgT, hfg⟩ := hTcover.2 f hf
          refine ⟨localizedFunction A g, Finset.mem_image.mpr ⟨g, hgT, rfl⟩, ?_⟩
          have hsub : localizedFunction A f - localizedFunction A g =
              localizedFunction A (f - g) := by
            funext x
            by_cases hx : x ∈ A <;> simp [localizedFunction, hx]
          rw [hsub, hlocal_norm]
          calc
            Q A * outerLpNorm R (f - g) 1
                ≤ outerLpNorm R (f - g) 1 := by
                  simpa [one_mul] using mul_le_mul_left hQA_le_one
                    (outerLpNorm R (f - g) 1)
            _ < ENNReal.ofReal δ * outerLpNorm R G 1 := hfg
            _ ≤ ENNReal.ofReal δ * ENNReal.ofReal M :=
              mul_le_mul_right hGbound _
            _ = ENNReal.ofReal ε * outerLpNorm Q (fun _ ↦ (1 : ℝ)) 1 := by
              rw [hscale]
              simp [outerLpNorm, outerExpectation_const]

private noncomputable def empiricalFiniteLaw (S : Finset Ω) : Measure Ω :=
  (S.card : ℝ≥0∞)⁻¹ • (∑ x : S, Measure.dirac (x : Ω))

private theorem empiricalFiniteLaw_isProbabilityMeasure
    (S : Finset Ω) (hS : S.Nonempty) :
    IsProbabilityMeasure (empiricalFiniteLaw S) := by
  refine ⟨?_⟩
  rw [empiricalFiniteLaw, Measure.smul_apply]
  rw [smul_eq_mul, Measure.finset_sum_apply]
  change (S.card : ℝ≥0∞)⁻¹ *
    (∑ x : S, (Measure.dirac (x : Ω)) Set.univ) = 1
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one]
  apply ENNReal.inv_mul_cancel
  · exact_mod_cast S.card_ne_zero.mpr hS
  · exact ENNReal.coe_ne_top

private theorem empiricalFiniteLaw_outerExpectation_lower
    (S : Finset Ω) (Z : Ω → ℝ≥0∞) :
    (S.card : ℝ≥0∞)⁻¹ * (∑ x : S, Z x) ≤
      outerExpectation (empiricalFiniteLaw S) Z := by
  unfold outerExpectation
  refine le_iInf fun U ↦ ?_
  rw [empiricalFiniteLaw, lintegral_smul_measure, smul_eq_mul,
    lintegral_finset_sum_measure]
  simp_rw [lintegral_dirac' _ U.2.1]
  apply mul_le_mul_right
  apply Finset.sum_le_sum
  intro x hx
  exact U.2.2 (x : Ω)

private theorem normalized_hammingMargin_lower
    {n d : ℕ} (hn : 0 < n) (γ : ℝ) (hγ : 0 < γ)
    (hd : (n : ℝ) / 4 ≤ d) :
    ENNReal.ofReal (γ / 2) ≤
      (n : ℝ≥0∞)⁻¹ * ((d : ℝ≥0∞) * ENNReal.ofReal (2 * γ)) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
  field_simp
  nlinarith

/-- A uniformly cardinal-bounded absolute `L¹` cover over every probability
law forces finite gamma dimension at every positive scale. -/
theorem allQ_absoluteCover_gammaDimension_lt_top
    (E : Set (Ω → ℝ))
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (Q : Measure Ω),
      IsProbabilityMeasure Q → ∃ S : Finset (Ω → ℝ),
        S.card ≤ N ∧
        IsStrictFiniteLpCover E (fun _ ↦ (1 : ℝ)) Q 1 ε S)
      -- absolute all-law cover with one uniform cardinal.
    : ∀ γ : ℝ, 0 < γ → gammaDimension E γ < ⊤ := by
  classical
  intro γ hγ
  by_contra hdim
  have hdimtop : gammaDimension E γ = ⊤ := top_unique (not_lt.mp hdim)
  let ε : ℝ := γ / 8
  have hε : 0 < ε := div_pos hγ (by norm_num)
  obtain ⟨N, hN⟩ := hcover ε hε
  let m : ℕ := 8 * (N + 1)
  have hm_top : (m : ℕ∞) < ⊤ := ENat.coe_lt_top m
  unfold gammaDimension at hdimtop
  obtain ⟨S, hSlarge⟩ := iSup_eq_top.mp hdimtop (m : ℕ∞) hm_top
  have hSshat : GammaShatters E γ S := by
    by_contra hnot
    simp [hnot] at hSlarge
  have hmS : m < S.card := by
    simpa [hSshat] using hSlarge
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨C, hCrate, hCdist⟩ := exists_booleanCode_halfDistance S.card
  have hq : N + 1 ≤ S.card / 8 := by
    dsimp [m] at hmS
    omega
  have hClarge : N < C.card := by
    calc
      N < 2 ^ (N + 1) := by
        exact Nat.lt_two_pow_self.trans_le
          (Nat.pow_le_pow_right (by omega) (Nat.le_succ N))
      _ ≤ 2 ^ (S.card / 8) := Nat.pow_le_pow_right (by omega) hq
      _ ≤ C.card := hCrate
  obtain ⟨threshold, hrealize⟩ := hSshat
  let e : S ≃ Fin S.card := Finset.equivFin S
  have hfun (a : Fin S.card → Bool) : ∃ f ∈ E, ∀ x : S,
      (a (e x) = true → threshold x + γ ≤ f x) ∧
      (a (e x) = false → f x ≤ threshold x - γ) :=
    hrealize (fun x ↦ a (e x))
  choose φ hφE hφmargin using hfun
  let Q : Measure Ω := empiricalFiniteLaw S
  have hQprob : IsProbabilityMeasure Q :=
    empiricalFiniteLaw_isProbabilityMeasure S hSnonempty
  obtain ⟨T, hTcard, hTcover⟩ := hN Q hQprob
  letI : IsProbabilityMeasure Q := hQprob
  have hone : outerLpNorm Q (fun _ ↦ (1 : ℝ)) 1 = 1 := by
    simp [outerLpNorm, outerExpectation_const]
  have hcenter (a : C) : ∃ g ∈ T,
      outerLpNorm Q (φ (a : Fin S.card → Bool) - g) 1 < ENNReal.ofReal ε := by
    obtain ⟨g, hgT, hg⟩ := hTcover.2 (φ (a : Fin S.card → Bool))
      (hφE (a : Fin S.card → Bool))
    refine ⟨g, hgT, ?_⟩
    simpa [hone] using hg
  choose c hcT hφc using hcenter
  let c' : C → T := fun a ↦ ⟨c a, hcT a⟩
  have hc_not_inj : ¬ Function.Injective c' := by
    intro hinj
    have hcards := Fintype.card_le_of_injective c' hinj
    simp only [Fintype.card_coe] at hcards
    omega
  obtain ⟨a, b, habc, hab⟩ := Function.not_injective_iff.mp hc_not_inj
  have hc_eq : c a = c b := congrArg Subtype.val habc
  have habfun : (a : Fin S.card → Bool) ≠ (b : Fin S.card → Bool) := by
    intro heq
    exact hab (Subtype.ext heq)
  let D : Finset (Fin S.card) :=
    Finset.univ.filter fun i ↦
      (a : Fin S.card → Bool) i ≠ (b : Fin S.card → Bool) i
  have hDcard : (S.card : ℝ) / 4 ≤ D.card := by
    simpa [D, hammingDist] using hCdist a a.property b b.property habfun
  have hpoint (i : Fin S.card) (hi : i ∈ D) :
      ENNReal.ofReal (2 * γ) ≤
        ENNReal.ofReal |φ (a : Fin S.card → Bool) (e.symm i) -
          φ (b : Fin S.card → Bool) (e.symm i)| := by
    have hne : (a : Fin S.card → Bool) i ≠ (b : Fin S.card → Bool) i := by
      simpa [D] using hi
    have ha := hφmargin (a : Fin S.card → Bool) (e.symm i)
    have hb := hφmargin (b : Fin S.card → Bool) (e.symm i)
    have hlabels :
        ((a : Fin S.card → Bool) i = true ∧
          (b : Fin S.card → Bool) i = false) ∨
        ((a : Fin S.card → Bool) i = false ∧
          (b : Fin S.card → Bool) i = true) := by
      cases hai : (a : Fin S.card → Bool) i <;>
        cases hbi : (b : Fin S.card → Bool) i <;> simp_all
    have hreal : 2 * γ ≤
        |φ (a : Fin S.card → Bool) (e.symm i) -
          φ (b : Fin S.card → Bool) (e.symm i)| := by
      rcases hlabels with ⟨hai, hbi⟩ | ⟨hai, hbi⟩
      · have hupp := ha.1 (by simpa using hai)
        have hlow := hb.2 (by simpa using hbi)
        rw [abs_of_nonneg]
        · linarith
        · linarith
      · have hlow := ha.2 (by simpa using hai)
        have hupp := hb.1 (by simpa using hbi)
        rw [abs_sub_comm, abs_of_nonneg]
        · linarith
        · linarith
    exact ENNReal.ofReal_le_ofReal hreal
  have hsum : (D.card : ℝ≥0∞) * ENNReal.ofReal (2 * γ) ≤
      ∑ x : S, ENNReal.ofReal
        |φ (a : Fin S.card → Bool) x - φ (b : Fin S.card → Bool) x| := by
    rw [← e.symm.sum_comp (fun x : S ↦ ENNReal.ofReal
      |φ (a : Fin S.card → Bool) x - φ (b : Fin S.card → Bool) x|)]
    calc
      (D.card : ℝ≥0∞) * ENNReal.ofReal (2 * γ) =
          ∑ _i ∈ D, ENNReal.ofReal (2 * γ) := by simp
      _ ≤ ∑ i ∈ D, ENNReal.ofReal
          |φ (a : Fin S.card → Bool) (e.symm i) -
            φ (b : Fin S.card → Bool) (e.symm i)| :=
        Finset.sum_le_sum fun i hi ↦ hpoint i hi
      _ ≤ ∑ i : Fin S.card, ENNReal.ofReal
          |φ (a : Fin S.card → Bool) (e.symm i) -
            φ (b : Fin S.card → Bool) (e.symm i)| := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
          (fun _ _ _ ↦ bot_le)
  have hlower : ENNReal.ofReal (γ / 2) ≤
      outerLpNorm Q
        (φ (a : Fin S.card → Bool) - φ (b : Fin S.card → Bool)) 1 := by
    have havg := normalized_hammingMargin_lower
      (Finset.card_pos.mpr hSnonempty) γ hγ hDcard
    simp only [outerLpNorm, inv_one, ENNReal.rpow_one]
    refine havg.trans ?_
    refine (mul_le_mul_right hsum _).trans ?_
    exact empiricalFiniteLaw_outerExpectation_lower S _
  have hupper : outerLpNorm Q
      (φ (a : Fin S.card → Bool) - φ (b : Fin S.card → Bool)) 1 ≤
      ENNReal.ofReal (γ / 4) := by
    have htri : outerLpNorm Q
        (φ (a : Fin S.card → Bool) - φ (b : Fin S.card → Bool)) 1 ≤
        outerLpNorm Q (φ (a : Fin S.card → Bool) - c a) 1 +
        outerLpNorm Q (φ (b : Fin S.card → Bool) - c b) 1 := by
      simp only [outerLpNorm, inv_one, ENNReal.rpow_one]
      refine (outerExpectation_mono (fun x ↦ ?_)).trans
        (outerExpectation_add_le _ _)
      simp only [Pi.sub_apply]
      rw [hc_eq]
      change ENNReal.ofReal |φ (a : Fin S.card → Bool) x -
          φ (b : Fin S.card → Bool) x| ≤
        ENNReal.ofReal |φ (a : Fin S.card → Bool) x - c b x| +
          ENNReal.ofReal |φ (b : Fin S.card → Bool) x - c b x|
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by
        simpa [abs_sub_comm] using
          (abs_sub_le (φ (a : Fin S.card → Bool) x) (c b x)
            (φ (b : Fin S.card → Bool) x)))
    refine htri.trans ?_
    calc
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε :=
        add_le_add (hφc a).le (hφc b).le
      _ = ENNReal.ofReal (γ / 4) := by
        rw [← ENNReal.ofReal_add hε.le hε.le]
        congr 1
        dsimp [ε]
        ring
  exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)))
    (hlower.trans hupper)

/-! ### Van Handel's bracketing theorem and tail expansion -/

private abbrev VHMeasSet (Ω : Type*) [MeasurableSpace Ω] :=
  {s : Set Ω // MeasurableSet s}

/-- The atom of the finite Boolean algebra generated by `I` with membership
pattern `a`.  Empty atoms are retained; this makes refinement literal. -/
private def vhCell (I : Finset (VHMeasSet Ω)) (a : I → Bool) : Set Ω :=
  ⋂ i : I, if a i then (i.1 : Set Ω) else i.1ᶜ

private theorem measurableSet_vhCell (I : Finset (VHMeasSet Ω)) (a : I → Bool) :
    MeasurableSet (vhCell I a) := by
  apply MeasurableSet.iInter
  intro i
  split_ifs
  · exact i.1.2
  · exact i.1.2.compl

private noncomputable def vhMembership (I : Finset (VHMeasSet Ω)) (x : Ω) : I → Bool := by
  classical
  exact fun i ↦ if x ∈ i.1 then true else false

private theorem mem_vhCell_membership (I : Finset (VHMeasSet Ω)) (x : Ω) :
    x ∈ vhCell I (vhMembership I x) := by
  classical
  apply Set.mem_iInter.mpr
  intro i
  dsimp [vhMembership]
  by_cases hi : x ∈ i.1
  · simp [hi]
  · simp [hi]

private theorem vhCell_subset_of_mem
    (I : Finset (VHMeasSet Ω)) (a : I → Bool) {s : VHMeasSet Ω} (hs : s ∈ I) :
    a ⟨s, hs⟩ = true → vhCell I a ⊆ s.1 := by
  intro ha x hx
  have hxi := Set.mem_iInter.mp hx ⟨s, hs⟩
  simpa [ha] using hxi

private theorem vhCell_subset_compl_of_mem
    (I : Finset (VHMeasSet Ω)) (a : I → Bool) {s : VHMeasSet Ω} (hs : s ∈ I) :
    a ⟨s, hs⟩ = false → vhCell I a ⊆ s.1ᶜ := by
  intro ha x hx
  have hxi := Set.mem_iInter.mp hx ⟨s, hs⟩
  simpa [ha] using hxi

/-- Essential finite-partition boundary of the two separated level sets of
`f`.  An atom is retained precisely when both sides have positive mass. -/
private def vhBoundary (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (α β : ℝ) : Set Ω :=
  ⋃ a : I → Bool,
    if P (vhCell I a ∩ {x | f x < α}) ≠ 0 ∧
        P (vhCell I a ∩ {x | β < f x}) ≠ 0 then
      vhCell I a else ∅

private theorem measurableSet_vhBoundary
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (α β : ℝ) :
    MeasurableSet (vhBoundary P I f α β) := by
  apply MeasurableSet.iUnion
  intro a
  split_ifs
  · exact measurableSet_vhCell I a
  · exact MeasurableSet.empty

private theorem vhCell_subset_boundary
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (α β : ℝ) (a : I → Bool)
    (hlo : P (vhCell I a ∩ {x | f x < α}) ≠ 0)
    (hhi : P (vhCell I a ∩ {x | β < f x}) ≠ 0) :
    vhCell I a ⊆ vhBoundary P I f α β := by
  intro x hx
  refine Set.mem_iUnion.mpr ⟨a, ?_⟩
  simpa [vhBoundary, hlo, hhi] using hx

private theorem boundary_cell_splits
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (α β : ℝ) (a : I → Bool)
    (hx : ∃ x ∈ vhCell I a, x ∈ vhBoundary P I f α β) :
    P (vhCell I a ∩ {x | f x < α}) ≠ 0 ∧
      P (vhCell I a ∩ {x | β < f x}) ≠ 0 := by
  rcases hx with ⟨x, hxa, hxb⟩
  simp only [vhBoundary, Set.mem_iUnion] at hxb
  rcases hxb with ⟨b, hb⟩
  split_ifs at hb with hgood
  · have hab : a = b := by
      funext i
      have hia := Set.mem_iInter.mp hxa i
      have hib := Set.mem_iInter.mp hb i
      by_cases hai : a i = true
      · have hxi : x ∈ i.1 := by simpa [hai] using hia
        by_cases hbi : b i = true
        · exact hai.trans hbi.symm
        · have : x ∈ i.1ᶜ := by simpa [hbi] using! hib
          exact (this hxi).elim
      · have hai' : a i = false := Bool.eq_false_of_not_eq_true hai
        have hxi : x ∈ i.1ᶜ := by simpa [hai'] using! hia
        by_cases hbi : b i = false
        · exact hai'.trans hbi.symm
        · have hbi' : b i = true := Bool.eq_true_of_not_eq_false hbi
          have : x ∈ i.1 := by simpa [hbi'] using hib
          exact (hxi this).elim
    simpa [hab] using hgood
  · simp at hb

private theorem vhCell_eq_of_common_mem
    (I : Finset (VHMeasSet Ω)) (a b : I → Bool) {x : Ω}
    (hxa : x ∈ vhCell I a) (hxb : x ∈ vhCell I b) : a = b := by
  funext i
  have hia := Set.mem_iInter.mp hxa i
  have hib := Set.mem_iInter.mp hxb i
  by_cases hai : a i = true
  · have hxi : x ∈ i.1 := by simpa [hai] using hia
    by_cases hbi : b i = true
    · exact hai.trans hbi.symm
    · have hbi' : b i = false := Bool.eq_false_of_not_eq_true hbi
      have : x ∈ i.1ᶜ := by simpa [hbi'] using! hib
      exact (this hxi).elim
  · have hai' : a i = false := Bool.eq_false_of_not_eq_true hai
    have hxi : x ∈ i.1ᶜ := by simpa [hai'] using! hia
    by_cases hbi : b i = false
    · exact hai'.trans hbi.symm
    · have hbi' : b i = true := Bool.eq_true_of_not_eq_false hbi
      have : x ∈ i.1 := by simpa [hbi'] using hib
      exact (hxi this).elim

private theorem vhCell_eq_membership
    (I : Finset (VHMeasSet Ω)) (a : I → Bool) {x : Ω}
    (hx : x ∈ vhCell I a) : a = vhMembership I x :=
  vhCell_eq_of_common_mem I a _ hx (mem_vhCell_membership I x)

private theorem vhBoundary_mono_refine
    (P : Measure Ω) {I J : Finset (VHMeasSet Ω)} (hIJ : I ⊆ J)
    (f : Ω → ℝ) (α β : ℝ) :
    vhBoundary P J f α β ⊆ vhBoundary P I f α β := by
  classical
  intro x hx
  let b := vhMembership J x
  have hxb : x ∈ vhCell J b := mem_vhCell_membership J x
  have hsplit := boundary_cell_splits P J f α β b ⟨x, hxb, hx⟩
  let a : I → Bool := fun i ↦ b ⟨i.1, hIJ i.2⟩
  have hsub : vhCell J b ⊆ vhCell I a := by
    intro y hy
    apply Set.mem_iInter.mpr
    intro i
    have hi := Set.mem_iInter.mp hy ⟨i.1, hIJ i.2⟩
    simpa [a] using hi
  exact (vhCell_subset_boundary P I f α β a
    (fun hz ↦ hsplit.1 (measure_mono_null
      (Set.inter_subset_inter_left _ hsub) hz))
    (fun hz ↦ hsplit.2 (measure_mono_null
      (Set.inter_subset_inter_left _ hsub) hz))) (hsub hxb)

/-- A finite family is weakly dense on `A` when one class member
simultaneously splits every positive measurable piece of `A`. -/
private def VHWeaklyDense (E : Set (Ω → ℝ)) (P : Measure Ω)
    (A : Set Ω) (α β : ℝ) : Prop :=
  MeasurableSet A ∧ P A ≠ 0 ∧
    ∀ {ι : Type} [Fintype ι] (C : ι → Set Ω),
      (∀ i, MeasurableSet (C i) ∧ C i ⊆ A ∧ P (C i) ≠ 0) →
      ∃ f ∈ E, ∀ i,
        P (C i ∩ {x | f x < α}) ≠ 0 ∧
          P (C i ∩ {x | β < f x}) ≠ 0

private def vhDualCell (A : Set Ω) {n : ℕ} (f : Fin n → Ω → ℝ)
    (label : Fin n → Bool) (α β : ℝ) : Set Ω :=
  A ∩ ⋂ i : Fin n,
    if label i then {x | β < f i x} else {x | f i x < α}

private theorem measurableSet_vhDualCell
    {A : Set Ω} (hA : MeasurableSet A) {n : ℕ} (f : Fin n → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (label : Fin n → Bool) (α β : ℝ) :
    MeasurableSet (vhDualCell A f label α β) := by
  apply hA.inter
  apply MeasurableSet.iInter
  intro i
  split_ifs
  · exact measurableSet_Ioi.preimage (hf i)
  · exact measurableSet_Iio.preimage (hf i)

omit [MeasurableSpace Ω] in
private theorem vhDualCell_zero (A : Set Ω) (f : Fin 0 → Ω → ℝ)
    (label : Fin 0 → Bool) (α β : ℝ) :
    vhDualCell A f label α β = A := by
  ext x
  simp [vhDualCell]

omit [MeasurableSpace Ω] in
private theorem vhDualCell_succ
    {n : ℕ} (A : Set Ω) (f : Fin n → Ω → ℝ) (g : Ω → ℝ)
    (label : Fin (n + 1) → Bool) (α β : ℝ) :
    vhDualCell A (Fin.lastCases g f) label α β =
      vhDualCell A f (fun i ↦ label i.castSucc) α β ∩
        (if label (Fin.last n) then {x | β < g x} else {x | g x < α}) := by
  ext x
  simp only [vhDualCell, Set.mem_inter_iff]
  constructor
  · rintro ⟨hxA, hx⟩
    have hall := Set.mem_iInter.mp hx
    refine ⟨⟨hxA, ?_⟩, ?_⟩
    · exact Set.mem_iInter.mpr fun i ↦ by simpa using hall i.castSucc
    · simpa using hall (Fin.last n)
  · rintro ⟨⟨hxA, hx⟩, hlast⟩
    refine ⟨hxA, Set.mem_iInter.mpr ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using hlast
    · simpa using Set.mem_iInter.mp hx j

/-- Iterating weak density produces a dual Boolean cube of arbitrary finite
dimension, with every cell retaining positive mass. -/
private theorem exists_dualCube_of_weaklyDense
    (E : Set (Ω → ℝ)) (P : Measure Ω) (A : Set Ω) (α β : ℝ)
    (hEmeas : ∀ f ∈ E, Measurable f)
    (hwd : VHWeaklyDense E P A α β) :
    ∀ n : ℕ, ∃ f : Fin n → Ω → ℝ,
      (∀ i, f i ∈ E) ∧
      ∀ label : Fin n → Bool, P (vhDualCell A f label α β) ≠ 0 := by
  intro n
  induction n with
  | zero =>
      let f : Fin 0 → Ω → ℝ := Fin.elim0
      refine ⟨f, (fun i ↦ Fin.elim0 i), ?_⟩
      intro label
      simpa [vhDualCell_zero] using hwd.2.1
  | succ n ih =>
      obtain ⟨f, hfE, hcells⟩ := ih
      let C : (Fin n → Bool) → Set Ω := fun label ↦ vhDualCell A f label α β
      have hC : ∀ label, MeasurableSet (C label) ∧ C label ⊆ A ∧ P (C label) ≠ 0 := by
        intro label
        have hm := measurableSet_vhDualCell hwd.1 f (fun i ↦ hEmeas _ (hfE i)) label α β
        refine ⟨hm, ?_, hcells label⟩
        intro x hx
        exact hx.1
      obtain ⟨g, hgE, hsplit⟩ := hwd.2.2 C hC
      refine ⟨Fin.lastCases g f, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa using hgE
        · simpa using hfE j
      · intro label
        rw [vhDualCell_succ]
        have hs := hsplit (fun i ↦ label i.castSucc)
        by_cases hl : label (Fin.last n) = true
        · simp only [hl, if_true]
          simpa [C] using hs.2
        · have hl' : label (Fin.last n) = false := Bool.eq_false_of_not_eq_true hl
          simp only [hl']
          simpa [C] using hs.1

/-- Weak density at two separated levels forces arbitrarily large primal
gamma-shattered carriers.  The proof uses a full dual cube indexed by the
Boolean labelings of the desired carrier. -/
private theorem gammaShatters_of_weaklyDense
    (E : Set (Ω → ℝ)) (P : Measure Ω) (A : Set Ω) (α β γ : ℝ)
    (hEmeas : ∀ f ∈ E, Measurable f)
    (hwd : VHWeaklyDense E P A α β)
    (hγ : 0 < γ)
    (hgap : 2 * γ ≤ β - α) :
    ∀ m : ℕ, ∃ S : Finset Ω, S.card = m ∧ GammaShatters E γ S := by
  classical
  intro m
  let L := Fin m → Bool
  let e : L ≃ Fin (Fintype.card L) := Fintype.equivFin L
  obtain ⟨f, hfE, hcube⟩ :=
    exists_dualCube_of_weaklyDense E P A α β hEmeas hwd (Fintype.card L)
  let φ : L → Ω → ℝ := fun b ↦ f (e b)
  let coordinateLabel : Fin m → Fin (Fintype.card L) → Bool :=
    fun i j ↦ (e.symm j) i
  have hcell_ne (i : Fin m) :
      P (vhDualCell A f (coordinateLabel i) α β) ≠ 0 := hcube _
  choose x hx using fun i ↦ nonempty_of_measure_ne_zero (hcell_ne i)
  have hxrel (i : Fin m) (b : L) :
      (b i = true → β < φ b (x i)) ∧
        (b i = false → φ b (x i) < α) := by
    have hi := Set.mem_iInter.mp (hx i).2 (e b)
    have he : (coordinateLabel i) (e b) = b i := by
      simp [coordinateLabel, e]
    rw [he] at hi
    constructor
    · intro hb
      simpa [φ, hb] using hi
    · intro hb
      simpa [φ, hb] using hi
  have hxinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    let b : L := fun k ↦ if k = i then true else false
    have hbi : b i = true := by simp [b]
    have hbj : b j = false := by simp [b, Ne.symm hne]
    have hi := (hxrel i b).1 hbi
    have hj := (hxrel j b).2 hbj
    rw [hij] at hi
    linarith
  let emb : Fin m ↪ Ω := ⟨x, hxinj⟩
  let S : Finset Ω := Finset.univ.map emb
  refine ⟨S, by simp [S], ?_⟩
  refine ⟨fun _ ↦ (α + β) / 2, ?_⟩
  intro label
  let b : L := fun i ↦ label ⟨x i, by
    exact Finset.mem_map_of_mem emb (Finset.mem_univ i)⟩
  refine ⟨φ b, hfE (e b), ?_⟩
  rintro ⟨y, hy⟩
  rw [Finset.mem_map] at hy
  rcases hy with ⟨i, _hi, rfl⟩
  have hlabel : label ⟨x i, Finset.mem_map_of_mem emb (Finset.mem_univ i)⟩ = b i := rfl
  constructor
  · intro ht
    have hhigh := (hxrel i b).1 (hlabel ▸ ht)
    dsimp only
    change (α + β) / 2 + γ ≤ φ b (x i)
    linarith
  · intro hf
    have hlow := (hxrel i b).2 (hlabel ▸ hf)
    dsimp only
    change φ b (x i) ≤ (α + β) / 2 - γ
    linarith

private theorem not_weaklyDense_of_gammaDimension
    (E : Set (Ω → ℝ)) (P : Measure Ω) (A : Set Ω) (α β γ : ℝ)
    (hEmeas : ∀ f ∈ E, Measurable f)
    (hγ : 0 < γ) (hgap : 2 * γ ≤ β - α)
    (hdim : gammaDimension E γ < ⊤) :
    ¬ VHWeaklyDense E P A α β := by
  intro hwd
  let m := ENat.toNat (gammaDimension E γ) + 1
  obtain ⟨S, hScard, hSshat⟩ :=
    gammaShatters_of_weaklyDense E P A α β γ hEmeas hwd hγ hgap m
  have hle : (S.card : ℕ∞) ≤ gammaDimension E γ := by
    unfold gammaDimension
    exact le_iSup_of_le S (by simp [hSshat])
  have heq : (ENat.toNat (gammaDimension E γ) : ℕ∞) = gammaDimension E γ :=
    ENat.coe_toNat hdim.ne
  rw [hScard, ← heq] at hle
  exact Nat.not_succ_le_self _ (ENat.coe_le_coe.mp hle)

/-- A uniform positive lower bound on all essential finite-partition
boundaries yields a weakly dense measurable support.  Banach--Alaoglu is
applied to the boundary indicators in `L²(P)` through the Hilbert-space
Riesz equivalence. -/
private theorem exists_weaklyDense_of_boundary_lower
    (E : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (α β c : ℝ) (hc : 0 < c)
    (hlower : ∀ I : Finset (VHMeasSet Ω), ∃ f ∈ E,
      c ≤ P.real (vhBoundary P I f α β)) :
    ∃ A : Set Ω, VHWeaklyDense E P A α β := by
  classical
  let J := Finset (VHMeasSet Ω)
  choose fI hfIE hfI using hlower
  let AI : J → Set Ω := fun I ↦ vhBoundary P I (fI I) α β
  have hAI (I : J) : MeasurableSet (AI I) :=
    measurableSet_vhBoundary P I (fI I) α β
  let v : J → (Ω →₂[P] ℝ) := fun I ↦
    indicatorConstLp 2 (hAI I) (measure_ne_top P _) (1 : ℝ)
  have hmeasure (I : J) : P.real (AI I) ≤ 1 := by
    calc
      P.real (AI I) ≤ P.real Set.univ := measureReal_mono (fun _ _ ↦ Set.mem_univ _)
      _ = 1 := by simp
  have hvnorm (I : J) : ‖v I‖ ≤ 1 := by
    change ‖indicatorConstLp 2 (hAI I) (measure_ne_top P _) (1 : ℝ)‖ ≤ 1
    rw [norm_indicatorConstLp (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
    norm_num only [norm_one, one_mul, ENNReal.toReal_ofNat]
    rw [← Real.sqrt_eq_rpow]
    simpa using Real.sqrt_le_sqrt (hmeasure I)
  let wI : J → WeakDual ℝ (Ω →₂[P] ℝ) := fun I ↦
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (Ω →₂[P] ℝ) (v I))
  have hwball (I : J) : wI I ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall
        (0 : StrongDual ℝ (Ω →₂[P] ℝ)) 1 := by
    change dist (WeakDual.toStrongDual (wI I)) 0 ≤ 1
    have heq : WeakDual.toStrongDual (wI I) =
        InnerProductSpace.toDual ℝ (Ω →₂[P] ℝ) (v I) := by
      rfl
    rw [heq, dist_zero_right]
    simpa using hvnorm I
  have hwfreq : ∃ᶠ I in (Filter.atTop : Filter J), wI I ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall
        (0 : StrongDual ℝ (Ω →₂[P] ℝ)) 1 :=
    (Filter.Eventually.of_forall hwball).frequently
  obtain ⟨w, hwball', hwcluster⟩ :=
    (WeakDual.isCompact_closedBall
      (0 : StrongDual ℝ (Ω →₂[P] ℝ)) 1).exists_mapClusterPt_of_frequently hwfreq
  let Hlp : Ω →₂[P] ℝ :=
    (InnerProductSpace.toDual ℝ (Ω →₂[P] ℝ)).symm (WeakDual.toStrongDual w)
  let H : Ω → ℝ := AEMeasurable.mk (fun x ↦ Hlp x) (Lp.aestronglyMeasurable Hlp).aemeasurable
  have hHmeas : Measurable H := by
    exact (Lp.aestronglyMeasurable Hlp).aemeasurable.measurable_mk
  have hHae : (fun x ↦ Hlp x) =ᵐ[P] H := by
    exact (Lp.aestronglyMeasurable Hlp).aemeasurable.ae_eq_mk
  have hHint_raw : Integrable (fun x ↦ Hlp x) P := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (integrableOn_Lp_of_measure_ne_top Hlp fact_one_le_two_ennreal.elim
        (measure_ne_top P Set.univ))
  have hHint : Integrable H P := hHint_raw.congr hHae
  have hw_eval (z : Ω →₂[P] ℝ) : w z = inner ℝ Hlp z := by
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Ω →₂[P] ℝ)).symm
  have hwI_eval (I : J) {C : Set Ω} (hC : MeasurableSet C) :
      wI I (indicatorConstLp 2 hC (measure_ne_top P C) (1 : ℝ)) =
        P.real (AI I ∩ C) := by
    simpa [wI, v] using
      (L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
        (hAI I) hC (measure_ne_top P _) (measure_ne_top P _))
  let zU : Ω →₂[P] ℝ :=
    indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P Set.univ) (1 : ℝ)
  have hwI_univ (I : J) : c ≤ wI I zU := by
    rw [hwI_eval I MeasurableSet.univ]
    simpa [AI] using hfI I
  have hw_univ : c ≤ w zU := by
    by_contra hnot
    have hopen : {u : WeakDual ℝ (Ω →₂[P] ℝ) | u zU < c} ∈ 𝓝 w :=
      (isOpen_lt (WeakDual.eval_continuous zU) continuous_const).mem_nhds
        (lt_of_not_ge hnot)
    have hf := hwcluster.frequently hopen
    have hev : ∀ᶠ I in (Filter.atTop : Filter J), ¬ wI I zU < c :=
      Filter.Eventually.of_forall fun I ↦ not_lt_of_ge (hwI_univ I)
    obtain ⟨I, hlt, hnlt⟩ := (hf.and_eventually hev).exists
    exact hnlt hlt
  have hw_univ_eq : w zU = ∫ x, H x ∂P := by
    rw [hw_eval, real_inner_comm]
    change inner ℝ zU Hlp = _
    change inner ℝ (indicatorConstLp 2 MeasurableSet.univ
      (measure_ne_top P Set.univ) (1 : ℝ)) Hlp = _
    exact (L2.inner_indicatorConstLp_one (𝕜 := ℝ) MeasurableSet.univ
      (measure_ne_top P Set.univ) Hlp).trans (by
        rw [setIntegral_univ]
        exact integral_congr_ae hHae)
  have hHpos : 0 < ∫ x, H x ∂P := lt_of_lt_of_le hc (hw_univ_eq ▸ hw_univ)
  let A : Set Ω := {x | 0 < H x}
  have hAmeas : MeasurableSet A := measurableSet_Ioi.preimage hHmeas
  have hAne : P A ≠ 0 := by
    intro hAzero
    have hnonpos : H ≤ᵐ[P] (fun _ ↦ 0) := by
      have hnot : ∀ᵐ x ∂P, x ∉ A := measure_eq_zero_iff_ae_notMem.mp hAzero
      filter_upwards [hnot] with x hx
      exact le_of_not_gt hx
    exact (not_lt_of_ge (integral_nonpos_of_ae hnonpos)) hHpos
  refine ⟨A, hAmeas, hAne, ?_⟩
  intro ι _ C hC
  have hCint (i : ι) : 0 < ∫ x in C i, H x ∂P := by
    have hnonneg : 0 ≤ᵐ[P.restrict (C i)] H :=
      (ae_restrict_mem (hC i).1).mono fun x hx ↦
        (le_of_lt ((hC i).2.1 hx))
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hHint.integrableOn).2
    have hsupp : Function.support H ∩ C i = C i := by
      ext x
      constructor
      · exact fun hx ↦ hx.2
      · intro hx
        exact ⟨ne_of_gt ((hC i).2.1 hx), hx⟩
    rw [hsupp]
    exact (pos_iff_ne_zero.mpr (hC i).2.2)
  let z : ι → (Ω →₂[P] ℝ) := fun i ↦
    indicatorConstLp 2 (hC i).1 (measure_ne_top P (C i)) (1 : ℝ)
  have hwz (i : ι) : 0 < w (z i) := by
    rw [hw_eval, real_inner_comm]
    change 0 < inner ℝ (z i) Hlp
    change 0 < inner ℝ (indicatorConstLp 2 (hC i).1
      (measure_ne_top P (C i)) (1 : ℝ)) Hlp
    have heq : inner ℝ (indicatorConstLp 2 (hC i).1
        (measure_ne_top P (C i)) (1 : ℝ)) Hlp =
        ∫ x in C i, Hlp x ∂P :=
      L2.inner_indicatorConstLp_one (𝕜 := ℝ) (hC i).1
        (measure_ne_top P (C i)) Hlp
    rw [heq]
    rw [integral_congr_ae (ae_restrict_of_ae hHae)]
    exact hCint i
  have hnhds : ∀ᶠ u in 𝓝 w, ∀ i, 0 < u (z i) := by
    rw [Filter.eventually_all]
    intro i
    exact (isOpen_lt continuous_const (WeakDual.eval_continuous (z i))).mem_nhds (hwz i)
  have hfrequent : ∃ᶠ I in (Filter.atTop : Filter J), ∀ i, 0 < wI I (z i) :=
    hwcluster.frequently hnhds
  let J0 : J := insert (⟨A, hAmeas⟩ : VHMeasSet Ω)
    (Finset.univ.image fun i ↦ (⟨C i, (hC i).1⟩ : VHMeasSet Ω))
  have htail : ∀ᶠ I in (Filter.atTop : Filter J), J0 ⊆ I := by
    rw [Filter.eventually_atTop]
    exact ⟨J0, fun _ h ↦ h⟩
  obtain ⟨I, hIw, hI0⟩ := (hfrequent.and_eventually htail).exists
  refine ⟨fI I, hfIE I, ?_⟩
  intro i
  have hCI : (⟨C i, (hC i).1⟩ : VHMeasSet Ω) ∈ I := hI0 (by
    change (⟨C i, (hC i).1⟩ : VHMeasSet Ω) ∈
      insert (⟨A, hAmeas⟩ : VHMeasSet Ω)
        (Finset.univ.image fun i ↦ (⟨C i, (hC i).1⟩ : VHMeasSet Ω))
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hAI0 : (⟨A, hAmeas⟩ : VHMeasSet Ω) ∈ I := hI0 (by
    change (⟨A, hAmeas⟩ : VHMeasSet Ω) ∈
      insert (⟨A, hAmeas⟩ : VHMeasSet Ω) _
    exact Finset.mem_insert_self _ _)
  have hboundary_inter : P (AI I ∩ C i) ≠ 0 := by
    intro hz
    have := hIw i
    rw [hwI_eval I (hC i).1, measureReal_def, hz] at this
    simp at this
  obtain ⟨x, hxAI, hxC⟩ := nonempty_of_measure_ne_zero hboundary_inter
  let a := vhMembership I x
  have hxa : x ∈ vhCell I a := mem_vhCell_membership I x
  have hsplit := boundary_cell_splits P I (fI I) α β a
    ⟨x, hxa, hxAI⟩
  have haC : vhCell I a ⊆ C i :=
    vhCell_subset_of_mem I a hCI (by simp [a, vhMembership, hxC])
  constructor
  · intro hz
    apply hsplit.1
    apply measure_mono_null _ hz
    exact Set.inter_subset_inter_left _ haC
  · intro hz
    apply hsplit.2
    apply measure_mono_null _ hz
    exact Set.inter_subset_inter_left _ haC

/-- A finite family of pointwise closed brackets that covers a skeleton also
covers its pointwise sequential closure. The proof uses the sequential form of
`IsPointwiseMeasurable`. -/
private theorem finiteBracketingCover_of_pointwiseSkeleton
    (E E₀ : Set (Ω → ℝ)) (P : Measure Ω) (ε : ℝ)
    (hdense : ∀ f ∈ E, ∃ g : ℕ → (Ω → ℝ), (∀ n, g n ∈ E₀) ∧
      ∀ x, Filter.Tendsto (fun n ↦ g n x) Filter.atTop (nhds (f x)))
    (hcov : HasFiniteBracketingCover E₀ ε 1 P) :
    HasFiniteBracketingCover E ε 1 P := by
  obtain ⟨k, l, u, hbr, hcover⟩ := hcov
  refine ⟨k, l, u, hbr, ?_⟩
  intro f hf
  obtain ⟨g, hgE₀, hg⟩ := hdense f hf
  have hall : ∀ n, ∃ i : Fin k, ∀ x, l i x ≤ g n x ∧ g n x ≤ u i x :=
    fun n ↦ hcover (g n) (hgE₀ n)
  have hfreq : ∃ᶠ n in (Filter.atTop : Filter ℕ),
      ∃ i : Fin k, ∀ x, l i x ≤ g n x ∧ g n x ≤ u i x :=
    (Filter.Eventually.of_forall hall).frequently
  rw [Filter.frequently_exists] at hfreq
  obtain ⟨i, hi⟩ := hfreq
  refine ⟨i, fun x ↦ ⟨?_, ?_⟩⟩
  · by_contra hnot
    have hfl : f x < l i x := lt_of_not_ge hnot
    have hev : ∀ᶠ n in (Filter.atTop : Filter ℕ), g n x < l i x :=
      (tendsto_order.1 (hg x)).2 _ hfl
    obtain ⟨n, hn, hnlt⟩ := (hi.and_eventually hev).exists
    exact (not_lt_of_ge (hn x).1) hnlt
  · by_contra hnot
    have huf : u i x < f x := lt_of_not_ge hnot
    have hev : ∀ᶠ n in (Filter.atTop : Filter ℕ), u i x < g n x :=
      (tendsto_order.1 (hg x)).1 _ huf
    obtain ⟨n, hn, hnlt⟩ := (hi.and_eventually hev).exists
    exact (not_lt_of_ge (hn x).2) hnlt

private theorem exists_partition_boundary_lt
    (E E₀ : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (hsub : E₀ ⊆ E) (hEmeas : ∀ f ∈ E, Measurable f)
    (α β γ c : ℝ) (hγ : 0 < γ) (hgap : 2 * γ ≤ β - α)
    (hc : 0 < c) (hdim : gammaDimension E γ < ⊤) :
    ∃ I : Finset (VHMeasSet Ω), ∀ f ∈ E₀,
      P.real (vhBoundary P I f α β) < c := by
  classical
  by_contra hnone
  push Not at hnone
  have hlower : ∀ I : Finset (VHMeasSet Ω), ∃ f ∈ E₀,
      c ≤ P.real (vhBoundary P I f α β) := by
    intro I
    obtain ⟨f, hf, hfc⟩ := hnone I
    exact ⟨f, hf, hfc⟩
  obtain ⟨A, hwd₀⟩ :=
    exists_weaklyDense_of_boundary_lower E₀ P α β c hc hlower
  have hwd : VHWeaklyDense E P A α β := by
    refine ⟨hwd₀.1, hwd₀.2.1, ?_⟩
    intro ι _ C hC
    obtain ⟨f, hf, hsplit⟩ := hwd₀.2.2 C hC
    exact ⟨f, hsub hf, hsplit⟩
  exact not_weaklyDense_of_gammaDimension E P A α β γ
    hEmeas hγ hgap hdim hwd

private theorem exists_partition_boundaries_lt
    (E E₀ : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (hsub : E₀ ⊆ E) (hEmeas : ∀ f ∈ E, Measurable f)
    (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c)
    (hdim : gammaDimension E γ < ⊤) (T : Finset ℝ) :
    ∃ I : Finset (VHMeasSet Ω), ∀ f ∈ E₀, ∀ t ∈ T,
      P.real (vhBoundary P I f t (t + 2 * γ)) < c := by
  classical
  have hone (t : ℝ) : ∃ I : Finset (VHMeasSet Ω), ∀ f ∈ E₀,
      P.real (vhBoundary P I f t (t + 2 * γ)) < c := by
    apply exists_partition_boundary_lt E E₀ P hsub hEmeas t (t + 2 * γ) γ c
      hγ (by ring_nf; exact le_rfl) hc hdim
  choose It hIt using hone
  let I : Finset (VHMeasSet Ω) := T.biUnion It
  refine ⟨I, ?_⟩
  intro f hf t ht
  have hsubIt : It t ⊆ I := by
    exact Finset.subset_biUnion_of_mem It ht
  have hset := vhBoundary_mono_refine P hsubIt f t (t + 2 * γ)
  exact (measureReal_mono hset).trans_lt (hIt t f hf)

private noncomputable def vhGridLevels (B δ : ℝ) (K : ℕ) : Finset ℝ :=
  (Finset.range K).image fun (j : ℕ) ↦ -B + (j : ℝ) * δ

private def vhBin (f : Ω → ℝ) (δ t : ℝ) : Set Ω :=
  {x | t ≤ f x ∧ f x < t + δ}

private theorem measurableSet_vhBin (f : Ω → ℝ) (hf : Measurable f) (δ t : ℝ) :
    MeasurableSet (vhBin f δ t) :=
  (measurableSet_Ici.preimage hf).inter (measurableSet_Iio.preimage hf)

private theorem exists_mem_vhGridLevels
    (B δ : ℝ) (K : ℕ) (hδ : 0 < δ)
    (hK : 2 * B / δ < K) (y : ℝ) (hy : |y| ≤ B) :
    ∃ t ∈ vhGridLevels B δ K, t ≤ y ∧ y < t + δ := by
  have hylo : -B ≤ y := (abs_le.mp hy).1
  have hyhi : y ≤ B := (abs_le.mp hy).2
  have hqnonneg : 0 ≤ (y + B) / δ := div_nonneg (by linarith) hδ.le
  let j : ℕ := ⌊(y + B) / δ⌋₊
  have hjle : (j : ℝ) ≤ (y + B) / δ := Nat.floor_le hqnonneg
  have hqK : (y + B) / δ < (K : ℝ) := by
    calc
      (y + B) / δ ≤ 2 * B / δ := by
        apply div_le_div_of_nonneg_right
        · linarith
        · exact hδ.le
      _ < (K : ℝ) := hK
  have hjKreal : (j : ℝ) < (K : ℝ) := hjle.trans_lt hqK
  have hjK : j < K := by exact_mod_cast hjKreal
  refine ⟨-B + (j : ℝ) * δ, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjK, rfl⟩
  · have := (mul_le_mul_of_nonneg_right hjle hδ.le)
    rw [div_mul_cancel₀ _ hδ.ne'] at this
    linarith
  · have hjupper : (y + B) / δ < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have := mul_lt_mul_of_pos_right hjupper hδ
    rw [div_mul_cancel₀ _ hδ.ne'] at this
    linarith

private noncomputable def vhActiveLevels
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (δ : ℝ) (levels : Finset ℝ) (a : I → Bool) : Finset ℝ :=
  levels.filter fun t ↦ P (vhCell I a ∩ vhBin f δ t) ≠ 0

private noncomputable def vhPatternLower
    (I : Finset (VHMeasSet Ω)) (B : ℝ)
    (patt : (I → Bool) → Finset ℝ) : Ω → ℝ :=
  fun x ↦ ∑ a : I → Bool, (vhCell I a).indicator
    (fun _ ↦ if ha : (patt a).Nonempty then (patt a).min' ha else -B) x

private noncomputable def vhPatternUpper
    (I : Finset (VHMeasSet Ω)) (B δ : ℝ)
    (patt : (I → Bool) → Finset ℝ) : Ω → ℝ :=
  fun x ↦ ∑ a : I → Bool, (vhCell I a).indicator
    (fun _ ↦ if ha : (patt a).Nonempty then (patt a).max' ha + δ else B) x

private theorem measurable_vhPatternLower
    (I : Finset (VHMeasSet Ω)) (B : ℝ)
    (patt : (I → Bool) → Finset ℝ) :
    Measurable (vhPatternLower I B patt) := by
  classical
  exact Finset.measurable_fun_sum Finset.univ fun a _ha ↦
    measurable_const.indicator (measurableSet_vhCell I a)

private theorem measurable_vhPatternUpper
    (I : Finset (VHMeasSet Ω)) (B δ : ℝ)
    (patt : (I → Bool) → Finset ℝ) :
    Measurable (vhPatternUpper I B δ patt) := by
  classical
  exact Finset.measurable_fun_sum Finset.univ fun a _ha ↦
    measurable_const.indicator (measurableSet_vhCell I a)

private theorem vhPatternLower_apply
    (I : Finset (VHMeasSet Ω)) (B : ℝ)
    (patt : (I → Bool) → Finset ℝ) (x : Ω) :
    vhPatternLower I B patt x =
      if ha : (patt (vhMembership I x)).Nonempty then
        (patt (vhMembership I x)).min' ha else -B := by
  classical
  unfold vhPatternLower
  rw [Finset.sum_eq_single (vhMembership I x)]
  · simp [mem_vhCell_membership]
  · intro a _ha hane
    have hnot : x ∉ vhCell I a := by
      intro hxa
      exact hane (vhCell_eq_membership I a hxa)
    simp [hnot]
  · simp

private theorem vhPatternUpper_apply
    (I : Finset (VHMeasSet Ω)) (B δ : ℝ)
    (patt : (I → Bool) → Finset ℝ) (x : Ω) :
    vhPatternUpper I B δ patt x =
      if ha : (patt (vhMembership I x)).Nonempty then
        (patt (vhMembership I x)).max' ha + δ else B := by
  classical
  unfold vhPatternUpper
  rw [Finset.sum_eq_single (vhMembership I x)]
  · simp [mem_vhCell_membership]
  · intro a _ha hane
    have hnot : x ∉ vhCell I a := by
      intro hxa
      exact hane (vhCell_eq_membership I a hxa)
    simp [hnot]
  · simp

private def vhExceptional
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (δ : ℝ) (levels : Finset ℝ) : Set Ω :=
  ⋃ a : I → Bool, ⋃ t : ↑levels,
    if P (vhCell I a ∩ vhBin f δ t.1) = 0 then
      vhCell I a ∩ vhBin f δ t.1 else ∅

private theorem measurableSet_vhExceptional
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (hf : Measurable f) (δ : ℝ) (levels : Finset ℝ) :
    MeasurableSet (vhExceptional P I f δ levels) := by
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro t
  split_ifs
  · exact (measurableSet_vhCell I a).inter (measurableSet_vhBin f hf δ t.1)
  · exact MeasurableSet.empty

private theorem measure_vhExceptional
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (δ : ℝ) (levels : Finset ℝ) :
    P (vhExceptional P I f δ levels) = 0 := by
  apply measure_iUnion_null
  intro a
  apply measure_iUnion_null
  intro t
  split_ifs with h
  · exact h
  · simp

private theorem mem_vhActiveLevels_of_not_exceptional
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (δ : ℝ) (levels : Finset ℝ) (x : Ω) (t : ℝ)
    (ht : t ∈ levels) (hbin : x ∈ vhBin f δ t)
    (hx : x ∉ vhExceptional P I f δ levels) :
    t ∈ vhActiveLevels P I f δ levels (vhMembership I x) := by
  classical
  rw [vhActiveLevels, Finset.mem_filter]
  refine ⟨ht, ?_⟩
  intro hzero
  apply hx
  refine Set.mem_iUnion.mpr ⟨vhMembership I x, ?_⟩
  refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
  simp [hzero, mem_vhCell_membership I x, hbin]

private def vhBoundaryUnion
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (γ : ℝ) (T : Finset ℝ) : Set Ω :=
  ⋃ t : ↑T, vhBoundary P I f t.1 (t.1 + 2 * γ)

private theorem measurableSet_vhBoundaryUnion
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (γ : ℝ) (T : Finset ℝ) :
    MeasurableSet (vhBoundaryUnion P I f γ T) := by
  apply MeasurableSet.iUnion
  intro t
  exact measurableSet_vhBoundary P I f t.1 (t.1 + 2 * γ)

private theorem measureReal_vhBoundaryUnion_lt
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (γ c : ℝ) (T : Finset ℝ)
    (hc : ∀ t ∈ T, P.real (vhBoundary P I f t (t + 2 * γ)) < c)
    (hcpos : 0 < c) :
    P.real (vhBoundaryUnion P I f γ T) < ((T.card : ℝ) + 1) * c := by
  calc
    P.real (vhBoundaryUnion P I f γ T) ≤
        ∑ t : ↑T, P.real (vhBoundary P I f t.1 (t.1 + 2 * γ)) := by
      exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ _t : ↑T, c := by
      exact Finset.sum_le_sum fun t _ ↦ (hc t.1 t.2).le
    _ = (T.card : ℝ) * c := by simp
    _ < ((T.card : ℝ) + 1) * c := by nlinarith

private theorem activeLevels_nonempty_of_not_exceptional
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (B δ : ℝ) (K : ℕ)
    (hδ : 0 < δ) (hK : 2 * B / δ < K)
    (hfB : ∀ x, |f x| ≤ B) (x : Ω)
    (hx : x ∉ vhExceptional P I f δ (vhGridLevels B δ K)) :
    (vhActiveLevels P I f δ (vhGridLevels B δ K)
      (vhMembership I x)).Nonempty := by
  obtain ⟨t, ht, htlo, hthi⟩ := exists_mem_vhGridLevels B δ K hδ hK (f x) (hfB x)
  exact ⟨t, mem_vhActiveLevels_of_not_exceptional P I f δ
    (vhGridLevels B δ K) x t ht ⟨htlo, hthi⟩ hx⟩

private theorem activePattern_contains_of_not_exceptional
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (B δ : ℝ) (K : ℕ)
    (hδ : 0 < δ) (hK : 2 * B / δ < K)
    (hfB : ∀ x, |f x| ≤ B) (x : Ω)
    (hx : x ∉ vhExceptional P I f δ (vhGridLevels B δ K)) :
    vhPatternLower I B
        (vhActiveLevels P I f δ (vhGridLevels B δ K)) x ≤ f x ∧
      f x ≤ vhPatternUpper I B δ
        (vhActiveLevels P I f δ (vhGridLevels B δ K)) x := by
  obtain ⟨t, ht, htlo, hthi⟩ := exists_mem_vhGridLevels B δ K hδ hK (f x) (hfB x)
  have htact := mem_vhActiveLevels_of_not_exceptional P I f δ
    (vhGridLevels B δ K) x t ht ⟨htlo, hthi⟩ hx
  have hne := activeLevels_nonempty_of_not_exceptional P I f B δ K hδ hK hfB x hx
  rw [vhPatternLower_apply, vhPatternUpper_apply]
  simp only [hne, dite_true]
  exact ⟨(Finset.min'_le _ t htact).trans htlo,
    hthi.le.trans (by simpa [add_comm] using
      (add_le_add_right (Finset.le_max' _ t htact) δ))⟩

private theorem activePattern_width_le_global
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (B δ : ℝ) (K : ℕ)
    (hδ : 0 < δ) (hK : 2 * B / δ < K)
    (hfB : ∀ x, |f x| ≤ B) (x : Ω)
    (hx : x ∉ vhExceptional P I f δ (vhGridLevels B δ K)) :
    vhPatternUpper I B δ
        (vhActiveLevels P I f δ (vhGridLevels B δ K)) x -
      vhPatternLower I B
        (vhActiveLevels P I f δ (vhGridLevels B δ K)) x ≤
      ((K : ℝ) + 1) * δ := by
  classical
  let s := vhActiveLevels P I f δ (vhGridLevels B δ K) (vhMembership I x)
  have hs : s.Nonempty :=
    activeLevels_nonempty_of_not_exceptional P I f B δ K hδ hK hfB x hx
  rw [vhPatternUpper_apply, vhPatternLower_apply]
  rw [dif_pos hs, dif_pos hs]
  have hminlevel : s.min' hs ∈ vhGridLevels B δ K :=
    (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
  have hmaxlevel : s.max' hs ∈ vhGridLevels B δ K :=
    (Finset.mem_filter.mp (Finset.max'_mem _ _)).1
  obtain ⟨jmin, hjmin, hmin⟩ := Finset.mem_image.mp hminlevel
  obtain ⟨jmax, hjmax, hmax⟩ := Finset.mem_image.mp hmaxlevel
  have hjmin0 : (0 : ℝ) ≤ jmin := by positivity
  have hjmaxK : (jmax : ℝ) < K := by exact_mod_cast Finset.mem_range.mp hjmax
  rw [← hmin, ← hmax]
  nlinarith

private theorem activePattern_width_le_off_boundary
    (P : Measure Ω) (I : Finset (VHMeasSet Ω))
    (f : Ω → ℝ) (B δ γ : ℝ) (K : ℕ)
    (hδ : 0 < δ) (hK : 2 * B / δ < K)
    (hfB : ∀ x, |f x| ≤ B) (x : Ω)
    (hxN : x ∉ vhExceptional P I f δ (vhGridLevels B δ K))
    (hxXi : x ∉ vhBoundaryUnion P I f γ
      ((vhGridLevels B δ K).image fun t ↦ t + δ)) :
    vhPatternUpper I B δ
        (vhActiveLevels P I f δ (vhGridLevels B δ K)) x -
      vhPatternLower I B
        (vhActiveLevels P I f δ (vhGridLevels B δ K)) x ≤
      2 * γ + 3 * δ := by
  classical
  let s := vhActiveLevels P I f δ (vhGridLevels B δ K) (vhMembership I x)
  have hs : s.Nonempty :=
    activeLevels_nonempty_of_not_exceptional P I f B δ K hδ hK hfB x hxN
  rw [vhPatternUpper_apply, vhPatternLower_apply]
  rw [dif_pos hs, dif_pos hs]
  by_contra hnot
  have hwide : 2 * γ + 3 * δ < s.max' hs + δ - s.min' hs := lt_of_not_ge hnot
  have hsep : s.min' hs + δ + 2 * γ < s.max' hs := by linarith
  have hminact : s.min' hs ∈ s := Finset.min'_mem _ _
  have hmaxact : s.max' hs ∈ s := Finset.max'_mem _ _
  have hminlevel : s.min' hs ∈ vhGridLevels B δ K :=
    (Finset.mem_filter.mp hminact).1
  have htT : s.min' hs + δ ∈
      (vhGridLevels B δ K).image (fun t ↦ t + δ) :=
    Finset.mem_image.mpr ⟨s.min' hs, hminlevel, rfl⟩
  have hlo : P (vhCell I (vhMembership I x) ∩
      {y | f y < s.min' hs + δ}) ≠ 0 := by
    have hact := (Finset.mem_filter.mp hminact).2
    intro hz
    apply hact
    apply measure_mono_null _ hz
    intro y hy
    exact ⟨hy.1, hy.2.2⟩
  have hhi : P (vhCell I (vhMembership I x) ∩
      {y | s.min' hs + δ + 2 * γ < f y}) ≠ 0 := by
    have hact := (Finset.mem_filter.mp hmaxact).2
    intro hz
    apply hact
    apply measure_mono_null _ hz
    intro y hy
    exact ⟨hy.1, hsep.trans_le hy.2.1⟩
  apply hxXi
  refine Set.mem_iUnion.mpr ⟨⟨s.min' hs + δ, htT⟩, ?_⟩
  exact vhCell_subset_boundary P I f (s.min' hs + δ)
    ((s.min' hs + δ) + 2 * γ) (vhMembership I x) hlo hhi
      (mem_vhCell_membership I x)

private noncomputable def vhCorrectedLower
    (N : Set Ω) (I : Finset (VHMeasSet Ω)) (B : ℝ)
    (patt : (I → Bool) → Finset ℝ) : Ω → ℝ := by
  classical
  exact fun x ↦ if x ∈ N then -B else vhPatternLower I B patt x

private noncomputable def vhCorrectedUpper
    (N : Set Ω) (I : Finset (VHMeasSet Ω)) (B δ : ℝ)
    (patt : (I → Bool) → Finset ℝ) : Ω → ℝ := by
  classical
  exact fun x ↦ if x ∈ N then B else vhPatternUpper I B δ patt x

private theorem measurable_vhCorrectedLower
    (N : Set Ω) (hN : MeasurableSet N) (I : Finset (VHMeasSet Ω)) (B : ℝ)
    (patt : (I → Bool) → Finset ℝ) :
    Measurable (vhCorrectedLower N I B patt) := by
  exact Measurable.piecewise hN measurable_const (measurable_vhPatternLower I B patt)

private theorem measurable_vhCorrectedUpper
    (N : Set Ω) (hN : MeasurableSet N) (I : Finset (VHMeasSet Ω)) (B δ : ℝ)
    (patt : (I → Bool) → Finset ℝ) :
    Measurable (vhCorrectedUpper N I B δ patt) := by
  exact Measurable.piecewise hN measurable_const (measurable_vhPatternUpper I B δ patt)

private theorem activePattern_corrected_isEpsBracket
    (P : Measure Ω) [IsProbabilityMeasure P]
    (I : Finset (VHMeasSet Ω)) (f : Ω → ℝ)
    (B δ γ ε m : ℝ) (K : ℕ) (N : Set Ω)
    (hB : 0 ≤ B) (hδ : 0 < δ) (hγ : 0 ≤ γ)
    (hK : 2 * B / δ < K) (hfB : ∀ x, |f x| ≤ B)
    (hNmeas : MeasurableSet N) (hNzero : P N = 0)
    (hexc : vhExceptional P I f δ (vhGridLevels B δ K) ⊆ N)
    (hXi : P.real (vhBoundaryUnion P I f γ
      ((vhGridLevels B δ K).image fun t ↦ t + δ)) < m)
    (hm : 0 ≤ m)
    (hsize : 2 * γ + 3 * δ + (((K : ℝ) + 1) * δ) * m < ε) :
    IsEpsBracket ε
      (vhCorrectedLower N I B
        (vhActiveLevels P I f δ (vhGridLevels B δ K)))
      (vhCorrectedUpper N I B δ
        (vhActiveLevels P I f δ (vhGridLevels B δ K))) 1 P := by
  classical
  let patt := vhActiveLevels P I f δ (vhGridLevels B δ K)
  let l := vhCorrectedLower N I B patt
  let u := vhCorrectedUpper N I B δ patt
  let Xi := vhBoundaryUnion P I f γ
    ((vhGridLevels B δ K).image fun t ↦ t + δ)
  let good := 2 * γ + 3 * δ
  let C := ((K : ℝ) + 1) * δ
  have hC : 0 ≤ C := mul_nonneg (by positivity) hδ.le
  have hgood : 0 ≤ good := by dsimp [good]; positivity
  have hεpos : 0 < ε :=
    lt_of_le_of_lt (add_nonneg hgood (mul_nonneg hC hm)) hsize
  have hout (x : Ω) (hx : x ∉ N) :
      vhPatternLower I B patt x ≤ f x ∧
        f x ≤ vhPatternUpper I B δ patt x := by
    apply activePattern_contains_of_not_exceptional P I f B δ K hδ hK hfB
    exact fun hxe ↦ hx (hexc hxe)
  have hbracket : IsBracket l u := by
    intro x
    by_cases hx : x ∈ N
    · simp [l, u, vhCorrectedLower, vhCorrectedUpper, hx, hB]
    · simpa [l, u, vhCorrectedLower, vhCorrectedUpper, hx] using
        (hout x hx).1.trans (hout x hx).2
  have hlmeas : Measurable l := measurable_vhCorrectedLower N hNmeas I B patt
  have humeas : Measurable u := measurable_vhCorrectedUpper N hNmeas I B δ patt
  have hwidth_global (x : Ω) (hx : x ∉ N) : u x - l x ≤ C := by
    simp only [l, u, vhCorrectedLower, vhCorrectedUpper, hx, if_false]
    exact activePattern_width_le_global P I f B δ K hδ hK hfB x
      (fun hxe ↦ hx (hexc hxe))
  have hlbound : ∀ x, |l x| ≤ B + C := by
    intro x
    by_cases hx : x ∈ N
    · simp only [l, vhCorrectedLower, hx, if_true, abs_neg]
      rw [abs_of_nonneg hB]
      linarith
    · have ho := hout x hx
      have hw := hwidth_global x hx
      have hlow : f x - C ≤ l x := by
        have hfu : f x ≤ u x := by
          simpa [u, vhCorrectedUpper, hx] using ho.2
        linarith
      have hhigh : l x ≤ f x := by
        simpa [l, vhCorrectedLower, hx] using ho.1
      rw [abs_le]
      constructor <;> linarith [(abs_le.mp (hfB x)).1, (abs_le.mp (hfB x)).2]
  have hubound : ∀ x, |u x| ≤ B + C := by
    intro x
    by_cases hx : x ∈ N
    · simp only [u, vhCorrectedUpper, hx, if_true]
      rw [abs_of_nonneg hB]
      linarith
    · have ho := hout x hx
      have hw := hwidth_global x hx
      have hlow : f x ≤ u x := by
        simpa [u, vhCorrectedUpper, hx] using ho.2
      have hhigh : u x ≤ f x + C := by
        have hlf : l x ≤ f x := by
          simpa [l, vhCorrectedLower, hx] using ho.1
        linarith
      rw [abs_le]
      constructor <;> linarith [(abs_le.mp (hfB x)).1, (abs_le.mp (hfB x)).2]
  have hlLp : MemLp l 1 P := MemLp.of_bound hlmeas.aestronglyMeasurable (B + C)
    (Filter.Eventually.of_forall fun x ↦ by simpa using hlbound x)
  have huLp : MemLp u 1 P := MemLp.of_bound humeas.aestronglyMeasurable (B + C)
    (Filter.Eventually.of_forall fun x ↦ by simpa using hubound x)
  refine ⟨hbracket, hlmeas, humeas, hlLp, huLp, ?_⟩
  have hXimeas : MeasurableSet Xi := by
    dsimp [Xi]
    exact measurableSet_vhBoundaryUnion P I f γ
      ((vhGridLevels B δ K).image fun t ↦ t + δ)
  have hmono : ∀ᵐ x ∂P, ‖u x - l x‖ ≤
      ‖good + Xi.indicator (fun _ ↦ C) x‖ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNzero] with x hxN
    have hnonneg : 0 ≤ u x - l x := sub_nonneg.mpr (hbracket x)
    by_cases hxXi : x ∈ Xi
    · have hw := hwidth_global x hxN
      simp only [Xi, Set.indicator_of_mem hxXi, Real.norm_eq_abs,
        abs_of_nonneg hnonneg, abs_of_nonneg (add_nonneg hgood hC)]
      linarith
    · have hw : u x - l x ≤ good := by
        simpa [u, l, patt, good, vhCorrectedUpper, vhCorrectedLower, hxN] using
          activePattern_width_le_off_boundary P I f B δ γ K hδ hK hfB x
            (fun hxe ↦ hxN (hexc hxe)) hxXi
      simp only [Xi, Set.indicator_of_notMem hxXi, add_zero, Real.norm_eq_abs,
        abs_of_nonneg hnonneg, abs_of_nonneg hgood]
      exact hw
  calc
    eLpNorm (fun x ↦ u x - l x) 1 P ≤
        eLpNorm (fun x ↦ good + Xi.indicator (fun _ ↦ C) x) 1 P :=
      eLpNorm_mono_ae hmono
    _ ≤ eLpNorm (fun _ : Ω ↦ good) 1 P +
        eLpNorm (Xi.indicator fun _ ↦ C) 1 P := by
      simpa only [Pi.add_apply] using!
        (eLpNorm_add_le (p := (1 : ℝ≥0∞)) (μ := P)
          measurable_const.aestronglyMeasurable
          (measurable_const.indicator hXimeas).aestronglyMeasurable le_rfl)
    _ = ENNReal.ofReal good + ENNReal.ofReal C * P Xi := by
      have hconst : eLpNorm (fun _ : Ω ↦ good) 1 P = ENNReal.ofReal good := by
        rw [eLpNorm_const good (by norm_num) (NeZero.ne P)]
        simp only [measure_univ, ENNReal.one_rpow, mul_one]
        exact Real.enorm_eq_ofReal hgood
      have hind : eLpNorm (Xi.indicator fun _ ↦ C) 1 P =
          ENNReal.ofReal C * P Xi := by
        rw [eLpNorm_indicator_const hXimeas (by norm_num) (by norm_num)]
        norm_num only [ENNReal.toReal_one, one_div, ENNReal.rpow_one]
        rw [Real.enorm_eq_ofReal hC]
      rw [hconst, hind]
    _ < ENNReal.ofReal ε := by
      rw [← ofReal_measureReal (measure_ne_top P Xi),
        ← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_add hgood (mul_nonneg hC measureReal_nonneg)]
      exact (ENNReal.ofReal_lt_ofReal_iff hεpos).mpr (by nlinarith [hXi])

/-- Van Handel's finite-bracketing theorem on an arbitrary measurable
space: a measurable, pointwise-measurable, uniformly bounded class with finite
gamma dimension at every positive scale has finite `L¹(P)` bracketing covers.
No standard-Borel or countable-generation assumption is imposed. -/
theorem finiteBracketing_of_gammaDimension
    (E : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ)
    (hEmeas : ∀ f ∈ E, Measurable f) -- measurable class members.
    (hPM : IsPointwiseMeasurable E) -- suitable measurability.
    (hbdd : ∀ f ∈ E, ∀ x, |f x| ≤ B) -- localized uniform bound.
    (hdim : ∀ γ : ℝ, 0 < γ → gammaDimension E γ < ⊤)
      -- The gamma-dimension bound holds at every positive scale.
    : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover E ε 1 P := by
  classical
  intro ε hε
  by_cases hE : E = ∅
  · subst E
    exact HasFiniteBracketingCover.empty ε 1 P
  let B₀ : ℝ := max B 0
  have hB₀ : 0 ≤ B₀ := by simp [B₀]
  have hbdd₀ : ∀ f ∈ E, ∀ x, |f x| ≤ B₀ := by
    intro f hf x
    exact (hbdd f hf x).trans (le_max_left _ _)
  obtain ⟨E₀, hE₀count, hE₀sub, hE₀dense⟩ := hPM
  let γ : ℝ := ε / 8
  let δ : ℝ := ε / 16
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * B₀ / δ)
  let levels := vhGridLevels B₀ δ K
  let T : Finset ℝ := levels.image fun t ↦ t + δ
  let C : ℝ := ((K : ℝ) + 1) * δ
  have hC : 0 < C := by dsimp [C]; positivity
  let m : ℝ := ε / (4 * C)
  have hm : 0 < m := by dsimp [m]; positivity
  let c : ℝ := m / (2 * ((T.card : ℝ) + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨I, hI⟩ := exists_partition_boundaries_lt E E₀ P hE₀sub hEmeas
    γ c hγ hc (hdim γ hγ) T
  letI : Countable (↑E₀) := hE₀count
  let N : Set Ω := ⋃ f : ↑E₀, vhExceptional P I f.1 δ levels
  have hNmeas : MeasurableSet N := by
    apply MeasurableSet.iUnion
    intro f
    exact measurableSet_vhExceptional P I f.1 (hEmeas f.1 (hE₀sub f.2)) δ levels
  have hNzero : P N = 0 := by
    apply measure_iUnion_null
    intro f
    exact measure_vhExceptional P I f.1 δ levels
  have hexc (f : Ω → ℝ) (hf : f ∈ E₀) :
      vhExceptional P I f δ levels ⊆ N := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hx⟩
  have hXi (f : Ω → ℝ) (hf : f ∈ E₀) :
      P.real (vhBoundaryUnion P I f γ T) < m := by
    have hraw := measureReal_vhBoundaryUnion_lt P I f γ c T
      (hI f hf) hc
    have heq : ((T.card : ℝ) + 1) * c = m / 2 := by
      dsimp [c]
      field_simp
    rw [heq] at hraw
    exact hraw.trans (by linarith)
  have hsize : 2 * γ + 3 * δ + C * m < ε := by
    dsimp [γ, δ, m]
    field_simp [hC.ne']
    nlinarith
  let Choices := ↑(levels.powerset)
  let Pattern := (I → Bool) → Choices
  let patternFinset : Pattern → (I → Bool) → Finset ℝ :=
    fun patt a ↦ (patt a).1
  let L : Pattern → Ω → ℝ := fun patt ↦
    vhCorrectedLower N I B₀ (patternFinset patt)
  let U : Pattern → Ω → ℝ := fun patt ↦
    vhCorrectedUpper N I B₀ δ (patternFinset patt)
  let Good := {patt : Pattern // IsEpsBracket ε (L patt) (U patt) 1 P}
  letI : Fintype Good := Fintype.ofFinite Good
  let e : Good ≃ Fin (Fintype.card Good) := Fintype.equivFin Good
  have hcover₀ : HasFiniteBracketingCover E₀ ε 1 P := by
    refine ⟨Fintype.card Good, fun i ↦ L (e.symm i).1,
      fun i ↦ U (e.symm i).1, ?_, ?_⟩
    · intro i
      exact (e.symm i).2
    · intro f hf
      let patt : Pattern := fun a ↦ ⟨vhActiveLevels P I f δ levels a,
        Finset.mem_powerset.mpr (fun t ht ↦ (Finset.mem_filter.mp ht).1)⟩
      have hpatt : patternFinset patt = vhActiveLevels P I f δ levels := by
        rfl
      have hT : (levels.image fun t ↦ t + δ) = T := rfl
      have hbr : IsEpsBracket ε (L patt) (U patt) 1 P := by
        dsimp [L, U]
        rw [hpatt]
        apply activePattern_corrected_isEpsBracket P I f B₀ δ γ ε m K N
          hB₀ hδ hγ.le hK (hbdd₀ f (hE₀sub hf))
          hNmeas hNzero
        · simpa [levels] using hexc f hf
        · simpa [levels, T] using hXi f hf
        · exact hm.le
        · simpa [C] using hsize
      let q : Good := ⟨patt, hbr⟩
      refine ⟨e q, ?_⟩
      intro x
      have heinv : (e.symm (e q)).1 = patt := by simp [q]
      change L (e.symm (e q)).1 x ≤ f x ∧ f x ≤ U (e.symm (e q)).1 x
      rw [heinv]
      by_cases hx : x ∈ N
      · simp only [L, U, vhCorrectedLower, vhCorrectedUpper, hx, if_true]
        exact ⟨(abs_le.mp (hbdd₀ f (hE₀sub hf) x)).1,
          (abs_le.mp (hbdd₀ f (hE₀sub hf) x)).2⟩
      · simp only [L, U, vhCorrectedLower, vhCorrectedUpper, hx, if_false]
        rw [hpatt]
        apply activePattern_contains_of_not_exceptional P I f B₀ δ K hδ hK
          (hbdd₀ f (hE₀sub hf)) x
        exact fun hxe ↦ hx (hexc f hf hxe)
  exact finiteBracketingCover_of_pointwiseSkeleton E E₀ P ε hE₀dense hcover₀

/-- Real-valued measurable envelope tail on the region where the outer
majorant `V` exceeds level `M`.

Edge behavior: for nonpositive `M` the same indicator formula is used; all
book-facing consumers choose `0 < M`. -/
noncomputable def tailReal (V : Ω → ℝ≥0∞) (H : Ω → ℝ) (M : ℝ) : Ω → ℝ :=
  {x | ENNReal.ofReal M < V x}.indicator H

/-- An integrable measurable nonnegative envelope has arbitrarily small
`L¹(P)` tail above a positive level. -/
theorem tailReal_small
    (V : Ω → ℝ≥0∞) (H : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (hVmeas : Measurable V) -- outer-integral majorant witness.
    (hVint : (∫⁻ x, V x ∂P) < ⊤) -- finite majorant integral.
    (hHV : ∀ x, ENNReal.ofReal |H x| ≤ V x)
      -- real envelope dominated by `V`.
    (ε : ℝ) (hε : 0 < ε) -- target tail radius.
    : ∃ M : ℝ, 0 < M ∧
      eLpNorm (tailReal V H M) 1 P < ENNReal.ofReal ε := by
  let s : ℕ → Set Ω := fun n ↦ {x | (n : ℝ≥0∞) < V x}
  have hs_meas : ∀ n, MeasurableSet (s n) := by
    intro n
    exact measurableSet_Ioi.preimage hVmeas
  have hs_anti : Antitone s := by
    intro n m hnm x hx
    change (n : ℝ≥0∞) < V x
    change (m : ℝ≥0∞) < V x at hx
    exact lt_of_le_of_lt (by exact_mod_cast hnm) hx
  have hs_inter : ⋂ n, s n = {x | V x = ⊤} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      apply top_unique
      rw [← ENNReal.iSup_natCast]
      exact iSup_le fun n ↦ (hx n).le
    · rintro hx n
      change (n : ℝ≥0∞) < V x
      rw [hx]
      exact ENNReal.coe_lt_top
  have hV_top : P {x | V x = ⊤} = 0 :=
    measure_eq_top_of_lintegral_ne_top hVmeas.aemeasurable hVint.ne
  have hs_measure : Filter.Tendsto (P ∘ s) Filter.atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (μ := P) (fun n ↦ (hs_meas n).nullMeasurableSet) hs_anti
      ⟨0, measure_ne_top P (s 0)⟩
    rw [hs_inter, hV_top] at h
    exact h
  have hs_integral : Filter.Tendsto (fun n ↦ ∫⁻ x in s n, V x ∂P)
      Filter.atTop (𝓝 0) :=
    tendsto_setLIntegral_zero hVint.ne hs_measure
  obtain ⟨n, hn⟩ : ∃ n, (∫⁻ x in s n, V x ∂P) < ENNReal.ofReal ε :=
    ((tendsto_order.1 hs_integral).2 (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.mpr hε)).exists
  refine ⟨(n + 1 : ℕ), by positivity, ?_⟩
  have hset : {x | ENNReal.ofReal (n + 1 : ℕ) < V x} ⊆ s n := by
    intro x hx
    change (n : ℝ≥0∞) < V x
    exact lt_of_le_of_lt (by
      rw [ENNReal.ofReal_natCast]
      exact_mod_cast Nat.le_add_right n 1) hx
  have htailset : {x | ENNReal.ofReal (n + 1 : ℕ) < V x} = s (n + 1) := by
    ext x
    change ENNReal.ofReal ((n + 1 : ℕ) : ℝ) < V x ↔ ((n + 1 : ℕ) : ℝ≥0∞) < V x
    rw [ENNReal.ofReal_natCast]
  calc
    eLpNorm (tailReal V H (n + 1 : ℕ)) 1 P
        = ∫⁻ x, ‖tailReal V H (n + 1 : ℕ) x‖ₑ ∂P :=
          eLpNorm_one_eq_lintegral_enorm
    _ ≤ ∫⁻ x in {x | ENNReal.ofReal (n + 1 : ℕ) < V x}, V x ∂P := by
      rw [htailset, ← lintegral_indicator (hs_meas (n + 1))]
      refine lintegral_mono fun x ↦ ?_
      by_cases hx : x ∈ s (n + 1)
      · have hx' : x ∈ {x | ENNReal.ofReal (n + 1 : ℕ) < V x} := by
          rw [htailset]
          exact hx
        simpa only [tailReal, Set.indicator_of_mem hx', Set.indicator_of_mem hx,
          Real.enorm_eq_ofReal_abs] using hHV x
      · have hx' : x ∉ {x | ENNReal.ofReal (n + 1 : ℕ) < V x} := by
          rw [htailset]
          exact hx
        have htail : ¬ ENNReal.ofReal ((n : ℝ) + 1) < V x := by
          intro hbad
          apply hx
          change ((n + 1 : ℕ) : ℝ≥0∞) < V x
          rw [← ENNReal.ofReal_natCast]
          norm_num at hbad ⊢
          exact hbad
        simp [tailReal, hx, htail]
    _ ≤ ∫⁻ x in s n, V x ∂P := by
      exact lintegral_mono' (Measure.restrict_mono hset le_rfl) (fun _ ↦ le_rfl)
    _ < ENNReal.ofReal ε := hn

/-- Expand brackets for the localization on `{V ≤ M}` by the measurable
tail `tailReal V H M`, obtaining pointwise brackets for the original class. -/
theorem expand_localized_bracketingCover
    (F : Set (Ω → ℝ)) (V : Ω → ℝ≥0∞) (H : Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (M δ η : ℝ)
    (hVmeas : Measurable V) -- outer-integral majorant witness.
    (hHmeas : Measurable H) -- measurable real envelope.
    (hHenv : UniformEntropyStructural.IsEnvelope F H)
      -- real majorant envelope property.
    (hδ : 0 < δ) -- positive localized bracket radius.
    (hη : 0 < η) -- positive tail radius.
    (htail : eLpNorm (tailReal V H M) 1 P < ENNReal.ofReal η)
      -- The tail has `L¹(P)` norm less than `η`.
    (hloc : HasFiniteBracketingCover
      (localizedClass F {x | V x ≤ ENNReal.ofReal M}) δ 1 P)
      -- The localized class has a finite bracketing cover.
    : HasFiniteBracketingCover F (δ + 2 * η) 1 P := by
  obtain ⟨k, l, u, hbr, hcov⟩ := hloc
  let t : Ω → ℝ := tailReal V H M
  have ht_meas : Measurable t := by
    exact hHmeas.indicator (measurableSet_Ioi.preimage hVmeas)
  have ht_nonneg : ∀ x, 0 ≤ t x := by
    intro x
    by_cases hx : ENNReal.ofReal M < V x
    · simpa [t, tailReal, hx] using hHenv.1 x
    · simp [t, tailReal, hx]
  have ht_mem : MemLp t 1 P := by
    refine ⟨ht_meas.aestronglyMeasurable, ?_⟩
    exact htail.trans (ENNReal.ofReal_lt_top.trans_le le_top)
  let l' : Fin k → Ω → ℝ := fun i x ↦ l i x - t x
  let u' : Fin k → Ω → ℝ := fun i x ↦ u i x + t x
  refine ⟨k, l', u', ?_, ?_⟩
  · intro i
    have hli_meas : Measurable (l i) := (hbr i).measurable_lower
    have hui_meas : Measurable (u i) := (hbr i).measurable_upper
    have hli_mem : MemLp (l i) 1 P := (hbr i).memLp_lower
    have hui_mem : MemLp (u i) 1 P := (hbr i).memLp_upper
    refine ⟨?_, hli_meas.sub ht_meas, hui_meas.add ht_meas,
      hli_mem.sub ht_mem, hui_mem.add ht_mem, ?_⟩
    · intro x
      dsimp [l', u']
      linarith [(hbr i).isBracket x, ht_nonneg x]
    · have hdiff : (fun x ↦ u' i x - l' i x) =
          (fun x ↦ u i x - l i x) + (2 • t) := by
        funext x
        simp [l', u', Pi.add_apply]
        ring
      rw [hdiff]
      calc
        eLpNorm ((fun x ↦ u i x - l i x) + (2 • t)) 1 P
            ≤ eLpNorm (fun x ↦ u i x - l i x) 1 P + eLpNorm (2 • t) 1 P :=
          eLpNorm_add_le (hui_meas.sub hli_meas).aestronglyMeasurable
            (ht_meas.aestronglyMeasurable.const_smul 2) le_rfl
        _ = eLpNorm (fun x ↦ u i x - l i x) 1 P +
              2 * eLpNorm t 1 P := by rw [eLpNorm_nsmul]; norm_num
        _ < ENNReal.ofReal δ + 2 * ENNReal.ofReal η :=
          ENNReal.add_lt_add (hbr i).size_lt
            (ENNReal.mul_lt_mul_right (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) htail)
        _ = ENNReal.ofReal (δ + 2 * η) := by
          calc
            ENNReal.ofReal δ + 2 * ENNReal.ofReal η
                = ENNReal.ofReal δ + ENNReal.ofReal 2 * ENNReal.ofReal η := by norm_num
            _ = ENNReal.ofReal δ + ENNReal.ofReal (2 * η) := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            _ = ENNReal.ofReal (δ + 2 * η) :=
              (ENNReal.ofReal_add hδ.le (by positivity)).symm
  · intro f hf
    obtain ⟨i, hi⟩ := hcov (localizedFunction {x | V x ≤ ENNReal.ofReal M} f)
      ⟨f, hf, rfl⟩
    refine ⟨i, fun x ↦ ?_⟩
    by_cases hx : V x ≤ ENNReal.ofReal M
    · have hnot : ¬ ENNReal.ofReal M < V x := not_lt.mpr hx
      simpa [l', u', t, localizedFunction, tailReal, hx, hnot] using hi x
    · have hgt : ENNReal.ofReal M < V x := lt_of_not_ge hx
      have hi0 : l i x ≤ 0 ∧ 0 ≤ u i x := by
        simpa [localizedFunction, hx] using hi x
      have hf_abs : |f x| ≤ H x := hHenv.2 f hf x
      have hf_lo : -H x ≤ f x := neg_le_of_abs_le hf_abs
      have hf_hi : f x ≤ H x := le_of_abs_le hf_abs
      dsimp [l', u', t]
      have hmem : x ∈ {x | ENNReal.ofReal M < V x} := hgt
      change l i x - {x | ENNReal.ofReal M < V x}.indicator H x ≤ f x ∧
        f x ≤ u i x + {x | ENNReal.ofReal M < V x}.indicator H x
      rw [Set.indicator_of_mem hmem]
      exact ⟨by linarith, by linarith⟩

/-! ### Uniform covering to bracketing for the original class -/

/-- The bracketing-transfer core for vdV Theorem 19.13.

For a suitably measurable class with a finite outer first envelope moment,
finite relative uniform `L¹` covering numbers over all probability measures
imply finite `L¹(P)` bracketing covers for the original class. -/
theorem uniformCovering_finiteBracketing_L1
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (hF_meas : ∀ f ∈ F, Measurable f) -- vdV 19.13 measurable members.
    (hPM : IsPointwiseMeasurable F) -- concrete suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV 19.13 outer envelope.
    (hG1 : outerLpNorm P G 1 < ⊤) -- vdV 19.13 finite outer first moment.
    (hcov : ∀ ε : ℝ, 0 < ε → uniformLpCoveringNumber F G 1 ε < ⊤)
      -- vdV 19.13 all-Q uniform `L¹` covering.
    : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F ε 1 P := by
  intro ε hε
  obtain ⟨V, H, hVmeas, hGV, hVint, hHmeas, hHenv, _hHint, hHV⟩ :=
    exists_localizingMajorants F G P hF_meas hPM hEnv hG1
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨M, hM, htail⟩ :=
    tailReal_small V H P hVmeas hVint hHV (ε / 3) hthird
  let A : Set Ω := {x | V x ≤ ENNReal.ofReal M}
  have hAmeas : MeasurableSet A := measurableSet_Iic.preimage hVmeas
  have hloc_meas : ∀ f ∈ localizedClass F A, Measurable f := by
    rintro _ ⟨f, hf, rfl⟩
    exact measurable_localizedFunction A f hAmeas (hF_meas f hf)
  have hloc_pm : IsPointwiseMeasurable (localizedClass F A) :=
    pointwiseMeasurable_localizedClass F A hPM
  have hloc_bound : ∀ f ∈ localizedClass F A, ∀ x, |f x| ≤ M := by
    simpa only [A] using localizedClass_uniformBound F V H M hHenv hHV hM
  have habs := localized_absoluteCover F G V hVmeas hGV hEnv hcov M hM
  have hdim : ∀ γ : ℝ, 0 < γ → gammaDimension (localizedClass F A) γ < ⊤ := by
    apply allQ_absoluteCover_gammaDimension_lt_top
    simpa only [A] using habs
  have hloc : HasFiniteBracketingCover (localizedClass F A) (ε / 3) 1 P :=
    finiteBracketing_of_gammaDimension (localizedClass F A) P M hloc_meas hloc_pm
      hloc_bound hdim (ε / 3) hthird
  have hexpand := expand_localized_bracketingCover F V H P M (ε / 3) (ε / 3)
    hVmeas hHmeas hHenv hthird hthird htail
    (by simpa only [A] using hloc)
  have hradius : ε / 3 + 2 * (ε / 3) = ε := by ring
  simpa only [hradius] using hexpand

end AsymptoticStatistics.EmpiricalProcess
