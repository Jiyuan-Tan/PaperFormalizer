module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.MaximalBoundedChaining
public import StatLean.AsymptoticStatistics.EmpiricalProcess.BracketingMaximalGeneral

@[expose] public section

/-!
# Uniformly bounded bracketing maximal inequality

This module constructs the finite-stop bounded chaining data and states vdV
Lemma 19.36 with no internal certificate exposed to callers.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {F : Set (Ω → ℝ)} {δ M : ℝ} {n : ℕ}

set_option linter.unusedSectionVars false in
/-- A class already bounded by `M` is fixed by projection truncation.

This is pointwise: `clampReal_of_mem` applies directly to the bound.  No
separate nonnegativity assumption on `M` is needed (nor would it follow when
the domain is empty).
-/
theorem truncateClass_eq_self_of_abs_le
    (hF_bdd : ∀ f ∈ F, ∀ x, |f x| ≤ M) :
    truncateClass F M = F := by
  apply Set.ext
  intro f
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hclamp : clampFn M g = g := by
      funext x
      exact clampReal_of_mem (hF_bdd g hg x)
    rw [hclamp]
    exact hg
  · intro hf
    refine ⟨f, hf, ?_⟩
    funext x
    exact (clampReal_of_mem (hF_bdd f hf x)).symm

/-- Construct the minimal finite-stop bounded chaining data from finite
bracketing entropy.  The result is an internal proof object, never a public
certificate binder of Lemma 19.36. -/
theorem exists_boundedChainingData
    (hF_ne : F.Nonempty) (hδ : 0 < δ)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_bdd : ∀ f ∈ F, ∀ x, |f x| ≤ M)
    (hn : 1 ≤ n)
    (hJ : bracketingEntropyIntegral δ F P < ⊤) :
    Nonempty (BoundedChainingData F P δ M n) := by
  classical
  have hcov : ∀ p, 0 ≤ p →
      HasFiniteBracketingCover F ((1 / 2 : ℝ) ^ (p - 0) * δ) 2 P := by
    intro p _hp
    apply hasFiniteBracketingCover_of_entropyIntegral_lt_top_at hJ
    · positivity
    · simp only [Nat.sub_zero]
      calc
        (1 / 2 : ℝ) ^ p * δ ≤ 1 * δ :=
          mul_le_mul_of_nonneg_right
            (pow_le_one₀ (by norm_num) (by norm_num)) hδ.le
        _ = δ := one_mul δ
  have hJ_pos : 0 < bracketingEntropyIntegral δ F P :=
    bracketingEntropyIntegral_pos_of_nonempty hF_ne hδ
  have hJ_ne : bracketingEntropyIntegral δ F P ≠ ⊤ := ne_of_lt hJ
  have hJ_real : 0 < (bracketingEntropyIntegral δ F P).toReal :=
    ENNReal.toReal_pos hJ_pos.ne' hJ_ne
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hdenom : 0 < 2 * (n : ℝ) * δ := by positivity
  obtain ⟨l, hl⟩ := exists_pow_lt_of_lt_one
    (div_pos hJ_real hdenom) (by norm_num : (1 / 2 : ℝ) < 1)
  have hreal : 2 * (n : ℝ) * boundedDyadicScale δ l <
      (bracketingEntropyIntegral δ F P).toReal := by
    calc
      2 * (n : ℝ) * boundedDyadicScale δ l =
          (1 / 2 : ℝ) ^ l * (2 * (n : ℝ) * δ) := by
        rw [boundedDyadicScale]
        ring
      _ < (bracketingEntropyIntegral δ F P).toReal :=
        (lt_div_iff₀ hdenom).mp hl
  let Stop : ℕ → Prop := fun k =>
    ENNReal.ofReal (2 * (n : ℝ) * boundedDyadicScale δ k) ≤
      bracketingEntropyIntegral δ F P
  have hStop : ∃ k, Stop k := by
    refine ⟨l, ?_⟩
    dsimp only [Stop]
    calc
      ENNReal.ofReal (2 * (n : ℝ) * boundedDyadicScale δ l) ≤
          ENNReal.ofReal (bracketingEntropyIntegral δ F P).toReal :=
        ENNReal.ofReal_le_ofReal hreal.le
      _ = bracketingEntropyIntegral δ F P :=
        ENNReal.ofReal_toReal hJ_ne
  let L := Nat.find hStop
  have hendpoint : ENNReal.ofReal
      (2 * (n : ℝ) * boundedDyadicScale δ L) ≤
      bracketingEntropyIntegral δ F P := by
    simpa only [L, Stop] using Nat.find_spec hStop
  have hminimal : ∀ k < L, bracketingEntropyIntegral δ F P <
      ENNReal.ofReal (2 * (n : ℝ) * boundedDyadicScale δ k) := by
    intro k hk
    apply lt_of_not_ge
    simpa only [Stop] using Nat.find_min hStop hk
  have htruncate : truncateClass F M = F :=
    truncateClass_eq_self_of_abs_le hF_bdd
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨x⟩⟩
  · let B₀ : NestedBracketPartition F P 0 δ :=
      nestedBracketPartition_of_finiteEntropy 0 hδ hcov hF_meas
    let B : NestedBracketPartition (truncateClass F M) P 0 δ := by
      rw [htruncate]
      exact B₀
    refine ⟨{
      partition := B
      truncate_eq := htruncate
      width_le := ?_
      L := L
      endpoint := hendpoint
      minimal := hminimal }⟩
    intro _q _i y
    exact hΩ.elim y
  · obtain ⟨f, hf⟩ := hF_ne
    have hM : 0 ≤ M :=
      (abs_nonneg (f x)).trans (hF_bdd f hf x)
    let B : NestedBracketPartition (truncateClass F M) P 0 δ :=
      nestedBracketPartition_of_finiteEntropy_clamped 0 hδ M hM hcov hF_meas
    refine ⟨{
      partition := B
      truncate_eq := htruncate
      width_le := ?_
      L := L
      endpoint := hendpoint
      minimal := hminimal }⟩
    intro q i y
    exact nestedBracketPartition_of_finiteEntropy_clamped_Δ_le
      0 hδ M hM hcov hF_meas (Nat.zero_le q) i y

set_option linter.unusedVariables false in
/-- **vdV Lemma 19.36 (uniformly bounded bracketing maximal inequality).**

One universal constant precedes every type and datum.  Empty classes, zero
sample size, and infinite entropy are internal branches; no nonnegativity,
nonemptiness, entropy-finiteness, or chaining-data certificate is public.
-/
theorem bracketingMaximal_bounded :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ] (μ : Measure Ξ)
        [IsProbabilityMeasure μ]
        (X : ℕ → Ξ → Ω)
        -- LEAN-ONLY: measurability of each sample coordinate.
        (hX_meas : ∀ i, Measurable (X i))
        -- USER-INPUT: iid observations with common law `P`; vdV Lemma 19.36.
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P)
        (F : Set (Ω → ℝ)) (δ M : ℝ) (n : ℕ) (hδ : 0 < δ)
        -- LEAN-ONLY: explicit measurability of the class members.
        (hF_meas : ∀ f ∈ F, Measurable f)
        -- USER-INPUT: `L²` localization and a uniform envelope bound;
        -- vdV Lemma 19.36.
        (hF_L2 : ∀ f ∈ F, eLpNorm f 2 P < ENNReal.ofReal δ)
        (hF_bdd : ∀ f ∈ F, ∀ x, |f x| ≤ M),
      outerExpectation μ (fun ξ => supNormOver F (fun f =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) ≤
        ENNReal.ofReal C * bracketingEntropyIntegral δ F P *
          (1 + bracketingEntropyIntegral δ F P *
            ENNReal.ofReal (M / (δ ^ 2 * Real.sqrt n))) := by
  classical
  obtain ⟨C, hC, hcore⟩ := bracketingMaximal_of_boundedChainingData
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ Ξ _ μ _ X hX_meas hX_iindep hX_idem hX_law
    F δ M n hδ hF_meas hF_L2 hF_bdd
  by_cases hF : F = ∅
  · subst F
    simp [supNormOver, outerExpectation_const]
  by_cases hn0 : n = 0
  · subst n
    simp [supNormOver, outerExpectation_const]
  by_cases hJtop : bracketingEntropyIntegral δ F P = ⊤
  · have hC_ne : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
    rw [hJtop]
    simp [hC_ne]
  have hF_ne : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
  have hn : 1 ≤ n := (Nat.one_le_iff_ne_zero).2 hn0
  have hJ : bracketingEntropyIntegral δ F P < ⊤ :=
    lt_top_iff_ne_top.mpr hJtop
  obtain ⟨D⟩ := exists_boundedChainingData
    hF_ne hδ hF_meas hF_bdd hn hJ
  exact hcore Ω P Ξ μ F δ M n D hF_ne hF_meas hF_L2 X
    hX_meas hX_iindep hX_idem hX_law hδ hn

end AsymptoticStatistics.EmpiricalProcess
