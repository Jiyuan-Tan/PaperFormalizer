module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChainingAssembly
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation

@[expose] public section

/-!
# Finite-stop chaining for uniformly bounded classes

This module contains the partition-level analytic argument of vdV Lemma 19.36,
independent of the general bound in Lemma 19.34.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal
open scoped ENNReal

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {P : Measure Ω} {μ : Measure Ξ} {F : Set (Ω → ℝ)}
variable {δ M : ℝ} {n : ℕ}

/-- The level-`q` radius `(1/2)^q δ` in the bounded chain.

Edge behavior: this is a total real expression; in the public theorem `δ` is
positive, while internal degenerate branches are handled before it is used.
-/
noncomputable def boundedDyadicScale (δ : ℝ) (q : ℕ) : ℝ := (1 / 2 : ℝ) ^ q * δ

/-- The bracketing-entropy integrand at the level-`q` bounded-chain radius.

Edge behavior is inherited from `entropyIntegrand`: an infinite bracketing
number has weight `⊤`.
-/
noncomputable def boundedCoverWeight (F : Set (Ω → ℝ)) (P : Measure Ω)
    (δ : ℝ) (q : ℕ) : ℝ≥0∞ :=
  entropyIntegrand (boundedDyadicScale δ q) F P

/-- The finite partition weight `sqrt (log (1 + N_q))`.

The `1 +` regularization makes the definition total at `N_q = 0`.
-/
noncomputable def boundedPartitionWeight
    (B : NestedBracketPartition F P 0 δ) (q : ℕ) : ℝ :=
  Real.sqrt (Real.log (1 + B.Nq q))

/-- The bounded-chain crossing threshold at level `q`.

The denominator is `1` plus the next partition weight, hence is positive even
for an empty finite index type.
-/
noncomputable def boundedCrossingThreshold
    (B : NestedBracketPartition F P 0 δ) (q : ℕ) : ℝ :=
  boundedDyadicScale δ q / (1 + boundedPartitionWeight B (q + 1))

/-- Level-zero is a separate strict-crossing gate in the bounded chain. -/
noncomputable def boundedChainB0 (B : NestedBracketPartition F P 0 δ)
    (n : ℕ) (i : Fin (B.Nq 0)) (x : Ω) : Prop :=
  Real.sqrt n * boundedCrossingThreshold B 0 < B.Δ 0 i x

/-- The positive-level first-crossing gate.  It is false at level zero, reads
only the ancestors of the current cell, and requires a strict current crossing.
-/
noncomputable def boundedChainB (B : NestedBracketPartition F P 0 δ)
    (n q : ℕ) (i : Fin (B.Nq q)) (x : Ω) : Prop :=
  0 < q ∧
    (∀ p (hpq : p < q),
      B.Δ p (B.ancestor (Nat.zero_le q) i p (Nat.zero_le p) (Nat.le_of_lt hpq)) x
        ≤ Real.sqrt n * boundedCrossingThreshold B p) ∧
    Real.sqrt n * boundedCrossingThreshold B q < B.Δ q i x

/-- The small-link gate: every ancestor through the current level is below its
bounded-chain threshold. -/
noncomputable def boundedChainA (B : NestedBracketPartition F P 0 δ)
    (n q : ℕ) (i : Fin (B.Nq q)) (x : Ω) : Prop :=
  ∀ p (hpq : p ≤ q),
    B.Δ p (B.ancestor (Nat.zero_le q) i p (Nat.zero_le p) hpq) x
      ≤ Real.sqrt n * boundedCrossingThreshold B p

/-- Structural data derived for the bounded proof of vdV Lemma 19.36.

Constitutive (vdV Lemmas 19.32--19.33, Lemma 19.36 p.288): the nested
partition of the truncated class, equality with the original bounded class,
the `2M` width bound, and a minimal finite stopping endpoint are precisely the
finite-chain inputs.  There is no maximal-inequality certificate field, and
the stopping rule is independent of `M`.
-/
structure BoundedChainingData (F : Set (Ω → ℝ)) (P : Measure Ω)
    (δ M : ℝ) (n : ℕ) where
  /-- Constitutive: nested brackets of the projection-truncated class. -/
  partition : NestedBracketPartition (truncateClass F M) P 0 δ
  /-- Constitutive: the pointwise bound makes projection truncation leave
  the class unchanged. -/
  truncate_eq : truncateClass F M = F
  /-- Constitutive: every cell oscillation is bounded by twice the uniform
  bound. -/
  width_le : ∀ q i x, partition.Δ q i x ≤ 2 * M
  /-- Constitutive: the finite stopping level. -/
  L : ℕ
  /-- Constitutive: the endpoint is the first level where the sample-scale
  dyadic radius is below the entropy budget. -/
  endpoint : ENNReal.ofReal (2 * (n : ℝ) * boundedDyadicScale δ L) ≤
    bracketingEntropyIntegral δ F P
  /-- Constitutive: every earlier level has the strict reverse inequality. -/
  minimal : ∀ l < L, bracketingEntropyIntegral δ F P <
    ENNReal.ofReal (2 * (n : ℝ) * boundedDyadicScale δ l)

/-- The measurable level-zero oscillation envelope selected by `B0`. -/
noncomputable def boundedB0Osc (B : NestedBracketPartition F P 0 δ)
    (n : ℕ) (i : Fin (B.Nq 0)) : Ω → ℝ := fun x =>
  B.Δ 0 i x * Set.indicator {y | boundedChainB0 B n i y} (1 : Ω → ℝ) x

/-- The measurable positive-level oscillation envelope selected by `B`. -/
noncomputable def boundedBposOsc (B : NestedBracketPartition F P 0 δ)
    (n q : ℕ) (i : Fin (B.Nq q)) : Ω → ℝ := fun x =>
  B.Δ q i x * Set.indicator {y | boundedChainB B n q i y} (1 : Ω → ℝ) x

/-- The level-`q` small-link jump from a child cell to its parent. -/
noncomputable def boundedAJump (B : NestedBracketPartition F P 0 δ)
    (n q : ℕ) (i : Fin (B.Nq (q + 1))) : Ω → ℝ := fun x =>
  B.jump (Nat.zero_le q) i x *
    Set.indicator {y | boundedChainA B n q (B.parent (Nat.zero_le q) i) y}
      (1 : Ω → ℝ) x

/-- The terminal level-`L` oscillation envelope on the all-small gate. -/
noncomputable def boundedRemainderOsc (B : NestedBracketPartition F P 0 δ)
    (n L : ℕ) (i : Fin (B.Nq L)) : Ω → ℝ := fun x =>
  B.Δ L i x * Set.indicator {y | boundedChainA B n L i y} (1 : Ω → ℝ) x

/-- Finite head majorant of the bounded chain. -/
noncomputable def boundedChainHeadMajorant (D : BoundedChainingData F P δ M n)
    (X : ℕ → Ξ → Ω) (ξ : Ξ) : ℝ≥0∞ :=
  ⨆ i : Fin (D.partition.Nq 0), ENNReal.ofReal
    |empiricalProcess P n (fun j : Fin n => X j.val ξ) (D.partition.π 0 i)|

/-- Level-zero first-crossing majorant, including the explicit centering
correction from domination by `boundedB0Osc`. -/
noncomputable def boundedChainB0Majorant (D : BoundedChainingData F P δ M n)
    (X : ℕ → Ξ → Ω) (ξ : Ξ) : ℝ≥0∞ :=
  3 * (⨆ i : Fin (D.partition.Nq 0), ENNReal.ofReal
      |empiricalProcess P n (fun j : Fin n => X j.val ξ)
        (boundedB0Osc D.partition n i)|) +
    4 * ENNReal.ofReal (Real.sqrt n) *
      (⨆ i : Fin (D.partition.Nq 0),
        ∫⁻ x, ENNReal.ofReal (boundedB0Osc D.partition n i x) ∂P)

/-- Finite sum of the small-link empirical-process majorants. -/
noncomputable def boundedChainAMajorant (D : BoundedChainingData F P δ M n)
    (X : ℕ → Ξ → Ω) (ξ : Ξ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.range D.L,
    ⨆ i : Fin (D.partition.Nq (q + 1)), ENNReal.ofReal
      |empiricalProcess P n (fun j : Fin n => X j.val ξ)
        (boundedAJump D.partition n q i)|

/-- Finite sum of the positive first-crossing majorants, with their mean
corrections kept explicit. -/
noncomputable def boundedChainBposMajorant (D : BoundedChainingData F P δ M n)
    (X : ℕ → Ξ → Ω) (ξ : Ξ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 D.L,
    (3 * (⨆ i : Fin (D.partition.Nq q), ENNReal.ofReal
        |empiricalProcess P n (fun j : Fin n => X j.val ξ)
          (boundedBposOsc D.partition n q i)|) +
      4 * ENNReal.ofReal (Real.sqrt n) *
        (⨆ i : Fin (D.partition.Nq q),
          ∫⁻ x, ENNReal.ofReal (boundedBposOsc D.partition n q i x) ∂P))

/-- Terminal all-small remainder majorant, including its centering correction. -/
noncomputable def boundedChainRemainderMajorant
    (D : BoundedChainingData F P δ M n)
    (X : ℕ → Ξ → Ω) (ξ : Ξ) : ℝ≥0∞ :=
  3 * (⨆ i : Fin (D.partition.Nq D.L), ENNReal.ofReal
      |empiricalProcess P n (fun j : Fin n => X j.val ξ)
        (boundedRemainderOsc D.partition n D.L i)|) +
    4 * ENNReal.ofReal (Real.sqrt n) *
      (⨆ i : Fin (D.partition.Nq D.L),
        ∫⁻ x, ENNReal.ofReal (boundedRemainderOsc D.partition n D.L i x) ∂P)

/-- `ξ ↦ ofReal |Gₙg|` is measurable for a measurable index function. -/
private lemma bounded_measurable_ofReal_abs_empiricalProcess
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (n : ℕ) {g : Ω → ℝ} (hg : Measurable g) :
    Measurable (fun ξ : Ξ => ENNReal.ofReal
      |empiricalProcess P n (fun j : Fin n => X j.val ξ) g|) := by
  have hE : Measurable (fun ξ : Ξ =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
    unfold empiricalProcess empiricalAvg
    refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum Finset.univ (fun i _ => hg.comp (hX_meas i.val))
  have habs : (fun ξ : Ξ =>
      |empiricalProcess P n (fun i : Fin n => X i.val ξ) g|) =
      (fun ξ : Ξ =>
        ‖empiricalProcess P n (fun i : Fin n => X i.val ξ) g‖) := by
    funext ξ
    exact (Real.norm_eq_abs _).symm
  exact Measurable.ennreal_ofReal (habs ▸ hE.norm)

/-- A finite `iSup` of absolute empirical processes is measurable. -/
private lemma bounded_measurable_iSup_ofReal_abs_empiricalProcess
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (n k : ℕ) {g : Fin k → Ω → ℝ} (hg : ∀ i, Measurable (g i)) :
    Measurable (fun ξ : Ξ => ⨆ i : Fin k, ENNReal.ofReal
      |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|) := by
  exact Measurable.iSup (fun i =>
    bounded_measurable_ofReal_abs_empiricalProcess (P := P) hX_meas n (hg i))

/-- The level-zero crossing set is measurable. -/
private lemma boundedChainB0_measurableSet
    (B : NestedBracketPartition F P 0 δ) (n : ℕ) (i : Fin (B.Nq 0)) :
    MeasurableSet {x | boundedChainB0 B n i x} := by
  change MeasurableSet
    {x | Real.sqrt n * boundedCrossingThreshold B 0 < B.Δ 0 i x}
  exact measurableSet_lt measurable_const (B.Δ_meas le_rfl i)

/-- Every positive-level first-crossing set is measurable. -/
private lemma boundedChainB_measurableSet
    (B : NestedBracketPartition F P 0 δ) (n q : ℕ) (i : Fin (B.Nq q)) :
    MeasurableSet {x | boundedChainB B n q i x} := by
  have hset : {x | boundedChainB B n q i x} =
      {_x : Ω | 0 < q} ∩
        ((⋂ (p : ℕ) (hpq : p < q),
            {x | B.Δ p
                (B.ancestor (Nat.zero_le q) i p (Nat.zero_le p) (Nat.le_of_lt hpq)) x
                  ≤ Real.sqrt n * boundedCrossingThreshold B p}) ∩
          {x | Real.sqrt n * boundedCrossingThreshold B q < B.Δ q i x}) := by
    ext x
    simp only [boundedChainB, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  refine MeasurableSet.inter ?_
    (measurableSet_lt measurable_const (B.Δ_meas (Nat.zero_le q) i))
  refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hpq => ?_))
  exact measurableSet_le (B.Δ_meas (Nat.zero_le p) _) measurable_const

/-- Every small-ancestor gate is measurable. -/
private lemma boundedChainA_measurableSet
    (B : NestedBracketPartition F P 0 δ) (n q : ℕ) (i : Fin (B.Nq q)) :
    MeasurableSet {x | boundedChainA B n q i x} := by
  have hset : {x | boundedChainA B n q i x} =
      ⋂ (p : ℕ) (hpq : p ≤ q),
        {x | B.Δ p
            (B.ancestor (Nat.zero_le q) i p (Nat.zero_le p) hpq) x
              ≤ Real.sqrt n * boundedCrossingThreshold B p} := by
    ext x
    simp only [boundedChainA, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hpq => ?_))
  exact measurableSet_le (B.Δ_meas (Nat.zero_le p) _) measurable_const

/-- Replacing a signed link `h` by a nonnegative integrable majorant `g`
retains the centering correction `2 sqrt(n) P g`. -/
theorem empiricalProcess_abs_le_of_abs_le
    (P : Measure Ω) (n : ℕ) (x : Fin n → Ω) (h g : Ω → ℝ)
    -- Integrability makes the deterministic mean correction finite.
    (hg_int : Integrable g P) (hg_nonneg : ∀ y, 0 ≤ g y)
    (hhg : ∀ y, |h y| ≤ g y) :
    |empiricalProcess P n x h| ≤ |empiricalProcess P n x g| +
      2 * Real.sqrt n * ∫ y, g y ∂P := by
  have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hg_avg_nonneg : 0 ≤ empiricalAvg g n x := by
    unfold empiricalAvg
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg (fun i _ => hg_nonneg (x i)))
  have hg_int_nonneg : 0 ≤ ∫ y, g y ∂P := integral_nonneg hg_nonneg
  have havg_abs_le : |empiricalAvg h n x| ≤ empiricalAvg g n x := by
    unfold empiricalAvg
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg n))
    calc |∑ i, h (x i)| ≤ ∑ i : Fin n, |h (x i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, g (x i) :=
          Finset.sum_le_sum (fun i _ => hhg (x i))
  have hint_abs_le : |∫ y, h y ∂P| ≤ ∫ y, g y ∂P := by
    by_cases hh_int : Integrable h P
    · calc |∫ y, h y ∂P| ≤ ∫ y, |h y| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ y, g y ∂P :=
          integral_mono hh_int.abs hg_int (fun y => hhg y)
    · rw [MeasureTheory.integral_undef hh_int, abs_zero]
      exact hg_int_nonneg
  have hcenter_h :
      |empiricalAvg h n x - ∫ y, h y ∂P| ≤
        empiricalAvg g n x + ∫ y, g y ∂P := by
    calc |empiricalAvg h n x - ∫ y, h y ∂P|
        ≤ |empiricalAvg h n x| + |∫ y, h y ∂P| := abs_sub _ _
      _ ≤ empiricalAvg g n x + ∫ y, g y ∂P :=
        add_le_add havg_abs_le hint_abs_le
  have havg_g_center :
      empiricalAvg g n x ≤
        |empiricalAvg g n x - ∫ y, g y ∂P| + ∫ y, g y ∂P := by
    calc empiricalAvg g n x =
          (empiricalAvg g n x - ∫ y, g y ∂P) + ∫ y, g y ∂P := by ring
      _ ≤ |empiricalAvg g n x - ∫ y, g y ∂P| + ∫ y, g y ∂P :=
        add_le_add (le_abs_self _) le_rfl
  unfold empiricalProcess
  simp only [abs_mul, abs_of_nonneg hsqrt]
  calc Real.sqrt n * |empiricalAvg h n x - ∫ y, h y ∂P|
      ≤ Real.sqrt n * (empiricalAvg g n x + ∫ y, g y ∂P) :=
        mul_le_mul_of_nonneg_left hcenter_h hsqrt
    _ = Real.sqrt n * empiricalAvg g n x +
          Real.sqrt n * ∫ y, g y ∂P := by ring
    _ ≤ (Real.sqrt n *
          |empiricalAvg g n x - ∫ y, g y ∂P| +
          Real.sqrt n * ∫ y, g y ∂P) +
          Real.sqrt n * ∫ y, g y ∂P := by
        exact add_le_add
          (by simpa [mul_add] using mul_le_mul_of_nonneg_left havg_g_center hsqrt)
          le_rfl
    _ = Real.sqrt n *
          |empiricalAvg g n x - ∫ y, g y ∂P| +
          2 * Real.sqrt n * ∫ y, g y ∂P := by ring

private lemma bounded_tsum_pow_half_sum_Icc_succ_le (a : ℕ → ℝ≥0∞) :
    (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p))
      ≤ 4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by
  have hsplit : ∀ q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p) =
        (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 q, a p) +
          (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1) := by
    intro q; rw [Finset.sum_Icc_succ_top (Nat.zero_le _), mul_add]
  calc
    (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p)) =
        (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 q, a p)) +
        ∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1) := by
      simp_rw [hsplit]; rw [ENNReal.tsum_add]
    _ ≤ 2 * (∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p) +
          2 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by
      refine add_le_add (AsymptoticStatistics.ForMathlib.ENNReal.tsum_pow_half_sum_Icc_le 0 a) ?_
      have hreidx : (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ (q + 1) * a (q + 1)) ≤
          ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p :=
        ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => by simpa using h) _
      have hhalf : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      calc
        (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1)) =
            2 * ∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ (q + 1) * a (q + 1) := by
          rw [← ENNReal.tsum_mul_left]; refine tsum_congr fun q => ?_
          have hpow : (2⁻¹ : ℝ≥0∞) ^ q = 2 * (2⁻¹ : ℝ≥0∞) ^ (q + 1) := by
            rw [pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞) _, mul_assoc, hhalf, mul_one]
          rw [hpow, mul_assoc]
        _ ≤ 2 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by gcongr
    _ = 4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by ring
set_option linter.unusedVariables false in
/-- The finite partition weights fit inside the bracketing entropy budget.

Class nonemptiness is derived internally after the public empty-class branch;
it is needed here because the positive head weight cannot be paid when the
entropy integral of the empty class is zero.
-/
theorem bounded_entropy_budget :
    ∃ cE : ℝ, 0 < cE ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        (F : Set (Ω → ℝ)) (δ M : ℝ) (n : ℕ)
        (D : BoundedChainingData F P δ M n) (hF_ne : F.Nonempty),
      0 < δ →
        ENNReal.ofReal δ * ENNReal.ofReal (boundedPartitionWeight D.partition 0)
            ≤ bracketingEntropyIntegral δ F P ∧
        ENNReal.ofReal (boundedPartitionWeight D.partition 0)
            ≤ bracketingEntropyIntegral δ F P / ENNReal.ofReal δ ∧
        (∑ q ∈ Finset.range (D.L + 1), ENNReal.ofReal
            (boundedDyadicScale δ q * (1 + boundedPartitionWeight D.partition (q + 1))))
          ≤ ENNReal.ofReal cE * bracketingEntropyIntegral δ F P := by
  classical
  have hs_pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  let K : ℝ := 1 + 1 / Real.sqrt (Real.log 2)
  have hK_pos : 0 < K := by dsimp [K]; positivity
  refine ⟨8 * K, by positivity, ?_⟩
  intro Ω _ P F δ M n D hF_ne hδ
  let a : ℕ → ℝ≥0∞ := fun q => entropyIntegrand (boundedDyadicScale δ q) F P
  have hJ_pos : 0 < bracketingEntropyIntegral δ F P :=
    bracketingEntropyIntegral_pos_of_nonempty hF_ne hδ
  have hw0_le : ENNReal.ofReal (boundedPartitionWeight D.partition 0) ≤
      entropyIntegrand δ F P := by
    have hcard : (D.partition.Nq 0 : ℕ∞) ≤ (D.partition.coverCard 0 : ℕ∞) := by
      simpa using D.partition.card_le (le_rfl : 0 ≤ 0)
    have hcover : (D.partition.coverCard 0 : ℕ∞) ≤
        bracketingNumber δ F 2 P := by
      have h' : (D.partition.coverCard 0 : ℕ∞) ≤
          bracketingNumber δ (truncateClass F M) 2 P := by
        simpa using D.partition.coverCard_le (le_rfl : 0 ≤ 0)
      exact h'.trans_eq (congrArg (fun G => bracketingNumber δ G 2 P) D.truncate_eq)
    calc
      ENNReal.ofReal (boundedPartitionWeight D.partition 0) =
          entropyWeight (D.partition.Nq 0 : ℕ∞) := by
            rw [entropyWeight_coe]; rfl
      _ ≤ entropyWeight (bracketingNumber δ F 2 P) :=
        entropyWeight_mono (hcard.trans hcover)
      _ = entropyIntegrand δ F P := rfl
  have hδ_integrand_le : ENNReal.ofReal δ * entropyIntegrand δ F P ≤
      bracketingEntropyIntegral δ F P := by
    rw [bracketingEntropyIntegral_eq_setLIntegral]
    have hmono : ∫⁻ _ε in Set.Ioc 0 δ, entropyIntegrand δ F P ∂volume ≤
        ∫⁻ ε in Set.Ioc 0 δ, entropyIntegrand ε F P ∂volume :=
      setLIntegral_mono' measurableSet_Ioc (fun ε hε => entropyIntegrand_antitone_eps hε.2)
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, sub_zero] at hmono
    simpa [mul_comm] using hmono
  have hhead : ENNReal.ofReal δ * ENNReal.ofReal (boundedPartitionWeight D.partition 0) ≤
      bracketingEntropyIntegral δ F P := by
    calc
      _ ≤ ENNReal.ofReal δ * entropyIntegrand δ F P := by gcongr
      _ ≤ _ := hδ_integrand_le
  refine ⟨hhead, ?_, ?_⟩
  · exact (ENNReal.le_div_iff_mul_le (Or.inr hJ_pos.ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 (by simpa [mul_comm] using hhead)
  · have hweight : ∀ q : ℕ,
        ENNReal.ofReal (boundedPartitionWeight D.partition (q + 1)) ≤
          ∑ p ∈ Finset.Icc 0 (q + 1), a p := by
      intro q
      have hIcc : (Finset.Icc 0 (q + 1)).Nonempty := ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      have hprod : (D.partition.Nq (q + 1) : ℝ) ≤
          ∏ p ∈ Finset.Icc 0 (q + 1), (D.partition.coverCard p : ℝ) := by
        exact_mod_cast D.partition.card_le (Nat.zero_le (q + 1))
      have hsalvage : boundedPartitionWeight D.partition (q + 1) ≤
          ∑ p ∈ Finset.Icc 0 (q + 1),
            Real.sqrt (Real.log (1 + (D.partition.coverCard p : ℝ))) := by
        refine (Real.sqrt_le_sqrt (Real.log_le_log (by positivity) ?_)).trans
          (AsymptoticStatistics.ForMathlib.Real.sqrt_log_prod_le_sum_one_add
            hIcc D.partition.coverCard)
        have hp : (0 : ℝ) ≤ ∏ p ∈ Finset.Icc 0 (q + 1), (D.partition.coverCard p : ℝ) :=
          Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
        linarith
      calc
        ENNReal.ofReal (boundedPartitionWeight D.partition (q + 1)) ≤
            ∑ p ∈ Finset.Icc 0 (q + 1), ENNReal.ofReal
              (Real.sqrt (Real.log (1 + (D.partition.coverCard p : ℝ)))) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hsalvage
        _ ≤ ∑ p ∈ Finset.Icc 0 (q + 1), a p := by
          refine Finset.sum_le_sum fun p _ => ?_
          have hc := D.partition.coverCard_le (Nat.zero_le p)
          calc
            ENNReal.ofReal (Real.sqrt (Real.log (1 + (D.partition.coverCard p : ℝ)))) =
                entropyWeight (D.partition.coverCard p : ℕ∞) :=
              (entropyWeight_coe _).symm
            _ ≤ entropyWeight
                (bracketingNumber (boundedDyadicScale δ p) (truncateClass F M) 2 P) := by
              apply entropyWeight_mono
              simpa [boundedDyadicScale] using hc
            _ = entropyWeight (bracketingNumber (boundedDyadicScale δ p) F 2 P) := by
              rw [D.truncate_eq]
            _ = a p := rfl
    have hone_add : ∀ q : ℕ,
        ENNReal.ofReal (1 + boundedPartitionWeight D.partition (q + 1)) ≤
          ENNReal.ofReal K * (∑ p ∈ Finset.Icc 0 (q + 1), a p) := by
      intro q
      let S : ℝ≥0∞ := ∑ p ∈ Finset.Icc 0 (q + 1), a p
      have hc0_le : ENNReal.ofReal (Real.sqrt (Real.log 2)) ≤ S := by
        have h0 : (0 : ℕ) ∈ Finset.Icc 0 (q + 1) :=
          Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
        calc
          _ ≤ a 0 := by simpa [a, boundedDyadicScale] using
            sqrt_log_two_le_entropyIntegrand (P := P) hF_ne δ
          _ ≤ S := Finset.single_le_sum (f := a) (fun _ _ => zero_le) h0
      have hc0_ne : ENNReal.ofReal (Real.sqrt (Real.log 2)) ≠ 0 := by
        simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hs_pos
      have hone : (1 : ℝ≥0∞) ≤
          (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹ * S := by
        calc
          (1 : ℝ≥0∞) = (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹ *
              ENNReal.ofReal (Real.sqrt (Real.log 2)) :=
            (ENNReal.inv_mul_cancel hc0_ne ENNReal.ofReal_ne_top).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hc0_le (zero_le)
      have hK : ENNReal.ofReal K * S =
          (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹ * S + S := by
        dsimp [K]
        rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_div_of_pos hs_pos, ENNReal.ofReal_one, one_div, add_mul,
          one_mul, add_comm]
      rw [hK, ENNReal.ofReal_add (by norm_num)
        (by unfold boundedPartitionWeight; positivity), ENNReal.ofReal_one]
      exact add_le_add hone (by simpa [S] using hweight q)
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    have hscale : ∀ q : ℕ, ENNReal.ofReal (boundedDyadicScale δ q) =
        (2⁻¹ : ℝ≥0∞) ^ q * ENNReal.ofReal δ := by
      intro q
      unfold boundedDyadicScale
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), hhalf]
    have hlevel : ∀ q : ℕ, ENNReal.ofReal
        (boundedDyadicScale δ q * (1 + boundedPartitionWeight D.partition (q + 1))) ≤
          ENNReal.ofReal K * (ENNReal.ofReal (boundedDyadicScale δ q) *
            (∑ p ∈ Finset.Icc 0 (q + 1), a p)) := by
      intro q
      rw [ENNReal.ofReal_mul (by unfold boundedDyadicScale; positivity)]
      calc
        _ ≤ ENNReal.ofReal (boundedDyadicScale δ q) *
            (ENNReal.ofReal K * (∑ p ∈ Finset.Icc 0 (q + 1), a p)) := by
          gcongr
          exact hone_add q
        _ = _ := by ring
    calc
      (∑ q ∈ Finset.range (D.L + 1), ENNReal.ofReal
          (boundedDyadicScale δ q * (1 + boundedPartitionWeight D.partition (q + 1)))) ≤
          ENNReal.ofReal K * ∑' q : ℕ, ENNReal.ofReal (boundedDyadicScale δ q) *
            (∑ p ∈ Finset.Icc 0 (q + 1), a p) := by
        calc
          _ ≤ ∑ q ∈ Finset.range (D.L + 1), ENNReal.ofReal K *
                (ENNReal.ofReal (boundedDyadicScale δ q) *
                  (∑ p ∈ Finset.Icc 0 (q + 1), a p)) :=
            Finset.sum_le_sum (fun q _ => hlevel q)
          _ = ENNReal.ofReal K * ∑ q ∈ Finset.range (D.L + 1),
                ENNReal.ofReal (boundedDyadicScale δ q) *
                  (∑ p ∈ Finset.Icc 0 (q + 1), a p) := by rw [Finset.mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left (ENNReal.sum_le_tsum _) (zero_le)
      _ = ENNReal.ofReal K * ∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q *
            (∑ p ∈ Finset.Icc 0 (q + 1), ENNReal.ofReal δ * a p) := by
        congr 1
        refine tsum_congr fun q => ?_
        rw [hscale q, ← Finset.mul_sum]
        ring
      _ ≤ ENNReal.ofReal K *
          (4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * (ENNReal.ofReal δ * a p)) := by
        gcongr
        exact bounded_tsum_pow_half_sum_Icc_succ_le
          (fun p => ENNReal.ofReal δ * a p)
      _ = ENNReal.ofReal K * (4 * ∑' p : ℕ,
            ENNReal.ofReal (boundedDyadicScale δ p) *
              entropyIntegrand (boundedDyadicScale δ p) F P) := by
        congr 1
        congr 1
        refine tsum_congr fun p => ?_
        rw [hscale p]
        dsimp [a]
        ring
      _ ≤ ENNReal.ofReal K * (4 * (2 * bracketingEntropyIntegral δ F P)) := by
        gcongr
        exact dyadic_sum_le_bracketingEntropyIntegral hδ
      _ = ENNReal.ofReal (8 * K) * bracketingEntropyIntegral δ F P := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
          show ENNReal.ofReal 8 = (8 : ℝ≥0∞) by norm_num]
        ring

/-- Along the chosen cell chain, the `A` gate is exactly smallness through the
current level. -/
private lemma boundedChainA_cellChain_iff
    (B : NestedBracketPartition F P 0 δ) {f : Ω → ℝ}
    (hf : f ∈ F) (n q : ℕ) (x : Ω) :
    boundedChainA B n (0 + q) (cellChain B hf q) x ↔
      ∀ j ≤ q, B.Δ (0 + j) (cellChain B hf j) x ≤
        Real.sqrt n * boundedCrossingThreshold B (0 + j) := by
  constructor
  · intro h j hjq
    have hj := h (0 + j) (by omega)
    rwa [cellChain_ancestor B hf q j hjq] at hj
  · intro h p hpq
    obtain ⟨j, rfl⟩ : ∃ j, p = 0 + j := ⟨p, by omega⟩
    have hjq : j ≤ q := by simpa using hpq
    rw [cellChain_ancestor B hf q j hjq]
    exact h j hjq

/-- Along the chosen cell chain, the positive `B` gate is the first strict
crossing after level zero. -/
private lemma boundedChainB_cellChain_iff
    (B : NestedBracketPartition F P 0 δ) {f : Ω → ℝ}
    (hf : f ∈ F) (n q : ℕ) (x : Ω) :
    boundedChainB B n (0 + q) (cellChain B hf q) x ↔
      0 < q ∧
        (∀ j < q, B.Δ (0 + j) (cellChain B hf j) x ≤
          Real.sqrt n * boundedCrossingThreshold B (0 + j)) ∧
        ¬ B.Δ (0 + q) (cellChain B hf q) x ≤
          Real.sqrt n * boundedCrossingThreshold B (0 + q) := by
  unfold boundedChainB
  constructor
  · rintro ⟨hq, hsmall, hcross⟩
    refine ⟨by omega, ?_, not_le_of_gt hcross⟩
    intro j hjq
    have hj := hsmall (0 + j) (by omega)
    rwa [cellChain_ancestor B hf q j (Nat.le_of_lt hjq)] at hj
  · rintro ⟨hq, hsmall, hcross⟩
    refine ⟨by omega, ?_, lt_of_not_ge hcross⟩
    intro p hpq
    obtain ⟨j, rfl⟩ : ∃ j, p = 0 + j := ⟨p, by omega⟩
    have hjq : j < q := by simpa using hpq
    rw [cellChain_ancestor B hf q j (Nat.le_of_lt hjq)]
    exact hsmall j hjq

/-- Finite head/`B0`/positive-`B`/`A` telescope, with the two positive-level
summands explicitly grouped and the terminal `A_L` remainder retained. -/
theorem bounded_chain_finite_telescope
    (D : BoundedChainingData F P δ M n) (f : Ω → ℝ)
    (hf : f ∈ truncateClass F M) (x : Ω) :
    f x = D.partition.π 0 (cellChain D.partition hf 0) x +
      (f x - D.partition.π 0 (cellChain D.partition hf 0) x) *
        Set.indicator {y | boundedChainB0 D.partition n (cellChain D.partition hf 0) y}
          (1 : Ω → ℝ) x +
      (∑ q ∈ Finset.Icc 1 D.L,
        ((D.partition.π (0 + q) (cellChain D.partition hf q) x -
            D.partition.π (0 + (q - 1)) (cellChain D.partition hf (q - 1)) x) *
          Set.indicator
            {y | boundedChainA D.partition n (0 + (q - 1))
              (cellChain D.partition hf (q - 1)) y} (1 : Ω → ℝ) x +
        (f x - D.partition.π (0 + q) (cellChain D.partition hf q) x) *
          Set.indicator
            {y | boundedChainB D.partition n (0 + q) (cellChain D.partition hf q) y}
            (1 : Ω → ℝ) x)) +
      (f x - D.partition.π (0 + D.L) (cellChain D.partition hf D.L) x) *
        Set.indicator
          {y | boundedChainA D.partition n (0 + D.L) (cellChain D.partition hf D.L) y}
          (1 : Ω → ℝ) x := by
  classical
  let head : ℝ := D.partition.π 0 (cellChain D.partition hf 0) x
  let b0 : ℝ :=
    (f x - D.partition.π 0 (cellChain D.partition hf 0) x) *
      Set.indicator
        {y | boundedChainB0 D.partition n (cellChain D.partition hf 0) y}
        (1 : Ω → ℝ) x
  let term : ℕ → ℝ := fun q =>
    (D.partition.π (0 + q) (cellChain D.partition hf q) x -
        D.partition.π (0 + (q - 1)) (cellChain D.partition hf (q - 1)) x) *
      Set.indicator
        {y | boundedChainA D.partition n (0 + (q - 1))
          (cellChain D.partition hf (q - 1)) y} (1 : Ω → ℝ) x +
    (f x - D.partition.π (0 + q) (cellChain D.partition hf q) x) *
      Set.indicator
        {y | boundedChainB D.partition n (0 + q) (cellChain D.partition hf q) y}
        (1 : Ω → ℝ) x
  let rem : ℕ → ℝ := fun q =>
    (f x - D.partition.π (0 + q) (cellChain D.partition hf q) x) *
      Set.indicator
        {y | boundedChainA D.partition n (0 + q) (cellChain D.partition hf q) y}
        (1 : Ω → ℝ) x
  have htel : ∀ L : ℕ,
      f x = head + b0 + (∑ q ∈ Finset.Icc 1 L, term q) + rem L := by
    intro L
    induction L with
    | zero =>
        have hA0 : boundedChainA D.partition n 0 (cellChain D.partition hf 0) x ↔
            D.partition.Δ 0 (cellChain D.partition hf 0) x ≤
              Real.sqrt n * boundedCrossingThreshold D.partition 0 := by
          simpa using boundedChainA_cellChain_iff D.partition hf n 0 x
        have hB0 : boundedChainB0 D.partition n (cellChain D.partition hf 0) x ↔
            ¬ D.partition.Δ 0 (cellChain D.partition hf 0) x ≤
              Real.sqrt n * boundedCrossingThreshold D.partition 0 := by
          unfold boundedChainB0
          rw [not_le]
        by_cases hs : D.partition.Δ 0 (cellChain D.partition hf 0) x ≤
            Real.sqrt n * boundedCrossingThreshold D.partition 0
        · have ha : boundedChainA D.partition n 0 (cellChain D.partition hf 0) x :=
            hA0.mpr hs
          have hb : ¬ boundedChainB0 D.partition n (cellChain D.partition hf 0) x :=
            fun h => (hB0.mp h) hs
          simp [head, b0, rem, ha, hb]
        · have ha : ¬ boundedChainA D.partition n 0 (cellChain D.partition hf 0) x :=
            fun h => hs (hA0.mp h)
          have hb : boundedChainB0 D.partition n (cellChain D.partition hf 0) x :=
            hB0.mpr hs
          simp [head, b0, rem, ha, hb]
    | succ L ih =>
        have hstep : rem L = term (L + 1) + rem (L + 1) := by
          by_cases hAL : boundedChainA D.partition n (0 + L)
              (cellChain D.partition hf L) x
          · have hsmall :=
              (boundedChainA_cellChain_iff D.partition hf n L x).mp hAL
            by_cases hnext : D.partition.Δ (0 + (L + 1))
                (cellChain D.partition hf (L + 1)) x ≤
                  Real.sqrt n * boundedCrossingThreshold D.partition (0 + (L + 1))
            · have hAL1 : boundedChainA D.partition n (0 + (L + 1))
                  (cellChain D.partition hf (L + 1)) x :=
                (boundedChainA_cellChain_iff D.partition hf n (L + 1) x).mpr
                  (fun j hj => by
                    by_cases hjtop : j = L + 1
                    · subst hjtop
                      exact hnext
                    · exact hsmall j (by omega))
              have hBL1 : ¬ boundedChainB D.partition n (0 + (L + 1))
                  (cellChain D.partition hf (L + 1)) x := by
                intro hB
                exact (boundedChainB_cellChain_iff D.partition hf n (L + 1) x).mp hB |>.2.2
                  hnext
              simp [term, rem, hAL, hAL1, hBL1]
            · have hAL1 : ¬ boundedChainA D.partition n (0 + (L + 1))
                  (cellChain D.partition hf (L + 1)) x := by
                intro hA
                exact hnext
                  ((boundedChainA_cellChain_iff D.partition hf n (L + 1) x).mp hA
                    (L + 1) le_rfl)
              have hBL1 : boundedChainB D.partition n (0 + (L + 1))
                  (cellChain D.partition hf (L + 1)) x :=
                (boundedChainB_cellChain_iff D.partition hf n (L + 1) x).mpr
                  ⟨by omega, fun j hj => hsmall j (by omega), hnext⟩
              simp [term, rem, hAL, hAL1, hBL1]
          · have hAL1 : ¬ boundedChainA D.partition n (0 + (L + 1))
                (cellChain D.partition hf (L + 1)) x := by
              intro hA
              apply hAL
              exact (boundedChainA_cellChain_iff D.partition hf n L x).mpr
                (fun j hj =>
                  (boundedChainA_cellChain_iff D.partition hf n (L + 1) x).mp hA j
                    (by omega))
            have hBL1 : ¬ boundedChainB D.partition n (0 + (L + 1))
                (cellChain D.partition hf (L + 1)) x := by
              intro hB
              apply hAL
              exact (boundedChainA_cellChain_iff D.partition hf n L x).mpr
                (fun j hj =>
                  (boundedChainB_cellChain_iff D.partition hf n (L + 1) x).mp hB |>.2.1 j
                    (by omega))
            simp [term, rem, hAL, hAL1, hBL1]
        rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
          Finset.sum_insert (by simp)]
        calc f x = head + b0 + (∑ q ∈ Finset.Icc 1 L, term q) + rem L := ih
          _ = head + b0 +
              (term (L + 1) + ∑ q ∈ Finset.Icc 1 L, term q) + rem (L + 1) := by
                rw [hstep]
                ring
  simpa only [head, b0, term, rem] using htel D.L

set_option linter.style.longLine false in
omit [MeasurableSpace Ξ] in
/-- The complete positive-level telescope sum is integrable, and its empirical process is controlled by the existing small-link and positive-crossing majorants. -/
private lemma bounded_chain_positive_sum_integrable_and_le_majorants
    [IsProbabilityMeasure P]
    (D : BoundedChainingData F P δ M n)
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω} (ξ : Ξ) (f : Ω → ℝ)
    (hf : f ∈ truncateClass F M) :
    let pos : Ω → ℝ := fun x =>
      ∑ q ∈ Finset.Icc 1 D.L,
        ((D.partition.π (0 + q) (cellChain D.partition hf q) x -
            D.partition.π (0 + (q - 1)) (cellChain D.partition hf (q - 1)) x) *
          Set.indicator
            {y | boundedChainA D.partition n (0 + (q - 1))
              (cellChain D.partition hf (q - 1)) y} (1 : Ω → ℝ) x +
        (f x - D.partition.π (0 + q) (cellChain D.partition hf q) x) *
          Set.indicator
            {y | boundedChainB D.partition n (0 + q) (cellChain D.partition hf q) y}
            (1 : Ω → ℝ) x)
    Integrable pos P ∧
      ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) pos| ≤
        boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ := by
  classical
  dsimp only
  let Y : Fin n → Ω := fun i => X i.val ξ
  let aLink : ℕ → Ω → ℝ := fun q x => (D.partition.π (0 + q) (cellChain D.partition hf q) x - D.partition.π (0 + (q - 1)) (cellChain D.partition hf (q - 1)) x) *
    Set.indicator {y | boundedChainA D.partition n (0 + (q - 1)) (cellChain D.partition hf (q - 1)) y} 1 x
  let bLink : ℕ → Ω → ℝ := fun q x => (f x - D.partition.π (0 + q) (cellChain D.partition hf q) x) *
    Set.indicator {y | boundedChainB D.partition n (0 + q) (cellChain D.partition hf q) y} 1 x
  have hfF : f ∈ F := by simpa only [D.truncate_eq] using hf
  have hΔ_nn : ∀ q i x, 0 ≤ D.partition.Δ q i x := by
    intro q i x
    have h := D.partition.diam (Nat.zero_le q) i (D.partition.π q i)
      (D.partition.π_mem (Nat.zero_le q) i) (D.partition.π q i) (D.partition.π_mem (Nat.zero_le q) i) x
    simpa using h
  have ha_eq : ∀ k, aLink (k + 1) = boundedAJump D.partition n (0 + k) (cellChain D.partition hf (k + 1)) := by
    intro k
    funext x
    simp only [aLink, boundedAJump, NestedBracketPartition.jump, Nat.add_one_sub_one]
    rw [cellChain_parent D.partition hf k]
    congr 4
  have ha_int : ∀ q, 1 ≤ q → Integrable (aLink q) P := by
    intro q hq
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [ha_eq k]
    let i := cellChain D.partition hf (k + 1)
    refine Integrable.mono' ((D.partition.Δ_memLp (Nat.zero_le (0 + k))
      (D.partition.parent (Nat.zero_le (0 + k)) i)).integrable (by norm_num))
      (((D.partition.jump_measurable D.partition.π_meas (Nat.zero_le (0 + k)) i).mul (measurable_const.indicator
        (boundedChainA_measurableSet D.partition n (0 + k) (D.partition.parent (Nat.zero_le (0 + k)) i)))).aestronglyMeasurable) ?_
    filter_upwards [] with x
    simp only [boundedAJump]
    rw [Real.norm_eq_abs, abs_mul]
    calc |D.partition.jump (Nat.zero_le (0 + k)) i x| * |Set.indicator {y | boundedChainA D.partition n
          (0 + k) (D.partition.parent (Nat.zero_le (0 + k)) i) y} 1 x|
        ≤ D.partition.Δ (0 + k) (D.partition.parent (Nat.zero_le (0 + k)) i) x * 1 := by
          refine mul_le_mul (D.partition.jump_abs_le (Nat.zero_le (0 + k)) i x) ?_ (abs_nonneg _) (hΔ_nn (0 + k) _ x)
          by_cases hx : boundedChainA D.partition n (0 + k) (D.partition.parent (Nat.zero_le (0 + k)) i) x <;> simp [hx]
      _ = _ := mul_one _
  have hb_int : ∀ q, Integrable (bLink q) P := by
    intro q
    refine Integrable.mono' ((D.partition.Δ_memLp (Nat.zero_le (0 + q)) (cellChain D.partition hf q)).integrable (by norm_num))
      (((hF_meas f hfF).sub (D.partition.π_meas (Nat.zero_le (0 + q)) _)).mul (measurable_const.indicator
        (boundedChainB_measurableSet D.partition n (0 + q) _))).aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    calc |f x - D.partition.π (0 + q) (cellChain D.partition hf q) x| * |Set.indicator
          {y | boundedChainB D.partition n (0 + q) (cellChain D.partition hf q) y} 1 x|
        ≤ D.partition.Δ (0 + q) (cellChain D.partition hf q) x * 1 := by
          refine mul_le_mul ?_ ?_ (abs_nonneg _) (hΔ_nn (0 + q) _ x)
          · exact D.partition.diam (Nat.zero_le (0 + q)) _ f (cellChain_mem D.partition hf q) _ (D.partition.π_mem (Nat.zero_le (0 + q)) _) x
          · by_cases hx : boundedChainB D.partition n (0 + q) (cellChain D.partition hf q) x <;> simp [hx]
      _ = _ := mul_one _
  have ht_int : ∀ q ∈ Finset.Icc 1 D.L, Integrable (fun x => aLink q x + bLink q x) P := fun q hq => (ha_int q (Finset.mem_Icc.mp hq).1).add (hb_int q)
  have hpos_int : Integrable (fun x => ∑ q ∈ Finset.Icc 1 D.L, (aLink q x + bLink q x)) P := integrable_finset_sum _ ht_int
  have hg_nn : ∀ q x, 0 ≤ boundedBposOsc D.partition n (0 + q) (cellChain D.partition hf q) x := by
    intro q x
    exact mul_nonneg (hΔ_nn (0 + q) _ x) (by
      by_cases hx : boundedChainB D.partition n (0 + q) (cellChain D.partition hf q) x <;> simp [hx])
  have hg_int : ∀ q, Integrable (boundedBposOsc D.partition n (0 + q) (cellChain D.partition hf q)) P := by
    intro q
    refine Integrable.mono' ((D.partition.Δ_memLp (Nat.zero_le (0 + q)) (cellChain D.partition hf q)).integrable (by norm_num))
      (((D.partition.Δ_meas (Nat.zero_le (0 + q)) _).mul (measurable_const.indicator (boundedChainB_measurableSet D.partition n (0 + q) _))).aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn q x)]
    simp only [boundedBposOsc, Set.indicator]
    split <;> simp [hΔ_nn]
  have hb_dom : ∀ q x, |bLink q x| ≤ boundedBposOsc D.partition n (0 + q) (cellChain D.partition hf q) x := by
    intro q x
    simp only [bLink, boundedBposOsc]
    simp only [Set.indicator]
    split
    · simp only [Pi.one_apply, mul_one]
      exact D.partition.diam (Nat.zero_le (0 + q)) _ f (cellChain_mem D.partition hf q) _
        (D.partition.π_mem (Nat.zero_le (0 + q)) _) x
    · simp
  have hb_le : ∀ q, ENNReal.ofReal |empiricalProcess P n Y (bLink q)| ≤ 3 * (⨆ i : Fin (D.partition.Nq (0 + q)),
      ENNReal.ofReal |empiricalProcess P n Y (boundedBposOsc D.partition n (0 + q) i)|) + 4 * ENNReal.ofReal (Real.sqrt n) *
        (⨆ i : Fin (D.partition.Nq (0 + q)), ∫⁻ x, ENNReal.ofReal (boundedBposOsc D.partition n (0 + q) i x) ∂P) := by
    intro q
    let g := boundedBposOsc D.partition n (0 + q) (cellChain D.partition hf q)
    have hdom := empiricalProcess_abs_le_of_abs_le P n Y (bLink q) g (hg_int q) (hg_nn q) (hb_dom q)
    calc
      ENNReal.ofReal |empiricalProcess P n Y (bLink q)| ≤ ENNReal.ofReal (|empiricalProcess P n Y g| + 2 * Real.sqrt n * ∫ x, g x ∂P) := ENNReal.ofReal_le_ofReal hdom
      _ ≤ ENNReal.ofReal |empiricalProcess P n Y g| + ENNReal.ofReal (2 * Real.sqrt n * ∫ x, g x ∂P) := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal |empiricalProcess P n Y g| + 2 * ENNReal.ofReal (Real.sqrt n) * ∫⁻ x, ENNReal.ofReal (g x) ∂P := by
          dsimp only [g]
          rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hg_int q) (Filter.Eventually.of_forall (hg_nn q))]
          simp only [ENNReal.ofReal_ofNat]
      _ ≤ 3 * (⨆ i : Fin (D.partition.Nq (0 + q)), ENNReal.ofReal |empiricalProcess P n Y
            (boundedBposOsc D.partition n (0 + q) i)|) + 4 * ENNReal.ofReal (Real.sqrt n) *
          (⨆ i : Fin (D.partition.Nq (0 + q)), ∫⁻ x, ENNReal.ofReal
            (boundedBposOsc D.partition n (0 + q) i x) ∂P) := by
          dsimp only [g]
          have h1 := le_iSup (fun i : Fin (D.partition.Nq (0 + q)) => ENNReal.ofReal
            |empiricalProcess P n Y (boundedBposOsc D.partition n (0 + q) i)|) (cellChain D.partition hf q)
          have h2 := le_iSup (fun i : Fin (D.partition.Nq (0 + q)) => ∫⁻ x, ENNReal.ofReal
            (boundedBposOsc D.partition n (0 + q) i x) ∂P) (cellChain D.partition hf q)
          have h1' : ENNReal.ofReal |empiricalProcess P n Y (boundedBposOsc D.partition n
              (0 + q) (cellChain D.partition hf q))| ≤ 3 * (⨆ i : Fin (D.partition.Nq (0 + q)),
                ENNReal.ofReal |empiricalProcess P n Y (boundedBposOsc D.partition n (0 + q) i)|) := by
            calc _ ≤ _ := h1
              _ = 1 * _ := (one_mul _).symm
              _ ≤ 3 * _ := mul_le_mul_left (by norm_num) _
          have h2' : 2 * ENNReal.ofReal (Real.sqrt n) * (∫⁻ x, ENNReal.ofReal
              (boundedBposOsc D.partition n (0 + q) (cellChain D.partition hf q) x) ∂P) ≤
              4 * ENNReal.ofReal (Real.sqrt n) * (⨆ i : Fin (D.partition.Nq (0 + q)),
                ∫⁻ x, ENNReal.ofReal (boundedBposOsc D.partition n (0 + q) i x) ∂P) := by
            refine (mul_le_mul_right h2 _).trans ?_
            exact mul_le_mul_left (mul_le_mul_left (by norm_num) _) _
          exact add_le_add h1' h2'
  have htri : ∀ (s : Finset ℕ) (v : ℕ → ℝ), ENNReal.ofReal |∑ q ∈ s, v q| ≤ ∑ q ∈ s, ENNReal.ofReal |v q| := by
    intro s v
    induction s using Finset.induction with
    | empty => simp
    | insert q s hqs ih =>
        rw [Finset.sum_insert hqs, Finset.sum_insert hqs]
        exact (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans
          (ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih))
  have ha_sum : (∑ q ∈ Finset.Icc 1 D.L, ENNReal.ofReal |empiricalProcess P n Y (aLink q)|) ≤ boundedChainAMajorant D X ξ := by
    rw [boundedChainAMajorant]
    calc
      (∑ q ∈ Finset.Icc 1 D.L, ENNReal.ofReal |empiricalProcess P n Y (aLink q)|) =
          ∑ k ∈ Finset.range D.L, ENNReal.ofReal |empiricalProcess P n Y
            (boundedAJump D.partition n (0 + k) (cellChain D.partition hf (k + 1)))| := by
            have hs : Finset.Icc 1 D.L = (Finset.range D.L).image (fun k => k + 1) := by
              ext q
              simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
              constructor
              · intro hq; exact ⟨q - 1, by omega, by omega⟩
              · rintro ⟨k, hk, rfl⟩; omega
            rw [hs, Finset.sum_image (by intro k _ l _ h; exact Nat.succ.inj h)]
            exact Finset.sum_congr rfl (fun k _ => by
              simpa only [zero_add] using congrArg
                (fun g => ENNReal.ofReal |empiricalProcess P n Y g|) (ha_eq k))
      _ ≤ ∑ k ∈ Finset.range D.L, ⨆ i : Fin (D.partition.Nq ((0 + k) + 1)), ENNReal.ofReal |empiricalProcess P n Y (boundedAJump D.partition n (0 + k) i)| := by
            exact Finset.sum_le_sum (fun k _ => le_iSup (fun i : Fin (D.partition.Nq ((0 + k) + 1)) => ENNReal.ofReal |empiricalProcess P n Y (boundedAJump D.partition n (0 + k) i)|) _)
      _ = ∑ k ∈ Finset.range D.L, ⨆ i : Fin (D.partition.Nq (k + 1)), ENNReal.ofReal |empiricalProcess P n (fun j : Fin n => X j.val ξ) (boundedAJump D.partition n k i)| := by
            dsimp only [Y]
            exact Finset.sum_congr rfl (fun k _ => by rw [show 0 + k = k by omega])
  refine ⟨hpos_int, ?_⟩
  rw [empiricalProcess_finset_sum P n Y (Finset.Icc 1 D.L) (fun q x => aLink q x + bLink q x) ht_int]
  calc
    ENNReal.ofReal |∑ q ∈ Finset.Icc 1 D.L, empiricalProcess P n Y (fun x => aLink q x + bLink q x)| ≤
        ∑ q ∈ Finset.Icc 1 D.L, ENNReal.ofReal |empiricalProcess P n Y (fun x => aLink q x + bLink q x)| := htri _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 D.L,
        (ENNReal.ofReal |empiricalProcess P n Y (aLink q)| +
          (3 * (⨆ i : Fin (D.partition.Nq (0 + q)), ENNReal.ofReal |empiricalProcess P n Y
              (boundedBposOsc D.partition n (0 + q) i)|) + 4 * ENNReal.ofReal (Real.sqrt n) *
            (⨆ i : Fin (D.partition.Nq (0 + q)), ∫⁻ x, ENNReal.ofReal
              (boundedBposOsc D.partition n (0 + q) i x) ∂P))) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          rw [empiricalProcess_add P n Y (aLink q) (bLink q)
            (ha_int q (Finset.mem_Icc.mp hq).1) (hb_int q)]
          exact (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans
            (ENNReal.ofReal_add_le.trans (add_le_add le_rfl (hb_le q)))
    _ = (∑ q ∈ Finset.Icc 1 D.L, ENNReal.ofReal |empiricalProcess P n Y (aLink q)|) +
        boundedChainBposMajorant D X ξ := by
          rw [Finset.sum_add_distrib, boundedChainBposMajorant]
          dsimp only [Y]
          congr 1
          exact Finset.sum_congr rfl (fun q _ => by rw [show 0 + q = q by omega])
    _ ≤ boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ :=
      add_le_add ha_sum le_rfl

set_option linter.style.longLine false in
omit [MeasurableSpace Ξ] in
/-- The finite telescope admits measurable head, crossing, small-link, and
remainder majorants pointwise in the sample. Measurability of every class member,
as assumed in Lemma 19.36, is used directly in this pointwise estimate. -/
theorem bounded_chain_supNorm_le_pointwise
    [IsProbabilityMeasure P]
    (D : BoundedChainingData F P δ M n)
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω} (ξ : Ξ) :
    supNormOver F (fun f => empiricalProcess P n
        (fun i : Fin n => X i.val ξ) f) ≤
      boundedChainHeadMajorant D X ξ + boundedChainB0Majorant D X ξ +
        boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ +
          boundedChainRemainderMajorant D X ξ := by
  classical
  let Y : Fin n → Ω := fun i => X i.val ξ
  refine iSup₂_le (fun f hfF => ?_)
  have hf : f ∈ truncateClass F M := by simpa only [D.truncate_eq] using hfF
  let i0 := cellChain D.partition hf 0
  let iL := cellChain D.partition hf D.L
  let head : Ω → ℝ := D.partition.π 0 i0
  let b0 : Ω → ℝ := fun x => (f x - D.partition.π 0 i0 x) * Set.indicator
    {y | boundedChainB0 D.partition n i0 y} (1 : Ω → ℝ) x
  let pos : Ω → ℝ := fun x =>
    ∑ q ∈ Finset.Icc 1 D.L,
      ((D.partition.π (0 + q) (cellChain D.partition hf q) x - D.partition.π
          (0 + (q - 1)) (cellChain D.partition hf (q - 1)) x) * Set.indicator
        {y | boundedChainA D.partition n (0 + (q - 1))
          (cellChain D.partition hf (q - 1)) y} (1 : Ω → ℝ) x +
      (f x - D.partition.π (0 + q) (cellChain D.partition hf q) x) *
        Set.indicator {y | boundedChainB D.partition n (0 + q)
          (cellChain D.partition hf q) y} (1 : Ω → ℝ) x)
  let rem : Ω → ℝ := fun x => (f x - D.partition.π (0 + D.L) iL x) * Set.indicator
    {y | boundedChainA D.partition n (0 + D.L) iL y} (1 : Ω → ℝ) x
  have hΔ_nn : ∀ q i x, 0 ≤ D.partition.Δ q i x := by
    intro q i x
    have h := D.partition.diam (Nat.zero_le q) i (D.partition.π q i)
      (D.partition.π_mem (Nat.zero_le q) i) _ (D.partition.π_mem (Nat.zero_le q) i) x
    simpa using h
  have hM : 0 ≤ M := by
    let x := (nonempty_of_isProbabilityMeasure P).some; nlinarith [hΔ_nn 0 i0 x, D.width_le 0 i0 x]
  have hhead_int : Integrable head P := by
    refine Integrable.of_bound (D.partition.π_meas (Nat.zero_le 0) i0).aestronglyMeasurable M ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact truncateClass_abs_le hM (D.partition.cell_subset (Nat.zero_le 0) i0
      (D.partition.π_mem (Nat.zero_le 0) i0)) x
  have hlink : ∀ (q : ℕ) (i : Fin (D.partition.Nq q)),
      f ∈ D.partition.cell q i → ∀ (s : Set Ω), MeasurableSet s →
      let h : Ω → ℝ := fun x => (f x - D.partition.π q i x) * s.indicator (1 : Ω → ℝ) x
      let g : Ω → ℝ := fun x => D.partition.Δ q i x * s.indicator (1 : Ω → ℝ) x
      Integrable h P ∧ Integrable g P ∧ (∀ x, 0 ≤ g x) ∧ (∀ x, |h x| ≤ g x) := by
    intro q i hfi s hs; dsimp only
    have hh_meas := ((hF_meas f hfF).sub (D.partition.π_meas (Nat.zero_le q) i)).mul (measurable_const.indicator hs : Measurable (s.indicator (1 : Ω → ℝ)))
    have hg_meas := (D.partition.Δ_meas (Nat.zero_le q) i).mul (measurable_const.indicator hs : Measurable (s.indicator (1 : Ω → ℝ)))
    have hg_nn : ∀ x, 0 ≤ D.partition.Δ q i x * s.indicator (1 : Ω → ℝ) x := by
      intro x
      exact mul_nonneg (hΔ_nn q i x) (by by_cases hx : x ∈ s <;> simp [hx])
    have hhg : ∀ x, |(f x - D.partition.π q i x) * s.indicator (1 : Ω → ℝ) x| ≤
        D.partition.Δ q i x * s.indicator (1 : Ω → ℝ) x := by
      intro x
      by_cases hx : x ∈ s
      · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
        exact D.partition.diam (Nat.zero_le q) i f hfi _ (D.partition.π_mem (Nat.zero_le q) i) x
      · simp [Set.indicator_of_notMem hx]
    have hΔ_int := (D.partition.Δ_memLp (Nat.zero_le q) i).integrable (by norm_num)
    refine ⟨Integrable.mono' hΔ_int hh_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact (hhg x).trans (by by_cases hx : x ∈ s <;> simp [Set.indicator, hx, hΔ_nn]))),
      ?_, hg_nn, hhg⟩
    refine Integrable.mono' hΔ_int hg_meas.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)]
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx, hΔ_nn]
  obtain ⟨hb0_int, hg0_int, hg0_nn, hb0_dom⟩ := hlink 0 i0 (cellChain_mem D.partition hf 0) _ (boundedChainB0_measurableSet D.partition n i0)
  obtain ⟨hrem_int, hgr_int, hgr_nn, hrem_dom⟩ := hlink (0 + D.L) iL (cellChain_mem D.partition hf D.L) _ (boundedChainA_measurableSet D.partition n _ iL)
  have hpos_data := bounded_chain_positive_sum_integrable_and_le_majorants D hF_meas (X := X) ξ f hf
  change Integrable pos P ∧ ENNReal.ofReal |empiricalProcess P n Y pos| ≤ boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ at hpos_data
  have dominated_le (h g : Ω → ℝ) (hg_int : Integrable g P) (hg_nn : ∀ x, 0 ≤ g x)
      (hhg : ∀ x, |h x| ≤ g x) (A B : ℝ≥0∞) (hA : ENNReal.ofReal |empiricalProcess P n Y g| ≤ A)
      (hB : (∫⁻ x, ENNReal.ofReal (g x) ∂P) ≤ B) :
      ENNReal.ofReal |empiricalProcess P n Y h| ≤ 3 * A + 4 * ENNReal.ofReal (Real.sqrt n) * B := by
    have hdom := empiricalProcess_abs_le_of_abs_le P n Y h g hg_int hg_nn hhg
    have h13 : (1 : ℝ≥0∞) ≤ 3 := by norm_num
    calc
      ENNReal.ofReal |empiricalProcess P n Y h| ≤ ENNReal.ofReal
          (|empiricalProcess P n Y g| + 2 * Real.sqrt n * ∫ x, g x ∂P) :=
        ENNReal.ofReal_le_ofReal hdom
      _ ≤ ENNReal.ofReal |empiricalProcess P n Y g| +
          ENNReal.ofReal (2 * Real.sqrt n * ∫ x, g x ∂P) := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal |empiricalProcess P n Y g| +
          2 * ENNReal.ofReal (Real.sqrt n) * ∫⁻ x, ENNReal.ofReal (g x) ∂P := by
            rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
              MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_int (Filter.Eventually.of_forall hg_nn)]
            simp only [ENNReal.ofReal_ofNat]
      _ ≤ 3 * A + 4 * ENNReal.ofReal (Real.sqrt n) * B := by
            have hA3 : ENNReal.ofReal |empiricalProcess P n Y g| ≤ 3 * A := by
              calc
                _ ≤ A := hA
                _ = A * 1 := (mul_one A).symm
                _ ≤ A * 3 := mul_le_mul_right h13 A
                _ = 3 * A := mul_comm _ _
            exact add_le_add hA3
              (calc
                2 * ENNReal.ofReal (Real.sqrt n) * (∫⁻ x, ENNReal.ofReal (g x) ∂P)
                    ≤ 2 * ENNReal.ofReal (Real.sqrt n) * B := by gcongr
                _ ≤ 4 * ENNReal.ofReal (Real.sqrt n) * B := by gcongr; norm_num)
  let g0 := boundedB0Osc D.partition n i0
  have hb0_le : ENNReal.ofReal |empiricalProcess P n Y b0| ≤ boundedChainB0Majorant D X ξ := by
    rw [boundedChainB0Majorant]
    apply dominated_le b0 g0 hg0_int hg0_nn hb0_dom
    · exact le_iSup (fun i : Fin (D.partition.Nq 0) => ENNReal.ofReal
        |empiricalProcess P n Y (boundedB0Osc D.partition n i)|) i0
    · exact le_iSup (fun i : Fin (D.partition.Nq 0) => ∫⁻ x,
        ENNReal.ofReal (boundedB0Osc D.partition n i x) ∂P) i0
  let gr := boundedRemainderOsc D.partition n (0 + D.L) iL
  have hrem_le : ENNReal.ofReal |empiricalProcess P n Y rem| ≤ boundedChainRemainderMajorant D X ξ := by
    rw [boundedChainRemainderMajorant, show D.L = 0 + D.L by omega]
    apply dominated_le rem gr hgr_int hgr_nn hrem_dom
    · exact le_iSup (fun i : Fin (D.partition.Nq (0 + D.L)) => ENNReal.ofReal
        |empiricalProcess P n Y (boundedRemainderOsc D.partition n (0 + D.L) i)|) iL
    · exact le_iSup (fun i : Fin (D.partition.Nq (0 + D.L)) =>
        ∫⁻ x, ENNReal.ofReal (boundedRemainderOsc D.partition n (0 + D.L) i x) ∂P) iL
  have hhead_le : ENNReal.ofReal |empiricalProcess P n Y head| ≤ boundedChainHeadMajorant D X ξ :=
    le_iSup (fun i : Fin (D.partition.Nq 0) => ENNReal.ofReal
      |empiricalProcess P n Y (D.partition.π 0 i)|) i0
  have hdecomp : f = fun x => (head x + b0 x) + pos x + rem x := by
    funext x
    simpa only [head, b0, pos, rem, i0, iL] using bounded_chain_finite_telescope D f hf x
  have hGdecomp : empiricalProcess P n Y f = (empiricalProcess P n Y head +
      empiricalProcess P n Y b0) + empiricalProcess P n Y pos + empiricalProcess P n Y rem := by
    conv_lhs => rw [hdecomp]
    rw [empiricalProcess_add P n Y (fun x => head x + b0 x + pos x) rem
        ((hhead_int.add hb0_int).add hpos_data.1) hrem_int,
      empiricalProcess_add P n Y (fun x => head x + b0 x) pos
        (hhead_int.add hb0_int) hpos_data.1,
      empiricalProcess_add P n Y head b0 hhead_int hb0_int]
  change ENNReal.ofReal |empiricalProcess P n Y f| ≤ _
  rw [hGdecomp]
  calc
    ENNReal.ofReal |(empiricalProcess P n Y head + empiricalProcess P n Y b0) +
        empiricalProcess P n Y pos + empiricalProcess P n Y rem| ≤ (ENNReal.ofReal
        |empiricalProcess P n Y head| + ENNReal.ofReal |empiricalProcess P n Y b0|) +
        ENNReal.ofReal |empiricalProcess P n Y pos| + ENNReal.ofReal |empiricalProcess P n Y rem| := by
            refine (ENNReal.ofReal_le_ofReal (abs_add_three _ _ _)).trans ?_
            calc
              _ ≤ ENNReal.ofReal (|empiricalProcess P n Y head + empiricalProcess P n Y b0| +
                  |empiricalProcess P n Y pos|) + ENNReal.ofReal |empiricalProcess P n Y rem| := ENNReal.ofReal_add_le
              _ ≤ (ENNReal.ofReal |empiricalProcess P n Y head + empiricalProcess P n Y b0| +
                  ENNReal.ofReal |empiricalProcess P n Y pos|) +
                  ENNReal.ofReal |empiricalProcess P n Y rem| := add_le_add ENNReal.ofReal_add_le le_rfl
              _ ≤ _ := add_le_add (add_le_add
                ((ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans ENNReal.ofReal_add_le)
                le_rfl) le_rfl
    _ ≤ (boundedChainHeadMajorant D X ξ + boundedChainB0Majorant D X ξ) +
        (boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ) + boundedChainRemainderMajorant D X ξ :=
      add_le_add (add_le_add (add_le_add hhead_le hb0_le) hpos_data.2) hrem_le
    _ = boundedChainHeadMajorant D X ξ + boundedChainB0Majorant D X ξ +
        boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ +
          boundedChainRemainderMajorant D X ξ := by ac_rfl

set_option linter.style.longLine false in
/-- The head and level-zero crossing have the bounded Lemma 19.36 budget.

The strict classwise `L²(P)` radius is load-bearing for the absolute head and
is supplied explicitly alongside the bounded chaining data.  Class
nonemptiness is derived internally after the public empty-class branch and is
forwarded to the entropy budget.
-/
theorem bounded_chain_head_B0_bound :
    ∃ cHB : ℝ, 0 < cHB ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (F : Set (Ω → ℝ)) (δ M : ℝ) (n : ℕ)
        (D : BoundedChainingData F P δ M n)
        (_ : F.Nonempty)
        (_ : ∀ f ∈ F, eLpNorm f 2 P < ENNReal.ofReal δ)
        (X : ℕ → Ξ → Ω) (_ : ∀ i, Measurable (X i))
        (_ : ProbabilityTheory.iIndepFun X μ)
        (_ : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (_ : μ.map (X 0) = P),
      0 < δ → 1 ≤ n →
        outerExpectation μ (fun ξ =>
          boundedChainHeadMajorant D X ξ + boundedChainB0Majorant D X ξ) ≤
          ENNReal.ofReal cHB *
          (bracketingEntropyIntegral δ F P +
            bracketingEntropyIntegral δ F P * bracketingEntropyIntegral δ F P *
              ENNReal.ofReal (M / (δ ^ 2 * Real.sqrt n))) := by
  classical
  obtain ⟨cE, hcE, hbudget⟩ := bounded_entropy_budget
  refine ⟨1000 * (1 + cE), by positivity, ?_⟩
  intro Ω _ P _ Ξ _ μ _ F δ M n D hF_ne hF_L2 X hX_meas hX_iindep hX_idem hX_law hδ hn
  set J := bracketingEntropyIntegral δ F P
  by_cases hJ : J = ⊤
  · rw [hJ, top_add, ENNReal.mul_top (by positivity : ENNReal.ofReal (1000 * (1 + cE)) ≠ 0)]
    exact le_top
  have hF_ne' := hF_ne
  obtain ⟨f₀, hf₀⟩ := hF_ne
  have hf₀t : f₀ ∈ truncateClass F M := by simpa only [D.truncate_eq] using hf₀
  obtain ⟨i₀, hi₀⟩ := D.partition.cover (le_rfl : 0 ≤ 0) f₀ hf₀t
  have hΔnn : ∀ q i x, 0 ≤ D.partition.Δ q i x := by
    intro q i x
    simpa using D.partition.diam (Nat.zero_le q) i (D.partition.π q i) (D.partition.π_mem
      (Nat.zero_le q) i) _ (D.partition.π_mem (Nat.zero_le q) i) x
  have hM : 0 ≤ M := by let x := (nonempty_of_isProbabilityMeasure P).some; nlinarith [hΔnn 0 i₀ x, D.width_le 0 i₀ x]
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn₀
  let w₀ := boundedPartitionWeight D.partition 0
  let w₁ := boundedPartitionWeight D.partition 1
  have hw₀ : 0 ≤ w₀ := by dsimp [w₀, boundedPartitionWeight]; positivity
  have hw₁ : 0 ≤ w₁ := by dsimp [w₁, boundedPartitionWeight]; positivity
  have hlog : 0 ≤ Real.log (1 + (D.partition.Nq 0 : ℝ)) := by
    apply Real.log_nonneg; have : (0 : ℝ) ≤ D.partition.Nq 0 := Nat.cast_nonneg _; linarith
  have hw₀sq : w₀ ^ 2 = Real.log (1 + (D.partition.Nq 0 : ℝ)) := by
    simpa only [w₀, boundedPartitionWeight] using Real.sq_sqrt hlog
  have hπt (i : Fin (D.partition.Nq 0)) : D.partition.π 0 i ∈ truncateClass F M := D.partition.cell_subset
    (le_rfl : 0 ≤ 0) i (D.partition.π_mem (le_rfl : 0 ≤ 0) i)
  have hπF (i : Fin (D.partition.Nq 0)) : D.partition.π 0 i ∈ F := by simpa only [D.truncate_eq] using hπt i
  have sq_integral_le (g : Ω → ℝ) (hg : MemLp g 2 P) (hgL2 : eLpNorm g 2 P ≤ ENNReal.ofReal δ) :
      ∫ x, (g x) ^ 2 ∂P ≤ δ ^ 2 := by
    have hnn : 0 ≤ ∫ x, (g x) ^ 2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
    have hsqrt : Real.sqrt (∫ x, (g x) ^ 2 ∂P) = (eLpNorm g 2 P).toReal := by
      rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      have heq : (fun x => ‖g x‖ ^ (2 : ℝ≥0∞).toReal) = (fun x => (g x) ^ 2) := by funext x; rw [htwo, Real.rpow_two, Real.norm_eq_abs, sq_abs]
      rw [heq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), htwo, Real.sqrt_eq_rpow]
      norm_num
    have hsqrt_le : Real.sqrt (∫ x, (g x) ^ 2 ∂P) ≤ δ := by
      rw [hsqrt]; exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hgL2).trans_eq (ENNReal.toReal_ofReal hδ.le)
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ x, (g x) ^ 2 ∂P)]
  have hπmem (i : Fin (D.partition.Nq 0)) : MemLp (D.partition.π 0 i) 2 P := ⟨(D.partition.π_meas
    (le_rfl : 0 ≤ 0) i).aestronglyMeasurable, (hF_L2 _ (hπF i)).trans ENNReal.ofReal_lt_top⟩
  have hπsq (i : Fin (D.partition.Nq 0)) : ∫ x, (D.partition.π 0 i x) ^ 2 ∂P ≤ δ ^ 2 :=
    sq_integral_le _ (hπmem i) (hF_L2 _ (hπF i)).le
  let g₀ : Fin (D.partition.Nq 0) → Ω → ℝ := fun i => boundedB0Osc D.partition n i
  have hg₀meas (i) : Measurable (g₀ i) := (D.partition.Δ_meas (le_rfl : 0 ≤ 0) i).mul
    (measurable_const.indicator (boundedChainB0_measurableSet D.partition n i))
  have hg₀nn (i) (x) : 0 ≤ g₀ i x := by
    dsimp only [g₀, boundedB0Osc]; exact mul_nonneg (hΔnn 0 i x)
      (by by_cases hx : boundedChainB0 D.partition n i x <;> simp [hx])
  have hΔsq (i : Fin (D.partition.Nq 0)) : ∫ x, (D.partition.Δ 0 i x) ^ 2 ∂P ≤ δ ^ 2 := sq_integral_le _
    (D.partition.Δ_memLp (le_rfl : 0 ≤ 0) i) (by simpa using D.partition.Δ_L2_le (le_rfl : 0 ≤ 0) i)
  have hg₀int (i) : Integrable (g₀ i) P := by
    refine Integrable.mono' ((D.partition.Δ_memLp (le_rfl : 0 ≤ 0) i).integrable (by norm_num))
      (hg₀meas i).aestronglyMeasurable ?_
    filter_upwards [] with x; rw [Real.norm_eq_abs, abs_of_nonneg (hg₀nn i x)]; dsimp only [g₀, boundedB0Osc]
    by_cases hx : boundedChainB0 D.partition n i x <;> simp [hx, hΔnn]
  have hg₀bdd (i) (x) : |g₀ i x| ≤ 2 * M := by
    rw [abs_of_nonneg (hg₀nn i x)]; dsimp only [g₀, boundedB0Osc]
    by_cases hx : boundedChainB0 D.partition n i x
    · simpa [hx] using D.width_le 0 i x
    · simp [hx, hM]
  have hg₀sq (i) : ∫ x, (g₀ i x) ^ 2 ∂P ≤ δ ^ 2 := by
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (D.partition.Δ_memLp (le_rfl : 0 ≤ 0) i).integrable_sq ?_).trans (hΔsq i)
    filter_upwards [] with x; dsimp only [g₀, boundedB0Osc]
    by_cases hx : boundedChainB0 D.partition n i x
    · simp [hx]
    · simp [hx, sq_nonneg]
  have hheadLeaf := finite_sup_bound_96 P hX_meas hX_iindep hX_idem hX_law
    (fun i : Fin (D.partition.Nq 0) => D.partition.π 0 i) (fun i => D.partition.π_meas
      (le_rfl : 0 ≤ 0) i) hM hδ.le (fun i x => truncateClass_abs_le hM (hπt i) x) hπsq n hn
  have hg₀Leaf := finite_sup_bound_96 P hX_meas hX_iindep hX_idem hX_law
    g₀ hg₀meas (by positivity : 0 ≤ 2 * M) hδ.le hg₀bdd hg₀sq n hn
  have hheadMeas : Measurable (boundedChainHeadMajorant D X) := Measurable.iSup (fun i =>
    bounded_measurable_ofReal_abs_empiricalProcess (P := P) hX_meas n (D.partition.π_meas (le_rfl : 0 ≤ 0) i))
  let A : Ξ → ℝ≥0∞ := fun ξ => ⨆ i : Fin (D.partition.Nq 0), ENNReal.ofReal |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g₀ i)|
  have hAmeas : Measurable A := Measurable.iSup (fun i => bounded_measurable_ofReal_abs_empiricalProcess (P := P) hX_meas n (hg₀meas i))
  have hheadInt : ∫⁻ ξ, boundedChainHeadMajorant D X ξ ∂μ ≤ ENNReal.ofReal
      (96 * (M * Real.log (1 + (D.partition.Nq 0 : ℝ)) / Real.sqrt n + δ * w₀)) := by
    refine (lintegral_mono (fun ξ => iSup_le (fun i => ENNReal.ofReal_le_ofReal
      (le_ciSup (Finite.bddAbove_range (fun i : Fin (D.partition.Nq 0) =>
        |empiricalProcess P n (fun j : Fin n => X j.val ξ) (D.partition.π 0 i)|)) i)))).trans ?_
    simpa only [Fintype.card_fin, w₀, boundedPartitionWeight] using hheadLeaf
  have hAInt : ∫⁻ ξ, A ξ ∂μ ≤ ENNReal.ofReal
      (96 * (2 * M * Real.log (1 + (D.partition.Nq 0 : ℝ)) / Real.sqrt n + δ * w₀)) := by
    refine (lintegral_mono (fun ξ => iSup_le (fun i => ENNReal.ofReal_le_ofReal
      (le_ciSup (Finite.bddAbove_range (fun i : Fin (D.partition.Nq 0) =>
        |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g₀ i)|)) i)))).trans ?_
    simpa only [Fintype.card_fin, w₀, boundedPartitionWeight] using hg₀Leaf
  obtain ⟨hδw₀, _, hsum⟩ := hbudget Ω P F δ M n D hF_ne' hδ
  have hterm₀ : ENNReal.ofReal (δ * (1 + w₁)) ≤ ENNReal.ofReal cE * J := by
    calc
      _ ≤ ∑ q ∈ Finset.range (D.L + 1), ENNReal.ofReal (boundedDyadicScale δ q *
          (1 + boundedPartitionWeight D.partition (q + 1))) := by
        have hzero := Finset.single_le_sum (s := Finset.range (D.L + 1)) (f := fun q =>
          ENNReal.ofReal (boundedDyadicScale δ q * (1 + boundedPartitionWeight D.partition (q + 1))))
          (fun q _ => zero_le) (by simp : 0 ∈ Finset.range (D.L + 1))
        simpa only [boundedDyadicScale, pow_zero, one_mul, zero_add, w₁] using hzero
      _ ≤ ENNReal.ofReal cE * J := by simpa only [J] using hsum
  have hmean : ENNReal.ofReal (Real.sqrt n) * (⨆ i : Fin (D.partition.Nq 0), ∫⁻ x,
      ENNReal.ofReal (g₀ i x) ∂P) ≤ ENNReal.ofReal cE * J := by
    rw [ENNReal.mul_iSup]
    refine (iSup_le fun i => ?_).trans hterm₀
    have hpoint : ∀ x, Real.sqrt n * δ * g₀ i x ≤ (1 + w₁) * (D.partition.Δ 0 i x) ^ 2 := by
      intro x
      by_cases hx : boundedChainB0 D.partition n i x
      · have hc : Real.sqrt n * δ / (1 + w₁) < D.partition.Δ 0 i x := by calc
            _ = Real.sqrt n * (δ / (1 + w₁)) := by ring
            _ < _ := by simpa only [boundedChainB0, boundedCrossingThreshold,
              boundedDyadicScale, pow_zero, one_mul, w₁] using hx
        have hc' := (div_lt_iff₀ (by linarith : 0 < 1 + w₁)).mp hc
        rw [show g₀ i x = D.partition.Δ 0 i x by simp [g₀, boundedB0Osc, hx]]
        nlinarith [hΔnn 0 i x]
      · rw [show g₀ i x = 0 by simp [g₀, boundedB0Osc, hx]]
        nlinarith [sq_nonneg (D.partition.Δ 0 i x)]
    have hint : Real.sqrt n * δ * ∫ x, g₀ i x ∂P ≤ (1 + w₁) *
        ∫ x, (D.partition.Δ 0 i x) ^ 2 ∂P := by
      simpa only [integral_const_mul] using integral_mono
        ((hg₀int i).const_mul _) ((D.partition.Δ_memLp
          (le_rfl : 0 ≤ 0) i).integrable_sq.const_mul _) hpoint
    have hreal : Real.sqrt n * ∫ x, g₀ i x ∂P ≤ δ * (1 + w₁) := by
      have hmul : (Real.sqrt n * ∫ x, g₀ i x ∂P) * δ ≤ (δ * (1 + w₁)) * δ := by calc
        (Real.sqrt n * ∫ x, g₀ i x ∂P) * δ = Real.sqrt n * δ * ∫ x, g₀ i x ∂P := by ring
        _ ≤ (1 + w₁) * ∫ x, (D.partition.Δ 0 i x) ^ 2 ∂P := hint
        _ ≤ (1 + w₁) * δ ^ 2 := mul_le_mul_of_nonneg_left (hΔsq i) (by linarith)
        _ = (δ * (1 + w₁)) * δ := by ring
      nlinarith
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hg₀int i) (Filter.Eventually.of_forall (hg₀nn i)),
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hreal
  let j := J.toReal
  let R := J * J * ENNReal.ofReal (M / (δ ^ 2 * Real.sqrt n))
  have hJof : ENNReal.ofReal j = J := ENNReal.ofReal_toReal hJ
  have hj : 0 ≤ j := ENNReal.toReal_nonneg
  have hδw₀r : δ * w₀ ≤ j := by
    have ht := ENNReal.toReal_mono hJ hδw₀
    change δ * w₀ ≤ j; simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le,
      ENNReal.toReal_ofReal hw₀, j, w₀] using ht
  have hMr : M * Real.log (1 + (D.partition.Nq 0 : ℝ)) / Real.sqrt n ≤ j * j * (M / (δ ^ 2 * Real.sqrt n)) := by
    rw [← hw₀sq]
    have hsquare : δ ^ 2 * w₀ ^ 2 ≤ j ^ 2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg hδ.le hw₀) hj).2 hδw₀r
    calc
      M * w₀ ^ 2 / Real.sqrt n = (M / (δ ^ 2 * Real.sqrt n)) * (δ ^ 2 * w₀ ^ 2) := by field_simp [hδ.ne', hsn.ne']
      _ ≤ (M / (δ ^ 2 * Real.sqrt n)) * j ^ 2 := by gcongr
      _ = j * j * (M / (δ ^ 2 * Real.sqrt n)) := by ring
  have hMterm : ENNReal.ofReal (M * Real.log (1 + (D.partition.Nq 0 : ℝ)) / Real.sqrt n) ≤ R := by
    refine (ENNReal.ofReal_le_ofReal hMr).trans_eq ?_
    rw [ENNReal.ofReal_mul (mul_nonneg hj hj), ENNReal.ofReal_mul hj, hJof]
  have hδterm : ENNReal.ofReal (δ * w₀) ≤ J := by
    rw [ENNReal.ofReal_mul hδ.le]; exact hδw₀
  have hhead : outerExpectation μ (boundedChainHeadMajorant D X) ≤ 96 * (R + J) := by
    rw [outerExpectation_eq_lintegral hheadMeas]; refine hheadInt.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num only [ENNReal.ofReal_ofNat]
    gcongr
  have hB₀meas : Measurable (boundedChainB0Majorant D X) := (measurable_const.mul hAmeas).add measurable_const
  have hB₀ : outerExpectation μ (boundedChainB0Majorant D X) ≤
      3 * (96 * (2 * R + J)) + 4 * ENNReal.ofReal cE * J := by
    rw [outerExpectation_eq_lintegral hB₀meas]
    change (∫⁻ ξ, 3 * A ξ + 4 * ENNReal.ofReal (Real.sqrt n) *
      (⨆ i : Fin (D.partition.Nq 0), ∫⁻ x, ENNReal.ofReal (g₀ i x) ∂P) ∂μ) ≤ _
    rw [MeasureTheory.lintegral_add_right' _ measurable_const.aemeasurable,
      MeasureTheory.lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ⊤),
      MeasureTheory.lintegral_const, measure_univ, mul_one]
    refine add_le_add (mul_le_mul_of_nonneg_left (hAInt.trans ?_) (zero_le))
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmean (zero_le (a := (4 : ℝ≥0∞))))
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
      show 2 * M * Real.log (1 + (D.partition.Nq 0 : ℝ)) / Real.sqrt n =
        2 * (M * Real.log (1 + (D.partition.Nq 0 : ℝ)) / Real.sqrt n) by ring,
      ENNReal.ofReal_mul (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    gcongr
  have hcR : (672 : ℝ≥0∞) ≤ ENNReal.ofReal (1000 * (1 + cE)) := by
    rw [show (672 : ℝ≥0∞) = ENNReal.ofReal (672 : ℝ) by norm_num]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hcE])
  have hcJ : (384 : ℝ≥0∞) + 4 * ENNReal.ofReal cE ≤
      ENNReal.ofReal (1000 * (1 + cE)) := by
    calc
      (384 : ℝ≥0∞) + 4 * ENNReal.ofReal cE = ENNReal.ofReal (384 + 4 * cE) := by
        rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 384) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hcE])
  calc
    outerExpectation μ (fun ξ => boundedChainHeadMajorant D X ξ +
        boundedChainB0Majorant D X ξ) ≤
        outerExpectation μ (boundedChainHeadMajorant D X) +
          outerExpectation μ (boundedChainB0Majorant D X) := outerExpectation_add_le _ _
    _ ≤ 96 * (R + J) + (3 * (96 * (2 * R + J)) + 4 * ENNReal.ofReal cE * J) :=
      add_le_add hhead hB₀
    _ = 672 * R + (384 + 4 * ENNReal.ofReal cE) * J := by ring
    _ ≤ ENNReal.ofReal (1000 * (1 + cE)) * R +
        ENNReal.ofReal (1000 * (1 + cE)) * J := by gcongr
    _ = ENNReal.ofReal (1000 * (1 + cE)) * (J + R) := by ring

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option linter.flexible false in
/-- The small links and positive first crossings cost only a universal
multiple of the entropy integral.  Class nonemptiness is derived internally
after the public empty-class branch and is forwarded to the entropy budget. -/
theorem bounded_chain_A_Bpos_bound :
    ∃ cAB : ℝ, 0 < cAB ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (F : Set (Ω → ℝ)) (δ M : ℝ) (n : ℕ)
        (D : BoundedChainingData F P δ M n)
        (hF_ne : F.Nonempty)
        (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P),
      0 < δ → 1 ≤ n →
        outerExpectation μ (fun ξ =>
          boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ) ≤
          ENNReal.ofReal cAB * bracketingEntropyIntegral δ F P := by
  classical
  obtain ⟨cE, hcE, hbudget⟩ := bounded_entropy_budget
  refine ⟨1000 * (1 + cE), by positivity, ?_⟩
  intro Ω _ P _ Ξ _ μ _ F δ M n D hF_ne X hX_meas hX_iindep hX_idem hX_law hδ hn
  let s : ℕ → ℝ := boundedDyadicScale δ
  let w : ℕ → ℝ := boundedPartitionWeight D.partition
  let T : ℕ → ℝ := fun q => s q * (1 + w (q + 1))
  let S : ℝ≥0∞ := ∑ q ∈ Finset.range (D.L + 1), ENNReal.ofReal (T q)
  have hs (q : ℕ) : 0 ≤ s q := by dsimp [s, boundedDyadicScale]; positivity
  have hs_pos (q : ℕ) : 0 < s q := by dsimp [s, boundedDyadicScale]; positivity
  have hw (q : ℕ) : 0 ≤ w q := by dsimp [w, boundedPartitionWeight]; positivity
  have hT (q : ℕ) : 0 ≤ T q := mul_nonneg (hs q) (by linarith [hw (q + 1)])
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog (q : ℕ) : 0 ≤ Real.log (1 + (D.partition.Nq q : ℝ)) := by
    apply Real.log_nonneg; have : (0 : ℝ) ≤ D.partition.Nq q := Nat.cast_nonneg _; linarith
  have hwsq (q : ℕ) : w q ^ 2 = Real.log (1 + (D.partition.Nq q : ℝ)) := by simpa only [w, boundedPartitionWeight] using Real.sq_sqrt (hlog q)
  have hΔnn : ∀ q i x, 0 ≤ D.partition.Δ q i x := by intro q i x; simpa using D.partition.diam (Nat.zero_le q) i (D.partition.π q i) (D.partition.π_mem (Nat.zero_le q) i) _ (D.partition.π_mem (Nat.zero_le q) i) x
  have sq_le (g : Ω → ℝ) (hg : MemLp g 2 P) (σ : ℝ) (hσ : 0 ≤ σ)
      (hgL2 : eLpNorm g 2 P ≤ ENNReal.ofReal σ) : ∫ x, (g x) ^ 2 ∂P ≤ σ ^ 2 := by
    have hnn : 0 ≤ ∫ x, (g x) ^ 2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
    have hsqrt : Real.sqrt (∫ x, (g x) ^ 2 ∂P) = (eLpNorm g 2 P).toReal := by
      rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      have heq : (fun x => ‖g x‖ ^ (2 : ℝ≥0∞).toReal) = (fun x => (g x) ^ 2) := by funext x; rw [htwo, Real.rpow_two, Real.norm_eq_abs, sq_abs]
      rw [heq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), htwo, Real.sqrt_eq_rpow]
      norm_num
    have hsqrt_le : Real.sqrt (∫ x, (g x) ^ 2 ∂P) ≤ σ := by
      rw [hsqrt]; exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hgL2).trans_eq (ENNReal.toReal_ofReal hσ)
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ x, (g x) ^ 2 ∂P)]
  have finite_level (q : ℕ) (g : Fin (D.partition.Nq (q + 1)) → Ω → ℝ) (hg_meas : ∀ i, Measurable (g i))
      (hg_bdd : ∀ i x, |g i x| ≤ Real.sqrt n * s q / (1 + w (q + 1))) (hg_var : ∀ i, ∫ x, (g i x) ^ 2 ∂P ≤ (s q) ^ 2) :
      (∫⁻ ξ, ⨆ i, ENNReal.ofReal |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)| ∂μ) ≤ 192 * ENNReal.ofReal (T q) := by
    have hleaf := finite_sup_bound_96 P hX_meas hX_iindep hX_idem hX_law g hg_meas
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hs q)) (by linarith [hw (q + 1)])) (hs q) hg_bdd hg_var n hn
    have hcancel : (Real.sqrt n * s q / (1 + w (q + 1))) * (w (q + 1)) ^ 2 / Real.sqrt n = s q * (w (q + 1)) ^ 2 / (1 + w (q + 1)) := by
      field_simp [hsn.ne', (by linarith [hw (q + 1)] : 1 + w (q + 1) ≠ 0)]
    have hfrac : s q * (w (q + 1)) ^ 2 / (1 + w (q + 1)) ≤ s q * w (q + 1) := by
      apply (div_le_iff₀ (by linarith [hw (q + 1)])).2
      nlinarith [mul_nonneg (hs q) (hw (q + 1))]
    have hreal : 96 * ((Real.sqrt n * s q / (1 + w (q + 1))) * Real.log (1 + (D.partition.Nq (q + 1) : ℝ)) / Real.sqrt n +
        s q * Real.sqrt (Real.log (1 + (D.partition.Nq (q + 1) : ℝ)))) ≤ 192 * T q := by
      rw [← hwsq (q + 1), Real.sqrt_sq (hw (q + 1)), hcancel]
      calc
        _ ≤ 96 * (s q * w (q + 1) + s q * w (q + 1)) := by gcongr
        _ ≤ 192 * T q := by dsimp only [T]; nlinarith [hs q, mul_nonneg (hs q) (hw (q + 1))]
    calc
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (⨆ i, |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|) ∂μ := lintegral_mono
        (fun ξ => iSup_le (fun i => ENNReal.ofReal_le_ofReal (le_ciSup (Finite.bddAbove_range (fun i : Fin (D.partition.Nq (q + 1)) => |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|)) i)))
      _ ≤ ENNReal.ofReal (96 * ((Real.sqrt n * s q / (1 + w (q + 1))) * Real.log (1 + (D.partition.Nq (q + 1) : ℝ)) / Real.sqrt n +
          s q * Real.sqrt (Real.log (1 + (D.partition.Nq (q + 1) : ℝ))))) := by simpa only [Fintype.card_fin] using hleaf
      _ ≤ ENNReal.ofReal (192 * T q) := ENNReal.ofReal_le_ofReal hreal
      _ = 192 * ENNReal.ofReal (T q) := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 192)]; norm_num
  have hAmeas (q : ℕ) (i : Fin (D.partition.Nq (q + 1))) : Measurable (boundedAJump D.partition n q i) := by
    exact (D.partition.jump_measurable D.partition.π_meas (Nat.zero_le q) i).mul (measurable_const.indicator (boundedChainA_measurableSet D.partition n q _))
  have hAbdd (q : ℕ) (i : Fin (D.partition.Nq (q + 1))) (x : Ω) : |boundedAJump D.partition n q i x| ≤ Real.sqrt n * s q / (1 + w (q + 1)) := by
    by_cases hx : boundedChainA D.partition n q (D.partition.parent (Nat.zero_le q) i) x
    · have hgate := hx q le_rfl
      rw [D.partition.ancestor_self (Nat.zero_le q) (D.partition.parent (Nat.zero_le q) i)] at hgate
      rw [boundedAJump, Set.indicator_of_mem (show x ∈ {y | boundedChainA D.partition n q (D.partition.parent (Nat.zero_le q) i) y} from hx), Pi.one_apply, mul_one]
      calc
        _ ≤ D.partition.Δ q (D.partition.parent (Nat.zero_le q) i) x := D.partition.jump_abs_le (Nat.zero_le q) i x
        _ ≤ Real.sqrt n * (s q / (1 + w (q + 1))) := by simpa only [s, w, boundedCrossingThreshold] using hgate
        _ = _ := by ring
    · simp [boundedAJump, hx]; exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hs q)) (by linarith [hw (q + 1)])
  have hAvar (q : ℕ) (i : Fin (D.partition.Nq (q + 1))) : ∫ x, (boundedAJump D.partition n q i x) ^ 2 ∂P ≤ (s q) ^ 2 := by
    have hj : MemLp (D.partition.jump (Nat.zero_le q) i) 2 P :=
      ⟨(D.partition.jump_measurable D.partition.π_meas (Nat.zero_le q) i).aestronglyMeasurable,
        lt_of_le_of_lt (D.partition.jump_L2_le (Nat.zero_le q) i) ENNReal.ofReal_lt_top⟩
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      hj.integrable_sq ?_).trans (sq_le _ hj _ (hs q) (by simpa only [s, boundedDyadicScale, Nat.sub_zero, mul_comm] using D.partition.jump_L2_le (Nat.zero_le q) i))
    filter_upwards [] with x
    by_cases hx : boundedChainA D.partition n q (D.partition.parent (Nat.zero_le q) i) x <;> simp [boundedAJump, hx, sq_nonneg]
  have hAlevel (q : ℕ) := finite_level q (fun i => boundedAJump D.partition n q i) (hAmeas q) (hAbdd q) (hAvar q)
  have hs_succ_le (q : ℕ) : s (q + 1) ≤ s q := by
    dsimp [s, boundedDyadicScale]; rw [pow_succ]
    nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) q) hδ.le]
  have hBmeas (q : ℕ) (i : Fin (D.partition.Nq q)) : Measurable (boundedBposOsc D.partition n q i) := (D.partition.Δ_meas (Nat.zero_le q) i).mul (measurable_const.indicator (boundedChainB_measurableSet D.partition n q i))
  have hBlevel (q : ℕ) : (∫⁻ ξ, ⨆ i : Fin (D.partition.Nq (q + 1)), ENNReal.ofReal |empiricalProcess P n (fun j : Fin n => X j.val ξ)
          (boundedBposOsc D.partition n (q + 1) i)| ∂μ) ≤ 192 * ENNReal.ofReal (T q) := by
    refine finite_level q (fun i => boundedBposOsc D.partition n (q + 1) i) (hBmeas (q + 1)) ?_ ?_
    · intro i x
      change |boundedBposOsc D.partition n (q + 1) i x| ≤ _
      by_cases hx : boundedChainB D.partition n (q + 1) i x
      · have hgate := hx.2.1 q (by omega)
        rw [D.partition.ancestor_succ_of_le (Nat.zero_le q) i q (Nat.zero_le q) le_rfl, D.partition.ancestor_self (Nat.zero_le q) (D.partition.parent (Nat.zero_le q) i)] at hgate
        rw [show boundedBposOsc D.partition n (q + 1) i x = D.partition.Δ (q + 1) i x by simp [boundedBposOsc, hx], abs_of_nonneg (hΔnn _ _ _)]
        calc
          _ ≤ D.partition.Δ q (D.partition.parent (Nat.zero_le q) i) x := by simpa only [NestedBracketPartition.parent] using D.partition.Δ_succ_le_parent (Nat.zero_le q) i x
          _ ≤ Real.sqrt n * (s q / (1 + w (q + 1))) := by simpa only [s, w, boundedCrossingThreshold] using hgate
          _ = _ := by ring
      · simp [boundedBposOsc, hx]; exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hs q)) (by linarith [hw (q + 1)])
    · intro i
      have hΔL2 : eLpNorm (D.partition.Δ (q + 1) i) 2 P ≤ ENNReal.ofReal (s q) := by
        have hbase : eLpNorm (D.partition.Δ (q + 1) i) 2 P ≤ ENNReal.ofReal (s (q + 1)) := by simpa only [s, boundedDyadicScale, Nat.sub_zero, mul_comm] using D.partition.Δ_L2_le (Nat.zero_le (q + 1)) i
        exact hbase.trans (ENNReal.ofReal_le_ofReal (hs_succ_le q))
      refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        (D.partition.Δ_memLp (Nat.zero_le (q + 1)) i).integrable_sq ?_).trans
        (sq_le _ (D.partition.Δ_memLp (Nat.zero_le (q + 1)) i) _ (hs q) hΔL2)
      filter_upwards [] with x
      by_cases hx : boundedChainB D.partition n (q + 1) i x <;> simp [boundedBposOsc, hx, sq_nonneg]
  have hBmean (q : ℕ) : ENNReal.ofReal (Real.sqrt n) * (⨆ i : Fin (D.partition.Nq q), ∫⁻ x, ENNReal.ofReal
        (boundedBposOsc D.partition n q i x) ∂P) ≤ ENNReal.ofReal (T q) := by
    rw [ENNReal.mul_iSup]
    refine iSup_le fun i => ?_
    let g := boundedBposOsc D.partition n q i
    have hgnn (x : Ω) : 0 ≤ g x := by
      dsimp only [g, boundedBposOsc]; exact mul_nonneg (hΔnn q i x) (by by_cases hx : boundedChainB D.partition n q i x <;> simp [hx])
    have hgint : Integrable g P := by
      refine Integrable.mono' ((D.partition.Δ_memLp (Nat.zero_le q) i).integrable (by norm_num)) (hBmeas q i).aestronglyMeasurable ?_
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hgnn x)]; dsimp only [g, boundedBposOsc]
      by_cases hx : boundedChainB D.partition n q i x <;> simp [hx, hΔnn]
    have hpoint (x : Ω) : Real.sqrt n * s q * g x ≤
        (1 + w (q + 1)) * (D.partition.Δ q i x) ^ 2 := by
      by_cases hx : boundedChainB D.partition n q i x
      · have hc : Real.sqrt n * s q / (1 + w (q + 1)) < D.partition.Δ q i x := by
          calc _ = Real.sqrt n * (s q / (1 + w (q + 1))) := by ring
            _ < _ := by simpa only [s, w, boundedCrossingThreshold] using hx.2.2
        have hc' := (div_lt_iff₀ (by linarith [hw (q + 1)])).mp hc
        rw [show g x = D.partition.Δ q i x by simp [g, boundedBposOsc, hx]]
        nlinarith [hΔnn q i x]
      · rw [show g x = 0 by simp [g, boundedBposOsc, hx]]; nlinarith [sq_nonneg (D.partition.Δ q i x), hw (q + 1)]
    have hint : Real.sqrt n * s q * ∫ x, g x ∂P ≤ (1 + w (q + 1)) * ∫ x, (D.partition.Δ q i x) ^ 2 ∂P := by
      simpa only [integral_const_mul] using integral_mono (hgint.const_mul _) ((D.partition.Δ_memLp (Nat.zero_le q) i).integrable_sq.const_mul _) hpoint
    have hreal : Real.sqrt n * ∫ x, g x ∂P ≤ T q := by
      have hsq := sq_le _ (D.partition.Δ_memLp (Nat.zero_le q) i) _ (hs q) (by simpa only [s, boundedDyadicScale, Nat.sub_zero, mul_comm] using D.partition.Δ_L2_le (Nat.zero_le q) i)
      have hmul : (Real.sqrt n * ∫ x, g x ∂P) * s q ≤ T q * s q := by
        calc
          _ = Real.sqrt n * s q * ∫ x, g x ∂P := by ring
          _ ≤ (1 + w (q + 1)) * ∫ x, (D.partition.Δ q i x) ^ 2 ∂P := hint
          _ ≤ (1 + w (q + 1)) * (s q) ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith [hw (q + 1)])
          _ = T q * s q := by dsimp only [T]; ring
      nlinarith [hs_pos q]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint
      (Filter.Eventually.of_forall hgnn), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hS : S ≤ ENNReal.ofReal cE * bracketingEntropyIntegral δ F P := by obtain ⟨_, _, hsum⟩ := hbudget Ω P F δ M n D hF_ne hδ; simpa only [S, T, s, w] using hsum
  have hArange : (∑ q ∈ Finset.range D.L, ENNReal.ofReal (T q)) ≤ S := Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have hshift : (∑ q ∈ Finset.range D.L, ENNReal.ofReal (T (q + 1))) ≤ S := by
    have hi : (Finset.range D.L).image (fun q => q + 1) = Finset.Icc 1 D.L := by
      ext q; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]; constructor
      · rintro ⟨k, hk, rfl⟩; omega
      · intro hq; exact ⟨q - 1, by omega, by omega⟩
    calc
      _ = ∑ q ∈ Finset.Icc 1 D.L, ENNReal.ofReal (T q) := by rw [← hi, Finset.sum_image (by intro a _ b _ h; exact Nat.add_right_cancel h)]
      _ ≤ S := by apply Finset.sum_le_sum_of_subset; intro q hq; exact Finset.mem_range.mpr (by simp only [Finset.mem_Icc] at hq; omega)
  have hAMeas : Measurable (boundedChainAMajorant D X) := by
    unfold boundedChainAMajorant; exact Finset.measurable_sum _ (fun q _ => Measurable.iSup (fun i =>
      bounded_measurable_ofReal_abs_empiricalProcess (P := P) hX_meas n (hAmeas q i)))
  have hA : outerExpectation μ (boundedChainAMajorant D X) ≤ 192 * S := by
    rw [outerExpectation_eq_lintegral hAMeas]; unfold boundedChainAMajorant; rw [MeasureTheory.lintegral_finset_sum (Finset.range D.L)]
    · calc
        _ ≤ ∑ q ∈ Finset.range D.L, 192 * ENNReal.ofReal (T q) := Finset.sum_le_sum (fun q _ => hAlevel q)
        _ = 192 * ∑ q ∈ Finset.range D.L, ENNReal.ofReal (T q) := by rw [Finset.mul_sum]
        _ ≤ 192 * S := mul_le_mul_of_nonneg_left hArange (zero_le)
    · intro q _; exact Measurable.iSup (fun i => bounded_measurable_ofReal_abs_empiricalProcess (P := P) hX_meas n (hAmeas q i))
  have hBMeas : Measurable (boundedChainBposMajorant D X) := by
    unfold boundedChainBposMajorant; exact Finset.measurable_sum _ (fun q _ => (measurable_const.mul (Measurable.iSup (fun i =>
      bounded_measurable_ofReal_abs_empiricalProcess (P := P) hX_meas n (hBmeas q i)))).add measurable_const)
  have hB : outerExpectation μ (boundedChainBposMajorant D X) ≤ 580 * S := by
    rw [outerExpectation_eq_lintegral hBMeas]; unfold boundedChainBposMajorant; rw [MeasureTheory.lintegral_finset_sum (Finset.Icc 1 D.L)]
    · calc
        _ ≤ ∑ q ∈ Finset.Icc 1 D.L,
            (3 * (192 * ENNReal.ofReal (T (q - 1))) + 4 * ENNReal.ofReal (T q)) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := (Finset.mem_Icc.mp hq).1; omega⟩
          rw [MeasureTheory.lintegral_add_right' _ measurable_const.aemeasurable,
            MeasureTheory.lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ⊤),
            MeasureTheory.lintegral_const, measure_univ, mul_one]
          exact add_le_add (mul_le_mul_of_nonneg_left (hBlevel k) (zero_le)) (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hBmean (k + 1)) (zero_le (a := (4 : ℝ≥0∞))))
        _ = ∑ q ∈ Finset.range D.L,
            (3 * (192 * ENNReal.ofReal (T q)) + 4 * ENNReal.ofReal (T (q + 1))) := by
          rw [show Finset.Icc 1 D.L = (Finset.range D.L).image (fun q => q + 1) by
            ext q; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]; constructor
            · intro hq; exact ⟨q - 1, by omega, by omega⟩
            · rintro ⟨k, hk, rfl⟩; omega,
            Finset.sum_image (by intro a _ b _ h; exact Nat.add_right_cancel h)]
          exact Finset.sum_congr rfl (fun q _ => by rw [Nat.add_sub_cancel])
        _ = 576 * (∑ q ∈ Finset.range D.L, ENNReal.ofReal (T q)) +
            4 * (∑ q ∈ Finset.range D.L, ENNReal.ofReal (T (q + 1))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]; ring
        _ ≤ 576 * S + 4 * S := add_le_add (mul_le_mul_of_nonneg_left hArange (zero_le)) (mul_le_mul_of_nonneg_left hshift (zero_le))
        _ = 580 * S := by ring
    · intro q _; exact (measurable_const.mul (Measurable.iSup (fun i => bounded_measurable_ofReal_abs_empiricalProcess (P := P) hX_meas n (hBmeas q i)))).add measurable_const
  have hc : (772 : ℝ≥0∞) * ENNReal.ofReal cE ≤ ENNReal.ofReal (1000 * (1 + cE)) := by
    calc _ = ENNReal.ofReal (772 * cE) := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 772)]; norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hcE])
  calc
    outerExpectation μ (fun ξ => boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ) ≤
        outerExpectation μ (boundedChainAMajorant D X) + outerExpectation μ (boundedChainBposMajorant D X) := outerExpectation_add_le _ _
    _ ≤ 192 * S + 580 * S := add_le_add hA hB
    _ = 772 * S := by ring
    _ ≤ 772 * (ENNReal.ofReal cE * bracketingEntropyIntegral δ F P) := by gcongr
    _ = (772 * ENNReal.ofReal cE) * bracketingEntropyIntegral δ F P := by ring
    _ ≤ ENNReal.ofReal (1000 * (1 + cE)) * bracketingEntropyIntegral δ F P := by gcongr

/-- The terminal `A_L` remainder is bounded by five times the stopping endpoint,
with no `M` in the stopping rule. The literal majorant spends `3 * 2 + 4 = 10`
units while the endpoint pays `2`, which gives the factor `5`. -/
theorem bounded_chain_remainder_bound
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (D : BoundedChainingData F P δ M n)
    (X : ℕ → Ξ → Ω) :
    0 < δ → 1 ≤ n →
      outerExpectation μ (boundedChainRemainderMajorant D X) ≤
        5 * bracketingEntropyIntegral δ F P := by
  classical
  intro hδ hn
  let r := boundedDyadicScale δ D.L
  let g : Fin (D.partition.Nq D.L) → Ω → ℝ :=
    fun i => boundedRemainderOsc D.partition n D.L i
  have hr : 0 ≤ r := by dsimp [r, boundedDyadicScale]; positivity
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hsqrt_sq : (Real.sqrt n) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hw : 0 ≤ boundedPartitionWeight D.partition (D.L + 1) := by
    dsimp [boundedPartitionWeight]
    positivity
  have hcross : boundedCrossingThreshold D.partition D.L ≤ r := by
    dsimp [boundedCrossingThreshold, r]
    apply (div_le_iff₀ (by linarith)).2
    nlinarith [mul_nonneg hr hw]
  have hΔnn (i : Fin (D.partition.Nq D.L)) (x : Ω) :
      0 ≤ D.partition.Δ D.L i x := by
    simpa using D.partition.diam (Nat.zero_le D.L) i
      (D.partition.π D.L i) (D.partition.π_mem (Nat.zero_le D.L) i)
      _ (D.partition.π_mem (Nat.zero_le D.L) i) x
  have hgate (i : Fin (D.partition.Nq D.L)) (x : Ω)
      (hx : boundedChainA D.partition n D.L i x) :
      D.partition.Δ D.L i x ≤ Real.sqrt n * r := by
    have hxL := hx D.L le_rfl
    rw [D.partition.ancestor_self (Nat.zero_le D.L) i] at hxL
    exact hxL.trans (mul_le_mul_of_nonneg_left hcross (Real.sqrt_nonneg _))
  have hg_meas (i : Fin (D.partition.Nq D.L)) : Measurable (g i) := by
    exact (D.partition.Δ_meas (Nat.zero_le D.L) i).mul
      (measurable_const.indicator
        (boundedChainA_measurableSet D.partition n D.L i))
  have hg_nn (i : Fin (D.partition.Nq D.L)) (x : Ω) : 0 ≤ g i x := by
    dsimp [g, boundedRemainderOsc]
    by_cases hx : boundedChainA D.partition n D.L i x
    · simp [hx, hΔnn i x]
    · simp [hx]
  have hg_le (i : Fin (D.partition.Nq D.L)) (x : Ω) :
      g i x ≤ Real.sqrt n * r := by
    dsimp [g, boundedRemainderOsc]
    by_cases hx : boundedChainA D.partition n D.L i x
    · simpa [hx] using hgate i x hx
    · simp [hx, mul_nonneg (Real.sqrt_nonneg _) hr]
  have hg_int (i : Fin (D.partition.Nq D.L)) : Integrable (g i) P := by
    refine Integrable.of_bound (hg_meas i).aestronglyMeasurable
      (Real.sqrt n * r) ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn i x)]
    exact hg_le i x
  have hg_int_le (i : Fin (D.partition.Nq D.L)) :
      ∫ x, g i x ∂P ≤ Real.sqrt n * r := by
    calc
      ∫ x, g i x ∂P ≤ ∫ _, Real.sqrt n * r ∂P :=
        integral_mono (hg_int i) (integrable_const _) (hg_le i)
      _ = Real.sqrt n * r := by simp
  have havg_nn (i : Fin (D.partition.Nq D.L)) (Y : Fin n → Ω) :
      0 ≤ empiricalAvg (g i) n Y := by
    unfold empiricalAvg
    exact mul_nonneg (inv_nonneg.mpr hnR.le)
      (Finset.sum_nonneg (fun j _ => hg_nn i (Y j)))
  have havg_le (i : Fin (D.partition.Nq D.L)) (Y : Fin n → Ω) :
      empiricalAvg (g i) n Y ≤ Real.sqrt n * r := by
    unfold empiricalAvg
    calc
      (n : ℝ)⁻¹ * ∑ j, g i (Y j) ≤
          (n : ℝ)⁻¹ * ∑ _j : Fin n, Real.sqrt n * r := by
        apply mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun j _ => hg_le i (Y j)))
          (inv_nonneg.mpr hnR.le)
      _ = Real.sqrt n * r := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        field_simp [hnR.ne']
  have hG (i : Fin (D.partition.Nq D.L)) (Y : Fin n → Ω) :
      |empiricalProcess P n Y (g i)| ≤ 2 * (n : ℝ) * r := by
    have hint_nn : 0 ≤ ∫ x, g i x ∂P := integral_nonneg (hg_nn i)
    have hcenter :
        |empiricalAvg (g i) n Y - ∫ x, g i x ∂P| ≤
          2 * Real.sqrt n * r := by
      calc
        _ ≤ |empiricalAvg (g i) n Y| + |∫ x, g i x ∂P| := abs_sub _ _
        _ = empiricalAvg (g i) n Y + ∫ x, g i x ∂P := by
          rw [abs_of_nonneg (havg_nn i Y), abs_of_nonneg hint_nn]
        _ ≤ 2 * Real.sqrt n * r := by
          linarith [havg_le i Y, hg_int_le i]
    unfold empiricalProcess
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt n * |empiricalAvg (g i) n Y - ∫ x, g i x ∂P| ≤
          Real.sqrt n * (2 * Real.sqrt n * r) :=
        mul_le_mul_of_nonneg_left hcenter (Real.sqrt_nonneg _)
      _ = 2 * (n : ℝ) * r := by
        nlinarith
  have hmean : ENNReal.ofReal (Real.sqrt n) *
      (⨆ i : Fin (D.partition.Nq D.L),
        ∫⁻ x, ENNReal.ofReal (g i x) ∂P) ≤
        ENNReal.ofReal ((n : ℝ) * r) := by
    rw [ENNReal.mul_iSup]
    refine iSup_le fun i => ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hg_int i)
      (Filter.Eventually.of_forall (hg_nn i)),
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      Real.sqrt n * ∫ x, g i x ∂P ≤
          Real.sqrt n * (Real.sqrt n * r) :=
        mul_le_mul_of_nonneg_left (hg_int_le i) (Real.sqrt_nonneg _)
      _ = (n : ℝ) * r := by nlinarith
  have hpoint : boundedChainRemainderMajorant D X ≤
      fun _ => 5 * ENNReal.ofReal (2 * (n : ℝ) * r) := by
    intro ξ
    have hsup : (⨆ i : Fin (D.partition.Nq D.L), ENNReal.ofReal
        |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|) ≤
        ENNReal.ofReal (2 * (n : ℝ) * r) :=
      iSup_le (fun i => ENNReal.ofReal_le_ofReal (hG i _))
    rw [boundedChainRemainderMajorant]
    change 3 * (⨆ i, ENNReal.ofReal
        |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|) +
      4 * ENNReal.ofReal (Real.sqrt n) *
        (⨆ i, ∫⁻ x, ENNReal.ofReal (g i x) ∂P) ≤ _
    calc
      _ ≤ 3 * ENNReal.ofReal (2 * (n : ℝ) * r) +
          4 * ENNReal.ofReal ((n : ℝ) * r) :=
        add_le_add (mul_le_mul_of_nonneg_left hsup (zero_le))
          (by simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hmean (zero_le (a := (4 : ℝ≥0∞))))
      _ = 5 * ENNReal.ofReal (2 * (n : ℝ) * r) := by
        rw [show 2 * (n : ℝ) * r = 2 * ((n : ℝ) * r) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat]
        ring
  calc
    outerExpectation μ (boundedChainRemainderMajorant D X) ≤
        outerExpectation μ (fun _ => 5 * ENNReal.ofReal
          (2 * (n : ℝ) * r)) := outerExpectation_mono hpoint
    _ = 5 * ENNReal.ofReal (2 * (n : ℝ) * r) := by
      rw [outerExpectation_const, measure_univ, mul_one]
    _ ≤ 5 * bracketingEntropyIntegral δ F P := by
      gcongr
      simpa only [r] using D.endpoint

/-- Partition-level bounded bracketing maximal inequality. The measurability
premise gives pointwise majorization, while the strict classwise `L²(P)` radius
gives the absolute-head bound. Class nonemptiness is derived after treating the
empty-class case. -/
theorem bracketingMaximal_of_boundedChainingData :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (F : Set (Ω → ℝ)) (δ M : ℝ) (n : ℕ)
        (_ : BoundedChainingData F P δ M n)
        (_ : F.Nonempty)
        (_ : ∀ f ∈ F, Measurable f)
        (_ : ∀ f ∈ F, eLpNorm f 2 P < ENNReal.ofReal δ)
        (X : ℕ → Ξ → Ω) (_ : ∀ i, Measurable (X i))
        (_ : ProbabilityTheory.iIndepFun X μ)
        (_ : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (_ : μ.map (X 0) = P) (_ : 0 < δ) (_ : 1 ≤ n),
      outerExpectation μ (fun ξ => supNormOver F (fun f =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) ≤
        ENNReal.ofReal C * bracketingEntropyIntegral δ F P *
          (1 + bracketingEntropyIntegral δ F P *
            ENNReal.ofReal (M / (δ ^ 2 * Real.sqrt n))) := by
  classical
  obtain ⟨cHB, hcHB, hHB⟩ := bounded_chain_head_B0_bound
  obtain ⟨cAB, hcAB, hAB⟩ := bounded_chain_A_Bpos_bound
  refine ⟨cHB + cAB + 5, by positivity, ?_⟩
  intro Ω _ P _ Ξ _ μ _ F δ M n D hF_ne hF_meas hF_L2 X
    hX_meas hX_iindep hX_idem hX_law hδ hn
  let J := bracketingEntropyIntegral δ F P
  let m := ENNReal.ofReal (M / (δ ^ 2 * Real.sqrt n))
  let T := J * (1 + J * m)
  let H : Ξ → ℝ≥0∞ := fun ξ =>
    boundedChainHeadMajorant D X ξ + boundedChainB0Majorant D X ξ
  let A : Ξ → ℝ≥0∞ := fun ξ =>
    boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ
  let R : Ξ → ℝ≥0∞ := boundedChainRemainderMajorant D X
  have hpoint : (fun ξ => supNormOver F (fun f =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) ≤
      fun ξ => (H ξ + A ξ) + R ξ := by
    intro ξ
    calc
      _ ≤ boundedChainHeadMajorant D X ξ + boundedChainB0Majorant D X ξ +
          boundedChainAMajorant D X ξ + boundedChainBposMajorant D X ξ +
            boundedChainRemainderMajorant D X ξ :=
        bounded_chain_supNorm_le_pointwise D hF_meas ξ
      _ = (H ξ + A ξ) + R ξ := by
        dsimp only [H, A, R]
        ac_rfl
  have hHB' : outerExpectation μ H ≤ ENNReal.ofReal cHB * T := by
    calc
      outerExpectation μ H ≤ ENNReal.ofReal cHB *
          (J + J * J * m) := by
        simpa only [H, J, m] using hHB Ω P Ξ μ F δ M n D hF_ne
          hF_L2 X hX_meas hX_iindep hX_idem hX_law hδ hn
      _ = ENNReal.ofReal cHB * T := by
        dsimp only [T]
        ring
  have hAB' : outerExpectation μ A ≤ ENNReal.ofReal cAB * J := by
    simpa only [A, J] using hAB Ω P Ξ μ F δ M n D hF_ne X
      hX_meas hX_iindep hX_idem hX_law hδ hn
  have hR' : outerExpectation μ R ≤ 5 * J := by
    simpa only [R, J] using bounded_chain_remainder_bound D X hδ hn
  have hJT : J ≤ T := by
    dsimp only [T]
    calc
      J = J * 1 := (mul_one J).symm
      _ ≤ J * (1 + J * m) :=
        mul_le_mul_right (le_add_of_nonneg_right (zero_le)) J
  have hCof : ENNReal.ofReal (cHB + cAB + 5) =
      ENNReal.ofReal cHB + ENNReal.ofReal cAB + 5 := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_add hcHB.le hcAB.le]
    norm_num
  calc
    outerExpectation μ (fun ξ => supNormOver F (fun f =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) ≤
        outerExpectation μ (fun ξ => (H ξ + A ξ) + R ξ) :=
      outerExpectation_mono hpoint
    _ ≤ outerExpectation μ (fun ξ => H ξ + A ξ) + outerExpectation μ R :=
      outerExpectation_add_le _ _
    _ ≤ (outerExpectation μ H + outerExpectation μ A) +
        outerExpectation μ R :=
      add_le_add (outerExpectation_add_le H A) le_rfl
    _ ≤ (ENNReal.ofReal cHB * T + ENNReal.ofReal cAB * J) + 5 * J :=
      add_le_add (add_le_add hHB' hAB') hR'
    _ ≤ (ENNReal.ofReal cHB * T + ENNReal.ofReal cAB * T) + 5 * T :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hJT (zero_le)))
        (mul_le_mul_of_nonneg_left hJT (zero_le))
    _ = ENNReal.ofReal (cHB + cAB + 5) * T := by
      rw [hCof]
      ring
    _ = ENNReal.ofReal (cHB + cAB + 5) * J * (1 + J * m) := by
      dsimp only [T]
      ring

end AsymptoticStatistics.EmpiricalProcess
