module
public import StatLean.AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterizationNondominated
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import StatLean.AsymptoticStatistics.ForMathlib.CramerWoldEuclidean
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

@[expose] public section

/-! # Full vector nondominated Lemma 25.23 -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterizationVecNondominated

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.Core.NondominatedTangent
open AsymptoticStatistics.Core.NondominatedPathwise
open AsymptoticStatistics.Core.NondominatedEfficiencyOperational
open AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterizationNondominated

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}

/-- Coordinate projection of nondominated vector pathwise differentiability.

Proof idea: compose the derivative with `EuclideanSpace.proj i` and project
the selected-path quotient. -/
noncomputable def nondominatedPathwiseDifferentiableAt_coordinate
    (C : NondominatedTangentCone P)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ) (i : Fin d) :
    NondominatedPathwiseDifferentiableAt P C (fun Q => ψ Q i) := by
  refine
    { derivative := EuclideanSpace.proj i ∘L hpd.derivative
      derivative_spec := ?_ }
  intro g
  have hvec := hpd.derivative_spec g
  have hcoord :=
    ((EuclideanSpace.proj i).continuous.tendsto
      (hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)).comp hvec
  convert! hcoord using 1
  ext t
  simp [div_eq_mul_inv, mul_comm]

/-- Coordinate extraction from a vector EIF.

Proof idea: unfold the componentwise vector EIF definition. -/
theorem nondominated_eif_coordinate
    (C : NondominatedTangentCone P)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    (φ : Fin d → ↥(L2ZeroMean P))
    (hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ) (i : Fin d) :
    IsEfficientInfluenceFunction P (tangentSpace C)
      (EuclideanSpace.proj i ∘L hpd.derivative) (φ i) := by
  exact hEIF i

/-- Coordinate projection of vector nondominated regularity.

Proof idea: use `Measure.map_map` to compose the measurable vector statistic
with the continuous coordinate projection, then map every weak limit. -/
theorem isRegularAtND_coordinate
    (C : NondominatedTangentCone P)
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    {L : Measure (EuclideanSpace ℝ (Fin d))}
    (hT : ∀ n, Measurable (T_n n))
    (hreg : IsRegularAtNDVec C T_n ψ L) (i : Fin d) :
    IsRegularAtND C (fun n X => T_n n X i) (fun Q => ψ Q i)
      (L.map (fun z => z i)) := by
  intro g
  have hpushed := (hreg g).map (f := fun z => z i)
    (by fun_prop) (by fun_prop)
  have hmap : ∀ n : ℕ,
      ((Measure.pi (fun _ : Fin n =>
          (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
        (fun X => Real.sqrt n •
          (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹))))).map
        (fun z => z i) =
      (Measure.pi (fun _ : Fin n =>
          (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
        (fun X => Real.sqrt n *
          (T_n n X i - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)) i)) := by
    intro n
    have hvecmeas : Measurable (fun X : Fin n → Ω => Real.sqrt n •
        (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)))) :=
      measurable_const.fun_smul ((hT n).fun_sub measurable_const)
    have hcoordmeas : Measurable
        (fun z : EuclideanSpace ℝ (Fin d) => z i) := by fun_prop
    rw [Measure.map_map hcoordmeas hvecmeas]
    congr 1
  have hfun :
      (fun n : ℕ =>
        ((Measure.pi (fun _ : Fin n =>
            (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n •
            (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹))))).map
          (fun z => z i)) =
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n =>
            (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n *
            (T_n n X i - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)) i))) :=
    funext hmap
  rw [hfun] at hpushed
  exact hpushed

private lemma vec_residual_coord
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : Fin d → ↥(L2ZeroMean P)) (c : EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) (i : Fin d) :
    (Real.sqrt n • (T_n n X - c)
        - (Real.sqrt n)⁻¹ • (∑ j, tupleEval P φ (X j))) i =
      Real.sqrt n * (T_n n X i - c i)
        - (Real.sqrt n)⁻¹ *
          (∑ j, ((φ i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j)) := by
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  rw [show (∑ j, tupleEval P φ (X j)).ofLp i =
      ∑ j, (tupleEval P φ (X j)).ofLp i by
    simp only [WithLp.ofLp_sum, Finset.sum_apply]]
  rfl

/-- Coordinate projection of vector asymptotic linearity.

Proof idea: the coordinate norm is bounded by the Euclidean norm. -/
theorem asymptoticallyLinearAt_coordinate
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    (φ : Fin d → ↥(L2ZeroMean P)) (c : EuclideanSpace ℝ (Fin d))
    (hAL : AsymptoticallyLinearAt_vec T_n P φ c) (i : Fin d) :
    AsymptoticallyLinearAt (fun n X => T_n n X i) P (φ i) (c i) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hAL ε hε)
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · refine Filter.Eventually.of_forall (fun n => measure_mono ?_)
    intro X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [← vec_residual_coord P φ c n X i] at hX
    exact hX.trans (by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ _)

/-- Cramér--Wold assembly for Euclidean weak convergence, including `d=0`.

Proof idea: the finite-dimensional Cramér--Wold theorem and continuity of
every inner-product projection. -/
theorem cramerWold_weakConverges_euclidean
    (μ : ℕ → Measure (EuclideanSpace ℝ (Fin d)))
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : ∀ u : EuclideanSpace ℝ (Fin d),
      AsymptoticStatistics.WeakConverges
        (fun n => (μ n).map (fun z => ⟪u, z⟫_ℝ))
        (ν.map (fun z => ⟪u, z⟫_ℝ))) :
    AsymptoticStatistics.WeakConverges μ ν := by
  exact AsymptoticStatistics.ForMathlib.cramerWold_weakConverges_euclidean h

/-- Every linear projection of a possibly singular Gram Gaussian is the
corresponding scalar Gaussian.

Proof idea: the characteristic function of `multivariateGaussian` and the
Gram quadratic-form identity.  No PosDef assumption; `d=0` and rank-deficient
Gram matrices are included. -/
theorem multivariateGaussian_map_inner_eq_gaussianReal
    (φ : Fin d → ↥(L2ZeroMean P)) (u : EuclideanSpace ℝ (Fin d)) :
    (multivariateGaussian 0 (Matrix.gram ℝ φ)).map (fun z => ⟪u, z⟫_ℝ) =
      gaussianReal 0
        ⟨‖∑ i, (u i) • φ i‖ ^ 2, sq_nonneg _⟩ := by
  rw [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal u
    (Matrix.posSemidef_gram ℝ φ)]
  congr 1
  apply NNReal.eq
  have hquad :
      u.ofLp ⬝ᵥ (Matrix.gram ℝ φ).mulVec u.ofLp =
        ‖∑ i, (u i) • φ i‖ ^ 2 := by
    calc
      u.ofLp ⬝ᵥ (Matrix.gram ℝ φ).mulVec u.ofLp =
          star u.ofLp ⬝ᵥ (Matrix.gram ℝ φ).mulVec u.ofLp := by
            simp
      _ = inner ℝ (∑ i, u.ofLp i • φ i) (∑ i, u.ofLp i • φ i) :=
        Matrix.star_dotProduct_gram_mulVec φ u.ofLp u.ofLp
      _ = ‖∑ i, (u i) • φ i‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
  have hnonneg : 0 ≤ u.ofLp ⬝ᵥ (Matrix.gram ℝ φ).mulVec u.ofLp := by
    simpa using (Matrix.posSemidef_gram ℝ φ).re_dotProduct_nonneg u.ofLp
  simpa [Real.coe_toNNReal _ hnonneg] using! hquad

private lemma norm_lt_of_forall_coord_lt
    (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (hd : 0 < d) (hε : 0 < ε)
    (h : ∀ i, |x i| < ε / Real.sqrt d) : ‖x‖ < ε := by
  rw [EuclideanSpace.norm_eq]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [show ε = Real.sqrt (ε ^ 2) by rw [Real.sqrt_sq hε.le]]
  apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => by positivity))
  calc
    ∑ i, ‖x.ofLp i‖ ^ 2 < ∑ _i : Fin d, (ε / Real.sqrt d) ^ 2 := by
      apply Finset.sum_lt_sum_of_nonempty
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd))
      intro i _
      rw [Real.norm_eq_abs, sq_abs]
      have hi := abs_lt.mp (h i)
      exact sq_lt_sq' hi.1 hi.2
    _ = ε ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        div_pow, Real.sq_sqrt hdR.le]
      field_simp

/-- Coordinatewise scalar AL implies vector AL in finite dimension.

Proof idea: a finite union bound and the coordinate-to-Euclidean norm
inequality.  The empty-dimensional case is immediate. -/
theorem asymptoticallyLinearAt_vec_of_forall_coord
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    (φ : Fin d → ↥(L2ZeroMean P)) (c : EuclideanSpace ℝ (Fin d))
    (h : ∀ i, AsymptoticallyLinearAt
      (fun n X => T_n n X i) P (φ i) (c i)) :
    AsymptoticallyLinearAt_vec T_n P φ c := by
  intro ε hε
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hempty : ∀ n : ℕ,
        {X : Fin n → Ω | ε ≤ ‖Real.sqrt n • (T_n n X - c)
            - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P φ (X i))‖} = ∅ := by
      intro n
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have hz : ‖Real.sqrt n • (T_n n X - c)
          - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P φ (X i))‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp
      rw [hz]
      exact hε
    simp only [hempty, measure_empty]
    exact tendsto_const_nhds
  · have hsqrt : (0 : ℝ) < Real.sqrt d :=
      Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have hcoord : ∀ i, Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε / Real.sqrt d ≤
            |Real.sqrt n * (T_n n X i - c i) - (Real.sqrt n)⁻¹ *
              (∑ j, ((φ i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j))|})
        atTop (nhds 0) := fun i => h i _ (div_pos hε hsqrt)
    rw [show (0 : ℝ≥0∞) = ∑ _i : Fin d, (0 : ℝ≥0∞) by simp]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_finset_sum Finset.univ (fun i _ => hcoord i))
    · exact Filter.Eventually.of_forall (fun _ => by simp)
    · refine Filter.Eventually.of_forall (fun n =>
        le_trans (measure_mono ?_) (measure_iUnion_fintype_le _ _))
      intro X hX
      simp only [Set.mem_setOf_eq] at hX
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      by_contra hc
      push Not at hc
      have hall : ∀ i,
          |(Real.sqrt n • (T_n n X - c)
            - (Real.sqrt n)⁻¹ • (∑ j, tupleEval P φ (X j))) i|
              < ε / Real.sqrt d := by
        intro i
        rw [vec_residual_coord P φ c]
        exact hc i
      exact absurd hX (not_le.mpr
        (norm_lt_of_forall_coord_lt _ ε hd hε hall))

/-- Vector ND regularity derives the baseline vector weak limit.

Proof idea: use the vector selected zero-path derivative to control the
functional-center displacement in every projection, apply scalar baseline
recovery, and assemble with probability-typed Cramér--Wold. -/
theorem hasLimitDistributionAtVec_of_isRegularAtNDVec
    (C : NondominatedTangentCone P)
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (L : Measure (EuclideanSpace ℝ (Fin d)))
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    (hT : ∀ n, Measurable (T_n n))
    (hreg : IsRegularAtNDVec C T_n ψ L) :
    HasLimitDistributionAtNDVec (P := P) T_n (ψ P) L := by
  let z : {g : ↥(L2ZeroMean P) // g ∈ C.carrier} := ⟨0, zero_mem C⟩
  let Q : (n : ℕ) → Measure (Fin n → Ω) := fun n =>
    Measure.pi (fun _ : Fin n =>
      (C.selectedPath z).curve ((Real.sqrt n)⁻¹))
  let F : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) := fun n X =>
    Real.sqrt n •
      (T_n n X - ψ ((C.selectedPath z).curve ((Real.sqrt n)⁻¹)))
  haveI hQprob : ∀ n, IsProbabilityMeasure (Q n) := fun n => by
    letI : IsProbabilityMeasure
        ((C.selectedPath z).curve ((Real.sqrt n)⁻¹)) :=
      (C.selectedPath z).curve_isProbability _
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    infer_instance
  have hFmeas : ∀ n, Measurable (F n) := fun n =>
    measurable_const.fun_smul ((hT n).fun_sub measurable_const)
  haveI hpushProb : ∀ n, IsProbabilityMeasure ((Q n).map (F n)) := fun n =>
    Measure.isProbabilityMeasure_map (hFmeas n).aemeasurable
  have hlocal : AsymptoticStatistics.WeakConverges
      (fun n => (Q n).map (F n)) L := by
    simpa only [Q, F] using hreg z
  have hLreal : L.real Set.univ = 1 := by
    have h := hlocal (BoundedContinuousFunction.const
      (EuclideanSpace ℝ (Fin d)) (1 : ℝ))
    have h' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (nhds (L.real Set.univ)) := by
      simpa only [BoundedContinuousFunction.const_apply', integral_const,
        smul_eq_mul, mul_one, probReal_univ] using h
    exact (tendsto_nhds_unique tendsto_const_nhds h').symm
  letI : IsProbabilityMeasure L :=
    MeasureTheory.isProbabilityMeasure_iff_real.mpr hLreal
  let μ : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun n =>
    (Measure.pi (fun _ : Fin n => P)).map
      (fun X => Real.sqrt n • (T_n n X - ψ P))
  have hμmeas : ∀ n, Measurable
      (fun X : Fin n → Ω => Real.sqrt n • (T_n n X - ψ P)) := fun n =>
    measurable_const.fun_smul ((hT n).fun_sub measurable_const)
  haveI hμprob : ∀ n, IsProbabilityMeasure (μ n) := fun n => by
    simp only [μ]
    exact Measure.isProbabilityMeasure_map (hμmeas n).aemeasurable
  refine cramerWold_weakConverges_euclidean μ L ?_
  intro u
  let Linner : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ u
  let ψu : Measure Ω → ℝ := fun R => ⟪u, ψ R⟫_ℝ
  let Tu : ∀ n, (Fin n → Ω) → ℝ := fun n X => ⟪u, T_n n X⟫_ℝ
  let hpdu : NondominatedPathwiseDifferentiableAt P C ψu :=
    { derivative := Linner.comp hpd.derivative
      derivative_spec := by
        intro g
        have hpushed := (Linner.continuous.tendsto
          (hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)).comp
            (hpd.derivative_spec g)
        convert! hpushed using 1
        ext t
        symm
        change Linner (t⁻¹ •
            (ψ ((C.selectedPath g).curve t) - ψ P)) =
          (ψu ((C.selectedPath g).curve t) - ψu P) / t
        change ⟪u, t⁻¹ •
            (ψ ((C.selectedPath g).curve t) - ψ P)⟫_ℝ =
          (ψu ((C.selectedPath g).curve t) - ψu P) / t
        rw [inner_smul_right, inner_sub_right, div_eq_inv_mul] }
  have hTu : ∀ n, Measurable (Tu n) := fun n =>
    Linner.measurable.comp (hT n)
  have hregu : IsRegularAtND C Tu ψu
      (L.map (fun v => ⟪u, v⟫_ℝ)) := by
    intro g
    have hpushed := (hreg g).map (f := fun v => ⟪u, v⟫_ℝ)
      Linner.continuous Linner.measurable
    have hmap : ∀ n : ℕ,
        ((Measure.pi (fun _ : Fin n =>
            (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n •
            (T_n n X - ψ ((C.selectedPath g).curve
              ((Real.sqrt n)⁻¹))))).map (fun v => ⟪u, v⟫_ℝ) =
        (Measure.pi (fun _ : Fin n =>
            (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n *
            (Tu n X - ψu ((C.selectedPath g).curve
              ((Real.sqrt n)⁻¹)))) := by
      intro n
      rw [Measure.map_map
        (by fun_prop : Measurable
          (fun v : EuclideanSpace ℝ (Fin d) => ⟪u, v⟫_ℝ))
        (measurable_const.fun_smul ((hT n).fun_sub measurable_const))]
      congr 1
      funext X
      change ⟪u, Real.sqrt n •
          (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)))⟫_ℝ = _
      rw [inner_smul_right, inner_sub_right]
    rw [show (fun n : ℕ =>
        ((Measure.pi (fun _ : Fin n =>
            (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n •
            (T_n n X - ψ ((C.selectedPath g).curve
              ((Real.sqrt n)⁻¹))))).map (fun v => ⟪u, v⟫_ℝ)) =
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n =>
            (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n *
            (Tu n X - ψu ((C.selectedPath g).curve
              ((Real.sqrt n)⁻¹))))) by funext n; exact hmap n] at hpushed
    exact hpushed
  have hbase := hasLimitDistributionAt_of_isRegularAtND C
    (L.map (fun v => ⟪u, v⟫_ℝ)) hpdu hTu hregu
  have hmap : ∀ n,
      (μ n).map (fun v => ⟪u, v⟫_ℝ) =
        (Measure.pi (fun _ : Fin n => P)).map
          (fun X => Real.sqrt n * (Tu n X - ψu P)) := by
    intro n
    simp only [μ]
    rw [Measure.map_map
      (by fun_prop : Measurable
        (fun v : EuclideanSpace ℝ (Fin d) => ⟪u, v⟫_ℝ)) (hμmeas n)]
    congr 1
    funext X
    change ⟪u, Real.sqrt n • (T_n n X - ψ P)⟫_ℝ = _
    rw [inner_smul_right, inner_sub_right]
  rw [show (fun n => (μ n).map (fun v => ⟪u, v⟫_ℝ)) =
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (fun X => Real.sqrt n * (Tu n X - ψu P))) by
    funext n; exact hmap n]
  exact hbase

/-- Vector AL by the EIF implies ND regularity with the possibly singular
Gram Gaussian law.

Proof idea: scalar projection forward theorems, the Gram projection identity,
and Cramér--Wold. -/
theorem regularVec_of_asymptoticallyLinearAtVecND
    (C : NondominatedTangentCone P)
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: vector pathwise differentiability and an efficient influence
    -- tuple; vdV Lemma 25.23.
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    (φ : Fin d → ↥(L2ZeroMean P))
    (hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (hT : ∀ n, Measurable (T_n n))
    (hAL : AsymptoticallyLinearAt_vec T_n P φ (ψ P)) :
    IsRegularAtNDVec C T_n ψ
      (multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
  intro g
  let μ : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun n =>
    (Measure.pi (fun _ : Fin n =>
      (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
      (fun X => Real.sqrt n •
        (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹))))
  have hμmeas : ∀ n, Measurable (fun X : Fin n → Ω =>
      Real.sqrt n •
        (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)))) := fun n =>
    measurable_const.fun_smul ((hT n).fun_sub measurable_const)
  haveI hμprob : ∀ n, IsProbabilityMeasure (μ n) := fun n => by
    letI : IsProbabilityMeasure
        ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)) :=
      (C.selectedPath g).curve_isProbability _
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    simp only [μ]
    exact Measure.isProbabilityMeasure_map (hμmeas n).aemeasurable
  refine cramerWold_weakConverges_euclidean μ
    (multivariateGaussian 0 (Matrix.gram ℝ φ)) ?_
  intro u
  let Linner : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ u
  let ψu : Measure Ω → ℝ := fun R => ⟪u, ψ R⟫_ℝ
  let Tu : ∀ n, (Fin n → Ω) → ℝ := fun n X => ⟪u, T_n n X⟫_ℝ
  let φu : ↥(L2ZeroMean P) := ∑ i, (u i) • φ i
  let hpdu : NondominatedPathwiseDifferentiableAt P C ψu :=
    { derivative := Linner.comp hpd.derivative
      derivative_spec := by
        intro v
        have hpushed := (Linner.continuous.tendsto
          (hpd.derivative ⟨v, selected_mem_tangentSpace C v⟩)).comp
            (hpd.derivative_spec v)
        convert! hpushed using 1
        ext t
        symm
        change Linner (t⁻¹ •
            (ψ ((C.selectedPath v).curve t) - ψ P)) =
          (ψu ((C.selectedPath v).curve t) - ψu P) / t
        change ⟪u, t⁻¹ •
            (ψ ((C.selectedPath v).curve t) - ψ P)⟫_ℝ =
          (ψu ((C.selectedPath v).curve t) - ψu P) / t
        rw [inner_smul_right, inner_sub_right, div_eq_inv_mul] }
  have hEIFu : IsEfficientInfluenceFunction P (tangentSpace C)
      hpdu.derivative φu := by
    refine ⟨?_, ?_⟩
    · intro v
      change ⟪(∑ i, (u i) • φ i : ↥(L2ZeroMean P)),
        (v : ↥(L2ZeroMean P))⟫_ℝ = Linner (hpd.derivative v)
      change (innerSLFlip ℝ (v : ↥(L2ZeroMean P)))
        (∑ i, (u i) • φ i) = Linner (hpd.derivative v)
      rw [map_sum]
      change ∑ i, ⟪(u i) • φ i, (v : ↥(L2ZeroMean P))⟫_ℝ =
        Linner (hpd.derivative v)
      rw [show (∑ i, ⟪(u i) • φ i,
          (v : ↥(L2ZeroMean P))⟫_ℝ) =
          ∑ i, (u i) * ⟪φ i, (v : ↥(L2ZeroMean P))⟫_ℝ by
        apply Finset.sum_congr rfl
        intro i _
        exact real_inner_smul_left (F := ↥(L2ZeroMean P))
          (φ i) (v : ↥(L2ZeroMean P)) (u i)]
      have hper : ∀ i,
          ⟪φ i, (v : ↥(L2ZeroMean P))⟫_ℝ =
            (EuclideanSpace.proj i ∘L hpd.derivative) v := fun i =>
        (hEIF i).1 v
      simp_rw [hper]
      change ∑ i, u i * (EuclideanSpace.proj i) (hpd.derivative v) =
        ⟪u, hpd.derivative v⟫_ℝ
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hproj : (EuclideanSpace.proj i) (hpd.derivative v) =
          (hpd.derivative v).ofLp i := rfl
      have hinner : inner ℝ (u.ofLp i) ((hpd.derivative v).ofLp i) =
          (hpd.derivative v).ofLp i * u.ofLp i := by rfl
      rw [hinner, hproj, mul_comm]
    · change (∑ i, (u i) • φ i : ↥(L2ZeroMean P)) ∈ tangentSpace C
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (hEIF i).2
  have hTu : ∀ n, Measurable (Tu n) := fun n =>
    Linner.measurable.comp (hT n)
  have hφeval :
      (fun x => ((φu : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x) =ᵐ[P]
        (fun x => ⟪u, tupleEval P φ x⟫_ℝ) := by
    have hcoe : ((φu : ↥(L2ZeroMean P)) : Lp ℝ 2 P) =
        ∑ i, (u i) • ((φ i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) := by
      simp only [φu]
      change (L2ZeroMean P).subtype (∑ i, (u i) • φ i) = _
      rw [map_sum]
      congr 1
    rw [hcoe]
    have hsum : ∀ (s : Finset (Fin d)) (f : Fin d → Lp ℝ 2 P),
        (⇑(∑ i ∈ s, f i) : Ω → ℝ) =ᵐ[P]
          (fun x => ∑ i ∈ s, (f i : Ω → ℝ) x) := by
      intro s f
      induction s using Finset.induction with
      | empty =>
        filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with x hx
        simp only [Finset.sum_empty]
        rw [hx]
        simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
        rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]
    refine (hsum Finset.univ
      (fun i => (u i) •
        ((φ i : ↥(L2ZeroMean P)) : Lp ℝ 2 P))).trans ?_
    have hsmul : ∀ i : Fin d,
        (⇑((u i) • ((φ i : ↥(L2ZeroMean P)) : Lp ℝ 2 P)) : Ω → ℝ)
          =ᵐ[P] (u i) •
            (⇑((φ i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) :=
      fun i => Lp.coeFn_smul _ _
    filter_upwards [ae_all_iff.mpr hsmul] with x hx
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i, Pi.smul_apply, smul_eq_mul]
    change u i * (((φ i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x) =
      (((φ i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x) * u i
    ring
  have hres : ∀ n,
      (fun X : Fin n → Ω =>
        Real.sqrt n * (Tu n X - ψu P) - (Real.sqrt n)⁻¹ *
          (∑ j, ((φu : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j)))
        =ᵐ[Measure.pi (fun _ : Fin n => P)]
      (fun X => ⟪u, Real.sqrt n • (T_n n X - ψ P) -
        (Real.sqrt n)⁻¹ • (∑ j, tupleEval P φ (X j))⟫_ℝ) := by
    intro n
    have hall : ∀ᵐ X ∂(Measure.pi (fun _ : Fin n => P)), ∀ j : Fin n,
        ((φu : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j) =
          ⟪u, tupleEval P φ (X j)⟫_ℝ := by
      rw [ae_all_iff]
      intro j
      exact hφeval.comp_tendsto
        (MeasureTheory.measurePreserving_eval
          (μ := fun _ : Fin n => P) j).quasiMeasurePreserving.tendsto_ae
    filter_upwards [hall] with X hX
    rw [inner_sub_right, inner_smul_right, inner_smul_right, inner_sub_right,
      inner_sum]
    simp_rw [hX]
    ring
  have hALu : AsymptoticallyLinearAt Tu P φu (ψu P) := by
    intro ε hε
    have hmeasure : ∀ n,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤
            |Real.sqrt n * (Tu n X - ψu P) - (Real.sqrt n)⁻¹ *
              (∑ j, ((φu : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j))|} =
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤
            |⟪u, Real.sqrt n • (T_n n X - ψ P) -
              (Real.sqrt n)⁻¹ • (∑ j, tupleEval P φ (X j))⟫_ℝ|} := by
      intro n
      apply measure_congr
      filter_upwards [hres n] with X hX
      change (ε ≤
        |Real.sqrt n * (Tu n X - ψu P) - (Real.sqrt n)⁻¹ *
          (∑ j, ((φu : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j))|) =
        (ε ≤ |⟪u, Real.sqrt n • (T_n n X - ψ P) -
          (Real.sqrt n)⁻¹ • (∑ j, tupleEval P φ (X j))⟫_ℝ|)
      rw [hX]
    simp_rw [hmeasure]
    by_cases hu : ‖u‖ = 0
    · have hu0 : u = 0 := norm_eq_zero.mp hu
      subst u
      have hset : ∀ n,
          {X : Fin n → Ω | ε ≤
            |⟪(0 : EuclideanSpace ℝ (Fin d)),
              Real.sqrt n • (T_n n X - ψ P) -
                (Real.sqrt n)⁻¹ • (∑ j, tupleEval P φ (X j))⟫_ℝ|} = ∅ := by
        intro n
        ext X
        simp only [Set.mem_setOf_eq, inner_zero_left, abs_zero,
          Set.mem_empty_iff_false, iff_false, not_le]
        exact hε
      simp only [hset, measure_empty]
      exact tendsto_const_nhds
    · have hu_pos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (hAL (ε / ‖u‖) (div_pos hε hu_pos))
      · exact Filter.Eventually.of_forall (fun _ => zero_le)
      · refine Filter.Eventually.of_forall (fun n => measure_mono ?_)
        intro X hX
        simp only [Set.mem_setOf_eq] at hX ⊢
        have hbound := abs_real_inner_le_norm u
          (Real.sqrt n • (T_n n X - ψ P) -
            (Real.sqrt n)⁻¹ • (∑ j, tupleEval P φ (X j)))
        apply (div_le_iff₀ hu_pos).2
        exact hX.trans (by simpa only [mul_comm] using hbound)
  have hscalar := regular_and_gaussian_of_asymptoticallyLinearND
    C hpdu hEIFu hTu hALu g
  have hseq : ∀ n,
      (μ n).map (fun v => ⟪u, v⟫_ℝ) =
        (Measure.pi (fun _ : Fin n =>
          (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n *
            (Tu n X - ψu ((C.selectedPath g).curve
              ((Real.sqrt n)⁻¹)))) := by
    intro n
    simp only [μ]
    rw [Measure.map_map
      (by fun_prop : Measurable
        (fun v : EuclideanSpace ℝ (Fin d) => ⟪u, v⟫_ℝ)) (hμmeas n)]
    congr 1
    funext X
    change ⟪u, Real.sqrt n •
      (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)))⟫_ℝ = _
    rw [inner_smul_right, inner_sub_right]
  have hlim := multivariateGaussian_map_inner_eq_gaussianReal φ u
  rw [show (fun n => (μ n).map (fun v => ⟪u, v⟫_ℝ)) =
      (fun n => (Measure.pi (fun _ : Fin n =>
        (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n *
            (Tu n X - ψu ((C.selectedPath g).curve
              ((Real.sqrt n)⁻¹))))) by funext n; exact hseq n]
  rw [hlim]
  simpa only [φu] using hscalar

/-- Vector nondominated regularity with the efficient Gram law implies vector
asymptotic linearity, by the scalar coordinate converse and finite-coordinate
recombination. -/
theorem asymptoticallyLinearAtVec_of_regularVecND
    (C : NondominatedTangentCone P)
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    (φ : Fin d → ↥(L2ZeroMean P))
    (hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (hT : ∀ n, Measurable (T_n n))
    (hreg : IsRegularAtNDVec C T_n ψ
      (multivariateGaussian 0 (Matrix.gram ℝ φ))) :
    AsymptoticallyLinearAt_vec T_n P φ (ψ P) := by
  apply asymptoticallyLinearAt_vec_of_forall_coord
  intro i
  let hpd_i := nondominatedPathwiseDifferentiableAt_coordinate C hpd i
  have hEIF_i : IsEfficientInfluenceFunction P (tangentSpace C)
      hpd_i.derivative (φ i) := by
    simpa only [hpd_i, nondominatedPathwiseDifferentiableAt_coordinate] using
      nondominated_eif_coordinate C hpd φ hEIF i
  have hreg_i := isRegularAtND_coordinate C hT hreg i
  have hgauss_i :
      (multivariateGaussian 0 (Matrix.gram ℝ φ)).map (fun z => z i) =
        gaussianReal 0 ⟨‖φ i‖ ^ 2, sq_nonneg _⟩ := by
    let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
    have hinner : (fun z : EuclideanSpace ℝ (Fin d) => ⟪e, z⟫_ℝ) =
        (fun z => z i) := by
      funext z
      simp only [e]
      rw [PiLp.inner_apply]
      simp only [PiLp.single_apply]
      calc
        ∑ j, inner ℝ (if j = i then 1 else 0 : ℝ) (z.ofLp j) =
            ∑ j, z.ofLp j * (if j = i then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          rfl
        _ = z.ofLp i := by simp [eq_comm]
    have hsum : ∑ j, (e j) • φ j = φ i := by
      simp [e, PiLp.single_apply, ite_smul, eq_comm]
    simpa only [hinner, hsum] using
      (multivariateGaussian_map_inner_eq_gaussianReal φ e)
  apply asymptoticallyLinear_of_regular_and_gaussianND C hpd_i hEIF_i
    (fun n => (by fun_prop))
  rwa [← hgauss_i]

/-- vdV Lemma 25.23, full vector nondominated characterization.

The covariance is the raw Gram matrix, with no closed-range or PosDef
hypothesis. Rank-deficient Gram matrices, `d=0`, and `φ=0` are in scope. -/
theorem operational_efficiency_characterization_vec_nondominated
    (C : NondominatedTangentCone P)
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: vector pathwise differentiability and an efficient influence
    -- tuple; vdV Lemma 25.23.
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    (φ : Fin d → ↥(L2ZeroMean P))
    (hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    -- LEAN-ONLY: measurability of each estimator.
    (hT : ∀ n, Measurable (T_n n)) :
    IsRegularAtNDVec C T_n ψ
        (multivariateGaussian 0 (Matrix.gram ℝ φ)) ↔
      AsymptoticallyLinearAt_vec T_n P φ (ψ P) := by
  constructor
  · exact asymptoticallyLinearAtVec_of_regularVecND C hpd φ hEIF hT
  · exact regularVec_of_asymptoticallyLinearAtVecND C hpd φ hEIF hT

end AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterizationVecNondominated
