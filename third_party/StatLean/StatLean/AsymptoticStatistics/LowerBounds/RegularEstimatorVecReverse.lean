module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorVec
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrow
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrowReverse
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrowReverseUncond
public import StatLean.AsymptoticStatistics.ForMathlib.CramerWoldEuclidean
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section

/-!
# Equivalence of the vector regular-estimator forms (chosen-family ⟺ all-paths)

This file relates the two vector-valued regular-estimator predicates:

* `IsRegularEstimator_vec` — the vdV §25.3.2 p.365 **canonical** (chosen-family,
  `∃ chosenFamily`) form;
* `IsRegularEstimator_broad_vec` — the **all-paths** (`∀ curve`) strengthening.

## Directions

* `isRegularEstimator_broad_vec_implies_vec` (**E3_vec**, trivial): the all-paths
  form implies the chosen-family form by instantiating `chosenFamily` at the
  canonical realiser `canonicalPath`.
* `scalar_narrow_of_vector_narrow` (**projection arm**): the vector chosen-family
  form projects, along any direction `λ`, to the *scalar* chosen-family form
  `IsRegularEstimator_narrow` for the scalarised functional `⟪λ, ψ⟫`. This reuses
  the `hψ_lam / hEIF_lam / hL_lam` construction of
  `ConvolutionVec.scalar_regularity_of_vector`, but threads it through the
  `∃ chosenFamily` quantifier rather than the `∀ curve` one.
* `isRegularEstimator_vec_implies_broad` (**E4_vec**, the substantive direction):
  the chosen-family form implies the all-paths conclusion (per realising curve),
  by Cramér–Wold reduction to the scalar reverse direction
  `isRegularEstimator_of_narrow`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.3.2
(paragraph preceding Theorem 25.20), generalized to vector codomain.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal MeasureTheory

namespace AsymptoticStatistics.LowerBounds.RegularEstimatorVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.PathwiseVec
open AsymptoticStatistics.Core.EIF
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.LowerBounds.RegularEstimator
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **E3_vec — the trivial direction `broad ⇒ canonical`.**

The all-paths (`∀ curve`) form `IsRegularEstimator_broad_vec` implies the
vdV-canonical chosen-family (`∃ chosenFamily`) form `IsRegularEstimator_vec`:
simply *select*, for each score direction `g`, the canonical realiser
`canonicalPath g` (which has `score = g` by `canonicalPath_score`), and read off
its weak-convergence clause from the all-paths hypothesis.

Vector analogue of the scalar `isRegularEstimator_implies_narrow`. -/
theorem isRegularEstimator_broad_vec_implies_vec
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {k : ℕ}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction_vec (P := P) (T := tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k)}
    {L : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure L]
    (h_broad : IsRegularEstimator_broad_vec P T_set ψ hψ hEIF T_n L) :
    IsRegularEstimator_vec P T_set ψ hψ hEIF T_n L := by
  refine ⟨fun g _hg => canonicalPath g, ?_, ?_⟩
  · -- Score equation: `(canonicalPath g).score = g`.
    intro g _hg
    exact canonicalPath_score g
  · -- Per-direction weak convergence: read off the all-paths hypothesis at the
    -- chosen realiser.
    intro g hg
    exact h_broad g hg (canonicalPath g) (canonicalPath_score g)

/-- **Projection arm — vector chosen-family ⇒ scalar chosen-family (per direction).**

For each direction `λ : Fin k → ℝ`, the vector chosen-family form
`IsRegularEstimator_vec` projects to the *scalar* chosen-family form
`IsRegularEstimator_narrow` for the scalarised functional
`ψ_lam := ⟪λ, ψ⟫`, scalarised estimator `T_n_lam := ⟪λ, T_n⟫`, scalarised
influence function `IF_lam := ∑ⱼ λⱼ • IF_eff j`, and pushforward limit
`L_lam := L.map ⟪λ, ·⟫`.

This is the chosen-family analogue of
`ConvolutionVec.scalar_regularity_of_vector`: Steps 1–3 (building
`hψ_lam / hEIF_lam / hL_lam`) are identical — `λ` acts on the *codomain* only, so
the score, paths and the chosen family are untouched — and Step 4 pushes the
chosen-family weak convergence through the inner-product CLM `Linner = ⟪λ, ·⟫`,
reusing the *same* chosen family supplied by the vector hypothesis. -/
theorem scalar_narrow_of_vector_narrow
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {k : ℕ}
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin k))
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_vec P T_set ψ hψ hEIF T_n L)
    (lam : Fin k → ℝ) :
    let ψ_lam : Measure Ω → ℝ := fun μ =>
      ⟪((WithLp.equiv 2 _).symm lam : EuclideanSpace ℝ (Fin k)), ψ μ⟫_ℝ
    let IF_lam : ↥(L2ZeroMean P) := ∑ j : Fin k, lam j • IF_eff j
    let T_n_lam : ∀ n, (Fin n → Ω) → ℝ := fun n X =>
      ⟪((WithLp.equiv 2 _).symm lam : EuclideanSpace ℝ (Fin k)), T_n n X⟫_ℝ
    let L_lam : Measure ℝ :=
      L.map (fun v => ⟪((WithLp.equiv 2 _).symm lam : EuclideanSpace ℝ (Fin k)), v⟫_ℝ)
    ∃ hψ_lam : PathwiseDifferentiableAt P (tangentSpace T_set) ψ_lam,
      ∃ hEIF_lam : IsEfficientInfluenceFunction P (tangentSpace T_set) hψ_lam.derivative IF_lam,
      ∃ _hL_lam : IsProbabilityMeasure L_lam,
      IsRegularEstimator_narrow P T_set ψ_lam hψ_lam hEIF_lam T_n_lam L_lam := by
  -- Notation: the lifted lambda as an element of EuclideanSpace.
  set lam_lifted : EuclideanSpace ℝ (Fin k) :=
      (WithLp.equiv 2 _).symm lam with hlam_lifted_def
  -- The inner-product CLM `v ↦ ⟪lam_lifted, v⟫_ℝ` from EuclideanSpace ℝ (Fin k) to ℝ.
  set Linner : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := innerSL ℝ lam_lifted with hLinner_def
  -- Intro the let-bound names so they appear in the goal.
  intro ψ_lam IF_lam T_n_lam L_lam
  -- ============== Step 1: build hψ_lam ==============
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- PathwiseDifferentiableAt with derivative Linner ∘L hψ.derivative.
    refine
      { derivative := Linner.comp hψ.derivative,
        derivative_spec := ?_ }
    intro γ h_in_T
    -- Vector form: t⁻¹ • (ψ(γ t) - ψ P) → hψ.derivative ⟨γ.score, _⟩
    have h_vec := hψ.derivative_spec γ h_in_T
    -- Push through continuous Linner.
    have h_pushed :
        Filter.Tendsto
          (fun t : ℝ => Linner (t⁻¹ • (ψ (γ.curve t) - ψ P)))
          (nhdsWithin 0 {0}ᶜ) (nhds (Linner (hψ.derivative ⟨γ.score, h_in_T⟩))) :=
      (Linner.continuous.tendsto _).comp h_vec
    -- Massage the integrand into scalar difference-quotient form (ψ_lam(γ t) - ψ_lam P) / t.
    have h_eq : ∀ t : ℝ,
        Linner (t⁻¹ • (ψ (γ.curve t) - ψ P))
          = (ψ_lam (γ.curve t) - ψ_lam P) / t := by
      intro t
      change ⟪lam_lifted, t⁻¹ • (ψ (γ.curve t) - ψ P)⟫_ℝ
            = (ψ_lam (γ.curve t) - ψ_lam P) / t
      rw [inner_smul_right, inner_sub_right, div_eq_inv_mul]
    have h_pushed' :
        Filter.Tendsto
          (fun t : ℝ => (ψ_lam (γ.curve t) - ψ_lam P) / t)
          (nhdsWithin 0 {0}ᶜ) (nhds (Linner (hψ.derivative ⟨γ.score, h_in_T⟩))) := by
      have : (fun t : ℝ => Linner (t⁻¹ • (ψ (γ.curve t) - ψ P))) =
              (fun t : ℝ => (ψ_lam (γ.curve t) - ψ_lam P) / t) := by
        funext t; exact h_eq t
      rwa [this] at h_pushed
    exact h_pushed'
  · -- ============== Step 2: build hEIF_lam ==============
    refine ⟨?_, ?_⟩
    · -- Representation: ∀ g : T, ⟪IF_lam, g⟫_ℝ = (Linner ∘L hψ.derivative) g.
      intro g
      change ⟪(∑ j : Fin k, lam j • IF_eff j : ↥(L2ZeroMean P)),
            (g : ↥(L2ZeroMean P))⟫_ℝ = Linner (hψ.derivative g)
      rw [sum_inner]
      simp_rw [real_inner_smul_left]
      have hEIF_per : ∀ j : Fin k,
          ⟪IF_eff j, (g : ↥(L2ZeroMean P))⟫_ℝ
            = (EuclideanSpace.proj j ∘L hψ.derivative) g := fun j => (hEIF j).1 g
      simp_rw [hEIF_per]
      change ∑ j, lam j * (EuclideanSpace.proj j) (hψ.derivative g)
            = ⟪lam_lifted, hψ.derivative g⟫_ℝ
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have h_lam : lam_lifted.ofLp j = lam j := rfl
      have h_proj : (EuclideanSpace.proj j) (hψ.derivative g) = (hψ.derivative g).ofLp j := rfl
      have h_inner_real :
          inner (𝕜 := ℝ) (lam_lifted.ofLp j) ((hψ.derivative g).ofLp j)
            = (hψ.derivative g).ofLp j * lam_lifted.ofLp j := by
        change (hψ.derivative g).ofLp j * lam_lifted.ofLp j
              = (hψ.derivative g).ofLp j * lam_lifted.ofLp j
        rfl
      rw [h_inner_real, h_lam, h_proj, mul_comm]
    · -- Membership: IF_lam = ∑ⱼ lam j • IF_eff j ∈ tangentSpace T_set.
      change (∑ j : Fin k, lam j • IF_eff j : ↥(L2ZeroMean P)) ∈ tangentSpace T_set
      apply Submodule.sum_mem
      intro j _
      exact Submodule.smul_mem _ _ (hEIF j).2
  · -- ============== Step 3: hL_lam ==============
    change IsProbabilityMeasure (L.map (fun v => ⟪lam_lifted, v⟫_ℝ))
    have h_meas : Measurable (fun v : EuclideanSpace ℝ (Fin k) =>
        ⟪lam_lifted, v⟫_ℝ) := Linner.measurable
    exact Measure.isProbabilityMeasure_map h_meas.aemeasurable
  · -- ============== Step 4: IsRegularEstimator_narrow ==============
    -- Extract the vector chosen family and reuse it verbatim (λ acts on the
    -- codomain only, so the chosen paths and their scores are unchanged).
    obtain ⟨cf, hcf_score, hcf_weak⟩ := hReg
    refine ⟨cf, hcf_score, ?_⟩
    intro g hg
    -- From vector chosen-family regularity: vec weak conv to L along `cf g hg`.
    have hRegV := hcf_weak g hg
    -- Push through Linner (continuous + measurable) to get pushforward weak conv.
    have h_pushed := hRegV.map (f := fun v => ⟪lam_lifted, v⟫_ℝ)
        Linner.continuous Linner.measurable
    -- The pushed sequence equals the scalar form.
    have h_map_eq : ∀ n : ℕ,
        ((MeasureTheory.Measure.pi
            (fun _ : Fin n => (cf g hg).curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n •
              (T_n n X - ψ ((cf g hg).curve ((Real.sqrt n)⁻¹))))).map
          (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam_lifted, v⟫_ℝ)
        = (MeasureTheory.Measure.pi
            (fun _ : Fin n => (cf g hg).curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n_lam n X - ψ_lam ((cf g hg).curve ((Real.sqrt n)⁻¹)))) := by
      intro n
      have h_inner_meas : Measurable (fun v : EuclideanSpace ℝ (Fin k) =>
          ⟪lam_lifted, v⟫_ℝ) := Linner.measurable
      have h_vec_meas : Measurable (fun X : Fin n → Ω =>
          Real.sqrt n • (T_n n X - ψ ((cf g hg).curve ((Real.sqrt n)⁻¹)))) :=
        measurable_const.fun_smul ((hT_meas n).fun_sub measurable_const)
      rw [Measure.map_map h_inner_meas h_vec_meas]
      congr 1
      funext X
      change ⟪lam_lifted, Real.sqrt n • (T_n n X - ψ ((cf g hg).curve ((Real.sqrt n)⁻¹)))⟫_ℝ
            = Real.sqrt n * (T_n_lam n X - ψ_lam ((cf g hg).curve ((Real.sqrt n)⁻¹)))
      rw [inner_smul_right, inner_sub_right]
    have h_pushed' :
        WeakConverges
          (fun n : ℕ =>
            (MeasureTheory.Measure.pi
                (fun _ : Fin n => (cf g hg).curve ((Real.sqrt n)⁻¹))).map
              (fun X : Fin n → Ω =>
                Real.sqrt n *
                  (T_n_lam n X - ψ_lam ((cf g hg).curve ((Real.sqrt n)⁻¹)))))
          L_lam := by
      have h_funext :
          (fun n : ℕ =>
            ((MeasureTheory.Measure.pi
                (fun _ : Fin n => (cf g hg).curve ((Real.sqrt n)⁻¹))).map
              (fun X : Fin n → Ω =>
                Real.sqrt n •
                  (T_n n X - ψ ((cf g hg).curve ((Real.sqrt n)⁻¹))))).map
              (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam_lifted, v⟫_ℝ)) =
          (fun n : ℕ =>
            (MeasureTheory.Measure.pi
                (fun _ : Fin n => (cf g hg).curve ((Real.sqrt n)⁻¹))).map
              (fun X : Fin n → Ω =>
                Real.sqrt n *
                  (T_n_lam n X - ψ_lam ((cf g hg).curve ((Real.sqrt n)⁻¹))))) := by
        funext n; exact h_map_eq n
      rwa [h_funext] at h_pushed
    exact h_pushed'

/-- **E4_vec — the substantive direction `canonical ⇒ broad`.**

The vdV-canonical chosen-family form `IsRegularEstimator_vec` implies the all-paths
strengthening `IsRegularEstimator_broad_vec`, with **no** dominator restriction.
The proof composes the three arms:

1. **Projection** (`scalar_narrow_of_vector_narrow`): the vector chosen-family form
   projects, along each direction `λ`, to the scalar chosen-family form.
2. **Scalar reverse** (`isRegularEstimator_of_narrow_unconditional`, dominator-free
   via the common-dominator Hellinger locality): each scalar narrow form yields the
   scalar all-paths conclusion along the *arbitrary* realising curve.
3. **Reverse Cramér–Wold** (`cramerWold_weakConverges_euclidean`): the per-direction
   scalar weak limits reassemble into the joint vector weak limit.

Together with the trivial `isRegularEstimator_broad_vec_implies_vec`, this shows the
two vector forms are equivalent — so the headline convolution theorem may present
the vdV-canonical hypothesis while the internal proof consumes the all-paths form. -/
theorem isRegularEstimator_vec_implies_broad
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {k : ℕ}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction_vec (P := P) (T := tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k)}
    {L : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_vec P T_set ψ hψ hEIF T_n L)
    (hT_meas : ∀ n, Measurable (T_n n)) :
    IsRegularEstimator_broad_vec P T_set ψ hψ hEIF T_n L := by
  intro g hg curve hscore
  -- Per-`n` vector sequence measure and its probability-measure structure.
  set μ_vec : ℕ → Measure (EuclideanSpace ℝ (Fin k)) := fun n =>
    (MeasureTheory.Measure.pi (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
      (fun X : Fin n → Ω =>
        Real.sqrt n • (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))) with hμ_vec
  have hF_vec_meas : ∀ n, Measurable (fun X : Fin n → Ω =>
      Real.sqrt n • (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))) := fun n =>
    measurable_const.fun_smul ((hT_meas n).fun_sub measurable_const)
  haveI hμ_prob : ∀ n, IsProbabilityMeasure (μ_vec n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (curve.curve ((Real.sqrt n)⁻¹)) :=
      fun _ => curve.curve_isProbability _
    rw [hμ_vec]
    exact Measure.isProbabilityMeasure_map (hF_vec_meas n).aemeasurable
  -- Reverse Cramér–Wold: reduce to per-direction scalar weak convergence.
  refine AsymptoticStatistics.ForMathlib.cramerWold_weakConverges_euclidean ?_
  intro lam
  -- Coordinates of `lam`, fed to the projection arm.
  set lam' : Fin k → ℝ := (WithLp.equiv 2 (Fin k → ℝ)) lam with hlam'
  obtain ⟨hψ_lam, hEIF_lam, hL_lam, h_narrow⟩ :=
    scalar_narrow_of_vector_narrow ψ hψ hEIF T_n hT_meas L hReg lam'
  set lam_lifted : EuclideanSpace ℝ (Fin k) :=
    (WithLp.equiv 2 (Fin k → ℝ)).symm lam' with hlam_lifted
  have h_lam_eq : lam_lifted = lam := by
    rw [hlam_lifted, hlam']; exact (WithLp.equiv 2 (Fin k → ℝ)).symm_apply_apply lam
  have hT_lam_meas : ∀ n, Measurable (fun X : Fin n → Ω => ⟪lam_lifted, T_n n X⟫_ℝ) :=
    fun n => (innerSL ℝ lam_lifted).measurable.comp (hT_meas n)
  -- Unconditional scalar narrow ⇒ broad, along the arbitrary curve `curve`.
  have h_broad := isRegularEstimator_of_narrow_unconditional
    (hEIF := hEIF_lam) h_narrow hT_lam_meas
  have h_at := h_broad g hg curve hscore
  -- Align the Cramér–Wold projected sequence/limit with the scalar ones.
  have h_seq_eq :
      (fun n => (μ_vec n).map (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam, v⟫_ℝ))
        = (fun n : ℕ =>
            (MeasureTheory.Measure.pi
                (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
              (fun X : Fin n → Ω =>
                Real.sqrt n *
                  (⟪lam_lifted, T_n n X⟫_ℝ
                    - ⟪lam_lifted, ψ (curve.curve ((Real.sqrt n)⁻¹))⟫_ℝ))) := by
    funext n
    rw [hμ_vec, Measure.map_map
      (by fun_prop : Measurable (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam, v⟫_ℝ))
      (hF_vec_meas n)]
    congr 1
    funext X
    change ⟪lam, Real.sqrt n • (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))⟫_ℝ
        = Real.sqrt n *
            (⟪lam_lifted, T_n n X⟫_ℝ
              - ⟪lam_lifted, ψ (curve.curve ((Real.sqrt n)⁻¹))⟫_ℝ)
    rw [h_lam_eq, inner_smul_right, inner_sub_right]
  have h_lim_eq :
      (L.map (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam, v⟫_ℝ))
        = L.map (fun v => ⟪lam_lifted, v⟫_ℝ) := by rw [h_lam_eq]
  rw [h_seq_eq, h_lim_eq]
  exact h_at

end AsymptoticStatistics.LowerBounds.RegularEstimatorVec
