module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation
public import StatLean.AsymptoticStatistics.ForMathlib.MeasurableSelectionRandomFunctions
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Donsker classes via the Theorem 18.14 characterization

Defines `IsPDonsker F P` for a class of measurable functions. Following
vdV §19.2, `F` is `P`-Donsker iff the empirical process `G_n f` converges in
distribution to a tight Gaussian limit in `ℓ^∞(F)`. vdV Theorem 18.14 gives an
equivalent characterization: `F` is Donsker iff (a) finite marginals
jointly satisfy the multivariate CLT, and (b) the empirical process is
asymptotically equicontinuous in the `L²(P)`-semimetric. Here `IsPDonsker` is
the conjunction of these two properties, `IsMarginalCLT` and
`IsAsymptoticallyEquicontinuous`.

The random-pair form of asymptotic equicontinuity is the standard
formulation in Vaart–Wellner, *Weak Convergence and Empirical Processes*, §2.1.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.2
(definitions) + Theorem 18.14 (characterization). Principal declarations:
`IsPDonsker`, `IsPDonsker.union`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter ProbabilityTheory Matrix
open scoped ENNReal Topology RealInnerProductSpace Matrix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Marginal covariance entry** of a finite tuple of functions under `P`:
`marginalCovEntry P f i j = P(fᵢ fⱼ) − (P fᵢ)(P fⱼ)`.

This is the `(i,j)` entry of the limiting Gaussian covariance in the
Theorem-18.14(a) marginal CLT: the empirical process `(𝔾ₙ fᵢ)ᵢ` of a P-Donsker
class converges to a centred Gaussian with this covariance (vdV §19.2,
book p.269). -/
noncomputable def marginalCovEntry
    {k : ℕ} (P : Measure Ω) (f : Fin k → (Ω → ℝ)) (i j : Fin k) : ℝ :=
  (∫ x, f i x * f j x ∂P) - (∫ x, f i x ∂P) * (∫ x, f j x ∂P)

/-- **Marginal covariance matrix** of a finite tuple of functions under `P`.
Entry `(i,j)` is `P(fᵢfⱼ) − (Pfᵢ)(Pfⱼ)` (vdV §19.2, book p.269). -/
noncomputable def marginalCovMatrix
    {k : ℕ} (P : Measure Ω) (f : Fin k → (Ω → ℝ)) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => marginalCovEntry P f i j

/-- **Coordinate vector** of a finite tuple `f : Fin k → (Ω → ℝ)` at a point
`ω : Ω`, as an element of `EuclideanSpace ℝ (Fin k)`: the `i`-th coordinate is
`f i ω`. -/
noncomputable def tupleVec
    {k : ℕ} (f : Fin k → (Ω → ℝ)) (ω : Ω) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 _).symm (fun i => f i ω)

/-- **Marginal CLT** — Theorem 18.14(a) form: every finite tuple of
functions from `F` has a joint `√n`-CLT under iid sampling from `P`, with the
Gaussian limit's covariance matrix given by `(Pfᵢfⱼ − Pfᵢ·Pfⱼ)ᵢⱼ`
(`marginalCovMatrix`).

Two conjuncts:

* **`memLp`** — every `f ∈ F` is square-integrable (`MemLp f 2 P`), without
  which the limiting covariance is undefined. It is available separately as
  the projection `IsMarginalCLT.memLp`.
* **`fdd`** — genuine finite-dimensional (marginal) convergence in
  distribution. For every finite tuple `f : Fin k → (Ω → ℝ)` valued in `F` and
  every iid sample `X : ℕ → Ξ → Ω` with law `P`, the empirical-process random
  vector `n ↦ (𝔾ₙ(f₀), …, 𝔾ₙ(f_{k-1}))` (built coordinatewise as the
  standardised sum `(√n)⁻¹ • ∑_{i<n} (tupleVec f (Xᵢ ξ) − E[tupleVec f (X₀)])`)
  converges in distribution to the centred multivariate Gaussian
  `multivariateGaussian 0 (marginalCovMatrix P f)`.

vdV §19.2 + Theorem 18.14(a) (book p.269): finite-dim joint convergence in
distribution to a tight Gaussian limit. -/
def IsMarginalCLT (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  (∀ f ∈ F, MemLp f 2 P) ∧
  (∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
      [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
      (∀ i, Measurable (X i)) →
      ProbabilityTheory.iIndepFun X μ →
      (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
      μ.map (X 0) = P →
      ∀ {k : ℕ} (f : Fin k → (Ω → ℝ)), (∀ i, f i ∈ F) →
        ∃ Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k),
          ProbabilityTheory.HasLaw Y
            (multivariateGaussian 0 (marginalCovMatrix P f))
            (multivariateGaussian 0 (marginalCovMatrix P f)) ∧
          MeasureTheory.TendstoInDistribution
            (fun (n : ℕ) ξ =>
              (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec f (X i ξ)
                - n • μ[fun ξ => tupleVec f (X 0 ξ)]))
            atTop Y (fun _ => μ) (multivariateGaussian 0 (marginalCovMatrix P f)))

/-- **Marginal CLT for an iid empirical process (`fdd` clause).**

From iid sampling `X : ℕ → Ξ → Ω` with law `P` and a finite tuple
`f : Fin k → (Ω → ℝ)` of square-integrable functions, the empirical-process
random vector converges in distribution to the centred Gaussian with covariance
`marginalCovMatrix P f`.

This is the multivariate-CLT content of Theorem 18.14(a). The proof builds the
coordinate vector
`Y i ξ := tupleVec f (X i ξ)`, transports iid / `MemLp 2` from `X` and `f`,
identifies the inner-product variance `Var[⟪t, Y 0⟫]` with the quadratic form of
`marginalCovMatrix P f` (which is positive semidefinite, being a covariance
Gram matrix), and applies the classical multivariate CLT.

vdV §19.2 + Theorem 18.14(a) (book p.269: the empirical process of a Donsker
class has Gaussian finite-dimensional marginals with covariance
`Pfᵢfⱼ − Pfᵢ·Pfⱼ`).

The proof applies the classical multivariate CLT to the iid vectors
`tupleVec f (Xᵢ ·)`, identifies their covariance with `marginalCovMatrix P f`,
and rewrites the standardized sum in empirical-process form. -/
lemma marginalCLT_fdd_of_iid
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (_hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (_hX_law : μ.map (X 0) = P)
    {k : ℕ} (f : Fin k → (Ω → ℝ)) (_hf_memLp : ∀ i, MemLp (f i) 2 P) :
    ∃ Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k),
      ProbabilityTheory.HasLaw Y
        (multivariateGaussian 0 (marginalCovMatrix P f))
        (multivariateGaussian 0 (marginalCovMatrix P f)) ∧
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ξ =>
          (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec f (X i ξ)
            - n • μ[fun ξ => tupleVec f (X 0 ξ)]))
        atTop Y (fun _ => μ) (multivariateGaussian 0 (marginalCovMatrix P f)) := by
  classical
  -- The witness for the Gaussian limit is `id`, with law `multivariateGaussian 0 …`.
  refine ⟨id, HasLaw.id, ?_⟩
  -- `μ.map (X j) = P` for every index, via `IdentDistrib` and `_hX_law`.
  have hmap : ∀ j, μ.map (X j) = P := by
    intro j
    rw [(_hX_id j).map_eq, _hX_law]
  -- `P` is a probability measure (pushforward of `μ` by the measurable `X 0`).
  haveI hP_prob : IsProbabilityMeasure P := by
    rw [← _hX_law]; exact Measure.isProbabilityMeasure_map (_hX_meas 0).aemeasurable
  -- Measurable representatives `f' i =ᵐ[P] f i` of the L²(P) tuple entries.
  set f' : Fin k → (Ω → ℝ) := fun i => (_hf_memLp i).aestronglyMeasurable.mk (f i) with hf'_def
  have hf'_meas : ∀ i, Measurable (f' i) := fun i =>
    (_hf_memLp i).aestronglyMeasurable.measurable_mk
  have hff' : ∀ i, f i =ᵐ[P] f' i := fun i => (_hf_memLp i).aestronglyMeasurable.ae_eq_mk
  have hf'_memLp : ∀ i, MemLp (f' i) 2 P := fun i =>
    (_hf_memLp i).ae_eq (hff' i)
  -- The coordinate map `tupleVec f'` is measurable (each coordinate is).
  have htv_meas : Measurable (tupleVec f') := by
    have hpi : Measurable (fun ω => (fun i => f' i ω) : Ω → (Fin k → ℝ)) :=
      measurable_pi_iff.mpr (fun i => hf'_meas i)
    exact (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.measurable.comp hpi
  -- The (measurable-representative) coordinate iid sequence `Y i ξ = tupleVec f' (X i ξ)`.
  set Y : ℕ → Ξ → EuclideanSpace ℝ (Fin k) := fun i ξ => tupleVec f' (X i ξ) with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := fun i => htv_meas.comp (_hX_meas i)
  have hY_iid : ProbabilityTheory.iIndepFun Y μ :=
    _hX_iindep.comp (fun _ => tupleVec f') (fun _ => htv_meas)
  have hY_id : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ := fun i =>
    (_hX_id i).comp htv_meas
  -- `tupleVec f' = tupleVec f` along the sample, μ-a.e.: each coordinate agrees `P`-a.e.,
  -- pulled back through `X i` (whose law is `P`).
  have hYY' : ∀ i, (fun ξ => tupleVec f (X i ξ)) =ᵐ[μ] Y i := by
    intro i
    have hcoord : ∀ j, (fun ξ => f j (X i ξ)) =ᵐ[μ] (fun ξ => f' j (X i ξ)) := by
      intro j
      exact ae_eq_comp (_hX_meas i).aemeasurable (by rw [hmap i]; exact hff' j)
    -- combine the finitely-many coordinate a.e. equalities
    have hall : ∀ᵐ ξ ∂μ, ∀ j, f j (X i ξ) = f' j (X i ξ) :=
      (ae_all_iff.mpr fun j => hcoord j)
    filter_upwards [hall] with ξ hξ
    change tupleVec f (X i ξ) = tupleVec f' (X i ξ)
    unfold tupleVec
    congr 1
    funext j
    exact hξ j
  -- `MemLp (tupleVec f') 2 P`: every coordinate is in L²(P).
  have htv_memLp : MemLp (tupleVec f') 2 P := by
    refine memLp_piLp_iff.mpr (fun i => ?_)
    have : (fun ω => tupleVec f' ω i) = f' i := rfl
    rw [this]; exact hf'_memLp i
  -- `MemLp (Y 0) 2 μ` by transporting `htv_memLp` along `X 0` (law `P`).
  have hY0_memLp : MemLp (Y 0) 2 μ := by
    have hmp : MemLp (tupleVec f') 2 (μ.map (X 0)) := by rw [hmap 0]; exact htv_memLp
    exact (memLp_map_measure_iff htv_meas.aestronglyMeasurable
      (_hX_meas 0).aemeasurable).1 hmp
  -- The covariance matrix is insensitive to the a.e.-replacement `f ↦ f'`.
  have hcov_eq : marginalCovMatrix P f' = marginalCovMatrix P f := by
    funext i j
    simp only [marginalCovMatrix, marginalCovEntry]
    have h1 : ∫ x, f' i x * f' j x ∂P = ∫ x, f i x * f j x ∂P :=
      integral_congr_ae (by filter_upwards [hff' i, hff' j] with x hi hj; rw [hi, hj])
    have h2 : ∫ x, f' i x ∂P = ∫ x, f i x ∂P :=
      integral_congr_ae ((hff' i).symm)
    have h3 : ∫ x, f' j x ∂P = ∫ x, f j x ∂P :=
      integral_congr_ae ((hff' j).symm)
    rw [h1, h2, h3]
  -- Pointwise inner-product expansion: `⟪t, tupleVec f' ω⟫ = ∑ i, t i * f' i ω`.
  have hinner_eq : ∀ (t : EuclideanSpace ℝ (Fin k)) (ω : Ω),
      ⟪t, tupleVec f' ω⟫ = ∑ i, t i * f' i ω := by
    intro t ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (f' i ω * t i : ℝ) = t i * f' i ω
    ring
  -- L¹-integrability of products `f' i · f' j` under `P` (Hölder for L²×L²).
  have hf'_int : ∀ i, Integrable (f' i) P := fun i =>
    (hf'_memLp i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hf'_mul_int : ∀ i j, Integrable (fun x => f' i x * f' j x) P := fun i j =>
    (hf'_memLp i).integrable_mul (hf'_memLp j)
  -- Variance identity: `Var[⟪t, Y 0⟫; μ] = t ⬝ᵥ marginalCovMatrix P f *ᵥ t`.
  have hvar : ∀ t : EuclideanSpace ℝ (Fin k),
      Var[fun ξ => ⟪t, Y 0 ξ⟫; μ] = t ⬝ᵥ marginalCovMatrix P f *ᵥ t := by
    intro t
    -- `Z ξ = gt (X 0 ξ)` where `gt ω = ∑ i, t i * f' i ω`.
    set gt : Ω → ℝ := fun ω => ∑ i, t i * f' i ω with hgt_def
    have hgt_meas : Measurable gt :=
      Finset.measurable_sum _ (fun i _ => (measurable_const.mul (hf'_meas i)))
    have hZ_eq : (fun ξ => ⟪t, Y 0 ξ⟫) = (fun ξ => gt (X 0 ξ)) := by
      funext ξ; exact hinner_eq t (X 0 ξ)
    -- `gt` and `gt²` are integrable under `P`.
    have hgt_int : Integrable gt P := by
      rw [hgt_def]
      exact integrable_finset_sum _ (fun i _ => (hf'_int i).const_mul _)
    have hgt_sq_int : Integrable (fun x => gt x ^ 2) P := by
      have hexpand : (fun x => gt x ^ 2)
          = fun x => ∑ i, ∑ j, (t i * t j) * (f' i x * f' j x) := by
        funext x
        rw [hgt_def]
        simp only [sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
      rw [hexpand]
      exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _
        (fun j _ => ((hf'_mul_int i j).const_mul _)))
    have hgt_memLp : MemLp gt 2 P :=
      (memLp_two_iff_integrable_sq hgt_meas.aestronglyMeasurable).mpr hgt_sq_int
    have hZ_memLp : MemLp (fun ξ => ⟪t, Y 0 ξ⟫) 2 μ := by
      rw [hZ_eq]
      have hmp : MemLp gt 2 (μ.map (X 0)) := by rw [hmap 0]; exact hgt_memLp
      exact (memLp_map_measure_iff hgt_meas.aestronglyMeasurable
        (_hX_meas 0).aemeasurable).1 hmp
    -- Push the mean and second moment to integrals under `P`.
    have hmean : μ[fun ξ => ⟪t, Y 0 ξ⟫] = ∫ x, gt x ∂P := by
      rw [hZ_eq, ← hmap 0,
        integral_map (_hX_meas 0).aemeasurable hgt_meas.aestronglyMeasurable]
    have hsq : μ[fun ξ => ⟪t, Y 0 ξ⟫ ^ 2] = ∫ x, gt x ^ 2 ∂P := by
      have hZ_eq_sq : (fun ξ => ⟪t, Y 0 ξ⟫ ^ 2) = (fun ξ => gt (X 0 ξ) ^ 2) := by
        funext ξ; rw [congrFun hZ_eq ξ]
      rw [hZ_eq_sq, ← hmap 0,
        integral_map (_hX_meas 0).aemeasurable
          (hgt_meas.pow_const 2).aestronglyMeasurable]
    -- Expand the two integrals over `P`.
    have hmean_exp : ∫ x, gt x ∂P = ∑ i, t i * ∫ x, f' i x ∂P := by
      rw [hgt_def]
      rw [integral_finset_sum _ (fun i _ => (hf'_int i).const_mul _)]
      exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)
    have hsq_exp : ∫ x, gt x ^ 2 ∂P
        = ∑ i, ∑ j, (t i * t j) * ∫ x, f' i x * f' j x ∂P := by
      have hexpand : (fun x => gt x ^ 2)
          = fun x => ∑ i, ∑ j, (t i * t j) * (f' i x * f' j x) := by
        funext x
        rw [hgt_def]
        simp only [sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
      rw [hexpand,
        integral_finset_sum _ (fun i _ => integrable_finset_sum _
          (fun j _ => (hf'_mul_int i j).const_mul _))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finset_sum _ (fun j _ => (hf'_mul_int i j).const_mul _)]
      exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
    -- Assemble: `Var = E[Z²] − (E Z)²`.
    rw [variance_eq_sub hZ_memLp]
    simp only [Pi.pow_apply]
    rw [hmean, hsq, hmean_exp, hsq_exp]
    -- RHS as a double sum over `marginalCovEntry P f`.
    have hrhs : t ⬝ᵥ marginalCovMatrix P f *ᵥ t
        = ∑ i, ∑ j, (t i * t j) * marginalCovEntry P f i j := by
      simp only [dotProduct, Matrix.mulVec, marginalCovMatrix]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hrhs]
    -- Expand `(∑ i, t i * ∫ f' i)²` into a double sum.
    rw [sq, Finset.sum_mul_sum]
    -- Merge the two double sums termwise.
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [marginalCovEntry]
    -- `f'`-integrals equal `f`-integrals (a.e.), so substitute.
    have e1 : ∫ x, f' i x * f' j x ∂P = ∫ x, f i x * f j x ∂P :=
      integral_congr_ae (by filter_upwards [hff' i, hff' j] with x hi hj; rw [hi, hj])
    have e2 : ∫ x, f' i x ∂P = ∫ x, f i x ∂P := integral_congr_ae ((hff' i).symm)
    have e3 : ∫ x, f' j x ∂P = ∫ x, f j x ∂P := integral_congr_ae ((hff' j).symm)
    rw [e1, e2, e3]
    ring
  -- Positive-semidefiniteness of the covariance matrix (via the variance form).
  have hpsd : (marginalCovMatrix P f).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
    · -- Hermitian: symmetric real matrix.
      ext i j
      simp only [marginalCovMatrix, marginalCovEntry,
        Matrix.conjTranspose_apply, star_trivial]
      rw [mul_comm (∫ x, f j x ∂P)]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))
    · -- Nonneg quadratic form = variance ≥ 0.
      have hx : (star x : Fin k → ℝ) = (x : Fin k → ℝ) := by
        funext i; exact star_trivial _
      rw [hx]
      have hxv : x ⬝ᵥ marginalCovMatrix P f *ᵥ x
          = Var[fun ξ => ⟪((WithLp.equiv 2 (Fin k → ℝ)).symm x), Y 0 ξ⟫; μ] :=
        (hvar ((WithLp.equiv 2 (Fin k → ℝ)).symm x)).symm
      rw [hxv]
      exact variance_nonneg _ _
  -- Apply the multivariate iid CLT with the identity witness.
  have hYid : ProbabilityTheory.HasLaw
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      (multivariateGaussian 0 (marginalCovMatrix P f))
      (multivariateGaussian 0 (marginalCovMatrix P f)) := ProbabilityTheory.HasLaw.id
  have hTID :
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ξ =>
          (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, Y i ξ - n • μ[fun ξ => Y 0 ξ]))
        atTop (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
        (fun _ => μ) (multivariateGaussian 0 (marginalCovMatrix P f)) :=
    ProbabilityTheory.tendstoInDistribution_multivariate_clt
      (P := μ) (P' := multivariateGaussian 0 (marginalCovMatrix P f))
      (X := Y) (Y := id) (S := marginalCovMatrix P f) hpsd hvar hYid hY0_memLp hY_iid hY_id
  -- Transfer to the original (un-modified) `f` via μ-a.e. equality of the random vectors.
  refine hTID.congr ?_ (Filter.EventuallyEq.refl _ _)
  intro n
  -- `μ[fun ξ => Y 0 ξ] = μ[fun ξ => tupleVec f (X 0 ξ)]` since the integrands are a.e. equal.
  have hcenter : μ[fun ξ => Y 0 ξ] = μ[fun ξ => tupleVec f (X 0 ξ)] :=
    integral_congr_ae (hYY' 0).symm
  rw [hcenter]
  -- Pointwise: the standardised sums agree μ-a.e. (each summand agrees a.e.).
  have hsum : ∀ᵐ ξ ∂μ, ∀ i ∈ Finset.range n, tupleVec f (X i ξ) = Y i ξ :=
    (ae_ball_iff (Finset.range n).countable_toSet).mpr
      (fun i _ => hYY' i)
  filter_upwards [hsum] with ξ hξ
  congr 1
  congr 1
  exact Finset.sum_congr rfl (fun i hi => (hξ i hi).symm)

/-- **Marginal-CLT predicate from tuple-wise L²-membership.** Assembles
`IsMarginalCLT F P` from `∀ f ∈ F, MemLp f 2 P`: the `memLp` conjunct is the
hypothesis itself; the `fdd` conjunct delegates, per finite tuple, to
`marginalCLT_fdd_of_iid` (each tuple entry inherits `MemLp 2` from membership in
`F`). -/
lemma isMarginalCLT_of_memLp {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hmem : ∀ f ∈ F, MemLp f 2 P) : IsMarginalCLT F P := by
  refine ⟨hmem, ?_⟩
  intro Ξ _ μ _ X hX_meas hX_iindep hX_id hX_law k f hf_in
  exact marginalCLT_fdd_of_iid (F := F) μ X hX_meas hX_iindep hX_id hX_law f
    (fun i => hmem (f i) (hf_in i))

/-- **Asymptotic equicontinuity** — van der Vaart Theorem 18.14(ii), the
**outer-probability modulus-of-continuity** form.

For every iid sample `X : ℕ → Ξ → Ω` on a probability space `(Ξ, μ)` with law
`P` and every pair of levels `ε, η > 0` there is a `distL2`-radius `δ > 0` such
that the `limsup` (over `n`) of the **outer** probability that the empirical
process `G_n` oscillates by more than `ε` across some `distL2`-close pair
`(s, t)` (`distL2 P s t < δ`) is at most `ENNReal.ofReal η`:

`∀ ε η > 0, ∃ δ > 0, limsupₙ μ* {ξ | ∃ s t : ↥F, distL2 P s t < δ ∧
    ε < |G_n(s)(ξ) − G_n(t)(ξ)|} ≤ ofReal η`.

This is exactly the conclusion of `outerMeasure_modulusComplement_le` in
`NecessityTightness.lean` and the hypothesis used by the sufficiency
discretization. The
**three parameters are distinct**: `ε` is the oscillation threshold, `η` the
outer-mass bound, `δ` the `distL2`-radius (vdV p.261).

The corresponding **per-pair form** — "for any measurable random pair
`(fhat, ghat)` in `F` with `∫ ‖fhat − ghat‖²_{L²(P)} dμ → 0`,
`μ {ξ | ε < |G_n(fhat) − G_n(ghat)|} → 0`" — is recovered for any concrete
pair through the bridge lemma `osc_modulus_to_random_pair`
(`NecessityTightness.lean`, the Markov-tail + bulk split).

**Universe of `Ξ`.** Fixed at `Type 0` (`Type`). All standard
measure-theoretic sample spaces live at universe 0; applications
requiring a higher universe introduce an isomorphism to a `Type 0`
representative.

vdV Theorem 18.14(ii) (book p.261), §19.2, Vaart–Wellner §2.1: the tightness
side of weak convergence in `ℓ^∞(F)`. -/
def IsAsymptoticallyEquicontinuous (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
    [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
    (∀ i, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X μ →
    (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
    μ.map (X 0) = P →
    ∀ ε η : ℝ, 0 < ε → 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ limsup (fun n => μ.outerMeasureStar
        {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
          ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|}) atTop
        ≤ ENNReal.ofReal η

/-- **P-Donsker class**.

Following vdV §19.2 + Theorem 18.14: `F` is `P`-Donsker iff the empirical
process `G_n` converges weakly in `ℓ^∞(F)` to a tight Gaussian limit.
The Theorem-18.14 characterization gives:
`IsPDonsker F P ↔ IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P`.

We adopt the right-hand side as the working definition.

vdV §19.2 + Theorem 18.14: `F` is `P`-Donsker. -/
def IsPDonsker (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P

/-- **L²-membership projection of the marginal CLT.** Every
`f ∈ F` is square-integrable. -/
lemma IsMarginalCLT.memLp {F : Set (Ω → ℝ)} {P : Measure Ω}
    (h : IsMarginalCLT F P) : ∀ f ∈ F, MemLp f 2 P := h.1

namespace IsPDonsker

variable {F : Set (Ω → ℝ)} {P : Measure Ω}

lemma marginalCLT (h : IsPDonsker F P) : IsMarginalCLT F P := h.1

lemma asymptoticallyEquicontinuous (h : IsPDonsker F P) :
    IsAsymptoticallyEquicontinuous F P := h.2

end IsPDonsker

/-! ### Outer-measure bounds and the per-pair bridge

The `IsAsymptoticallyEquicontinuous` predicate is the vdV 18.14(ii) outer-sup
modulus. The corresponding **per-pair** consequence
("`μ {ξ | ε < |G_n(fhat) − G_n(ghat)|} → 0` for a concrete measurable pair")
follows from `osc_modulus_to_random_pair` below (the Markov-tail + bulk split). The
small outer-measure and `distL2`-tail bricks it needs are `distL2`-only /
`outerMeasureStar`-only (no `gaussianPBridge` machinery), so they live here at the
predicate layer and are reused in `NecessityTightness.lean`. -/

/-- **Monotonicity of the outer measure `P*`.** `A ⊆ B ⟹ P*(A) ≤ P*(B)`
(the indicators satisfy `1_A ≤ 1_B`, and `E*` is monotone). -/
theorem outerMeasureStar_mono {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    {A B : Set Ξ} (hAB : A ⊆ B) :
    μ.outerMeasureStar A ≤ μ.outerMeasureStar B := by
  refine outerExpectation_mono fun ω => ?_
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (hAB hω), le_refl]
  · simp only [Set.indicator_of_notMem hω, Pi.zero_apply, zero_le]

/-- **`μ`-measure is dominated by the outer measure `P*`.** `μ A ≤ P*(A)`: every
measurable majorant `U ≥ 1_A` has `μ A = ∫⁻ 1_A ≤ ∫⁻ U`, so `μ A` is below the
infimum defining `outerExpectation μ (1_A) = P*(A)`. -/
theorem measure_le_outerMeasureStar {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (A : Set Ξ) : μ A ≤ μ.outerMeasureStar A := by
  rw [Measure.outerMeasureStar, outerExpectation]
  refine le_iInf fun U => ?_
  -- `μ A = ∫⁻_{A} 1 ≤ ∫⁻_{A} U ≤ ∫⁻ U` (on `A`, `U ≥ 1_A = 1`).
  calc μ A = ∫⁻ _ω in A, (1 : ℝ≥0∞) ∂μ := by rw [setLIntegral_one]
      _ ≤ ∫⁻ ω in A, (U : Ξ → ℝ≥0∞) ω ∂μ := by
          refine setLIntegral_mono U.2.1 (fun ω hω => ?_)
          have := U.2.2 ω
          simpa [Set.indicator_of_mem hω] using this
      _ ≤ ∫⁻ ω, (U : Ξ → ℝ≥0∞) ω ∂μ := setLIntegral_le_lintegral A _

/-- **`distL2`-tail to integral-tail.** If `distL2 P f g` has positive value
`δ`-or-more, then `f − g` is `2`-`MemLp` (else `distL2 = 0 < δ`), so
`δ² ≤ distL2² = ∫ (f − g)² ∂P`. Used to feed Markov on the integral. -/
theorem distL2_ge_imp_integral_ge {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    {δ : ℝ} (hδ : 0 < δ) (hge : δ ≤ distL2 P f g) :
    δ ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂P := by
  -- `distL2 P f g = (eLpNorm (f - g) 2 P).toReal`; positivity forces `eLpNorm < ⊤`.
  have hpos : 0 < distL2 P f g := lt_of_lt_of_le hδ hge
  have hne_top : eLpNorm (f - g) 2 P ≠ ⊤ := by
    intro htop
    rw [distL2, htop, ENNReal.toReal_top] at hpos
    exact lt_irrefl 0 hpos
  have hmeas : AEStronglyMeasurable (f - g) P := hf.sub hg
  have hmemLp : MemLp (f - g) 2 P := ⟨hmeas, lt_of_le_of_ne le_top hne_top⟩
  -- `distL2² = ((∫ ‖(f-g)‖²)^(2⁻¹))² = ∫ ‖(f-g) x‖² = ∫ (f x - g x)²`.
  have hint_nonneg : (0 : ℝ) ≤ ∫ x, ‖(f - g) x‖ ^ (2 : ℝ≥0∞).toReal ∂P :=
    integral_nonneg (fun x => by positivity)
  have hsq : distL2 P f g ^ 2 = ∫ x, (f x - g x) ^ 2 ∂P := by
    rw [distL2, hmemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hint_nonneg _)]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hint_nonneg]
    simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
    rw [inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change ‖(f - g) x‖ ^ (2 : ℝ) = (f x - g x) ^ 2
    rw [Pi.sub_apply, Real.norm_eq_abs,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact sq_abs (f x - g x)
  calc δ ^ 2 ≤ distL2 P f g ^ 2 := by
        apply pow_le_pow_left₀ (le_of_lt hδ) hge
    _ = ∫ x, (f x - g x) ^ 2 ∂P := hsq

/-- **Markov vanishing of the `distL2`-tail.** Under the L²-consistency
hypotheses (joint measurability of `fhat`/`ghat`, integrability and `μ`-integral
vanishing of the squared `L²`-distance), the `μ`-mass of the complement event
`{ξ | δ ≤ distL2 P (fhat n ξ) (ghat n ξ)}` tends to `0`. Proof:
`distL2_ge_imp_integral_ge` lands the tail event inside
`{ξ | δ² ≤ ∫ (fhat − ghat)²}`, Markov bounds its real mass by
`(∫ξ ∫x (fhat − ghat)²)/δ²`, which `→ 0`. -/
theorem markov_distL2_tail {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (hfm : ∀ n, Measurable (Function.uncurry (fhat n)))
    (hgm : ∀ n, Measurable (Function.uncurry (ghat n)))
    (hint : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (htend : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
      atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => μ {ξ | δ ≤ distL2 P (fhat n ξ) (ghat n ξ)}) atTop (𝓝 0) := by
  -- Per-section measurability of `fhat n ξ` / `ghat n ξ` from the joint measurability.
  have hf_sec : ∀ n ξ, Measurable (fhat n ξ) := fun n ξ =>
    (hfm n).comp measurable_prodMk_left
  have hg_sec : ∀ n ξ, Measurable (ghat n ξ) := fun n ξ =>
    (hgm n).comp measurable_prodMk_left
  -- `I n = ∫ξ ∫x (fhat − ghat)²`; nonneg, integrable per `hint`.
  set I : ℕ → ℝ := fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ with hI
  -- Real-valued tail mass bound `μ.real {δ ≤ distL2} ≤ I n / δ²`.
  have hbound : ∀ n, μ.real {ξ | δ ≤ distL2 P (fhat n ξ) (ghat n ξ)} ≤ I n / δ ^ 2 := by
    intro n
    -- subset into the integral-tail event.
    have hsub : {ξ | δ ≤ distL2 P (fhat n ξ) (ghat n ξ)}
        ⊆ {ξ | δ ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P} := by
      intro ξ hξ
      exact distL2_ge_imp_integral_ge (hf_sec n ξ).aestronglyMeasurable
        (hg_sec n ξ).aestronglyMeasurable hδ hξ
    -- Markov on the nonneg integrable `ξ ↦ ∫ (fhat − ghat)²`.
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P)
      (Eventually.of_forall fun ξ => integral_nonneg fun x => by positivity)
      (hint n) (δ ^ 2)
    -- transport the Markov bound across the subset and divide by `δ²`.
    have hmono : μ.real {ξ | δ ≤ distL2 P (fhat n ξ) (ghat n ξ)}
        ≤ μ.real {ξ | δ ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
    rw [le_div_iff₀ hδ2, mul_comm]
    exact le_trans (by nlinarith [hmono, hδ2]) hmark
  -- `I n / δ² → 0`, squeeze the nonneg real tail mass.
  have htendReal : Tendsto (fun n => I n / δ ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n => I n) atTop (𝓝 0) := htend
    simpa using this.div_const (δ ^ 2)
  -- real tail mass `→ 0`.
  have htailReal : Tendsto (fun n => μ.real {ξ | δ ≤ distL2 P (fhat n ξ) (ghat n ξ)})
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ENNReal.toReal_nonneg) hbound htendReal
  -- lift to `ℝ≥0∞` via `ofReal` of the real mass (finite measure).
  have : Tendsto (fun n => ENNReal.ofReal
      (μ.real {ξ | δ ≤ distL2 P (fhat n ξ) (ghat n ξ)})) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp htailReal
  refine this.congr (fun n => ?_)
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Bulk inclusion (pointwise).** If the random pair `(fhat, ghat)` at a point
is a close pair (`distL2 < δ`) with oscillation `η < |G_n fhat − G_n ghat|`, then
the existential close-pair predicate of the modulus holds at that point (take
`f := ⟨fhat, _⟩`, `g := ⟨ghat, _⟩`). -/
theorem bulk_osc_mem {F : Set (Ω → ℝ)} {P : Measure Ω} {n : ℕ}
    {fhat ghat : Ω → ℝ} (hf : fhat ∈ F) (hg : ghat ∈ F)
    {X : Fin n → Ω} {δ η : ℝ}
    (hclose : distL2 P fhat ghat < δ)
    (hosc : η < |empiricalProcess P n X fhat - empiricalProcess P n X ghat|) :
    ∃ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ ∧
      η < |empiricalProcess P n X (f : Ω → ℝ)
            - empiricalProcess P n X (g : Ω → ℝ)| :=
  ⟨⟨fhat, hf⟩, ⟨ghat, hg⟩, hclose, hosc⟩

-- reason: the generic `limsup_add_le` `whnf`-explodes on `ℝ≥0∞`/`atTop` (even in a
-- small context); we only need the `Vf → 0` specialization, proved here directly.
set_option maxHeartbeats 800000 in
/-- **`limsup (Uf + Vf) ≤ a` when `limsup Uf ≤ a` and `Vf → 0`** (over `atTop`,
`ℝ≥0∞`). For every `b > a` the `limsup`-characterization needs `Uf n + Vf n < b`
eventually: pick `c` with `limsup Uf < c < b`, so eventually `Uf n < c` and (from
`Vf → 0`) `Vf n < b − c`, whence `Uf n + Vf n < c + (b − c) = b`. -/
theorem limsup_add_tendsto_zero_le (Uf Vf : ℕ → ℝ≥0∞) (a : ℝ≥0∞)
    (hU : limsup Uf atTop ≤ a) (hV : Tendsto Vf atTop (𝓝 0)) :
    limsup (fun n => Uf n + Vf n) atTop ≤ a := by
  rw [limsup_le_iff isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)]
  intro b hb
  obtain ⟨c, hac, hcb⟩ := exists_between (lt_of_le_of_lt hU hb)
  have hUev : ∀ᶠ n in atTop, Uf n < c := eventually_lt_of_limsup_lt hac
  have hbc : (0 : ℝ≥0∞) < b - c := tsub_pos_of_lt hcb
  have hVev : ∀ᶠ n in atTop, Vf n < b - c := hV (Iio_mem_nhds hbc)
  filter_upwards [hUev, hVev] with n hUn hVn
  calc Uf n + Vf n < c + (b - c) := ENNReal.add_lt_add hUn hVn
    _ = b := add_tsub_cancel_of_le (le_of_lt hcb)

/-- **`limsup (Uf + Vf) ≤ a + b` from `limsup Uf ≤ a`, `limsup Vf ≤ b`** (over
`atTop`, `ℝ≥0∞`, both bounds `≠ ⊤`). The `CountableInterFilter`-free analogue of
`ENNReal.limsup_add_le` for the non-countably-complete filter `atTop`. For every
`d > a + b` pick the slack `c := d − (a + b) > 0`; since `a, b ≠ ⊤` we have
`a < a + c/2` and `b < b + c/2`, so eventually `Uf n < a + c/2`, `Vf n < b + c/2`,
whence `Uf n + Vf n < (a + c/2) + (b + c/2) = a + b + c = d`. -/
theorem limsup_add_le_of_le (Uf Vf : ℕ → ℝ≥0∞) (a b : ℝ≥0∞)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hU : limsup Uf atTop ≤ a) (hV : limsup Vf atTop ≤ b) :
    limsup (fun n => Uf n + Vf n) atTop ≤ a + b := by
  rw [limsup_le_iff isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)]
  intro d hd
  -- Slack `c := d − (a + b) > 0`; the two half-slack thresholds beat `a`, `b`.
  set c : ℝ≥0∞ := d - (a + b) with hc
  have hc_pos : 0 < c := tsub_pos_of_lt hd
  have hc2_pos : 0 < c / 2 := ENNReal.div_pos (ne_of_gt hc_pos) (by norm_num)
  have ha' : a < a + c / 2 := ENNReal.lt_add_right ha (ne_of_gt hc2_pos)
  have hb' : b < b + c / 2 := ENNReal.lt_add_right hb (ne_of_gt hc2_pos)
  have hUev : ∀ᶠ n in atTop, Uf n < a + c / 2 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hU ha')
  have hVev : ∀ᶠ n in atTop, Vf n < b + c / 2 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hV hb')
  -- `(a + c/2) + (b + c/2) = a + b + c = d`.
  have hsum : (a + c / 2) + (b + c / 2) = d := by
    rw [show (a + c / 2) + (b + c / 2) = (a + b) + (c / 2 + c / 2) by ring,
      ENNReal.add_halves, hc, add_tsub_cancel_of_le (le_of_lt hd)]
  filter_upwards [hUev, hVev] with n hUn hVn
  calc Uf n + Vf n < (a + c / 2) + (b + c / 2) := ENNReal.add_lt_add hUn hVn
    _ = d := hsum

-- reason: the bulk/tail `limsup` split unfolds the giant empirical-process payload;
-- the `clear_value` opacity device keeps it from `whnf`-exploding but the residual
-- `limsup`/`Tendsto` arithmetic still needs headroom above the default.
set_option maxHeartbeats 1000000 in
/-- **Outer-sup modulus implies per-pair consistency.** From the
`IsAsymptoticallyEquicontinuous` predicate (the vdV 18.14(ii) outer-sup modulus)
and a concrete jointly-measurable random pair `(fhat, ghat)` valued in `F` whose
mean squared `L²(P)`-distance tends to `0`, conclude that for every `ε > 0` the
`μ`-probability of an `ε`-oscillation `μ {ξ | ε < |G_n(fhat) − G_n(ghat)|}` tends
to `0`, which is the per-pair form.

Fix `ε`; for the `limsup ≤ ofReal ε'` reduction take `η' := min ε ε'` and apply
the modulus at oscillation `η'`, mass `η'`. Split `Ξ` on `{distL2 < δ}`: the bulk
lands in the modulus event (`bulk_osc_mem`), the `distL2`-tail mass vanishes by
Markov (`markov_distL2_tail`); the two `limsup`s combine via
`limsup_add_tendsto_zero_le`.

vdV p.261 (⟹): the modified-random-function trick (split by `{‖fhat − ghat‖ < δ}`
and apply textbook equicontinuity to the modified pair on the small-mass
complement). -/
theorem osc_modulus_to_random_pair {F : Set (Ω → ℝ)} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (h_eq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (hfm : ∀ n, Measurable (Function.uncurry (fhat n)))
    (hgm : ∀ n, Measurable (Function.uncurry (ghat n)))
    (hf_in : ∀ n ξ, fhat n ξ ∈ F) (hg_in : ∀ n ξ, ghat n ξ ∈ F)
    (hint : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (htend : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
      atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) := by
  -- Abbreviate the oscillation deviation event.
  set osc : ℕ → Ξ → ℝ := fun n ξ =>
    |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
      - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)| with hosc
  set u : ℕ → ℝ≥0∞ := fun n => μ {ξ | η < osc n ξ} with hu
  -- Reduce `Tendsto u → 0` to `∀ ε > 0, limsup u ≤ ofReal ε`.
  suffices hlimsup : ∀ ε : ℝ, 0 < ε → limsup u atTop ≤ ENNReal.ofReal ε by
    have hsup0 : limsup u atTop ≤ 0 := by
      refine ENNReal.le_of_forall_pos_le_add fun ε hεpos _ => ?_
      rw [zero_add]
      have := hlimsup (ε : ℝ) (by exact_mod_cast hεpos)
      rwa [ENNReal.ofReal_coe_nnreal] at this
    have hsup0' : limsup u atTop = 0 := le_antisymm hsup0 bot_le
    refine tendsto_of_le_liminf_of_limsup_le bot_le hsup0'.le ?_ ?_
    · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
    · exact isBoundedUnder_of ⟨0, fun _ => bot_le⟩
  -- Fix `ε > 0`; let `η' := min η ε` (the threshold/mass for the modulus).
  intro ε hε
  set η' : ℝ := min η ε with hη'
  have hη'pos : 0 < η' := lt_min hη hε
  have hη'_le_η : η' ≤ η := min_le_left _ _
  have hη'_le_ε : η' ≤ ε := min_le_right _ _
  -- The modulus at oscillation `η'`, mass `η'`: the close-pair radius `δ` and bound.
  obtain ⟨δ, hδpos, hBlimsup⟩ :=
    h_eq μ X hX_meas hX_indep hX_id hX_law η' η' hη'pos hη'pos
  -- The `distL2`-tail event mass vanishes (Markov).
  have htail := markov_distL2_tail (F := F) μ fhat ghat hfm hgm
    hint htend hδpos
  -- Abbreviate the modulus existential close-pair event and the `distL2`-tail event.
  set Bev : ℕ → Set Ξ := fun n =>
    {ξ | ∃ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ ∧
      η' < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (g : Ω → ℝ)|} with hBev
  set Tev : ℕ → Set Ξ := fun n => {ξ | δ ≤ distL2 P (fhat n ξ) (ghat n ξ)} with hTev
  -- Make the giant empirical-process payload opaque so the `limsup` machinery
  -- below does not `whnf`-explode on it; unfold via `hBev`/`hTev` where needed.
  clear_value Bev Tev
  -- Set-level decomposition: `{η < osc} ⊆ Bev n ∪ Tev n`.
  have hsplit : ∀ n, {ξ | η < osc n ξ} ⊆ Bev n ∪ Tev n := by
    intro n ξ hξ
    rw [hBev, hTev]
    by_cases hcl : distL2 P (fhat n ξ) (ghat n ξ) < δ
    · exact Or.inl (bulk_osc_mem (hf_in n ξ) (hg_in n ξ) hcl (lt_of_le_of_lt hη'_le_η hξ))
    · exact Or.inr (le_of_not_gt hcl)
  -- Opaque envelopes `Uf = μ* ∘ Bev`, `Vf = μ ∘ Tev`; fold `hBlimsup`/`htail`/`u`.
  set Uf : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar (Bev n) with hUf
  set Vf : ℕ → ℝ≥0∞ := fun n => μ (Tev n) with hVf
  -- `u n ≤ Uf n + Vf n`.
  have hbound : ∀ n, u n ≤ Uf n + Vf n := by
    intro n
    rw [hUf, hVf]
    calc u n ≤ μ (Bev n ∪ Tev n) := measure_mono (hsplit n)
      _ ≤ μ (Bev n) + μ (Tev n) := measure_union_le _ _
      _ ≤ μ.outerMeasureStar (Bev n) + μ (Tev n) := by
          gcongr
          exact measure_le_outerMeasureStar μ (Bev n)
  -- `Vf → 0`, `limsup Uf ≤ ofReal η'`.
  have htail' : Tendsto Vf atTop (𝓝 0) := by
    rw [hVf]; simpa only [hTev] using htail
  have hBlimsup' : limsup Uf atTop ≤ ENNReal.ofReal η' := by
    rw [hUf]; simp only [hBev]; exact hBlimsup
  -- Everything below treats `u`, `Uf`, `Vf` as opaque (no `whnf` on the payload).
  clear_value u osc Uf Vf
  -- `limsup u ≤ limsup (Uf + Vf) ≤ ofReal η' ≤ ofReal ε`.
  have hstep1 : limsup u atTop ≤ limsup (fun n => Uf n + Vf n) atTop :=
    limsup_le_limsup (Eventually.of_forall hbound)
      isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
  calc limsup u atTop
      ≤ limsup (fun n => Uf n + Vf n) atTop := hstep1
    _ ≤ ENNReal.ofReal η' := limsup_add_tendsto_zero_le Uf Vf _ hBlimsup' htail'
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hη'_le_ε

/-- **Binary subadditivity of the outer measure `P*`.**
`P*(A ∪ B) ≤ P*(A) + P*(B)`. Pointwise `1_{A∪B} ≤ 1_A + 1_B`, then monotonicity of
`E*` (`outerExpectation_mono`) and binary subadditivity (`outerExpectation_add_le`)
of outer expectation close it. -/
theorem outerMeasureStar_union_le {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (A B : Set Ξ) :
    μ.outerMeasureStar (A ∪ B) ≤ μ.outerMeasureStar A + μ.outerMeasureStar B := by
  refine le_trans (outerExpectation_mono (μ := μ) (X := (A ∪ B).indicator 1)
    (Y := A.indicator 1 + B.indicator 1) (fun ω => ?_)) (outerExpectation_add_le _ _)
  refine Set.indicator_apply_le (fun hω => ?_)
  rw [Pi.add_apply, Pi.one_apply]
  rcases hω with hA | hB
  · rw [Set.indicator_of_mem hA, Pi.one_apply]
    exact le_self_add
  · rw [Set.indicator_of_mem hB, Pi.one_apply]
    exact le_add_self

/-- **Integral-squared lower bound ⟹ `distL2` lower bound** (no measurability /
finiteness hypotheses). If `c² ≤ ∫ (f − g)² ∂P`, then `c ≤ distL2 P f g`. This is
the converse direction of `distL2_ge_imp_integral_ge`, used in the union closure
to make separated cross-pairs `distL2`-far apart. The proof routes through the
universally-true inequality `∫ (f − g)² ≤ (∫⁻ ‖(f − g)·‖ₑ² ∂P).toReal` (Jensen /
`norm_integral_le_lintegral_norm`) together with the identity
`distL2² = (∫⁻ ‖(f − g)·‖ₑ² ∂P).toReal` — valid even when the lintegral is `⊤`
(both sides are then `0`), so neither `MemLp` nor measurability is needed. -/
theorem le_distL2_of_integral_sq_ge {P : Measure Ω} {f g : Ω → ℝ}
    {c : ℝ} (hge : c ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂P) :
    c ≤ distL2 P f g := by
  -- `L = ∫⁻ ‖(f − g) x‖ₑ² ∂P` (Nat power); the squared distance equals `L.toReal`.
  set L : ℝ≥0∞ := ∫⁻ x, ‖(f - g) x‖ₑ ^ 2 ∂P with hL
  -- Pointwise: `‖(f − g) x‖ₑ ^ (2:ℝ) = ‖(f − g) x‖ₑ ^ (2:ℕ)`.
  have hpow : ∀ x, ‖(f - g) x‖ₑ ^ (2 : ℝ≥0∞).toReal = ‖(f - g) x‖ₑ ^ 2 := by
    intro x; rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast _ 2, Nat.cast_ofNat]
  -- `distL2² = L.toReal`.
  have hdist_sq : distL2 P f g ^ 2 = L.toReal := by
    rw [distL2, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [← ENNReal.toReal_rpow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul ENNReal.toReal_nonneg]
    rw [show ((1 : ℝ) / (2 : ℝ≥0∞).toReal) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    rw [hL]; congr 1; exact lintegral_congr hpow
  -- `∫ (f − g)² ≤ L.toReal` (Jensen, no measurability needed).
  have hbound : ∫ x, (f x - g x) ^ 2 ∂P ≤ L.toReal := by
    have hnn : (0 : ℝ) ≤ ∫ x, (f x - g x) ^ 2 ∂P :=
      integral_nonneg (fun x => by positivity)
    calc ∫ x, (f x - g x) ^ 2 ∂P
        = ‖∫ x, (f x - g x) ^ 2 ∂P‖ := (Real.norm_of_nonneg hnn).symm
      _ ≤ (∫⁻ x, ENNReal.ofReal ‖(f x - g x) ^ 2‖ ∂P).toReal :=
          norm_integral_le_lintegral_norm _
      _ = L.toReal := by
          rw [hL]
          congr 1
          refine lintegral_congr (fun x => ?_)
          rw [Pi.sub_apply, Real.norm_of_nonneg (by positivity),
            Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  -- Chain: `c² ≤ ∫ (f − g)² ≤ L.toReal = distL2²`, then take roots.
  have hsq : c ^ 2 ≤ distL2 P f g ^ 2 := by rw [hdist_sq]; exact hge.trans hbound
  have hd_nonneg : 0 ≤ distL2 P f g := ENNReal.toReal_nonneg
  nlinarith [hsq, hd_nonneg, sq_nonneg (c - distL2 P f g), sq_nonneg (c + distL2 P f g)]

/-- **Union closure of asymptotic equicontinuity**.

vdV §19.4 (used inside the proof of Theorem 19.23): "The union of two Donsker
classes is Donsker." For the marginal-CLT half this is trivial; the
equicontinuity half is this lemma.

**Proof.** For the vdV 18.14(ii) outer-sup modulus, apply `hF` and `hG` at the
same iid sample with the halved mass `η/2`, yielding radii `δ_F`, `δ_G`; pick the
union radius `δ := min (min δ_F δ_G) c` where `c` is the `L²`-separation constant.
The `L²`-separation `hFG_sep` forces every cross-pair (`s ∈ F`, `t ∈ G`, or vice
versa) to satisfy `c ≤ distL2 P s t` (`le_distL2_of_integral_sq_ge`), so a
`distL2`-close pair (`distL2 < δ ≤ c`) is never a cross-pair: both lie in `F` or
both in `G`. Hence the `F ∪ G` close-pair event is contained in the union of the
`F`-event and the `G`-event, and `μ*`-subadditivity (`outerMeasureStar_union_le`)
plus monotonicity (`outerMeasureStar_mono`, since `δ ≤ δ_F, δ_G`) bound its limsup
by `ofReal (η/2) + ofReal (η/2) = ofReal η`. The selection/nonempty admissibility
properties are not needed by the outer-sup formulation.
-/
lemma isAsymptoticallyEquicontinuous_union {F G : Set (Ω → ℝ)} {P : Measure Ω}
    (hF : IsAsymptoticallyEquicontinuous F P)
    (hG : IsAsymptoticallyEquicontinuous G P)
    -- admissibility hypotheses for F and G
    -- (Vaart–Wellner Thm 2.10.1 / vdV §19.4).
    -- Selection and nonempty admissibility as in Vaart–Wellner §2.10.1.
    -- These hypotheses are not needed by the outer-sup formulation.
    (_hF_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions F)
    (_hG_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions G)
    (_hF_nonempty : ∃ f₀ ∈ F, Measurable f₀)
    (_hG_nonempty : ∃ g₀ ∈ G, Measurable g₀)
    -- (Vaart–Wellner §2.10.1, §2.3).
    (hFG_sep : ∃ c > 0, ∀ f ∈ F ∪ G, ∀ g ∈ F ∪ G,
      ¬ (f ∈ F ∧ g ∈ F) → ¬ (f ∈ G ∧ g ∈ G) →
      c ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂P) :
    IsAsymptoticallyEquicontinuous (F ∪ G) P := by
  -- Unfold the outer-sup modulus for `F ∪ G`; introduce the iid sample + levels.
  intro Ξ _inst μ _inst2 X hX_meas hX_indep hX_id hX_law ε η hε hη
  -- Apply `hF`/`hG` at the SAME sample with halved mass `η/2`.
  have hη2 : (0 : ℝ) < η / 2 := by positivity
  obtain ⟨δF, hδF, hFlim⟩ := hF μ X hX_meas hX_indep hX_id hX_law ε (η / 2) hε hη2
  obtain ⟨δG, hδG, hGlim⟩ := hG μ X hX_meas hX_indep hX_id hX_law ε (η / 2) hε hη2
  -- The `L²`-separation constant `c`.
  obtain ⟨c, hc_pos, hsep⟩ := hFG_sep
  -- Union radius: small enough to beat both modulus radii and the separation.
  refine ⟨min (min δF δG) c, lt_min (lt_min hδF hδG) hc_pos, ?_⟩
  set δ : ℝ := min (min δF δG) c with hδ
  have hδ_le_F : δ ≤ δF := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_le_G : δ ≤ δG := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ_le_c : δ ≤ c := min_le_right _ _
  -- The three close-pair events (`F∪G` at `δ`, `F` at `δF`, `G` at `δG`), `n`-indexed.
  set Aev : ℕ → Set Ξ := fun n => {ξ | ∃ s t : ↥(F ∪ G),
      distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} with hAev
  set AF : ℕ → Set Ξ := fun n => {ξ | ∃ s t : ↥F,
      distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δF ∧
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} with hAF
  set AG : ℕ → Set Ξ := fun n => {ξ | ∃ s t : ↥G,
      distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δG ∧
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} with hAG
  -- Fold goal + `hF`/`hG` outputs into the abbreviations (definitional, `Aev`/`AF`/`AG`
  -- are still transparent here so the `change`/coercion goes through by defeq).
  change limsup (fun n => μ.outerMeasureStar (Aev n)) atTop ≤ ENNReal.ofReal η
  replace hFlim : limsup (fun n => μ.outerMeasureStar (AF n)) atTop
      ≤ ENNReal.ofReal (η / 2) := hFlim
  replace hGlim : limsup (fun n => μ.outerMeasureStar (AG n)) atTop
      ≤ ENNReal.ofReal (η / 2) := hGlim
  -- **Separation kills cross-pairs.** A `distL2`-close pair (`< δ ≤ c`) is never a
  -- cross-pair, so `Aev n ⊆ AF n ∪ AG n`.
  have hsubset : ∀ n, Aev n ⊆ AF n ∪ AG n := by
    intro n ξ hξ
    simp only [hAev, Set.mem_setOf_eq] at hξ
    obtain ⟨s, t, hst_close, hst_osc⟩ := hξ
    -- `s`, `t` lie in `F ∪ G`.
    have hs : (s : Ω → ℝ) ∈ F ∪ G := s.2
    have ht : (t : Ω → ℝ) ∈ F ∪ G := t.2
    -- Rule out the cross-pair case: else `c ≤ distL2`, contradicting `distL2 < δ ≤ c`.
    have hnot_cross : ((s : Ω → ℝ) ∈ F ∧ (t : Ω → ℝ) ∈ F) ∨
        ((s : Ω → ℝ) ∈ G ∧ (t : Ω → ℝ) ∈ G) := by
      by_contra hcross
      rw [not_or] at hcross
      have hsep' := hsep _ hs _ ht hcross.1 hcross.2
      have hc_le : c ≤ distL2 P (s : Ω → ℝ) (t : Ω → ℝ) :=
        le_distL2_of_integral_sq_ge hsep'
      exact absurd (lt_of_lt_of_le hst_close hδ_le_c) (not_lt.mpr hc_le)
    -- Lift the close pair into the appropriate single-class event.
    rcases hnot_cross with ⟨hsF, htF⟩ | ⟨hsG, htG⟩
    · refine Or.inl ?_
      simp only [hAF, Set.mem_setOf_eq]
      exact ⟨⟨(s : Ω → ℝ), hsF⟩, ⟨(t : Ω → ℝ), htF⟩,
        lt_of_lt_of_le hst_close hδ_le_F, hst_osc⟩
    · refine Or.inr ?_
      simp only [hAG, Set.mem_setOf_eq]
      exact ⟨⟨(s : Ω → ℝ), hsG⟩, ⟨(t : Ω → ℝ), htG⟩,
        lt_of_lt_of_le hst_close hδ_le_G, hst_osc⟩
  -- Make the giant empirical-process payload opaque for the `limsup` arithmetic.
  clear_value Aev AF AG
  -- Per-`n` outer-measure bound: `μ*(Aev n) ≤ μ*(AF n) + μ*(AG n)`.
  have hμbound : ∀ n, μ.outerMeasureStar (Aev n)
      ≤ μ.outerMeasureStar (AF n) + μ.outerMeasureStar (AG n) := fun n =>
    le_trans (outerMeasureStar_mono μ (hsubset n)) (outerMeasureStar_union_le μ _ _)
  -- Chain the `limsup`s: `limsup μ*(Aev) ≤ limsup(μ*(AF)+μ*(AG)) ≤ ofReal η/2 + ofReal η/2`.
  calc limsup (fun n => μ.outerMeasureStar (Aev n)) atTop
      ≤ limsup (fun n => μ.outerMeasureStar (AF n)
          + μ.outerMeasureStar (AG n)) atTop :=
        limsup_le_limsup (Eventually.of_forall hμbound)
          isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        limsup_add_le_of_le _ _ _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
          hFlim hGlim
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add hη2.le hη2.le]; congr 1; ring

/-- Closure under finite union: the union of two Donsker classes is
Donsker.

vdV §19.4 (used inside the proof of Theorem 19.23): "The union
of two Donsker classes is Donsker, in general."

The marginal-CLT half is the trivial fact that L²(P)-integrability is
closed under finite union. The equicontinuity half goes through
`isAsymptoticallyEquicontinuous_union`. -/
lemma IsPDonsker.union {F G : Set (Ω → ℝ)} {P : Measure Ω}
    (hF : IsPDonsker F P) (hG : IsPDonsker G P)
    -- admissibility + L²-separation
    -- (Vaart–Wellner Thm 2.10.1, §2.3 / vdV §19.4).
    (hF_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions F)
    (hG_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions G)
    (hF_nonempty : ∃ f₀ ∈ F, Measurable f₀)
    (hG_nonempty : ∃ g₀ ∈ G, Measurable g₀)
    (hFG_sep : ∃ c > 0, ∀ f ∈ F ∪ G, ∀ g ∈ F ∪ G,
      ¬ (f ∈ F ∧ g ∈ F) → ¬ (f ∈ G ∧ g ∈ G) →
      c ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂P) :
    IsPDonsker (F ∪ G) P := by
  refine ⟨?_, ?_⟩
  · refine isMarginalCLT_of_memLp ?_
    intro f hf
    cases hf with
    | inl h => exact hF.marginalCLT.memLp f h
    | inr h => exact hG.marginalCLT.memLp f h
  · exact isAsymptoticallyEquicontinuous_union hF.asymptoticallyEquicontinuous
      hG.asymptoticallyEquicontinuous hF_sel hG_sel hF_nonempty hG_nonempty hFG_sep

end AsymptoticStatistics.EmpiricalProcess
