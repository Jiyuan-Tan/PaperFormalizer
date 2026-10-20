module
public import StatLean.AsymptoticStatistics.LowerBounds.ConvolutionUnbounded
public import StatLean.AsymptoticStatistics.Core.PathwiseVec
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorVec
public import StatLean.AsymptoticStatistics.ForMathlib.SlutskyVec

@[expose] public section

/-!
# Vector-valued semiparametric adapter for `unboundedParamSubmodel`

Vector-valued versions of the affine functional `ψ_proj_vec` and its Fréchet
derivative, adapted to general output dimension `k` instead of the scalar `Fin 1`
case. The matrix `ψDotMat_vec : Matrix (Fin k) (Fin m) ℝ` is genuinely
`(Fin k) × (Fin m)`. All proofs follow the affine pattern: the Fréchet derivative
is the linear part, and `HasFDerivAt ψ_proj_vec ψDot_proj_vec_clm 0` reduces to
`HasFDerivAt.const_add`.

* `ψ_proj_vec g_P IF_eff ψ_P θ := ψ_P + A·θ`, where `A : Matrix (Fin k) (Fin m) ℝ`
  has entries `A_{j i} = ⟪IF_eff j, g_P i⟫`.
* `ψDot_proj_vec_clm g_P IF_eff` is the linear map `θ ↦ A·θ` lifted into
  `EuclideanSpace ℝ (Fin k)`.

Headline declarations: `ψ_proj_vec`, `ψDot_proj_vec_clm`, `ψ_proj_vec_HasFDerivAt`,
`derived_convolution_decomp_unbounded_vec`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped InnerProductSpace ENNReal NNReal BigOperators MeasureTheory

namespace AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics.LowerBounds.RegularEstimator

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## The vector affine functional `ψ_proj_vec`

For an orthonormal basis `g_P : Fin m → L²₀(P)`, an efficient influence function
`IF_eff : Fin k → L²₀(P)` (vector-valued), and constant `ψ_P : EuclideanSpace ℝ (Fin k)`,
define `ψ_proj_vec g_P IF_eff ψ_P θ` as the constant `ψ_P` plus the matrix product
`A·θ` where `A_{j i} = ⟪IF_eff j, g_P i⟫`.

Because `ψ_proj_vec` is **affine** in `θ`, its Fréchet derivative `ψDot_proj_vec_clm`
is its linear part `θ ↦ A·θ`, and `HasFDerivAt ψ_proj_vec ψDot_proj_vec_clm 0`
reduces to `HasFDerivAt.const_add`. No Hadamard regularity required.
-/

/-- The matrix `A : Matrix (Fin k) (Fin m) ℝ` with entries `A_{j i} = ⟪IF_eff j, g_P i⟫_ℝ`.
This encodes the (vector-valued) influence function's inner products with the basis. -/
noncomputable def ψDotMat_vec
    {m k : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)) (IF_eff : Fin k → ↥(L2ZeroMean P)) :
    Matrix (Fin k) (Fin m) ℝ :=
  fun j i => @inner ℝ _ _ (IF_eff j : ↥(L2ZeroMean P)) (g_P i)

/-- The affine functional `ψ_proj_vec : Θ m → 𝓨 k`:
`ψ_proj_vec θ := ψ_P + A·θ` where A is the matrix of inner products. -/
noncomputable def ψ_proj_vec
    {m k : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : Fin k → ↥(L2ZeroMean P)) (ψ_P : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k) :=
  fun θ =>
    ψ_P + (WithLp.equiv 2 (Fin k → ℝ)).symm
      ((ψDotMat_vec g_P IF_eff).mulVec ((WithLp.equiv 2 (Fin m → ℝ)) θ))

/-- Continuous linear map of the vector derivative: `θ ↦ A·θ` lifted into EuclideanSpace form. -/
noncomputable def ψDot_proj_vec_clm
    {m k : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)) (IF_eff : Fin k → ↥(L2ZeroMean P)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toLinearMap.comp
      ((ψDotMat_vec g_P IF_eff).mulVecLin.comp
        (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap))

/-- `ψDot_proj_vec_clm` agrees with the matrix form `ψDotMat_vec`. -/
lemma ψDot_proj_vec_clm_apply
    {m k : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)) (IF_eff : Fin k → ↥(L2ZeroMean P))
    (θ : EuclideanSpace ℝ (Fin m)) :
    ψDot_proj_vec_clm g_P IF_eff θ
      = (WithLp.equiv 2 (Fin k → ℝ)).symm
        ((ψDotMat_vec g_P IF_eff).mulVec ((WithLp.equiv 2 (Fin m → ℝ)) θ)) := rfl

/-- The j-th coordinate of `ψDot_proj_vec_clm h` equals the inner product with
the linear perturbation score. Mirrors the scalar pattern. -/
lemma ψDot_proj_vec_clm_coord_eq_inner
    {m k : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)) (IF_eff : Fin k → ↥(L2ZeroMean P))
    (θ : EuclideanSpace ℝ (Fin m)) (j : Fin k) :
    (ψDot_proj_vec_clm g_P IF_eff θ).ofLp j
      = ⟪(IF_eff j : ↥(L2ZeroMean P)), linPerturbScore g_P θ⟫_ℝ := by
  -- Unfold the CLM application and extract coordinate j
  have h_lhs : (ψDot_proj_vec_clm g_P IF_eff θ).ofLp j
      = ∑ i : Fin m,
          (@inner ℝ _ _ (IF_eff j : ↥(L2ZeroMean P)) (g_P i))
            * θ.ofLp i := by
    rw [ψDot_proj_vec_clm_apply]
    rfl
  -- Use the linPerturbScore definition and match via sum
  rw [h_lhs, linPerturbScore, inner_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [inner_smul_right]
  change ⟪(IF_eff j : ↥(L2ZeroMean P)), g_P i⟫_ℝ * θ.ofLp i
    = θ.ofLp i * ⟪(IF_eff j : ↥(L2ZeroMean P)), g_P i⟫_ℝ
  ring

/-- `ψ_proj_vec θ = ψ_P + ψDot_proj_vec_clm θ` (algebraic affine decomp). -/
lemma ψ_proj_vec_eq_const_add
    {m k : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : Fin k → ↥(L2ZeroMean P)) (ψ_P : EuclideanSpace ℝ (Fin k)) :
    ψ_proj_vec g_P IF_eff ψ_P
      = fun θ => ψ_P + ψDot_proj_vec_clm g_P IF_eff θ := by
  funext θ
  -- Both sides are vectors in EuclideanSpace ℝ (Fin k); compare at every coord.
  ext j
  -- LHS coord j: ψ_P j + ⟪IF_eff j, linPerturbScore g_P θ⟫.
  have h_lhs :
      (ψ_proj_vec g_P IF_eff ψ_P θ).ofLp j
        = ψ_P.ofLp j + ⟪(IF_eff j : ↥(L2ZeroMean P)),
            linPerturbScore g_P θ⟫_ℝ := by
    unfold ψ_proj_vec
    have h_add :
        ((ψ_P + (WithLp.equiv 2 (Fin k → ℝ)).symm
            ((ψDotMat_vec g_P IF_eff).mulVec
              ((WithLp.equiv 2 (Fin m → ℝ)) θ))).ofLp j : ℝ)
          = ψ_P.ofLp j +
              ((WithLp.equiv 2 (Fin k → ℝ)).symm
                ((ψDotMat_vec g_P IF_eff).mulVec
                  ((WithLp.equiv 2 (Fin m → ℝ)) θ))).ofLp j := rfl
    rw [h_add]
    -- Coordinate j of the lifted matrix product is the matrix dot row j with θ.
    have h_coord :
        ((WithLp.equiv 2 (Fin k → ℝ)).symm
          ((ψDotMat_vec g_P IF_eff).mulVec
            ((WithLp.equiv 2 (Fin m → ℝ)) θ))).ofLp j
          = ∑ i : Fin m,
              (ψDotMat_vec g_P IF_eff j i)
                * ((WithLp.equiv 2 (Fin m → ℝ)) θ) i := rfl
    rw [h_coord]
    -- The sum coincides with ⟪IF_eff j, linPerturbScore g_P θ⟫.
    have h_inner :
        ∑ i : Fin m,
            (ψDotMat_vec g_P IF_eff j i) * ((WithLp.equiv 2 (Fin m → ℝ)) θ) i
          = ⟪(IF_eff j : ↥(L2ZeroMean P)),
              linPerturbScore g_P θ⟫_ℝ := by
      rw [show linPerturbScore g_P θ
            = ∑ i : Fin m,
                ((WithLp.equiv 2 (Fin m → ℝ)) θ) i • g_P i from rfl,
          inner_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [inner_smul_right]
      change ⟪(IF_eff j : ↥(L2ZeroMean P)), g_P i⟫_ℝ
            * ((WithLp.equiv 2 (Fin m → ℝ)) θ) i
          = ((WithLp.equiv 2 (Fin m → ℝ)) θ) i
            * ⟪(IF_eff j : ↥(L2ZeroMean P)), g_P i⟫_ℝ
      ring
    rw [h_inner]
  -- RHS coord j: ψ_P j + (ψDot_proj_vec_clm θ).ofLp j, which is the same by the
  -- coordinate lemma.
  have h_rhs :
      (ψ_P + ψDot_proj_vec_clm g_P IF_eff θ).ofLp j
        = ψ_P.ofLp j + ⟪(IF_eff j : ↥(L2ZeroMean P)),
            linPerturbScore g_P θ⟫_ℝ := by
    have h_add :
        ((ψ_P + ψDot_proj_vec_clm g_P IF_eff θ).ofLp j : ℝ)
          = ψ_P.ofLp j + (ψDot_proj_vec_clm g_P IF_eff θ).ofLp j := rfl
    rw [h_add, ψDot_proj_vec_clm_coord_eq_inner g_P IF_eff θ j]
  change (ψ_proj_vec g_P IF_eff ψ_P θ).ofLp j
      = (ψ_P + ψDot_proj_vec_clm g_P IF_eff θ).ofLp j
  rw [h_lhs, h_rhs]

/-- `ψ_proj_vec` has Fréchet derivative `ψDot_proj_vec_clm` at 0 (and in fact at every point). -/
theorem ψ_proj_vec_HasFDerivAt
    {m k : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : Fin k → ↥(L2ZeroMean P)) (ψ_P : EuclideanSpace ℝ (Fin k)) :
    HasFDerivAt (ψ_proj_vec g_P IF_eff ψ_P) (ψDot_proj_vec_clm g_P IF_eff) 0 := by
  rw [ψ_proj_vec_eq_const_add g_P IF_eff ψ_P]
  exact (ψDot_proj_vec_clm g_P IF_eff).hasFDerivAt.const_add _

/-! ## Identity wrapper for vector estimators -/

/-- Identity wrapper: a vector-valued estimator `T_n` is mapped to itself.
Vector-form analogue of the scalar `T_param_of`, with no `Fin 1` / `single 0`
machinery. -/
def T_param_of_vec
    {k : ℕ} (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k)) :
    ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k) :=
  T_n

/-- Measurability is preserved under the identity wrapper. -/
theorem T_param_of_vec_measurable
    {k : ℕ} {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k)}
    (hT_meas : ∀ n, Measurable (T_n n)) :
    ∀ n, Measurable (T_param_of_vec T_n n) :=
  hT_meas


open AsymptoticStatistics.Core.PathwiseVec
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.LowerBounds.RegularEstimatorVec

/-! ## Per-`h` product-measure weak convergence (vec target) -/

/-- Per-`h` vector weak convergence under `unboundedParamSubmodel`, recentered at
`ψ_proj_vec`. Vector analogue of
`ConvolutionUnbounded.productMeasure_unbounded_pushforward_scalar_at_perturbed_truth`. -/
private theorem productMeasure_unbounded_pushforward_vec_target
    (T_set : TangentSpec P)
    {k : ℕ}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_broad_vec P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    ∀ h : EuclideanSpace ℝ (Fin m),
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n n X - ψ_proj_vec g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h))))
        L := by
  classical
  intro h
  -- The score of the per-direction QMDPath is `linPerturbScore g_P h`. It lies in
  -- the algebraic span (consumed by the regularity hypothesis `hReg`); lift to the
  -- closure for the pathwise-derivative / EIF computations below.
  have hLin_in_span :
      (linPerturbScore g_P h : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier :=
    linPerturbScore_mem_span T_set g_P h_in_T h
  have hLin_in_T :
      (linPerturbScore g_P h : ↥(L2ZeroMean P)) ∈ tangentSpace T_set :=
    span_carrier_le_tangentSpace _ hLin_in_span
  have hScore_eq :
      (unboundedParamSubmodel_oneDimPath g_P h_orth h).score
        = linPerturbScore g_P h := rfl
  -- Abbreviate the per-direction QMDPath curve.
  set γ : QMDPath P := unboundedParamSubmodel_oneDimPath g_P h_orth h with hγ_def
  -- Step 1: Apply `IsRegularEstimator_broad_vec` on the per-direction QMDPath.
  -- This gives `√n • (T_n - ψ(γ.curve (1/√n))) ⇝ L` under `Measure.pi (γ.curve _)`.
  have h_vec_at_curve :
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))))
        L :=
    hReg (linPerturbScore g_P h) hLin_in_span γ hScore_eq
  -- Step 2: Identify `Measure.pi (γ.curve _) = productMeasure unbounded P ((√n)⁻¹•h) n`.
  have h_pi_eq : ∀ n : ℕ,
      MeasureTheory.Measure.pi
          (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))
        = AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (unboundedParamSubmodel g_P h_orth) P
            ((Real.sqrt n)⁻¹ • h) n :=
    fun n =>
      AsymptoticStatistics.LowerBounds.ConvolutionUnbounded.pi_oneDimCurve_eq_productMeasure
        g_P h_orth h (Real.sqrt n)⁻¹ n
  have h_vec_pm :
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P
              ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))))
        L := by
    have h_seq_eq : (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n •
              (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))))
        = (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P
              ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹))))) := by
      funext n; rw [h_pi_eq n]
    rw [← h_seq_eq]; exact h_vec_at_curve
  -- Step 3: Deterministic shift `cn n := √n • (ψ_proj_vec((√n)⁻¹•h) - ψ(γ.curve(1/√n)))`.
  -- We will use `vec_slutsky_recentering` to swap the recentering term from
  -- `ψ(γ.curve(1/√n))` to `ψ_proj_vec((1/√n)•h)`.
  set cn : ℕ → EuclideanSpace ℝ (Fin k) := fun n =>
    Real.sqrt n • (ψ_proj_vec g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h)
        - ψ (γ.curve ((Real.sqrt n)⁻¹))) with hcn_def
  set Xn : ∀ n : ℕ, (Fin n → Ω) → EuclideanSpace ℝ (Fin k) := fun n X =>
    Real.sqrt n • (T_n n X - ψ_proj_vec g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h))
    with hXn_def
  -- Algebraic identity: Xn n X + cn n = √n • (T_n n X - ψ(γ.curve(1/√n))).
  have h_alg : ∀ n : ℕ, ∀ X : Fin n → Ω,
      Xn n X + cn n
        = Real.sqrt n • (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹))) := by
    intro n X
    rw [hXn_def, hcn_def]
    -- √n•(T_n - ψ_proj_vec) + √n•(ψ_proj_vec - ψ(curve)) = √n•(T_n - ψ(curve))
    rw [← smul_add]
    congr 1
    abel
  -- Recast h_vec_pm in the form expected by `vec_slutsky_recentering`.
  have h_weak_form :
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P
              ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω => Xn n X + cn n)) L := by
    have h_seq_eq : (fun n : ℕ =>
        (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (unboundedParamSubmodel g_P h_orth) P
            ((Real.sqrt n)⁻¹ • h) n).map
          (fun X : Fin n → Ω => Xn n X + cn n))
        = (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P
              ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹))))) := by
      funext n
      congr 1
      funext X
      exact h_alg n X
    rw [h_seq_eq]; exact h_vec_pm
  -- Step 4: Show `cn → 0`.
  -- Using `ψ_proj_vec_eq_const_add`: `ψ_proj_vec((1/√n)•h) = ψ P + ψDot_proj_vec_clm((1/√n)•h)`
  -- and the CLM is linear so `= ψ P + (1/√n) • ψDot_proj_vec_clm h`.
  -- Multiplying by √n:
  -- cn n = √n • (ψ P + (1/√n) • ψDot_proj_vec_clm h - ψ(γ.curve(1/√n)))
  --      = ψDot_proj_vec_clm h - √n • (ψ(γ.curve(1/√n)) - ψ P)   (for √n ≠ 0)
  -- And `derivative_spec` gives `√n • (ψ(γ.curve(1/√n)) - ψ P) → derivative ⟨score, _⟩`.
  -- Since `derivative ⟨linPerturbScore g_P h, _⟩ = ψDot_proj_vec_clm h` (EIF property
  -- componentwise), the limit is `ψDot_proj_vec_clm h - ψDot_proj_vec_clm h = 0`.
  -- Composition: `(fun n => (Real.sqrt n)⁻¹) → 0` from atTop with `≠ 0` eventually.
  have h_inv_tendsto :
      Filter.Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) Filter.atTop
        (nhdsWithin (0 : ℝ) {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · -- (Real.sqrt n)⁻¹ → 0
      have h_sqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt n) Filter.atTop Filter.atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      exact h_sqrt.inv_tendsto_atTop
    · -- eventually `(Real.sqrt n)⁻¹ ∈ {0}ᶜ` i.e. `≠ 0`
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpos : (0 : ℝ) < Real.sqrt n :=
        Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hn1)
      exact Set.mem_compl_singleton_iff.mpr (inv_ne_zero hpos.ne')
  -- Apply derivative_spec at the curve `γ` with score `linPerturbScore g_P h`.
  have hψ_diff_spec :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (ψ (γ.curve t) - ψ P))
        (nhdsWithin 0 {0}ᶜ)
        (nhds (hψ.derivative ⟨γ.score, by rw [hScore_eq]; exact hLin_in_T⟩)) :=
    hψ.derivative_spec γ (by rw [hScore_eq]; exact hLin_in_T)
  -- Compose: along `n` via `(Real.sqrt n)⁻¹`, we get
  -- `((Real.sqrt n)⁻¹)⁻¹ • (ψ (γ.curve (1/√n)) - ψ P) → derivative ⟨…⟩`.
  -- Note `((Real.sqrt n)⁻¹)⁻¹ = Real.sqrt n` for `Real.sqrt n ≠ 0`, but the limit
  -- statement uses the literal `t⁻¹` so we'll convert below.
  have h_quot_tendsto :
      Filter.Tendsto
        (fun n : ℕ => ((Real.sqrt n)⁻¹)⁻¹ • (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P))
        Filter.atTop
        (nhds (hψ.derivative ⟨γ.score, by rw [hScore_eq]; exact hLin_in_T⟩)) :=
    hψ_diff_spec.comp h_inv_tendsto
  -- Convert `((Real.sqrt n)⁻¹)⁻¹ • _` to `Real.sqrt n • _` eventually (n ≥ 1).
  have h_sqrt_smul_tendsto :
      Filter.Tendsto
        (fun n : ℕ => Real.sqrt n • (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P))
        Filter.atTop
        (nhds (hψ.derivative ⟨γ.score, by rw [hScore_eq]; exact hLin_in_T⟩)) := by
    refine h_quot_tendsto.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < Real.sqrt n :=
      Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hn1)
    have h_inv_inv : ((Real.sqrt n)⁻¹)⁻¹ = Real.sqrt n := inv_inv _
    rw [h_inv_inv]
  -- Identify `hψ.derivative ⟨linPerturbScore g_P h, _⟩ = ψDot_proj_vec_clm g_P IF_eff h`.
  have h_deriv_eq :
      hψ.derivative ⟨γ.score, by rw [hScore_eq]; exact hLin_in_T⟩
        = ψDot_proj_vec_clm g_P IF_eff h := by
    -- Compare coordinatewise via EIF property.
    ext j
    -- j-th coord of LHS via EIF for `EuclideanSpace.proj j ∘L derivative`:
    -- (proj j ∘L derivative) ⟨linPerturbScore g_P h, _⟩ = ⟪IF_eff j, linPerturbScore g_P h⟫.
    have hEIF_j : IsEfficientInfluenceFunction P (tangentSpace T_set)
        (EuclideanSpace.proj j ∘L hψ.derivative) (IF_eff j) := hEIF j
    have hIF_j := hEIF_j.1 -- IsInfluenceFunction
    -- Specialise hIF_j at `g := ⟨linPerturbScore g_P h, hLin_in_T⟩`.
    have h_coord_lhs :
        (hψ.derivative ⟨γ.score, by rw [hScore_eq]; exact hLin_in_T⟩).ofLp j
          = ⟪(IF_eff j : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫_ℝ := by
      have hg_eq : (⟨γ.score, by rw [hScore_eq]; exact hLin_in_T⟩
            : tangentSpace T_set)
            = ⟨(linPerturbScore g_P h : ↥(L2ZeroMean P)), hLin_in_T⟩ := by
        apply Subtype.ext
        change γ.score = linPerturbScore g_P h
        exact hScore_eq
      rw [hg_eq]
      have h_apply := hIF_j ⟨(linPerturbScore g_P h : ↥(L2ZeroMean P)), hLin_in_T⟩
      -- h_apply: ⟪IF_eff j, linPerturbScore g_P h⟫ = (proj j ∘L derivative) ⟨…⟩.
      -- And (proj j ∘L derivative) ⟨…⟩ = (derivative ⟨…⟩).ofLp j definitionally.
      have h_proj_eq :
          (EuclideanSpace.proj j ∘L hψ.derivative)
              ⟨(linPerturbScore g_P h : ↥(L2ZeroMean P)), hLin_in_T⟩
            = (hψ.derivative
                ⟨(linPerturbScore g_P h : ↥(L2ZeroMean P)), hLin_in_T⟩).ofLp j := rfl
      rw [h_proj_eq] at h_apply
      exact h_apply.symm
    -- j-th coord of RHS: ψDot_proj_vec_clm g_P IF_eff h)
    --                                = ⟪IF_eff j, linPerturbScore g_P h⟫.
    have h_coord_rhs :
        (ψDot_proj_vec_clm g_P IF_eff h).ofLp j
          = ⟪(IF_eff j : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫_ℝ :=
      ψDot_proj_vec_clm_coord_eq_inner g_P IF_eff h j
    rw [h_coord_lhs, h_coord_rhs]
  -- Rewrite the limit using h_deriv_eq.
  rw [h_deriv_eq] at h_sqrt_smul_tendsto
  -- Now show cn n = ψDot_proj_vec_clm g_P IF_eff h - √n • (ψ (γ.curve (1/√n)) - ψ P)
  -- eventually (n ≥ 1 needed because of inv arithmetic), and so cn → 0.
  have h_cn_eq : ∀ᶠ n : ℕ in Filter.atTop,
      cn n = ψDot_proj_vec_clm g_P IF_eff h
              - Real.sqrt n • (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < Real.sqrt n :=
      Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hn1)
    have hne : Real.sqrt n ≠ 0 := hpos.ne'
    -- Unfold cn definition.
    change Real.sqrt n • (ψ_proj_vec g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h)
              - ψ (γ.curve ((Real.sqrt n)⁻¹)))
        = ψDot_proj_vec_clm g_P IF_eff h
              - Real.sqrt n • (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P)
    -- ψ_proj_vec((1/√n)•h) = ψ P + ψDot_proj_vec_clm((1/√n)•h)
    --                     = ψ P + (1/√n) • ψDot_proj_vec_clm h.
    have h_psi_proj :
        ψ_proj_vec g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h)
          = ψ P + (Real.sqrt n)⁻¹ • ψDot_proj_vec_clm g_P IF_eff h := by
      rw [ψ_proj_vec_eq_const_add g_P IF_eff (ψ P)]
      -- After rewrite, goal LHS is `(fun θ ↦ ψ P + clm θ) ((√n)⁻¹ • h)` (not β-reduced).
      change ψ P + ψDot_proj_vec_clm g_P IF_eff ((Real.sqrt n)⁻¹ • h)
          = ψ P + (Real.sqrt n)⁻¹ • ψDot_proj_vec_clm g_P IF_eff h
      rw [(ψDot_proj_vec_clm g_P IF_eff).map_smul]
    rw [h_psi_proj]
    -- Now goal: √n • (ψ P + (1/√n) • ψDot_proj_vec_clm h - ψ(γ.curve(1/√n)))
    --        = ψDot_proj_vec_clm h - √n • (ψ(γ.curve(1/√n)) - ψ P)
    have h_smul_inv : Real.sqrt n • ((Real.sqrt n)⁻¹ • ψDot_proj_vec_clm g_P IF_eff h)
        = ψDot_proj_vec_clm g_P IF_eff h := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [smul_sub, smul_add, h_smul_inv, smul_sub]
    abel
  -- Conclude cn → 0 from `h_sqrt_smul_tendsto`.
  have h_cn_tendsto : Filter.Tendsto cn Filter.atTop (nhds (0 : EuclideanSpace ℝ (Fin k))) := by
    have h_diff_tendsto :
        Filter.Tendsto
          (fun n : ℕ => ψDot_proj_vec_clm g_P IF_eff h
              - Real.sqrt n • (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P))
          Filter.atTop
          (nhds (ψDot_proj_vec_clm g_P IF_eff h - ψDot_proj_vec_clm g_P IF_eff h)) :=
      tendsto_const_nhds.sub h_sqrt_smul_tendsto
    have h_sub_self : ψDot_proj_vec_clm g_P IF_eff h - ψDot_proj_vec_clm g_P IF_eff h
        = (0 : EuclideanSpace ℝ (Fin k)) := sub_self _
    rw [h_sub_self] at h_diff_tendsto
    exact h_diff_tendsto.congr' (h_cn_eq.mono fun n hn => hn.symm)
  -- Step 5: Conclude via `vec_slutsky_recentering`.
  -- We need AEMeasurability of Xn n. Each Xn is measurable since T_n is.
  have hXn_aemeas : ∀ n,
      AEMeasurable (Xn n)
        (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
          (unboundedParamSubmodel g_P h_orth) P ((Real.sqrt n)⁻¹ • h) n) := by
    intro n
    refine Measurable.aemeasurable ?_
    -- √n • (T_n n - const) is measurable.
    have h1 : Measurable (fun X : Fin n → Ω => T_n n X) := hT_meas n
    have h2 : Measurable (fun X : Fin n → Ω =>
        T_n n X - ψ_proj_vec g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h)) :=
      h1.sub_const _
    exact h2.const_smul (Real.sqrt n)
  -- IsProbabilityMeasure instance for the product measure (needed by vec_slutsky_recentering).
  haveI h_prod_isProb : ∀ n : ℕ, IsProbabilityMeasure
      (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
        (unboundedParamSubmodel g_P h_orth) P ((Real.sqrt n)⁻¹ • h) n) := fun n =>
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      (unboundedParamSubmodel g_P h_orth) P
      (unboundedParamSubmodel_isPDFOf g_P h_orth)
      ((Real.sqrt n)⁻¹ • h) n
  -- Apply the bridge.
  exact AsymptoticStatistics.ForMathlib.vec_slutsky_recentering
    hXn_aemeas h_weak_form h_cn_tendsto

/-! ## `RegularEstimatorSequence` constructor (vec) -/

/-- Wrap vec weak convergence into `RegularEstimatorSequence` structure. -/
noncomputable def unboundedParamSubmodel_RegularEstimatorSequence_vec
    (T_set : TangentSpec P)
    {k : ℕ}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_broad_vec P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    AsymptoticStatistics.ParametricFamily.RegularEstimatorSequence
      (unboundedParamSubmodel g_P h_orth) P (0 : EuclideanSpace ℝ (Fin m))
      (ψ_proj_vec g_P IF_eff (ψ P)) (T_param_of_vec T_n) where
  limitDist := L
  isProb := inferInstance
  tendsto h := by
    have := productMeasure_unbounded_pushforward_vec_target
      T_set hψ hEIF T_n hT_meas hReg g_P h_orth h_in_T h
    simpa [zero_add] using! this

/-! ## Main vec convolution decomposition -/

/-- **Vector convolution decomposition** (vec extension of
    `ConvolutionUnbounded.derived_convolution_decomp_unbounded`).

For vector-valued `ψ : Measure Ω → EuclideanSpace ℝ (Fin k)` with vec regular estimator
and vec efficient influence function `IF_eff : Fin k → L²₀(P)`, the limit law decomposes
as a multivariate Gaussian convolution (no `Fin 1` / `single 0` collapsing).
-/
theorem derived_convolution_decomp_unbounded_vec
    (T_set : TangentSpec P)
    {k : ℕ}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_broad_vec P T_set ψ hψ hEIF T_n L) :
    ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
      Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)) →
      (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) →
      ∃ M_per : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure M_per ∧
        L = MeasureTheory.Measure.conv
              (ProbabilityTheory.multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin k))
                (ψDotMat_vec g_P IF_eff *
                  (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
                  (ψDotMat_vec g_P IF_eff).transpose))
              M_per := by
  intro m g_P h_orth h_in_T
  classical
  let hReg_param := unboundedParamSubmodel_RegularEstimatorSequence_vec
    T_set hψ hEIF T_n hT_meas hReg g_P h_orth h_in_T
  have h_gP_total_meas : Measurable (g_P_total g_P) := by
    unfold g_P_total
    exact (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp
      (measurable_pi_iff.mpr (fun i => gMk_meas g_P i))
  have h_paramSub_hJ_fisher :
      ∀ u v : EuclideanSpace ℝ (Fin m),
        fisherInformation
            (unboundedParamSubmodel g_P h_orth) P 0 (g_P_total g_P) u v
          = @inner ℝ _ _ u
              ((WithLp.equiv 2 _).symm
                ((1 : Matrix (Fin m) (Fin m) ℝ).mulVec ((WithLp.equiv 2 _) v))) := by
    intro u v
    rw [unboundedParamSubmodel_fisher_info g_P h_orth u v,
      Matrix.one_mulVec, Equiv.symm_apply_apply]
  have hψ_diff := ψ_proj_vec_HasFDerivAt g_P IF_eff (ψ P)
  have hT_param_meas : ∀ n, Measurable (T_param_of_vec T_n n) :=
    T_param_of_vec_measurable hT_meas
  obtain ⟨M_θ, hM_θ_prob, hConv⟩ :=
    AsymptoticStatistics.HajekLeCamConvolution.hajek_le_cam_convolution_theorem
      (unboundedParamSubmodel g_P h_orth)
      P 0 (g_P_total g_P)
      h_gP_total_meas
      (unboundedParamSubmodel_DQM g_P h_orth)
      (1 : Matrix (Fin m) (Fin m) ℝ) Matrix.PosDef.one
      h_paramSub_hJ_fisher
      (ψ_proj_vec g_P IF_eff (ψ P)) (ψDot_proj_vec_clm g_P IF_eff) hψ_diff
      (ψDotMat_vec g_P IF_eff)
      (fun h => ψDot_proj_vec_clm_apply g_P IF_eff h)
      (T_param_of_vec T_n) hT_param_meas hReg_param
      (unboundedParamSubmodel_isPDFOf g_P h_orth)
  haveI := hM_θ_prob
  refine ⟨M_θ, hM_θ_prob, ?_⟩
  -- hReg_param.limitDist = L by construction.
  exact hConv

end AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec
