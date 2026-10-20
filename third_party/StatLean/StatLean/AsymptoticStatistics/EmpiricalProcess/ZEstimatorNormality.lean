module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.InfiniteDimZEstimator
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ParametricClassDonsker
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import StatLean.AsymptoticStatistics.ForMathlib.SlutskyVec
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.AsymptoticStatistics.ParametricFamily.ScoreCLT

@[expose] public section

/-!
# Finite-dimensional Z-estimator asymptotic normality (vdV Theorem 5.21)

This file specializes the infinite-dimensional Z-estimator theorem
(`infinite_dim_z_estimator`, vdV Thm 19.26) to the classical finite-dimensional
Z-estimator of vdV §5.3: `θ ∈` an open subset of Euclidean space `ℝᵏ`, `k`
estimating functions `ψ_{θ,h}` (`h ∈ Fin k`), with `θ ↦ Pψ_θ` differentiable at a
zero `θ₀` with nonsingular derivative matrix `V`. Under `P‖ψ_{θ₀}‖² < ∞`, the
`o_P(n^{-1/2})` estimating equation, and `θ̂ₙ →ₚ θ₀`,

    √n(θ̂ₙ − θ₀) = −V⁻¹ √n ℙₙψ_{θ₀} + o_P(1),

and in particular `√n(θ̂ₙ − θ₀) ⇝ N(0, V⁻¹ P[ψ_{θ₀}ψ_{θ₀}ᵀ] (V⁻¹)ᵀ)`.

The limit covariance `psiCov = P[ψ_{θ₀}ψ_{θ₀}ᵀ]` is constructed explicitly;
`psiCov_posSemidef` and `psiCov_variance_eq` establish the properties needed
for the multivariate central limit theorem. The final declaration
`zEstimator_asymptotic_normality` derives the required Donsker property from
the Lipschitz assumptions of vdV Example 19.7.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace Matrix ProbabilityTheory

/-! ### Setup and abbreviations -/

/-- **Linear map `Vlin V : ℝᵏ →ₗ ℝᵏ`.** Bridges the
Euclidean parameter space `EuclideanSpace ℝ (Fin k)` to the plain `Fin k → ℝ`
codomain of the derivative field `V` in Theorem 19.26, by first forgetting the
`L²` structure (`WithLp.linearEquiv`) and then applying the matrix `V`
(`Matrix.mulVecLin`). Its
bounded-below field is discharged by `matrix_bddbelow_of_isUnit_det`. -/
noncomputable def Vlin {k : ℕ} (V : Matrix (Fin k) (Fin k) ℝ) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] (Fin k → ℝ) :=
  (Matrix.mulVecLin V) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap

/-- **ψ bundled as a Euclidean vector.** Collects the `k` estimating
functions `h ↦ ψ_{θ,h}(ω)` into a single `EuclideanSpace ℝ (Fin k)` point via the
`L²` re-tagging `(WithLp.equiv 2 _).symm`. This is the vector whose CLT / Gaussian
limit (`P‖ψ_{θ₀}‖² < ∞` is `MemLp (psiVec ψ θ₀) 2 P`). -/
noncomputable def psiVec {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ : EuclideanSpace ℝ (Fin k)) (ω : Ω) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun h => ψ θ h ω)

/-- **Vector empirical process** `𝔾ₙψ_θ` bundled into `EuclideanSpace ℝ (Fin k)`.
Coordinate `h` is the scalar empirical process
`empiricalProcess P n Xs (ψ θ h)`; re-tagged into the `L²` space so the CLT and
`multivariateGaussian` apply. Its weak limit is `N(0, psiCov)`. -/
noncomputable def empiricalProcessVec {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ) (Xs : Fin n → Ω) :
    EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun h => empiricalProcess P n Xs (ψ θ h))

/-- **Limit covariance `Σ = P[ψ_{θ₀}ψ_{θ₀}ᵀ]`.** Entry `(i, j)` is
`P[ψ_{θ₀,i} ψ_{θ₀,j}]`, which
equals the covariance of `psiVec ψ θ₀` because `Pψ_{θ₀} = 0`. Its PSD
(`psiCov_posSemidef`) and directional-variance identity (`psiCov_variance_eq`) feed
the multivariate CLT and determine the Gaussian limit `N(0, V⁻¹ Σ V⁻ᵀ)`. -/
noncomputable def psiCov {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of (fun i j => ∫ x, ψ θ₀ i x * ψ θ₀ j x ∂P)

/-! ### Finite-`H` collapse of outer-probability suprema -/

/-- **Finite-`H` collapse.** For a finite index `Fin k`, `‖g_n‖_{Fin k} →ₚ 0`
in outer probability upgrades to `→ₚ 0` of the `EuclideanSpace ℝ (Fin k)`-bundled
family in the ordinary (measurable) sense: the `∃ j` exceedance event is a finite
union of measurable sets so the outer measure collapses to `μ`, and the Euclidean
norm is controlled by `√k · maxⱼ |·|`. Thus `TendstoZeroInOuterProbSup` implies
vector-valued `TendstoInProbZero`. -/
theorem tendstoInProbZero_of_tendstoZeroInOuterProbSup_fin
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) {k : ℕ}
    (g : ℕ → Ξ → Fin k → ℝ) (hg : ∀ n j, Measurable fun ξ => g n ξ j)
    (h : TendstoZeroInOuterProbSup μ g) :
    TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => ((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
        EuclideanSpace ℝ (Fin k))) := by
  intro ε hε
  set sk : ℝ := Real.sqrt k with hsk_def
  have hsk_nonneg : 0 ≤ sk := Real.sqrt_nonneg _
  have hsk_sq : sk ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  have hsk1_pos : 0 < sk + 1 := by linarith
  set ε' : ℝ := ε / (sk + 1) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε hsk1_pos
  have hε'eq : ε' * (sk + 1) = ε := by
    rw [hε'_def, div_mul_cancel₀ _ (ne_of_gt hsk1_pos)]
  -- The `ε`-exceedance of the Euclidean norm forces a coordinate above `ε'`.
  have hTS : ∀ n,
      {ξ | ε ≤ ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
          EuclideanSpace ℝ (Fin k))‖}
        ⊆ {ξ | ∃ j, ε' < |g n ξ j|} := by
    intro n ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    by_contra hcon
    push_neg at hcon
    have hnorm_sq :
        ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) : EuclideanSpace ℝ (Fin k))‖ ^ 2
          = ∑ i, |g n ξ i| ^ 2 := by
      rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change ‖g n ξ i‖ ^ 2 = |g n ξ i| ^ 2
      rw [Real.norm_eq_abs]
    have hsum_le : ∑ i, |g n ξ i| ^ 2 ≤ (k : ℝ) * ε' ^ 2 := by
      calc ∑ i, |g n ξ i| ^ 2 ≤ ∑ _i : Fin k, ε' ^ 2 :=
            Finset.sum_le_sum (fun i _ => by
              nlinarith [hcon i, abs_nonneg (g n ξ i), hε'_pos.le])
        _ = (k : ℝ) * ε' ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hεsq : ε ^ 2 ≤ (k : ℝ) * ε' ^ 2 := by
      have h1 : ε ^ 2 ≤ ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
          EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
        nlinarith [norm_nonneg ((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
          EuclideanSpace ℝ (Fin k)), hε.le]
      rw [hnorm_sq] at h1
      exact le_trans h1 hsum_le
    nlinarith [hsk_sq, hε'eq, hε'_pos, hsk_nonneg, hεsq]
  -- The `∃j`-events are dominated by the outer-measure events, which vanish.
  have hμ_tendsto : Tendsto (fun n => μ {ξ | ε ≤ ‖((WithLp.equiv 2 (Fin k → ℝ)).symm
      (g n ξ) : EuclideanSpace ℝ (Fin k))‖}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h ε' hε'_pos)
      (Eventually.of_forall fun n => zero_le)
      (Eventually.of_forall fun n =>
        (measure_le_outerMeasureStar μ _).trans (outerMeasureStar_mono μ (hTS n)))
  simp only [measureReal_def]
  have hcomp := (ENNReal.tendsto_toReal (by simp)).comp hμ_tendsto
  rwa [ENNReal.toReal_zero] at hcomp

/-! ### An invertible matrix is bounded below on `ℝᵏ` -/

/-- **`IsUnit V.det` implies that `Vlin V` is bounded below.** An invertible finite-dimensional
matrix is bounded below: `‖b‖ = ‖V⁻¹(V b)‖ ≤ ‖V⁻¹‖ · ‖V b‖₂ ≤ ‖V⁻¹‖ · √k · supⱼ|V b_j|`,
so with `c = 1/(‖V⁻¹‖ √k)`, `c‖b‖ ≤ supⱼ|Vlin V b_j| ≤ ⨆ⱼ ofReal|Vlin V b_j|`. This
discharges the `bddbelow_V` field of `Theorem19_26Hyp` from `hV`. -/
theorem matrix_bddbelow_of_isUnit_det {k : ℕ} (V : Matrix (Fin k) (Fin k) ℝ)
    (hV : IsUnit V.det) :
    ∃ c : ℝ, 0 < c ∧ ∀ b : EuclideanSpace ℝ (Fin k),
      ENNReal.ofReal (c * ‖b‖) ≤ ⨆ h, ENNReal.ofReal |Vlin V b h| := by
  -- `Vlin V b h` is the `h`-coordinate of the `L²` map `toEuclideanCLM V b`.
  have hcoord : ∀ (b : EuclideanSpace ℝ (Fin k)) (h : Fin k),
      Vlin V b h = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V) b h := fun b h => rfl
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: everything is `0`.
    refine ⟨1, one_pos, fun b => ?_⟩
    have hb : ‖b‖ = 0 := by rw [EuclideanSpace.norm_eq]; subst hk0; simp
    rw [hb, mul_zero, ENNReal.ofReal_zero]
    exact zero_le
  · haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    set S := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹ with hS
    set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V with hT
    -- `S ∘ T = id`, so `‖b‖ ≤ ‖S‖ · ‖T b‖`.
    have hInv : S * T = 1 := by
      rw [hS, hT, ← map_mul, Matrix.nonsing_inv_mul V hV, map_one]
    have hST : ∀ b : EuclideanSpace ℝ (Fin k), S (T b) = b := by
      intro b
      rw [← ContinuousLinearMap.mul_apply, hInv, ContinuousLinearMap.one_apply]
    set sk : ℝ := Real.sqrt k with hsk
    have hsk_nonneg : 0 ≤ sk := Real.sqrt_nonneg _
    have hsk_sq : sk ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
    have hsk_pos : 0 < sk := by rw [hsk]; exact Real.sqrt_pos.mpr (by exact_mod_cast hk)
    have hden_pos : 0 < (‖S‖ + 1) * sk := mul_pos (by positivity) hsk_pos
    refine ⟨1 / ((‖S‖ + 1) * sk), div_pos one_pos hden_pos, fun b => ?_⟩
    -- Pick a coordinate `h₀` realizing the sup of `|T b|`.
    obtain ⟨h₀, hmax⟩ := Finite.exists_max (fun h => |(T b) h|)
    -- `‖T b‖ ≤ sk · |(T b) h₀|`.
    have hnormTb : ‖T b‖ ≤ sk * |(T b) h₀| := by
      have hsq_le : ‖T b‖ ^ 2 ≤ (sk * |(T b) h₀|) ^ 2 := by
        have hnorm_sq : ‖T b‖ ^ 2 = ∑ h, |(T b) h| ^ 2 := by
          rw [EuclideanSpace.norm_eq,
            Real.sq_sqrt (Finset.sum_nonneg (fun h _ => by positivity))]
          exact Finset.sum_congr rfl (fun h _ => by rw [Real.norm_eq_abs])
        rw [hnorm_sq, mul_pow, hsk_sq]
        calc ∑ h, |(T b) h| ^ 2 ≤ ∑ _h : Fin k, |(T b) h₀| ^ 2 :=
              Finset.sum_le_sum (fun h _ => by
                nlinarith [hmax h, abs_nonneg ((T b) h), abs_nonneg ((T b) h₀)])
          _ = (k : ℝ) * |(T b) h₀| ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h1 := Real.sqrt_le_sqrt hsq_le
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h1
    -- `‖b‖ ≤ ‖S‖ · ‖T b‖`.
    have hb_le : ‖b‖ ≤ ‖S‖ * ‖T b‖ := by
      have := ContinuousLinearMap.le_opNorm S (T b)
      rwa [hST b] at this
    -- `c · ‖b‖ ≤ |(T b) h₀|`.
    have hc_le : (1 / ((‖S‖ + 1) * sk)) * ‖b‖ ≤ |(T b) h₀| := by
      have hchain : ‖b‖ ≤ (‖S‖ + 1) * sk * |(T b) h₀| := by
        calc ‖b‖ ≤ ‖S‖ * ‖T b‖ := hb_le
          _ ≤ ‖S‖ * (sk * |(T b) h₀|) :=
              mul_le_mul_of_nonneg_left hnormTb (norm_nonneg _)
          _ ≤ (‖S‖ + 1) * sk * |(T b) h₀| := by
              nlinarith [mul_nonneg hsk_nonneg (abs_nonneg ((T b) h₀)), norm_nonneg S]
      calc (1 / ((‖S‖ + 1) * sk)) * ‖b‖
          ≤ (1 / ((‖S‖ + 1) * sk)) * ((‖S‖ + 1) * sk * |(T b) h₀|) :=
            mul_le_mul_of_nonneg_left hchain (by positivity)
        _ = |(T b) h₀| := by rw [one_div, inv_mul_cancel_left₀ (ne_of_gt hden_pos)]
    calc ENNReal.ofReal ((1 / ((‖S‖ + 1) * sk)) * ‖b‖)
        ≤ ENNReal.ofReal |(T b) h₀| := ENNReal.ofReal_le_ofReal hc_le
      _ = ENNReal.ofReal |Vlin V b h₀| := by rw [hcoord b h₀]
      _ ≤ ⨆ h, ENNReal.ofReal |Vlin V b h| :=
          le_iSup (fun h => ENNReal.ofReal |Vlin V b h|) h₀

/-! ### Properties of the covariance `psiCov` -/

/-- **`psiCov` is positive semidefinite.** `psiCov = P[ψ_{θ₀}ψ_{θ₀}ᵀ]`
is a Gram-type matrix of `L²` functions, hence PSD (`t ⬝ᵥ psiCov *ᵥ t = P[⟪t, ψ⟫²] ≥ 0`;
`Matrix.posSemidef_gram`-flavored), providing the CLT assumption `hS_pos`. -/
theorem psiCov_posSemidef {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P) :
    (psiCov P ψ θ₀).PosSemidef := by
  have hψi : ∀ i, MemLp (fun ω => ψ θ₀ i ω) 2 P := fun i => hψ_L2.eval_piLp i
  have hψ_mul_int : ∀ i j, Integrable (fun x => ψ θ₀ i x * ψ θ₀ j x) P := fun i j =>
    (hψi i).integrable_mul (hψi j)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · -- Hermitian: `∫ ψⱼψᵢ = ∫ ψᵢψⱼ`.
    ext i j
    simp only [psiCov, Matrix.of_apply, Matrix.conjTranspose_apply, star_trivial]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  · -- Quadratic form is `∫ (∑ i, xᵢ ψ_{θ₀,i})² ≥ 0`.
    have hx : (star x : Fin k → ℝ) = x := by funext i; exact star_trivial _
    rw [hx]
    have hquad : x ⬝ᵥ (psiCov P ψ θ₀) *ᵥ x = ∫ ω, (∑ i, x i * ψ θ₀ i ω) ^ 2 ∂P := by
      have hrhs : x ⬝ᵥ (psiCov P ψ θ₀) *ᵥ x
          = ∑ i, ∑ j, (x i * x j) * ∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P := by
        simp only [dotProduct, Matrix.mulVec, psiCov, Matrix.of_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hint : ∫ ω, (∑ i, x i * ψ θ₀ i ω) ^ 2 ∂P
          = ∑ i, ∑ j, (x i * x j) * ∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P := by
        calc ∫ ω, (∑ i, x i * ψ θ₀ i ω) ^ 2 ∂P
            = ∫ ω, ∑ i, ∑ j, (x i * x j) * (ψ θ₀ i ω * ψ θ₀ j ω) ∂P := by
              apply integral_congr_ae
              filter_upwards with ω
              rw [sq, Finset.sum_mul_sum]
              exact Finset.sum_congr rfl
                (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
          _ = ∑ i, ∫ ω, ∑ j, (x i * x j) * (ψ θ₀ i ω * ψ θ₀ j ω) ∂P :=
              integral_finset_sum _ (fun i _ => integrable_finset_sum _
                (fun j _ => (hψ_mul_int i j).const_mul _))
          _ = ∑ i, ∑ j, (x i * x j) * ∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [integral_finset_sum _ (fun j _ => (hψ_mul_int i j).const_mul _)]
              exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
      rw [hrhs, hint]
    rw [hquad]
    exact integral_nonneg (fun ω => sq_nonneg _)

/-- **Directional variance identity.** With `Pψ_{θ₀} = 0`,
`Var[⟪t, psiVec ψ θ₀ ·⟫] = t ⬝ᵥ psiCov *ᵥ t` for every direction `t`: the inner
product `⟪t, psiVec⟫ = ∑ⱼ tⱼ ψ_{θ₀,j}` is a linear combination whose variance is the
quadratic form `∑ᵢⱼ tᵢ tⱼ P[ψ_{θ₀,i}ψ_{θ₀,j}]` (using `Pψ_{θ₀} = 0` to drop the mean
correction), providing the CLT assumption `hS_eq`. -/
theorem psiCov_variance_eq {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hPθ₀_zero : ∀ i, ∫ x, ψ θ₀ i x ∂P = 0) :
    ∀ t : EuclideanSpace ℝ (Fin k),
      Var[fun ω => ⟪t, psiVec ψ θ₀ ω⟫; P] = t ⬝ᵥ (psiCov P ψ θ₀) *ᵥ t := by
  -- Each coordinate `ψ_{θ₀,i}` is `L²(P)`; products are `L¹`.
  have hψi : ∀ i, MemLp (fun ω => ψ θ₀ i ω) 2 P := fun i => hψ_L2.eval_piLp i
  have hψ_int : ∀ i, Integrable (fun ω => ψ θ₀ i ω) P := fun i =>
    (hψi i).integrable (by norm_num)
  have hψ_mul_int : ∀ i j, Integrable (fun x => ψ θ₀ i x * ψ θ₀ j x) P := fun i j =>
    (hψi i).integrable_mul (hψi j)
  intro t
  -- `⟪t, psiVec ψ θ₀ ω⟫ = ∑ i, t i * ψ_{θ₀,i} ω`.
  have hinner_eq : (fun ω => ⟪t, psiVec ψ θ₀ ω⟫) = fun ω => ∑ i, t i * ψ θ₀ i ω := by
    funext ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (ψ θ₀ i ω * t i : ℝ) = t i * ψ θ₀ i ω
    ring
  rw [hinner_eq]
  have hgt_memLp : MemLp (fun ω => ∑ i, t i * ψ θ₀ i ω) 2 P :=
    memLp_finset_sum Finset.univ (fun i _ => (hψi i).const_mul (t i))
  -- Mean is zero, second moment is the quadratic form.
  have hmean : ∫ ω, (∑ i, t i * ψ θ₀ i ω) ∂P = 0 := by
    rw [integral_finset_sum _ (fun i _ => (hψ_int i).const_mul (t i))]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [integral_const_mul, hPθ₀_zero i, mul_zero]
  have hsq : ∫ ω, (∑ i, t i * ψ θ₀ i ω) ^ 2 ∂P
      = ∑ i, ∑ j, (t i * t j) * ∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P := by
    calc ∫ ω, (∑ i, t i * ψ θ₀ i ω) ^ 2 ∂P
        = ∫ ω, ∑ i, ∑ j, (t i * t j) * (ψ θ₀ i ω * ψ θ₀ j ω) ∂P := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      _ = ∑ i, ∫ ω, ∑ j, (t i * t j) * (ψ θ₀ i ω * ψ θ₀ j ω) ∂P :=
          integral_finset_sum _ (fun i _ => integrable_finset_sum _
            (fun j _ => (hψ_mul_int i j).const_mul _))
      _ = ∑ i, ∑ j, (t i * t j) * ∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [integral_finset_sum _ (fun j _ => (hψ_mul_int i j).const_mul _)]
          exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
  have hrhs : t ⬝ᵥ (psiCov P ψ θ₀) *ᵥ t
      = ∑ i, ∑ j, (t i * t j) * ∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P := by
    simp only [dotProduct, Matrix.mulVec, psiCov, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [variance_eq_sub hgt_memLp]
  simp only [Pi.pow_apply]
  rw [hsq, hmean, hrhs]
  ring

/-! ### Linear representation -/

/-- **Linear representation of the Z-estimator.**

Under the stated hypotheses,
`√n(θ̂ₙ − θ₀) = −V⁻¹ 𝔾ₙψ_{θ₀} + o_P(1)` in `EuclideanSpace ℝ (Fin k)`, stated as
`√n(θ̂ₙ − θ₀) + V⁻¹ 𝔾ₙψ_{θ₀} →ₚ 0`.

The theorem `infinite_dim_z_estimator`, applied to the `Theorem19_26Hyp` bundle `hyp` with
derivative `Vlin V`) gives `√n · Vlin V(θ̂ − θ₀) + 𝔾ₙψ_{θ₀} →ₚ 0` in outer-prob-sup;
`tendstoInProbZero_of_tendstoZeroInOuterProbSup_fin` collapses the finite
`Fin k` sup to Euclidean `→ₚ 0`; applying the CLM `toEuclideanCLM V⁻¹` (Lipschitz,
preserves `→ₚ 0`) with `V⁻¹ · V = id` (from `hV`) collapses the first term. -/
theorem zEstimator_linear_representation
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Set (Ω → ℝ)) (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (V : Matrix (Fin k) (Fin k) ℝ)
    (hV : IsUnit V.det) (δcls : ℝ)
    (hyp : Theorem19_26Hyp P 𝓕 ψ θ₀ (Vlin V) δcls)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (_hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖))
    (hθhat_meas' : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    (hψθ₀_meas : ∀ h, Measurable (ψ θ₀ h))
    (_hψ_joint : ∀ (n : ℕ) (h : Fin k), Measurable
      (fun p : Ξ × Ω => ψ (θ_hat n (fun i : Fin n => X i.val p.1)) h p.2))
    (h_tight : IsBoundedInOuterProbSup μ (fun n ξ h =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)))
    (h_consist : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0))
    (h_est_eq : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
        n (fun i : Fin n => X i.val ξ))) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
            (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))) := by
  classical
  -- Apply Theorem 19.26 to the outer-probability supremum of
  -- `√n · Vlin V(θ̂ − θ₀) + 𝔾ₙψ_{θ₀}`.
  have h_engine := infinite_dim_z_estimator P 𝓕 ψ θ₀ (Vlin V) δcls hyp θ_hat μ X
    hX_meas hX_indep hX_id hX_law h_tight h_consist h_est_eq
  -- Coordinatewise measurability of the resulting `ℓ∞(Fin k)` family.
  have hg_meas : ∀ (n : ℕ) (j : Fin k), Measurable (fun ξ : Ξ =>
      Real.sqrt n * Vlin V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j
        + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ j)) := by
    intro n j
    have hVterm : Measurable (fun ξ : Ξ =>
        Real.sqrt n * Vlin V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j) := by
      refine measurable_const.mul ?_
      have hclm : Measurable (fun ξ => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V
          (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :=
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V).continuous.measurable.comp
          ((hθhat_meas' n).sub measurable_const)
      exact (measurable_pi_apply j).comp
        ((MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm.measurable.comp hclm)
    have hEP : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ j)) := by
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul
        (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hψθ₀_meas j).comp (hX_meas i.val))
    exact hVterm.add hEP
  -- Collapse the finite supremum to Euclidean `→ₚ 0`.
  have h_L1 := tendstoInProbZero_of_tendstoZeroInOuterProbSup_fin μ
    (fun n ξ h => Real.sqrt n * Vlin V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h
      + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
    hg_meas h_engine
  -- Apply the (Lipschitz) inverse-derivative endomorphism `toEuclideanCLM V⁻¹`.
  have h_clm := tendstoInProbZero_clm μ
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹) h_L1
  -- `V⁻¹ ∘ V = id` on `EuclideanSpace ℝ (Fin k)`.
  have hVV : ∀ w : EuclideanSpace ℝ (Fin k),
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V w) = w := by
    intro w
    have hInv : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹
          * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul V hV, map_one]
    calc Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V w)
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹
            * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V) w := by
          rw [ContinuousLinearMap.mul_apply]
      _ = w := by rw [hInv, ContinuousLinearMap.one_apply]
  -- Pointwise identification of the collapsed vector with the target.
  have hpt : ∀ (n : ℕ) (ξ : Ξ),
      Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
            (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹
          ((WithLp.equiv 2 (Fin k → ℝ)).symm
            (fun h => Real.sqrt n * Vlin V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h
              + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))) := by
    intro n ξ
    have hsymm : (WithLp.equiv 2 (Fin k → ℝ)).symm
          (fun h => Real.sqrt n * Vlin V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h
            + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
        = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V
            (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
          + empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ) := by
      apply (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).injective
      rw [map_add]
      funext h
      rw [Pi.add_apply]
      change Real.sqrt n * Vlin V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h
          + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)
        = Vlin V (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) h
          + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hsymm, map_add, hVV]
  have hfun : (fun (n : ℕ) (ξ : Ξ) =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
      = (fun (n : ℕ) (ξ : Ξ) => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹
          ((WithLp.equiv 2 (Fin k → ℝ)).symm
            (fun h => Real.sqrt n * Vlin V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h
              + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)))) :=
    funext fun n => funext fun ξ => hpt n ξ
  rw [hfun]
  exact h_clm

/-! ### Weak limit of the vector empirical process -/

/-- **Weak limit of the vector empirical process** by the multivariate CLT.

For the iid sample and `Pψ_{θ₀} = 0`, the vector empirical process
`empiricalProcessVec P ψ θ₀ n` converges weakly to `N(0, Σ)` with `Σ = psiCov P ψ θ₀`.

The identity `Pψ_{θ₀} = 0` makes `empiricalProcess = (√n)⁻¹ ∑ᵢ ψ_{θ₀}(Xᵢ)` match the CLT
standardised statistic; `tendstoInDistribution_multivariate_clt` applied to
`Xk := psiVec ψ θ₀ ∘ X k` with `hS_eq := psiCov_variance_eq`,
`hS_pos := psiCov_posSemidef`, then reindex `Fin n ↔ range n` and bridge
`TendstoInDistribution → WeakConverges`. -/
theorem empiricalProcessVec_weakConverges
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k))
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hψθ₀_meas : ∀ h, Measurable (ψ θ₀ h))
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hPθ₀_zero : ∀ i, ∫ x, ψ θ₀ i x ∂P = 0) :
    WeakConverges
      (fun n => μ.map (fun ξ =>
        empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
      (multivariateGaussian 0 (psiCov P ψ θ₀)) := by
  classical
  -- Measurability of the bundled estimating function `psiVec ψ θ₀`.
  have hpsiVec_meas : Measurable (psiVec ψ θ₀) := by
    have h1 : Measurable (fun ω => (fun h => ψ θ₀ h ω : Fin k → ℝ)) :=
      measurable_pi_iff.mpr hψθ₀_meas
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp h1
  -- The iid `EuclideanSpace`-valued sample `Y i = psiVec ∘ X i`.
  have hY_meas : ∀ i, Measurable (fun ξ => psiVec ψ θ₀ (X i ξ)) :=
    fun i => hpsiVec_meas.comp (hX_meas i)
  have hY_iid : ProbabilityTheory.iIndepFun (fun i ξ => psiVec ψ θ₀ (X i ξ)) μ :=
    hX_indep.comp (fun _ => psiVec ψ θ₀) (fun _ => hpsiVec_meas)
  have hY_ident : ∀ i, ProbabilityTheory.IdentDistrib
      (fun ξ => psiVec ψ θ₀ (X i ξ)) (fun ξ => psiVec ψ θ₀ (X 0 ξ)) μ μ :=
    fun i => (hX_id i).comp hpsiVec_meas
  have hmp : MeasureTheory.MeasurePreserving (X 0) μ P := ⟨hX_meas 0, hX_law⟩
  have hY0_L2 : MemLp (fun ξ => psiVec ψ θ₀ (X 0 ξ)) 2 μ :=
    hψ_L2.comp_measurePreserving hmp
  -- Integrability of the coordinate functions and their products under `P`.
  have hψi : ∀ i, MemLp (fun ω => ψ θ₀ i ω) 2 P := fun i => hψ_L2.eval_piLp i
  have hψ_int : ∀ i, Integrable (fun ω => ψ θ₀ i ω) P := fun i =>
    (hψi i).integrable (by norm_num)
  have hψ_mul_int : ∀ i j, Integrable (fun x => ψ θ₀ i x * ψ θ₀ j x) P := fun i j =>
    (hψi i).integrable_mul (hψi j)
  -- Inner-product expansion `⟪u, psiVec ω⟫ = ∑ i, u i · ψ_{θ₀,i} ω`.
  have hinner : ∀ (u : EuclideanSpace ℝ (Fin k)) (ω : Ω),
      (⟪u, psiVec ψ θ₀ ω⟫ : ℝ) = ∑ i, u i * ψ θ₀ i ω := by
    intro u ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (ψ θ₀ i ω * u i : ℝ) = u i * ψ θ₀ i ω
    ring
  -- Pushforward transport `∫ F(X₀ ·) dμ = ∫ F dP`.
  have htrans : ∀ (F : Ω → ℝ), AEStronglyMeasurable F P →
      ∫ ξ, F (X 0 ξ) ∂μ = ∫ ω, F ω ∂P := by
    intro F hF
    have hF_map : AEStronglyMeasurable F (μ.map (X 0)) := by rw [hX_law]; exact hF
    have hmap := integral_map (φ := X 0) (μ := μ) (hX_meas 0).aemeasurable hF_map
    rw [hX_law] at hmap
    exact hmap.symm
  -- Apply the multivariate score CLT of `ScoreCLT`.
  have hCLT := ParametricFamily.ScoreCLT.clt_finDim (Ω := Ξ) μ
    (fun i ξ => psiVec ψ θ₀ (X i ξ)) hY_meas hY_iid hY_ident
    (fun u => by
      refine (htrans (fun ω => (⟪u, psiVec ψ θ₀ ω⟫ : ℝ))
        ((show Continuous (fun w : EuclideanSpace ℝ (Fin k) => ⟪u, w⟫) from
            continuous_const.inner continuous_id).comp_aestronglyMeasurable
              hψ_L2.aestronglyMeasurable)).trans ?_
      simp only [hinner]
      rw [integral_finset_sum _ (fun i _ => (hψ_int i).const_mul (u i))]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [integral_const_mul, hPθ₀_zero i, mul_zero])
    (psiCov P ψ θ₀) (psiCov_posSemidef P ψ θ₀ hψ_L2)
    (fun u v => by
      refine (htrans (fun ω => (⟪u, psiVec ψ θ₀ ω⟫ : ℝ) * ⟪v, psiVec ψ θ₀ ω⟫)
        (((show Continuous (fun w : EuclideanSpace ℝ (Fin k) => ⟪u, w⟫) from
            continuous_const.inner continuous_id).comp_aestronglyMeasurable
              hψ_L2.aestronglyMeasurable).mul
         ((show Continuous (fun w : EuclideanSpace ℝ (Fin k) => ⟪v, w⟫) from
            continuous_const.inner continuous_id).comp_aestronglyMeasurable
              hψ_L2.aestronglyMeasurable))).trans ?_
      have hrhs : u.ofLp ⬝ᵥ (psiCov P ψ θ₀).mulVec v.ofLp
          = ∑ i, ∑ j, (u i * v j) * ∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P := by
        simp only [dotProduct, Matrix.mulVec, psiCov, Matrix.of_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        change u i * ((∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P) * v j)
            = (u i * v j) * ∫ ω, ψ θ₀ i ω * ψ θ₀ j ω ∂P
        ring
      rw [hrhs]
      have hintegrand : (fun ω => (⟪u, psiVec ψ θ₀ ω⟫ : ℝ) * ⟪v, psiVec ψ θ₀ ω⟫)
          = fun ω => ∑ i, ∑ j, (u i * v j) * (ψ θ₀ i ω * ψ θ₀ j ω) := by
        funext ω
        rw [hinner u ω, hinner v ω, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl
          (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      rw [hintegrand,
        integral_finset_sum _ (fun i _ => integrable_finset_sum _
          (fun j _ => (hψ_mul_int i j).const_mul _))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finset_sum _ (fun j _ => (hψ_mul_int i j).const_mul _)]
      exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _))
    hY0_L2
  -- Identify the CLT statistic with `empiricalProcessVec` (uses `Pψ_{θ₀} = 0`).
  have hsqrt_inv : ∀ n : ℕ, Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp
    · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
      have hsqrt_ne : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast h0)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
      refine mul_right_cancel₀ hsqrt_ne ?_
      rw [inv_mul_cancel₀ hsqrt_ne, mul_right_comm, hsq, mul_inv_cancel₀ hn]
  have hidentity : ∀ (n : ℕ) (ξ : Ξ),
      empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)
        = (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, psiVec ψ θ₀ (X i ξ) := by
    intro n ξ
    apply (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).injective
    rw [map_smul, map_sum]
    funext h
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    change empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)
        = (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ψ θ₀ h (X i ξ)
    simp only [empiricalProcess, empiricalAvg]
    rw [hPθ₀_zero h, sub_zero, Fin.sum_univ_eq_sum_range (fun m => ψ θ₀ h (X m ξ)) n,
      ← mul_assoc, hsqrt_inv n]
  -- Rewrite the pushforward family and conclude.
  have hmapeq : (fun n : ℕ => μ.map (fun ξ =>
        empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
      = (fun n : ℕ => μ.map (fun ξ =>
        (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, psiVec ψ θ₀ (X i ξ))) := by
    funext n; congr 1; funext ξ; exact hidentity n ξ
  rw [hmapeq]
  exact hCLT

/-! ### Asymptotic normality -/

/-- **Asymptotic normality of the finite-dimensional Z-estimator.**
This core accepts a `Theorem19_26Hyp` bundle; `zEstimator_asymptotic_normality`
carries vdV Theorem 5.21's stated hypotheses and constructs the
`Theorem19_26Hyp` bundle `hyp` internally). vdV Thm 5.21, §5.3 book p.52-53.

For an iid sample `X₁,…,Xₙ ~ P` and a Z-estimator `θ̂ₙ` solving the `k` estimating
equations up to `o_P(n^{-1/2})` (`h_est_eq`) with `θ̂ₙ →ₚ θ₀` (`h_consist`), under
Fréchet differentiability of `θ ↦ Pψ_θ` at the zero `θ₀` with nonsingular derivative
matrix `V` (`hV`, plus `hyp.frechet` / `hyp.hPθ₀_zero`) and `P‖ψ_{θ₀}‖² < ∞`
(`hψ_L2`):

    √n(θ̂ₙ − θ₀) ⇝ N(0, V⁻¹ P[ψ_{θ₀}ψ_{θ₀}ᵀ] (V⁻¹)ᵀ).

The covariance `psiCov = P[ψ_{θ₀}ψ_{θ₀}ᵀ]` is constructed explicitly, with
its positive-semidefinite and variance properties proved by
`psiCov_posSemidef` and `psiCov_variance_eq`.

The linear representation gives `√n(θ̂ − θ₀) = −V⁻¹ 𝔾ₙψ_{θ₀} + o_P(1)`, while
the empirical-process CLT gives
`𝔾ₙψ_{θ₀} ⇝ N(0, psiCov)`; CMT (`WeakConverges.map` by `−V⁻¹` via
`multivariateGaussian_map_toEuclideanCLM`, using `(−A) Σ (−A)ᵀ = A Σ Aᵀ`) plus
`vec_slutsky_recentering` (deterministic `o_P` shift) transport the limit to
`√n(θ̂ − θ₀)`. -/
theorem zEstimator_asymptotic_normality_core
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Set (Ω → ℝ)) (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (V : Matrix (Fin k) (Fin k) ℝ)
    (hV : IsUnit V.det) (δcls : ℝ)
    (hyp : Theorem19_26Hyp P 𝓕 ψ θ₀ (Vlin V) δcls)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖))
    (hθhat_meas' : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    (hψθ₀_meas : ∀ h, Measurable (ψ θ₀ h))
    (hψ_joint : ∀ (n : ℕ) (h : Fin k), Measurable
      (fun p : Ξ × Ω => ψ (θ_hat n (fun i : Fin n => X i.val p.1)) h p.2))
    (h_tight : IsBoundedInOuterProbSup μ (fun n ξ h =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)))
    (h_consist : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0))
    (h_est_eq : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
        n (fun i : Fin n => X i.val ξ))) :
    WeakConverges
      (fun n => μ.map (fun ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
      (multivariateGaussian 0 (V⁻¹ * psiCov P ψ θ₀ * (V⁻¹)ᵀ)) := by
  classical
  -- The hypotheses give `Pψ_{θ₀} = 0`.
  have hPθ₀_zero := hyp.hPθ₀_zero
  -- Linear representation: `√n(θ̂ − θ₀) + V⁻¹ 𝔾ₙψ_{θ₀} →ₚ 0`.
  have hA := zEstimator_linear_representation P 𝓕 ψ θ₀ V hV δcls hyp θ_hat μ X
    hX_meas hX_indep hX_id hX_law hθhat_meas hθhat_meas' hψθ₀_meas hψ_joint
    h_tight h_consist h_est_eq
  -- Empirical-process limit: `𝔾ₙψ_{θ₀} ⇝ N(0, psiCov)`.
  have hC := empiricalProcessVec_weakConverges P ψ θ₀ μ X hX_meas hX_indep hX_id hX_law
    hψθ₀_meas hψ_L2 hPθ₀_zero
  -- Measurability of the bundled empirical process (as a function of `ξ`).
  have heproc_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hpi : Measurable (fun ξ : Ξ =>
        (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h) : Fin k → ℝ)) := by
      refine measurable_pi_iff.mpr (fun h => ?_)
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hψθ₀_meas h).comp (hX_meas i.val))
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp hpi
  -- The (negated) inverse derivative as a continuous linear endomorphism.
  set g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (-V⁻¹) with hg_def
  -- Gaussian pushforward: `N(0, psiCov).map g = N(0, V⁻¹ psiCov V⁻ᵀ)` (signs cancel).
  have hgauss_map :
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (psiCov P ψ θ₀)).map g
        = multivariateGaussian 0 (V⁻¹ * psiCov P ψ θ₀ * (V⁻¹)ᵀ) := by
    have hmean : (Matrix.toEuclideanCLM (𝕜 := ℝ) (-V⁻¹)) (0 : EuclideanSpace ℝ (Fin k)) = 0 :=
      map_zero _
    have hcov : (-V⁻¹) * psiCov P ψ θ₀ * (-V⁻¹)ᴴ
        = V⁻¹ * psiCov P ψ θ₀ * (V⁻¹)ᵀ := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_neg,
        neg_mul, neg_mul_neg]
    rw [hg_def, multivariateGaussian_map_toEuclideanCLM (-V⁻¹) (0 : EuclideanSpace ℝ (Fin k))
      (psiCov_posSemidef P ψ θ₀ hψ_L2), hmean, hcov]
  -- Push the empirical-process limit through `g`, then collapse the double pushforward.
  have hCmap := hC.map g.continuous g.continuous.measurable
  rw [hgauss_map] at hCmap
  have hX_weak : WeakConverges
      (fun n => μ.map (fun ξ =>
        g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))))
      (multivariateGaussian 0 (V⁻¹ * psiCov P ψ θ₀ * (V⁻¹)ᵀ)) := by
    have hfam : (fun n => μ.map (fun ξ =>
          g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))))
        = (fun n => (μ.map (fun ξ =>
          empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))).map g) := by
      funext n
      rw [Measure.map_map g.continuous.measurable (heproc_meas n)]
      rfl
    rw [hfam]; exact hCmap
  -- Rewrite the linear representation as
  -- `dist (g 𝔾ₙψ_{θ₀}) (√n(θ̂ − θ₀)) →ₚ 0` (since `g = −V⁻¹`).
  have hpt : ∀ (n : ℕ) (ω : Ξ),
      dist (g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ω)))
          (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ω) - θ₀))
        = ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ω) - θ₀)
            + Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
                (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ω))‖ := by
    intro n ω
    set e := empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ω) with he
    set b := Real.sqrt (n : ℝ) • (θ_hat n (fun i : Fin n => X i.val ω) - θ₀) with hb
    have hgapply : g e = -(Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹ e) := by
      rw [hg_def, map_neg, ContinuousLinearMap.neg_apply]
    rw [dist_eq_norm, hgapply,
      show -(Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹ e) - b
          = -(b + Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹ e) from by abel,
      norm_neg]
  have hDist : ∀ ε > 0, Tendsto (fun n => μ.real {ω |
      ε ≤ dist (g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ω)))
        (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ω) - θ₀))}) atTop (𝓝 0) := by
    intro ε hε
    have hfam : (fun n => μ.real {ω |
        ε ≤ dist (g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ω)))
          (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ω) - θ₀))})
        = (fun n : ℕ => μ.real {ω |
          ε ≤ ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ω) - θ₀)
            + Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
                (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ω))‖}) := by
      funext n
      have hset : {ω |
          ε ≤ dist (g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ω)))
            (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ω) - θ₀))}
          = {ω | ε ≤ ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ω) - θ₀)
              + Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
                  (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ω))‖} := by
        ext ω
        simp only [Set.mem_setOf_eq, hpt n ω]
      rw [hset]
    rw [hfam]
    exact hA ε hε
  -- Slutsky: the target statistic shares the Gaussian limit of `g 𝔾ₙψ_{θ₀}`.
  have hXslut_meas : ∀ n, Measurable (fun ξ : Ξ =>
      g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))) :=
    fun n => g.continuous.measurable.comp (heproc_meas n)
  have hYtarget_meas : ∀ n : ℕ, Measurable (fun ξ : Ξ =>
      Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :=
    fun n => ((hθhat_meas' n).sub measurable_const).const_smul (Real.sqrt n)
  exact AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
    (Ω := fun _ => Ξ) (P := fun _ => μ)
    (X := fun n ξ => g (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
    (Y := fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    (fun n => (hXslut_meas n).aemeasurable) (fun n => (hYtarget_meas n).aemeasurable)
    hX_weak hDist

/-- **Asymptotic normality of the finite-dimensional
Z-estimator** (vdV Thm 5.21, §5.3 book p.52-53).

Carries exactly van der Vaart's stated hypotheses: an `L²(P)` Lipschitz modulus
`m` for the estimating functions on the ball `‖θ − θ₀‖ < δcls` (`hLip`, `hm`),
measurability (`hψ_meas`), `θ₀` a zero of `θ ↦ Pψ_θ` (`hPθ₀_zero`),
Fréchet-differentiability of `θ ↦ Pψ_θ` at `θ₀` with nonsingular derivative `V`
(`hfrechet`, `hV`), `P‖ψ_{θ₀}‖² < ∞` (`hψ_L2`), the `o_P(n^{-1/2})` estimating
equation (`h_est_eq`) and consistency `θ̂ₙ →ₚ θ₀` (`h_consist`):

    √n(θ̂ₙ − θ₀) ⇝ N(0, V⁻¹ P[ψ_{θ₀}ψ_{θ₀}ᵀ] (V⁻¹)ᵀ).

The `P`-Donsker equicontinuity hypothesis of the core is derived here
from the Lipschitz data via `parametricClass_isPDonsker` (vdV Ex 19.7); the
`henv`/`unif_L2_cont`/`bddbelow_V` fields of `Theorem19_26Hyp` are derived from
the Lipschitz/envelope/nonsingularity data; and marginal tightness (`h_tight`)
is derived from the vector CLT via
`isBoundedInProb_of_weakConverges`. The class
`𝓕 = paramClass ψ (ball θ₀ δcls)` and the corresponding
`Theorem19_26Hyp` assumptions are constructed internally and supplied to
`zEstimator_asymptotic_normality_core`. -/
theorem zEstimator_asymptotic_normality
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (V : Matrix (Fin k) (Fin k) ℝ)
    (hV : IsUnit V.det) (δcls : ℝ) (hδcls : 0 < δcls)
    (m : Ω → ℝ) (hm : MemLp m 2 P) (hm_meas : Measurable m)
    (hLip : ∀ θ₁ : EuclideanSpace ℝ (Fin k), ‖θ₁ - θ₀‖ < δcls →
      ∀ θ₂ : EuclideanSpace ℝ (Fin k), ‖θ₂ - θ₀‖ < δcls →
      ∀ (j : Fin k) (x : Ω), |ψ θ₁ j x - ψ θ₂ j x| ≤ m x * ‖θ₁ - θ₂‖)
    (hψ_meas : ∀ (θ : EuclideanSpace ℝ (Fin k)) (j : Fin k), Measurable (ψ θ j))
    (hPθ₀_zero : ∀ h, ∫ x, ψ θ₀ h x ∂P = 0)
    (hfrechet : ∀ ε > 0, ∃ δ > 0, ∀ θ : EuclideanSpace ℝ (Fin k),
        0 < ‖θ - θ₀‖ → ‖θ - θ₀‖ < δ →
        (⨆ h, ENNReal.ofReal
            |∫ x, ψ θ h x ∂P - ∫ x, ψ θ₀ h x ∂P - Vlin V (θ - θ₀) h|)
          ≤ ENNReal.ofReal (ε * ‖θ - θ₀‖))
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hθhat_meas' : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    (hψ_joint : ∀ (n : ℕ) (h : Fin k), Measurable
      (fun p : Ξ × Ω => ψ (θ_hat n (fun i : Fin n => X i.val p.1)) h p.2))
    (h_consist : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0))
    (h_est_eq : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
        n (fun i : Fin n => X i.val ξ))) :
    WeakConverges
      (fun n => μ.map (fun ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
      (multivariateGaussian 0 (V⁻¹ * psiCov P ψ θ₀ * (V⁻¹)ᵀ)) := by
  classical
  -- Derived measurability / L² facts (`hθhat_meas`, `hψθ₀_meas`, `hψ0_L2` are strict
  -- specializations of `hθhat_meas'`, `hψ_meas`, and `hψ_L2`).
  have hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) :=
    fun n => ((hθhat_meas' n).sub_const θ₀).norm
  have hψθ₀_meas : ∀ h, Measurable (ψ θ₀ h) := fun h => hψ_meas θ₀ h
  have hψ0_L2 : ∀ j, MemLp (ψ θ₀ j) 2 P := fun j => hψ_L2.eval_piLp j
  -- Donsker class and Lipschitz data reshaped to ball membership.
  set 𝓕 : Set (Ω → ℝ) := paramClass ψ (Metric.ball θ₀ δcls) with h𝓕def
  have hθ₀_ball : θ₀ ∈ Metric.ball θ₀ δcls := Metric.mem_ball_self hδcls
  have hLip' : ∀ θ₁ ∈ Metric.ball θ₀ δcls, ∀ θ₂ ∈ Metric.ball θ₀ δcls,
      ∀ (j : Fin k) (x : Ω), |ψ θ₁ j x - ψ θ₂ j x| ≤ m x * ‖θ₁ - θ₂‖ := by
    intro θ₁ h₁ θ₂ h₂ j x
    exact hLip θ₁ (by rwa [Metric.mem_ball, dist_eq_norm] at h₁)
      θ₂ (by rwa [Metric.mem_ball, dist_eq_norm] at h₂) j x
  have hmeas𝓕 : ∀ g ∈ 𝓕, Measurable g := by
    rw [h𝓕def]; rintro g ⟨θ, _, j, rfl⟩; exact hψ_meas θ j
  set M : ℝ := (eLpNorm m 2 P).toReal with hMdef
  have hMnn : 0 ≤ M := ENNReal.toReal_nonneg
  -- Verify the hypotheses of Theorem 19.26 from those of vdV Theorem 5.21.
  have hyp : Theorem19_26Hyp P 𝓕 ψ θ₀ (Vlin V) δcls := by
    refine
      { hδcls := hδcls
        hclass_mem := ?_
        hψ_meas := hψ_meas
        henv := ?_
        h_equicont := ?_
        hPθ₀_zero := hPθ₀_zero
        bddbelow_V := matrix_bddbelow_of_isUnit_det V hV
        frechet := hfrechet
        unif_L2_cont := ?_ }
    · -- hclass_mem : `‖θ − θ₀‖ < δcls ⇒ ψ θ h ∈ 𝓕`.
      intro θ hθ h
      rw [h𝓕def]
      exact ⟨θ, by rw [Metric.mem_ball, dist_eq_norm]; exact hθ, h, rfl⟩
    · -- henv : integrable envelope `G = ∑ⱼ|ψθ₀ⱼ| + δcls·‖m‖`.
      refine ⟨fun x => (∑ j, |ψ θ₀ j x|) + δcls * ‖m x‖, ?_, ?_⟩
      · rw [h𝓕def]
        rintro f ⟨θ, hθ, j, rfl⟩ x
        have hθn : ‖θ - θ₀‖ < δcls := by rwa [Metric.mem_ball, dist_eq_norm] at hθ
        have h1 : |ψ θ j x| ≤ |ψ θ₀ j x| + m x * ‖θ - θ₀‖ := by
          have key : |ψ θ j x| ≤ |ψ θ₀ j x| + |ψ θ j x - ψ θ₀ j x| := by
            have h := abs_add_le (ψ θ₀ j x) (ψ θ j x - ψ θ₀ j x)
            rwa [show ψ θ₀ j x + (ψ θ j x - ψ θ₀ j x) = ψ θ j x from by ring] at h
          have hlip := hLip θ hθn θ₀ (by rw [sub_self, norm_zero]; exact hδcls) j x
          linarith [key, hlip]
        have h2 : m x * ‖θ - θ₀‖ ≤ δcls * ‖m x‖ := by
          calc m x * ‖θ - θ₀‖ ≤ ‖m x‖ * ‖θ - θ₀‖ :=
                mul_le_mul_of_nonneg_right (Real.le_norm_self (m x)) (norm_nonneg _)
            _ ≤ ‖m x‖ * δcls := mul_le_mul_of_nonneg_left hθn.le (norm_nonneg _)
            _ = δcls * ‖m x‖ := mul_comm _ _
        have h3 : |ψ θ₀ j x| ≤ ∑ j', |ψ θ₀ j' x| :=
          Finset.single_le_sum (f := fun j' => |ψ θ₀ j' x|) (fun i _ => abs_nonneg _)
            (Finset.mem_univ j)
        calc |ψ θ j x| ≤ |ψ θ₀ j x| + m x * ‖θ - θ₀‖ := h1
          _ ≤ (∑ j', |ψ θ₀ j' x|) + δcls * ‖m x‖ := by linarith [h2, h3]
      · exact (integrable_finset_sum _
          (fun j _ => ((hψ0_L2 j).integrable (by norm_num)).abs)).add
          ((hm.integrable (by norm_num)).norm.const_mul δcls)
    · -- h_equicont : vdV Ex 19.7 Lipschitz ⇒ Donsker.
      have hDonsker := parametricClass_isPDonsker P ψ (Metric.ball θ₀ δcls)
        Metric.isBounded_ball m hm hm_meas hLip' θ₀ hθ₀_ball hψ0_L2 hmeas𝓕
      rw [h𝓕def]
      intro Ξ' _ μ' _ X' hX'm hX'i hX'id hX'l ε η hε hη
      exact hDonsker.asymptoticallyEquicontinuous μ' X' hX'm hX'i hX'id hX'l ε η hε hη
    · -- unif_L2_cont : `distL2 P (ψθh)(ψθ₀h) ≤ ‖θ−θ₀‖·M`, pick `δ = min (ε/(M+1)) δcls`.
      intro ε hε
      refine ⟨min (ε / (M + 1)) δcls, lt_min (by positivity) hδcls, ?_⟩
      intro θ hθ
      have hθε : ‖θ - θ₀‖ < ε / (M + 1) := lt_of_lt_of_le hθ (min_le_left _ _)
      have hθδ : ‖θ - θ₀‖ < δcls := lt_of_lt_of_le hθ (min_le_right _ _)
      refine iSup_le (fun h => ?_)
      apply ENNReal.ofReal_le_ofReal
      have hstepA : eLpNorm ((ψ θ h) - (ψ θ₀ h)) 2 P
          ≤ ENNReal.ofReal ‖θ - θ₀‖ * eLpNorm m 2 P := by
        have hmono : eLpNorm ((ψ θ h) - (ψ θ₀ h)) 2 P
            ≤ eLpNorm (fun x => ‖θ - θ₀‖ * ‖m x‖) 2 P := by
          refine eLpNorm_mono_ae_real (Filter.Eventually.of_forall (fun x => ?_))
          rw [Pi.sub_apply, Real.norm_eq_abs]
          calc |ψ θ h x - ψ θ₀ h x|
              ≤ m x * ‖θ - θ₀‖ :=
                hLip θ hθδ θ₀ (by rw [sub_self, norm_zero]; exact hδcls) h x
            _ ≤ ‖m x‖ * ‖θ - θ₀‖ :=
                mul_le_mul_of_nonneg_right (Real.le_norm_self (m x)) (norm_nonneg _)
            _ = ‖θ - θ₀‖ * ‖m x‖ := mul_comm _ _
        have hsmul : eLpNorm (fun x => ‖θ - θ₀‖ * ‖m x‖) 2 P
            = ENNReal.ofReal ‖θ - θ₀‖ * eLpNorm m 2 P := by
          have hfe : (fun x => ‖θ - θ₀‖ * ‖m x‖) = ‖θ - θ₀‖ • (fun x => ‖m x‖) := by
            funext x; rw [Pi.smul_apply, smul_eq_mul]
          rw [hfe, eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal (norm_nonneg _)]
        rwa [hsmul] at hmono
      have hdistbd : distL2 P (ψ θ h) (ψ θ₀ h) ≤ ‖θ - θ₀‖ * M := by
        rw [distL2]
        calc (eLpNorm ((ψ θ h) - (ψ θ₀ h)) 2 P).toReal
            ≤ (ENNReal.ofReal ‖θ - θ₀‖ * eLpNorm m 2 P).toReal :=
              ENNReal.toReal_mono
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.2.ne) hstepA
          _ = ‖θ - θ₀‖ * M := by
              rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), hMdef]
      have h2 : ‖θ - θ₀‖ * M ≤ (ε / (M + 1)) * M :=
        mul_le_mul_of_nonneg_right hθε.le hMnn
      have h3 : (ε / (M + 1)) * M ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < M + 1)]
        nlinarith [hMnn, hε.le]
      linarith [hdistbd, h2, h3]
  -- The vector empirical process converges weakly, hence is marginally `O_P(1)`;
  -- this yields the marginal tightness `h_tight` required by the core.
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (psiCov P ψ θ₀)) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  have hC := empiricalProcessVec_weakConverges P ψ θ₀ μ X hX_meas hX_indep hX_id hX_law
    hψθ₀_meas hψ_L2 hPθ₀_zero
  have heproc_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hpi : Measurable (fun ξ : Ξ =>
        (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h) : Fin k → ℝ)) := by
      refine measurable_pi_iff.mpr (fun h => ?_)
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hψθ₀_meas h).comp (hX_meas i.val))
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp hpi
  have hbdd := isBoundedInProb_of_weakConverges (P := fun _ : ℕ => μ) heproc_meas hC
  have h_tight : IsBoundedInOuterProbSup μ (fun n ξ h =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)) := by
    intro η hη
    obtain ⟨MM, hMM⟩ := hbdd η hη
    refine ⟨MM, ?_⟩
    -- Each coordinate of a Euclidean vector is bounded by its norm.
    have hcoordbd : ∀ (v : EuclideanSpace ℝ (Fin k)) (h : Fin k), |v h| ≤ ‖v‖ := by
      intro v h
      have h1 : ‖v h‖ ≤ ‖v‖ := by
        rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (v h))]
        apply Real.sqrt_le_sqrt
        exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ h)
      rwa [Real.norm_eq_abs] at h1
    -- The `∃h` exceedance sits inside the Euclidean-norm exceedance.
    have hsub : ∀ n, {ξ | ∃ h, MM <
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)|}
        ⊆ {ξ | MM < ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖} := by
      intro n ξ hξ
      simp only [Set.mem_setOf_eq] at hξ ⊢
      obtain ⟨h, hh⟩ := hξ
      have hcoord : empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)
          = (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)) h := rfl
      rw [hcoord] at hh
      exact lt_of_lt_of_le hh (hcoordbd _ h)
    have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, MM <
        |empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)|}
        ≤ ENNReal.ofReal η := by
      intro n
      calc μ.outerMeasureStar {ξ | ∃ h, MM <
            |empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)|}
          ≤ μ.outerMeasureStar
              {ξ | MM < ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖} :=
            outerMeasureStar_mono μ (hsub n)
        _ ≤ μ {ξ | MM < ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖} :=
            outerMeasureStar_le_measure μ _
        _ ≤ ENNReal.ofReal η := by
            rw [← ENNReal.ofReal_toReal (measure_ne_top μ
              {ξ | MM < ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖})]
            exact ENNReal.ofReal_le_ofReal (hMM n)
    calc limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, MM <
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)|}) atTop
        ≤ limsup (fun _ : ℕ => ENNReal.ofReal η) atTop :=
          limsup_le_limsup (Eventually.of_forall hb) isCobounded_le_of_bot
            (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      _ = ENNReal.ofReal η := limsup_const _
  -- Apply the preceding normality theorem.
  exact zEstimator_asymptotic_normality_core P 𝓕 ψ θ₀ V hV δcls hyp hψ_L2 θ_hat μ X
    hX_meas hX_indep hX_id hX_law hθhat_meas hθhat_meas' hψθ₀_meas hψ_joint h_tight
    h_consist h_est_eq

end AsymptoticStatistics.EmpiricalProcess
