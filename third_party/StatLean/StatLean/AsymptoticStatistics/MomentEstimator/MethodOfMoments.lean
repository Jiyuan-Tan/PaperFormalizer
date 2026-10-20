module
public import StatLean.AsymptoticStatistics.ForMathlib.DeltaMethod
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.AsymptoticStatistics.ForMathlib.SlutskyVec
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

@[expose] public section

/-!
# Method of moments (van der Vaart, *Asymptotic Statistics*, Theorem 4.1)

Let `X₁, …, Xₙ` be an i.i.d. sample from `P = P_{θ₀}` and let `f : Ω → ℝᵈ` be a
vector of moment functions.  Write the moment map `e(ϑ) = P_ϑ f`, so that at the
true parameter `e θ₀ = P f =: μ`.  The **moment estimator** solves the system
`ℙₙ f = e(θhatₙ)`, i.e. `θhatₙ = e⁻¹(ℙₙ f)`.  Theorem 4.1 states that if `e` is
one-to-one, continuously differentiable at `θ₀` with nonsingular derivative `e_{θ₀}`,
and `P‖f‖² < ∞`, then the moment estimators exist with probability tending to one
and

    √n (θhatₙ − θ₀)  ⇝  N(0, e_{θ₀}⁻¹ P[(f−Pf)(f−Pf)ᵀ] e_{θ₀}⁻ᵀ).

## Proof route (vdV §4.1, book p.35–36)

Existence is the **inverse function theorem** (`HasStrictFDerivAt.localInverse`):
`e` maps an open neighbourhood `U ∋ θ₀` diffeomorphically onto an open `V ∋ μ`, so
`θhatₙ = φ(ℙₙ f)` with `φ` the local inverse (a *globally-defined* function, differentiable
at `μ` with derivative `e_{θ₀}⁻¹`, `φ μ = θ₀`).  It solves the moment equation as soon
as `ℙₙ f ∈ V`, which happens with probability → 1 by consistency `ℙₙ f →ₚ μ`.

Asymptotic normality is the **delta method** (`delta_method_remainder`) applied to `φ`:
the multivariate CLT gives `√n(ℙₙ f − μ) ⇝ N(0, Σ_f)` (`empiricalMoment_weakConverges`),
whence consistency and `O_P(1)` are derived; `delta_method_remainder` linearises
`√n(φ(ℙₙ f) − θ₀) = e_{θ₀}⁻¹ √n(ℙₙ f − μ) + o_P(1)`, and the linear part's limit is
`N(0, Σ_f).map e_{θ₀}⁻¹ = N(0, e_{θ₀}⁻¹ Σ_f e_{θ₀}⁻ᵀ)` (`momentGaussian_map_eq`).

## Sample-space convention (matches `EmpiricalProcess/ZEstimatorNormality.lean`)

The i.i.d. sample is `X : ℕ → Ξ → Ω` on a base `(Ξ, μ)` with `μ.map (X 0) = P`.  The
`delta_method_remainder` engine is used at the *constant* varying base `Ω k := Ξ`,
`P k := μ`.

-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace Matrix

namespace AsymptoticStatistics.MomentEstimator

/-! ### Definitions -/

/-- **Empirical moment `ℙₙ f`.** The sample mean `(1/n) Σ_{i<n} f(Xᵢ)` of the moment
functions, as a function of the base point `ξ`.  Written with `Finset.range n` to align
with `tendstoInDistribution_multivariate_clt`'s standardised sum. -/
noncomputable def empiricalMoment {d : ℕ} {Ω Ξ : Type*}
    (f : Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (X : ℕ → Ξ → Ω) (ξ : Ξ) :
    EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (X i ξ)

/-- **Limit covariance `Σ_f = P[(f − Pf)(f − Pf)ᵀ]`.** Entry `(i,j)` is the covariance of
the `i`-th and `j`-th coordinates of `f` under `P`.  Its PSD (`fCov_posSemidef`) and
directional-variance identity (`fCov_variance_eq`) feed the multivariate CLT. -/
noncomputable def fCov {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    ∫ x, (f x i - ∫ y, f y i ∂P) * (f x j - ∫ y, f y j ∂P) ∂P

/-- **Matrix of the inverse derivative `e_{θ₀}⁻¹`.** The nonsingular derivative `e'`
is a continuous linear equiv; `e_{θ₀}⁻¹ = e'.symm` is embedded back as a matrix via the
`Matrix ≃⋆ₐ CLM` star-algebra iso `Matrix.toEuclideanCLM`. -/
noncomputable def invDerivMatrix {d : ℕ}
    (e' : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm (e'.symm : _ →L[ℝ] _)

/-- **Limit covariance `e_{θ₀}⁻¹ Σ_f e_{θ₀}⁻ᵀ`.** -/
noncomputable def momentLimitCov {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → EuclideanSpace ℝ (Fin d))
    (e' : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  invDerivMatrix e' * fCov P f * (invDerivMatrix e')ᵀ

/-! ### Measurable extension of the local inverse -/

/-- **Measurable modification of a continuous-on-open map.** The IFT local inverse
`φ` is continuous only on the open target `U`; composed with a measurable statistic `Z`
it need not be globally measurable. This produces a globally measurable `g`
agreeing with `φ ∘ Z` wherever `Z ∈ U` (elsewhere the constant `c`), so pushforwards
`μ.map (√n • (g − θ₀))` are well-defined while `g = φ ∘ Z` on the good event.

The construction is `g := (Z ⁻¹' U).piecewise (φ ∘ Z) (fun _ => c)`;
measurability from `ContinuousOn φ U` + `IsOpen U` + `Measurable Z`. -/
theorem exists_measurable_eq_on_open
    {E Ξ : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ξ]
    (φ : E → E) (U : Set E) (hU : IsOpen U) (hφ : ContinuousOn φ U) (c : E)
    {Z : Ξ → E} (hZ : Measurable Z) :
    ∃ g : Ξ → E, Measurable g ∧ ∀ ξ, Z ξ ∈ U → g ξ = φ (Z ξ) := by
  classical
  -- `φ` extended by the constant `c` off `U` is globally measurable
  -- (`ContinuousOn.measurable_piecewise`); precompose with the measurable `Z`.
  have hφ_ext : Measurable (U.piecewise φ (fun _ => c)) :=
    hφ.measurable_piecewise continuousOn_const hU.measurableSet
  refine ⟨fun ξ => U.piecewise φ (fun _ => c) (Z ξ), hφ_ext.comp hZ, ?_⟩
  intro ξ hξ
  simp only [Set.piecewise_eq_of_mem _ _ _ hξ]

/-! ### Covariance identities -/

/-- **Shared quadratic-form core.** The quadratic form of `fCov P f` in direction `x`
equals the mean square of the linear combination `∑ᵢ xᵢ (fᵢ − Pfᵢ)` of the centred
coordinates.  Feeds both `fCov_posSemidef` (nonnegativity of a mean square) and
`fCov_variance_eq` (the directional variance identity). -/
private lemma fCov_quad_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → EuclideanSpace ℝ (Fin d)} (hf_L2 : MemLp f 2 P)
    (x : Fin d → ℝ) :
    x ⬝ᵥ (fCov P f) *ᵥ x
      = ∫ ω, (∑ i, x i * (f ω i - ∫ y, f y i ∂P)) ^ 2 ∂P := by
  classical
  -- each coordinate of `f` is `L²` (continuous-linear projection of an `L²` function)
  have hf_coord : ∀ i, MemLp (fun ω => f ω i) 2 P := by
    intro i
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf_L2
    simpa [Function.comp, EuclideanSpace.coe_proj] using! h
  -- centred coordinates are `L²`
  have hg : ∀ i, MemLp (fun ω => f ω i - ∫ y, f y i ∂P) 2 P := fun i =>
    (hf_coord i).sub (memLp_const _)
  -- products of centred coordinates are integrable (Hölder `L²·L² → L¹`)
  have hprod_int : ∀ i j, Integrable
      (fun ω => (f ω i - ∫ y, f y i ∂P) * (f ω j - ∫ y, f y j ∂P)) P := fun i j =>
    (hg i).integrable_mul (hg j)
  -- entry of `fCov` is the integral of the product (definitional)
  have hentry : ∀ i j, fCov P f i j
      = ∫ ω, (f ω i - ∫ y, f y i ∂P) * (f ω j - ∫ y, f y j ∂P) ∂P := fun _ _ => rfl
  -- LHS: expand the quadratic form
  have hLHS : x ⬝ᵥ (fCov P f) *ᵥ x
      = ∑ i, ∑ j, x i * x j
          * ∫ ω, (f ω i - ∫ y, f y i ∂P) * (f ω j - ∫ y, f y j ∂P) ∂P := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hentry i j]; ring
  -- integrability bookkeeping for the `∫`/`∑` swaps
  have hInt2 : ∀ i j, Integrable
      (fun ω => x i * x j
          * ((f ω i - ∫ y, f y i ∂P) * (f ω j - ∫ y, f y j ∂P))) P := fun i j =>
    (hprod_int i j).const_mul (x i * x j)
  have hInt1 : ∀ i, Integrable
      (fun ω => ∑ j, x i * x j
          * ((f ω i - ∫ y, f y i ∂P) * (f ω j - ∫ y, f y j ∂P))) P := fun i =>
    integrable_finset_sum _ fun j _ => hInt2 i j
  -- RHS: expand the square, swap `∫`/`∑`
  have hRHS : ∫ ω, (∑ i, x i * (f ω i - ∫ y, f y i ∂P)) ^ 2 ∂P
      = ∑ i, ∑ j, x i * x j
          * ∫ ω, (f ω i - ∫ y, f y i ∂P) * (f ω j - ∫ y, f y j ∂P) ∂P := by
    have hpt : ∀ ω, (∑ i, x i * (f ω i - ∫ y, f y i ∂P)) ^ 2
        = ∑ i, ∑ j, x i * x j
            * ((f ω i - ∫ y, f y i ∂P) * (f ω j - ∫ y, f y j ∂P)) := by
      intro ω
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    rw [integral_finset_sum _ fun i _ => hInt1 i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hInt2 i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  rw [hLHS, hRHS]

/-- **The covariance matrix `Σ_f = P[(f−Pf)(f−Pf)ᵀ]` is positive semidefinite.** It is a
Gram-type matrix of the centred `L²` coordinates (`Matrix.posSemidef_gram`-flavoured). -/
theorem fCov_posSemidef {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → EuclideanSpace ℝ (Fin d)}
    (hf_L2 : MemLp f 2 P) :
    (fCov P f).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · -- Hermitian: `fCov` is symmetric (real, so `conjTranspose = transpose`)
    ext i j
    rw [Matrix.conjTranspose_apply, star_trivial]
    simp only [fCov, Matrix.of_apply]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  · -- nonnegativity: the quadratic form is a mean square
    have hstar : star x = x := by funext i; rw [Pi.star_apply, star_trivial]
    rw [hstar, fCov_quad_eq P hf_L2 x]
    exact integral_nonneg fun ω => sq_nonneg _

/-- **Directional-variance identity.** `Var[⟪t, f⟫; P] = t ⬝ᵥ Σ_f *ᵥ t` for every
direction `t`: the variance of the linear combination `⟪t, f⟫ = Σⱼ tⱼ fⱼ` is the
quadratic form of the covariance matrix `Σ_f`.  Feeds the CLT `hS_eq`. -/
theorem fCov_variance_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → EuclideanSpace ℝ (Fin d)}
    (hf_L2 : MemLp f 2 P) :
    ∀ t : EuclideanSpace ℝ (Fin d),
      Var[fun ω => ⟪t, f ω⟫; P] = t ⬝ᵥ (fCov P f) *ᵥ t := by
  classical
  intro t
  -- coordinates of `f` are `L²`, hence `L¹`
  have hf_coord : ∀ i, MemLp (fun ω => f ω i) 2 P := by
    intro i
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf_L2
    simpa [Function.comp, EuclideanSpace.coe_proj] using! h
  -- the linear functional `⟪t, f ·⟫` is AE(strongly)measurable
  have h_asm : AEStronglyMeasurable (fun ω => ⟪t, f ω⟫) P :=
    (continuous_const.inner continuous_id).comp_aestronglyMeasurable hf_L2.aestronglyMeasurable
  have h_AEM : AEMeasurable (fun ω => ⟪t, f ω⟫) P := h_asm.aemeasurable
  -- inner product as the coordinate combination `∑ᵢ tᵢ fᵢ`
  have h_inner : ∀ ω, ⟪t, f ω⟫ = ∑ i, t i * f ω i := by
    intro ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- real inner of scalars is multiplication (order flipped, `⟪a,b⟫ = b*a` by defeq)
    exact mul_comm _ _
  -- integral of the inner product
  have h_int_inner : ∫ y, ⟪t, f y⟫ ∂P = ∑ i, t i * ∫ y, f y i ∂P := by
    simp_rw [h_inner]
    rw [integral_finset_sum _ fun i _ =>
      ((hf_coord i).integrable (by norm_num)).const_mul (t i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [variance_eq_integral h_AEM, fCov_quad_eq P hf_L2 t]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  dsimp only
  congr 1
  rw [h_inner ω, h_int_inner, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Weak limit of the empirical moment -/

/-- **`√n(ℙₙ f − Pf) ⇝ N(0, Σ_f)`** (multivariate CLT, general nonzero mean).

For the i.i.d. sample `X : ℕ → Ξ → Ω` with `μ.map (X 0) = P` and `P‖f‖² < ∞`, the
rescaled centred empirical moment converges weakly to `N(0, Σ_f)`.

The proof applies
`tendstoInDistribution_multivariate_clt` to the i.i.d. sequence `Yₖ := f ∘ Xₖ` on
`(Ξ, μ)` with `hS_pos := fCov_posSemidef`, `hS_eq := fCov_variance_eq` (transported along
`μ.map (X 0) = P`), match `(√n)⁻¹•(Σ − n•μ) = √n•(ℙₙf − μ)`, reindex `range n ↔ Fin n`,
and bridge `TendstoInDistribution → WeakConverges`.  (The `Pf = 0` special case is
`EmpiricalProcess.empiricalProcessVec_weakConverges`.) -/
theorem empiricalMoment_weakConverges {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → EuclideanSpace ℝ (Fin d)} (hf_meas : Measurable f) (hf_L2 : MemLp f 2 P)
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConverges
      (fun n => μ.map (fun ξ =>
        Real.sqrt n • (empiricalMoment f n X ξ - ∫ x, f x ∂P)))
      (multivariateGaussian 0 (fCov P f)) := by
  classical
  -- √n scalar identities used to reshape the standardised statistic
  have hc_v : ∀ n : ℕ, (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hs : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
      have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hpos.le
      calc (Real.sqrt n)⁻¹ * (n : ℝ)
          = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n) := by rw [h2]
        _ = Real.sqrt n := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have hc_S : ∀ n : ℕ, Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hs : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
      have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hpos.le
      calc Real.sqrt n * (n : ℝ)⁻¹
          = Real.sqrt n * (Real.sqrt n * Real.sqrt n)⁻¹ := by rw [h2]
        _ = (Real.sqrt n)⁻¹ := by
            rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  -- the iid sequence `Y k := f ∘ X k` on the base `(Ξ, μ)`
  set Y : ℕ → Ξ → EuclideanSpace ℝ (Fin d) := fun k ξ => f (X k ξ) with hY_def
  have hY_iid : iIndepFun Y μ := hX_indep.comp (fun _ => f) (fun _ => hf_meas)
  have hY_id : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i => (hX_id i).comp hf_meas
  have hf_map : MemLp f 2 (μ.map (X 0)) := by rw [hX_law]; exact hf_L2
  have hY_L2 : MemLp (Y 0) 2 μ := hf_map.comp_of_map (hX_meas 0).aemeasurable
  -- mean of `Y 0` equals `Pf`
  have hasm_map : AEStronglyMeasurable f (μ.map (X 0)) := by
    rw [hX_law]; exact hf_L2.aestronglyMeasurable
  have hEY0 : ∫ ξ, f (X 0 ξ) ∂μ = ∫ x, f x ∂P := by
    rw [← hX_law]
    exact (integral_map (hX_meas 0).aemeasurable hasm_map).symm
  -- directional variance identity, transported along `μ.map (X 0) = P`
  have hvar_Y : ∀ t : EuclideanSpace ℝ (Fin d),
      Var[fun ξ => ⟪t, Y 0 ξ⟫; μ] = t ⬝ᵥ (fCov P f) *ᵥ t := by
    intro t
    have hXam : AEMeasurable (fun ω => ⟪t, f ω⟫) (μ.map (X 0)) := by
      rw [hX_law]
      exact ((continuous_const.inner continuous_id).comp_aestronglyMeasurable
        hf_L2.aestronglyMeasurable).aemeasurable
    have hvm := variance_map hXam (hX_meas 0).aemeasurable
    rw [hX_law] at hvm
    rw [show (fun ξ => ⟪t, Y 0 ξ⟫) = (fun ω => ⟪t, f ω⟫) ∘ (X 0) from rfl, ← hvm]
    exact fCov_variance_eq P hf_L2 t
  have hS_pos : (fCov P f).PosSemidef := fCov_posSemidef P hf_L2
  haveI : IsProbabilityMeasure (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (fCov P f)) := inferInstance
  have hY_law : HasLaw (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (multivariateGaussian 0 (fCov P f)) (multivariateGaussian 0 (fCov P f)) := HasLaw.id
  -- the multivariate CLT for the standardised empirical moment
  have h_TID :
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ξ =>
          (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, Y k ξ - n • μ[Y 0]))
        atTop (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (fun _ => μ)
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (fCov P f)) :=
    tendstoInDistribution_multivariate_clt
      (P := μ) (P' := multivariateGaussian 0 (fCov P f))
      (X := Y) (Y := id) (S := fCov P f) hS_pos hvar_Y hY_law hY_L2 hY_iid hY_id
  -- the standardised statistic equals the target `√n(ℙₙf − Pf)`
  have hfun_eq : ∀ n : ℕ,
      (fun ξ => (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, Y k ξ - n • μ[Y 0]))
        = (fun ξ => Real.sqrt n • (empiricalMoment f n X ξ - ∫ x, f x ∂P)) := by
    intro n
    funext ξ
    simp only [hY_def, empiricalMoment]
    rw [hEY0, ← Nat.cast_smul_eq_nsmul (R := ℝ) n (∫ x, f x ∂P),
      smul_sub, smul_sub, smul_smul, smul_smul, hc_v n, hc_S n]
  -- bridge `TendstoInDistribution → WeakConverges`
  intro g
  have h_PM := h_TID.tendsto
  have h_it := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_PM) g
  have h_map_id : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (fCov P f)).map
      (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      = multivariateGaussian 0 (fCov P f) := Measure.map_id
  simp only [h_map_id] at h_it
  have h_map_eq : ∀ n : ℕ,
      μ.map (fun ξ => (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, Y k ξ - n • μ[Y 0]))
        = μ.map (fun ξ => Real.sqrt n • (empiricalMoment f n X ξ - ∫ x, f x ∂P)) :=
    fun n => congrArg (fun h => μ.map h) (hfun_eq n)
  have h_pw : ∀ n : ℕ,
      ∫ x, g x ∂(μ.map (fun ξ =>
          (Real.sqrt n)⁻¹ • (∑ k ∈ Finset.range n, Y k ξ - n • μ[Y 0])))
        = ∫ x, g x ∂(μ.map (fun ξ =>
          Real.sqrt n • (empiricalMoment f n X ξ - ∫ x, f x ∂P))) :=
    fun n => by rw [h_map_eq n]
  simpa [h_pw] using h_it

/-! ### Push the Gaussian law through the inverse derivative -/

/-- **`N(0, Σ_f).map e_{θ₀}⁻¹ = N(0, e_{θ₀}⁻¹ Σ_f e_{θ₀}⁻ᵀ)`.** The delta-method
limit law, computed via `multivariateGaussian_map_toEuclideanCLM` with
`A := invDerivMatrix e'` (using `toEuclideanCLM A = ↑e'.symm`, `A 0 = 0`, `Aᴴ = Aᵀ`). -/
theorem momentGaussian_map_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → EuclideanSpace ℝ (Fin d)} (hf_L2 : MemLp f 2 P)
    (e' : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    (multivariateGaussian 0 (fCov P f)).map (e'.symm : _ →L[ℝ] _)
      = multivariateGaussian 0 (momentLimitCov P f e') := by
  -- `e'.symm` is the CLM of the matrix `A := invDerivMatrix e'`.
  have hAeq : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (invDerivMatrix e')
      = (e'.symm : _ →L[ℝ] _) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).apply_symm_apply _
  rw [← hAeq,
    multivariateGaussian_map_toEuclideanCLM (invDerivMatrix e') 0 (fCov_posSemidef P hf_L2)]
  have hmean : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (invDerivMatrix e')
      (0 : EuclideanSpace ℝ (Fin d)) = 0 := map_zero _
  -- `A * Σ_f * Aᴴ = A * Σ_f * Aᵀ = momentLimitCov` (star trivial over ℝ)
  have hcov : invDerivMatrix e' * fCov P f * (invDerivMatrix e')ᴴ
      = momentLimitCov P f e' := by
    rw [momentLimitCov, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hmean, hcov]

/-! ### Asymptotic normality of the moment estimator -/

/-- **Method of moments — van der Vaart, Theorem 4.1** (§4.1, book p.35–36).

For an i.i.d. sample `X₁,…,Xₙ ~ P` and moment functions `f : Ω → ℝᵈ` with `P‖f‖² < ∞`
(`hf_L2`), a moment map `e` that is (strictly) differentiable at the true parameter `θ₀`
with nonsingular derivative `e'` (`he`) and satisfies the moment-matching identity
`e θ₀ = P f` (`hμ`): the moment estimators `θhatₙ` (solving `e(θhatₙ) = ℙₙ f`) exist with
probability tending to one and satisfy vdV's displayed expansion

    √n (θhatₙ − θ₀) = e_{θ₀}⁻¹ √n (ℙₙ f − P f) + o_P(1)   ⇝   N(0, e_{θ₀}⁻¹ P[(f−Pf)(f−Pf)ᵀ] e_{θ₀}⁻ᵀ).

The three conclusion conjuncts are: existence w.p.→1 (`μ.real{e(θhatₙ)=ℙₙf} → 1`), the linear
representation (`√n(θhatₙ−θ₀) − e_{θ₀}⁻¹ √n(ℙₙf−Pf) →ₚ 0`, the `o_P(1)` term), and the
resulting asymptotic normality (`WeakConverges`).

Consistency `ℙₙ f →ₚ P f` and tightness `O_P(1)` are **derived** from the CLT
(`empiricalMoment_weakConverges`), not assumed (hypothesis discipline).  Existence and the
estimator itself are part of the *conclusion*: `θhatₙ` is exhibited as a measurable function
equal to `e⁻¹(ℙₙ f)` on the (probability → 1) event where the local inverse solves the
equation.

Assembly: IFT local inverse `φ` for existence + `delta_method_remainder` for the
linearisation + `momentGaussian_map_eq` for the limit law + `WeakConverges` Slutsky bridge
absorbing the vanishing-mass discrepancy between `θhatₙ` and `φ(ℙₙ f)`. -/
theorem method_of_moments_normality {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → EuclideanSpace ℝ (Fin d)} (hf_meas : Measurable f) (hf_L2 : MemLp f 2 P)
    {e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {e' : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)}
    {θ₀ : EuclideanSpace ℝ (Fin d)}
    (he : HasStrictFDerivAt e (e' : _ →L[ℝ] _) θ₀)
    (hμ : e θ₀ = ∫ x, f x ∂P)
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ θhat : ℕ → Ξ → EuclideanSpace ℝ (Fin d),
      (∀ n, Measurable (θhat n)) ∧
      Tendsto (fun n => μ.real {ξ | e (θhat n ξ) = empiricalMoment f n X ξ}) atTop (𝓝 1) ∧
      TendstoInProbZero (fun _ : ℕ => μ)
        (fun n ξ => Real.sqrt n • (θhat n ξ - θ₀)
          - (↑e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
              (Real.sqrt n • (empiricalMoment f n X ξ - ∫ x, f x ∂P))) ∧
      WeakConverges (fun n => μ.map (fun ξ => Real.sqrt n • (θhat n ξ - θ₀)))
        (multivariateGaussian 0 (momentLimitCov P f e')) := by
  classical
  set μ_vec : EuclideanSpace ℝ (Fin d) := ∫ x, f x ∂P with hμvec
  -- ── IFT: local inverse `φ`, open target `U`, packaged ──────────────────
  obtain ⟨φ, U, hU_open, hφ_cont, hrinv, hφμ, hμmem, hφ_deriv⟩ :
      ∃ (φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (U : Set (EuclideanSpace ℝ (Fin d))),
        IsOpen U ∧ ContinuousOn φ U ∧ (∀ y ∈ U, e (φ y) = y) ∧
          φ μ_vec = θ₀ ∧ μ_vec ∈ U ∧
          HasFDerivAt φ (↑e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
            μ_vec := by
    refine ⟨⇑(he.toOpenPartialHomeomorph e).symm, (he.toOpenPartialHomeomorph e).target,
      (he.toOpenPartialHomeomorph e).open_target,
      (he.toOpenPartialHomeomorph e).continuousOn_invFun, ?_, ?_, ?_, ?_⟩
    · intro y hy
      have hy2 := (he.toOpenPartialHomeomorph e).right_inv hy
      rwa [he.toOpenPartialHomeomorph_coe] at hy2
    · have hl := (he.toOpenPartialHomeomorph e).left_inv he.mem_toOpenPartialHomeomorph_source
      rwa [he.toOpenPartialHomeomorph_coe, hμ] at hl
    · rw [← hμ]; exact he.image_mem_toOpenPartialHomeomorph_target
    · have h1 := he.to_localInverse.hasFDerivAt
      rw [he.localInverse_def, hμ] at h1
      exact h1
  -- Measurability, the multivariate CLT, boundedness, and consistency.
  have hemp_meas : ∀ n, Measurable (empiricalMoment f n X) := by
    intro n
    show Measurable fun ξ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (X i ξ)
    exact (Finset.measurable_sum _ fun i _ => hf_meas.comp (hX_meas i)).const_smul ((n : ℝ)⁻¹)
  have hZmeas : ∀ n : ℕ, Measurable (fun ξ => Real.sqrt n • (empiricalMoment f n X ξ - μ_vec)) :=
    fun n => ((hemp_meas n).sub measurable_const).const_smul (Real.sqrt n)
  have hC : WeakConverges
      (fun n => μ.map (fun ξ => Real.sqrt n • (empiricalMoment f n X ξ - μ_vec)))
      (multivariateGaussian 0 (fCov P f)) := by
    have hh := empiricalMoment_weakConverges hf_meas hf_L2 hX_meas hX_indep hX_id hX_law
    rwa [← hμvec] at hh
  have hsqn : Tendsto (fun k : ℕ => Real.sqrt k) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hOP : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • (empiricalMoment f n X ξ - μ_vec)) :=
    isBoundedInProb_of_weakConverges hZmeas hC
  have hcons : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => empiricalMoment f n X ξ - μ_vec) :=
    tendstoInProbZero_of_isBoundedInProb_smul hsqn hOP
  -- remainder →ₚ 0 (delta method, measurability-free)
  have hrem : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n •
        (φ (empiricalMoment f n X ξ) - φ μ_vec
          - (↑e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
              (empiricalMoment f n X ξ - μ_vec))) :=
    delta_method_remainder hφ_deriv hcons hOP
  -- ── the measurable estimator + good-event masses ───────────────────────
  choose θhat hθhat_meas hθhat_eq using
    (fun n => exists_measurable_eq_on_open φ U hU_open hφ_cont θ₀ (hemp_meas n))
  have hmassU_compl :
      Tendsto (fun n => μ.real {ξ | empiricalMoment f n X ξ ∉ U}) atTop (𝓝 0) := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open μ_vec hμmem
    have hsub : ∀ n, {ξ | empiricalMoment f n X ξ ∉ U}
        ⊆ {ξ | ε ≤ ‖empiricalMoment f n X ξ - μ_vec‖} := by
      intro n ξ hξ
      simp only [Set.mem_setOf_eq] at hξ ⊢
      by_contra hlt
      push_neg at hlt
      exact hξ (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hlt))
    exact squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
      (Eventually.of_forall fun n => measureReal_mono (hsub n)) (hcons ε hε)
  have hmassU :
      Tendsto (fun n => μ.real {ξ | empiricalMoment f n X ξ ∈ U}) atTop (𝓝 1) := by
    have heq : ∀ n, μ.real {ξ | empiricalMoment f n X ξ ∈ U}
        = 1 - μ.real {ξ | empiricalMoment f n X ξ ∉ U} := by
      intro n
      have hm : MeasurableSet {ξ | empiricalMoment f n X ξ ∈ U} :=
        (hemp_meas n) hU_open.measurableSet
      have hc : {ξ | empiricalMoment f n X ξ ∉ U}
          = {ξ | empiricalMoment f n X ξ ∈ U}ᶜ := rfl
      rw [hc, measureReal_compl hm, probReal_univ]; ring
    rw [tendsto_congr heq]
    simpa using hmassU_compl.const_sub (1 : ℝ)
  -- shared: `Wn := e'⁻¹(√n•(ℙₙf−μ))`, `Zn := √n•(θ̂−θ₀)`, and `dist(Wn,Zn) →ₚ 0`.
  set Wn : ℕ → Ξ → EuclideanSpace ℝ (Fin d) := fun n ξ =>
    (↑e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (Real.sqrt n • (empiricalMoment f n X ξ - μ_vec)) with hWndef
  set Zn : ℕ → Ξ → EuclideanSpace ℝ (Fin d) := fun n ξ =>
    Real.sqrt n • (θhat n ξ - θ₀) with hZndef
  have hWn_meas : ∀ n : ℕ, AEMeasurable (Wn n) μ := fun n =>
    (((e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).continuous.measurable).comp
      (hZmeas n)).aemeasurable
  have hZn_meas : ∀ n : ℕ, AEMeasurable (Zn n) μ := fun n =>
    (((hθhat_meas n).sub measurable_const).const_smul (Real.sqrt n)).aemeasurable
  have hWn_wc : WeakConverges (fun n => μ.map (Wn n))
      (multivariateGaussian 0 (momentLimitCov P f e')) := by
    have hmap := hC.map
      (e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).continuous
      (e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).continuous.measurable
    rw [momentGaussian_map_eq P hf_L2 e'] at hmap
    have hfix : (fun n : ℕ => (μ.map fun ξ => Real.sqrt n • (empiricalMoment f n X ξ - μ_vec)).map
          (↑e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        = fun n : ℕ => μ.map (Wn n) := by
      funext n
      rw [Measure.map_map
        (e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).continuous.measurable
        (hZmeas n)]
      rfl
    rwa [hfix] at hmap
  have hDist : ∀ ε > 0,
      Tendsto (fun n => μ.real {ξ | ε ≤ dist (Wn n ξ) (Zn n ξ)}) atTop (𝓝 0) := by
    intro ε hε
    have hbound : ∀ n : ℕ, μ.real {ξ | ε ≤ dist (Wn n ξ) (Zn n ξ)}
        ≤ μ.real {ξ | ε ≤ ‖Real.sqrt n •
            (φ (empiricalMoment f n X ξ) - φ μ_vec
              - (↑e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
                  (empiricalMoment f n X ξ - μ_vec))‖}
          + μ.real {ξ | empiricalMoment f n X ξ ∉ U} := by
      intro n
      refine le_trans (measureReal_mono ?_) (measureReal_union_le _ _)
      intro ξ hξ
      by_cases hmem : empiricalMoment f n X ξ ∈ U
      · left
        simp only [Set.mem_setOf_eq] at hξ ⊢
        have hWZ : Wn n ξ - Zn n ξ = -(Real.sqrt n •
            (φ (empiricalMoment f n X ξ) - φ μ_vec
              - (↑e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
                  (empiricalMoment f n X ξ - μ_vec))) := by
          simp only [hWndef, hZndef, hθhat_eq n ξ hmem, hφμ, map_sub, map_smul, smul_sub,
            smul_neg]
          abel
        rwa [dist_eq_norm, hWZ, norm_neg] at hξ
      · right; exact hmem
    have hsum0 : Tendsto (fun n : ℕ => μ.real {ξ | ε ≤ ‖Real.sqrt n •
            (φ (empiricalMoment f n X ξ) - φ μ_vec
              - (↑e'.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
                  (empiricalMoment f n X ξ - μ_vec))‖}
          + μ.real {ξ | empiricalMoment f n X ξ ∉ U}) atTop (𝓝 0) := by
      simpa using (hrem ε hε).add hmassU_compl
    exact squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
      (Eventually.of_forall hbound) hsum0
  -- linear representation = vdV Thm 4.1 display's `o_P` expansion (`√n(θ̂−θ₀) = e'⁻¹√n(ℙₙf−Pf)+o_P`)
  have hlin : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => Zn n ξ - Wn n ξ) := by
    intro ε hε
    refine (hDist ε hε).congr fun n => ?_
    congr 1
    ext ξ
    simp only [Set.mem_setOf_eq]
    rw [dist_eq_norm, norm_sub_rev]
  refine ⟨θhat, hθhat_meas, ?_, ?_, ?_⟩
  · -- existence w.p. → 1
    have hsub_ex : ∀ n, {ξ | empiricalMoment f n X ξ ∈ U}
        ⊆ {ξ | e (θhat n ξ) = empiricalMoment f n X ξ} := by
      intro n ξ hξ
      simp only [Set.mem_setOf_eq] at hξ ⊢
      rw [hθhat_eq n ξ hξ]; exact hrinv _ hξ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hmassU tendsto_const_nhds
      (Eventually.of_forall fun n => measureReal_mono (hsub_ex n))
      (Eventually.of_forall fun n => measureReal_le_one)
  · -- linear representation
    exact hlin
  · -- asymptotic normality
    exact WeakConverges.slutsky_of_tendstoInMeasure_dist hWn_meas hZn_meas hWn_wc hDist

end AsymptoticStatistics.MomentEstimator
