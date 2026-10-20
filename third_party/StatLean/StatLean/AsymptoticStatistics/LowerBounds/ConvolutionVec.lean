module
public import StatLean.AsymptoticStatistics.LowerBounds.Convolution
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorVec
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorVecReverse
public import StatLean.AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import StatLean.AsymptoticStatistics.ForMathlib.CramerWoldAux
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.LevyMpassVec
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Semiparametric Convolution Theorem (vector form)

Let $\psi$ be a vector-valued functional, pathwise differentiable along a tangent set
with efficient influence function tuple $(\tilde\ell_1,\dots,\tilde\ell_k)$, and let
$T_n$ be a *regular* estimator sequence whose normalized error
$\sqrt{n}\,(T_n - \psi(P))$ converges in distribution under $P$ to a limit law $L$ on
$\mathbb{R}^k$. Write $G$ for the Gram (information) matrix of the efficient influence
functions, $G_{ij} = \langle \tilde\ell_i, \tilde\ell_j\rangle$. Then:

* **(a) Covariance lower bound.** If $L$ has a finite second moment with covariance
  matrix $\Sigma$, then $\Sigma - G$ is positive semidefinite; equivalently the
  asymptotic covariance of any regular estimator is no smaller (in the Loewner order)
  than the efficient information matrix $G$.
* **(b) Convolution decomposition.** The limit law factors as
  $L = N(0, G) * M$, a convolution of the centered multivariate Gaussian with
  covariance $G$ and some probability measure $M$ on $\mathbb{R}^k$. In particular the
  efficient (Gaussian) part is a sharp lower bound on the dispersion, attained exactly
  when $M$ is degenerate at $0$.

This is the multivariate generalization of the scalar convolution theorem: the scalar
result is recovered along each direction $\lambda \in \mathbb{R}^k$ by passing to the
real functional $\langle \lambda, \psi\rangle$, whose efficient influence function is
$\sum_j \lambda_j \tilde\ell_j$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information),
Theorem 25.20 — here generalized to vector-valued functionals and efficient influence
function tuples.

**Proof formalization notes.**
Proof strategy for clause (a): inline Cramér-Wold per-λ reduction, scalar application,
and matrix PSD via Brick A (`Matrix.sub_PosSemidef_iff_quadratic_form_le`). For every
direction `lam : Fin k → ℝ` we reduce to the scalar functional `⟪lam, ψ⟫`, apply the
scalar clause (a) to get `lam ⬝ᵥ G ⬝ᵥ lam ≤ lam ⬝ᵥ Σ ⬝ᵥ lam`, and conclude `Σ - G` PSD.

Proof strategy for clause (b): vector analogue of the scalar decomposition using
vec-specific adapters from `ConvolutionUnboundedVec` for the per-`m` Hájek decomposition
and `LevyMpassVec` for the matrix-valued Lévy m-pass with matrix convergence. The key
steps are: universal-`m` decomposition (`derived_convolution_decomp_unbounded_vec`),
per-`m` covariance matrices built from component projection sequences (`proj_seq_to_eif`,
finset-union to a common subspace), a per-`m` orthonormal basis with Parseval
identifying `Σ_m` entrywise, matrix convergence `Σ_m → G` from continuity of the inner
product, and `levyMpass_vec` to extract the convolution decomposition.

**Bibliographic comments.**
The convolution theorem originates with J. Hájek, "A characterization of limiting
distributions of regular estimates," *Zeitschrift für Wahrscheinlichkeitstheorie und
Verwandte Gebiete* **14** (1970), 323–330, which proves that the limit law of any
regular estimator in a (locally asymptotically normal) parametric model is the
convolution of the optimal Gaussian law with an independent residual — the result
van der Vaart presents in finite-dimensional form as Theorem 8.8. Closely related
characterizations were given independently by L. Le Cam and by T. Inagaki, "On the
limiting distribution of a sequence of estimators with uniformity property,"
*Annals of the Institute of Statistical Mathematics* **22** (1970), 1–13. The
semiparametric (infinite-dimensional tangent space) generalization formalized here is
due to J. M. Begun, W. J. Hall, W.-M. Huang and J. A. Wellner, "Information and
asymptotic efficiency in parametric–nonparametric models," *Annals of Statistics*
**11** (1983), 432–452; it is the form appearing as vdV Theorem 25.20.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal BigOperators

namespace AsymptoticStatistics.LowerBounds.ConvolutionVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.PathwiseVec
open AsymptoticStatistics.Core.EIF
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.LowerBounds.RegularEstimator
open AsymptoticStatistics.LowerBounds.RegularEstimatorVec
open AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {T_set : TangentSpec P}
variable {k : ℕ}

/-- **Helper: norm squared of linear combination equals quadratic form.

Norm squared of ∑ⱼ λⱼ • IF_j equals the quadratic form λ ⬝ᵥ G ⬝ᵥ λ.
-/
theorem eif_linear_combo_norm_sq
    (T : Submodule ℝ ↥(L2ZeroMean P))
    (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin k))
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec Dψ IF_eff)
    (lam : Fin k → ℝ) :
    ‖(∑ j : Fin k, lam j • IF_eff j : ↥(L2ZeroMean P))‖ ^ 2
      = dotProduct (star lam) ((Matrix.gram ℝ IF_eff).mulVec lam) := by
  rw [← @real_inner_self_eq_norm_sq]
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
    Matrix.gram_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [real_inner_comm (IF_eff i) (IF_eff j)]
  ring

/-- **Helper: per-λ scalar regularity from vector regularity.**

For each direction λ, scalar regularity follows from vector regularity via inner product projection.
-/
theorem scalar_regularity_of_vector
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin k))
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_broad_vec P T_set ψ hψ hEIF T_n L)
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
      IsRegularEstimator P T_set ψ_lam hψ_lam hEIF_lam T_n_lam L_lam := by
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
      -- Linner v = ⟪lam_lifted, v⟫_ℝ.
      change ⟪lam_lifted, t⁻¹ • (ψ (γ.curve t) - ψ P)⟫_ℝ
            = (ψ_lam (γ.curve t) - ψ_lam P) / t
      rw [inner_smul_right, inner_sub_right, div_eq_inv_mul]
    -- Apply the rewrite under the Tendsto.
    have h_pushed' :
        Filter.Tendsto
          (fun t : ℝ => (ψ_lam (γ.curve t) - ψ_lam P) / t)
          (nhdsWithin 0 {0}ᶜ) (nhds (Linner (hψ.derivative ⟨γ.score, h_in_T⟩))) := by
      have : (fun t : ℝ => Linner (t⁻¹ • (ψ (γ.curve t) - ψ P))) =
              (fun t : ℝ => (ψ_lam (γ.curve t) - ψ_lam P) / t) := by
        funext t; exact h_eq t
      rwa [this] at h_pushed
    -- The derivative of the new pathwise structure is (Linner.comp hψ.derivative) ⟨γ.score, _⟩
    -- which equals Linner (hψ.derivative ⟨γ.score, _⟩).
    exact h_pushed'
  · -- ============== Step 2: build hEIF_lam ==============
    -- The derivative of the constructed hψ_lam is (Linner.comp hψ.derivative).
    -- We need: IsInfluenceFunction (representation) ∧ IF_lam ∈ tangentSpace T_set.
    refine ⟨?_, ?_⟩
    · -- Representation: ∀ g : T, ⟪IF_lam, g⟫_ℝ = (Linner ∘L hψ.derivative) g.
      intro g
      -- LHS: ⟪Σⱼ lam j • IF_eff j, g⟫
      change ⟪(∑ j : Fin k, lam j • IF_eff j : ↥(L2ZeroMean P)),
            (g : ↥(L2ZeroMean P))⟫_ℝ = Linner (hψ.derivative g)
      rw [sum_inner]
      simp_rw [real_inner_smul_left]
      -- Each term: lam j * ⟪IF_eff j, g⟫_ℝ = lam j * (EuclideanSpace.proj j ∘L hψ.derivative) g
      have hEIF_per : ∀ j : Fin k,
          ⟪IF_eff j, (g : ↥(L2ZeroMean P))⟫_ℝ
            = (EuclideanSpace.proj j ∘L hψ.derivative) g := fun j => (hEIF j).1 g
      simp_rw [hEIF_per]
      -- Unfold Linner and use PiLp.inner_apply to express the inner product as a sum.
      change ∑ j, lam j * (EuclideanSpace.proj j) (hψ.derivative g)
            = ⟪lam_lifted, hψ.derivative g⟫_ℝ
      rw [PiLp.inner_apply]
      -- ⟪lam_lifted, hψ.derivative g⟫_ℝ = ∑ j, inner ℝ (lam_lifted.ofLp j) ((hψ.derivative g).ofLp
      -- j)
      -- For ℝ scalars: inner ℝ a b = b * a; (EuclideanSpace.proj j) x = x.ofLp j; lam_lifted.ofLp j
      -- = lam j.
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
    -- L_lam = L.map (fun v => ⟪lam_lifted, v⟫_ℝ).
    change IsProbabilityMeasure (L.map (fun v => ⟪lam_lifted, v⟫_ℝ))
    have h_meas : Measurable (fun v : EuclideanSpace ℝ (Fin k) =>
        ⟪lam_lifted, v⟫_ℝ) := Linner.measurable
    exact Measure.isProbabilityMeasure_map h_meas.aemeasurable
  · -- ============== Step 4: IsRegularEstimator ==============
    -- Need: ∀ g hg curve hscore, WeakConverges (...) L_lam.
    intro g hg curve hscore
    -- From vector regularity: vec weak conv to L.
    have hRegV := hReg g hg curve hscore
    -- Push through Linner (continuous + measurable) to get pushforward weak conv.
    have h_pushed := hRegV.map (f := fun v => ⟪lam_lifted, v⟫_ℝ)
        Linner.continuous Linner.measurable
    -- The pushed measure on RHS is L_lam by definition.
    -- The pushed sequence on LHS: each measure is `(Pn n).map (vec scaled diff)`.
    -- After `WeakConverges.map`, it becomes `((Pn n).map (vec)).map (inner) = (Pn n).map (inner ∘
    -- vec)`.
    -- We need it to equal `(Pn n).map (scalar scaled diff)`.
    have h_map_eq : ∀ n : ℕ,
        ((MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n •
              (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹))))).map
          (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam_lifted, v⟫_ℝ)
        = (MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n_lam n X - ψ_lam (curve.curve ((Real.sqrt n)⁻¹)))) := by
      intro n
      -- Measurability of the inner-product function.
      have h_inner_meas : Measurable (fun v : EuclideanSpace ℝ (Fin k) =>
          ⟪lam_lifted, v⟫_ℝ) := Linner.measurable
      -- Measurability of the vec scaled diff function.
      have h_vec_meas : Measurable (fun X : Fin n → Ω =>
          Real.sqrt n • (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))) :=
        measurable_const.fun_smul ((hT_meas n).fun_sub measurable_const)
      -- Compose the two maps.
      rw [Measure.map_map h_inner_meas h_vec_meas]
      -- Show the composed function equals the scalar form.
      congr 1
      funext X
      -- Inner with √n • (T_n n X - ψ ...) = √n * ⟪lam_lifted, T_n n X - ψ ...⟫
      --                                  = √n * (T_n_lam n X - ψ_lam ...)
      change ⟪lam_lifted, Real.sqrt n • (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))⟫_ℝ
            = Real.sqrt n * (T_n_lam n X - ψ_lam (curve.curve ((Real.sqrt n)⁻¹)))
      rw [inner_smul_right, inner_sub_right]
    -- Apply h_map_eq to rewrite h_pushed.
    have h_pushed' :
        WeakConverges
          (fun n : ℕ =>
            (MeasureTheory.Measure.pi
                (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
              (fun X : Fin n → Ω =>
                Real.sqrt n *
                  (T_n_lam n X - ψ_lam (curve.curve ((Real.sqrt n)⁻¹)))))
          L_lam := by
      have h_funext :
          (fun n : ℕ =>
            ((MeasureTheory.Measure.pi
                (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
              (fun X : Fin n → Ω =>
                Real.sqrt n •
                  (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹))))).map
              (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam_lifted, v⟫_ℝ)) =
          (fun n : ℕ =>
            (MeasureTheory.Measure.pi
                (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
              (fun X : Fin n → Ω =>
                Real.sqrt n *
                  (T_n_lam n X - ψ_lam (curve.curve ((Real.sqrt n)⁻¹))))) := by
        funext n; exact h_map_eq n
      rwa [h_funext] at h_pushed
    exact h_pushed'

/-- **Helper: pushforward variance as quadratic form.

Variance of the pushforward under inner product equals the quadratic form λ ⬝ᵥ Σ ⬝ᵥ λ.
-/
theorem pushforward_variance_eq_quadratic
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L]
    (hL : MemLp (id : EuclideanSpace ℝ (Fin k) → _) 2 L)
    (lam : Fin k → ℝ) :
    let Sigma : Matrix (Fin k) (Fin k) ℝ := fun i j =>
      ∫ y, (y.ofLp i - ∫ z, z.ofLp i ∂L) * (y.ofLp j - ∫ z, z.ofLp j ∂L) ∂L
    variance (id : ℝ → ℝ)
      (L.map (fun v => ⟪((WithLp.equiv 2 _).symm lam : EuclideanSpace ℝ (Fin k)), v⟫_ℝ))
      = dotProduct (star lam) (Sigma.mulVec lam) := by
  intro Sigma
  -- Notation: `lam_lifted` is `lam` viewed as a vector in `EuclideanSpace ℝ (Fin k)`.
  set lam_lifted : EuclideanSpace ℝ (Fin k) := (WithLp.equiv 2 _).symm lam with hlam_def
  -- The pushforward function `f : EuclideanSpace ℝ (Fin k) → ℝ`.
  set f : EuclideanSpace ℝ (Fin k) → ℝ := fun v => ⟪lam_lifted, v⟫_ℝ with hf_def
  have hf_meas : Measurable f := by fun_prop
  have hf_aem : AEMeasurable f L := hf_meas.aemeasurable
  -- `id : EuclideanSpace ℝ (Fin k) → _` is integrable on `L` (from `MemLp` at `q = 2 ≥ 1`).
  have hL_int : Integrable (id : EuclideanSpace ℝ (Fin k) → _) L :=
    hL.integrable (by norm_num)
  -- Each coordinate `z ↦ z.ofLp i` is integrable on `L`.
  have h_coord_int : ∀ i : Fin k, Integrable (fun z : EuclideanSpace ℝ (Fin k) => z.ofLp i) L := by
    intro i
    exact (MeasureTheory.Integrable.eval_piLp hL_int) i
  -- `f` itself is integrable on `L` (Cauchy–Schwarz / `MemLp.const_inner`).
  have hf_int : Integrable f L :=
    (MeasureTheory.MemLp.const_inner (𝕜 := ℝ) lam_lifted hL).integrable (by norm_num)
  -- Step 1: collapse the pushforward variance using `variance_map`.
  have h_var_map :
      variance (id : ℝ → ℝ) (L.map f) = variance f L := by
    rw [variance_map measurable_id.aemeasurable hf_aem]
    rfl
  -- Step 2: rewrite `variance f L` as the integral form.
  have h_var_int :
      variance f L = ∫ y, (f y - ∫ z, f z ∂L) ^ 2 ∂L :=
    variance_eq_integral hf_aem
  -- Step 3: compute `∫ z, f z ∂L = ⟪lam_lifted, ∫ z, z ∂L⟫_ℝ`.
  have h_integral_inner :
      ∫ z, f z ∂L = ⟪lam_lifted, ∫ z, z ∂L⟫_ℝ :=
    integral_inner (𝕜 := ℝ) hL_int lam_lifted
  -- Let `μ` denote the vector mean.
  set μ : EuclideanSpace ℝ (Fin k) := ∫ z, z ∂L with hμ_def
  -- For each i, `μ.ofLp i = ∫ z, z.ofLp i ∂L` (coordinate evaluation of vector integral).
  have h_mean_coord : ∀ i : Fin k, μ.ofLp i = ∫ z, z.ofLp i ∂L := by
    intro i
    -- `(∫ z, z ∂L) i = ∫ z, z i ∂L` by `eval_integral_piLp`.
    -- Note: for `z : EuclideanSpace ℝ (Fin k)`, `z i = z.ofLp i` via the `CoeFun` instance.
    exact MeasureTheory.eval_integral_piLp (fun i => h_coord_int i) i
  -- Step 4: identify the integrand as `⟪lam_lifted, y - μ⟫_ℝ ^ 2`.
  have h_integrand_eq : ∀ y : EuclideanSpace ℝ (Fin k),
      (f y - ∫ z, f z ∂L) ^ 2 = ⟪lam_lifted, y - μ⟫_ℝ ^ 2 := by
    intro y
    rw [h_integral_inner, hf_def]
    -- ⟪lam_lifted, y⟫ - ⟪lam_lifted, μ⟫ = ⟪lam_lifted, y - μ⟫ by `inner_sub_right`.
    congr 1
    exact (inner_sub_right (𝕜 := ℝ) lam_lifted y μ).symm
  -- Step 5: unfold the inner product into a coordinate sum.
  -- `⟪lam_lifted, y - μ⟫_ℝ = ∑ i, (y.ofLp i - μ.ofLp i) * lam i`.
  have h_inner_sum : ∀ y : EuclideanSpace ℝ (Fin k),
      ⟪lam_lifted, y - μ⟫_ℝ = ∑ i : Fin k, (y.ofLp i - μ.ofLp i) * lam i := by
    intro y
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- For real coordinates, `⟪a, b⟫_ℝ = b * a` by `RCLike.inner_apply` (real conj = id).
    -- `lam_lifted.ofLp i = lam i` (from `ofLp_toLp`).
    -- `(y - μ).ofLp i = y.ofLp i - μ.ofLp i` (from `PiLp.sub_apply`).
    change (y - μ).ofLp i * lam_lifted.ofLp i
        = (y.ofLp i - μ.ofLp i) * lam i
    rfl
  -- Step 6: square as a double sum.
  have h_sq_double_sum : ∀ y : EuclideanSpace ℝ (Fin k),
      ⟪lam_lifted, y - μ⟫_ℝ ^ 2
        = ∑ i : Fin k, ∑ j : Fin k,
            lam i * lam j * ((y.ofLp i - μ.ofLp i) * (y.ofLp j - μ.ofLp j)) := by
    intro y
    rw [h_inner_sum y, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  -- Step 7: integrate term-by-term.
  have h_term_int : ∀ i j : Fin k,
      Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
        lam i * lam j * ((y.ofLp i - μ.ofLp i) * (y.ofLp j - μ.ofLp j))) L := by
    intro i j
    -- The factor `(y.ofLp i - μ.ofLp i)` is in L² (since `z ↦ z.ofLp i` is in L² via
    -- `MemLp.eval_piLp` on `hL`), and product of two L² is L¹ via `MemLp.integrable_mul`.
    have hL_coord : ∀ i : Fin k,
        MemLp (fun z : EuclideanSpace ℝ (Fin k) => z.ofLp i) 2 L := by
      intro i
      exact (MeasureTheory.MemLp.eval_piLp hL) i
    have h1 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y.ofLp i - μ.ofLp i) 2 L :=
      (hL_coord i).sub (memLp_const _)
    have h2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y.ofLp j - μ.ofLp j) 2 L :=
      (hL_coord j).sub (memLp_const _)
    have h_mul : Integrable
        (fun y => (y.ofLp i - μ.ofLp i) * (y.ofLp j - μ.ofLp j)) L := by
      have := MemLp.integrable_mul h1 h2
      exact this
    exact h_mul.const_mul (lam i * lam j)
  -- Step 8: chain it all together.
  calc
    variance (id : ℝ → ℝ) (L.map f)
        = variance f L := h_var_map
    _ = ∫ y, (f y - ∫ z, f z ∂L) ^ 2 ∂L := h_var_int
    _ = ∫ y, ⟪lam_lifted, y - μ⟫_ℝ ^ 2 ∂L := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro y; exact h_integrand_eq y
    _ = ∫ y, (∑ i : Fin k, ∑ j : Fin k,
              lam i * lam j * ((y.ofLp i - μ.ofLp i) * (y.ofLp j - μ.ofLp j))) ∂L := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro y; exact h_sq_double_sum y
    _ = ∑ i : Fin k, ∑ j : Fin k,
          ∫ y, lam i * lam j * ((y.ofLp i - μ.ofLp i) * (y.ofLp j - μ.ofLp j)) ∂L := by
          rw [integral_finset_sum _ (fun i _ =>
            integrable_finset_sum _ (fun j _ => h_term_int i j))]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [integral_finset_sum _ (fun j _ => h_term_int i j)]
    _ = ∑ i : Fin k, ∑ j : Fin k,
          lam i * lam j *
            ∫ y, (y.ofLp i - μ.ofLp i) * (y.ofLp j - μ.ofLp j) ∂L := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [integral_const_mul]
    _ = ∑ i : Fin k, ∑ j : Fin k, lam i * lam j * Sigma i j := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          congr 1
          change (∫ y, (y.ofLp i - μ.ofLp i) * (y.ofLp j - μ.ofLp j) ∂L)
              = ∫ y, (y.ofLp i - ∫ z, z.ofLp i ∂L)
                    * (y.ofLp j - ∫ z, z.ofLp j ∂L) ∂L
          rw [h_mean_coord i, h_mean_coord j]
    _ = dotProduct (star lam) (Sigma.mulVec lam) := by
          simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
    Matrix.gram_apply]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          ring

/-- **Theorem 25.20 clause (a), vector form** — variance bound on the
asymptotic covariance matrix of a regular vector estimator.

Conclusion: the covariance matrix of `L` minus the Gram matrix of the EIF
tuple is positive semidefinite.

This is proved via inline Cramér-Wold reduction: for every direction `lam : Fin k → ℝ`,
we reduce to the scalar functional `⟪lam, ψ⟫` and apply the scalar clause (a), obtaining
`lam ⬝ᵥ G ⬝ᵥ lam ≤ lam ⬝ᵥ Σ ⬝ᵥ lam` for the respective quadratic forms. Since this holds
for all `lam`, the difference matrix is PSD. -/
theorem semiparametric_convolution_theorem_vec_clause_a
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_vec P T_set ψ hψ hEIF T_n L)
    (hL_memLp : MemLp (id : EuclideanSpace ℝ (Fin k) → _) 2 L) :
    let G : Matrix (Fin k) (Fin k) ℝ := Matrix.gram ℝ IF_eff
    let Sigma : Matrix (Fin k) (Fin k) ℝ := fun i j =>
      ∫ y, (y.ofLp i - ∫ z, z.ofLp i ∂L)
          * (y.ofLp j - ∫ z, z.ofLp j ∂L) ∂L
    (Sigma - G).PosSemidef := by
  intro G Sigma
  -- Present the vdV-canonical hypothesis; recover the all-paths form for the
  -- internal per-λ Cramér–Wold reduction via the formal equivalence (E4_vec).
  replace hReg := isRegularEstimator_vec_implies_broad hReg hT_meas
  -- Use Brick A to reduce to checking quadratic form inequality for all vectors.
  rw [Matrix.sub_PosSemidef_iff_quadratic_form_le]
  · intro lam
    -- Cramér-Wold per-λ reduction: apply scalar theorem and convert between quadratic forms.
    obtain ⟨hψ_lam, hEIF_lam, hL_lam_prob, hReg_lam⟩ :=
      scalar_regularity_of_vector ψ hψ hEIF T_n hT_meas L hReg lam
    -- 2. Build the scalar pieces: the lifted vector, the inner-product functional,
    -- measurability of the scalarised statistic, and `MemLp` of the pushforward.
    set lam_lifted : EuclideanSpace ℝ (Fin k) :=
        (WithLp.equiv 2 _).symm lam with hlam_lifted_def
    set Linner : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := innerSL ℝ lam_lifted with hLinner_def
    have hT_lam_meas : ∀ n, Measurable (fun X : Fin n → Ω =>
        ⟪lam_lifted, T_n n X⟫_ℝ) :=
      fun n => Linner.measurable.comp (hT_meas n)
    have hf_meas : Measurable (fun v : EuclideanSpace ℝ (Fin k) =>
        ⟪lam_lifted, v⟫_ℝ) := Linner.measurable
    have hf_memLp : MemLp (fun v : EuclideanSpace ℝ (Fin k) =>
        ⟪lam_lifted, v⟫_ℝ) 2 L :=
      MemLp.const_inner (𝕜 := ℝ) lam_lifted hL_memLp
    haveI hL_lam_prob' :
        IsProbabilityMeasure (L.map (fun v : EuclideanSpace ℝ (Fin k) =>
          ⟪lam_lifted, v⟫_ℝ)) := hL_lam_prob
    have hL_lam_memLp : MemLp (id : ℝ → ℝ) 2
        (L.map (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam_lifted, v⟫_ℝ)) := by
      rw [memLp_map_measure_iff aestronglyMeasurable_id hf_meas.aemeasurable]
      exact hf_memLp
    -- 3. Apply scalar clause (a) to the lifted regularity package.
    -- Use `_` for `hψ` so Lean infers it from `hEIF_lam`'s type — this avoids
    -- the `hψ_lam✝` shadowing artifact from destructuring nested dependent ∃.
    have h_scalar :=
      AsymptoticStatistics.LowerBounds.Convolution.semiparametric_convolution_theorem_clause_a
        T_set _ hEIF_lam _ hT_lam_meas _ hReg_lam hL_lam_memLp
    -- 4. Rewrite RHS (`∫ x, (x - ∫ y, y ∂L_lam)² ∂L_lam`) as `variance id L_lam`.
    have h_var_form :
        (∫ x, (x - ∫ y, y ∂(L.map (fun v : EuclideanSpace ℝ (Fin k) =>
              ⟪lam_lifted, v⟫_ℝ)))^2
            ∂(L.map (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam_lifted, v⟫_ℝ)))
          = variance (id : ℝ → ℝ)
              (L.map (fun v : EuclideanSpace ℝ (Fin k) => ⟪lam_lifted, v⟫_ℝ)) := by
      rw [variance_eq_integral aemeasurable_id]
      simp
    rw [h_var_form] at h_scalar
    rw [pushforward_variance_eq_quadratic L hL_memLp lam] at h_scalar
    rw [eif_linear_combo_norm_sq (tangentSpace T_set) hψ.derivative hEIF lam] at h_scalar
    -- `G = Matrix.gram ℝ IF_eff` and `Sigma = ...` are the same let-bound values; the goal closes.
    exact h_scalar
  · -- G is Hermitian (symmetric for reals)
    exact Matrix.isHermitian_gram ℝ IF_eff
  · -- Sigma is Hermitian (symmetric for reals) — covariance matrices are always symmetric
    unfold Matrix.IsHermitian
    funext i j
    change Sigma j i = star (Sigma i j)
    simp only [star_trivial]
    change (∫ y, (y.ofLp j - ∫ z, z.ofLp j ∂L) * (y.ofLp i - ∫ z, z.ofLp i ∂L) ∂L) =
           (∫ y, (y.ofLp i - ∫ z, z.ofLp i ∂L) * (y.ofLp j - ∫ z, z.ofLp j ∂L) ∂L)
    congr 1 with y
    ring

set_option maxHeartbeats 800000 in
-- The composite Tendsto-on-matrices chain (entrywise inner-product tendsto,
-- Parseval + `tendsto_pi_nhds` twice, plus the dependent let-bound `Sigma_m / G`
-- elaboration) exceeds the default 200 000-heartbeat cap.
/-- **Theorem 25.20 clause (b), vector form** — convolution decomposition of the
asymptotic distribution of a regular vector estimator.

Conclusion: the limiting measure `L` decomposes as a convolution of a multivariate
Gaussian with covariance equal to the Gram matrix of the efficient influence
function tuple, and an arbitrary probability measure. The argument runs entirely in
the closed linear span `tangentSpace T_set`.

This is proved parallel to the scalar clause (b), using vec-specific adapters
from `ConvolutionUnboundedVec` for the per-m Hájek decomposition and `LevyMpassVec`
for the matrix-valued Lévy m-pass. The key steps are:
- Step 0a: derive universal-m decomposition via `derived_convolution_decomp_unbounded_vec`
- Steps 1a-1b: build per-m covariance matrices via component projection sequences
  (componentwise projection via `proj_seq_to_eif`, finset-union to build a common subspace)
- Step 2: per-m basis via `stdOrthonormalBasis` and Parseval to identify
  `Σ_m = (ψDotMat * 1⁻¹ * ψDotMat.T)` entrywise as `⟪p m i, p m j⟫`
- Step 3: matrix convergence `Σ_m → G` from continuity of inner product
- Step 4: apply `levyMpass_vec` to extract the convolution decomposition.
-/
theorem semiparametric_convolution_theorem_vec_clause_b
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_vec P T_set ψ hψ hEIF T_n L) :
    let G : Matrix (Fin k) (Fin k) ℝ := Matrix.gram ℝ IF_eff
    ∃ M : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure M ∧
      L = (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) G) ∗ M := by
  classical
  intro G
  -- Present the vdV-canonical hypothesis; recover the all-paths form for the
  -- internal per-`m` Hájek decomposition via the formal equivalence (E4_vec).
  replace hReg := isRegularEstimator_vec_implies_broad hReg hT_meas
  -- Step 0: register useful instances.
  haveI hUG_L2 : IsUniformAddGroup ↥(L2ZeroMean P) :=
    (L2ZeroMean P).toAddSubgroup.isUniformAddGroup
  -- Step 0a: per-`m` vec decomposition for any orthonormal basis in `tangentSpace T_set`.
  have hRegular_vec : ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
      (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
      (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
      ∃ M_per : Measure (EuclideanSpace ℝ (Fin k)),
        IsProbabilityMeasure M_per ∧
        L = MeasureTheory.Measure.conv
              (ProbabilityTheory.multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin k))
                (ψDotMat_vec g_P IF_eff *
                  (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
                  (ψDotMat_vec g_P IF_eff).transpose))
              M_per := fun {m} g_P h_orth h_in_T =>
    derived_convolution_decomp_unbounded_vec T_set hψ hEIF T_n hT_meas hReg
      g_P h_orth h_in_T
  -- Step 1a: per-component projection sequence + L²-convergence.
  -- For each i : Fin k, apply `proj_seq_to_eif` to `IF_eff i ∈ tangentSpace T_set`.
  have h_mem : ∀ i : Fin k, (IF_eff i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set :=
    fun i => (hEIF i).2
  have h_per_comp : ∀ i : Fin k,
      ∃ V : ℕ → Submodule ℝ ↥(L2ZeroMean P),
      ∃ p : ℕ → ↥(L2ZeroMean P),
        (∀ m, V m ≤ tangentSpace T_set) ∧
        (∀ m, ∃ S : Finset ↥(L2ZeroMean P),
                (↑S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier ∧
                V m = Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P))) ∧
        (∀ m, p m ∈ V m ∧ (IF_eff i) - p m ∈ (V m)ᗮ) ∧
        Tendsto (fun m => ‖(p m : ↥(L2ZeroMean P)) - IF_eff i‖) atTop (𝓝 0) := by
    intro i
    obtain ⟨V_i, p_i, hV_le_i, _hV_inc_i, _hV_findim_i, hV_span_i,
              hp_proj_i, h_p_tendsto_i⟩ :=
      AsymptoticStatistics.LowerBounds.ProjSeqToEif.proj_seq_to_eif T_set (h_mem i)
    exact ⟨V_i, p_i, hV_le_i, hV_span_i, hp_proj_i, h_p_tendsto_i⟩
  choose Vc pc hVc_le hVc_span hpc_proj hpc_tendsto using h_per_comp
  -- Step 1b: build a common finset sequence `S_m := ⋃ i, S_m^{(i)}` for each `m`.
  -- Each `Vc i m = Submodule.span ℝ (Sc i m)` via `choose` on `hVc_span`.
  choose Sc hSc_sub hVc_eq using hVc_span
  -- Joint finset: union over components.
  let S : ℕ → Finset ↥(L2ZeroMean P) :=
    fun m => Finset.univ.biUnion (fun i : Fin k => Sc i m)
  -- Joint subspace `V m := span ℝ (S m)`.
  let V : ℕ → Submodule ℝ ↥(L2ZeroMean P) :=
    fun m => Submodule.span ℝ (↑(S m) : Set ↥(L2ZeroMean P))
  -- Each `S m ⊆ T_set.carrier`.
  have hS_sub : ∀ m, (↑(S m) : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier := by
    intro m x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact hSc_sub i m hxi
  -- Each `V m ≤ tangentSpace T_set`.
  have hV_le : ∀ m, V m ≤ tangentSpace T_set := by
    intro m
    refine le_trans (Submodule.span_mono (hS_sub m)) ?_
    exact (Submodule.span ℝ T_set.carrier).le_topologicalClosure
  -- Each `V m ≤ span carrier` (regularity is invoked only on span directions).
  have hV_le_span : ∀ m, V m ≤ Submodule.span ℝ T_set.carrier :=
    fun m => Submodule.span_mono (hS_sub m)
  -- Each `Vc i m ≤ V m` (since `Sc i m ⊆ S m`).
  have hVc_le_V : ∀ i m, Vc i m ≤ V m := by
    intro i m
    rw [hVc_eq i m]
    refine Submodule.span_mono ?_
    intro x hx
    rw [Finset.mem_coe]
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact hx
  -- Each `V m` is finite-dimensional.
  have hV_findim : ∀ m, FiniteDimensional ℝ (V m) :=
    fun m => FiniteDimensional.span_finset ℝ (S m)
  -- Each `V m` is complete (finite-dim ⇒ complete).
  have hV_complete : ∀ m, CompleteSpace (V m) := fun m =>
    haveI := hV_findim m
    haveI : IsUniformAddGroup ↥(V m) := (V m).toAddSubgroup.isUniformAddGroup
    @FiniteDimensional.complete ℝ ↥(V m) _ _ _ _ _ _ _ _ _
  -- Each `V m` has an orthogonal-projection instance.
  have hV_proj : ∀ m, (V m).HasOrthogonalProjection := fun m =>
    @Submodule.HasOrthogonalProjection.ofCompleteSpace _ _ _ _ _ (V m)
      (hV_complete m)
  -- Joint projection sequence: `p m i := V m.starProjection (IF_eff i)`.
  let p : ℕ → Fin k → ↥(L2ZeroMean P) := fun m i =>
    haveI := hV_proj m; (V m).starProjection (IF_eff i)
  -- Joint convergence: for each i, `‖p m i - IF_eff i‖ → 0` as `m → ∞`.
  -- Reason: `‖p m i - IF_eff i‖ = dist (IF_eff i) (V m) ≤ dist (IF_eff i) (Vc i m)
  --                              = ‖pc i m - IF_eff i‖ → 0`.
  have hp_tendsto : ∀ i : Fin k,
      Tendsto (fun m => ‖(p m i : ↥(L2ZeroMean P)) - IF_eff i‖) atTop (𝓝 0) := by
    intro i
    -- Squeeze: `0 ≤ ‖p m i - IF_eff i‖ ≤ ‖pc i m - IF_eff i‖`.
    refine squeeze_zero (fun _ => norm_nonneg _) ?_ (hpc_tendsto i)
    intro m
    -- `p m i = V m.starProjection (IF_eff i)`; `pc i m ∈ V m`.
    haveI := hV_proj m
    have hpc_in_V : pc i m ∈ V m := by
      have hpc_in_Vc : pc i m ∈ Vc i m := (hpc_proj i m).1
      exact hVc_le_V i m hpc_in_Vc
    -- Switch to a `norm_sub_rev` form, then minimality.
    have h_norm_swap : ‖(p m i : ↥(L2ZeroMean P)) - IF_eff i‖
        = ‖IF_eff i - p m i‖ := norm_sub_rev _ _
    rw [h_norm_swap, norm_sub_rev (pc i m) (IF_eff i)]
    -- Now goal: `‖IF_eff i - p m i‖ ≤ ‖IF_eff i - pc i m‖`.
    -- Use minimality: `‖IF_eff i - p m i‖ = ⨅ x : V m, ‖IF_eff i - x‖ ≤ ‖IF_eff i - pc i m‖`.
    rw [show p m i = (V m).starProjection (IF_eff i) from rfl,
      Submodule.starProjection_minimal (IF_eff i)]
    refine ciInf_le ⟨0, ?_⟩ (⟨pc i m, hpc_in_V⟩ : V m)
    rintro _ ⟨_, rfl⟩
    exact norm_nonneg _
  -- Step 2: per-`m` orthonormal basis `g_P_m` of `V m` and PSD matrix `Σ_m`.
  -- Define `n_m m := finrank ℝ (V m)`, `g_P_m m i := stdOrthonormalBasis i`.
  have h_basis_data : ∀ m,
      ∃ (n_m : ℕ) (g_P_m : Fin n_m → ↥(L2ZeroMean P))
        (_h_orth_m : Orthonormal ℝ
          (fun i : Fin n_m => (g_P_m i : Lp ℝ 2 P)))
        (_h_in_m : ∀ i, (g_P_m i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
        ∀ i j : Fin k,
          (ψDotMat_vec g_P_m IF_eff *
            (1 : Matrix (Fin n_m) (Fin n_m) ℝ)⁻¹ *
            (ψDotMat_vec g_P_m IF_eff).transpose) i j =
            ⟪(p m i : ↥(L2ZeroMean P)), p m j⟫_ℝ := by
    intro m
    haveI := hV_findim m
    haveI := hV_proj m
    let b : OrthonormalBasis (Fin (Module.finrank ℝ ↥(V m))) ℝ ↥(V m) :=
      stdOrthonormalBasis ℝ ↥(V m)
    let g_P_m : Fin (Module.finrank ℝ ↥(V m)) → ↥(L2ZeroMean P) :=
      fun i => (b i : ↥(L2ZeroMean P))
    have hg_orth : Orthonormal ℝ
        (fun i : Fin (Module.finrank ℝ ↥(V m)) =>
          (g_P_m i : ↥(L2ZeroMean P))) := by
      have hb := b.orthonormal
      simpa [g_P_m, Function.comp] using!
        ((V m).subtypeₗᵢ.orthonormal_comp_iff).mpr hb
    have hg_in_T : ∀ i, (g_P_m i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier :=
      fun i => hV_le_span m (b i).2
    -- Matrix entry identity:
    -- `(ψDotMat * 1⁻¹ * ψDotMat^T)_{i,j} = Σ_l ⟪IF_i, g_l⟫ * ⟪IF_j, g_l⟫ = ⟪p_i, p_j⟫`.
    refine ⟨_, g_P_m, hg_orth, hg_in_T, ?_⟩
    intro i j
    -- Step 2.1: expand the matrix product entrywise.
    have h_mat_expand :
        (ψDotMat_vec g_P_m IF_eff *
          (1 : Matrix (Fin (Module.finrank ℝ ↥(V m)))
            (Fin (Module.finrank ℝ ↥(V m))) ℝ)⁻¹ *
          (ψDotMat_vec g_P_m IF_eff).transpose) i j
          = ∑ l : Fin (Module.finrank ℝ ↥(V m)),
              ⟪IF_eff i, (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
                * ⟪IF_eff j, (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ := by
      simp only [inv_one, Matrix.mul_one]
      -- Now goal: `(ψDotMat * ψDotMat^T) i j = Σ_l …`.
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [ψDotMat_vec, Matrix.transpose_apply]
    rw [h_mat_expand]
    -- Step 2.2: rewrite each `⟪IF_eff i, g_l⟫ = ⟪p_m i, g_l⟫` via orthogonality residual.
    -- Use `hpc_proj` analogue for V m: `IF_eff i - p m i ⊥ V m`, so
    -- `⟪g_l, IF_eff i - p m i⟫ = 0`, i.e. `⟪g_l, IF_eff i⟫ = ⟪g_l, p m i⟫`.
    have h_resid : ∀ (i : Fin k) (l : Fin (Module.finrank ℝ ↥(V m))),
        ⟪(g_P_m l : ↥(L2ZeroMean P)), (IF_eff i) - (p m i)⟫_ℝ = 0 := by
      intro i l
      have h_perp : (IF_eff i) - (p m i) ∈ (V m)ᗮ := by
        change (IF_eff i : ↥(L2ZeroMean P)) - (V m).starProjection (IF_eff i)
              ∈ (V m)ᗮ
        exact (V m).sub_starProjection_mem_orthogonal (IF_eff i)
      have h_g_in : (g_P_m l : ↥(L2ZeroMean P)) ∈ V m := (b l).2
      exact (Submodule.mem_orthogonal _ _).mp h_perp _ h_g_in
    have h_swap_g : ∀ (i : Fin k) (l : Fin (Module.finrank ℝ ↥(V m))),
        ⟪(IF_eff i : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪(p m i : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ := by
      intro i l
      have hres := h_resid i l
      rw [inner_sub_right, sub_eq_zero] at hres
      -- `hres : ⟪g_l, IF_eff i⟫ = ⟪g_l, p m i⟫`.
      have h_sym1 : ⟪(IF_eff i : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
            = ⟪(g_P_m l : ↥(L2ZeroMean P)), (IF_eff i : ↥(L2ZeroMean P))⟫_ℝ :=
        real_inner_comm _ _
      have h_sym2 : ⟪(p m i : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
            = ⟪(g_P_m l : ↥(L2ZeroMean P)), (p m i : ↥(L2ZeroMean P))⟫_ℝ :=
        real_inner_comm _ _
      rw [h_sym1, h_sym2]
      exact hres
    -- Rewrite the sum LHS using `h_swap_g` on both factors.
    have h_sum_rewrite :
        (∑ l : Fin (Module.finrank ℝ ↥(V m)),
            ⟪IF_eff i, (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
              * ⟪IF_eff j, (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ)
          = ∑ l : Fin (Module.finrank ℝ ↥(V m)),
              ⟪(p m i : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
                * ⟪(p m j : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [h_swap_g i l, h_swap_g j l]
    rw [h_sum_rewrite]
    -- Step 2.3: apply Parseval (OrthonormalBasis.sum_inner_mul_inner) on V m.
    -- Lift `p m i, p m j` into V m via `⟨p m i, _⟩, ⟨p m j, _⟩`.
    have hp_i_in : (p m i : ↥(L2ZeroMean P)) ∈ V m := by
      change (V m).starProjection (IF_eff i) ∈ V m
      exact (V m).starProjection_apply_mem (IF_eff i)
    have hp_j_in : (p m j : ↥(L2ZeroMean P)) ∈ V m := by
      change (V m).starProjection (IF_eff j) ∈ V m
      exact (V m).starProjection_apply_mem (IF_eff j)
    let qi : ↥(V m) := ⟨p m i, hp_i_in⟩
    let qj : ↥(V m) := ⟨p m j, hp_j_in⟩
    -- `⟪qi, b l⟫_{V m} = ⟪p m i, g_l⟫_{L²}` and same for j.
    have h_inner_lift_i : ∀ l : Fin (Module.finrank ℝ ↥(V m)),
        ⟪(p m i : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪qi, b l⟫_ℝ := by intro l; rfl
    have h_inner_lift_j : ∀ l : Fin (Module.finrank ℝ ↥(V m)),
        ⟪(p m j : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪qj, b l⟫_ℝ := by intro l; rfl
    -- Apply Parseval: `Σ_l ⟪qi, b l⟫ * ⟪b l, qj⟫ = ⟪qi, qj⟫`.
    have h_parseval := b.sum_inner_mul_inner qi qj
    -- Rewrite ⟪qi, qj⟫_{V m} = ⟪p m i, p m j⟫_{L²}.
    have h_final_inner : ⟪qi, qj⟫_ℝ = ⟪(p m i : ↥(L2ZeroMean P)), p m j⟫_ℝ := rfl
    rw [show
        (∑ l, ⟪(p m i : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
              * ⟪(p m j : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ)
        = ∑ l, ⟪qi, b l⟫_ℝ * ⟪b l, qj⟫_ℝ by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [h_inner_lift_i l]
      -- Need to swap `⟪p m j, g_l⟫ → ⟪b l, qj⟫`.
      have : ⟪(p m j : ↥(L2ZeroMean P)), (g_P_m l : ↥(L2ZeroMean P))⟫_ℝ
            = ⟪b l, qj⟫_ℝ := by
        rw [h_inner_lift_j l]
        exact real_inner_comm _ _
      rw [this]]
    rw [h_parseval, h_final_inner]
  choose n_m g_P_m h_orth_m h_in_m h_mat_eq using h_basis_data
  -- Step 3: per-`m` decomposition via `hRegular_vec`.
  have h_perM_decomp : ∀ m,
      ∃ M : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure M ∧
        L = MeasureTheory.Measure.conv
              (ProbabilityTheory.multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin k))
                (ψDotMat_vec (g_P_m m) IF_eff *
                  (1 : Matrix (Fin (n_m m)) (Fin (n_m m)) ℝ)⁻¹ *
                  (ψDotMat_vec (g_P_m m) IF_eff).transpose))
              M := fun m =>
    hRegular_vec (g_P_m m) (h_orth_m m) (h_in_m m)
  choose M_m hM_prob hM_decomp using h_perM_decomp
  -- Step 4: build the per-`m` matrix `Σ_m` and its convergence to `G`.
  let Sigma_m : ℕ → Matrix (Fin k) (Fin k) ℝ := fun m =>
    ψDotMat_vec (g_P_m m) IF_eff *
      (1 : Matrix (Fin (n_m m)) (Fin (n_m m)) ℝ)⁻¹ *
      (ψDotMat_vec (g_P_m m) IF_eff).transpose
  -- PSD for each `Σ_m`: `B * 1 * B^T = B * B^T = B * B.conjTranspose` (TrivialStar on ℝ).
  have hSigma_psd : ∀ m, (Sigma_m m).PosSemidef := by
    intro m
    change (ψDotMat_vec (g_P_m m) IF_eff *
            (1 : Matrix (Fin (n_m m)) (Fin (n_m m)) ℝ)⁻¹ *
            (ψDotMat_vec (g_P_m m) IF_eff).transpose).PosSemidef
    rw [inv_one, Matrix.mul_one]
    rw [show (ψDotMat_vec (g_P_m m) IF_eff).transpose
          = (ψDotMat_vec (g_P_m m) IF_eff).conjTranspose from
        (Matrix.conjTranspose_eq_transpose_of_trivial _).symm]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  -- Gram matrix `G` PSD: same way, `G = ψ_eff * 1 * ψ_eff.T` with ψ_eff being the "matrix"
  -- of inner products of IF_eff with itself, BUT here `G_{ij} = ⟪IF_eff i, IF_eff j⟫`.
  -- We can show `G.PosSemidef` directly via `G = M * M^T` with `M = ψDotMat_vec g_P IF_eff`
  -- for some basis spanning span(IF_eff), but it's simpler to use `Matrix.PosSemidef`
  -- characterization via `IsHermitian + quadratic form ≥ 0`.
  -- Cleaner: just use that the Gram matrix of inner products is automatically PSD.
  -- Proof via `Σ_m → G` and PSD is closed: since each `Σ_m` is PSD and PSD set is closed.
  -- Actually it's easier to show G PSD directly; let's prove via the quadratic form.
  have hG_psd : G.PosSemidef := by
    rw [Matrix.PosSemidef_iff_quadratic_form_nonneg (Matrix.isHermitian_gram ℝ IF_eff)]
    intro x
    -- `x^* G x = Σ_{i,j} x_i G_{ij} x_j = Σ_{i,j} x_i ⟪IF_i, IF_j⟫ x_j = ‖Σ_j x_j • IF_j‖² ≥ 0`.
    have h_quad := eif_linear_combo_norm_sq (tangentSpace T_set) hψ.derivative hEIF x
    -- h_quad: ‖Σⱼ x j • IF_eff j‖² = dotProduct (star x) ((Matrix.gram ℝ IF_eff).mulVec x)
    -- We need: 0 ≤ dotProduct (star x) (G.mulVec x) where G = Matrix.gram ℝ IF_eff.
    change 0 ≤ dotProduct (star x) (G.mulVec x)
    rw [show G = Matrix.gram ℝ IF_eff from rfl, ← h_quad]
    exact sq_nonneg _
  -- Convergence `Σ_m → G` entrywise (i.e. as `(Fin k → Fin k → ℝ)`, hence as a matrix
  -- via the `Pi` topology which is the matrix topology by `Matrix.topologicalSpace`).
  have hSigma_tendsto : Tendsto Sigma_m atTop (𝓝 G) := by
    -- Reduce to entrywise convergence via `tendsto_pi_nhds` (twice — Matrix is `n → n → α`).
    -- Strategy: rewrite `Σ_m i j = ⟪p m i, p m j⟫` (via `h_mat_eq`) and conclude
    -- `→ ⟪IF_eff i, IF_eff j⟫ = G_{ij}` from continuity of inner product on H × H
    -- and `p m i → IF_eff i`.
    have h_entry_tendsto : ∀ i j : Fin k,
        Tendsto (fun m => (Sigma_m m) i j) atTop (𝓝 (G i j)) := by
      intro i j
      have h_entry : ∀ m, (Sigma_m m) i j = ⟪(p m i : ↥(L2ZeroMean P)), p m j⟫_ℝ :=
        fun m => h_mat_eq m i j
      have hG_entry : G i j = ⟪(IF_eff i : ↥(L2ZeroMean P)), IF_eff j⟫_ℝ := rfl
      have hp_i_tendsto : Tendsto (fun m => (p m i : ↥(L2ZeroMean P))) atTop
          (𝓝 (IF_eff i)) :=
        tendsto_iff_norm_sub_tendsto_zero.mpr (hp_tendsto i)
      have hp_j_tendsto : Tendsto (fun m => (p m j : ↥(L2ZeroMean P))) atTop
          (𝓝 (IF_eff j)) :=
        tendsto_iff_norm_sub_tendsto_zero.mpr (hp_tendsto j)
      have h_inner_tendsto :
          Tendsto (fun m => ⟪(p m i : ↥(L2ZeroMean P)), p m j⟫_ℝ) atTop
            (𝓝 (⟪(IF_eff i : ↥(L2ZeroMean P)), IF_eff j⟫_ℝ)) := by
        have h_cont : Continuous (fun pq : (↥(L2ZeroMean P)) × (↥(L2ZeroMean P)) =>
            @inner ℝ _ _ pq.1 pq.2) := continuous_inner
        exact h_cont.tendsto _ |>.comp (hp_i_tendsto.prodMk_nhds hp_j_tendsto)
      have h_funeq : (fun m => (Sigma_m m) i j)
          = (fun m => ⟪(p m i : ↥(L2ZeroMean P)), p m j⟫_ℝ) := by
        funext m; exact h_entry m
      rw [h_funeq, hG_entry]
      exact h_inner_tendsto
    -- Lift entrywise convergence to matrix convergence using `continuous_apply_apply`.
    refine tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => ?_))
    exact h_entry_tendsto i j
  -- Step 5: apply `levyMpass_vec` to get the final convolution decomposition.
  haveI hM_prob_inst : ∀ m, IsProbabilityMeasure (M_m m) := hM_prob
  -- Rewrite `Measure.conv` notation to `∗` for `levyMpass_vec`.
  have hM_decomp' : ∀ m,
      L = (ProbabilityTheory.multivariateGaussian
              (0 : EuclideanSpace ℝ (Fin k)) (Sigma_m m)) ∗ (M_m m) := hM_decomp
  exact AsymptoticStatistics.ForMathlib.LevyMpassVec.levyMpass_vec
    L M_m Sigma_m hSigma_psd G hG_psd hM_decomp' hSigma_tendsto

/-- **Theorem 25.20: vector convolution theorem (combined `(a) ∧ (b)` package, vec form).**

Combined-form `(a) ∧ (b)` package for vector-valued functionals and efficient
influence function tuples. Mirrors the scalar version `semiparametric_convolution_theorem` but
with vector codomain.

This delegates trivially to the per-clause forms:
- `semiparametric_convolution_theorem_vec_clause_a` for the variance bound
- `semiparametric_convolution_theorem_vec_clause_b` for the convolution decomposition
-/
theorem semiparametric_convolution_theorem_vec
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_vec P T_set ψ hψ hEIF T_n L)
    (hL_memLp : MemLp (id : EuclideanSpace ℝ (Fin k) → _) 2 L) :
    let G : Matrix (Fin k) (Fin k) ℝ := Matrix.gram ℝ IF_eff
    let Sigma : Matrix (Fin k) (Fin k) ℝ := fun i j =>
      ∫ y, (y.ofLp i - ∫ z, z.ofLp i ∂L)
          * (y.ofLp j - ∫ z, z.ofLp j ∂L) ∂L
    (Sigma - G).PosSemidef ∧
    (∃ M : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure M ∧
      L = (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) G) ∗ M) := by
  intro G Sigma
  exact ⟨semiparametric_convolution_theorem_vec_clause_a hψ hEIF T_n hT_meas L hReg hL_memLp,
         semiparametric_convolution_theorem_vec_clause_b hψ hEIF T_n hT_meas L hReg⟩

end AsymptoticStatistics.LowerBounds.ConvolutionVec
