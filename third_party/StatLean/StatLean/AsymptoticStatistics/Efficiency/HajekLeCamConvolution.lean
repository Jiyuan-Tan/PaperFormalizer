module
public import StatLean.AsymptoticStatistics.Efficiency.LowerBoundForExperiments
public import StatLean.AsymptoticStatistics.Experiment.GaussianShiftConvolution
public import StatLean.AsymptoticStatistics.ParametricFamily.RegularEstimator
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Hájek–Le Cam Convolution Theorem (parametric)

Consider a parametric experiment $(P_\theta : \theta \in \Theta)$ that is differentiable
in quadratic mean at $\theta_0$ with non-singular Fisher information matrix $I_{\theta_0}$,
and a parameter of interest $\psi : \Theta \to \mathbb{R}^d$ that is (Fréchet-)differentiable
at $\theta_0$ with derivative $\dot\psi_{\theta_0}$. Let $T_n$ be a *regular* estimator
sequence for $\psi(\theta)$ at $\theta_0$: for every local direction $h$,
$$\sqrt{n}\bigl(T_n - \psi(\theta_0 + h/\sqrt{n})\bigr) \rightsquigarrow L_{\theta_0}$$
under $P_{\theta_0+h/\sqrt n}^{\,n}$, with a limit law $L_{\theta_0}$ that does **not** depend
on $h$.

**Convolution theorem.** There exists a probability measure $M_{\theta_0}$ on
$\mathbb{R}^d$ such that the regular limit law factors as a fixed Gaussian convolved with
$M_{\theta_0}$:
$$L_{\theta_0} = N\!\bigl(0,\ \dot\psi_{\theta_0}\, I_{\theta_0}^{-1}\, \dot\psi_{\theta_0}^{\mathsf T}\bigr) * M_{\theta_0}.$$
The Gaussian factor $N(0, \dot\psi_{\theta_0} I_{\theta_0}^{-1} \dot\psi_{\theta_0}^{\mathsf T})$
is the smallest possible limit law in the concentration ordering; it is the best regular
estimator's law.

**Covariance corollary.** If, in addition, the limit law $L_{\theta_0}$ has a finite second
moment with covariance matrix $\Sigma_{\theta_0}$, then
$$\Sigma_{\theta_0} - \dot\psi_{\theta_0}\, I_{\theta_0}^{-1}\, \dot\psi_{\theta_0}^{\mathsf T}$$
is positive semidefinite. This is the asymptotic analogue of the Cramér–Rao lower bound:
no regular estimator can have asymptotic covariance smaller than the inverse Fisher
information bound $\dot\psi_{\theta_0} I_{\theta_0}^{-1} \dot\psi_{\theta_0}^{\mathsf T}$.

*Lean-specific deviations.* The book's $\dot\psi_{\theta_0}$ appears both as a continuous
linear map (`ψDot`) and as its matrix `ψDotMat`; the two are tied by the hypothesis
`h_ψDot_mat`, which the book leaves prose-implicit. The covariance corollary takes the
finite-second-moment hypothesis (`MemLp 2`) and the covariance matrix `Σ_θ` (specified
through its bilinear form) as explicit inputs — without them the covariance is undefined,
so the PSD statement would be vacuous; this is the only addition over the main theorem's
signature.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 8
(Efficiency of Estimators), §8.5 (Convolution Theorem), Theorem 8.8 (Convolution); the
covariance corollary is the closing "In particular …" clause of Theorem 8.8, and the
equivariant-in-law characterization used in the proof is Eq (8.7).

**Proof formalization notes.** This file proves the convolution theorem
`hajek_le_cam_convolution_theorem` and the covariance corollary
`cov_psd_of_regular_estimator`. The proof follows the book's three-step reduction:

* *Step A* (`regularity_implies_8_2_hypothesis`): translate the regularity hypothesis into
  the weak-convergence input (8.2) required by `lower_bound_for_experiments`, feeding it the
  constant $h$-indexed family `fun _ => hReg.limitDist` (regularity says $L_{\theta,h}$ is
  independent of $h$).
* *Step B* (`randomized_kernel_is_equivariant_in_law`): the Markov kernel $\kappa$ produced
  by `lower_bound_for_experiments` is an equivariant-in-law estimator of $\dot\psi_{\theta_0} h$
  in the limit Gaussian-shift experiment $(N(h, I^{-1}) : h \in \mathbb{R}^k)$ — this is the
  book's Theorem 8.3 + the property (8.7).
* *Step C*: apply `equivariant_in_law_convolution_decomposition` (the convolution structure
  of equivariant-in-law laws, vdV Proposition 8.4) with $A := \dot\psi_{\theta_0}$ matrix and
  $\Sigma := I_{\theta_0}^{-1}$ to obtain the decomposition; identifying the null distribution
  with `hReg.limitDist` (Step B at $h=0$) gives the stated factorization.

The covariance corollary is the helper `cov_psd_from_conv_decomp`: variance is additive for
independent sums, the multivariate Gaussian with covariance $V$ has covariance $V$, and any
probability-measure covariance matrix is PSD, so $\Sigma_{\theta_0} = V + \mathrm{Cov}(M_{\theta_0})$
with $\mathrm{Cov}(M_{\theta_0}) \succeq 0$.

**Bibliographic comments.** The convolution theorem originates with J. Hájek, "A
characterization of limiting distributions of regular estimates", *Zeitschrift für
Wahrscheinlichkeitstheorie und verwandte Gebiete* **14** (1970), 323–330, which proves
(its Theorem) that the limiting law of any regular estimator in a locally asymptotically
normal family is a convolution of the optimal Gaussian with a residual measure. An
essentially equivalent result was obtained independently by N. Inagaki, "On the limiting
distribution of a sequence of estimators with uniformity property", *Annals of the
Institute of Statistical Mathematics* **22** (1970), 1–13. The underlying local-asymptotic
framework and an early form of the lower bound are due to L. Le Cam, "On some asymptotic
properties of maximum likelihood estimates and related Bayes' estimates", *University of
California Publications in Statistics* **1** (1953), 277–330 (hence the "Hájek–Le Cam"
attribution); van der Vaart's Theorem 8.8 is the textbook synthesis of these results.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace AsymptoticStatistics
namespace HajekLeCamConvolution

variable {k d : ℕ}
variable {𝓧 : Type*} [MeasurableSpace 𝓧]

open AsymptoticRepresentation (Θ 𝓨 productMeasure productMeasure_isProbabilityMeasure)
open AsymptoticStatistics.EquivariantInLaw
open AsymptoticStatistics.GaussianShiftConvolution
open AsymptoticStatistics.ParametricFamily

/-! ## Step A — local glue: regularity → (8.2) hypothesis shape -/

/-- **Regularity supplies the (8.2) weak-convergence input** (vdV §8.5 local glue): a
`RegularEstimatorSequence M μ θ₀ ψ T` provides the `(8.2)` weak-convergence
input shape that `lower_bound_for_experiments` requires, with the `h`-indexed family of limit
laws `L_θh` chosen as the constant family `fun _ => hReg.limitDist`.

vdV's regularity hypothesis says the limit `L_θ` is
independent of `h`, so feeding `(8.2)` with the constant family is exactly
the unfolding. -/
theorem regularity_implies_8_2_hypothesis
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k)
    (ψ : Θ k → 𝓨 d)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d)
    (hReg : RegularEstimatorSequence M μ θ₀ ψ T) :
    ∀ h : Θ k,
      WeakConverges
        (fun n : ℕ =>
          (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map
            (fun x => (Real.sqrt n) •
              (T n x - ψ (θ₀ + (Real.sqrt n)⁻¹ • h))))
        hReg.limitDist :=
  hReg.tendsto

/-! ## Step B — local glue: the 8.3-produced kernel is equivariant-in-law -/

/-- **The 8.3-produced kernel is equivariant-in-law** (vdV §8.5 local glue): given the Markov kernel
`κ : Kernel ℝᵏ ℝᵈ` produced by `lower_bound_for_experiments` together with the regularity
hypothesis (so the per-`h` limit `L_θh h = hReg.limitDist` is constant in
`h`), the kernel `κ` is an equivariant-in-law estimator of `A·h` in the
limit Gaussian-shift experiment `(N(h, J⁻¹) : h ∈ ℝᵏ)`, where
`A := ψ̇_{θ₀}` (in its matrix form `ψDotMat`) and the null distribution is
`hReg.limitDist`.

vdV §8.5: *"`L_θ` is the distribution of an equivariant-in-
law estimator `T` in the limit experiment."*

Proof sketch: `lower_bound_for_experiments`'s conclusion is `L_θh h = (N(h, J⁻¹) ⊗ κ).map
(· − ψ̇h)`. Under regularity (`L_θh h = hReg.limitDist` for every `h`), this
gives `(N(h, J⁻¹) ⊗ κ).map (· − ψ̇h) = hReg.limitDist` for every `h`, which
is exactly the `IsEquivariantInLaw κ ψDotMat J⁻¹` defining clause. -/
theorem randomized_kernel_is_equivariant_in_law
    (J : Matrix (Fin k) (Fin k) ℝ) (_hJ_pd : Matrix.PosDef J)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    -- vdV §8.5 prose-implicit (writes `ψ̇` as both linear map and matrix).
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    {L_θ : Measure (𝓨 d)} [IsProbabilityMeasure L_θ]
    (κ : Kernel (Θ k) (𝓨 d)) [IsMarkovKernel κ]
    -- Conclusion of `lower_bound_for_experiments` specialised to the regularity-constant
    -- limit family `L_θh ≡ L_θ`.
    (hκ : ∀ h : Θ k,
      L_θ =
        (((ProbabilityTheory.multivariateGaussian h J⁻¹).bind κ)).map
          (fun y : 𝓨 d => y - ψDot h)) :
    IsEquivariantInLaw κ ψDotMat J⁻¹ := by
  refine ⟨⟨L_θ, inferInstance, ?_⟩⟩
  intro h
  -- `κ ∘ₘ μ` unfolds to `Measure.bind μ κ`; rewrite ψDot via h_ψDot_mat.
  have hκh := hκ h
  -- Goal: (κ ∘ₘ multivariateGaussian h J⁻¹).map (· - ψDotMat·h) = L_θ
  -- hκh:  L_θ = (multivariateGaussian h J⁻¹).bind κ).map (· - ψDot h)
  rw [hκh]
  congr 1
  funext y
  rw [h_ψDot_mat h]

/-! ## Main theorem — vdV §8.5 Theorem 8.8 -/

/-- **vdV §8.5 Theorem 8.8 — Convolution Theorem.**

Assume the experiment `(P_θ : θ ∈ Θ)` is DQM at `θ₀` with non-singular
Fisher information `J`. Let `ψ : Θ → ℝᵈ` be Fréchet-differentiable at `θ₀`
with derivative `ψ̇`. Let `T_n` be a regular estimator sequence for `ψ(θ)`
with limit distribution `L_θ` (via `RegularEstimatorSequence`).

Then there exists a probability measure `M_θ` such that

    L_θ = N(0, ψ̇·J⁻¹·ψ̇ᵀ) ∗ M_θ.

Proof: Apply Step A (regularity → (8.2)) then `lower_bound_for_experiments` to get a Markov
kernel `κ`; apply Step B to get `IsEquivariantInLaw κ
ψDotMat J⁻¹`; apply `equivariant_in_law_convolution_decomposition` to get the
convolution decomposition with `A := ψDotMat` and `Σ := J⁻¹`. The null
distribution of the equivariant-in-law witness equals `hReg.limitDist`
by construction (Step B). ∎ -/
theorem hajek_le_cam_convolution_theorem
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d) (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_diff : HasFDerivAt ψ ψDot θ₀)
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (hReg : RegularEstimatorSequence M μ θ₀ ψ T)
    (hPDF : IsPDFOf M μ) :
    ∃ M_θ : Measure (𝓨 d),
      IsProbabilityMeasure M_θ ∧
      hReg.limitDist =
        (ProbabilityTheory.multivariateGaussian (0 : 𝓨 d)
          (ψDotMat * J⁻¹ * ψDotMat.transpose)) ∗ M_θ := by
  classical
  -- Step A: translate regularity → (8.2), then apply lower_bound_for_experiments to get κ.
  have hT_weak := regularity_implies_8_2_hypothesis M μ θ₀ ψ T hReg
  -- The constant family L_θh ≡ hReg.limitDist; instance provided by hReg.isProb.
  obtain ⟨κ, hκ_markov, hκ⟩ :=
    LowerBoundForExperiments.lower_bound_for_experiments M μ θ₀ ℓ hℓ hDQM J hJ_pd hJ_fisher ψ ψDot
        hψ_diff
      T hT_meas (L_θh := fun _ => hReg.limitDist) hT_weak hPDF
  -- Step B: build the IsEquivariantInLaw witness.
  haveI := hκ_markov
  have hEquiv :=
    randomized_kernel_is_equivariant_in_law (k := k) (d := d)
      J hJ_pd ψDot ψDotMat h_ψDot_mat (L_θ := hReg.limitDist) κ hκ
  -- Step C: apply equivariant_in_law_convolution_decomposition.
  obtain ⟨M_θ, hM_prob, hM_conv⟩ :=
    equivariant_in_law_convolution_decomposition (S := J⁻¹) hJ_pd.inv ψDotMat κ hEquiv
  refine ⟨M_θ, hM_prob, ?_⟩
  -- Goal: hReg.limitDist = multivariateGaussian 0 (ψDotMat * J⁻¹ * ψDotMatᵀ) ∗ M_θ.
  -- hM_conv: hEquiv.nullDist = multivariateGaussian 0 (ψDotMat * J⁻¹ * ψDotMatᵀ) ∗ M_θ.
  -- Need: hReg.limitDist = hEquiv.nullDist. Use map_sub_eq_nullDist at h = 0.
  have h_nullDist : hReg.limitDist = hEquiv.nullDist := by
    have h0 := IsEquivariantInLaw.map_sub_eq_nullDist hEquiv 0
    -- h0: (κ ∘ₘ multivariateGaussian 0 J⁻¹).map (· - (...mulVec 0)) = hEquiv.nullDist
    have hκ0 := hκ 0
    -- hκ0: hReg.limitDist = ((multivariateGaussian 0 J⁻¹).bind κ).map (· - ψDot 0)
    -- Convert hκ0's map function to match h0's map function.
    have h_map_eq :
        (fun y : 𝓨 d => y - ψDot 0)
          = (fun y : 𝓨 d => y - (WithLp.equiv 2 (Fin d → ℝ)).symm
              (ψDotMat.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) 0))) := by
      funext y; rw [h_ψDot_mat 0]
    rw [hκ0, h_map_eq]
    -- κ ∘ₘ μ and μ.bind κ are definitionally equal.
    exact h0
  rw [h_nullDist]
  exact hM_conv

/-! ## Helper for the corollary -/

/-- **Convolution covariance gap is PSD.**

If a probability measure `L` on `ℝᵈ` decomposes as the convolution
`multivariateGaussian 0 V ∗ N` for some probability measure `N` and PSD matrix
`V`, and `L` has finite second moment with covariance matrix `Σ` (specified
through bilinear forms via `h_Sigma_isCov`), then `Σ − V` is positive
semidefinite.

This is the standard measure-theoretic fact: variance is additive for
independent sums, the multivariate Gaussian on `ℝᵈ` with covariance matrix `V`
has covariance `V`, and any probability-measure covariance matrix is PSD. -/
theorem cov_psd_from_conv_decomp
    {d : ℕ}
    (V : Matrix (Fin d) (Fin d) ℝ) (hV_psd : V.PosSemidef)
    (L : Measure (𝓨 d)) [IsProbabilityMeasure L]
    (hL_memLp : MemLp (fun y : 𝓨 d => y) 2 L)
    (Sigma : Matrix (Fin d) (Fin d) ℝ)
    (h_Sigma_isCov : ∀ u v : 𝓨 d,
      ∫ y, ⟪u, y⟫ * ⟪v, y⟫ ∂L
        - (∫ y, ⟪u, y⟫ ∂L) * (∫ y, ⟪v, y⟫ ∂L)
        = ⟪u, (WithLp.equiv 2 _).symm (Sigma.mulVec ((WithLp.equiv 2 _) v))⟫)
    (N : Measure (𝓨 d)) [IsProbabilityMeasure N]
    (h_conv : L =
      (ProbabilityTheory.multivariateGaussian (0 : 𝓨 d) V) ∗ N) :
    (Sigma - V).PosSemidef := by
  classical
  -- Abbreviation: G is the multivariate Gaussian; haveI's for instance lookup.
  set G : Measure (𝓨 d) := ProbabilityTheory.multivariateGaussian (0 : 𝓨 d) V with hG_def
  haveI : IsProbabilityMeasure G := inferInstance
  haveI : IsGaussian G := inferInstance
  -- Inner-product bridge: `⟪u_lift x, w_lift⟫ = x ⬝ᵥ w` over ℝ, where
  -- `u_lift x := (WithLp.equiv 2 _).symm x`.
  have inner_bridge : ∀ x w : Fin d → ℝ,
      (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm x,
          (WithLp.equiv 2 (Fin d → ℝ)).symm w⟫ : ℝ) = x ⬝ᵥ w := by
    intro x w
    rw [show (x ⬝ᵥ w) = ∑ i, x i * w i from rfl]
    simp only [PiLp.inner_apply, WithLp.equiv_symm_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- Over ℝ, `⟪a, b⟫ = b * a` (via `RCLike.inner_apply`); flip to `a * b`.
    change (WithLp.toLp 2 w) i * (WithLp.toLp 2 x) i = x i * w i
    ring
  -- For any `u : 𝓨 d`, `fun y => ⟪u, y⟫` is `MemLp 2` under L (via CLM comp).
  have hLp_inner : ∀ u : 𝓨 d, MemLp (fun y => (⟪u, y⟫ : ℝ)) 2 L := by
    intro u
    have h := hL_memLp.continuousLinearMap_comp (innerSL ℝ u)
    simpa [innerSL_apply_apply] using h
  -- Step 1: Sigma is symmetric (Hermitian over ℝ).
  -- LHS of h_Sigma_isCov is symmetric in (u, v) by mul_comm; so the RHS
  -- bilinear form is symmetric; instantiated at standard basis vectors, this
  -- yields Sigma j i = Sigma i j.
  have h_lift_basis : ∀ a b : Fin d,
      (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single a (1 : ℝ)),
          (WithLp.equiv 2 (Fin d → ℝ)).symm
            (Sigma.mulVec (Pi.single b (1 : ℝ)))⟫ : ℝ) = Sigma a b := by
    intro a b
    rw [inner_bridge]
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']
  have hSigma_symm : ∀ i j : Fin d, Sigma i j = Sigma j i := by
    intro i j
    have hij := h_Sigma_isCov
      ((WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single i (1 : ℝ)))
      ((WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single j (1 : ℝ)))
    have hji := h_Sigma_isCov
      ((WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single j (1 : ℝ)))
      ((WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single i (1 : ℝ)))
    -- The integrand factors in (u, v) ↔ (v, u) are products, hence symmetric.
    have hLHS_eq : (∫ y, (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single i (1 : ℝ)), y⟫ : ℝ)
            * ⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single j (1 : ℝ)), y⟫ ∂L)
        = ∫ y, (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single j (1 : ℝ)), y⟫ : ℝ)
            * ⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single i (1 : ℝ)), y⟫ ∂L := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_)); ring
    have hLHS_swap : (∫ y, (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single i (1 : ℝ)), y⟫ : ℝ) ∂L)
        * (∫ y, (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single j (1 : ℝ)), y⟫ : ℝ) ∂L)
        = (∫ y, (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single j (1 : ℝ)), y⟫ : ℝ) ∂L)
          * (∫ y, (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm (Pi.single i (1 : ℝ)), y⟫ : ℝ) ∂L) := by
      ring
    -- Rewriting hij to the form of hji via these symmetries gives the equality.
    rw [hLHS_eq, hLHS_swap] at hij
    -- Now hij and hji have identical LHS, so RHSes are equal.
    have hRHS_eq := hij.symm.trans hji
    -- Cancel `(equiv) ((equiv).symm _) = _` so the RHS exposes
    -- `Sigma.mulVec (Pi.single _ 1)`, then apply `h_lift_basis`.
    simp only [Equiv.apply_symm_apply] at hRHS_eq
    rw [h_lift_basis, h_lift_basis] at hRHS_eq
    exact hRHS_eq
  have hSigma_Herm : Sigma.IsHermitian := by
    refine Matrix.IsHermitian.ext (fun i j => ?_)
    change star (Sigma j i) = Sigma i j
    rw [star_trivial, hSigma_symm]
  -- Step 2: the variance identity at u_x := (WithLp.equiv 2 _).symm x.
  -- Convolution: L = (G.prod N).map (fun p => p.1 + p.2).
  have hL_conv_map :
      L = (G.prod N).map (fun p : 𝓨 d × 𝓨 d => p.1 + p.2) := by
    rw [h_conv]; rfl
  -- Variance additivity at f_u(y) = ⟪u, y⟫.
  have hVar_add : ∀ u : 𝓨 d,
      Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); L]
        = Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); G]
          + Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); N] := by
    intro u
    have hLp_G : MemLp (fun y : 𝓨 d => (⟪u, y⟫ : ℝ)) 2 G := by
      have := (IsGaussian.memLp_two_id (μ := G)).continuousLinearMap_comp (innerSL ℝ u)
      simpa [innerSL_apply_apply] using this
    -- For N we don't have MemLp 2 directly, but variance is defined unconditionally;
    -- the additivity uses MemLp 2 on both sides of the product.  We split: first
    -- bridge the LHS to a sum on the product, then apply variance_add_prod.
    -- Case split: whether `fun y => ⟪u, y⟫` is MemLp 2 under N or not.
    -- If yes, use variance_add_prod directly.  If no, both sides are equal to
    -- variance under L's CLM-composed measure, which itself may not be MemLp 2 --
    -- but in our setup `hL_memLp` gives MemLp 2 of `id` under L, which implies
    -- MemLp 2 of `⟪u,·⟫` under L, hence (by convolution) MemLp 2 under both
    -- G and N (Lp comp with translation in product).
    -- Direct route via the convolution shape.
    have hmeas_add : Measurable (fun p : 𝓨 d × 𝓨 d => p.1 + p.2) := by fun_prop
    have hmeas_inner : Measurable (fun y : 𝓨 d => (⟪u, y⟫ : ℝ)) :=
      (innerSL ℝ u).continuous.measurable
    have h_map :
        Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); L]
          = Var[fun p : 𝓨 d × 𝓨 d => (⟪u, p.1⟫ : ℝ) + (⟪u, p.2⟫ : ℝ);
              G.prod N] := by
      rw [hL_conv_map]
      rw [variance_map hmeas_inner.aemeasurable hmeas_add.aemeasurable]
      refine variance_congr ?_
      refine Filter.Eventually.of_forall (fun p => ?_)
      simp [inner_add_right]
    rw [h_map]
    -- MemLp 2 of `fun y => ⟪u, y⟫` under N: transfer from L through the conv-map
    -- structure, then project to the second factor via `measurePreserving_snd`.
    have hLp_N : MemLp (fun y : 𝓨 d => (⟪u, y⟫ : ℝ)) 2 N := by
      have hL_inner : MemLp (fun y : 𝓨 d => (⟪u, y⟫ : ℝ)) 2 L := hLp_inner u
      rw [hL_conv_map] at hL_inner
      have hLp_prod_sum : MemLp
          (fun p : 𝓨 d × 𝓨 d => (⟪u, p.1 + p.2⟫ : ℝ)) 2 (G.prod N) := by
        rw [show (fun p : 𝓨 d × 𝓨 d => (⟪u, p.1 + p.2⟫ : ℝ))
              = (fun y : 𝓨 d => (⟪u, y⟫ : ℝ)) ∘ (fun p : 𝓨 d × 𝓨 d => p.1 + p.2) from rfl]
        exact (memLp_map_measure_iff hmeas_inner.aestronglyMeasurable
          hmeas_add.aemeasurable).mp hL_inner
      have hLp_prod_sum' : MemLp
          (fun p : 𝓨 d × 𝓨 d => (⟪u, p.1⟫ : ℝ) + (⟪u, p.2⟫ : ℝ)) 2 (G.prod N) := by
        refine MemLp.ae_eq ?_ hLp_prod_sum
        refine Filter.Eventually.of_forall (fun p => ?_)
        simp [inner_add_right]
      have hLp_prod_fst : MemLp (fun p : 𝓨 d × 𝓨 d => (⟪u, p.1⟫ : ℝ)) 2 (G.prod N) :=
        hLp_G.comp_fst N
      have hLp_prod_snd : MemLp (fun p : 𝓨 d × 𝓨 d => (⟪u, p.2⟫ : ℝ)) 2 (G.prod N) := by
        have h_sub := hLp_prod_sum'.sub hLp_prod_fst
        refine MemLp.ae_eq ?_ h_sub
        refine Filter.Eventually.of_forall (fun p => ?_)
        simp
      -- Project to N via measurePreserving_snd: N = (G.prod N).map Prod.snd.
      have hMP : MeasurePreserving (Prod.snd : 𝓨 d × 𝓨 d → 𝓨 d) (G.prod N) N :=
        measurePreserving_snd
      have hN_eq : N = (G.prod N).map Prod.snd := hMP.map_eq.symm
      rw [hN_eq]
      have h_rw : (fun y : 𝓨 d => (⟪u, y⟫ : ℝ)) ∘ Prod.snd
            = (fun p : 𝓨 d × 𝓨 d => (⟪u, p.2⟫ : ℝ)) := rfl
      exact (memLp_map_measure_iff hmeas_inner.aestronglyMeasurable
        measurable_snd.aemeasurable).mpr (h_rw ▸ hLp_prod_snd)
    -- Apply variance_add_prod directly.
    have hAddProd : Var[fun p : 𝓨 d × 𝓨 d => (⟪u, p.1⟫ : ℝ) + (⟪u, p.2⟫ : ℝ); G.prod N]
        = Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); G] + Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); N] :=
      variance_add_prod hLp_G hLp_N
    exact hAddProd
  -- Gaussian variance: Var[⟨u, ·⟩; G] = covarianceBilin G u u = u_ofLp ⬝ᵥ V *ᵥ u_ofLp.
  have hVar_G : ∀ u : 𝓨 d,
      Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); G]
        = u.ofLp ⬝ᵥ V.mulVec u.ofLp := by
    intro u
    have hLp_G : MemLp (fun y : 𝓨 d => (⟪u, y⟫ : ℝ)) 2 G := by
      have := (IsGaussian.memLp_two_id (μ := G)).continuousLinearMap_comp (innerSL ℝ u)
      simpa [innerSL_apply_apply] using this
    have hMemLp_id : MemLp (id : 𝓨 d → 𝓨 d) 2 G := IsGaussian.memLp_two_id
    -- covarianceBilin_self gives covarianceBilin G u u = Var[fun y => ⟪u, y⟫; G].
    have h_self : covarianceBilin G u u = Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); G] :=
      covarianceBilin_self hMemLp_id u
    -- covarianceBilin_multivariateGaussian gives the matrix form.
    have h_mat : covarianceBilin G u u = u ⬝ᵥ V.mulVec u :=
      covarianceBilin_multivariateGaussian hV_psd u u
    -- u ⬝ᵥ V.mulVec u for u : EuclideanSpace ℝ (Fin d) reduces to u.ofLp ⬝ᵥ V.mulVec u.ofLp
    -- by defeq (EuclideanSpace ℝ (Fin d) = WithLp 2 (Fin d → ℝ); ofLp = id).
    rw [← h_self]; exact h_mat
  -- L variance: Var[⟨u, ·⟩; L] = u.ofLp ⬝ᵥ Sigma *ᵥ u.ofLp.
  have hVar_L : ∀ u : 𝓨 d,
      Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); L]
        = u.ofLp ⬝ᵥ Sigma.mulVec u.ofLp := by
    intro u
    have hLp_inner_u : MemLp (fun y : 𝓨 d => (⟪u, y⟫ : ℝ)) 2 L := hLp_inner u
    have h_cov_eq : cov[fun y : 𝓨 d => (⟪u, y⟫ : ℝ), fun y : 𝓨 d => (⟪u, y⟫ : ℝ); L]
        = ∫ y, (⟪u, y⟫ : ℝ) * ⟪u, y⟫ ∂L
          - (∫ y, (⟪u, y⟫ : ℝ) ∂L) * (∫ y, (⟪u, y⟫ : ℝ) ∂L) :=
      covariance_eq_sub hLp_inner_u hLp_inner_u
    have h_self_cov := covariance_self (μ := L) hLp_inner_u.aemeasurable
    -- h_self_cov: cov[X, X; L] = Var[X; L]
    have h_eq := h_Sigma_isCov u u
    -- h_eq: ∫ ... * ... - ... = ⟪u, (WithLp.equiv 2 _).symm (Sigma.mulVec u)⟫.
    -- Use inner_bridge with x := u.ofLp, w := Sigma.mulVec u.ofLp.
    have h_bridge := inner_bridge u.ofLp (Sigma.mulVec u.ofLp)
    -- The hypothesis's RHS unfolds (defeq) to
    --   ⟪(equiv).symm u.ofLp, (equiv).symm (Sigma.mulVec u.ofLp)⟫.
    rw [← h_self_cov, h_cov_eq, h_eq]
    change (⟪(WithLp.equiv 2 (Fin d → ℝ)).symm u.ofLp,
              (WithLp.equiv 2 (Fin d → ℝ)).symm (Sigma.mulVec u.ofLp)⟫ : ℝ)
            = u.ofLp ⬝ᵥ Sigma.mulVec u.ofLp
    exact h_bridge
  -- Step 3: assemble.
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · -- (Sigma - V).IsHermitian.
    have hV_Herm : V.IsHermitian := hV_psd.isHermitian
    refine Matrix.IsHermitian.ext (fun i j => ?_)
    change star ((Sigma - V) j i) = (Sigma - V) i j
    rw [star_trivial]
    have hS_ij := hSigma_symm i j
    have hV_ij : V j i = V i j := by
      have := Matrix.IsHermitian.apply hV_Herm i j
      -- this : star (V j i) = V i j
      change star (V j i) = V i j at this
      rw [star_trivial] at this
      exact this
    simp [Matrix.sub_apply, hS_ij, hV_ij]
  · intro x
    -- Goal: 0 ≤ star x ⬝ᵥ (Sigma - V).mulVec x.
    have h_star : (star x : Fin d → ℝ) = x := by funext i; exact star_trivial _
    rw [h_star, Matrix.sub_mulVec, dotProduct_sub]
    -- Let u := (WithLp.equiv 2 _).symm x.  Then u.ofLp = x by defeq.
    set u : 𝓨 d := (WithLp.equiv 2 (Fin d → ℝ)).symm x with hu_def
    have h_ofLp : u.ofLp = x := rfl
    rw [show x ⬝ᵥ Sigma.mulVec x = u.ofLp ⬝ᵥ Sigma.mulVec u.ofLp from by rw [h_ofLp]]
    rw [show x ⬝ᵥ V.mulVec x = u.ofLp ⬝ᵥ V.mulVec u.ofLp from by rw [h_ofLp]]
    rw [← hVar_L u, ← hVar_G u, hVar_add u]
    -- Goal: 0 ≤ (Var G + Var N) - Var G = Var N
    have hVN : 0 ≤ Var[fun y : 𝓨 d => (⟪u, y⟫ : ℝ); N] := variance_nonneg _ _
    linarith

/-- **Corollary to vdV §8.5 Theorem 8.8 — PSD on limit covariance.**

If the regular limit law `L_θ` has finite second moment with covariance
matrix `Σ_θ`, then `Σ_θ − ψ̇·J⁻¹·ψ̇ᵀ` is positive semidefinite.

Proof: variance is additive for independent sums, so
`Σ_θ = ψ̇·J⁻¹·ψ̇ᵀ + Cov(M_θ)`, and `Cov(M_θ) ⪰ 0`. ∎

The `MemLp 2` (finite second-moment) hypothesis is the only addition above
the main theorem's signature; without it the covariance `Σ_θ` is undefined. -/
theorem cov_psd_of_regular_estimator
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d) (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_diff : HasFDerivAt ψ ψDot θ₀)
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (hReg : RegularEstimatorSequence M μ θ₀ ψ T)
    -- vdV §8.5 corollary clause implicitly assumes this; without it the
    -- covariance `Σ_θ` is undefined and the PSD statement is vacuous.
    (hL_memLp : MemLp (fun y : 𝓨 d => y) 2 hReg.limitDist)
    -- matrix form is a Lean-side choice (Mathlib's covariance API).
    (Sigmaθ : Matrix (Fin d) (Fin d) ℝ)
    (hSigmaθ_isCov : ∀ u v : 𝓨 d,
      ∫ y, ⟪u, y⟫ * ⟪v, y⟫ ∂hReg.limitDist
        - (∫ y, ⟪u, y⟫ ∂hReg.limitDist) * (∫ y, ⟪v, y⟫ ∂hReg.limitDist)
        = ⟪u, (WithLp.equiv 2 _).symm (Sigmaθ.mulVec ((WithLp.equiv 2 _) v))⟫)
    (hPDF : IsPDFOf M μ) :
    (Sigmaθ - ψDotMat * J⁻¹ * ψDotMat.transpose).PosSemidef := by
  classical
  -- Step 1: apply the convolution theorem to obtain the M_θ decomposition.
  obtain ⟨M_θ, hM_prob, hM_conv⟩ :=
    hajek_le_cam_convolution_theorem (k := k) (d := d) M μ θ₀ ℓ hℓ hDQM J hJ_pd
      hJ_fisher ψ ψDot hψ_diff ψDotMat h_ψDot_mat T hT_meas hReg hPDF
  haveI := hM_prob
  haveI := hReg.isProb
  -- Step 2: ψDotMat * J⁻¹ * ψDotMatᵀ is PSD.
  have hV_psd : (ψDotMat * J⁻¹ * ψDotMat.transpose).PosSemidef := by
    -- (B * A * Bᵀ).PosSemidef for A = J⁻¹ PSD, B = ψDotMat.
    have hJ_inv_psd : (J⁻¹).PosSemidef := hJ_pd.inv.posSemidef
    have h := Matrix.PosSemidef.mul_mul_conjTranspose_same hJ_inv_psd ψDotMat
    -- ℝ matrices: conjTranspose = transpose.
    have h_eq : (ψDotMat.conjTranspose : Matrix (Fin k) (Fin d) ℝ)
        = ψDotMat.transpose := by
      ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    rw [h_eq] at h
    exact h
  -- Step 3: apply the helper lemma.
  exact cov_psd_from_conv_decomp (d := d)
    (ψDotMat * J⁻¹ * ψDotMat.transpose) hV_psd
    hReg.limitDist hL_memLp Sigmaθ hSigmaθ_isCov M_θ hM_conv

end HajekLeCamConvolution
end AsymptoticStatistics
