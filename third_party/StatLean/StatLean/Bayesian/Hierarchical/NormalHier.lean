module
public import StatLean.Bayesian.Conjugacy.NormalNormal
public import StatLean.Bayesian.ForMathlib.PiKernel

@[expose] public section

/-!
# The normal one-way hierarchy and partial pooling

The canonical hierarchical normal model `Y_j ∣ θ_j ∼ N(θ_j, σ²)`, `θ_j ∣ μ, τ² ∼ N(μ, τ²)`. Given
the hyperparameters, the group means have independent scalar Normal–Normal posteriors, whose mean
is a **convex combination** `(1−B)·y_j + B·μ` of the observation and the grand mean with shrinkage
weight `B = σ²/(σ²+τ²)` (partial pooling), and whose variance is strictly below the sampling
variance. Integrating out the group means, the data are i.i.d. `N(μ, σ²+τ²)`, so the
hyperparameter `μ` itself has a Normal–Normal posterior with `J` observations.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §5.4 (normal
one-way hierarchy), p. 113; §5.5 (eight schools), p. 119.

**Proof formalization notes.** Every coupling reuses the Batch-2 `Conjugacy.NormalNormal` API: the
per-group posterior (`normal_normal_posterior_ae` at `n = 1`), the μ-posterior (the same at
`n = J`, noise variance `σ²+τ²`), and the marginal (`comp_gaussKernel_gaussianReal` per coordinate,
assembled with the diagonal product kernel `diagKernel`). The convex-combination mean and
`postVar < σ²` are scalar `postMean`/`postVar` real algebra (`field_simp`; `ht₀`, `hv` for the
nonzero denominators). No new posterior machinery is introduced.

**Bibliographic comments.** Partial pooling and shrinkage of group means toward a grand mean are
the content of C. Stein's estimator (1956) read hierarchically, and of the empirical-Bayes analysis
of D. V. Lindley and A. F. M. Smith (1972) and B. Efron and C. Morris ("Stein's estimation rule and
its competitors—an empirical Bayes approach," *J. Amer. Statist. Assoc.* 68 (1973), 117–130).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- The **shrinkage weight** `B = σ²/(σ²+τ²)` of the normal hierarchy (Gelman §5.4). -/
noncomputable def shrinkageWeight (σ2 τ2 : ℝ≥0) : ℝ := (σ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))

/-- The shrinkage weight lies in `[0, 1]` (3C.3). -/
theorem shrinkageWeight_mem_Icc (σ2 τ2 : ℝ≥0) : shrinkageWeight σ2 τ2 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [shrinkageWeight, Set.mem_Icc]
  refine ⟨div_nonneg (NNReal.coe_nonneg _)
      (add_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)), ?_⟩
  exact div_le_one_of_le₀ (le_add_of_nonneg_right (NNReal.coe_nonneg _))
    (add_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

/-- **Partial pooling** (3C.3): the per-group posterior mean is the convex combination
`(1−B)·y + B·μ` of the observation and the prior (grand) mean (Gelman §5.4). -/
theorem normalHier_posteriorMean_convexCombination (μ : ℝ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate prior and noise variances; Gelman §5.4
    (hτ : τ2 ≠ 0) (hσ : σ2 ≠ 0) (y : ℝ) :
    postMean μ τ2 σ2 (fun _ : Fin 1 => y)
      = (1 - shrinkageWeight σ2 τ2) * y + shrinkageWeight σ2 τ2 * μ := by
  have ha : (τ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hτ
  have hb : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hσ
  have hbpos : (0 : ℝ) < (σ2 : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ)
  have hab : (σ2 : ℝ) + (τ2 : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hbpos (le_add_of_nonneg_right (NNReal.coe_nonneg _)))
  rw [shrinkageWeight]
  simp only [postMean, postVar, Fin.sum_univ_one, Nat.cast_one, one_mul]
  push_cast
  field_simp
  ring

/-- **Variance reduction** (3C.4): the per-group posterior variance is strictly below the sampling
variance (Gelman §5.4). -/
theorem normalHier_posteriorVar_lt_samplingVar (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate prior and noise variances; Gelman §5.4
    (hτ : τ2 ≠ 0) (hσ : σ2 ≠ 0) :
    (postVar τ2 σ2 1 : ℝ) < (σ2 : ℝ) := by
  have ha : (0 : ℝ) < (τ2 : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hτ)
  have hb : (0 : ℝ) < (σ2 : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ)
  simp only [postVar, Nat.cast_one, one_mul, NNReal.coe_inv, NNReal.coe_add]
  have key : ((τ2 : ℝ)⁻¹ + (σ2 : ℝ)⁻¹)⁻¹ = (τ2 : ℝ) * (σ2 : ℝ) / ((τ2 : ℝ) + (σ2 : ℝ)) := by
    field_simp
    ring
  rw [key, div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos ha hb, mul_pos hb hb]

/-- **Marginal of the data given the hyperparameters** (3C.1): integrating out the group means, the
`J` groups are i.i.d. `N(μ, σ²+τ²)` (Gelman §5.4). -/
theorem normalHier_marginal_y_given_hyper (μ : ℝ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Gelman §5.4
    (hσ : σ2 ≠ 0)
    -- LEAN-ONLY: Markov instance for the Gaussian kernel; from `isMarkovKernel_gaussKernel hσ`
    [IsMarkovKernel (gaussKernel σ2)] (J : ℕ) :
    (diagKernel (gaussKernel σ2) J) ∘ₘ (Measure.pi fun _ : Fin J => gaussianReal μ τ2)
      = Measure.pi fun _ : Fin J => gaussianReal μ (τ2 + σ2) := by
  refine (Measure.pi_eq (μ := fun _ : Fin J => gaussianReal μ (τ2 + σ2))
    (fun s hs => ?_)).symm
  have hmeas : ∀ j : Fin J, Measurable fun θ : ℝ => gaussKernel σ2 θ (s j) :=
    fun j => (gaussKernel σ2).measurable_coe (hs j)
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  calc (diagKernel (gaussKernel σ2) J ∘ₘ (Measure.pi fun _ : Fin J => gaussianReal μ τ2))
          (Set.univ.pi s)
      = ∫⁻ θ, diagKernel (gaussKernel σ2) J θ (Set.univ.pi s)
          ∂(Measure.pi fun _ : Fin J => gaussianReal μ τ2) :=
        Measure.bind_apply hbox (Kernel.aemeasurable _)
    _ = ∫⁻ θ, ∏ j, gaussKernel σ2 (θ j) (s j)
          ∂(Measure.pi fun _ : Fin J => gaussianReal μ τ2) := by
        refine lintegral_congr (fun θ => ?_)
        rw [diagKernel_apply_pi (gaussKernel σ2) J θ hs]
    _ = ∏ j, ∫⁻ θ, gaussKernel σ2 θ (s j) ∂(gaussianReal μ τ2) :=
        lintegral_pi_prod (gaussianReal μ τ2) hmeas
    _ = ∏ j, (gaussKernel σ2 ∘ₘ gaussianReal μ τ2) (s j) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [Measure.bind_apply (hs j) (Kernel.aemeasurable _)]
    _ = ∏ j, gaussianReal μ (τ2 + σ2) (s j) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [comp_gaussKernel_gaussianReal hσ μ τ2]

/-- **Posterior of the hyper-mean given `τ²`** (3C.5): with the group means integrated out, `μ` has
a Normal–Normal posterior from `J` i.i.d. observations of variance `σ²+τ²` (Gelman §5.4). -/
theorem normalHier_muPosterior_given_tau (μ0 : ℝ) (t0 τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate hyperprior and marginal variances; Gelman §5.4
    (ht0 : t0 ≠ 0) (hστ : σ2 + τ2 ≠ 0)
    -- LEAN-ONLY: Markov instance for the marginal Gaussian kernel
    [IsMarkovKernel (gaussKernel (σ2 + τ2))] (J : ℕ) :
    ∀ᵐ y ∂(iidKernel (gaussKernel (σ2 + τ2)) J ∘ₘ gaussianReal μ0 t0),
      ((iidKernel (gaussKernel (σ2 + τ2)) J) † (gaussianReal μ0 t0)) y
        = gaussianReal (postMean μ0 t0 (σ2 + τ2) y) (postVar t0 (σ2 + τ2) J) := by
  exact normal_normal_posterior_ae ht0 hστ J

/-- **Per-group posterior given the hyperparameters** (3C.2, one coordinate): the group mean `θ_j`
has the scalar Normal–Normal posterior `N((1−B)y_j + B·μ, postVar)` (Gelman §5.4). -/
theorem normalHier_thetaPosterior_given_mu_tau_coord (μ : ℝ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate prior and noise variances; Gelman §5.4
    (hτ : τ2 ≠ 0) (hσ : σ2 ≠ 0)
    -- LEAN-ONLY: Markov instance for the Gaussian kernel
    [IsMarkovKernel (gaussKernel σ2)] :
    ∀ᵐ y ∂(iidKernel (gaussKernel σ2) 1 ∘ₘ gaussianReal μ τ2),
      ((iidKernel (gaussKernel σ2) 1) † (gaussianReal μ τ2)) y
        = gaussianReal (postMean μ τ2 σ2 y) (postVar τ2 σ2 1) := by
  exact normal_normal_posterior_ae hτ hσ 1

end StatLean.Bayesian
