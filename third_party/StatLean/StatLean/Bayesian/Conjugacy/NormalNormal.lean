module
public import StatLean.Bayesian.Conjugacy.Defs
public import StatLean.Bayesian.Conjugacy.Criterion
public import StatLean.Bayesian.ForMathlib.IIDKernel
public import StatLean.Bayesian.Updating.Defs

@[expose] public section

/-!
# Normal-Normal conjugacy (known variance) and the normal posterior predictive

For a mean `μ ~ 𝒩(m₀, t₀)` and iid observations `xᵢ ~ 𝒩(μ, v)` with known noise variance `v`:

* **posterior** (Gelman §2.5): `μ | x_{1:n} ~ 𝒩(postMean, postVar)` with
  `postVar = (t₀⁻¹ + n v⁻¹)⁻¹` and `postMean = postVar · (m₀/t₀ + (∑xᵢ)/v)`;
* **posterior predictive**: a future observation satisfies
  `x_{n+1} | x_{1:n} ~ 𝒩(postMean, postVar + v)` — posterior uncertainty plus noise.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §2.5
(normal mean, known variance), p. 39.

**Proof formalization notes.** The heart is a real **sum-of-squares (completing the square)
identity**: `(θ−m₀)²/t₀ + ∑ᵢ(xᵢ−θ)²/v = (θ−postMean)²/postVar + R(x)` with `R` independent of
`θ` (`field_simp` + `ring` with the nonzeroness of `t₀`, `v`, and `postVar`); exponentiating gives
the pointwise recognized form for the criterion (`gaussianReal_of_var_ne_zero` on both sides).
The predictive composes the posterior with one more Gaussian: `gaussKernel v ∘ₘ gaussianReal m V =
gaussianReal m (V + v)` — the bind-is-convolution step, closed by the pinned
`gaussianReal_conv_gaussianReal`. The Gaussian kernel is Markov only for `v ≠ 0` (at `v = 0` the
`withDensity` construction degenerates to the zero kernel), so statements carry the instance
`[IsMarkovKernel (gaussKernel v)]`, discharged by `isMarkovKernel_gaussKernel hv` — a LEAN-ONLY
plumbing argument, not a statistical assumption beyond `v ≠ 0`.

**Bibliographic comments.** The Gaussian-mean update with Gaussian prior is Gauss's own
combination-of-observations calculus (*Theoria motus*, 1809) read as Bayesian shrinkage; the
precision-weighted form is the basis of the Kalman filter (R. E. Kalman, *J. Basic Eng.* 82
(1960), 35–45 — sequential Normal-Normal updating) and of credibility formulas in actuarial
science.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- Joint measurability of the Gaussian density `(θ, x) ↦ gaussianPDF θ v x`. -/
private theorem measurable_uncurry_gaussKernelDensity (v : ℝ≥0) :
    Measurable (Function.uncurry fun θ x => gaussianPDF θ v x) := by
  change Measurable fun z : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal z.1 v z.2)
  refine Measurable.ennreal_ofReal ?_
  unfold gaussianPDFReal
  fun_prop

/-- The Gaussian known-variance kernel is Markov for nonzero variance. -/
theorem isMarkovKernel_gaussKernel {v : ℝ≥0}
    -- USER-INPUT: nondegenerate noise variance; Gelman §2.5
    (hv : v ≠ 0) :
    IsMarkovKernel (gaussKernel v) := by
  refine ⟨fun θ => ⟨?_⟩⟩
  rw [gaussKernel, Kernel.withDensity_apply _ (measurable_uncurry_gaussKernelDensity v),
    Kernel.const_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact lintegral_gaussianPDF_eq_one θ hv

/-- The real inverse of `postVar` is the sum of precisions `t₀⁻¹ + n·v⁻¹`. -/
private theorem postVar_coe_inv (t₀ v : ℝ≥0) (n : ℕ) :
    ((postVar t₀ v n : ℝ))⁻¹ = (t₀ : ℝ)⁻¹ + ↑n * (v : ℝ)⁻¹ := by
  unfold postVar
  rw [NNReal.coe_inv, inv_inv, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_inv,
    NNReal.coe_natCast]

/-- **Sum-of-squares (completing the square)**: the prior-plus-likelihood exponent is the
posterior exponent plus a `θ`-free remainder. -/
theorem sumSq_completion {m₀ : ℝ} {t₀ v : ℝ≥0}
    -- USER-INPUT: nondegenerate prior and noise variances; Gelman §2.5
    (ht₀ : t₀ ≠ 0) (hv : v ≠ 0) {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    (θ - m₀) ^ 2 / (t₀ : ℝ) + ∑ i, (x i - θ) ^ 2 / (v : ℝ)
      = (θ - postMean m₀ t₀ v x) ^ 2 / (postVar t₀ v n : ℝ)
        + ((∑ i, (x i) ^ 2) / (v : ℝ) + m₀ ^ 2 / (t₀ : ℝ)
            - postMean m₀ t₀ v x ^ 2 / (postVar t₀ v n : ℝ)) := by
  have hT : (t₀ : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr ht₀
  have hV : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hTpos : (0 : ℝ) < t₀ := lt_of_le_of_ne (NNReal.coe_nonneg t₀) (Ne.symm hT)
  have hVpos : (0 : ℝ) < v := lt_of_le_of_ne (NNReal.coe_nonneg v) (Ne.symm hV)
  have hinv : ((postVar t₀ v n : ℝ))⁻¹ = (t₀ : ℝ)⁻¹ + ↑n * (v : ℝ)⁻¹ := postVar_coe_inv t₀ v n
  have hpvinv_pos : (0 : ℝ) < ((postVar t₀ v n : ℝ))⁻¹ := by
    rw [hinv]
    have h1 : (0 : ℝ) < (t₀ : ℝ)⁻¹ := inv_pos.mpr hTpos
    have h2 : (0 : ℝ) ≤ ↑n * (v : ℝ)⁻¹ := by positivity
    linarith
  have hPV : (postVar t₀ v n : ℝ) ≠ 0 := by
    intro h; rw [h, inv_zero] at hpvinv_pos; exact lt_irrefl 0 hpvinv_pos
  have hden : (v : ℝ) + ↑n * (t₀ : ℝ) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hVpos (by positivity)).ne'
  have hkey : (postVar t₀ v n : ℝ) * ((v : ℝ) + ↑n * (t₀ : ℝ)) = (t₀ : ℝ) * (v : ℝ) := by
    have e : ((postVar t₀ v n : ℝ))⁻¹ * ((t₀ : ℝ) * (v : ℝ)) = (v : ℝ) + ↑n * (t₀ : ℝ) := by
      rw [hinv]; field_simp
    calc (postVar t₀ v n : ℝ) * ((v : ℝ) + ↑n * (t₀ : ℝ))
        = (postVar t₀ v n : ℝ) * (((postVar t₀ v n : ℝ))⁻¹ * ((t₀ : ℝ) * (v : ℝ))) := by rw [e]
      _ = (t₀ : ℝ) * (v : ℝ) := by rw [← mul_assoc, mul_inv_cancel₀ hPV, one_mul]
  have hPVval : (postVar t₀ v n : ℝ) = (t₀ : ℝ) * (v : ℝ) / ((v : ℝ) + ↑n * (t₀ : ℝ)) := by
    rw [eq_div_iff hden]; exact hkey
  have hsum : (∑ i, (x i - θ) ^ 2) = (∑ i, (x i) ^ 2) - 2 * θ * (∑ i, x i) + ↑n * θ ^ 2 := by
    have hpt : ∀ i, (x i - θ) ^ 2 = (x i) ^ 2 - 2 * θ * (x i) + θ ^ 2 := fun i => by ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_div, hsum]
  simp only [postMean]
  rw [hPVval]
  field_simp
  ring

/-- `postVar` is nonzero for nondegenerate prior variance. -/
private theorem postVar_ne_zero {t₀ v : ℝ≥0} (ht₀ : t₀ ≠ 0) (n : ℕ) : postVar t₀ v n ≠ 0 := by
  unfold postVar
  rw [ne_eq, inv_eq_zero, add_eq_zero]
  exact fun h => ht₀ (inv_eq_zero.mp h.1)

/-- The recognized normalizing constant `c(x)` collecting the Gaussian √-normalizations and the
`θ`-free remainder of the completed square. -/
private noncomputable def nnConst (m₀ : ℝ) (t₀ v : ℝ≥0) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * (postVar t₀ v n : ℝ)) * (Real.sqrt (2 * Real.pi * (t₀ : ℝ)))⁻¹
    * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) ^ n
    * Real.exp (-(((∑ i, (x i) ^ 2) / (v : ℝ) + m₀ ^ 2 / (t₀ : ℝ)
        - (postMean m₀ t₀ v x) ^ 2 / (postVar t₀ v n : ℝ))) / 2)

/-- Pointwise real density identity: prior pdf times the iid Gaussian likelihood is the recognized
constant times the posterior pdf. -/
private theorem pdf_prod_real {m₀ : ℝ} {t₀ v : ℝ≥0} (ht₀ : t₀ ≠ 0) (hv : v ≠ 0)
    {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    gaussianPDFReal m₀ t₀ θ * ∏ i, gaussianPDFReal θ v (x i)
      = nnConst m₀ t₀ v x * gaussianPDFReal (postMean m₀ t₀ v x) (postVar t₀ v n) θ := by
  have hpost_pos : (0 : ℝ) < (postVar t₀ v n : ℝ) :=
    lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm (NNReal.coe_ne_zero.mpr (postVar_ne_zero ht₀ n)))
  have hpi := Real.pi_pos
  have hsqt : Real.sqrt (2 * Real.pi * (t₀ : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi * (t₀ : ℝ) :=
      mul_pos (mul_pos two_pos hpi) (lt_of_le_of_ne (NNReal.coe_nonneg _)
        (Ne.symm (NNReal.coe_ne_zero.mpr ht₀)))
    exact (Real.sqrt_pos.mpr this).ne'
  have hsqv : Real.sqrt (2 * Real.pi * (v : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi * (v : ℝ) :=
      mul_pos (mul_pos two_pos hpi) (lt_of_le_of_ne (NNReal.coe_nonneg _)
        (Ne.symm (NNReal.coe_ne_zero.mpr hv)))
    exact (Real.sqrt_pos.mpr this).ne'
  have hsq : Real.sqrt (2 * Real.pi * (postVar t₀ v n : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos hpi) hpost_pos)).ne'
  have hAeq : gaussianPDFReal m₀ t₀ θ * ∏ i, gaussianPDFReal θ v (x i)
      = ((Real.sqrt (2 * Real.pi * (t₀ : ℝ)))⁻¹ * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) ^ n)
        * Real.exp (-(θ - m₀) ^ 2 / (2 * (t₀ : ℝ)) + ∑ i, -(x i - θ) ^ 2 / (2 * (v : ℝ))) := by
    simp only [gaussianPDFReal]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, mul_mul_mul_comm, ← Real.exp_add]
  have hBeq : nnConst m₀ t₀ v x * gaussianPDFReal (postMean m₀ t₀ v x) (postVar t₀ v n) θ
      = ((Real.sqrt (2 * Real.pi * (t₀ : ℝ)))⁻¹ * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) ^ n)
        * Real.exp (-(((∑ i, (x i) ^ 2) / (v : ℝ) + m₀ ^ 2 / (t₀ : ℝ)
              - (postMean m₀ t₀ v x) ^ 2 / (postVar t₀ v n : ℝ))) / 2
            + -(θ - postMean m₀ t₀ v x) ^ 2 / (2 * (postVar t₀ v n : ℝ))) := by
    simp only [gaussianPDFReal, nnConst]
    rw [Real.exp_add]
    field_simp
  rw [hAeq, hBeq]
  have hes : (∑ i, -(x i - θ) ^ 2 / (2 * (v : ℝ)))
      = -(1 / 2) * (∑ i, (x i - θ) ^ 2 / (v : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hexp : (-(θ - m₀) ^ 2 / (2 * (t₀ : ℝ)) + ∑ i, -(x i - θ) ^ 2 / (2 * (v : ℝ)))
      = (-(((∑ i, (x i) ^ 2) / (v : ℝ) + m₀ ^ 2 / (t₀ : ℝ)
              - (postMean m₀ t₀ v x) ^ 2 / (postVar t₀ v n : ℝ))) / 2
          + -(θ - postMean m₀ t₀ v x) ^ 2 / (2 * (postVar t₀ v n : ℝ))) := by
    rw [hes]
    have hs := sumSq_completion (m₀ := m₀) ht₀ hv x θ
    linear_combination (-1 / 2 : ℝ) * hs
  rw [hexp]

/-- Pointwise `ℝ≥0∞` density identity fed to the conjugacy criterion. -/
private theorem pdf_prod_ennreal {m₀ : ℝ} {t₀ v : ℝ≥0} (ht₀ : t₀ ≠ 0) (hv : v ≠ 0)
    {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    gaussianPDF m₀ t₀ θ * ∏ i, gaussianPDF θ v (x i)
      = ENNReal.ofReal (nnConst m₀ t₀ v x)
          * gaussianPDF (postMean m₀ t₀ v x) (postVar t₀ v n) θ := by
  have hcnn : (0 : ℝ) ≤ nnConst m₀ t₀ v x := by
    unfold nnConst; positivity
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul hcnn, pdf_prod_real ht₀ hv x θ]

set_option maxHeartbeats 1000000 in
/-- **Normal-Normal posterior, known variance** (Gelman §2.5): iid Gaussian
observations update `𝒩(m₀, t₀)` to `𝒩(postMean, postVar)`, predictive-a.e. -/
theorem normal_normal_posterior_ae {m₀ : ℝ} {t₀ v : ℝ≥0}
    -- USER-INPUT: nondegenerate prior and noise variances; Gelman §2.5
    (ht₀ : t₀ ≠ 0) (hv : v ≠ 0)
    -- LEAN-ONLY: Markov instance for the Gaussian kernel; from `isMarkovKernel_gaussKernel hv`
    [IsMarkovKernel (gaussKernel v)] (n : ℕ) :
    ∀ᵐ x ∂(iidKernel (gaussKernel v) n ∘ₘ gaussianReal m₀ t₀),
      ((iidKernel (gaussKernel v) n)†(gaussianReal m₀ t₀)) x
        = gaussianReal (postMean m₀ t₀ v x) (postVar t₀ v n) := by
  have hunc : Measurable (Function.uncurry fun θ y => gaussianPDF θ v y) :=
    measurable_uncurry_gaussKernelDensity v
  have hκ : ∀ θ, gaussKernel v θ = volume.withDensity (fun y => gaussianPDF θ v y) := by
    intro θ
    rw [gaussKernel, Kernel.withDensity_apply _ hunc, Kernel.const_apply]
  refine posterior_ae_eq_of_withDensity_eq_smul
    (ν := Measure.pi fun _ : Fin n => (volume : Measure ℝ))
    (p := fun θ (y : Fin n → ℝ) => ∏ i, gaussianPDF θ v (y i))
    (ρ := fun y => gaussianReal (postMean m₀ t₀ v y) (postVar t₀ v n))
    (c := fun y => ENNReal.ofReal (nnConst m₀ t₀ v y))
    (measurable_uncurry_prod_likelihood hunc)
    (fun θ => iidKernel_withDensity hunc hκ n θ)
    (fun _ => inferInstance)
    ?_
  intro x
  have hprior : Measurable (gaussianPDF m₀ t₀) := measurable_gaussianPDF m₀ t₀
  have hprod : Measurable (fun θ => ∏ i, gaussianPDF θ v (x i)) :=
    Finset.measurable_prod _ (fun i _ =>
      hunc.of_uncurry_right)
  have hfun : (gaussianPDF m₀ t₀) * (fun θ => ∏ i, gaussianPDF θ v (x i))
      = ENNReal.ofReal (nnConst m₀ t₀ v x)
          • (fun θ => gaussianPDF (postMean m₀ t₀ v x) (postVar t₀ v n) θ) := by
    funext θ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact pdf_prod_ennreal ht₀ hv x θ
  rw [gaussianReal_of_var_ne_zero m₀ ht₀,
    gaussianReal_of_var_ne_zero (postMean m₀ t₀ v x) (postVar_ne_zero ht₀ n),
    ← withDensity_mul _ hprior hprod, hfun,
    withDensity_smul' _ _ ENNReal.ofReal_ne_top]

/-- The Gaussian kernel evaluated at `m'` is the Gaussian law `𝒩(m', v)` (for `v ≠ 0`). -/
private theorem gaussKernel_apply_eq {v : ℝ≥0} (hv : v ≠ 0) (m' : ℝ) :
    gaussKernel v m' = gaussianReal m' v := by
  rw [gaussKernel, Kernel.withDensity_apply _ (measurable_uncurry_gaussKernelDensity v),
    Kernel.const_apply, gaussianReal_of_var_ne_zero _ hv]

/-- **Bind is convolution for Gaussians**: pushing a Gaussian law through the Gaussian kernel adds
the variances. -/
theorem comp_gaussKernel_gaussianReal {v : ℝ≥0}
    -- USER-INPUT: nondegenerate noise variance; Gelman §2.5
    (hv : v ≠ 0) (m : ℝ) (V : ℝ≥0) :
    gaussKernel v ∘ₘ gaussianReal m V = gaussianReal m (V + v) := by
  have hconv : gaussianReal m V ∗ gaussianReal 0 v = gaussianReal m (V + v) := by
    rw [gaussianReal_conv_gaussianReal, add_zero]
  rw [← hconv]
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable hf.aemeasurable,
    Measure.lintegral_conv hf]
  refine lintegral_congr (fun m' => ?_)
  rw [gaussKernel_apply_eq hv m']
  have hmap : (gaussianReal 0 v).map (m' + ·) = gaussianReal m' v := by
    rw [gaussianReal_map_const_add, zero_add]
  rw [← hmap, lintegral_map hf (measurable_const_add m')]

/-- **Normal posterior predictive** (Gelman §2.5 specialized): a future observation is
Gaussian with the posterior mean and variance `postVar + v`, predictive-a.e. -/
theorem normal_normal_posteriorPredictive_ae {m₀ : ℝ} {t₀ v : ℝ≥0}
    -- USER-INPUT: nondegenerate prior and noise variances; Gelman §2.5
    (ht₀ : t₀ ≠ 0) (hv : v ≠ 0)
    -- LEAN-ONLY: Markov instance for the Gaussian kernel; from `isMarkovKernel_gaussKernel hv`
    [IsMarkovKernel (gaussKernel v)] (n : ℕ) :
    ∀ᵐ x ∂(iidKernel (gaussKernel v) n ∘ₘ gaussianReal m₀ t₀),
      posteriorPredictive (iidKernel (gaussKernel v) n) (gaussKernel v) (gaussianReal m₀ t₀) x
        = gaussianReal (postMean m₀ t₀ v x) (postVar t₀ v n + v) := by
  filter_upwards [normal_normal_posterior_ae ht₀ hv n] with x hx
  rw [posteriorPredictive_apply, hx, comp_gaussKernel_gaussianReal hv]

end StatLean.Bayesian
