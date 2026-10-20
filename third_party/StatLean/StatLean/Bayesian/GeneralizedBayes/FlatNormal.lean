module
public import StatLean.Bayesian.GeneralizedBayes.Basic
public import StatLean.Bayesian.Conjugacy.NormalNormal

@[expose] public section

/-!
# The flat-prior normal mean (canonical generalized-Bayes example)

For iid observations `xᵢ ~ 𝒩(μ, v)` and the improper flat prior `π(dμ) = dμ` (Lebesgue), the
generalized posterior is proper and Gaussian:
$$\mu \mid x_{1:n} \sim \mathcal N\big(\bar x,\ v/n\big).$$

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §2.5 (normal,
known variance) + §3.2 (noninformative prior, N(ȳ,σ²/n)), p. 39/64.

**Proof formalization notes.** The pointwise normalization engine applies with `π := volume`:
the product Gaussian likelihood completes the square in `μ` (the `sumSq_completion` lemma of
`Conjugacy.NormalNormal` with the prior term absent — equivalently its `t₀ → ∞` limit, proved
directly), exhibiting `volume.withDensity (∏ᵢ gaussianPDF μ v xᵢ)` as
`C(x) • gaussianReal x̄ (v/n)` with `C(x) ∈ (0, ∞)` for `n ≠ 0`. Note the abstract posterior
`κ†π` does not exist here (Lebesgue is not finite) — the statement is genuinely about
`generalizedPosterior`, which is the point of the example.

**Bibliographic comments.** The flat prior on a location parameter is Laplace's original
"principle of insufficient reason" (1774) and the simplest Jeffreys prior;
that it reproduces the frequentist answer `𝒩(x̄, v/n)` — with credible intervals numerically
equal to confidence intervals — is the classical reconciliation example. It is safe for estimation
but the arbitrary constant wrecks Bayes factors, formalized in `GeneralizedBayes.Basic`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

open Real

/-- **Flat completing-the-square** (prior-free): the iid Gaussian exponent is the posterior
exponent `(θ − x̄)²/(v/n)` plus a `θ`-free remainder. This is the `t₀ → ∞` limit of
`sumSq_completion`, proved directly (no prior term). -/
private theorem sumSq_completion_flat {v : ℝ} (hv : v ≠ 0) {n : ℕ} (hn : (n : ℝ) ≠ 0)
    (x : Fin n → ℝ) (θ : ℝ) :
    ∑ i, (x i - θ) ^ 2 / v
      = (θ - (∑ i, x i) / n) ^ 2 / (v / n)
        + ((∑ i, (x i) ^ 2) / v - (n : ℝ) * ((∑ i, x i) / n) ^ 2 / v) := by
  have hsum : (∑ i, (x i - θ) ^ 2) = (∑ i, (x i) ^ 2) - 2 * θ * (∑ i, x i) + ↑n * θ ^ 2 := by
    have hpt : ∀ i, (x i - θ) ^ 2 = (x i) ^ 2 - 2 * θ * (x i) + θ ^ 2 := fun i => by ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_div, hsum]
  field_simp
  ring

/-- The recognized `θ`-free normalizing constant for the flat-prior computation: the product of
Gaussian √-normalizations against the posterior √-normalization, times the remainder factor. -/
private noncomputable def flatConst (v : ℝ≥0) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (√(2 * π * (v : ℝ)))⁻¹ ^ n * √(2 * π * ((v / n : ℝ≥0) : ℝ))
    * Real.exp (-((∑ i, (x i) ^ 2) / (v : ℝ)
        - (n : ℝ) * ((∑ i, x i) / n) ^ 2 / (v : ℝ)) / 2)

/-- Pointwise real density identity: the iid Gaussian likelihood equals the recognized constant
times the posterior pdf `𝒩(x̄, v/n)`. -/
private theorem flat_pdf_prod_real {v : ℝ≥0} (hv : v ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (x : Fin n → ℝ) (θ : ℝ) :
    ∏ i, gaussianPDFReal θ v (x i)
      = flatConst v x * gaussianPDFReal ((∑ i, x i) / n) (v / n) θ := by
  have hV : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hwc : ((v / n : ℝ≥0) : ℝ) = (v : ℝ) / (n : ℝ) := by
    rw [NNReal.coe_div, NNReal.coe_natCast]
  have hVpos : (0 : ℝ) < (v : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg v) (Ne.symm hV)
  have hsqv : √(2 * π * (v : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos Real.pi_pos) hVpos)).ne'
  have hsqw : √(2 * π * ((v / n : ℝ≥0) : ℝ)) ≠ 0 := by
    refine (Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos Real.pi_pos) ?_)).ne'
    rw [hwc]; positivity
  have hAeq : ∏ i, gaussianPDFReal θ v (x i)
      = ((√(2 * π * (v : ℝ)))⁻¹) ^ n
        * Real.exp (∑ i, -(x i - θ) ^ 2 / (2 * (v : ℝ))) := by
    simp only [gaussianPDFReal]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
  have hBeq : flatConst v x * gaussianPDFReal ((∑ i, x i) / n) (v / n) θ
      = ((√(2 * π * (v : ℝ)))⁻¹) ^ n
        * Real.exp (-((∑ i, (x i) ^ 2) / (v : ℝ)
              - (n : ℝ) * ((∑ i, x i) / n) ^ 2 / (v : ℝ)) / 2
            + -(θ - (∑ i, x i) / n) ^ 2 / (2 * ((v / n : ℝ≥0) : ℝ))) := by
    simp only [gaussianPDFReal, flatConst]
    rw [Real.exp_add]
    field_simp
  have hes : (∑ i, -(x i - θ) ^ 2 / (2 * (v : ℝ)))
      = -(1 / 2) * (∑ i, (x i - θ) ^ 2 / (v : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hexp : (∑ i, -(x i - θ) ^ 2 / (2 * (v : ℝ)))
      = -((∑ i, (x i) ^ 2) / (v : ℝ)
            - (n : ℝ) * ((∑ i, x i) / n) ^ 2 / (v : ℝ)) / 2
          + -(θ - (∑ i, x i) / n) ^ 2 / (2 * ((v / n : ℝ≥0) : ℝ)) := by
    rw [hes, sumSq_completion_flat hV hn' x θ, hwc]
    ring
  rw [hAeq, hBeq, hexp]

/-- Strict positivity of the recognized constant (needed for `c ≠ 0` and nonnegativity). -/
private theorem flatConst_pos {v : ℝ≥0} (hv : v ≠ 0) {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ) :
    0 < flatConst v x := by
  have hV : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hVpos : (0 : ℝ) < (v : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg v) (Ne.symm hV)
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hWpos : (0 : ℝ) < ((v / n : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_div, NNReal.coe_natCast]
    exact div_pos hVpos hnpos
  have h1 : (0 : ℝ) < √(2 * π * (v : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos Real.pi_pos) hVpos)
  have h2 : (0 : ℝ) < √(2 * π * ((v / n : ℝ≥0) : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos Real.pi_pos) hWpos)
  unfold flatConst
  exact mul_pos (mul_pos (pow_pos (inv_pos.mpr h1) n) h2) (Real.exp_pos _)

/-- Measure-level recognized form: the unnormalized posterior under the flat prior is a positive
finite multiple of the `𝒩(x̄, v/n)` probability measure. -/
private theorem flat_withDensity_eq_smul {v : ℝ≥0} (hv : v ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (x : Fin n → ℝ) :
    volume.withDensity (fun θ => ∏ i, gaussianPDF θ v (x i))
      = ENNReal.ofReal (flatConst v x) • gaussianReal ((∑ i, x i) / n) (v / n) := by
  have hw : (v / n : ℝ≥0) ≠ 0 := div_ne_zero hv (Nat.cast_ne_zero.mpr hn)
  have hCnonneg : 0 ≤ flatConst v x := (flatConst_pos hv hn x).le
  have hdens : (fun θ => ∏ i, gaussianPDF θ v (x i))
      = ENNReal.ofReal (flatConst v x) • gaussianPDF ((∑ i, x i) / n) (v / n) := by
    funext θ
    simp only [Pi.smul_apply, smul_eq_mul, gaussianPDF]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg θ v (x i)),
      flat_pdf_prod_real hv hn x θ, ENNReal.ofReal_mul hCnonneg]
  rw [hdens, withDensity_smul' _ _ ENNReal.ofReal_ne_top, ← gaussianReal_of_var_ne_zero _ hw]

/-- **Flat-prior normal mean** (Gelman §2.5, `n`-observation form): under the improper
Lebesgue prior, the generalized posterior from iid `𝒩(·, v)` data is `𝒩(x̄, v/n)`. -/
theorem flat_normal_generalizedPosterior {v : ℝ≥0}
    -- USER-INPUT: nondegenerate noise variance; Gelman §2.5
    (hv : v ≠ 0) {n : ℕ}
    -- USER-INPUT: at least one observation (propriety needs it); Gelman §3.2
    (hn : n ≠ 0) (x : Fin n → ℝ) :
    generalizedPosterior (fun (θ : ℝ) (x : Fin n → ℝ) => ∏ i, gaussianPDF θ v (x i))
        volume x
      = gaussianReal ((∑ i, x i) / n) (v / n) :=
  generalizedPosterior_eq_of_withDensity_eq_smul
    (ENNReal.ofReal_pos.mpr (flatConst_pos hv hn x)).ne'
    ENNReal.ofReal_ne_top
    (flat_withDensity_eq_smul hv hn x)

end StatLean.Bayesian
