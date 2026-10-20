module
public import StatLean.HypothesisTesting.LikelihoodMethods.EstimatorUnderAlternatives
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# The local asymptotic normality expansion, uniformly over bounded directions

The quadratic expansion of the log-likelihood ratio
$$ \log L_{n,h} \;=\; \langle h, Z_n\rangle - \tfrac12\langle h, I(\theta_0)h\rangle + o_P(1)
   \qquad (L_{n,h} = L_n(\theta_0 + h/\sqrt n)/L_n(\theta_0)) $$
holds under quadratic-mean differentiability for each **fixed** direction `h`. Arguments that
substitute a *random* direction — most importantly `ĥₙ = √n(θ̂ₙ − θ₀)` in the analysis of the
likelihood ratio statistic — need the remainder to be small **uniformly over `‖h‖ ≤ c`**:
$$ \epsilon_{n,c} \;=\; \sup_{\|h\|\le c}
   \Bigl|\log L_{n,h} - \bigl[\langle h, Z_n\rangle
     - \tfrac12 \langle h, I(\theta_0) h\rangle\bigr]\Bigr| \;\xrightarrow{P}\; 0 . $$
This file states and proves that uniform version, under quadratic-mean differentiability
together with a **two-point** second-order envelope condition
$$ \bigl|\log\tfrac{p_\theta(x)}{p_{\theta_0}(x)} - \log\tfrac{p_{\theta'}(x)}{p_{\theta_0}(x)}
   - \langle \theta - \theta', \tilde\eta_{\theta_0}(x)\rangle\bigr|
   \;\le\; M(x)\,\bigl(\|\theta-\theta_0\| + \|\theta'-\theta_0\|\bigr)\,\|\theta-\theta'\|,
   \qquad E_{\theta_0}[M(X)] < \infty, $$
for `θ, θ'` in a neighbourhood of `θ₀` — the hypothesis under which the trinity of likelihood
tests is analysed.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 14 (Quadratic Mean
Differentiable Families), §14.2 (Quadratic Mean Differentiability (q.m.d.)), the quadratic
mean differentiability expansion, in the locally asymptotically normal form used uniformly
over bounded directions. (`TSH4 §14.2`.)

**Deviation from the printed hypotheses (documented amendment).** The source's envelope
condition is *one-point*: it controls the second-order Taylor remainder of
`θ ↦ log p_θ(x)` only at the base point `θ₀`,
`|log p_θ(x) − log p_{θ₀}(x) − ⟪θ−θ₀, ℓ x⟫| ≤ M(x)‖θ−θ₀‖²`. At exactly those hypotheses the
uniform statement is **false**; an explicit counterexample is recorded at
`sup_LAN_remainder_tendsto` below. The hypothesis actually used here is the *two-point* form
displayed above, i.e. the same second-order Taylor control imposed on every pair `(θ, θ')` in
the neighbourhood rather than only on the pairs `(θ, θ₀)`. Setting `θ' = θ₀` recovers the
printed condition verbatim (in ratio form: `log(p_{θ₀}(x)/p_{θ₀}(x)) = 0` for every `x`,
including the junk-value case `p_{θ₀}(x) = 0`, so the middle term drops and the right-hand
side becomes `M(x)‖θ−θ₀‖²`). The amendment is therefore a genuine strengthening of the
hypothesis and it is the *minimal* one that restores the theorem: what the one-point form
fails to provide is any control on the *increments* of the remainder, and it is exactly the
increments that a random direction probes. It is satisfied in every situation the source has
in mind (it follows from a `μ`-integrable bound on the second derivative of
`θ ↦ log p_θ(x)`, by Taylor's theorem with integral remainder), and it is what the
counterexample violates.

**Proof formalization notes.**
* The supremum over the uncountable ball is avoided at statement level: instead of asserting
  that a (possibly non-measurable) supremum converges in probability, the statement says
  that for every `ε > 0` the measure of the event `∃ h, ‖h‖ ≤ c ∧ ε ≤ |remainder|` tends to
  zero. Quantified over all `ε > 0` this is equivalent to `ε_{n,c} →_P 0`, and it needs no
  measurable-selection or separability argument to be well posed. Measures of non-measurable
  sets are the outer measure, so the statement is meaningful as written.
* The envelope condition is transcribed pointwise in `x` (as in the source) rather than
  almost everywhere; the almost-everywhere form is a weaker hypothesis and would give a
  formally stronger theorem, but the pointwise form is what the source assumes and what
  applications verify.
* Both the remainder and the envelope are expressed through the area's `logLikelihood`
  (the log-likelihood ratio of the shifted family on a sample) and `scoreSum` (the
  normalized score sum), so the fixed-`h` case of the statement is exactly the area's
  `lanResidual_tendsto_productMeasure`; the content added here is uniformity in `h`.
* `E_{θ₀}[M(X)] < ∞` is integrability of `M` against `μ.withDensity p_{θ₀}`, the model's
  single-observation law at `θ₀`.
* The proof is a chaining/net argument: the two-point envelope makes
  `h ↦ lanRemainder … h n ω` Lipschitz with the *random* constant
  `Λₙ(ω) = 2c·n⁻¹∑ᵢ M(ωᵢ) + c‖J‖`, which is `O_P(1)` by Markov's inequality (no law of large
  numbers is needed — only the mean of `Λₙ`); a finite `ρ`-net of the compact ball
  `‖h‖ ≤ c` then reduces uniformity to finitely many fixed-`h` statements, each supplied by
  `lanResidual_tendsto_productMeasure`.

**Bibliographic comments.** The quadratic expansion of the log-likelihood ratio and the local
asymptotic normality framework are due to L. Le Cam ("Locally asymptotically normal families
of distributions," *Univ. California Publ. Statist.* **3** (1960), 37–98), with the
quadratic-mean differentiability hypothesis introduced in L. Le Cam ("On the assumptions used
to prove asymptotic normality of maximum likelihood estimates," *Ann. Math. Statist.* **41**
(1970), 802–828). Uniform-in-direction control of the remainder is the technical device by
which the classical likelihood ratio theory of S. S. Wilks ("The large-sample distribution of
the likelihood ratio for testing composite hypotheses," *Ann. Math. Statist.* **9** (1938),
60–62) is recovered without third-derivative conditions.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-- The **LAN remainder** in direction `h` on a sample of size `n`:
`log L_{n,h} − (⟪h, Zₙ⟫ − ½⟪h, J h⟫)`, where `L_{n,h}` is the likelihood ratio of the
shifted parameter `θ₀ + h/√n` against `θ₀` and `Zₙ` is the normalized score sum.

Edge behaviour: at `n = 0` the empty sample makes both the log-likelihood ratio and the
score sum vanish, so the remainder is `½⟪h, J h⟫`. -/
noncomputable def lanRemainder (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ) (h : EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (ω : Fin n → 𝓧) : ℝ :=
  logLikelihood M θ₀ h n ω - (⟪h, scoreSum ℓ n ω⟫ - (1 / 2 : ℝ) * ⟪h, mulVecE J h⟫)

/-! ## Deterministic ingredients of the net argument -/

/-- `mulVecE J` is the action of the continuous linear map `Matrix.toEuclideanCLM J`;
the two spellings are definitionally equal. -/
private lemma mulVecE_eq_clm (J : Matrix (Fin k) (Fin k) ℝ)
    (v : EuclideanSpace ℝ (Fin k)) :
    mulVecE J v = Matrix.toEuclideanCLM (𝕜 := ℝ) J v := rfl

/-- The Fisher quadratic form is Lipschitz on the ball `‖h‖ ≤ c`, with constant
`2c‖J‖`. -/
private lemma abs_quadratic_sub_le (J : Matrix (Fin k) (Fin k) ℝ) {c : ℝ}
    {h h' : EuclideanSpace ℝ (Fin k)} (hh : ‖h‖ ≤ c) (hh' : ‖h'‖ ≤ c) :
    |⟪h, mulVecE J h⟫ - ⟪h', mulVecE J h'⟫|
      ≤ 2 * c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * ‖h - h'‖ := by
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J with hA
  have hrw : ⟪h, mulVecE J h⟫ - ⟪h', mulVecE J h'⟫
      = ⟪h - h', A h⟫ + ⟪h', A h - A h'⟫ := by
    simp only [mulVecE_eq_clm, hA, inner_sub_left, inner_sub_right]
    ring
  have h0 : (0 : ℝ) ≤ c := le_trans (norm_nonneg _) hh
  have hAnn : (0 : ℝ) ≤ ‖A‖ := norm_nonneg _
  have hb1 : |⟪h - h', A h⟫| ≤ ‖h - h'‖ * (‖A‖ * c) := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have : ‖A h‖ ≤ ‖A‖ * c :=
      le_trans (A.le_opNorm h) (by nlinarith [norm_nonneg h])
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have hb2 : |⟪h', A h - A h'⟫| ≤ c * (‖A‖ * ‖h - h'‖) := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have hmap : A h - A h' = A (h - h') := (map_sub A h h').symm
    have : ‖A h - A h'‖ ≤ ‖A‖ * ‖h - h'‖ := by
      rw [hmap]; exact A.le_opNorm _
    exact mul_le_mul hh' this (norm_nonneg _) h0
  calc |⟪h, mulVecE J h⟫ - ⟪h', mulVecE J h'⟫|
      = |⟪h - h', A h⟫ + ⟪h', A h - A h'⟫| := by rw [hrw]
    _ ≤ |⟪h - h', A h⟫| + |⟪h', A h - A h'⟫| := abs_add_le _ _
    _ ≤ ‖h - h'‖ * (‖A‖ * c) + c * (‖A‖ * ‖h - h'‖) := add_le_add hb1 hb2
    _ = 2 * c * ‖A‖ * ‖h - h'‖ := by ring

/-- **Stochastic Lipschitz property of the LAN remainder.**

Under the two-point envelope condition, on a sample of size `n ≥ 1` with `c/√n ≤ δ` the map
`h ↦ lanRemainder M θ₀ ℓ J h n ω` is Lipschitz on the ball `‖h‖ ≤ c`, with the random
constant `2c·n⁻¹·∑ᵢ G(ωᵢ) + c‖J‖`. -/
private lemma abs_lanRemainder_sub_le
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ) (G : 𝓧 → ℝ) (hG0 : ∀ x, 0 ≤ G x)
    (δ : ℝ)
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ G x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖)
    (c : ℝ) (_hc : 0 < c) (n : ℕ) (hn : 1 ≤ n)
    (hnδ : (Real.sqrt n)⁻¹ * c ≤ δ)
    (h h' : EuclideanSpace ℝ (Fin k)) (hh : ‖h‖ ≤ c) (hh' : ‖h'‖ ≤ c)
    (ω : Fin n → 𝓧) :
    |lanRemainder M θ₀ ℓ J h n ω - lanRemainder M θ₀ ℓ J h' n ω|
      ≤ (2 * c * ((n : ℝ)⁻¹ * ∑ i, G (ω i))
          + c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖) * ‖h - h'‖ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqinv : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := le_of_lt (inv_pos.mpr hsq)
  -- Shorthand for the two shifted parameters.
  set θh : EuclideanSpace ℝ (Fin k) := θ₀ + (Real.sqrt n)⁻¹ • h with hθh
  set θh' : EuclideanSpace ℝ (Fin k) := θ₀ + (Real.sqrt n)⁻¹ • h' with hθh'
  have hnormshift : ∀ u : EuclideanSpace ℝ (Fin k),
      ‖(Real.sqrt n)⁻¹ • u‖ = (Real.sqrt n)⁻¹ * ‖u‖ := by
    intro u
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqinv]
  have hθhnorm : ‖θh - θ₀‖ = (Real.sqrt n)⁻¹ * ‖h‖ := by
    rw [hθh, add_sub_cancel_left, hnormshift]
  have hθh'norm : ‖θh' - θ₀‖ = (Real.sqrt n)⁻¹ * ‖h'‖ := by
    rw [hθh', add_sub_cancel_left, hnormshift]
  have hdiffvec : θh - θh' = (Real.sqrt n)⁻¹ • (h - h') := by
    rw [hθh, hθh', smul_sub]; abel
  have hθhδ : ‖θh - θ₀‖ ≤ δ := by
    rw [hθhnorm]; exact le_trans (by nlinarith [hsqinv]) hnδ
  have hθh'δ : ‖θh' - θ₀‖ ≤ δ := by
    rw [hθh'norm]; exact le_trans (by nlinarith [hsqinv]) hnδ
  -- Step 1: the log-likelihood increment, linearised by the score, is a finite sum of
  -- envelope-controlled terms.
  have hsplit :
      logLikelihood M θ₀ h n ω - logLikelihood M θ₀ h' n ω - ⟪h - h', scoreSum ℓ n ω⟫
        = ∑ i, (Real.log (M.density θh (ω i) / M.density θ₀ (ω i))
              - Real.log (M.density θh' (ω i) / M.density θ₀ (ω i))
              - ⟪θh - θh', ℓ (ω i)⟫) := by
    have hinner : ∑ i, ⟪θh - θh', ℓ (ω i)⟫ = ⟪h - h', scoreSum ℓ n ω⟫ := by
      simp only [hdiffvec, scoreSum, real_inner_smul_left, real_inner_smul_right]
      rw [← Finset.mul_sum, inner_sum]
    simp only [logLikelihood, hθh, hθh']
    rw [← hinner, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hterm : ∀ i : Fin n,
      |Real.log (M.density θh (ω i) / M.density θ₀ (ω i))
        - Real.log (M.density θh' (ω i) / M.density θ₀ (ω i))
        - ⟪θh - θh', ℓ (ω i)⟫| ≤ G (ω i) * (2 * c * ‖h - h'‖ / n) := by
    intro i
    refine le_trans (henv θh θh' hθhδ hθh'δ (ω i)) ?_
    have hfac : (‖θh - θ₀‖ + ‖θh' - θ₀‖) * ‖θh - θh'‖ ≤ 2 * c * ‖h - h'‖ / n := by
      rw [hθhnorm, hθh'norm, hdiffvec, hnormshift]
      have hprod : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (le_of_lt hnpos)]
      have hsum : (Real.sqrt n)⁻¹ * ‖h‖ + (Real.sqrt n)⁻¹ * ‖h'‖
          ≤ (Real.sqrt n)⁻¹ * (2 * c) := by nlinarith [hsqinv]
      calc ((Real.sqrt n)⁻¹ * ‖h‖ + (Real.sqrt n)⁻¹ * ‖h'‖)
              * ((Real.sqrt n)⁻¹ * ‖h - h'‖)
          ≤ ((Real.sqrt n)⁻¹ * (2 * c)) * ((Real.sqrt n)⁻¹ * ‖h - h'‖) := by
            refine mul_le_mul_of_nonneg_right hsum ?_
            exact mul_nonneg hsqinv (norm_nonneg _)
        _ = ((Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹) * (2 * c * ‖h - h'‖) := by ring
        _ = 2 * c * ‖h - h'‖ / n := by rw [hprod]; ring
    have hfac0 : (0 : ℝ) ≤ (‖θh - θ₀‖ + ‖θh' - θ₀‖) * ‖θh - θh'‖ := by positivity
    calc G (ω i) * (‖θh - θ₀‖ + ‖θh' - θ₀‖) * ‖θh - θh'‖
        = G (ω i) * ((‖θh - θ₀‖ + ‖θh' - θ₀‖) * ‖θh - θh'‖) := by ring
      _ ≤ G (ω i) * (2 * c * ‖h - h'‖ / n) :=
          mul_le_mul_of_nonneg_left hfac (hG0 _)
  have hlin : |logLikelihood M θ₀ h n ω - logLikelihood M θ₀ h' n ω
        - ⟪h - h', scoreSum ℓ n ω⟫|
      ≤ (∑ i, G (ω i)) * (2 * c * ‖h - h'‖ / n) := by
    rw [hsplit]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
    rw [← Finset.sum_mul]
  -- Step 2: assemble with the Lipschitz bound on the Fisher quadratic form.
  have hdecomp : lanRemainder M θ₀ ℓ J h n ω - lanRemainder M θ₀ ℓ J h' n ω
      = (logLikelihood M θ₀ h n ω - logLikelihood M θ₀ h' n ω
          - ⟪h - h', scoreSum ℓ n ω⟫)
        + (1 / 2 : ℝ) * (⟪h, mulVecE J h⟫ - ⟪h', mulVecE J h'⟫) := by
    simp only [lanRemainder, inner_sub_left]
    ring
  have hquad := abs_quadratic_sub_le J hh hh'
  have hnormd : (0 : ℝ) ≤ ‖h - h'‖ := norm_nonneg _
  calc |lanRemainder M θ₀ ℓ J h n ω - lanRemainder M θ₀ ℓ J h' n ω|
      ≤ |logLikelihood M θ₀ h n ω - logLikelihood M θ₀ h' n ω
            - ⟪h - h', scoreSum ℓ n ω⟫|
          + |(1 / 2 : ℝ) * (⟪h, mulVecE J h⟫ - ⟪h', mulVecE J h'⟫)| := by
        rw [hdecomp]; exact abs_add_le _ _
    _ ≤ (∑ i, G (ω i)) * (2 * c * ‖h - h'‖ / n)
          + (1 / 2 : ℝ) * (2 * c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * ‖h - h'‖) := by
        refine add_le_add hlin ?_
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1/2 : ℝ))]
        exact mul_le_mul_of_nonneg_left hquad (by norm_num)
    _ = (2 * c * ((n : ℝ)⁻¹ * ∑ i, G (ω i))
          + c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖) * ‖h - h'‖ := by
        rw [div_eq_mul_inv]
        ring

/-- **Markov bound for the empirical envelope total on a product measure.**

For a nonnegative integrable `G` and a threshold `K > 0`, the `ν^n`-probability that the
sample total `∑ᵢ G(ωᵢ)` reaches `K·n` is at most `E_ν[G]/K`. Only the mean of `G` is used:
no law of large numbers is needed. -/
private lemma measureReal_pi_sum_ge_le {n : ℕ} (ν : Measure 𝓧) [IsProbabilityMeasure ν]
    (G : 𝓧 → ℝ) (hGm : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (hGtop : ∫⁻ x, ENNReal.ofReal (G x) ∂ν ≠ ⊤)
    (K : ℝ) (hK : 0 < K) (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n => ν).real {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)}
      ≤ (∫⁻ x, ENNReal.ofReal (G x) ∂ν).toReal / K := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (G x) ∂ν with hIdef
  have hfmeas : Measurable fun ω : Fin n → 𝓧 => ENNReal.ofReal (∑ i, G (ω i)) := by
    refine Measurable.ennreal_ofReal ?_
    exact Finset.univ.measurable_sum fun i _ => hGm.comp (measurable_pi_apply i)
  -- Total mass of the empirical sum.
  have hlint : ∫⁻ ω, ENNReal.ofReal (∑ i, G (ω i)) ∂(Measure.pi fun _ : Fin n => ν)
      = (n : ℝ≥0∞) * I := by
    have hpt : (fun ω : Fin n → 𝓧 => ENNReal.ofReal (∑ i, G (ω i)))
        = fun ω : Fin n → 𝓧 => ∑ i, ENNReal.ofReal (G (ω i)) := by
      funext ω
      exact ENNReal.ofReal_sum_of_nonneg fun i _ => hG0 _
    rw [hpt, lintegral_finset_sum (μ := Measure.pi fun _ : Fin n => ν) Finset.univ
      (f := fun (i : Fin n) (ω : Fin n → 𝓧) => ENNReal.ofReal (G (ω i)))
      (fun i _ => ((hGm.comp (measurable_pi_apply i)).ennreal_ofReal))]
    have heval : ∀ i : Fin n,
        ∫⁻ ω, ENNReal.ofReal (G (ω i)) ∂(Measure.pi fun _ : Fin n => ν) = I := by
      intro i
      have hmap : (Measure.pi fun _ : Fin n => ν).map (fun ω : Fin n → 𝓧 => ω i) = ν :=
        (measurePreserving_eval (μ := fun _ : Fin n => ν) i).map_eq
      have hL := lintegral_map (μ := Measure.pi fun _ : Fin n => ν)
        (g := fun ω : Fin n → 𝓧 => ω i) (f := fun x : 𝓧 => ENNReal.ofReal (G x))
        hGm.ennreal_ofReal (measurable_pi_apply i)
      rw [hmap] at hL
      exact hL.symm
    rw [Finset.sum_congr rfl fun i _ => heval i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  -- Markov's inequality, in multiplicative form.
  have hset : {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)}
      = {ω : Fin n → 𝓧 |
          ENNReal.ofReal (K * n) ≤ ENNReal.ofReal (∑ i, G (ω i))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => hG0 _)).symm
  have hmarkov : ENNReal.ofReal (K * n)
        * (Measure.pi fun _ : Fin n => ν) {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)}
      ≤ (n : ℝ≥0∞) * I := by
    rw [hset, ← hlint]
    exact mul_meas_ge_le_lintegral hfmeas _
  have hfin : ((n : ℝ≥0∞) * I) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hGtop
  have h2 := ENNReal.toReal_mono hfin hmarkov
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ K * n), ENNReal.toReal_natCast] at h2
  rw [measureReal_def, le_div_iff₀ hK]
  have hkey : (n : ℝ)
      * (((Measure.pi fun _ : Fin n => ν)
          {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)}).toReal * K)
      ≤ (n : ℝ) * I.toReal := by
    have hre : (n : ℝ)
        * (((Measure.pi fun _ : Fin n => ν)
            {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)}).toReal * K)
        = K * n
          * ((Measure.pi fun _ : Fin n => ν)
              {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)}).toReal := by ring
    rw [hre]; exact h2
  exact le_of_mul_le_mul_left hkey hnpos

/-- **Threshold for the empirical envelope average under the model.**

Specialisation of `measureReal_pi_sum_ge_le` to `P^n_{θ₀}`. -/
private lemma exists_threshold_envelope_sum
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (G : 𝓧 → ℝ) (hGm : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (hGint : Integrable G (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (α : ℝ) (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      (productMeasure M μ θ₀ n).real {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)} ≤ α := by
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x) with hνdef
  haveI hνprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable θ₀)
        (Filter.Eventually.of_forall (M.density_nonneg θ₀)),
      hPDF.density_integral_eq_one θ₀, ENNReal.ofReal_one]
  have hGtop : ∫⁻ x, ENNReal.ofReal (G x) ∂ν ≠ ⊤ := by
    have hle : ∫⁻ x, ENNReal.ofReal (G x) ∂ν ≤ ∫⁻ x, ‖G x‖ₑ ∂ν := by
      refine lintegral_mono fun x => ?_
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    exact ne_top_of_le_ne_top (ne_of_lt hGint.hasFiniteIntegral) hle
  set A : ℝ := (∫⁻ x, ENNReal.ofReal (G x) ∂ν).toReal with hAdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  refine ⟨(A + 1) / α, by positivity, fun n hn => ?_⟩
  have hK0 : 0 < (A + 1) / α := by positivity
  have hpi : productMeasure M μ θ₀ n = Measure.pi fun _ : Fin n => ν := rfl
  rw [hpi]
  refine le_trans (measureReal_pi_sum_ge_le ν G hGm hG0 hGtop _ hK0 hn) ?_
  rw [← hAdef, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **Uniform LAN remainder.**

Under quadratic-mean differentiability at `θ₀` and the two-point second-order envelope
condition, the LAN remainder is uniformly small over every bounded set of directions: for
every radius `c > 0` and every `ε > 0`, the `P^n_{θ₀}`-probability that some direction `h`
with `‖h‖ ≤ c` has remainder at least `ε` tends to zero.

This is the statement consumed by the likelihood ratio analysis, where the direction is the
random `ĥₙ = √n(θ̂ₙ − θ₀)`, bounded in probability but not fixed.

**AMENDED HYPOTHESIS (documented deviation).** The source's *one-point* envelope condition
`|log p_θ(x) − log p_{θ₀}(x) − ⟪θ−θ₀, ℓ x⟫| ≤ M(x)‖θ−θ₀‖²` does **not** suffice: at exactly
those hypotheses the statement below is **false**. Quadratic-mean differentiability and the
one-point envelope constrain `θ ↦ log p_θ(x)` only through a *bound*, and leave the class of
functions `{x ↦ n·(log p_{θ₀ + h/√n}(x) − log p_{θ₀}(x) − ⟪h/√n, ℓ x⟫) : ‖h‖ ≤ c}`
completely unrestricted apart from the envelope `c²·M`. Such a class need not be
Glivenko–Cantelli, and then the empirical average over the sample can be far from its mean
at a *data-dependent* direction `h` even though it converges for every fixed one. The
counterexample:

* `𝓧 = ℝ`, `μ` Lebesgue measure, `k = 1`, base law `P_{θ₀}` uniform on `[0,1]` with score
  `ℓ x = x − 1/2` (so `E_{θ₀}[ℓ] = 0` and `J = 1/12 > 0`), and the exponential-family core
  `q_θ(x) = p_{θ₀}(x)·exp((θ−θ₀)·ℓ x)/Z₀(θ)`.
* Fix a bijection `s ↦ A_s` from `(0, c]` onto the finite subsets of `ℝ`, arranged so that for
  every `n` and every `n`-element set `S` there is `h ∈ (c√n/√(n+1), c]` with
  `A_{h/√n} = S` (possible: both sides have the cardinality of the continuum), and put
  `p_θ(x) = q_θ(x)·exp(|θ−θ₀|²·(2·1_{A_{|θ−θ₀|}}(x) − 1))/Z(θ)`.
  Every `p_θ` is Borel and normalized, the one-point envelope condition holds with the
  *constant* `Menv ≡ 2`, and the model is q.m.d. at `θ₀` with score `ℓ` and information `J` —
  the perturbation is `O(|θ−θ₀|²)` uniformly, hence `o(|θ−θ₀|)` in `L²`.
* For each **fixed** `h`, the set `A_{|h|/√n}` is a fixed finite set, which the sample misses
  almost surely (the base law is atomless), so the perturbation contributes exactly its mean
  and `lanRemainder M θ₀ ℓ J h n = 0` almost surely: the fixed-`h` expansion
  (`AsymptoticRepresentation.lanResidual_tendsto_productMeasure`) holds, as it must.
* But for **each `n`**, on the almost-sure event that `ω₁, …, ωₙ` are distinct, the direction
  `h(ω)` with `A_{|h(ω)|/√n} = {ω₁, …, ωₙ}` satisfies `‖h(ω)‖ ≤ c` and
  `lanRemainder M θ₀ ℓ J (h ω) n ω = 2‖h ω‖² ≥ 2c²·n/(n+1)`.
  So for `ε < c²` the probability in the conclusion tends to `1`, not to `0`.

What the counterexample violates — and what the printed hypotheses fail to supply — is any
control on the *increments* of the second-order remainder: the perturbation
`exp(|θ−θ₀|²(2·1_{A_{|θ−θ₀|}} − 1))` jumps discontinuously as `θ` moves, while staying
`O(|θ−θ₀|²)` at each `θ` separately. The hypothesis `henv` below is therefore the *two-point*
form of the same second-order Taylor bound, imposed on pairs `(θ, θ')` in the neighbourhood
rather than only on `(θ, θ₀)`; taking `θ' = θ₀` returns the printed condition verbatim (in
ratio form, using `log(p_{θ₀}(x)/p_{θ₀}(x)) = 0`). It follows from an integrable bound on the
second derivative of `θ ↦ log p_θ(x)` — which is how the source's applications verify the
condition — and it is exactly what makes the remainder class stochastically equicontinuous,
hence Glivenko–Cantelli over the compact ball. -/
theorem sup_LAN_remainder_tendsto
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF` through
    -- `productMeasure_isProbabilityMeasure`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable; the model is a density family
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which the expansion is taken
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the envelope function of the second-order expansion
    (Menv : 𝓧 → ℝ)
    -- LEAN-ONLY: measurability of the envelope; standard regularity
    (hMenv_meas : Measurable Menv)
    -- USER-INPUT: the envelope has finite mean under the model at `θ₀`
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: two-point second-order envelope condition on the log-density increment.
    -- AMENDED: the printed condition is the special case `θ' = θ₀`; see the docstring.
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖)
    -- USER-INPUT: the radius of the ball of directions over which uniformity is claimed
    (c : ℝ) (hc : 0 < c) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ∃ h : EuclideanSpace ℝ (Fin k),
          ‖h‖ ≤ c ∧ ε ≤ |lanRemainder M θ₀ ℓ J h n ω|})
        atTop (𝓝 0) := by
  intro ε hε
  -- Replace the envelope by its positive part: the bound is unchanged (the multiplier is
  -- nonnegative) and the positive part is nonnegative and still integrable.
  set G : 𝓧 → ℝ := fun x => max (Menv x) 0 with hGdef
  have hGm : Measurable G := hMenv_meas.max measurable_const
  have hG0 : ∀ x, 0 ≤ G x := fun x => le_max_right _ _
  have hGint : Integrable G (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) := by
    exact ⟨hGm.aestronglyMeasurable, hMenv_int.hasFiniteIntegral.max_zero⟩
  have henvG : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ G x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖ := by
    intro θ θ' hθ hθ' x
    refine le_trans (henv θ θ' hθ hθ' x) ?_
    have hnn : (0 : ℝ) ≤ (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖ := by positivity
    have := mul_le_mul_of_nonneg_right (le_max_left (Menv x) 0) hnn
    calc Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖
        = Menv x * ((‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) := by ring
      _ ≤ G x * ((‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) := this
      _ = G x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖ := by ring
  -- The fixed-direction LAN residual, available for every `h`.
  have hfixed : ∀ (h : EuclideanSpace ℝ (Fin k)) (η : ℝ), 0 < η →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | η ≤ |lanRemainder M θ₀ ℓ J h n ω|}) atTop (𝓝 0) := by
    intro h η hη
    have := lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      (hPDF.density_integral_eq_one θ₀) (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one _) (fun t u => hPDF.density_integrable _)
      hDQM J (fun u v => hJ u v) h η hη
    simpa [lanRemainder, mulVecE] using this
  -- `(√n)⁻¹ → 0`, so the local neighbourhood eventually contains the whole ball.
  have hsqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * c) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    simpa using h2.mul_const c
  have hδev : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ * c ≤ δ := by
    have := hsqrt (Iio_mem_nhds hδ)
    filter_upwards [this] with n hn using le_of_lt hn
  -- The convergence statement, checked against every tolerance `α > 0`.
  refine NormedAddGroup.tendsto_nhds_zero.2 ?_
  intro α hα
  -- A threshold making the random Lipschitz constant bounded with probability `≥ 1 − α/2`.
  obtain ⟨K, hK0, hKbound⟩ :=
    exists_threshold_envelope_sum M μ hPDF θ₀ G hGm hG0 hGint (α / 2) (by positivity)
  -- The resulting deterministic Lipschitz bound on the good event.
  set Λ : ℝ := 2 * c * K + c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ with hΛdef
  have hΛ0 : 0 < Λ := by
    have : (0 : ℝ) ≤ c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ := by positivity
    have h2 : 0 < 2 * c * K := by positivity
    simp only [hΛdef]; linarith
  set ρ : ℝ := ε / (2 * Λ) with hρdef
  have hρ0 : 0 < ρ := by simp only [hρdef]; positivity
  -- A finite `ρ`-net of the compact ball of directions.
  obtain ⟨F, hFsub, hFfin, hFcov⟩ :=
    finite_cover_balls_of_compact
      (isCompact_closedBall (x := (0 : EuclideanSpace ℝ (Fin k))) (r := c)) hρ0
  set Ff : Finset (EuclideanSpace ℝ (Fin k)) := hFfin.toFinset with hFfdef
  -- Each net point contributes a vanishing probability.
  have hnet : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Ff,
      (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε / 2 ≤ |lanRemainder M θ₀ ℓ J y n ω|}
      ≤ α / (2 * (Ff.card + 1)) := by
    refine Ff.eventually_all.2 fun y _ => ?_
    have hpos : 0 < α / (2 * (Ff.card + 1)) := by positivity
    have := hfixed y (ε / 2) (by positivity)
    have hev := (NormedAddGroup.tendsto_nhds_zero.1 this) _ hpos
    filter_upwards [hev] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] at hn
    exact hn.le
  filter_upwards [hnet, hδev, eventually_ge_atTop 1] with n hn hnδ hn1
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  -- The bad event is contained in "envelope large" ∪ "some net point fails".
  have hincl : {ω : Fin n → 𝓧 | ∃ h : EuclideanSpace ℝ (Fin k),
        ‖h‖ ≤ c ∧ ε ≤ |lanRemainder M θ₀ ℓ J h n ω|}
      ⊆ {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)}
        ∪ ⋃ y ∈ Ff, {ω : Fin n → 𝓧 | ε / 2 ≤ |lanRemainder M θ₀ ℓ J y n ω|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists,
      not_le] at hcon
    obtain ⟨henvsmall, hnetsmall⟩ := hcon
    obtain ⟨h, hhc, hhε⟩ := hω
    -- Pick a net point within `ρ`.
    have hmem : h ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) c := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hhc
    obtain ⟨y, hyF, hylt⟩ := Set.mem_iUnion₂.1 (hFcov hmem)
    have hyFf : y ∈ Ff := by rwa [hFfdef, Set.Finite.mem_toFinset]
    have hdist : ‖h - y‖ ≤ ρ := by
      have := Metric.mem_ball.1 hylt
      rw [dist_eq_norm] at this
      exact this.le
    have hyc : ‖y‖ ≤ c := by
      have hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) c := hFsub hyF
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    -- The Lipschitz estimate on the good event.
    have hlip := abs_lanRemainder_sub_le M θ₀ ℓ J G hG0 δ henvG c hc n hn1 hnδ h y hhc hyc ω
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsumbound : (n : ℝ)⁻¹ * ∑ i, G (ω i) < K := by
      have := henvsmall
      rw [inv_mul_lt_iff₀ hnpos]
      linarith [this]
    have hΛn : 2 * c * ((n : ℝ)⁻¹ * ∑ i, G (ω i))
        + c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ ≤ Λ := by
      have h2c : (0 : ℝ) < 2 * c := by positivity
      simp only [hΛdef]
      nlinarith [hsumbound.le]
    have hstep : |lanRemainder M θ₀ ℓ J h n ω - lanRemainder M θ₀ ℓ J y n ω| ≤ ε / 2 := by
      refine le_trans hlip ?_
      have hchain : (2 * c * ((n : ℝ)⁻¹ * ∑ i, G (ω i))
          + c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖) * ‖h - y‖ ≤ Λ * ρ :=
        mul_le_mul hΛn hdist (norm_nonneg _) hΛ0.le
      refine le_trans hchain ?_
      rw [hρdef]
      field_simp
      exact le_rfl
    have hyval : |lanRemainder M θ₀ ℓ J y n ω| < ε / 2 := hnetsmall y hyFf
    have : |lanRemainder M θ₀ ℓ J h n ω| < ε := by
      have := abs_sub_abs_le_abs_sub (lanRemainder M θ₀ ℓ J h n ω)
        (lanRemainder M θ₀ ℓ J y n ω)
      linarith
    linarith
  -- Subadditivity and the two bounds.
  have hmono := measureReal_mono (μ := productMeasure M μ θ₀ n) hincl (measure_ne_top _ _)
  have hunion := measureReal_union_le (μ := productMeasure M μ θ₀ n)
    {ω : Fin n → 𝓧 | K * n ≤ ∑ i, G (ω i)}
    (⋃ y ∈ Ff, {ω : Fin n → 𝓧 | ε / 2 ≤ |lanRemainder M θ₀ ℓ J y n ω|})
  have hbiU : (productMeasure M μ θ₀ n).real
      (⋃ y ∈ Ff, {ω : Fin n → 𝓧 | ε / 2 ≤ |lanRemainder M θ₀ ℓ J y n ω|})
      ≤ ∑ y ∈ Ff, (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε / 2 ≤ |lanRemainder M θ₀ ℓ J y n ω|} :=
    measureReal_biUnion_finset_le _ _
  have hsum : ∑ y ∈ Ff, (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 | ε / 2 ≤ |lanRemainder M θ₀ ℓ J y n ω|}
      ≤ Ff.card * (α / (2 * (Ff.card + 1))) := by
    calc ∑ y ∈ Ff, (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 | ε / 2 ≤ |lanRemainder M θ₀ ℓ J y n ω|}
        ≤ ∑ _y ∈ Ff, α / (2 * (Ff.card + 1)) :=
          Finset.sum_le_sum fun y hy => hn y hy
      _ = Ff.card * (α / (2 * (Ff.card + 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have henvterm := hKbound n hn1
  have hcard : (Ff.card : ℝ) * (α / (2 * (Ff.card + 1))) < α / 2 := by
    have hden : (0 : ℝ) < 2 * (Ff.card + 1) := by positivity
    rw [mul_div_assoc'] at *
    rw [div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    have : (0 : ℝ) ≤ Ff.card := Nat.cast_nonneg _
    nlinarith
  linarith

end StatLean.HypothesisTesting
