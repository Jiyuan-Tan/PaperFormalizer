module
public import StatLean.Minimaxity.EstimationToTesting
public import StatLean.Minimaxity.ForMathlib.TotalVariation

@[expose] public section

/-!
# Le Cam's two-point method and the Bayes-error / total-variation identity

Consider a binary hypothesis-testing problem in which a label $J \in \{0,1\}$ is drawn uniformly
and, conditionally on $J = j$, the observation $Z$ is generated from $\mathbb{P}_j$. The **Bayes
error** of the optimal (possibly randomized) test equals the total-variation distance between the
two hypotheses:
$$
\inf_{\psi}\; \mathbb{Q}\bigl[\psi(Z) \neq J\bigr]
  \;=\; \tfrac{1}{2}\bigl(1 - \|\mathbb{P}_1 - \mathbb{P}_0\|_{\mathrm{TV}}\bigr),
$$
where the infimum is over all tests and $\|\cdot\|_{\mathrm{TV}}$ is the total-variation distance.
Combining this identity with the estimation-to-testing reduction yields **Le Cam's two-point lower
bound**: for an increasing distortion function $\Phi$ and any pair $\theta_0, \theta_1$ whose
functional values $g(\theta_0), g(\theta_1)$ are $2\delta$-separated (i.e.
$\rho\bigl(g(\theta_0), g(\theta_1)\bigr) \geq 2\delta$), the minimax risk obeys
$$
\mathfrak{M}\bigl(\theta(\mathcal{P});\, \Phi \circ \rho\bigr)
  \;\geq\; \frac{\Phi(\delta)}{2}\,
    \bigl(1 - \|P_{\theta_0} - P_{\theta_1}\|_{\mathrm{TV}}\bigr).
$$

The Lean statements are over the extended nonnegative reals $[0,\infty]$, so the distortion
$\Phi : [0,\infty] \to [0,\infty]$ is assumed only `Monotone` (increasing) and the separation and
distance are measured by an extended pseudometric.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.13) (Bayes
error = total variation) and Eq. (15.14) (the two-point bound); the underlying reduction is
Proposition 15.1.

**Proof formalization notes.**
The Bayes-error / total-variation identity (`binary_testingError_eq_tvDist`, Eq. (15.13)) is proved
by identifying the infimum over Markov-kernel tests defining `bayesRisk` with the variational
representation `one_sub_tvDist_eq_iInf` of total variation:

* *Lower bound* — every Markov test `κ` contributes the feasible pair $(\kappa(\cdot)\{1\},
  \kappa(\cdot)\{0\})$, whose pointwise sum is $1$, to the variational infimum.
* *Upper bound* — conversely each feasible pair $(f_0, f_1)$ is realized, up to a value-decreasing
  truncation $a = \min(f_0, 1)$, by the explicit randomized test `binaryTest a`, which answers `1`
  with probability $a(x)$ and `0` with probability $1 - a(x)$.

The two-point bound (`minimax_two_point`, Eq. (15.14)) then specializes the general
estimation-to-testing inequality `minimax_ge_testing_error` to the two-point sub-family
$\theta\mathrm{fam} = [\theta_0, \theta_1]$ and rewrites its testing-error term via the identity
above.

**Bibliographic comments.**
The reduction of estimation to two-point testing originates with L. Le Cam, "Convergence of
Estimates Under Dimensionality Restrictions," *The Annals of Statistics* **1** (1973), no. 1,
38–53 (DOI 10.1214/aos/1193342380), which introduced what is now called *Le Cam's method* (or the
*two-point method*) for minimax lower bounds. The exact identification of the optimal binary-testing
error with the total-variation distance is the classical Neyman–Pearson consequence (the optimal
test thresholds the likelihood ratio), and is textbook folklore rather than attributable to a single
paper; Wainwright Eq. (15.13)–(15.14) is the synthesis used here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- The singleton mass of the uniform prior on `Fin 2` is `½`. -/
private lemma uniformPrior_two_apply (j : Fin 2) : uniformPrior 2 {j} = 2⁻¹ := by
  unfold uniformPrior
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j), PMF.uniformOfFintype_apply]
  simp [Fintype.card_fin]

/-- Integration against the uniform prior on `Fin 2` averages the two values. -/
private lemma uniformPrior_two_lintegral (g : Fin 2 → ℝ≥0∞) :
    ∫⁻ j, g j ∂(uniformPrior 2) = 2⁻¹ * (g 0 + g 1) := by
  rw [lintegral_fintype, Fin.sum_univ_two, uniformPrior_two_apply, uniformPrior_two_apply]
  ring

/-- **Randomized binary test** with acceptance function `a`: on input `x` it answers `1` with
probability `a x` and `0` with probability `1 − a x`. This realizes the `iInf`-over-Markov-kernels
in `bayesRisk` by the explicit family of estimators `Kernel 𝓧 (Fin 2)`. -/
private noncomputable def binaryTest (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) : Kernel 𝓧 (Fin 2) :=
  Kernel.mk (fun x => a x • Measure.dirac 1 + (1 - a x) • Measure.dirac 0)
    (by
      refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      exact (ha.mul measurable_const).add ((measurable_const.sub ha).mul measurable_const))

private lemma binaryTest_apply (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) (x : 𝓧) :
    binaryTest a ha x = a x • Measure.dirac 1 + (1 - a x) • Measure.dirac 0 := by
  unfold binaryTest; rw [Kernel.coe_mk]

private lemma binaryTest_apply_one (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) (x : 𝓧) :
    binaryTest a ha x {1} = a x := by
  rw [binaryTest_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton (1 : Fin 2)),
      Measure.dirac_apply' _ (measurableSet_singleton (1 : Fin 2))]
  simp

private lemma binaryTest_apply_zero (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) (x : 𝓧) :
    binaryTest a ha x {0} = 1 - a x := by
  rw [binaryTest_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton (0 : Fin 2)),
      Measure.dirac_apply' _ (measurableSet_singleton (0 : Fin 2))]
  simp

private lemma isMarkovKernel_binaryTest (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) (h1 : ∀ x, a x ≤ 1) :
    IsMarkovKernel (binaryTest a ha) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [binaryTest_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      smul_eq_mul, smul_eq_mul, measure_univ, measure_univ, mul_one, mul_one]
  exact add_tsub_cancel_of_le (h1 x)

/-- The average 0–1 risk of a Markov test `κ` against equally-weighted hypotheses `Q 0, Q 1`
equals `½ (Q 0[κ accepts `1`] + Q 1[κ accepts `0`])` (the two ways of being wrong). -/
private lemma avgRisk_zeroOneLoss_two (Q : Kernel (Fin 2) 𝓧) (κ : Kernel 𝓧 (Fin 2)) :
    avgRisk (zeroOneLoss 2) Q κ (uniformPrior 2)
      = 2⁻¹ * (∫⁻ x, κ x {1} ∂(Q 0) + ∫⁻ x, κ x {0} ∂(Q 1)) := by
  unfold avgRisk
  rw [uniformPrior_two_lintegral]
  have h0 : ∫⁻ y, zeroOneLoss 2 0 y ∂((κ ∘ₖ Q) 0) = ∫⁻ x, κ x {1} ∂(Q 0) := by
    rw [← Kernel.comp_apply' κ Q 0 (measurableSet_singleton 1), lintegral_fintype, Fin.sum_univ_two]
    simp [zeroOneLoss]
  have h1 : ∫⁻ y, zeroOneLoss 2 1 y ∂((κ ∘ₖ Q) 1) = ∫⁻ x, κ x {0} ∂(Q 1) := by
    rw [← Kernel.comp_apply' κ Q 1 (measurableSet_singleton 0), lintegral_fintype, Fin.sum_univ_two]
    simp [zeroOneLoss]
  rw [h0, h1]

/-- **Bayes error equals total variation** (Wainwright Eq. (15.13)): in a binary test with equally
weighted hypotheses `Q 0, Q 1`, the optimal (Bayes) error probability is `½(1 − ‖Q 0 − Q 1‖_TV)`.

The proof identifies the `iInf`-over-Markov-kernels defining `bayesRisk` with the variational
representation `one_sub_tvDist_eq_iInf` of total variation. Each Markov test `κ` contributes the
feasible pair `(κ·{1}, κ·{0})` (whose pointwise sum is `1`), giving the lower bound; conversely each
feasible `(f₀, f₁)` is realized — up to a value-decreasing truncation `a = min f₀ 1` — by the
explicit randomized test `binaryTest a`, giving the upper bound.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.13). -/
theorem binary_testingError_eq_tvDist (Q : Kernel (Fin 2) 𝓧) [IsMarkovKernel Q] :
    multiwayTestingError Q = 2⁻¹ * (1 - tvDist (Q 0) (Q 1)) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  refine le_antisymm ?_ ?_
  · -- Upper bound: each feasible `(f₀, f₁)` is realized by a randomized test.
    have key : 2 * multiwayTestingError Q ≤ 1 - tvDist (Q 0) (Q 1) := by
      rw [one_sub_tvDist_eq_iInf (Q 0) (Q 1)]
      refine le_iInf fun f₀ => le_iInf fun f₁ => le_iInf fun hf0 => le_iInf fun hf1 =>
        le_iInf fun hfeas => ?_
      have ha : Measurable (fun x => min (f₀ x) 1) := hf0.min measurable_const
      have h1 : ∀ x, (fun x => min (f₀ x) 1) x ≤ 1 := fun x => min_le_right _ _
      haveI : IsMarkovKernel (binaryTest (fun x => min (f₀ x) 1) ha) :=
        isMarkovKernel_binaryTest _ ha h1
      have e1 : ∫⁻ x, binaryTest (fun x => min (f₀ x) 1) ha x {1} ∂(Q 0)
          = ∫⁻ x, min (f₀ x) 1 ∂(Q 0) := lintegral_congr fun x => binaryTest_apply_one _ ha x
      have e0 : ∫⁻ x, binaryTest (fun x => min (f₀ x) 1) ha x {0} ∂(Q 1)
          = ∫⁻ x, (1 - min (f₀ x) 1) ∂(Q 1) := lintegral_congr fun x => binaryTest_apply_zero _ ha x
      calc 2 * multiwayTestingError Q
          ≤ 2 * avgRisk (zeroOneLoss 2) Q
              (binaryTest (fun x => min (f₀ x) 1) ha) (uniformPrior 2) := by
            gcongr; exact bayesRisk_le_avgRisk _ _ _ _
        _ = ∫⁻ x, min (f₀ x) 1 ∂(Q 0) + ∫⁻ x, (1 - min (f₀ x) 1) ∂(Q 1) := by
            rw [avgRisk_zeroOneLoss_two Q (binaryTest (fun x => min (f₀ x) 1) ha), e1, e0,
                ← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
        _ ≤ ∫⁻ x, f₀ x ∂(Q 0) + ∫⁻ x, f₁ x ∂(Q 1) := by
            refine add_le_add (lintegral_mono fun x => min_le_left _ _) (lintegral_mono fun x => ?_)
            rcases le_total (f₀ x) 1 with h | h
            · rw [min_eq_left h, tsub_le_iff_right, add_comm]; exact hfeas x
            · rw [min_eq_right h, tsub_self]; exact zero_le
    calc multiwayTestingError Q
        = 2⁻¹ * (2 * multiwayTestingError Q) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2 h2', one_mul]
      _ ≤ 2⁻¹ * (1 - tvDist (Q 0) (Q 1)) := mul_le_mul_right key _
  · -- Lower bound: every Markov test contributes a feasible pair to the variational `iInf`.
    unfold multiwayTestingError bayesRisk
    refine le_iInf fun κ => le_iInf fun hκ => ?_
    rw [avgRisk_zeroOneLoss_two Q κ]
    gcongr
    rw [one_sub_tvDist_eq_iInf (Q 0) (Q 1)]
    have hfeas : ∀ x, (1 : ℝ≥0∞) ≤ κ x {1} + κ x {0} := by
      intro x
      rw [← measure_union (Set.disjoint_singleton.mpr (by decide)) (measurableSet_singleton 0)]
      have huniv : ({1} ∪ {0} : Set (Fin 2)) = Set.univ := by ext i; fin_cases i <;> simp
      rw [huniv, measure_univ]
    exact iInf_le_of_le (fun x => κ x {1}) (iInf_le_of_le (fun x => κ x {0})
      (iInf_le_of_le (κ.measurable_coe (measurableSet_singleton 1))
        (iInf_le_of_le (κ.measurable_coe (measurableSet_singleton 0))
          (iInf_le_of_le hfeas le_rfl))))

/-- **Le Cam's two-point lower bound** (Wainwright Eq. (15.14)): for an increasing distortion `Φ`
and a pair `θ₀, θ₁` whose functional values are `2δ`-separated,
`M(θ(𝒫); Φ∘ρ) ≥ (Φ(δ)/2)(1 − ‖P_{θ₀} − P_{θ₁}‖_TV)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.14). -/
theorem minimax_two_point [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (θ₀ θ₁ : Θ) (δ : ℝ≥0∞)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.2.1, Eq. (15.14).
    (hΦ : Monotone Φ)
    -- USER-INPUT: the two functional values are `2δ`-separated; Wainwright §15.2.1.
    (hsep : 2 * δ ≤ edist (g θ₀) (g θ₁)) :
    Φ δ / 2 * (1 - tvDist (P θ₀) (P θ₁)) ≤ minimaxRiskDist Φ g P := by
  classical
  -- The two-point sub-family `θfam = ![θ₀, θ₁]`.
  set θfam : Fin 2 → Θ := ![θ₀, θ₁] with hfam
  have hθ : Measurable θfam := measurable_of_countable _
  haveI : IsMarkovKernel (P.comap θfam hθ) := Kernel.IsMarkovKernel.comap P hθ
  have h01 : 2 * δ ≤ edist (g (θfam 0)) (g (θfam 1)) := by simpa [θfam] using hsep
  have hsepf : IsSeparatedFamily g θfam δ := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
        | exact absurd rfl hjk
        | exact h01
        | (rw [edist_comm]; exact h01)
  have key := minimax_ge_testing_error Φ g P θfam hθ δ hΦ hsepf
  rw [binary_testingError_eq_tvDist (P.comap θfam hθ)] at key
  simp only [Kernel.comap_apply, θfam, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  calc Φ δ / 2 * (1 - tvDist (P θ₀) (P θ₁))
      = Φ δ * (2⁻¹ * (1 - tvDist (P θ₀) (P θ₁))) := by rw [div_eq_mul_inv, mul_assoc]
    _ ≤ minimaxRiskDist Φ g P := key

end StatLean.Minimaxity
