module
public import StatLean.Minimaxity.ForMathlib.TotalVariation
public import StatLean.Minimaxity.ForMathlib.HellingerDivergence
public import StatLean.AsymptoticStatistics.ForMathlib.RnDerivSqrt
public import StatLean.AsymptoticStatistics.ForMathlib.L2

@[expose] public section

/-!
# Le Cam's inequality (total variation controlled by Hellinger distance)

For probability measures $\mathbb{P}, \mathbb{Q}$, the total variation distance is bounded above by
the Hellinger distance through
$$\|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}} \;\le\; H(\mathbb{P}\,\|\,\mathbb{Q})\,
  \sqrt{1 - \tfrac{1}{4}\,H^2(\mathbb{P}\,\|\,\mathbb{Q})},$$
where $H = \sqrt{H^2}$ is the (unsquared) Hellinger distance and $H^2(\mathbb{P}\,\|\,\mathbb{Q})
= \int (\sqrt{p} - \sqrt{q})^2 \, d\xi$ is the squared Hellinger distance against a common
dominating measure $\xi$. This is the upper half of the classical pair of Hellinger–total-variation
inequalities.

In the Lean statement the squared Hellinger distance `sqHellinger μ ν` plays the role of $H^2$, the
unsquared distance is its `ℝ≥0∞` square root `rpow (1/2)`, and the dominating measure is taken to be
$\xi = \mu + \nu$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.3,
Eq. (15.10). Wainwright leaves the proof as Exercise 15.5.

**Proof formalization notes.** The argument follows Exercise 15.5. Writing $p = d\mathbb{P}/d\xi$,
$q = d\mathbb{Q}/d\xi$ for the densities against $\xi = \mu + \nu$, factor the integrand pointwise as
$|p - q| = |\sqrt{p} - \sqrt{q}| \cdot (\sqrt{p} + \sqrt{q})$ and apply Cauchy–Schwarz:
$$\tfrac{1}{2}\!\int |p - q|\, d\xi \;\le\; \tfrac{1}{2}\,
  \sqrt{\textstyle\int (\sqrt{p} - \sqrt{q})^2 d\xi}\;\cdot\;
  \sqrt{\textstyle\int (\sqrt{p} + \sqrt{q})^2 d\xi}.$$
The "cross" integral is computed via the identity $\int (\sqrt{p} + \sqrt{q})^2 d\xi
= 2 + 2\int \sqrt{pq}\, d\xi = 4 - H^2$, which turns the second factor into $2\sqrt{1 - H^2/4}$ and
yields the stated bound. The development is layered: `lecam_real_bound` is the real-analytic core
(Cauchy–Schwarz plus the $4 - H^2$ identity over `ℝ`); `lecam_half_lintegral_le` is the Cauchy–Schwarz
crux transported to the `ℝ≥0∞` half-`L¹` form; and the public theorem `lecam_tv_le_hellinger`
follows by the density form `tvDist_eq_half_lintegral`.

**Bibliographic comments.** L. Le Cam, "Convergence of Estimates Under Dimensionality
Restrictions," *The Annals of Statistics* **1**(1), 38–53, 1973. Le Cam introduced the Hellinger
affinity / Hellinger distance as the controlling quantity for testing and estimation rates, and the
two-sided comparison between total variation and Hellinger distance — of which the inequality
formalized here ($\mathrm{TV} \le H\sqrt{1 - H^2/4}$) is the upper bound — originates in this line of
work; the complementary lower bound $H^2/2 \le \mathrm{TV}$ is the other half. The sharp constants and
the clean Cauchy–Schwarz derivation reproduced here are now standard textbook material (Wainwright
§15.1.3); the result is commonly attributed to Le Cam rather than to a single equation in the
original paper.
-/

open MeasureTheory
open scoped ENNReal
open AsymptoticStatistics.ForMathlib.RnDerivSqrt
open AsymptoticStatistics.ForMathlib.HellingerProduct
open AsymptoticStatistics.L2Utils

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- Pointwise factorisation `|a − b| = |√a − √b| · (√a + √b)` for `a, b ≥ 0`. This is the
Cauchy–Schwarz splitting underlying Le Cam's inequality. -/
private lemma abs_sub_eq_abs_sqrt_sub_mul_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| = |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
  have h1 : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    have hpa := Real.mul_self_sqrt ha
    have hpb := Real.mul_self_sqrt hb
    nlinarith [hpa, hpb]
  rw [← h1, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt a + Real.sqrt b)]

/-- **Real-analytic core of Le Cam's inequality** (Wainwright Exercise 15.5): the half-`L¹`
distance `½ ∫ |p − q| dξ` is bounded by `√(H²) · √(1 − H²/4)`, where `H² = ∫ (√p − √q)² dξ`.
Proved by Cauchy–Schwarz on `|p − q| = |√p − √q| · (√p + √q)` together with the identity
`∫ (√p + √q)² dξ = 4 − H²`. -/
private lemma lecam_real_bound (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ ω, |(μ.rnDeriv (μ + ν) ω).toReal - (ν.rnDeriv (μ + ν) ω).toReal| ∂(μ + ν)) / 2
      ≤ Real.sqrt (∫ ω, (Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
                  - Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal) ^ 2 ∂(μ + ν))
        * Real.sqrt (1 - (∫ ω, (Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
                  - Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal) ^ 2 ∂(μ + ν)) / 4) := by
  set ξ : Measure α := μ + ν with hξ
  have hμ : μ ≪ ξ := rfl.absolutelyContinuous.add_right _
  have hν : ν ≪ ξ := rfl.absolutelyContinuous.add_right' _
  set P : α → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal with hP
  set Q : α → ℝ := fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal with hQ
  have hPnn : ∀ ω, 0 ≤ P ω := fun ω => Real.sqrt_nonneg _
  have hQnn : ∀ ω, 0 ≤ Q ω := fun ω => Real.sqrt_nonneg _
  have hPmem : MemLp P 2 ξ := memLp_sqrt_rnDeriv hμ
  have hQmem : MemLp Q 2 ξ := memLp_sqrt_rnDeriv hν
  -- Key real quantities.
  set Hr : ℝ := ∫ ω, (P ω - Q ω) ^ 2 ∂ξ with hHr
  set A : ℝ := ∫ ω, P ω * Q ω ∂ξ with hA
  have hPQint : Integrable (fun ω => P ω * Q ω) ξ := hPmem.integrable_mul hQmem
  have hsq_int : Integrable (fun ω => (P ω - Q ω) ^ 2) ξ := (hPmem.sub hQmem).integrable_sq
  have hper : Hr = 2 - 2 * A := integral_per_sample_residual_sq_eq hμ hν
  -- `∫ (P + Q)² dξ = 4 − Hr`.
  have hGsq : ∫ ω, (P ω + Q ω) ^ 2 ∂ξ = 4 - Hr := by
    have hexp : ∀ ω, (P ω + Q ω) ^ 2 = (P ω - Q ω) ^ 2 + 4 * (P ω * Q ω) := fun ω => by ring
    calc ∫ ω, (P ω + Q ω) ^ 2 ∂ξ
        = ∫ ω, ((P ω - Q ω) ^ 2 + 4 * (P ω * Q ω)) ∂ξ :=
          integral_congr_ae (Filter.Eventually.of_forall hexp)
      _ = (∫ ω, (P ω - Q ω) ^ 2 ∂ξ) + ∫ ω, 4 * (P ω * Q ω) ∂ξ :=
          integral_add hsq_int (hPQint.const_mul 4)
      _ = Hr + 4 * A := by rw [integral_const_mul, ← hHr, ← hA]
      _ = 4 - Hr := by rw [hper]; ring
  -- L² memberships of the two Cauchy–Schwarz factors.
  have hf : MemLp (fun ω => |P ω - Q ω|) 2 ξ := (hPmem.sub hQmem).abs
  have hg : MemLp (fun ω => P ω + Q ω) 2 ξ := hPmem.add hQmem
  -- `|p − q| = |P − Q| · (P + Q)` pointwise.
  have hpt : ∀ ω, |(μ.rnDeriv ξ ω).toReal - (ν.rnDeriv ξ ω).toReal|
                = |P ω - Q ω| * (P ω + Q ω) := fun ω =>
    abs_sub_eq_abs_sqrt_sub_mul_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hD : (∫ ω, |(μ.rnDeriv ξ ω).toReal - (ν.rnDeriv ξ ω).toReal| ∂ξ)
              = ∫ ω, |P ω - Q ω| * (P ω + Q ω) ∂ξ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- Cauchy–Schwarz.
  have hCS := abs_integral_mul_le_sqrt_integral_sq ξ hf hg
  have hint_nn : 0 ≤ ∫ ω, |P ω - Q ω| * (P ω + Q ω) ∂ξ :=
    integral_nonneg (fun ω => mul_nonneg (abs_nonneg _) (add_nonneg (hPnn ω) (hQnn ω)))
  have hf2 : (∫ ω, |P ω - Q ω| ^ 2 ∂ξ) = Hr := by simp_rw [sq_abs]; rw [hHr]
  rw [hf2, hGsq, abs_of_nonneg hint_nn] at hCS
  -- `√(4 − Hr) = 2 √(1 − Hr/4)`.
  have hHr_le2 : Hr ≤ 2 := by
    rw [hper]
    have : 0 ≤ A := hA ▸ integral_nonneg (fun ω => mul_nonneg (hPnn ω) (hQnn ω))
    linarith
  have hsqrt4 : Real.sqrt (4 - Hr) = 2 * Real.sqrt (1 - Hr / 4) := by
    rw [show (4:ℝ) - Hr = 4 * (1 - Hr / 4) from by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    congr 1
    rw [show (4:ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsqrt4, show Real.sqrt Hr * (2 * Real.sqrt (1 - Hr / 4))
        = 2 * (Real.sqrt Hr * Real.sqrt (1 - Hr / 4)) from by ring] at hCS
  rw [hD]
  linarith

/-- **Cauchy–Schwarz crux of Le Cam's inequality** (Wainwright Exercise 15.5).

Writing `p = dℙ/dξ`, `q = dℚ/dξ` for the densities against `ξ = ℙ + ℚ`, the half-`L¹` form of
total variation is bounded by the Hellinger product via Cauchy–Schwarz on the factorization
`|p − q| = |√p − √q| · (√p + √q)`:
`½ ∫ |p − q| dξ ≤ ½ √(∫ (√p − √q)² dξ) · √(∫ (√p + √q)² dξ)`,
and `∫ (√p + √q)² dξ = 2 + 2 ∫ √(pq) dξ = 4 − H²`, giving the stated bound. This is the genuine
analytic core; the public theorem `lecam_tv_le_hellinger` follows by the density form
`tvDist_eq_half_lintegral`. -/
private lemma lecam_half_lintegral_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν)
      ≤ (sqHellinger μ ν) ^ (1 / 2 : ℝ) * (1 - sqHellinger μ ν / 4) ^ (1 / 2 : ℝ) := by
  have hμ : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hν : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  set D : ℝ := ∫ ω, |(μ.rnDeriv (μ + ν) ω).toReal - (ν.rnDeriv (μ + ν) ω).toReal| ∂(μ + ν)
    with hDdef
  set Hr : ℝ := ∫ ω, (Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
                  - Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal) ^ 2 ∂(μ + ν) with hHrdef
  -- Integrabilities.
  have hp_int : Integrable (fun ω => (μ.rnDeriv (μ + ν) ω).toReal) (μ + ν) :=
    Measure.integrable_toReal_rnDeriv
  have hq_int : Integrable (fun ω => (ν.rnDeriv (μ + ν) ω).toReal) (μ + ν) :=
    Measure.integrable_toReal_rnDeriv
  have habs_int : Integrable (fun ω => |(μ.rnDeriv (μ + ν) ω).toReal
                    - (ν.rnDeriv (μ + ν) ω).toReal|) (μ + ν) := (hp_int.sub hq_int).abs
  have hsq_int : Integrable (fun ω => (Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
                  - Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal) ^ 2) (μ + ν) :=
    (hellinger_per_sample_residual_memLp_two hμ hν).integrable_sq
  -- `∫⁻ ofReal|p − q| = ofReal D`.
  have hLH : ∫⁻ x, ENNReal.ofReal |(μ.rnDeriv (μ + ν) x).toReal
              - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν) = ENNReal.ofReal D :=
    (ofReal_integral_eq_lintegral_ofReal habs_int
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
  -- `sqHellinger μ ν = ofReal Hr`.
  have hsqH : sqHellinger μ ν = ENNReal.ofReal Hr := by
    rw [show sqHellinger μ ν = ∫⁻ x, ENNReal.ofReal
          ((Real.sqrt (μ.rnDeriv (μ + ν) x).toReal
            - Real.sqrt (ν.rnDeriv (μ + ν) x).toReal) ^ 2) ∂(μ + ν) from rfl]
    exact (ofReal_integral_eq_lintegral_ofReal hsq_int
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
  -- Bounds on `Hr`.
  have hHr_nn : 0 ≤ Hr := integral_nonneg (fun _ => sq_nonneg _)
  have hHr_le2 : Hr ≤ 2 := by
    have h := hsqH ▸ sqHellinger_le_two μ ν
    rwa [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
      ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h
  have h14nn : 0 ≤ 1 - Hr / 4 := by linarith
  -- Rewrite the goal into `ofReal` form.
  rw [hLH, hsqH]
  have hL : (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal D = ENNReal.ofReal (D / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat,
        div_eq_mul_inv, mul_comm]
  have hRb1 : (ENNReal.ofReal Hr) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt Hr) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hHr_nn (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow]
  have h14 : (1:ℝ≥0∞) - ENNReal.ofReal Hr / 4 = ENNReal.ofReal (1 - Hr / 4) := by
    rw [ENNReal.ofReal_sub 1 (by positivity : (0:ℝ) ≤ Hr / 4), ENNReal.ofReal_one,
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4), ENNReal.ofReal_ofNat]
  have hRb2 : (1 - ENNReal.ofReal Hr / 4) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (1 - Hr / 4)) := by
    rw [h14, ENNReal.ofReal_rpow_of_nonneg h14nn (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow]
  rw [hL, hRb1, hRb2, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hDdef, hHrdef]
  exact lecam_real_bound μ ν

/-- **Le Cam's inequality** (Wainwright Lemma 15.3, Eq. (15.10)):
`‖ℙ − ℚ‖_TV ≤ H(ℙ ‖ ℚ) · √(1 − H²(ℙ ‖ ℚ)/4)`, with `H = √(H²)` the Hellinger distance.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.3. -/
theorem lecam_tv_le_hellinger (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν
      ≤ (sqHellinger μ ν) ^ (1 / 2 : ℝ) * (1 - sqHellinger μ ν / 4) ^ (1 / 2 : ℝ) := by
  rw [tvDist_eq_half_lintegral]
  exact lecam_half_lintegral_le μ ν

end StatLean.Minimaxity
