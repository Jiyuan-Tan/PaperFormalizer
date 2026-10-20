module
public import StatLean.ConcentrationInequalities.Bernstein.Defs
public import StatLean.ConcentrationInequalities.SubExponential.Defs

@[expose] public section

/-!
# Bernstein condition implies a sub-exponential moment generating function bound

Let $X$ be a mean-zero random variable on a probability space satisfying the **Bernstein
moment condition** with variance proxy $\sigma^2$ and scale parameter $b$, i.e. there exist
constants such that the centered moments are controlled by
$$\mathbb{E}\,|X|^m \;\le\; \tfrac{1}{2}\,\sigma^2\, m!\, b^{\,m-2}, \qquad m \ge 3,$$
together with $\mathbb{E}[X] = 0$ and $\operatorname{Var}(X) = \sigma^2$. Then $X$ is
**sub-exponential** with parameter $\alpha = 2\,(\sigma \vee b)$: for every $\lambda$ with
$|\lambda| \le 1/\alpha$, the random variable $e^{\lambda X}$ is integrable and the moment
generating function obeys
$$\mathbb{E}\,e^{\lambda X} \;\le\; \exp\!\bigl(\tfrac{1}{2}\,\lambda^2\,\alpha^2\bigr).$$
Here $\sigma \vee b = \max(\sigma, b)$ and $\sigma = \sqrt{\sigma^2}$ is the standard deviation.

**Deviation from the originally stated constant.** A naive transcription asks for
$\alpha = 2\,(\sigma^2 \vee b)$, mixing the *variance* $\sigma^2$ (quadratic units) with the
linear scale $b$. That formula fails whenever $\sigma^2 > 2\,(\sigma^2 \vee b)^2$ — e.g. with
$\sigma^2 = 0.01$ and the minimal admissible $b = 1/30$ one gets
$2\,(\sigma^2 \vee b)^2 \approx 0.0022 < 0.01$. The provable parameter uses the **standard
deviation**, $\alpha = 2\,(\sigma \vee b)$ (Lu-BDA §6.1 implicitly works with the standard
deviation in the geometric-series range condition). Writing $s := \sigma \vee b$:
* **Range** — $|\lambda| \le 1/\alpha = 1/(2s)$ implies $|\lambda| \le 1/(2b)$ (since
  $s \ge b$), so $|\lambda|\,b \le 1/2$ and the Bernstein geometric series converges.
* **Variance bound** — $\sigma^2 = (\sqrt{\sigma^2})^2 \le s^2 \le 2s^2 = \alpha^2/2$, so
  $\exp(\lambda^2 \sigma^2) \le \exp(\lambda^2 \alpha^2/2)$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 6 (Bernstein and Maximal Inequalities), §6.1,
Theorem 6.1 (Bernstein Inequality), Step 1 (Bernstein condition, Definition 6.1, ⇒
sub-exponential moment generating function).
Compare M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
University Press, 2019, Chapter 2 (Basic tail and concentration bounds), §2.1.3 (sub-exponential
variables and Bernstein's condition), Eq. (2.16)–(2.17).

**Proof formalization notes.**
The proof route avoids `hasFPowerSeriesAt_mgf`. `bernstein_key` below covers both the
integrability of $e^{\lambda X}$ and the MGF bound. Rather than fight the
`FormalMultilinearSeries.radius` bookkeeping of `hasFPowerSeriesAt_mgf`, we use the elementary
monotone-convergence route enabled by the `∫⁻` form of the moment bound (`Bernstein/Defs.lean`):

* Expand `exp(|l|·|X|) - 1 - |l|·|X| = ∑_{k≥0} (|l|·|X|)^{k+2}/(k+2)!` pointwise, push through
  `MeasureTheory.lintegral_tsum` (Tonelli), pull constants out with `lintegral_const_mul`, and
  bound each moment with `HasBernsteinCondition.moment_le` (extended to `k = 2` via the
  variance).  The resulting geometric series `∑ (|l|b)^n` converges since `|l|·b ≤ 1/2`, giving
  `∫⁻ ofReal(exp(|l||X|) - 1 - |l||X|) ≤ ofReal(σ2·l²)`.
* Integrability of `exp(l·X)` follows by dominating `exp(l·X) ≤ exp(|l|·|X|) = 1 + |l||X| +
  (tail)`, all three pieces integrable.
* The MGF bound: `mgf = 1 + E[exp(lX) - 1 - lX] ≤ 1 + E[exp(|l||X|) - 1 - |l||X|] ≤ 1 + σ2·l²
  ≤ exp(σ2·l²) ≤ exp(l²·α²/2)` (using `E[X] = 0` and `σ2 ≤ α²/2`).

Key Mathlib lemmas: `MeasureTheory.lintegral_tsum`, `ENNReal.ofReal_tsum_of_nonneg`,
`lintegral_const_mul`, `ENNReal.tsum_geometric`, `NormedSpace.exp_eq_tsum_div`,
`Summable.sum_add_tsum_nat_add`, `integral_eq_lintegral_of_nonneg_ae`.

**Bibliographic comments.**
This is folklore with no single seminal paper. The moment ("Bernstein") condition and
its use to bound the moment generating function trace back to S. N. Bernstein's work on
probability inequalities in the 1920s–1930s (S. N. Bernstein, *The Theory of Probabilities*,
Moscow–Leningrad, 1927; reprinted in his collected works). The modern packaging — that the
Bernstein moment condition is equivalent to sub-exponentiality and yields the bound
$\mathbb{E}\,e^{\lambda X} \le \exp(\lambda^2 \alpha^2/2)$ on the range $|\lambda| \le 1/\alpha$
— is standard and appears, with the constants used here up to the variance-vs-standard-deviation
convention, in M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, §2.1.3. It is reproduced as Step 1 of Lu-BDA §6.1; no original
research-paper theorem number is attached.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {X : Ω → ℝ} {σ2 b : ℝ≥0} {μ : Measure Ω}

/-! ### The key lemma -/

set_option maxHeartbeats 800000 in
-- The full closed-form proof is long (≈40 `have`s sharing one budget); raising the limit
-- avoids a cumulative timeout. No single step is expensive.
/-- For `|l| ≤ 1 / α` with `α = 2 * (√σ2 ⊔ b)`, the exponential `ω ↦ exp(l · X ω)` is
integrable and the MGF satisfies the sub-exponential bound `mgf X μ l ≤ exp(l²·α²/2)`.

Proved by the elementary monotone-convergence route (see the module header): expand the
exponential tail as a power series, push through `lintegral_tsum`, and sum the resulting
geometric series, which converges because `|l|·b ≤ 1/2` on the allowed range.

(`maxHeartbeats` is raised because the whole closed-form proof is long; no single step is
expensive.) -/
private lemma bernstein_key [IsProbabilityMeasure μ]
    -- USER-INPUT: `X` measurable (random variable); Lu-BDA §6.1 (the book tacitly assumes `X`
    -- is a random variable; without it the Bochner-integral hypotheses are junk `0`).
    (hX : Measurable X)
    (hB : HasBernsteinCondition X σ2 b μ)
    {l : ℝ}
    (hl : |l| ≤ 1 / ((2 * (NNReal.sqrt σ2 ⊔ b) : ℝ≥0) : ℝ)) :
    Integrable (fun ω => Real.exp (l * X ω)) μ ∧
    mgf X μ l ≤ Real.exp (l ^ 2 * ((2 * (NNReal.sqrt σ2 ⊔ b) : ℝ≥0) : ℝ) ^ 2 / 2) := by
  classical
  set s : ℝ≥0 := NNReal.sqrt σ2 ⊔ b with hs_def
  -- ### Real-number facts about the parameter `s = √σ2 ⊔ b`.
  have hb_le_s : (b : ℝ) ≤ (s : ℝ) := by exact_mod_cast (le_sup_right : b ≤ s)
  have hσ_le_s2 : (σ2 : ℝ) ≤ (s : ℝ) ^ 2 := by
    have h2 : σ2 ≤ s ^ 2 := by
      calc σ2 = NNReal.sqrt σ2 ^ 2 := (NNReal.sq_sqrt σ2).symm
        _ ≤ s ^ 2 := by gcongr; exact le_sup_left
    exact_mod_cast h2
  have hlb_nonneg : (0 : ℝ) ≤ |l| * (b : ℝ) := mul_nonneg (abs_nonneg l) (NNReal.coe_nonneg b)
  have hlb : |l| * (b : ℝ) ≤ 1 / 2 := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with hs0 | hs0
    · -- (s : ℝ) = 0
      have hb0 : (b : ℝ) = 0 := le_antisymm (hs0 ▸ hb_le_s) (NNReal.coe_nonneg b)
      rw [hb0, mul_zero]; norm_num
    · -- 0 < (s : ℝ)
      have hα : ((2 * s : ℝ≥0) : ℝ) = 2 * (s : ℝ) := by push_cast; ring
      rw [hα] at hl
      have h2s : (0 : ℝ) < 2 * (s : ℝ) := by linarith
      have hstep : |l| * (b : ℝ) ≤ (1 / (2 * (s : ℝ))) * (b : ℝ) :=
        mul_le_mul_of_nonneg_right hl (NNReal.coe_nonneg b)
      refine hstep.trans ?_
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h2s]
      nlinarith [hb_le_s]
  -- ### The exponential power series and its `+2`-reindexing.
  have hexp_tsum : ∀ u : ℝ, Real.exp u = ∑' n : ℕ, u ^ n / (Nat.factorial n : ℝ) := by
    intro u
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun NormedSpace.exp_eq_tsum_div u
  have hreindex : ∀ u : ℝ,
      (∑' n : ℕ, u ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) = Real.exp u - 1 - u := by
    intro u
    have hsum := (Real.summable_pow_div_factorial u).sum_add_tsum_nat_add 2
    rw [← hexp_tsum u] at hsum
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hsum
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
      Nat.factorial_one] at hsum
    linarith
  -- ### `X²` is integrable and its lower-Lebesgue integral is `σ2`.
  have hX2int : Integrable (fun ω => (X ω) ^ 2) μ := by
    rcases eq_or_ne σ2 0 with hσ | hσ
    · -- σ2 = 0 forces X = 0 a.e. (from the third moment bound).
      have h3 := hB.moment_le 3 (by norm_num)
      rw [hσ] at h3
      simp only [NNReal.coe_zero, zero_div, zero_mul, ENNReal.ofReal_zero,
        nonpos_iff_eq_zero] at h3
      rw [lintegral_eq_zero_iff' ((hX.abs.pow_const 3).ennreal_ofReal.aemeasurable)] at h3
      have hae : (fun ω => (X ω) ^ 2) =ᵐ[μ] 0 := by
        filter_upwards [h3] with ω hω
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
        have hcube : |X ω| ^ 3 = 0 := le_antisymm hω (by positivity)
        have hXabs : |X ω| = 0 := by
          have := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
          exact this
        simp [abs_eq_zero.mp hXabs]
      exact (integrable_zero Ω ℝ μ).congr hae.symm
    · -- σ2 ≠ 0: the variance `∫ X² = σ2 ≠ 0` is nonzero, so `X²` is integrable.
      by_contra hni
      have h0 := integral_undef hni
      rw [hB.variance_eq] at h0
      exact hσ (by exact_mod_cast h0)
  have hM2 : ∫⁻ ω, ENNReal.ofReal ((X ω) ^ 2) ∂μ = ENNReal.ofReal (σ2 : ℝ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hX2int
      (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω)), hB.variance_eq]
  -- ### Moment bound `E|X|^m ≤ (σ2/2)·m!·b^(m-2)` for all `m ≥ 2` (k=2 from the variance).
  have hM : ∀ m : ℕ, 2 ≤ m →
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ m) ∂μ
        ≤ ENNReal.ofReal ((σ2 : ℝ) / 2 * (Nat.factorial m : ℝ) * (b : ℝ) ^ (m - 2)) := by
    intro m hm
    rcases eq_or_lt_of_le hm with h2 | h3
    · subst h2
      have heq : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ 2) ∂μ = ENNReal.ofReal (σ2 : ℝ) := by
        simp_rw [sq_abs]; exact hM2
      rw [heq]
      apply ENNReal.ofReal_le_ofReal
      have hfac : ((Nat.factorial 2 : ℝ)) = 2 := by norm_num [Nat.factorial]
      rw [hfac, show (2 : ℕ) - 2 = 0 from rfl, pow_zero, mul_one]
      linarith
    · exact hB.moment_le m h3
  -- ### The core ENNReal bound on the exponential tail.
  have hmeas_term : ∀ n : ℕ, Measurable fun ω =>
      ENNReal.ofReal ((|l| * |X ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) :=
    fun n => (((hX.abs.const_mul |l|).pow_const (n + 2)).div_const _).ennreal_ofReal
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (|l| * |X ω|) - 1 - |l| * |X ω|)
      = ∑' n : ℕ, ENNReal.ofReal ((|l| * |X ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) := by
    intro ω
    rw [← hreindex (|l| * |X ω|),
      ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        ((summable_nat_add_iff 2).mpr (Real.summable_pow_div_factorial (|l| * |X ω|)))]
  have per_term : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((|l| * |X ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) ∂μ
        ≤ ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2) * (ENNReal.ofReal (|l| * (b : ℝ))) ^ n := by
    intro n
    have hrw : ∀ ω, ENNReal.ofReal ((|l| * |X ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
        = ENNReal.ofReal (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
            * ENNReal.ofReal (|X ω| ^ (n + 2)) := by
      intro ω
      rw [mul_pow,
        show |l| ^ (n + 2) * |X ω| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)
          = (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) * |X ω| ^ (n + 2) by ring,
        ENNReal.ofReal_mul (by positivity)]
    have hpowl : |l| ^ (n + 2) = l ^ 2 * |l| ^ n := by rw [pow_add, sq_abs]; ring
    have hAB : (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
          * ((σ2 : ℝ) / 2 * (Nat.factorial (n + 2) : ℝ) * (b : ℝ) ^ (n + 2 - 2))
        = (σ2 : ℝ) / 2 * l ^ 2 * (|l| * (b : ℝ)) ^ n := by
      rw [Nat.add_sub_cancel, hpowl, mul_pow]
      have hfac : (Nat.factorial (n + 2) : ℝ) ≠ 0 := by positivity
      field_simp
    calc ∫⁻ ω, ENNReal.ofReal ((|l| * |X ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
              * ENNReal.ofReal (|X ω| ^ (n + 2)) ∂μ := by simp_rw [hrw]
      _ = ENNReal.ofReal (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
              * ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (n + 2)) ∂μ :=
            lintegral_const_mul _ ((hX.abs.pow_const (n + 2)).ennreal_ofReal)
      _ ≤ ENNReal.ofReal (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
              * ENNReal.ofReal ((σ2 : ℝ) / 2 * (Nat.factorial (n + 2) : ℝ)
                  * (b : ℝ) ^ (n + 2 - 2)) := by
            gcongr
            exact hM (n + 2) (by omega)
      _ = ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2) * (ENNReal.ofReal (|l| * (b : ℝ))) ^ n := by
            rw [← ENNReal.ofReal_mul (by positivity), hAB,
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (σ2 : ℝ) / 2 * l ^ 2),
              ENNReal.ofReal_pow hlb_nonneg]
  have hgeom : (1 - ENNReal.ofReal (|l| * (b : ℝ)))⁻¹ ≤ 2 := by
    have hr : ENNReal.ofReal (|l| * (b : ℝ)) ≤ 2⁻¹ := by
      calc ENNReal.ofReal (|l| * (b : ℝ)) ≤ ENNReal.ofReal (2⁻¹ : ℝ) :=
            ENNReal.ofReal_le_ofReal (by linarith [hlb])
        _ = (2 : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    have h1 : (2 : ℝ≥0∞)⁻¹ ≤ 1 - ENNReal.ofReal (|l| * (b : ℝ)) := by
      calc (2 : ℝ≥0∞)⁻¹ = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
        _ ≤ 1 - ENNReal.ofReal (|l| * (b : ℝ)) := tsub_le_tsub_left hr 1
    calc (1 - ENNReal.ofReal (|l| * (b : ℝ)))⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹)⁻¹ := ENNReal.inv_le_inv' h1
      _ = 2 := inv_inv _
  have hSbound : ∫⁻ ω, ENNReal.ofReal (Real.exp (|l| * |X ω|) - 1 - |l| * |X ω|) ∂μ
      ≤ ENNReal.ofReal ((σ2 : ℝ) * l ^ 2) := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (|l| * |X ω|) - 1 - |l| * |X ω|) ∂μ
        = ∑' n : ℕ, ∫⁻ ω,
            ENNReal.ofReal ((|l| * |X ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) ∂μ := by
          simp_rw [hpt]
          rw [lintegral_tsum (fun n => (hmeas_term n).aemeasurable)]
      _ ≤ ∑' n : ℕ, ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2)
              * (ENNReal.ofReal (|l| * (b : ℝ))) ^ n := ENNReal.tsum_le_tsum per_term
      _ = ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2)
              * ∑' n : ℕ, (ENNReal.ofReal (|l| * (b : ℝ))) ^ n := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2)
              * (1 - ENNReal.ofReal (|l| * (b : ℝ)))⁻¹ := by rw [ENNReal.tsum_geometric]
      _ ≤ ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2) * 2 := by gcongr
      _ = ENNReal.ofReal ((σ2 : ℝ) * l ^ 2) := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
              ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (σ2 : ℝ) / 2 * l ^ 2)]
            congr 1; ring
  -- ### Integrability of the tail `S(X) = exp(|l||X|) - 1 - |l||X|`.
  have hS_meas : Measurable fun ω => Real.exp (|l| * |X ω|) - 1 - |l| * |X ω| := by
    have h1 : Measurable fun ω => |l| * |X ω| := hX.abs.const_mul |l|
    exact (h1.exp.sub measurable_const).sub h1
  have hSnonneg : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => Real.exp (|l| * |X ω|) - 1 - |l| * |X ω| :=
    Filter.Eventually.of_forall fun ω => by
      have := Real.add_one_le_exp (|l| * |X ω|); simpa using by linarith
  have hSint : Integrable (fun ω => Real.exp (|l| * |X ω|) - 1 - |l| * |X ω|) μ := by
    refine ⟨hS_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hSnonneg]
    exact lt_of_le_of_lt hSbound ENNReal.ofReal_lt_top
  have hS_int_bound : ∫ ω, (Real.exp (|l| * |X ω|) - 1 - |l| * |X ω|) ∂μ ≤ (σ2 : ℝ) * l ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae hSnonneg hS_meas.aestronglyMeasurable]
    calc (∫⁻ ω, ENNReal.ofReal (Real.exp (|l| * |X ω|) - 1 - |l| * |X ω|) ∂μ).toReal
        ≤ (ENNReal.ofReal ((σ2 : ℝ) * l ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hSbound
      _ = (σ2 : ℝ) * l ^ 2 := ENNReal.toReal_ofReal (by positivity)
  -- ### Integrability of `X` and of `exp(l·X)`.
  have hXint : Integrable X μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hX2int)
      hX.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    nlinarith [sq_nonneg (|X ω| - 1), abs_nonneg (X ω), sq_abs (X ω)]
  have hexpAbsInt : Integrable (fun ω => Real.exp (|l| * |X ω|)) μ := by
    have heq : (fun ω => Real.exp (|l| * |X ω|))
        = fun ω => 1 + |l| * |X ω| + (Real.exp (|l| * |X ω|) - 1 - |l| * |X ω|) := by
      funext ω; ring
    rw [heq]
    exact ((integrable_const (1 : ℝ)).add (hXint.abs.const_mul |l|)).add hSint
  have hexpInt : Integrable (fun ω => Real.exp (l * X ω)) μ := by
    refine hexpAbsInt.mono' ((hX.const_mul l).exp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by rw [abs_mul]))
  -- ### Pointwise `R(X) ≤ S(X)` and the MGF bound.
  have hRmono : ∀ u : ℝ, Real.exp u - 1 - u ≤ Real.exp |u| - 1 - |u| := by
    intro u
    have hsu : Summable (fun n : ℕ => u ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) :=
      (summable_nat_add_iff 2).mpr (Real.summable_pow_div_factorial u)
    have hsau : Summable (fun n : ℕ => |u| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) :=
      (summable_nat_add_iff 2).mpr (Real.summable_pow_div_factorial |u|)
    have hterm : ∀ n : ℕ, u ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)
        ≤ |u| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
      intro n
      have hnum : u ^ (n + 2) ≤ |u| ^ (n + 2) :=
        (le_abs_self _).trans (le_of_eq (abs_pow u (n + 2)))
      exact div_le_div_of_nonneg_right hnum (by positivity)
    rw [← hreindex u, ← hreindex |u|]
    exact hsu.tsum_le_tsum hterm hsau
  have hRmono' : ∀ ω, Real.exp (l * X ω) - 1 - l * X ω
      ≤ Real.exp (|l| * |X ω|) - 1 - |l| * |X ω| := by
    intro ω
    have := hRmono (l * X ω)
    rwa [abs_mul] at this
  have hRint : Integrable (fun ω => Real.exp (l * X ω) - 1 - l * X ω) μ :=
    (hexpInt.sub (integrable_const 1)).sub (hXint.const_mul l)
  have hmgf_eq : mgf X μ l = 1 + ∫ ω, (Real.exp (l * X ω) - 1 - l * X ω) ∂μ := by
    have h1lX : Integrable (fun ω => 1 + l * X ω) μ :=
      (integrable_const 1).add (hXint.const_mul l)
    have hone : ∫ ω, (1 + l * X ω) ∂μ = 1 := by
      rw [integral_add (integrable_const 1) (hXint.const_mul l), integral_const_mul,
        hB.mean_zero]
      simp
    have hsplit : (fun ω => Real.exp (l * X ω))
        = fun ω => (1 + l * X ω) + (Real.exp (l * X ω) - 1 - l * X ω) := by funext ω; ring
    simp only [mgf]
    rw [hsplit, integral_add h1lX hRint, hone]
  have hmgf : mgf X μ l ≤ 1 + (σ2 : ℝ) * l ^ 2 := by
    rw [hmgf_eq]
    have h1 : ∫ ω, (Real.exp (l * X ω) - 1 - l * X ω) ∂μ
        ≤ ∫ ω, (Real.exp (|l| * |X ω|) - 1 - |l| * |X ω|) ∂μ :=
      integral_mono hRint hSint hRmono'
    linarith [h1, hS_int_bound]
  -- ### Conclusion.
  refine ⟨hexpInt, ?_⟩
  calc mgf X μ l ≤ 1 + (σ2 : ℝ) * l ^ 2 := hmgf
    _ ≤ Real.exp ((σ2 : ℝ) * l ^ 2) := by linarith [Real.add_one_le_exp ((σ2 : ℝ) * l ^ 2)]
    _ ≤ Real.exp (l ^ 2 * ((2 * s : ℝ≥0) : ℝ) ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have hα : ((2 * s : ℝ≥0) : ℝ) = 2 * (s : ℝ) := by push_cast; ring
        rw [hα]
        nlinarith [hσ_le_s2, sq_nonneg l, mul_nonneg (sq_nonneg (s : ℝ)) (sq_nonneg l)]

/-! ### Main theorem -/

/-- A random variable satisfying the Bernstein condition (Lu-BDA §6.1) is sub-exponential
with parameter `α = 2 · (√σ2 ⊔ b)`.

**Proof**: from `bernstein_key` plus the mean-zero centering. For `|l| ≤ 1/α`:
- `mgf_le`: since `E[X] = 0`, the centered MGF equals the uncentered one; apply `bernstein_key`.
- `integrable_exp_mul`: same centering, integrability from `bernstein_key`.

**Constant deviation from the task statement** — the task asks for `α = 2*(σ2⊔b)`.
See the module header for why this is incorrect and `α = 2*(NNReal.sqrt σ2 ⊔ b)` is the
provable form.

-- USER-INPUT: `X` (random variable), `σ2`, `b` (Bernstein parameters); Lu-BDA §6.1.
-- LEAN-ONLY: `[IsProbabilityMeasure μ]`; Lu-BDA §6.1 works on a probability space
   (tacit from the book context). -/
theorem isSubExponential_of_hasBernsteinCondition
    [IsProbabilityMeasure μ]
    -- USER-INPUT: `X` measurable (random variable); Lu-BDA §6.1.
    (hX : Measurable X)
    -- USER-INPUT: Bernstein condition for X; Lu-BDA §6.1.
    (hB : HasBernsteinCondition X σ2 b μ) :
    IsSubExponential X (2 * (NNReal.sqrt σ2 ⊔ b)) μ where
  mgf_le l hl := by
    -- X ω - E[X] = X ω - 0 = X ω  (by mean_zero)
    have hcenter : (fun ω => X ω - ∫ x, X x ∂μ) = X := by
      funext ω; simp [hB.mean_zero]
    rw [hcenter]
    exact (bernstein_key hX hB hl).2
  integrable_exp_mul l hl := by
    -- exp(l · (X ω - E[X])) = exp(l · X ω)  (by mean_zero)
    simp_rw [hB.mean_zero, sub_zero]
    exact (bernstein_key hX hB hl).1

end StatLean.ConcentrationInequalities
