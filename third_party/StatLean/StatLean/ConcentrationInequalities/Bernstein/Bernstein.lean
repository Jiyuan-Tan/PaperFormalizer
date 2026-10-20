module
public import StatLean.ConcentrationInequalities.Bernstein.Defs
public import Mathlib.Probability.Moments.Basic

@[expose] public section

/-!
# Bernstein's inequality for the sample mean

If $X_1, \dots, X_n$ are **independent** random variables, each centered ($\mathbb{E} X_i = 0$)
with common variance $\mathrm{Var}(X_i) = \sigma^2 > 0$, and each satisfies the *Bernstein moment
condition* with parameter $b > 0$ — that is, $\mathbb{E}\,|X_i|^k \le \tfrac{\sigma^2}{2}\,k!\,
b^{k-2}$ for all $k \ge 3$ — then the sample mean $\bar X_n = \tfrac1n \sum_{i=1}^n X_i$ obeys,
for every $t > 0$,
$$
  \mathbb{P}\bigl(\bar X_n > t\bigr) \;\le\; \exp\!\left(- \frac{n t^2}{2\,(\sigma^2 + b t)}\right).
$$

This is exactly the book's statement.  The Lean formalization makes explicit two positivity
hypotheses that the book's narrative carries implicitly ($\sigma^2 > 0$ and $b > 0$, used to place
the Chernoff parameter $\lambda = t/(\sigma^2 + b t)$ strictly inside $(0, 1/b)$); the constant
$(\sigma^2 + b t)$ is the book's and is *not* relaxed.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 6 (Bernstein and Maximal Inequalities), §6.1,
Theorem 6.1 (Bernstein Inequality) (Steps 1 & 2 of its proof). The Bernstein condition is
Definition 6.1 (Bernstein Condition), given just above that theorem in §6.1.

**Proof formalization notes.**

*Step 2 (Chernoff on the sum).* Apply the raw Chernoff bound to the sum $S = \sum_i X_i$ at
threshold $n t$: for $0 \le \lambda$ with $\lambda b < 1$,
$$
  \mathbb{P}(n t \le S) \le e^{-\lambda n t}\,\textstyle\prod_i \mathrm{mgf}\,X_i(\lambda)
    \le e^{-\lambda n t}\,\exp\!\Bigl(\tfrac{n \lambda^2 \sigma^2}{2(1-\lambda b)}\Bigr),
$$
where the product factorises by independence (`iIndepFun.mgf_sum`) and each factor is the
**sharp** sub-exponential MGF bound $\mathrm{mgf}\,X_i(\lambda) \le \exp\!\bigl(\tfrac{\sigma^2
\lambda^2}{2(1-\lambda b)}\bigr)$.  Choosing $\lambda = t/(\sigma^2 + b t)$ (so $0 < \lambda$ and
$\lambda b < 1$, since $\sigma^2 > 0$) gives $1 - \lambda b = \sigma^2/(\sigma^2 + b t)$, hence
$\lambda^2 \sigma^2/(2(1-\lambda b)) = \lambda^2(\sigma^2 + b t)/2$ and $-\lambda t +
\lambda^2(\sigma^2 + b t)/2 = -t^2/(2(\sigma^2 + b t))$, so the exponent collapses to
$-n t^2/(2(\sigma^2 + b t))$.

*Why the per-variable MGF bound (Step 1) is re-derived here.* `Bernstein/MGFBound.lean` proves only
the *loose* sub-exponential bound $\mathrm{mgf}\,X_i(\lambda) \le \exp(\lambda^2 \alpha^2/2)$ with
$\alpha = 2(\sqrt{\sigma^2} \vee b)$ (via `isSubExponential_of_hasBernsteinCondition`, whose
`bernstein_key` core bounds the geometric series $1/(1-|\lambda|b) \le 2$).  That constant yields a
sub-Gaussian-type tail $\exp(-n t^2/(4\sigma^2))$, **not** the sharp Bernstein constant
$\sigma^2 + b t$.  To get the book's bound we keep the geometric factor $1/(1-\lambda b)$ rather
than bounding it by $2$; the elementary monotone-convergence derivation (power-series expansion of
$e^{\lambda X} - 1 - \lambda X$, `lintegral_tsum`, geometric sum) is reproduced in
`bernstein_mgf_sharp` below.  It mirrors `bernstein_key` step-for-step, differing only in the
geometric-series step. The book's Step 1 uses the same Taylor-series expansion of the MGF and the
same geometric sum $\sum_{k\ge0} |\lambda|^k b^k = 1/(1-|\lambda|b)$.

*Constant.* The provable constant is the $(\sigma^2 + b t)$ form, exactly as stated by Lu §6.1
(Theorem 6.1).  No deviation.

**Bibliographic comments.** The inequality originates with S. N. Bernstein, "On a modification of
Chebyshev's inequality and of the error formula of Laplace" (in Russian), *Annals of the Scientific
Institutes of Savings of Ukraine, Mathematical Section* (Uchen. Zapiski Nauchno-Issled. Kafedr
Ukrainy, Otd. Mat.), vol. 1 (1924), pp. 38–49; reprinted in S. N. Bernstein, *Collected Works*,
Vol. IV, Nauka, Moscow, 1964.  Bernstein replaced the Chebyshev second-moment bound by control of
all higher moments (the *Bernstein moment condition* used here, $\mathbb{E}|X|^k \le
\tfrac{\sigma^2}{2}k!\,b^{k-2}$), which interpolates between the sub-Gaussian regime (small $t$,
constant $\sigma^2$) and the sub-exponential regime (large $t$, constant $b$).  The formulation
proved here — the two-regime tail $\exp(-nt^2/(2(\sigma^2 + bt)))$ for the sample mean — is the
standard modern synthesis; see e.g. Boucheron, Lugosi & Massart, *Concentration Inequalities*
(Oxford, 2013), §2.8, for the modern moment/MGF presentation that Lu §6.1 (Theorem 6.1) follows.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sharp per-variable MGF bound -/

set_option maxHeartbeats 800000 in
-- The closed-form proof is long (≈40 `have`s sharing one budget); raising the limit avoids a
-- cumulative timeout. No single step is expensive.
/-- **Sharp sub-exponential MGF bound from the Bernstein condition** (Lu-BDA §6.1,
Theorem 6.1 (Bernstein Inequality), Step 1).

For `0 ≤ l` with `l · b < 1`, the exponential `ω ↦ exp(l · Y ω)` is integrable and
`mgf Y μ l ≤ exp(σ² l² / (2(1 − l b)))`.

This is the sharp version (geometric factor `1/(1 − l b)` retained) needed for the Bernstein
inequality; `Bernstein/MGFBound.lean` only exposes the looser `exp(λ²α²/2)` form (see the module
header).  Proof by the elementary monotone-convergence route: expand the exponential tail as a
power series, push through `lintegral_tsum`, and sum the geometric series, which converges because
`l · b < 1`.

(`maxHeartbeats` raised because the closed-form proof is long; no single step is expensive.) -/
private lemma bernstein_mgf_sharp {Y : Ω → ℝ} {σ2 b : ℝ≥0} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    -- USER-INPUT: `Y` measurable (random variable); Lu-BDA §6.1.
    (hY : Measurable Y)
    -- USER-INPUT: Bernstein condition for `Y`; Lu-BDA §6.1, Definition 6.1 (Bernstein Condition).
    (hB : HasBernsteinCondition Y σ2 b μ)
    -- LEAN-ONLY: `0 ≤ l` (right-tail Chernoff only needs nonnegative `l`); Lu-BDA §6.1 MGF range.
    {l : ℝ} (hl0 : 0 ≤ l)
    -- LEAN-ONLY: `l · b < 1` (geometric-series convergence range); Lu-BDA §6.1.
    (hlb : l * (b : ℝ) < 1) :
    Integrable (fun ω => Real.exp (l * Y ω)) μ ∧
    mgf Y μ l ≤ Real.exp ((σ2 : ℝ) * l ^ 2 / (2 * (1 - l * (b : ℝ)))) := by
  classical
  -- ### Range facts.
  have habs : |l| = l := abs_of_nonneg hl0
  have hlb_abs : |l| * (b : ℝ) < 1 := by rw [habs]; exact hlb
  have hlb_nonneg : (0 : ℝ) ≤ |l| * (b : ℝ) := mul_nonneg (abs_nonneg l) (NNReal.coe_nonneg b)
  have h1mlb_pos : (0 : ℝ) < 1 - |l| * (b : ℝ) := by linarith
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
  -- ### `Y²` is integrable and its lower-Lebesgue integral is `σ2`.
  have hY2int : Integrable (fun ω => (Y ω) ^ 2) μ := by
    rcases eq_or_ne σ2 0 with hσ | hσ
    · have h3 := hB.moment_le 3 (by norm_num)
      rw [hσ] at h3
      simp only [NNReal.coe_zero, zero_div, zero_mul, ENNReal.ofReal_zero,
        nonpos_iff_eq_zero] at h3
      rw [lintegral_eq_zero_iff' ((hY.abs.pow_const 3).ennreal_ofReal.aemeasurable)] at h3
      have hae : (fun ω => (Y ω) ^ 2) =ᵐ[μ] 0 := by
        filter_upwards [h3] with ω hω
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
        have hcube : |Y ω| ^ 3 = 0 := le_antisymm hω (by positivity)
        have hYabs : |Y ω| = 0 := by
          have := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
          exact this
        simp [abs_eq_zero.mp hYabs]
      exact (integrable_zero Ω ℝ μ).congr hae.symm
    · by_contra hni
      have h0 := integral_undef hni
      rw [hB.variance_eq] at h0
      exact hσ (by exact_mod_cast h0)
  have hM2 : ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ = ENNReal.ofReal (σ2 : ℝ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hY2int
      (Filter.Eventually.of_forall fun ω => sq_nonneg (Y ω)), hB.variance_eq]
  -- ### Moment bound `E|Y|^m ≤ (σ2/2)·m!·b^(m-2)` for all `m ≥ 2` (k=2 from the variance).
  have hM : ∀ m : ℕ, 2 ≤ m →
      ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ m) ∂μ
        ≤ ENNReal.ofReal ((σ2 : ℝ) / 2 * (Nat.factorial m : ℝ) * (b : ℝ) ^ (m - 2)) := by
    intro m hm
    rcases eq_or_lt_of_le hm with h2 | h3
    · subst h2
      have heq : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ 2) ∂μ = ENNReal.ofReal (σ2 : ℝ) := by
        simp_rw [sq_abs]; exact hM2
      rw [heq]
      apply ENNReal.ofReal_le_ofReal
      have hfac : ((Nat.factorial 2 : ℝ)) = 2 := by norm_num [Nat.factorial]
      rw [hfac, show (2 : ℕ) - 2 = 0 from rfl, pow_zero, mul_one]
      linarith
    · exact hB.moment_le m h3
  -- ### The core ENNReal bound on the exponential tail.
  have hmeas_term : ∀ n : ℕ, Measurable fun ω =>
      ENNReal.ofReal ((|l| * |Y ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) :=
    fun n => (((hY.abs.const_mul |l|).pow_const (n + 2)).div_const _).ennreal_ofReal
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω|)
      = ∑' n : ℕ, ENNReal.ofReal ((|l| * |Y ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) := by
    intro ω
    rw [← hreindex (|l| * |Y ω|),
      ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        ((summable_nat_add_iff 2).mpr (Real.summable_pow_div_factorial (|l| * |Y ω|)))]
  have per_term : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((|l| * |Y ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) ∂μ
        ≤ ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2) * (ENNReal.ofReal (|l| * (b : ℝ))) ^ n := by
    intro n
    have hrw : ∀ ω, ENNReal.ofReal ((|l| * |Y ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
        = ENNReal.ofReal (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
            * ENNReal.ofReal (|Y ω| ^ (n + 2)) := by
      intro ω
      rw [mul_pow,
        show |l| ^ (n + 2) * |Y ω| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)
          = (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) * |Y ω| ^ (n + 2) by ring,
        ENNReal.ofReal_mul (by positivity)]
    have hpowl : |l| ^ (n + 2) = l ^ 2 * |l| ^ n := by rw [pow_add, sq_abs]; ring
    have hAB : (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
          * ((σ2 : ℝ) / 2 * (Nat.factorial (n + 2) : ℝ) * (b : ℝ) ^ (n + 2 - 2))
        = (σ2 : ℝ) / 2 * l ^ 2 * (|l| * (b : ℝ)) ^ n := by
      rw [Nat.add_sub_cancel, hpowl, mul_pow]
      have hfac : (Nat.factorial (n + 2) : ℝ) ≠ 0 := by positivity
      field_simp
    calc ∫⁻ ω, ENNReal.ofReal ((|l| * |Y ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
              * ENNReal.ofReal (|Y ω| ^ (n + 2)) ∂μ := by simp_rw [hrw]
      _ = ENNReal.ofReal (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
              * ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (n + 2)) ∂μ :=
            lintegral_const_mul _ ((hY.abs.pow_const (n + 2)).ennreal_ofReal)
      _ ≤ ENNReal.ofReal (|l| ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
              * ENNReal.ofReal ((σ2 : ℝ) / 2 * (Nat.factorial (n + 2) : ℝ)
                  * (b : ℝ) ^ (n + 2 - 2)) := by
            gcongr
            exact hM (n + 2) (by omega)
      _ = ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2) * (ENNReal.ofReal (|l| * (b : ℝ))) ^ n := by
            rw [← ENNReal.ofReal_mul (by positivity), hAB,
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (σ2 : ℝ) / 2 * l ^ 2),
              ENNReal.ofReal_pow hlb_nonneg]
  -- ### Geometric series with the factor `1/(1 − |l|b)` retained (the sharp step).
  have hsub_eq : (1 : ℝ≥0∞) - ENNReal.ofReal (|l| * (b : ℝ))
      = ENNReal.ofReal (1 - |l| * (b : ℝ)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hlb_nonneg]
  have hinv_eq : (1 - ENNReal.ofReal (|l| * (b : ℝ)))⁻¹
      = ENNReal.ofReal ((1 - |l| * (b : ℝ))⁻¹) := by
    rw [hsub_eq]; exact (ENNReal.ofReal_inv_of_pos h1mlb_pos).symm
  have hc_nonneg : (0 : ℝ) ≤ (σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹ :=
    mul_nonneg (by positivity) (inv_nonneg.mpr h1mlb_pos.le)
  have hSbound : ∫⁻ ω, ENNReal.ofReal (Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω|) ∂μ
      ≤ ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹) := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω|) ∂μ
        = ∑' n : ℕ, ∫⁻ ω,
            ENNReal.ofReal ((|l| * |Y ω|) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) ∂μ := by
          simp_rw [hpt]
          rw [lintegral_tsum (fun n => (hmeas_term n).aemeasurable)]
      _ ≤ ∑' n : ℕ, ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2)
              * (ENNReal.ofReal (|l| * (b : ℝ))) ^ n := ENNReal.tsum_le_tsum per_term
      _ = ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2)
              * ∑' n : ℕ, (ENNReal.ofReal (|l| * (b : ℝ))) ^ n := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2)
              * (1 - ENNReal.ofReal (|l| * (b : ℝ)))⁻¹ := by rw [ENNReal.tsum_geometric]
      _ = ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2)
              * ENNReal.ofReal ((1 - |l| * (b : ℝ))⁻¹) := by rw [hinv_eq]
      _ = ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹) := by
            rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (σ2 : ℝ) / 2 * l ^ 2)]
  -- ### Integrability of the tail `S(Y) = exp(|l||Y|) - 1 - |l||Y|`.
  have hS_meas : Measurable fun ω => Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω| := by
    have h1 : Measurable fun ω => |l| * |Y ω| := hY.abs.const_mul |l|
    exact (h1.exp.sub measurable_const).sub h1
  have hSnonneg : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω| :=
    Filter.Eventually.of_forall fun ω => by
      have := Real.add_one_le_exp (|l| * |Y ω|); simpa using by linarith
  have hSint : Integrable (fun ω => Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω|) μ := by
    refine ⟨hS_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hSnonneg]
    exact lt_of_le_of_lt hSbound ENNReal.ofReal_lt_top
  have hS_int_bound : ∫ ω, (Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω|) ∂μ
      ≤ (σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹ := by
    rw [integral_eq_lintegral_of_nonneg_ae hSnonneg hS_meas.aestronglyMeasurable]
    calc (∫⁻ ω, ENNReal.ofReal (Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω|) ∂μ).toReal
        ≤ (ENNReal.ofReal ((σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hSbound
      _ = (σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹ := ENNReal.toReal_ofReal hc_nonneg
  -- ### Integrability of `Y` and of `exp(l·Y)`.
  have hYint : Integrable Y μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hY2int)
      hY.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    nlinarith [sq_nonneg (|Y ω| - 1), abs_nonneg (Y ω), sq_abs (Y ω)]
  have hexpAbsInt : Integrable (fun ω => Real.exp (|l| * |Y ω|)) μ := by
    have heq : (fun ω => Real.exp (|l| * |Y ω|))
        = fun ω => 1 + |l| * |Y ω| + (Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω|) := by
      funext ω; ring
    rw [heq]
    exact ((integrable_const (1 : ℝ)).add (hYint.abs.const_mul |l|)).add hSint
  have hexpInt : Integrable (fun ω => Real.exp (l * Y ω)) μ := by
    refine hexpAbsInt.mono' ((hY.const_mul l).exp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by rw [abs_mul]))
  -- ### Pointwise `R(Y) ≤ S(Y)` and the MGF bound.
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
  have hRmono' : ∀ ω, Real.exp (l * Y ω) - 1 - l * Y ω
      ≤ Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω| := by
    intro ω
    have := hRmono (l * Y ω)
    rwa [abs_mul] at this
  have hRint : Integrable (fun ω => Real.exp (l * Y ω) - 1 - l * Y ω) μ :=
    (hexpInt.sub (integrable_const 1)).sub (hYint.const_mul l)
  have hmgf_eq : mgf Y μ l = 1 + ∫ ω, (Real.exp (l * Y ω) - 1 - l * Y ω) ∂μ := by
    have h1lY : Integrable (fun ω => 1 + l * Y ω) μ :=
      (integrable_const 1).add (hYint.const_mul l)
    have hone : ∫ ω, (1 + l * Y ω) ∂μ = 1 := by
      rw [integral_add (integrable_const 1) (hYint.const_mul l), integral_const_mul,
        hB.mean_zero]
      simp
    have hsplit : (fun ω => Real.exp (l * Y ω))
        = fun ω => (1 + l * Y ω) + (Real.exp (l * Y ω) - 1 - l * Y ω) := by funext ω; ring
    simp only [mgf]
    rw [hsplit, integral_add h1lY hRint, hone]
  have hmgf : mgf Y μ l ≤ 1 + (σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹ := by
    rw [hmgf_eq]
    have h1 : ∫ ω, (Real.exp (l * Y ω) - 1 - l * Y ω) ∂μ
        ≤ ∫ ω, (Real.exp (|l| * |Y ω|) - 1 - |l| * |Y ω|) ∂μ :=
      integral_mono hRint hSint hRmono'
    linarith [h1, hS_int_bound]
  -- ### Conclusion.
  refine ⟨hexpInt, ?_⟩
  calc mgf Y μ l ≤ 1 + (σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹ := hmgf
    _ ≤ Real.exp ((σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹) := by
        linarith [Real.add_one_le_exp ((σ2 : ℝ) / 2 * l ^ 2 * (1 - |l| * (b : ℝ))⁻¹)]
    _ = Real.exp ((σ2 : ℝ) * l ^ 2 / (2 * (1 - l * (b : ℝ)))) := by
        have hne : (1 : ℝ) - l * (b : ℝ) ≠ 0 := by rw [← habs]; exact h1mlb_pos.ne'
        rw [habs]; congr 1; field_simp

/-! ### Main theorem -/

/-- **Bernstein's inequality for the sample mean** (Lu-BDA §6.1, Theorem 6.1 (Bernstein Inequality)).

If `X 0, …, X (n−1)` are jointly independent, each measurable, each satisfying the Bernstein
condition with variance `σ² > 0` and scale `b > 0` under the probability measure `μ`, then for
every `t > 0` the sample mean `X̄ₙ = (1/n) ∑ᵢ Xᵢ` satisfies

  `μ {ω | t < X̄ₙ ω} ≤ exp(− n t² / (2 (σ² + b t)))`.

**Proof.** Apply the raw Chernoff bound `measure_ge_le_exp_mul_mgf` to the sum `S = ∑ᵢ Xᵢ` at
threshold `n t` and `λ = t/(σ² + b t)` (which lies in `[0, 1/b)` since `σ² > 0`).  Independence
factorises the sum-MGF (`iIndepFun.mgf_sum`); each factor is controlled by the sharp per-variable
bound `bernstein_mgf_sharp`.  With `1 − λ b = σ²/(σ²+b t)` the per-variable exponent becomes
`λ²(σ²+b t)/2`, and the Chernoff exponent `−λ n t + n λ²(σ²+b t)/2` collapses to
`−n t²/(2(σ²+b t))`.
The `μ.real → μ` ENNReal bridge mirrors `SubGaussian/TailBounds.lean`.

**Constant.** Exactly Lu's `(σ² + b t)`; no deviation. -/
theorem bernstein_inequality {n : ℕ} {X : Fin n → Ω → ℝ} {σ2 b : ℝ≥0} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    -- USER-INPUT: each `Xᵢ` measurable (random variable); Lu-BDA §6.1.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: `X 0, …, X (n-1)` jointly independent; Lu-BDA §6.1.
    (hX_indep : iIndepFun X μ)
    -- USER-INPUT: each `Xᵢ` satisfies the Bernstein condition (E Xᵢ=0, Var Xᵢ=σ², moment bound);
    --             Lu-BDA §6.1, Definition 6.1 (Bernstein Condition).
    (hB : ∀ i, HasBernsteinCondition (X i) σ2 b μ)
    -- USER-INPUT: positive sample size `n ≥ 1`; Lu-BDA §6.1.
    (hn : 0 < n)
    -- USER-INPUT: Bernstein scale `b > 0`; Lu-BDA §6.1.
    (hb : 0 < b)
    -- USER-INPUT: variance `σ² > 0`; Lu-BDA §6.1.
    (hσ2 : 0 < σ2)
    -- USER-INPUT: deviation `t > 0`; Lu-BDA §6.1.
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t < (∑ i, X i ω) / (n : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (2 * ((σ2 : ℝ) + (b : ℝ) * t)))) := by
  -- ### The Chernoff parameter `λ = t / (σ² + b t)` and its range.
  set lam : ℝ := t / ((σ2 : ℝ) + (b : ℝ) * t) with hlam_def
  have hσR : (0 : ℝ) < (σ2 : ℝ) := by exact_mod_cast hσ2
  have hden_pos : (0 : ℝ) < (σ2 : ℝ) + (b : ℝ) * t := by
    have : (0 : ℝ) ≤ (b : ℝ) * t := by positivity
    linarith
  have hden_ne : (σ2 : ℝ) + (b : ℝ) * t ≠ 0 := ne_of_gt hden_pos
  have hσ2ne : (σ2 : ℝ) ≠ 0 := ne_of_gt hσR
  have hlam0 : 0 ≤ lam := by rw [hlam_def]; positivity
  have hlamb : lam * (b : ℝ) < 1 := by
    rw [hlam_def, div_mul_eq_mul_div, div_lt_one hden_pos]
    have hcomm : t * (b : ℝ) = (b : ℝ) * t := mul_comm _ _
    linarith [hσR, hcomm]
  -- ### `1 − λ b = σ²/(σ²+b t)`, hence the per-variable exponent simplifies.
  have h1mlamb_eq : 1 - lam * (b : ℝ) = (σ2 : ℝ) / ((σ2 : ℝ) + (b : ℝ) * t) := by
    rw [hlam_def]; field_simp; ring
  have hcle : (σ2 : ℝ) * lam ^ 2 / (2 * (1 - lam * (b : ℝ)))
      = lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2 := by
    rw [h1mlamb_eq]; field_simp
  -- ### Per-variable MGF bound at `λ`.
  have per_var_bound : ∀ i, mgf (X i) μ lam
      ≤ Real.exp (lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2) := by
    intro i
    have h := (bernstein_mgf_sharp (hX_meas i) (hB i) hlam0 hlamb).2
    rwa [hcle] at h
  -- ### MGF of the sum factorises and is bounded.
  have hmgf_sum_le : mgf (∑ i, X i) μ lam
      ≤ Real.exp ((n : ℝ) * (lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2)) := by
    rw [hX_indep.mgf_sum (t := lam) hX_meas Finset.univ]
    calc ∏ i, mgf (X i) μ lam
        ≤ ∏ _i : Fin n, Real.exp (lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2) :=
          Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => per_var_bound i)
      _ = Real.exp (lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = Real.exp ((n : ℝ) * (lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2)) :=
          (Real.exp_nat_mul _ _).symm
  -- ### The Chernoff exponent collapses to `−n t²/(2(σ²+b t))`.
  have hexp_arg_eq : -lam * ((n : ℝ) * t) + (n : ℝ) * (lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2)
      = -(n : ℝ) * t ^ 2 / (2 * ((σ2 : ℝ) + (b : ℝ) * t)) := by
    rw [hlam_def]; field_simp; ring
  -- ### Integrability of `exp(λ · ∑ Xᵢ)` from independence + per-variable integrability.
  have hSint : Integrable (fun ω => Real.exp (lam * (∑ i, X i) ω)) μ :=
    hX_indep.integrable_exp_mul_sum hX_meas
      (fun i _ => (bernstein_mgf_sharp (hX_meas i) (hB i) hlam0 hlamb).1)
  -- ### Raw Chernoff on the sum at threshold `n t`.
  have hcher : μ.real {ω | (n : ℝ) * t ≤ (∑ i, X i) ω}
      ≤ Real.exp (-(n : ℝ) * t ^ 2 / (2 * ((σ2 : ℝ) + (b : ℝ) * t))) := by
    have hC := measure_ge_le_exp_mul_mgf (X := (∑ i, X i)) (t := lam)
      ((n : ℝ) * t) hlam0 hSint
    refine hC.trans ?_
    calc Real.exp (-lam * ((n : ℝ) * t)) * mgf (∑ i, X i) μ lam
        ≤ Real.exp (-lam * ((n : ℝ) * t))
            * Real.exp ((n : ℝ) * (lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2)) :=
          mul_le_mul_of_nonneg_left hmgf_sum_le (Real.exp_pos _).le
      _ = Real.exp (-lam * ((n : ℝ) * t)
            + (n : ℝ) * (lam ^ 2 * ((σ2 : ℝ) + (b : ℝ) * t) / 2)) := (Real.exp_add _ _).symm
      _ = Real.exp (-(n : ℝ) * t ^ 2 / (2 * ((σ2 : ℝ) + (b : ℝ) * t))) := by rw [hexp_arg_eq]
  -- ### Reduce the sample-mean event to the sum event and bridge to ENNReal.
  have hsub : {ω | t < (∑ i, X i ω) / (n : ℝ)} ⊆ {ω | (n : ℝ) * t ≤ (∑ i, X i) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [Finset.sum_apply]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [lt_div_iff₀ hnpos] at hω
    have hcomm : (n : ℝ) * t = t * (n : ℝ) := mul_comm _ _
    linarith [hω, hcomm]
  calc μ {ω | t < (∑ i, X i ω) / (n : ℝ)}
      ≤ μ {ω | (n : ℝ) * t ≤ (∑ i, X i) ω} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (2 * ((σ2 : ℝ) + (b : ℝ) * t)))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | (n : ℝ) * t ≤ (∑ i, X i) ω})]
        exact ENNReal.ofReal_le_ofReal hcher

end StatLean.ConcentrationInequalities
