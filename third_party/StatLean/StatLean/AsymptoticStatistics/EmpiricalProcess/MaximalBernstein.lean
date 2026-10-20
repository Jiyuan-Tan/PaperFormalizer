module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Bernstein's inequality for the empirical process

Let $X_1, \dots, X_n$ be i.i.d. draws from a probability measure $P$ on a sample
space, and let $f$ be a measurable function that is uniformly bounded,
$|f| \le M$, with second-moment (variance proxy) bound $\int f^2 \, dP \le \sigma^2$.
Write the empirical process indexed by $f$ as
$$
\mathbb{G}_n f \;=\; \frac{1}{\sqrt n} \sum_{i=1}^n \bigl(f(X_i) - Pf\bigr),
\qquad Pf = \int f \, dP .
$$
Then for every $x > 0$ the empirical process obeys the two-sided exponential
(Bernstein) tail bound
$$
P\bigl(\, |\mathbb{G}_n f| > x \,\bigr)
\;\le\; 2 \exp\!\left( - \frac{x^2}{4\bigl(\sigma^2 + x M / \sqrt n\bigr)} \right).
$$

The right-tail (one-sided) version replaces the leading factor $2$ by $1$:
$P(\mathbb{G}_n f > x) \le \exp\bigl(-x^2 / (4(\sigma^2 + xM/\sqrt n))\bigr)$.

*Deviations from the book.* van der Vaart states the denominator with the
second moment $Pf^2$ of the (centred) summand; here we expose it through the
caller-supplied variance proxy $\sigma^2 \ge \int f^2 \, dP$, and the centring by
$Pf$ is performed internally rather than assumed. The provable constant is
$1/4$ in the exponent (matching the book), together with the factor $2$ from the
union of the two one-sided tails.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 19 (Empirical Processes), §19.6, Lemma 19.32.

**Proof formalization notes.** The development decomposes the two-sided bound into
the following named steps:

* `centered_moment_bound_pow` — a centered-moment bound: for $k \ge 2$,
  $\bigl|\int (f - Pf)^k \, dP\bigr| \le (\int f^2 \, dP)\,(2M)^{k-2}$, via the
  pointwise estimate $|f - Pf| \le 2M$ and $|{\int Y}| \le \int |Y|$.
* `mgf_bounded_taylor` — the convergent power-series expansion of the moment
  generating function of a bounded variable, $\mathbb{E}[e^{\lambda X}] =
  \sum_{k\ge 0} (\lambda^k/k!)\,\mathbb{E}[X^k]$, by dominated convergence on the
  partial sums with dominator $e^{|\lambda| M}$.
* `bernstein_mgf_centered_bound` — the per-sample Bennett–Bernstein MGF bound: for
  a centred variable with $|Y| \le 2M$, $\mathbb{E}Y = 0$ and the centred-moment
  bound above, and $0 \le t$ with $2Mt < 1$,
  $\mathbb{E}[e^{tY}] \le \exp\bigl(\sigma^2 t^2 / (2(1 - 2Mt))\bigr)$, obtained by
  summing the geometric tail of the MGF series and upgrading via $1 + u \le e^u$.
* `bernstein_one_sided` — the right-tail bound, assembled via Markov on the MGF,
  i.i.d. factorisation (`iIndepFun.mgf_sum`), the per-sample bound, the optimal
  choice $\lambda = (x/2)/(\sigma^2 + xM/\sqrt n)$, and $(1 + a/n)^n \le e^a$.
  Includes the degenerate edge cases $M = 0$ (then $f \equiv 0$) and $\sigma = 0$
  (then $f = 0$ a.e. $P$, so $\mathbb{G}_n f = 0$ a.e.).
* `bernstein_two_sided` — combines `bernstein_one_sided` applied to $f$ and to
  $-f$ (using `empiricalProcess_neg`: $\mathbb{G}_n(-f) = -\mathbb{G}_n f$) through
  a union bound. Exposed publicly as `bernstein_inequality_aux`, which is the body
  of `bernstein_inequality` (stated in `Maximal.lean` for import-DAG reasons).

**Bibliographic comments.** The scalar exponential inequality underlying this
result originates with S. N. Bernstein, *On a modification of Chebyshev's
inequality and of the error formula of Laplace*, Ann. Sci. Inst. Sav. Ukraine,
Sect. Math. **1** (1924), 38–49 (in Russian) — the first sub-exponential tail
bound trading the variance against a one-sided boundedness (or moment-growth)
condition. The empirical-process form stated here, with the explicit
$\sigma^2 + xM/\sqrt n$ denominator, is textbook synthesis: it is the
specialisation of Bernstein's bound to the centred, normalised sums $\mathbb{G}_n f$
collected as Lemma 19.32 in van der Vaart (1998); there is no single seminal paper
for this packaged empirical-process statement beyond Bernstein's original
inequality and its standard maximal-inequality applications.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter Real
open scoped ENNReal Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Step 4: `empiricalProcess` is odd in `f`. -/

/-- `empiricalProcess` is linear-odd in `f`: `G_n(-f) = -G_n f`. -/
lemma empiricalProcess_neg
    (P : Measure Ω) (n : ℕ) (X : Fin n → Ω) (f : Ω → ℝ) :
    empiricalProcess P n X (fun ω => -f ω) = -empiricalProcess P n X f := by
  unfold empiricalProcess empiricalAvg
  simp [Finset.sum_neg_distrib, integral_neg]
  ring

/-! ### Step 1: bounded centered-moment bound. -/

/-- For a measurable bounded function `f : Ω → ℝ` with `|f ω| ≤ M`,
the centered absolute moment is dominated by the variance times `(2M)^{k-2}`:
`|∫ ω, (f ω - ∫ f)^k ∂P| ≤ (∫ f²) · (2M)^{k-2}` for all `k ≥ 2`.

The proof is by the pointwise bound `|f - Pf| ≤ 2M` and
`|f - Pf|^k = (f - Pf)^2 · |f - Pf|^{k-2} ≤ (f - Pf)^2 · (2M)^{k-2}`,
then Jensen's inequality `|∫ Y| ≤ ∫ |Y|`. -/
private lemma centered_moment_bound_pow
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf_meas : Measurable f)
    {M : ℝ} (hM : 0 ≤ M) (hf_bdd : ∀ ω, |f ω| ≤ M)
    (k : ℕ) (hk : 2 ≤ k) :
    |∫ ω, (f ω - ∫ ω', f ω' ∂P) ^ k ∂P|
      ≤ (∫ ω, (f ω) ^ 2 ∂P) * (2 * M) ^ (k - 2) := by
  -- `|f| ≤ M ⇒ |Pf| ≤ M` (Jensen) ⇒ `|f - Pf| ≤ 2M` pointwise.
  set μf : ℝ := ∫ ω', f ω' ∂P with hμf_def
  have h_int_f : Integrable f P := by
    refine Integrable.mono' (g := fun _ => M) (integrable_const _) hf_meas.aestronglyMeasurable ?_
    refine ae_of_all _ (fun ω => ?_)
    simpa [Real.norm_eq_abs] using hf_bdd ω
  have h_abs_intf : |μf| ≤ M := by
    have := abs_integral_le_integral_abs (μ := P) (f := f)
    refine this.trans ?_
    have hbnd : ∀ᵐ ω ∂P, |f ω| ≤ M := ae_of_all _ hf_bdd
    have : ∫ ω, |f ω| ∂P ≤ ∫ _, M ∂P := by
      refine integral_mono_ae h_int_f.abs (integrable_const _) hbnd
    simpa using this
  have h_diff_bdd : ∀ ω, |f ω - μf| ≤ 2 * M := by
    intro ω
    calc |f ω - μf| ≤ |f ω| + |μf| := abs_sub _ _
      _ ≤ M + M := add_le_add (hf_bdd ω) h_abs_intf
      _ = 2 * M := by ring
  have h_diff_sq_bdd : ∀ ω, (f ω - μf) ^ 2 ≤ (2 * M) ^ 2 := fun ω => by
    rw [sq_abs (f ω - μf) |>.symm]
    exact pow_le_pow_left₀ (abs_nonneg _) (h_diff_bdd ω) 2
  -- Pointwise: `(f - Pf)^k ≤ |f - Pf|^k = (f - Pf)^2 · |f - Pf|^{k-2}`.
  have h_diff_meas : Measurable (fun ω => f ω - μf) := hf_meas.sub_const _
  have h_diff_sq_meas : Measurable (fun ω => (f ω - μf) ^ 2) := h_diff_meas.pow_const _
  -- `f²` is integrable (bounded by `M²`).
  have h_f_sq_int : Integrable (fun ω => (f ω) ^ 2) P := by
    refine Integrable.mono' (g := fun _ => M ^ 2) (integrable_const _)
      (hf_meas.pow_const _).aestronglyMeasurable ?_
    refine ae_of_all _ (fun ω => ?_)
    have : |f ω ^ 2| ≤ M ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hf_bdd ω) 2
    simpa [Real.norm_eq_abs] using this
  -- `(f - μf)²` is integrable (bounded by `(2M)²`).
  have h_diff_sq_int : Integrable (fun ω => (f ω - μf) ^ 2) P := by
    refine Integrable.mono' (g := fun _ => (2 * M) ^ 2) (integrable_const _)
      h_diff_sq_meas.aestronglyMeasurable ?_
    refine ae_of_all _ (fun ω => ?_)
    have hnn : 0 ≤ (f ω - μf) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact h_diff_sq_bdd ω
  -- Bound the absolute moment.
  have h_abs_le : |∫ ω, (f ω - μf) ^ k ∂P|
      ≤ ∫ ω, |(f ω - μf) ^ k| ∂P := abs_integral_le_integral_abs
  have h_pt : ∀ ω, |(f ω - μf) ^ k| ≤ (f ω - μf) ^ 2 * (2 * M) ^ (k - 2) := by
    intro ω
    rw [abs_pow]
    have hk2 : k = 2 + (k - 2) := by omega
    nth_rewrite 1 [hk2]
    rw [pow_add]
    have h_abs_sq : |f ω - μf| ^ 2 = (f ω - μf) ^ 2 := sq_abs _
    rw [h_abs_sq]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (h_diff_bdd ω) (k - 2)
  have h_abs_pow_meas : Measurable (fun ω => |(f ω - μf) ^ k|) :=
    (h_diff_meas.pow_const k).norm
  have h_diff_k_int : Integrable (fun ω => |(f ω - μf) ^ k|) P := by
    refine Integrable.mono' (g := fun ω => (f ω - μf) ^ 2 * (2 * M) ^ (k - 2))
      (h_diff_sq_int.mul_const _) h_abs_pow_meas.aestronglyMeasurable ?_
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact h_pt ω)
  have h_int_le : ∫ ω, |(f ω - μf) ^ k| ∂P
      ≤ ∫ ω, (f ω - μf) ^ 2 * (2 * M) ^ (k - 2) ∂P := by
    exact integral_mono_ae h_diff_k_int (h_diff_sq_int.mul_const _) (ae_of_all _ h_pt)
  -- Pull constant out.
  have h_pull : ∫ ω, (f ω - μf) ^ 2 * (2 * M) ^ (k - 2) ∂P
      = (∫ ω, (f ω - μf) ^ 2 ∂P) * (2 * M) ^ (k - 2) := integral_mul_const _ _
  rw [h_pull] at h_int_le
  -- Variance ≤ second moment: ∫ (f - μf)² ∂P ≤ ∫ f² ∂P.
  have h_var_le : ∫ ω, (f ω - μf) ^ 2 ∂P ≤ ∫ ω, (f ω) ^ 2 ∂P := by
    have h_expand : ∀ ω, (f ω - μf) ^ 2 = (f ω) ^ 2 - 2 * μf * f ω + μf ^ 2 := by
      intro ω; ring
    have h_2μf_int : Integrable (fun ω => 2 * μf * f ω) P := h_int_f.const_mul (2 * μf)
    have h_const_int : Integrable (fun (_ : Ω) => μf ^ 2) P := integrable_const _
    have h_diff_sub : Integrable (fun ω => f ω ^ 2 - 2 * μf * f ω) P := h_f_sq_int.sub h_2μf_int
    have h_eq_int : ∫ ω, (f ω - μf) ^ 2 ∂P
        = (∫ ω, (f ω) ^ 2 ∂P) - 2 * μf * μf + μf ^ 2 := by
      calc ∫ ω, (f ω - μf) ^ 2 ∂P
          = ∫ ω, (f ω ^ 2 - 2 * μf * f ω + μf ^ 2) ∂P := by
            refine integral_congr_ae (ae_of_all _ ?_); intro ω; exact h_expand ω
        _ = ∫ ω, (f ω ^ 2 - 2 * μf * f ω) ∂P + ∫ _, μf ^ 2 ∂P :=
            integral_add h_diff_sub h_const_int
        _ = (∫ ω, f ω ^ 2 ∂P - ∫ ω, 2 * μf * f ω ∂P) + ∫ _, μf ^ 2 ∂P := by
            rw [integral_sub h_f_sq_int h_2μf_int]
        _ = (∫ ω, f ω ^ 2 ∂P - 2 * μf * (∫ ω, f ω ∂P)) + μf ^ 2 := by
            rw [integral_const_mul, integral_const]
            simp
        _ = (∫ ω, f ω ^ 2 ∂P - 2 * μf * μf) + μf ^ 2 := by
            change μf = ∫ ω', f ω' ∂P at hμf_def
            rw [← hμf_def]
        _ = (∫ ω, f ω ^ 2 ∂P) - 2 * μf * μf + μf ^ 2 := by ring
    rw [h_eq_int]
    nlinarith [sq_nonneg μf]
  calc |∫ ω, (f ω - μf) ^ k ∂P|
      ≤ ∫ ω, |(f ω - μf) ^ k| ∂P := h_abs_le
    _ ≤ (∫ ω, (f ω - μf) ^ 2 ∂P) * (2 * M) ^ (k - 2) := h_int_le
    _ ≤ (∫ ω, (f ω) ^ 2 ∂P) * (2 * M) ^ (k - 2) := by
        refine mul_le_mul_of_nonneg_right h_var_le (by positivity)

/-! ### Step 2: power-series expansion of the MGF for bounded variables. -/

/-- For a bounded measurable real-valued random variable `X` with `|X ω| ≤ M`,
the moment-generating function admits a convergent power-series expansion:
`mgf X μ λ = ∑_{k=0}^∞ λ^k/k! · μ[X^k]`.

Proof: dominated convergence on the partial sums
`S_N(ω) = ∑_{k=0}^N (λ X ω)^k / k!`, with uniform dominator `exp(|λ| · M)`.
The pointwise limit is `Real.exp (λ · X ω)` (Taylor series of exp), and the
DCT exchange transports it to integrals (the `μ[X^k]` are well-defined since
each `X^k` is bounded by `M^k`). -/
private lemma mgf_bounded_taylor
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : Ξ → ℝ) (hX_meas : Measurable X)
    {M : ℝ} (hM : 0 ≤ M) (hX_bdd : ∀ ω, |X ω| ≤ M)
    (lam : ℝ) :
    ProbabilityTheory.mgf X μ lam
      = ∑' k : ℕ, lam ^ k / k.factorial * (∫ ω, (X ω) ^ k ∂μ) := by
  -- Term-by-term: `(lam * X ω)^k / k! = lam^k / k! · X ω^k`.
  set f : ℕ → Ξ → ℝ := fun k ω => (lam * X ω) ^ k / k.factorial with hf_def
  -- Step 1: pointwise `Real.exp (lam * X ω) = ∑' k, f k ω`.
  have h_pt_eq : ∀ ω, Real.exp (lam * X ω) = ∑' k, f k ω := fun ω => by
    rw [show Real.exp = NormedSpace.exp from Real.exp_eq_exp_ℝ]
    exact congr_fun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) (lam * X ω)
  -- Step 2: each `f k` is integrable (bounded by `(|lam| · M)^k / k!`).
  have h_meas : ∀ k, Measurable (f k) := fun k => by
    refine Measurable.div_const ?_ _
    refine Measurable.pow_const ?_ k
    exact (measurable_const.mul hX_meas)
  have h_pt_bound : ∀ k ω, |f k ω| ≤ (|lam| * M) ^ k / k.factorial := fun k ω => by
    rw [hf_def]
    simp only
    rw [abs_div, abs_pow, abs_mul, Nat.abs_cast]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left (hX_bdd ω) (abs_nonneg _)) k
  -- Each `f k` is integrable.
  have h_int : ∀ k, Integrable (f k) μ := fun k => by
    refine Integrable.mono' (g := fun _ => (|lam| * M) ^ k / k.factorial)
      (integrable_const _) (h_meas k).aestronglyMeasurable ?_
    refine ae_of_all _ (fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact h_pt_bound k ω
  -- Step 3: summability of `‖f k ω‖ₑ` integrals.
  have h_int_norm : ∀ k, ∫⁻ ω, ‖f k ω‖ₑ ∂μ ≤ ENNReal.ofReal ((|lam| * M) ^ k / k.factorial) := by
    intro k
    have h_pt_le : ∀ ω, ‖f k ω‖ₑ ≤ ENNReal.ofReal ((|lam| * M) ^ k / k.factorial) := by
      intro ω
      rw [show ‖f k ω‖ₑ = ENNReal.ofReal |f k ω| from by
        rw [Real.enorm_eq_ofReal_abs]]
      exact ENNReal.ofReal_le_ofReal (h_pt_bound k ω)
    calc ∫⁻ ω, ‖f k ω‖ₑ ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal ((|lam| * M) ^ k / k.factorial) ∂μ :=
          MeasureTheory.lintegral_mono h_pt_le
      _ = ENNReal.ofReal ((|lam| * M) ^ k / k.factorial) * μ Set.univ := by
          rw [MeasureTheory.lintegral_const]
      _ = ENNReal.ofReal ((|lam| * M) ^ k / k.factorial) := by
          rw [measure_univ, mul_one]
  have h_summable_real : Summable (fun k : ℕ => (|lam| * M) ^ k / k.factorial) := by
    have h := NormedSpace.expSeries_div_summable (𝔸 := ℝ) (|lam| * M)
    simpa using h
  have h_sum_int : ∑' k : ℕ, ∫⁻ ω, ‖f k ω‖ₑ ∂μ
      ≤ ∑' k : ℕ, ENNReal.ofReal ((|lam| * M) ^ k / k.factorial) :=
    ENNReal.tsum_le_tsum h_int_norm
  have h_sum_finite : ∑' k : ℕ, ENNReal.ofReal ((|lam| * M) ^ k / k.factorial) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) h_summable_real]
    exact ENNReal.ofReal_ne_top
  have h_sum_int_finite : ∑' k : ℕ, ∫⁻ ω, ‖f k ω‖ₑ ∂μ ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt h_sum_int (lt_top_iff_ne_top.mpr h_sum_finite))
  -- Step 4: integral-tsum swap.
  have h_swap : ∫ ω, (∑' k, f k ω) ∂μ = ∑' k, ∫ ω, f k ω ∂μ := by
    refine MeasureTheory.integral_tsum (fun k => (h_meas k).aestronglyMeasurable) ?_
    exact h_sum_int_finite
  -- Step 5: assemble.
  unfold ProbabilityTheory.mgf
  have h_exp_int_eq : ∫ ω, Real.exp (lam * X ω) ∂μ = ∫ ω, ∑' k, f k ω ∂μ := by
    refine integral_congr_ae (ae_of_all _ ?_); intro ω; exact h_pt_eq ω
  rw [h_exp_int_eq, h_swap]
  refine tsum_congr (fun k => ?_)
  -- Goal: ∫ ω, f k ω ∂μ = lam^k / k.factorial * ∫ ω, (X ω)^k ∂μ.
  have h_int_eq : ∫ ω, f k ω ∂μ = ∫ ω, (lam ^ k / k.factorial) * (X ω) ^ k ∂μ := by
    refine integral_congr_ae (ae_of_all _ ?_); intro ω
    change (lam * X ω) ^ k / ↑k.factorial = (lam ^ k / ↑k.factorial) * X ω ^ k
    have : (lam * X ω) ^ k = lam ^ k * X ω ^ k := by ring
    rw [this]; ring
  rw [h_int_eq, integral_const_mul]

/-! ### Step 2.5: per-sample MGF bound for centred bounded variables. -/

/-- **Per-sample Bennett-Bernstein MGF bound.** For a centred bounded
measurable real random variable `Y` with `|Y| ≤ 2M`, mean zero, and centred
moment bound `|E Y^k| ≤ σ² (2M)^{k-2}` for `k ≥ 2`, and any `0 ≤ t` with
`2 M t < 1`, the moment generating function satisfies

`mgf Y μ t ≤ exp(σ² t² / (2 (1 - 2 M t)))`.

This is the per-sample MGF bound at the heart of vdV Lem 19.32. The proof is
standard real analysis: `mgf_bounded_taylor` expands `mgf Y μ t` as a power
series in `t`; the `k=0` term is `1`, the `k=1` term is `t · 0 = 0`, and the
`k ≥ 2` tail is bounded by

`∑_{k≥2} σ² (2Mt)^{k-2} t² / k! ≤ σ² t² · (1/2) · ∑_{j≥0} (2Mt)^j
                                = σ² t² / (2 (1 - 2Mt))`,

after which `1 + u ≤ exp u` upgrades the additive bound to the multiplicative
form.

The proof splits the Taylor series at indices `0`, `1` and the `k ≥ 2` tail,
bounds the tail term-by-term by `σ² t² · (2Mt)^j / 2` (using `(j+2)! ≥ 2` and
`hY_mom`), sums the geometric series via `tsum_geometric_of_lt_one`, and upgrades
the additive bound `mgf ≤ 1 + ...` to the multiplicative form via
`Real.add_one_le_exp`. -/
private lemma bernstein_mgf_centered_bound
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (Y : Ξ → ℝ) (hY_meas : Measurable Y)
    {M σ : ℝ} (hM : 0 ≤ M) (_hσ : 0 ≤ σ)
    (hY_bdd : ∀ ω, |Y ω| ≤ 2 * M)
    (hY_mean : ∫ ω, Y ω ∂μ = 0)
    (hY_mom : ∀ k, 2 ≤ k → |∫ ω, (Y ω) ^ k ∂μ| ≤ σ ^ 2 * (2 * M) ^ (k - 2))
    {t : ℝ} (ht_nn : 0 ≤ t) (ht_lt : 2 * M * t < 1) :
    ProbabilityTheory.mgf Y μ t
      ≤ Real.exp (σ ^ 2 * t ^ 2 / (2 * (1 - 2 * M * t))) := by
  -- Abbreviations.
  set a : ℕ → ℝ := fun k => t ^ k / k.factorial * (∫ ω, (Y ω) ^ k ∂μ) with ha_def
  -- 2Mt ≥ 0 and < 1.
  have h2Mt_nn : 0 ≤ 2 * M * t := mul_nonneg (by linarith) ht_nn
  have h2Mt_lt : 2 * M * t < 1 := ht_lt
  have h_one_minus_pos : 0 < 1 - 2 * M * t := by linarith
  -- σ ^ 2 ≥ 0.
  have hσ2_nn : 0 ≤ σ ^ 2 := sq_nonneg _
  have ht2_nn : 0 ≤ t ^ 2 := sq_nonneg _
  -- |Y ω|^k ≤ (2M)^k pointwise (used several places).
  have hY_pow_bdd : ∀ ω k, |Y ω| ^ k ≤ (2 * M) ^ k := fun ω k =>
    pow_le_pow_left₀ (abs_nonneg _) (hY_bdd ω) k
  -- Power moments are bounded; |∫ Y^k ∂μ| ≤ (2M)^k.
  have hY_pow_int_bdd : ∀ k, |∫ ω, (Y ω) ^ k ∂μ| ≤ (2 * M) ^ k := by
    intro k
    have h1 : |∫ ω, (Y ω) ^ k ∂μ| ≤ ∫ ω, |(Y ω) ^ k| ∂μ := abs_integral_le_integral_abs
    have hmeas : Measurable (fun ω => (Y ω) ^ k) := hY_meas.pow_const _
    have habs : Measurable (fun ω => |(Y ω) ^ k|) := hmeas.norm
    have hbnd : ∀ ω, |(Y ω) ^ k| ≤ (2 * M) ^ k := fun ω => by
      rw [abs_pow]; exact hY_pow_bdd ω k
    have hint_pow : Integrable (fun ω => |(Y ω) ^ k|) μ := by
      refine Integrable.mono' (g := fun _ => (2 * M) ^ k) (integrable_const _)
        habs.aestronglyMeasurable ?_
      refine ae_of_all _ (fun ω => ?_)
      have h0 : 0 ≤ |(Y ω) ^ k| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hbnd ω
    have h2 : ∫ ω, |(Y ω) ^ k| ∂μ ≤ ∫ _, ((2 * M) ^ k : ℝ) ∂μ :=
      integral_mono_ae hint_pow (integrable_const _) (ae_of_all _ hbnd)
    have h3 : ∫ _, ((2 * M) ^ k : ℝ) ∂μ = (2 * M) ^ k := by simp
    exact h1.trans (h2.trans (le_of_eq h3))
  -- Power-series expansion of mgf.
  have h_taylor : ProbabilityTheory.mgf Y μ t = ∑' k : ℕ, a k :=
    mgf_bounded_taylor μ Y hY_meas (by linarith : (0 : ℝ) ≤ 2 * M) hY_bdd t
  -- Termwise bound: |a k| ≤ (2Mt)^k / k!.
  have ha_abs_bdd : ∀ k, |a k| ≤ (2 * M * t) ^ k / k.factorial := by
    intro k
    rw [ha_def]
    simp only
    rw [abs_mul, abs_div, abs_pow, abs_of_nonneg ht_nn, Nat.abs_cast]
    have hfact_pos : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_mul_eq_mul_div]
    rw [div_le_div_iff₀ hfact_pos hfact_pos]
    have : t ^ k * |∫ ω, (Y ω) ^ k ∂μ| ≤ t ^ k * (2 * M) ^ k :=
      mul_le_mul_of_nonneg_left (hY_pow_int_bdd k) (pow_nonneg ht_nn k)
    calc t ^ k * |∫ ω, (Y ω) ^ k ∂μ| * ↑k.factorial
        ≤ t ^ k * (2 * M) ^ k * ↑k.factorial :=
          mul_le_mul_of_nonneg_right this (le_of_lt hfact_pos)
      _ = (2 * M * t) ^ k * ↑k.factorial := by ring
  -- Summability of `a` (via dominator (2Mt)^k/k! which is summable as exp series).
  have h_dom_summable : Summable (fun k : ℕ => (2 * M * t) ^ k / k.factorial) := by
    have h := NormedSpace.expSeries_div_summable (𝔸 := ℝ) (2 * M * t)
    simpa using h
  have ha_summable : Summable a := by
    refine Summable.of_norm_bounded h_dom_summable (fun k => ?_)
    rw [Real.norm_eq_abs]
    exact ha_abs_bdd k
  -- Split the tsum: ∑' k, a k = a 0 + a 1 + ∑' j, a (j + 2).
  have h_split : ∑' k : ℕ, a k = (∑ i ∈ Finset.range 2, a i) + ∑' j : ℕ, a (j + 2) :=
    (ha_summable.sum_add_tsum_nat_add 2).symm
  -- a 0 = 1.
  have ha0 : a 0 = 1 := by
    rw [ha_def]
    simp only
    have h_int_one : ∫ _ω, ((Y _ω : ℝ) ^ 0) ∂μ = 1 := by
      simp [integral_const]
    rw [h_int_one]; simp
  -- a 1 = 0.
  have ha1 : a 1 = 0 := by
    rw [ha_def]
    simp only
    have h_int_Y : ∫ ω, (Y ω) ^ 1 ∂μ = 0 := by
      simp [hY_mean]
    rw [h_int_Y]; simp
  -- ∑ i ∈ range 2, a i = 1.
  have h_first2 : (∑ i ∈ Finset.range 2, a i) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [ha0, ha1]; ring
  -- Tail summability and bound.
  -- The tail term a (j+2) is bounded by σ²·t² · (2Mt)^j / 2.
  set b : ℕ → ℝ := fun j => σ ^ 2 * t ^ 2 / 2 * (2 * M * t) ^ j with hb_def
  have hb_nn : ∀ j, 0 ≤ b j := fun j => by
    rw [hb_def]; positivity
  have hb_summable : Summable b := by
    rw [hb_def]
    exact (summable_geometric_of_lt_one h2Mt_nn h2Mt_lt).mul_left _
  have hb_tsum : ∑' j : ℕ, b j = σ ^ 2 * t ^ 2 / (2 * (1 - 2 * M * t)) := by
    rw [hb_def]
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one h2Mt_nn h2Mt_lt]
    field_simp
  -- Key: |a (j+2)| ≤ b j.
  have h_tail_pt : ∀ j, |a (j + 2)| ≤ b j := by
    intro j
    -- |a (j+2)| ≤ (2Mt)^(j+2) / (j+2)!
    have h1 := ha_abs_bdd (j + 2)
    -- Rewrite (2Mt)^(j+2) = (2Mt)^j · (2Mt)^2 = (2Mt)^j · (4M²t²)
    -- and (j+2)! ≥ 2.
    have hfact_ge_2 : (2 : ℝ) ≤ ((j + 2).factorial : ℝ) := by
      have : 2 ≤ (j + 2).factorial := by
        calc 2 = Nat.factorial 2 := by decide
          _ ≤ (j + 2).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    have hfact_pos : (0 : ℝ) < ((j + 2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    -- (2Mt)^(j+2) = (2Mt)^j · (2Mt)^2
    have hpow_split : (2 * M * t) ^ (j + 2) = (2 * M * t) ^ j * (2 * M * t) ^ 2 := by
      rw [pow_add]
    -- Thus (2Mt)^(j+2) / (j+2)! ≤ (2Mt)^j · (2Mt)^2 / 2 = (2Mt)^j · (2M)² t² / 2.
    have h2Mt_j_nn : 0 ≤ (2 * M * t) ^ j := pow_nonneg h2Mt_nn _
    have h2Mt_sq_nn : 0 ≤ (2 * M * t) ^ 2 := sq_nonneg _
    -- Step: divide-by-larger inequality.
    have h_div_le : (2 * M * t) ^ (j + 2) / ((j + 2).factorial : ℝ)
        ≤ (2 * M * t) ^ (j + 2) / 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hfact_ge_2
    -- Apply the centered-moment bound directly:
    -- `|a (j+2)| ≤ t^(j+2)/(j+2)! · σ² · (2M)^j`.
    -- Since `(j+2)! ≥ 2` and `t^(j+2) · (2M)^j = t² · (2Mt)^j`, this is at most `b j`.
    have h_a_bound : |a (j + 2)|
        ≤ t ^ (j + 2) / ((j + 2).factorial : ℝ) * (σ ^ 2 * (2 * M) ^ j) := by
      rw [ha_def]
      simp only
      rw [abs_mul, abs_div, abs_pow, abs_of_nonneg ht_nn, Nat.abs_cast]
      -- Goal: t^(j+2)/(j+2)! · |∫ Y^(j+2)| ≤ t^(j+2)/(j+2)! · (σ² · (2M)^j)
      have hmom := hY_mom (j + 2) (by omega)
      -- (j + 2 - 2) = j
      have hj_eq : j + 2 - 2 = j := by omega
      rw [hj_eq] at hmom
      refine mul_le_mul_of_nonneg_left hmom ?_
      positivity
    -- Continue: t^(j+2) = t^2 · t^j; rearrange.
    refine h_a_bound.trans ?_
    rw [hb_def]
    -- LHS: t^(j+2)/(j+2)! · σ² · (2M)^j
    -- RHS: σ²·t²/2 · (2Mt)^j
    -- Compute: t^(j+2) · σ² · (2M)^j / (j+2)! ≤ t^(j+2) · σ² · (2M)^j / 2
    --        = σ² · t² · (t · 2M)^j / 2  ... since t^(j+2) · (2M)^j = t^2 · (2Mt)^j.
    have h_step1 : t ^ (j + 2) / ((j + 2).factorial : ℝ) * (σ ^ 2 * (2 * M) ^ j)
        ≤ t ^ (j + 2) / 2 * (σ ^ 2 * (2 * M) ^ j) := by
      apply mul_le_mul_of_nonneg_right
      · apply div_le_div_of_nonneg_left (pow_nonneg ht_nn _) (by norm_num) hfact_ge_2
      · positivity
    refine h_step1.trans ?_
    -- Now: t^(j+2)/2 · σ² · (2M)^j = σ²·t²/2 · (2Mt)^j
    have h_eq : t ^ (j + 2) / 2 * (σ ^ 2 * (2 * M) ^ j)
        = σ ^ 2 * t ^ 2 / 2 * (2 * M * t) ^ j := by
      have hexp : t ^ (j + 2) = t ^ 2 * t ^ j := by
        rw [pow_add]; ring
      rw [hexp]
      have hpow : (2 * M * t) ^ j = (2 * M) ^ j * t ^ j := by
        rw [mul_pow]
      rw [hpow]; ring
    rw [h_eq]
  -- Tail sum is bounded.
  have h_inj : Function.Injective (fun n : ℕ => n + 2) :=
    fun a b h => by simpa using h
  have h_tail_summable : Summable (fun j : ℕ => a (j + 2)) :=
    ha_summable.comp_injective h_inj
  have h_tail_le : ∑' j : ℕ, a (j + 2) ≤ ∑' j : ℕ, b j := by
    have h_le : ∀ j, a (j + 2) ≤ b j := fun j => le_trans (le_abs_self _) (h_tail_pt j)
    exact h_tail_summable.tsum_le_tsum h_le hb_summable
  -- Combine: mgf Y μ t ≤ 1 + σ²t²/(2(1-2Mt)).
  have h_mgf_le_add : ProbabilityTheory.mgf Y μ t
      ≤ 1 + σ ^ 2 * t ^ 2 / (2 * (1 - 2 * M * t)) := by
    rw [h_taylor, h_split, h_first2]
    rw [← hb_tsum]
    linarith
  -- Upgrade additive bound to multiplicative exp via u + 1 ≤ exp u.
  refine h_mgf_le_add.trans ?_
  have := add_one_le_exp (σ ^ 2 * t ^ 2 / (2 * (1 - 2 * M * t)))
  linarith

/-! ### Step 3: one-sided Bernstein (right-tail). -/

/-- Right-tail of the empirical process under iid bounded `f`:
`μ {ω | x < G_n f (ω)} ≤ exp(-x²/(4(σ² + xM/√n)))`.

Proof outline (vdV §19.6):
* Express `G_n f (ω) = (1/√n) Σᵢ Y_i(ω)` where `Y_i(ω) = f(X_i ω) - Pf`.
* Markov on the MGF `μ(G_n f > x) ≤ exp(-λ x) · μ[exp(λ G_n f)]` for any `λ > 0`.
* iid factorisation via `iIndepFun.mgf_sum`:
  `μ[exp(λ G_n f)] = (μ[exp((λ/√n) Y_1)])^n`.
* Power-series expansion (`mgf_bounded_taylor`):
  `μ[exp((λ/√n) Y_1)] = 1 + (1/n) · Σ_{k≥2} (λ/√n)^k/k! · P(f-Pf)^k`
  (the k=1 term vanishes since `P(f-Pf) = 0`).
* Centered-moment bound (`centered_moment_bound_pow`): for `k ≥ 2`,
  `|P(f-Pf)^k| ≤ σ² · (2M)^{k-2}`.
* Optimal-λ choice: `λ = (x/2) / (σ² + x M / √n)`. Telescoping the geometric
  series and using `(1 + a/n)^n ≤ exp(a)` gives
  `μ[exp(λ G_n f)] ≤ exp(λ x / 2)`.
* Combine: `μ(G_n f > x) ≤ exp(-λ x + λ x / 2) = exp(-λ x / 2) =
  exp(-x²/(4(σ² + xM/√n)))`. -/
private lemma bernstein_one_sided
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf_meas : Measurable f)
    {M σ : ℝ} (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hf_bdd : ∀ ω, |f ω| ≤ M)
    (hf_var : ∫ ω, (f ω) ^ 2 ∂P ≤ σ ^ 2)
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    μ {ω : Ξ | x < empiricalProcess P n (fun j : Fin n => X j.val ω) f}
      ≤ ENNReal.ofReal (Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) := by
  -- Edge case: if M = 0, then f = 0 pointwise, G_n f = 0, LHS = 0.
  by_cases hM_zero : M = 0
  · have hf_zero : ∀ ω, f ω = 0 := by
      intro ω
      have := hf_bdd ω
      rw [hM_zero] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    have hG_zero : ∀ ω : Ξ, empiricalProcess P n (fun j : Fin n => X j.val ω) f = 0 := by
      intro ω
      unfold empiricalProcess empiricalAvg
      simp [hf_zero]
    have hset_eq : {ω : Ξ | x < empiricalProcess P n (fun j : Fin n => X j.val ω) f}
        = ∅ := by
      ext ω; simp [hG_zero ω, not_lt.mpr hx.le]
    rw [hset_eq]; simp
  · -- Main case: M > 0. We further split on σ = 0.
    have hM_pos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM_zero)
    -- Setup mean.
    set Pf : ℝ := ∫ ω, f ω ∂P with hPf_def
    have h_int_f : Integrable f P := by
      refine Integrable.mono' (g := fun _ => M) (integrable_const _)
        hf_meas.aestronglyMeasurable ?_
      refine ae_of_all _ (fun ω => ?_)
      simpa [Real.norm_eq_abs] using hf_bdd ω
    have h_abs_Pf : |Pf| ≤ M := by
      have h1 : |Pf| ≤ ∫ ω, |f ω| ∂P := abs_integral_le_integral_abs
      have h2 : ∫ ω, |f ω| ∂P ≤ ∫ _, M ∂P :=
        integral_mono_ae h_int_f.abs (integrable_const _) (ae_of_all _ hf_bdd)
      simpa using h1.trans h2
    -- σ = 0 edge case: f² = 0 ae P ⟹ f = 0 ae P ⟹ G_n f = 0 ae μ.
    by_cases hσ_zero : σ = 0
    · have hf_sq_int : Integrable (fun ω => (f ω) ^ 2) P := by
        refine Integrable.mono' (g := fun _ => M ^ 2) (integrable_const _)
          (hf_meas.pow_const _).aestronglyMeasurable ?_
        refine ae_of_all _ (fun ω => ?_)
        have : |f ω ^ 2| ≤ M ^ 2 := by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hf_bdd ω) 2
        simpa [Real.norm_eq_abs] using this
      have hf_sq_zero : ∫ ω, (f ω) ^ 2 ∂P ≤ 0 := by
        have := hf_var; rw [hσ_zero] at this; simpa using this
      have hf_sq_nn : ∀ᵐ ω ∂P, 0 ≤ (f ω) ^ 2 := ae_of_all _ (fun _ => sq_nonneg _)
      have hf_sq_eq_zero : ∫ ω, (f ω) ^ 2 ∂P = 0 :=
        le_antisymm hf_sq_zero (integral_nonneg_of_ae hf_sq_nn)
      have hf_zero_ae : ∀ᵐ ω ∂P, f ω = 0 := by
        have hae := (integral_eq_zero_iff_of_nonneg_ae hf_sq_nn hf_sq_int).mp hf_sq_eq_zero
        filter_upwards [hae] with ω hω
        exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hω
      have hPf_zero : Pf = 0 := by
        have : ∫ ω, f ω ∂P = 0 :=
          integral_eq_zero_of_ae (by filter_upwards [hf_zero_ae] with ω hω using hω)
        rw [hPf_def]; exact this
      -- For each i : ℕ, μ {ω | f (X i ω) = 0} = 1.
      have hf_zero_aei : ∀ i, μ {ω : Ξ | f (X i ω) = 0} = 1 := by
        intro i
        have hlaw_Xi : μ.map (X i) = P := by
          have := (hX_idem i).map_eq; rw [hX_law] at this; exact this
        have hmeas_set : MeasurableSet {y : Ω | f y = 0} :=
          hf_meas (measurableSet_singleton 0)
        have hP_set : P {y : Ω | f y = 0} = 1 := by
          have hcompl_set : MeasurableSet {y : Ω | f y = 0}ᶜ := hmeas_set.compl
          have h_compl_zero : P {y : Ω | f y = 0}ᶜ = 0 := by
            have := hf_zero_ae
            rw [Filter.eventually_iff] at this
            convert! this using 1
          have : P {y : Ω | f y = 0} + P {y : Ω | f y = 0}ᶜ = P Set.univ :=
            measure_add_measure_compl hmeas_set
          rw [h_compl_zero, add_zero] at this
          rw [this, measure_univ]
        have h_pre : (X i) ⁻¹' {y : Ω | f y = 0} = {ω : Ξ | f (X i ω) = 0} := by
          ext ω; simp
        have hmap : (μ.map (X i)) {y : Ω | f y = 0} = μ ((X i) ⁻¹' {y : Ω | f y = 0}) :=
          Measure.map_apply (hX_meas i) hmeas_set
        rw [hlaw_Xi] at hmap
        rw [← h_pre, ← hmap, hP_set]
      -- Hence ae μ, ∀ i : Fin n, f(X i.val ω) = 0.
      have h_all_i : ∀ᵐ ω ∂μ, ∀ i : Fin n, f (X i.val ω) = 0 := by
        rw [ae_iff]
        have h_subset : {ω : Ξ | ¬ ∀ i : Fin n, f (X i.val ω) = 0}
            ⊆ ⋃ i : Fin n, {ω : Ξ | f (X i.val ω) ≠ 0} := by
          intro ω hω; simp only [Set.mem_setOf_eq, not_forall] at hω
          obtain ⟨i, hi⟩ := hω
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        refine measure_mono_null h_subset ?_
        rw [measure_iUnion_null_iff]
        intro i
        have hμ1 := hf_zero_aei i.val
        have hcompl : {ω : Ξ | f (X i.val ω) = 0}ᶜ = {ω : Ξ | f (X i.val ω) ≠ 0} := by
          ext ω; simp
        have hmeas := (hf_meas.comp (hX_meas i.val)) (measurableSet_singleton 0)
        have h_split : μ {ω : Ξ | f (X i.val ω) = 0}
            + μ {ω : Ξ | f (X i.val ω) = 0}ᶜ = μ Set.univ :=
          measure_add_measure_compl hmeas
        rw [hμ1, measure_univ] at h_split
        have h_eq : μ {ω : Ξ | f (X i.val ω) = 0}ᶜ = 0 := by
          have hh : (1 : ℝ≥0∞) + μ {ω : Ξ | f (X i.val ω) = 0}ᶜ = 1 := h_split
          have hh' : μ {ω : Ξ | f (X i.val ω) = 0}ᶜ = 1 - 1 := by
            rw [add_comm] at hh
            exact (ENNReal.eq_sub_of_add_eq one_ne_top hh)
          rw [tsub_self] at hh'
          exact hh'
        rw [hcompl] at h_eq; exact h_eq
      -- G_n f = 0 ae μ.
      have hG_zero_ae : ∀ᵐ ω ∂μ,
          empiricalProcess P n (fun j : Fin n => X j.val ω) f = 0 := by
        filter_upwards [h_all_i] with ω hω
        unfold empiricalProcess empiricalAvg
        have hsum : ∑ i : Fin n, f (X i.val ω) = 0 :=
          Finset.sum_eq_zero (fun i _ => hω i)
        have h_intf : ∫ y, f y ∂P = 0 := by rw [← hPf_def]; exact hPf_zero
        rw [hsum, h_intf]; ring
      -- Conclude.
      have h_set_le : {ω : Ξ | x < empiricalProcess P n (fun j : Fin n => X j.val ω) f}
          ⊆ {ω : Ξ | empiricalProcess P n (fun j : Fin n => X j.val ω) f ≠ 0} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro h0; rw [h0] at hω; linarith
      have h_null : μ {ω : Ξ | empiricalProcess P n (fun j : Fin n => X j.val ω) f ≠ 0} = 0 := by
        rw [← ae_iff]; exact hG_zero_ae
      calc μ {ω : Ξ | x < empiricalProcess P n (fun j : Fin n => X j.val ω) f}
          ≤ μ {ω : Ξ | empiricalProcess P n (fun j : Fin n => X j.val ω) f ≠ 0} :=
            measure_mono h_set_le
        _ = 0 := h_null
        _ ≤ _ := zero_le
    -- Main case: M > 0, σ > 0.
    · have hσ_pos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ_zero)
      have hσ2_pos : 0 < σ ^ 2 := by positivity
      have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      have hsqrt_n_nn : 0 ≤ Real.sqrt n := hsqrt_n_pos.le
      have hsqrt_n_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_n_pos
      have hsqrt_n_sq : (Real.sqrt n) ^ 2 = n :=
        Real.sq_sqrt (by exact_mod_cast (Nat.zero_le n))
      have hxM_nn : 0 ≤ x * M / Real.sqrt n := by positivity
      have hD_pos : 0 < σ ^ 2 + x * M / Real.sqrt n := by positivity
      have hD_ne : σ ^ 2 + x * M / Real.sqrt n ≠ 0 := ne_of_gt hD_pos
      -- The optimal λ.
      set lam : ℝ := x / (2 * (σ ^ 2 + x * M / Real.sqrt n)) with hlam_def
      have hlam_pos : 0 < lam := by rw [hlam_def]; positivity
      have hlam_nn : 0 ≤ lam := hlam_pos.le
      -- t := lam / √n.
      set tparam : ℝ := lam / Real.sqrt n with htparam_def
      have htparam_pos : 0 < tparam := by rw [htparam_def]; positivity
      have htparam_nn : 0 ≤ tparam := htparam_pos.le
      -- Key algebraic identity: 1 - 2 M tparam = σ² / D.
      have h_one_minus : 1 - 2 * M * tparam = σ ^ 2 / (σ ^ 2 + x * M / Real.sqrt n) := by
        rw [htparam_def, hlam_def]
        field_simp
        ring
      have h_one_minus_pos : 0 < 1 - 2 * M * tparam := by
        rw [h_one_minus]; positivity
      have h_2Mt_lt_one : 2 * M * tparam < 1 := by linarith
      -- ============================================================
      -- Centred random variables Y_i ω := f(X i ω) - Pf.
      -- ============================================================
      set Y : ℕ → Ξ → ℝ := fun i ω => f (X i ω) - Pf with hY_def
      have hY_meas : ∀ i, Measurable (Y i) :=
        fun i => (hf_meas.comp (hX_meas i)).sub_const _
      have hY_bdd : ∀ i ω, |Y i ω| ≤ 2 * M := by
        intro i ω
        calc |f (X i ω) - Pf| ≤ |f (X i ω)| + |Pf| := abs_sub _ _
          _ ≤ M + M := add_le_add (hf_bdd _) h_abs_Pf
          _ = 2 * M := by ring
      -- Identical distribution of Y_i and (f - Pf) on P.
      have hY_id : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (fun y => f y - Pf) μ P := by
        intro i
        have hg : Measurable (fun y : Ω => f y - Pf) := hf_meas.sub_const _
        refine ⟨(hY_meas i).aemeasurable, hg.aemeasurable, ?_⟩
        have hlaw_Xi : μ.map (X i) = P := by
          have := (hX_idem i).map_eq; rw [hX_law] at this; exact this
        have h1 : μ.map (Y i) = (μ.map (X i)).map (fun y => f y - Pf) := by
          have hmm : (μ.map (X i)).map (fun y : Ω => f y - Pf)
              = μ.map ((fun y : Ω => f y - Pf) ∘ X i) :=
            Measure.map_map hg (hX_meas i)
          rw [hmm]
          rfl
        rw [h1, hlaw_Xi]
      -- Mean Y_i = 0.
      have hY_mean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
        intro i
        rw [(hY_id i).integral_eq, integral_sub h_int_f (integrable_const _)]
        simp [hPf_def]
      -- Power moments transfer to (f - Pf).
      have hY_pow_eq : ∀ (i : ℕ) (k : ℕ),
          ∫ ω, (Y i ω) ^ k ∂μ = ∫ ω, (f ω - Pf) ^ k ∂P := by
        intro i k
        have hpk : Measurable (fun y : ℝ => y ^ k) := measurable_id.pow_const k
        have := ((hY_id i).comp (u := fun y : ℝ => y ^ k) hpk).integral_eq
        simpa [Function.comp] using this
      -- Centered moment bound.
      have hY_mom : ∀ (i : ℕ) (k : ℕ), 2 ≤ k →
          |∫ ω, (Y i ω) ^ k ∂μ| ≤ σ ^ 2 * (2 * M) ^ (k - 2) := by
        intro i k hk
        rw [hY_pow_eq i k]
        have hbase :=
          centered_moment_bound_pow P f hf_meas hM hf_bdd k hk
        have h1 : |∫ ω, (f ω - Pf) ^ k ∂P|
            ≤ (∫ ω, (f ω) ^ 2 ∂P) * (2 * M) ^ (k - 2) := by
          simpa [hPf_def] using hbase
        exact h1.trans (mul_le_mul_of_nonneg_right hf_var (by positivity))
      -- Independence: Y_i = (f - Pf) ∘ X_i.
      have hY_iindep : ProbabilityTheory.iIndepFun Y μ := by
        have hcomp : ProbabilityTheory.iIndepFun
            (fun i ω => (fun y => f y - Pf) (X i ω)) μ :=
          hX_iindep.comp (g := fun _ y => f y - Pf) (fun _ => hf_meas.sub_const _)
        exact hcomp
      -- ============================================================
      -- Step A: G_n f X' ω = (Σ_i Y_{i.val} ω) / √n.
      -- ============================================================
      have h_G_eq : ∀ ω : Ξ,
          empiricalProcess P n (fun j : Fin n => X j.val ω) f
            = (∑ i : Fin n, Y i.val ω) / Real.sqrt n := by
        intro ω
        unfold empiricalProcess empiricalAvg
        have h_sum_Y_calc : ∑ i : Fin n, Y i.val ω
            = (∑ i : Fin n, f (X i.val ω)) - n * Pf := by
          have h1 : (∑ i : Fin n, Y i.val ω) = ∑ i : Fin n, (f (X i.val ω) - Pf) := rfl
          rw [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin]
          simp [hPf_def, mul_comm]
        rw [h_sum_Y_calc]
        have hn_ne_real : (n : ℝ) ≠ 0 := by exact_mod_cast (by linarith : 0 < n).ne'
        have h_sqr : Real.sqrt n * Real.sqrt n = n := by
          have := hsqrt_n_sq; rw [pow_two] at this; exact this
        have h_intf : ∫ y, f y ∂P = Pf := by rw [← hPf_def]
        rw [h_intf]
        -- Goal: √n * (n⁻¹ * (Σ f - n*Pf) - Pf) ... actually after sum rewrite
        -- it's √n * (n⁻¹ * Σ - Pf) = (Σ - n*Pf)/√n.
        -- This is field_simp + h_sqr.
        have hsum_term : ∑ i : Fin n, f (X i.val ω) = ∑ i : Fin n, f (X i.val ω) := rfl
        -- Multiply both sides by √n.
        rw [eq_div_iff hsqrt_n_ne]
        ring_nf
        rw [show Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) from hsqrt_n_sq]
        field_simp
        ring
      -- ============================================================
      -- Step B: rewrite event and reduce to {x √n ≤ Σ Y}.
      -- ============================================================
      set Sω : Ξ → ℝ := fun ω => ∑ i : Fin n, Y i.val ω with hSω_def
      have hSω_meas : Measurable Sω := by
        refine Finset.measurable_sum _ ?_
        intros i _; exact hY_meas i.val
      have h_event_eq : {ω : Ξ | x < empiricalProcess P n (fun j : Fin n => X j.val ω) f}
          = {ω : Ξ | x * Real.sqrt n < Sω ω} := by
        ext ω; simp only [Set.mem_setOf_eq]; rw [h_G_eq ω]
        rw [lt_div_iff₀ hsqrt_n_pos]
      rw [h_event_eq]
      have h_subset : {ω : Ξ | x * Real.sqrt n < Sω ω} ⊆ {ω : Ξ | x * Real.sqrt n ≤ Sω ω} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        exact le_of_lt hω
      refine (measure_mono h_subset).trans ?_
      -- ============================================================
      -- Step C: Markov / Chernoff in real form, then bridge to ENNReal.
      -- ============================================================
      -- Compute μ.real {x √n ≤ Sω ω} ≤ exp(-tparam · x √n) · mgf Sω μ tparam.
      -- exp(t · Sω) is integrable since Sω is bounded by 2Mn.
      have h_Sω_bdd : ∀ ω, |Sω ω| ≤ 2 * M * n := by
        intro ω
        have h1 : |Sω ω| ≤ ∑ i : Fin n, |Y i.val ω| := by
          rw [hSω_def]; exact Finset.abs_sum_le_sum_abs _ _
        have h2 : ∑ i : Fin n, |Y i.val ω| ≤ ∑ _ : Fin n, (2 * M) :=
          Finset.sum_le_sum (fun i _ => hY_bdd i.val ω)
        have h3 : ∑ _ : Fin n, (2 * M : ℝ) = n * (2 * M) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        calc |Sω ω| ≤ ∑ i : Fin n, |Y i.val ω| := h1
          _ ≤ ∑ _ : Fin n, (2 * M) := h2
          _ = n * (2 * M) := h3
          _ = 2 * M * n := by ring
      have h_exp_t_int : Integrable (fun ω => Real.exp (tparam * Sω ω)) μ := by
        refine Integrable.mono' (g := fun _ => Real.exp (tparam * (2 * M * n))) (integrable_const _)
          ((measurable_const.mul hSω_meas).exp.aestronglyMeasurable) ?_
        refine ae_of_all _ (fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        have h2 : Sω ω ≤ 2 * M * n := (abs_le.mp (h_Sω_bdd ω)).2
        nlinarith [htparam_nn, h2]
      -- Apply the Chernoff bound: μ.real {x √n ≤ Sω ω} ≤ exp(-tparam · x √n) · mgf Sω μ tparam.
      have h_chernoff :
          μ.real {ω | x * Real.sqrt n ≤ Sω ω}
            ≤ Real.exp (-tparam * (x * Real.sqrt n)) * ProbabilityTheory.mgf Sω μ tparam :=
        ProbabilityTheory.measure_ge_le_exp_mul_mgf
          (μ := μ) (X := Sω) (ε := x * Real.sqrt n) htparam_nn h_exp_t_int
      -- mgf of sum = product of mgfs (iid).
      have h_mgf_sum : ProbabilityTheory.mgf Sω μ tparam
          = ∏ i : Fin n, ProbabilityTheory.mgf (fun ω => Y i.val ω) μ tparam := by
        -- Use precomp for re-indexing iid family from ℕ to Fin n via Fin.val.
        have hZ_iindep : ProbabilityTheory.iIndepFun (fun i : Fin n => Y i.val) μ :=
          hY_iindep.precomp Fin.val_injective
        have hZ_meas : ∀ i : Fin n, Measurable (Y i.val) := fun i => hY_meas i.val
        -- Convert finite sum to indexed.
        have hsum_eq : Sω = ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (fun ω => Y i.val ω) := by
          funext ω
          change ∑ i : Fin n, Y i.val ω
            = (∑ i ∈ (Finset.univ : Finset (Fin n)), fun ω => Y i.val ω) ω
          rw [Finset.sum_apply]
        rw [hsum_eq]
        exact hZ_iindep.mgf_sum hZ_meas Finset.univ
      -- All mgfs equal (identical distribution).
      have h_mgf_eq : ∀ i : Fin n, ProbabilityTheory.mgf (fun ω => Y i.val ω) μ tparam
          = ProbabilityTheory.mgf (Y 0) μ tparam := by
        intro i
        have hidem : ProbabilityTheory.IdentDistrib (Y i.val) (Y 0) μ μ :=
          (hY_id i.val).trans (hY_id 0).symm
        exact ProbabilityTheory.mgf_congr_of_identDistrib (Y i.val) (Y 0) hidem tparam
      have h_mgf_pow : ProbabilityTheory.mgf Sω μ tparam
          = (ProbabilityTheory.mgf (Y 0) μ tparam) ^ n := by
        rw [h_mgf_sum]
        rw [Finset.prod_congr rfl (fun i _ => h_mgf_eq i)]
        rw [Finset.prod_const, Finset.card_fin]
      -- Bound mgf (Y 0) μ tparam ≤ exp(σ² tparam² / (2 (1 - 2M tparam))).
      have h_mgf_bound : ProbabilityTheory.mgf (Y 0) μ tparam
          ≤ Real.exp (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam))) :=
        bernstein_mgf_centered_bound μ (Y 0) (hY_meas 0) hM hσ
          (hY_bdd 0) (hY_mean 0) (fun k hk => hY_mom 0 k hk)
          htparam_nn h_2Mt_lt_one
      have h_mgf_pos : 0 < ProbabilityTheory.mgf (Y 0) μ tparam :=
        ProbabilityTheory.mgf_pos (μ := μ) (by
          -- need integrability of exp(tparam · Y 0)
          refine Integrable.mono' (g := fun _ => Real.exp (tparam * (2 * M))) (integrable_const _)
            ((measurable_const.mul (hY_meas 0)).exp.aestronglyMeasurable) ?_
          refine ae_of_all _ (fun ω => ?_)
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          refine Real.exp_le_exp.mpr ?_
          have h2 := (abs_le.mp (hY_bdd 0 ω)).2
          nlinarith [htparam_nn, h2])
      have h_mgf_pow_bound : (ProbabilityTheory.mgf (Y 0) μ tparam) ^ n
          ≤ Real.exp (n * (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam)))) := by
        calc (ProbabilityTheory.mgf (Y 0) μ tparam) ^ n
            ≤ (Real.exp (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam)))) ^ n :=
              pow_le_pow_left₀ h_mgf_pos.le h_mgf_bound _
          _ = Real.exp (n * (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam)))) := by
              rw [← Real.exp_nat_mul]
      have h_combined : Real.exp (-tparam * (x * Real.sqrt n)) * ProbabilityTheory.mgf Sω μ tparam
          ≤ Real.exp (-tparam * (x * Real.sqrt n)
              + n * (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam)))) := by
        rw [h_mgf_pow]
        rw [Real.exp_add]
        refine mul_le_mul_of_nonneg_left h_mgf_pow_bound (Real.exp_pos _).le
      have h_chernoff' :
          μ.real {ω | x * Real.sqrt n ≤ Sω ω}
            ≤ Real.exp (-tparam * (x * Real.sqrt n)
                + n * (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam)))) :=
        h_chernoff.trans h_combined
      -- ============================================================
      -- Step D: optimal-λ algebra: the exponent ≤ -x²/(4 D).
      -- ============================================================
      -- Recall: 1 - 2M tparam = σ²/D, tparam = lam/√n, lam = x/(2D).
      -- So:
      --   (σ² tparam² / (2(1 - 2M tparam))) = (σ² (lam/√n)² · D / (2 σ²)) = lam² D / (2 n)
      --   n · ... = lam² D / 2 = (x/(2D))² D / 2 = x²/(8 D)
      --   -tparam · x √n = -lam x = -x²/(2D) = -4 x² / (8D)
      --   sum: -4x²/(8D) + x²/(8D) = -3x²/(8D) ≤ -x²/(4D) = -2x²/(8D)  (since -3/8 ≤ -2/8).
      -- Combined exponent computation. Use a clean intermediate variable for √n.
      have h_sigma_t2 : (n : ℝ) * (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam)))
          = x ^ 2 / (8 * (σ ^ 2 + x * M / Real.sqrt n)) := by
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 1 ≤ n from hn)
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hsqrt_sq : Real.sqrt n ^ 2 = (n : ℝ) := hsqrt_n_sq
        have hD_pos' : 0 < σ ^ 2 + x * M / Real.sqrt n := hD_pos
        have hD_ne' : σ ^ 2 + x * M / Real.sqrt n ≠ 0 := hD_ne
        have hσ_ne : σ ^ 2 ≠ 0 := ne_of_gt hσ2_pos
        -- Abstract Real.sqrt n to a variable s with s² = n.
        set s := Real.sqrt n with hs_def
        have hs_pos : 0 < s := hsqrt_n_pos
        have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        have hs_sq : s ^ 2 = (n : ℝ) := hsqrt_sq
        rw [show (n : ℝ) = s ^ 2 from hs_sq.symm]
        rw [h_one_minus, htparam_def, hlam_def]
        change s ^ 2 * (σ ^ 2 * (x / (2 * (σ ^ 2 + x * M / s)) / s) ^ 2 /
            (2 * (σ ^ 2 / (σ ^ 2 + x * M / s))))
          = x ^ 2 / (8 * (σ ^ 2 + x * M / s))
        field_simp
        ring
      have h_neg_t : -tparam * (x * Real.sqrt n)
          = -(x ^ 2 / (2 * (σ ^ 2 + x * M / Real.sqrt n))) := by
        rw [htparam_def, hlam_def]
        field_simp
      have h_total_exponent : -tparam * (x * Real.sqrt n)
          + (n : ℝ) * (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam)))
          = -(x ^ 2 / (2 * (σ ^ 2 + x * M / Real.sqrt n)))
            + x ^ 2 / (8 * (σ ^ 2 + x * M / Real.sqrt n)) := by
        rw [h_neg_t, h_sigma_t2]
      have h_exp_bound : -(x ^ 2 / (2 * (σ ^ 2 + x * M / Real.sqrt n)))
          + x ^ 2 / (8 * (σ ^ 2 + x * M / Real.sqrt n))
          ≤ -(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)) := by
        -- Common denominator argument:
        -- LHS = -3 x² / (8 D), RHS = -x²/(4D) = -2 x²/(8D). LHS ≤ RHS iff -3 ≤ -2 ✓.
        set D : ℝ := σ ^ 2 + x * M / Real.sqrt n with hD_set
        have hD_pos' : 0 < D := hD_pos
        have hD_ne' : D ≠ 0 := ne_of_gt hD_pos'
        have hxx : 0 ≤ x ^ 2 := sq_nonneg _
        have hLHS : -(x ^ 2 / (2 * D)) + x ^ 2 / (8 * D) = -3 * x ^ 2 / (8 * D) := by
          field_simp; ring
        have hRHS : -(x ^ 2) / (4 * D) = -2 * x ^ 2 / (8 * D) := by
          field_simp; ring
        rw [hLHS, hRHS]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hD_pos', hxx]
      -- Compose: the real exponent ≤ -x²/(4D), so exp ≤ exp(-x²/(4D)).
      have h_real_exp_le : Real.exp (-tparam * (x * Real.sqrt n)
              + n * (σ ^ 2 * tparam ^ 2 / (2 * (1 - 2 * M * tparam))))
          ≤ Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n))) := by
        rw [h_total_exponent]
        exact Real.exp_le_exp.mpr h_exp_bound
      have h_real_bound : μ.real {ω | x * Real.sqrt n ≤ Sω ω}
          ≤ Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n))) :=
        h_chernoff'.trans h_real_exp_le
      -- ============================================================
      -- Step E: lift μ.real to μ ≤ ENNReal.ofReal.
      -- ============================================================
      have hmeas_set : MeasurableSet {ω : Ξ | x * Real.sqrt n ≤ Sω ω} := by
        exact measurableSet_le measurable_const hSω_meas
      have hμ_ne_top : μ {ω : Ξ | x * Real.sqrt n ≤ Sω ω} ≠ ∞ := measure_ne_top _ _
      have h_real_eq : μ.real {ω | x * Real.sqrt n ≤ Sω ω}
          = (μ {ω : Ξ | x * Real.sqrt n ≤ Sω ω}).toReal := rfl
      have h_exp_nn : 0 ≤ Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n))) :=
        (Real.exp_pos _).le
      rw [ENNReal.le_ofReal_iff_toReal_le hμ_ne_top h_exp_nn]
      rw [← h_real_eq]
      exact h_real_bound

/-! ### Step 5: assembly — two-sided Bernstein from one-sided. -/

/-- Bernstein's inequality assembled from `bernstein_one_sided` + `empiricalProcess_neg`.
The analytic proof lives in this lower-level module, which `Maximal.lean` imports;
the public `bernstein_inequality` wrapper is grouped there with the finite-class and
bracketing maximal inequalities and delegates to `bernstein_inequality_aux` below. -/
private lemma bernstein_two_sided
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf_meas : Measurable f)
    {M σ : ℝ} (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hf_bdd : ∀ ω, |f ω| ≤ M)
    (hf_var : ∫ ω, (f ω) ^ 2 ∂P ≤ σ ^ 2)
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    μ {ω : Ξ | x < |empiricalProcess P n (fun j : Fin n => X j.val ω) f|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) := by
  -- Set the right-tail event for f and -f.
  let R₁ : Set Ξ := {ω | x < empiricalProcess P n (fun j : Fin n => X j.val ω) f}
  let R₂ : Set Ξ := {ω | x < empiricalProcess P n (fun j : Fin n => X j.val ω) (fun ω => -f ω)}
  -- Step (a): `{|G_n f| > x} ⊆ R₁ ∪ R₂`.
  have h_subset :
      {ω : Ξ | x < |empiricalProcess P n (fun j : Fin n => X j.val ω) f|} ⊆ R₁ ∪ R₂ := by
    intro ω hω
    simp only [Set.mem_setOf_eq, lt_abs] at hω
    rcases hω with hpos | hneg
    · exact Or.inl hpos
    · refine Or.inr ?_
      change x < empiricalProcess P n (fun j : Fin n => X j.val ω) (fun ω => -f ω)
      rw [empiricalProcess_neg]
      linarith
  -- Step (b): bound each tail by exp(...).
  -- `f` itself.
  have hbnd1 : μ R₁ ≤ ENNReal.ofReal
      (Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) :=
    bernstein_one_sided P f hf_meas hM hσ hf_bdd hf_var
      hX_meas hX_iindep hX_idem hX_law n hn hx
  -- `-f` has the same hypotheses (M, σ unchanged).
  have hf_neg_meas : Measurable (fun ω => -f ω) := hf_meas.neg
  have hf_neg_bdd : ∀ ω, |(fun ω => -f ω) ω| ≤ M := by
    intro ω
    change |-f ω| ≤ M
    rw [abs_neg]; exact hf_bdd ω
  have hf_neg_var : ∫ ω, ((fun ω => -f ω) ω) ^ 2 ∂P ≤ σ ^ 2 := by
    have : ∀ ω, ((-f ω) : ℝ) ^ 2 = (f ω) ^ 2 := by intro ω; ring
    simp_rw [this]; exact hf_var
  have hbnd2 : μ R₂ ≤ ENNReal.ofReal
      (Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) :=
    bernstein_one_sided P (fun ω => -f ω) hf_neg_meas hM hσ hf_neg_bdd hf_neg_var
      hX_meas hX_iindep hX_idem hX_law n hn hx
  -- Step (c): combine via measurable monotonicity + measure_union_le.
  have h_chain : μ {ω : Ξ | x < |empiricalProcess P n (fun j : Fin n => X j.val ω) f|}
      ≤ μ R₁ + μ R₂ :=
    (measure_mono h_subset).trans (measure_union_le _ _)
  -- Combine bounds.
  have h_two_exp : ENNReal.ofReal
        (Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n))))
      + ENNReal.ofReal
        (Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n))))
      = ENNReal.ofReal
        (2 * Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) := by
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    congr 1; ring
  calc μ {ω : Ξ | x < |empiricalProcess P n (fun j : Fin n => X j.val ω) f|}
      ≤ μ R₁ + μ R₂ := h_chain
    _ ≤ ENNReal.ofReal
          (Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n))))
        + ENNReal.ofReal
          (Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) :=
        add_le_add hbnd1 hbnd2
    _ = ENNReal.ofReal
          (2 * Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) := h_two_exp

/-- Public assembly of `bernstein_inequality` body — invoked from
`Maximal.lean`. Identical statement; routes through the private
`bernstein_two_sided`.

**Reference.** van der Vaart, *Asymptotic Statistics* (1998), §19.6, Lemma 19.32. -/
lemma bernstein_inequality_aux
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf_meas : Measurable f)
    {M σ : ℝ} (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hf_bdd : ∀ ω, |f ω| ≤ M)
    (hf_var : ∫ ω, (f ω) ^ 2 ∂P ≤ σ ^ 2)
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    μ {ω : Ξ | x < |empiricalProcess P n (fun j : Fin n => X j.val ω) f|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) :=
  bernstein_two_sided P f hf_meas hM hσ hf_bdd hf_var
    hX_meas hX_iindep hX_idem hX_law n hn hx

end AsymptoticStatistics.EmpiricalProcess
