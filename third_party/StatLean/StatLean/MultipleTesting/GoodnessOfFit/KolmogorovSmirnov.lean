module
public import StatLean.MultipleTesting.ForMathlib.EmpiricalProcessSup

@[expose] public section

/-!
# Kolmogorov–Smirnov test — level guarantee

The one-sided Kolmogorov–Smirnov test of the global null hypothesis rejects when the one-sided KS
statistic
$$ \mathrm{KS}^{+} \;=\; \sup_{t} \bigl(F_n(t) - t\bigr) $$
exceeds the threshold $u_\alpha = \sqrt{\log(n/\alpha) / (2n)}$, where $F_n$ is the empirical CDF of
$n$ p-values. Under the global null — that the $n$ p-values are jointly independent and each is
super-uniform (its CDF lies below the uniform CDF) — the test has **level** $\alpha$, i.e. its
type-I error is controlled:
$$ \mu\bigl\{\, \mathrm{KS}^{+} \ge u_\alpha \,\bigr\} \;\le\; \alpha . $$
This follows immediately from the one-sided KS union-bound tail inequality (formalized in
`ForMathlib/EmpiricalProcessSup.ksPlus_tail_union`): substituting the threshold $u_\alpha$ makes the
union tail equal to $n\,e^{-2n\,u_\alpha^{2}} = n\cdot(\alpha/n) = \alpha$.

The sharp Dvoretzky–Kiefer–Wolfowitz–Massart constant would let the threshold improve to
$\sqrt{\log(2/\alpha)/(2n)}$; the version proved here uses the (weaker) union-bound tail, which is the
inequality actually available in the library.

**Reference.** E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford University,
2023. Lecture 3, §3.3.1 (Kolmogorov–Smirnov goodness-of-fit test).

**Proof formalization notes.** The main result (`ks_test_level`): under the global null (jointly
independent, super-uniform p-values), $\mu\{\mathrm{KS}^{+} \ge u_\alpha\} \le \alpha$. The proof
plugs the threshold $u = u_\alpha$ (which is $\ge 0$) into the one-sided union-bound KS tail
`ksPlus_tail_union`, then simplifies the resulting bound $n\,e^{-2n u_\alpha^{2}} = \alpha$ using
$u_\alpha^{2} = \log(n/\alpha)/(2n)$ and $e^{-\log(n/\alpha)} = \alpha/n$. The library uses the
union-bound tail rather than the sharp Massart constant, hence the threshold $\sqrt{\log(n/\alpha)/(2n)}$
in place of the sharper $\sqrt{\log(2/\alpha)/(2n)}$.

**Bibliographic comments.** The two-sided KS statistic and its limiting distribution originate with
A. N. Kolmogorov, "Sulla determinazione empirica di una legge di distribuzione," *Giornale
dell'Istituto Italiano degli Attuari* **4** (1933), 83–91, who derived the asymptotic distribution of
$\sqrt{n}\,\sup_t |F_n(t) - F(t)|$ for continuous $F$. N. V. Smirnov, "Table for estimating the
goodness of fit of empirical distributions," *Annals of Mathematical Statistics* **19** (1948),
279–281, tabulated the limiting distribution and studied the two-sample form. The *non-asymptotic*
exponential tail bound used here (and the underlying finite-$n$ control of the empirical process
supremum) is the Dvoretzky–Kiefer–Wolfowitz inequality — A. Dvoretzky, J. Kiefer, and J. Wolfowitz,
"Asymptotic minimax character of the sample distribution function and of the classical multinomial
estimator," *Annals of Mathematical Statistics* **27** (1956), 642–669 — with the sharp leading
constant established by P. Massart, "The tight constant in the Dvoretzky–Kiefer–Wolfowitz
inequality," *Annals of Probability* **18** (1990), 1269–1283. The specific level-$\alpha$ KS test
calibration formalized here is the textbook synthesis presented in Candès's STAT 300C notes; the
union-bound threshold $\sqrt{\log(n/\alpha)/(2n)}$ is a standard pedagogical simplification rather
than a separately seminal result.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Kolmogorov–Smirnov test level** (Candès, Lecture 3, §3.3.1, STAT 300C). Rejecting the global
null when `KS⁺ ≥ u_α` with `u_α = √(log(n/α)/(2n))` has type-I error at most `α`: directly from the
one-sided KS tail `ksPlus_tail_union`, since `n·e^{−2n u_α²} = α`. -/
theorem ks_test_level {n : ℕ} (hn : 0 < n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin n → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L3 §3.3.1
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L3 §3.3.1
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is super-uniform; Candès L3 §3.3.1
    (hnull : ∀ j, SuperUniform (p j) μ)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    μ {ω | Real.sqrt (Real.log ((n : ℝ) / α) / (2 * n)) ≤ ksPlus p ω} ≤ ENNReal.ofReal α := by
  set u := Real.sqrt (Real.log ((n : ℝ) / α) / (2 * n)) with hu_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≠ 0 := ne_of_gt hnR
  -- `n/α ≥ 1` (since `α < 1 ≤ n`), hence `log(n/α) ≥ 0`, hence the sqrt argument is `≥ 0`.
  have hαn : α ≤ (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog_nonneg : 0 ≤ Real.log ((n : ℝ) / α) := Real.log_nonneg ((one_le_div hα0).2 hαn)
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have harg_nonneg : 0 ≤ Real.log ((n : ℝ) / α) / (2 * n) := div_nonneg hlog_nonneg h2n.le
  have husq : u ^ 2 = Real.log ((n : ℝ) / α) / (2 * n) := Real.sq_sqrt harg_nonneg
  -- Plug the threshold `u = u_α` (which is `≥ 0`) into the one-sided union-bound KS tail.
  refine le_trans (ksPlus_tail_union μ p hmeas hindep hnull hn (Real.sqrt_nonneg _)) (le_of_eq ?_)
  -- It remains to simplify `n · e^{−2n u²} = α`.
  congr 1
  rw [husq]
  have hexp_arg : -2 * (n : ℝ) * (Real.log ((n : ℝ) / α) / (2 * n)) = -Real.log ((n : ℝ) / α) := by
    field_simp
  rw [hexp_arg, Real.exp_neg, Real.exp_log (div_pos hnR hα0), inv_div, ← mul_div_assoc,
    mul_div_cancel_left₀ _ hnR']

end StatLean.MultipleTesting
