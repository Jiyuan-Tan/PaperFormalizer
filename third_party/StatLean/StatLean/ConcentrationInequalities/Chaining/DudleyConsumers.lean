module
public import StatLean.ConcentrationInequalities.Chaining.Dudley
public import StatLean.ConcentrationInequalities.Chaining.DudleySup

@[expose] public section

/-!
# Dudley plug-in corollaries — exponential entropy branch

Evaluated plug-in corollaries of Dudley's inequality for classes with
exponential-type entropy: if
$\mathcal{N}(T, d, \varepsilon) \le e^{C/\varepsilon}$ on $(0, D]$, then
$$ \int_0^{D} \sqrt{\log \mathcal{N}(T,d,\varepsilon)}\, d\varepsilon
     \;\le\; \int_0^{D} \sqrt{C/\varepsilon}\, d\varepsilon
     \;=\; 2\sqrt{C D}, $$
so a process with sub-gaussian increments satisfies
$\mathbb{E} \sup_{t} |X_t - X_{t_0}| \le 80\, K \sqrt{C D}$. This is the
shape consumed by the Lipschitz-class law of large numbers.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2 (application arithmetic; Exercise 8.9-
flavored entropy bound for Lipschitz classes) and the Exercise 8.9/8.10
pipeline.

**Proof formalization notes.** Per the batch's consumer-ownership rule, this
file keeps ONLY the exponential branch: the polynomial (`(2/ε)^m`, VC-type)
branch and its integral evaluation are OWNED by the VC cluster
(`VC/EntropyIntegral.lean`), which plugs `dudley_inequality_abs_of_finite` (frozen
constant `40`) directly. The integral evaluation
`∫_0^D √(C/ε) dε = 2√(CD)` is exact (via `integral_rpow`), deliberately
avoiding the `Γ(3/2)` change-of-variables. Headline constant frozen to
`80·K·√(C·D)` (= `40` from `dudley_inequality_abs_of_finite` × `2` from the integral
evaluation). The covering hypothesis shape
`hcov : ∀ ε ∈ Ioc 0 D, coveringNumber T ε ≠ ⊤ ∧ (toNat 𝒩 : ℝ) ≤ exp (C/ε)`
is frozen for the gaussian-lln cluster. Named-sorry fallback of this work
item: `integral_sqrt_div_le` (the `integral_rpow` arithmetic), with the two
corollary skeletons standing on it.

**Bibliographic comments.** Entropy bounds of order $e^{C/\varepsilon}$ for
Lipschitz function classes go back to Kolmogorov–Tikhomirov (1959, §2); the
plug-in route through Dudley's integral is the standard empirical-process
argument (Dudley 1967; van der Vaart–Wellner 1996, §2.7).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- Exact evaluation `∫_0^D √(C/ε) dε = 2√(CD)`, stated as an inequality
(via `integral_rpow` on `ε^{-1/2}`). -/
lemma integral_sqrt_div_le {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD : 0 < D) :
    ∫ ε in Set.Ioc (0 : ℝ) D, Real.sqrt (C / ε)
      ≤ 2 * Real.sqrt (C * D) := by
  have hcongr : Set.EqOn (fun ε => Real.sqrt (C / ε))
      (fun ε => Real.sqrt C * ε ^ (-(1 / 2) : ℝ)) (Set.Ioc (0 : ℝ) D) := by
    intro ε hε
    have hεpos : 0 < ε := hε.1
    simp only
    rw [Real.sqrt_div hC, div_eq_mul_inv, Real.sqrt_eq_rpow ε, ← Real.rpow_neg hεpos.le]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_const_mul,
    ← intervalIntegral.integral_of_le hD.le,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
  rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), ← Real.sqrt_eq_rpow, Real.sqrt_mul hC,
    sub_zero]
  exact le_of_eq (by ring)

/-- Integrability of the majorant `ε ↦ √(C/ε)` on `(0, D]` (the RHS of the
entropy-integral bound), obtained via `ε^{-1/2}` interval integrability. -/
private lemma integrableOn_sqrt_div {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) :
    MeasureTheory.IntegrableOn (fun ε => Real.sqrt (C / ε)) (Set.Ioc (0 : ℝ) D) := by
  have hcongr : Set.EqOn (fun ε => Real.sqrt (C / ε))
      (fun ε => Real.sqrt C * ε ^ (-(1 / 2) : ℝ)) (Set.Ioc (0 : ℝ) D) := by
    intro ε hε
    have hεpos : 0 < ε := hε.1
    simp only
    rw [Real.sqrt_div hC, div_eq_mul_inv, Real.sqrt_eq_rpow ε, ← Real.rpow_neg hεpos.le]
  rw [integrableOn_congr_fun hcongr measurableSet_Ioc]
  refine MeasureTheory.Integrable.const_mul ?_ (Real.sqrt C)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hD.le).mp
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))

/-- **Entropy-integral evaluation, exponential branch** (HDP §8.2 /
Exercise 8.9 shape): `𝒩 ≤ e^{C/ε}` on `(0, D]` gives
`dudleyIntegral T D ≤ 2√(CD)`. -/
theorem dudleyIntegral_le_of_cov_le_exp_div {T : Set E}
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD : 0 < D)
    -- USER-INPUT: Lipschitz-type entropy bound 𝒩 ≤ e^{C/ε} with finite
    -- covering numbers; HDP §8.2 / Exercise 8.9
    (hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) D, coveringNumber T ε ≠ ⊤ ∧
      ((coveringNumber T ε).toNat : ℝ) ≤ Real.exp (C / ε)) :
    dudleyIntegral T D ≤ 2 * Real.sqrt (C * D) := by
  refine le_trans ?_ (integral_sqrt_div_le hC hD)
  unfold dudleyIntegral
  refine integral_mono_of_nonneg (ae_of_all _ (fun ε => sqrtLogCov_nonneg T ε))
    (integrableOn_sqrt_div hC hD) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun ε hε => ?_))
  have hε0 : 0 < ε := hε.1
  have hexp1 : (1 : ℝ) ≤ Real.exp (C / ε) := Real.one_le_exp (by positivity)
  have hb := sqrtLogCov_le_sqrt_log_of_le hne (hcov ε hε).1 (hcov ε hε).2 hexp1
  rwa [Real.log_exp] at hb

/-- **Dudley plug-in, exponential branch** (HDP §8.2, Exercise 8.9/8.10
pipeline): sub-gaussian increments + entropy `𝒩 ≤ e^{C/ε}` give the fully
evaluated bound `E sup |X_t − X_{t₀}| ≤ 80·K·√(CD)`. Frozen headline
constant `80 = 40 × 2`. -/
theorem dudley_abs_of_cov_le_exp_div {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T) {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hdiam : Metric.diam T ≤ D)
    -- USER-INPUT: Lipschitz-type entropy bound 𝒩 ≤ e^{C/ε}; HDP §8.2 /
    -- Exercise 8.9
    (hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) D, coveringNumber T ε ≠ ⊤ ∧
      ((coveringNumber T ε).toNat : ℝ) ≤ Real.exp (C / ε)) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 80 * K * Real.sqrt (C * D) := by
  have h2 : dudleyIntegral T D ≤ 2 * Real.sqrt (C * D) :=
    dudleyIntegral_le_of_cov_le_exp_div hne hC hD0 hcov
  calc ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * dudleyIntegral T D :=
        dudley_inequality_abs_of_finite hfin hne hmeas hinc ht₀ hdiam hD0
    _ ≤ 40 * K * (2 * Real.sqrt (C * D)) := by
        refine mul_le_mul_of_nonneg_left h2 ?_; positivity
    _ = 80 * K * Real.sqrt (C * D) := by ring

/-- **Entropy-integral evaluation, exponential branch, `ℝ≥0∞` twin**
(HDP §8.2 / Exercise 8.9 shape): `𝒩 ≤ e^{C/ε}` on `(0, D]` gives
`dudleyLIntegral T D ≤ ENNReal.ofReal (2√(CD))` — in particular the
lintegral carrier is finite, which is the `hDL` junk-guard the sup-form
displays need. -/
theorem dudleyLIntegral_le_of_cov_le_exp_div {T : Set E}
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD : 0 < D)
    -- USER-INPUT: Lipschitz-type entropy bound 𝒩 ≤ e^{C/ε} with finite
    -- covering numbers; HDP §8.2 / Exercise 8.9
    (hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) D, coveringNumber T ε ≠ ⊤ ∧
      ((coveringNumber T ε).toNat : ℝ) ≤ Real.exp (C / ε)) :
    dudleyLIntegral T D ≤ ENNReal.ofReal (2 * Real.sqrt (C * D)) := by
  unfold dudleyLIntegral
  have hmono : ∫⁻ ε in Set.Ioc (0 : ℝ) D, ENNReal.ofReal (sqrtLogCov T ε)
      ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) D, ENNReal.ofReal (Real.sqrt (C / ε)) := by
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun ε hε => ?_))
    have hε0 : 0 < ε := hε.1
    have hexp1 : (1 : ℝ) ≤ Real.exp (C / ε) := Real.one_le_exp (by positivity)
    have hb := sqrtLogCov_le_sqrt_log_of_le hne (hcov ε hε).1 (hcov ε hε).2 hexp1
    rw [Real.log_exp] at hb
    exact ENNReal.ofReal_le_ofReal hb
  refine hmono.trans ?_
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_sqrt_div hC hD)
    (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (integral_sqrt_div_le hC hD)

/-- **Dudley plug-in, exponential branch, separable supremum** (HDP §8.2,
Exercise 8.9/8.10 pipeline; general `T`): sub-gaussian increments + entropy
`𝒩 ≤ e^{C/ε}` give `E sup_{t∈T} |X_t − X_{t₀}| ≤ 80·K·√(CD)` for a
separable version of the process — the genuine-supremum upgrade of
`dudley_abs_of_cov_le_exp_div` (which requires `T.Finite`). Frozen headline
constant `80 = 40 × 2`, as in the finite twin. -/
theorem dudley_abs_of_cov_le_exp_div_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T) {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hdiam : Metric.diam T ≤ D)
    -- USER-INPUT: Lipschitz-type entropy bound 𝒩 ≤ e^{C/ε}; HDP §8.2 /
    -- Exercise 8.9
    (hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) D, coveringNumber T ε ≠ ⊤ ∧
      ((coveringNumber T ε).toNat : ℝ) ≤ Real.exp (C / ε)) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 80 * K * Real.sqrt (C * D) := by
  -- Finite covering numbers at EVERY positive radius: below `D` from `hcov`,
  -- above `D` by anti-monotonicity of the covering number.
  have hcovall : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤ := by
    intro ε hε
    rcases le_or_gt ε D with h | h
    · exact (hcov ε ⟨hε, h⟩).1
    · exact ne_top_of_le_ne_top (hcov D ⟨hD0, le_refl D⟩).1 (coveringNumber_anti h.le)
  have hb : dudleyLIntegral T D ≤ ENNReal.ofReal (2 * Real.sqrt (C * D)) :=
    dudleyLIntegral_le_of_cov_le_exp_div hne hC hD0 hcov
  have hDL : dudleyLIntegral T D ≠ ⊤ := (hb.trans_lt ENNReal.ofReal_lt_top).ne
  have htr : (dudleyLIntegral T D).toReal ≤ 2 * Real.sqrt (C * D) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  calc ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * (dudleyLIntegral T D).toReal :=
        dudley_inequality_abs_separable_real hcovall hne hmeas hinc hsep ht₀ hDL hdiam hD0
    _ ≤ 40 * K * (2 * Real.sqrt (C * D)) := by
        refine mul_le_mul_of_nonneg_left htr ?_; positivity
    _ = 80 * K * Real.sqrt (C * D) := by ring

/-- **Dudley plug-in, exponential branch, countable supremum** (HDP §8.2):
the countable-`T` display of `dudley_abs_of_cov_le_exp_div_separable`. -/
theorem dudley_abs_of_cov_le_exp_div_countable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T) {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hdiam : Metric.diam T ≤ D)
    -- USER-INPUT: Lipschitz-type entropy bound 𝒩 ≤ e^{C/ε}; HDP §8.2 /
    -- Exercise 8.9
    (hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) D, coveringNumber T ε ≠ ⊤ ∧
      ((coveringNumber T ε).toNat : ℝ) ≤ Real.exp (C / ε)) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 80 * K * Real.sqrt (C * D) := by
  exact dudley_abs_of_cov_le_exp_div_separable hne hmeas hinc
    (IsSeparableProcess.of_countable hcnt) ht₀ hC hD0 hdiam hcov

end StatLean.ConcentrationInequalities
