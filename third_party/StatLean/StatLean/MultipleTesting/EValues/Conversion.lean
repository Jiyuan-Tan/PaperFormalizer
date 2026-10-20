module
public import StatLean.MultipleTesting.EValues.Defs
public import StatLean.MultipleTesting.PValues.Defs

@[expose] public section

/-!
# E-to-p conversion: the reciprocal of an e-value is a conservative p-value

Let $E$ be an *e-variable* for a simple null hypothesis with law $\mu$ — a nonnegative random
variable with $\mathbb{E}_\mu[E] \le 1$. Then its reciprocal $1/E$ is a (conservative) *p-variable*:
for every level $\alpha \in (0,1)$,
$$ \mu\{\,1/E \le \alpha\,\} \le \alpha. $$
This is the simplest *calibrator* turning evidence measured on the e-value scale into a valid
p-value, so e-values plug directly into p-value-based multiple-testing procedures.

The main result (`isPVariable_inv_of_isEVariable`) states exactly this. We also record the
companion `superUniform_inv_of_isEVariable`, which says $1/E$ is *super-uniform*
($\mu\{1/E \le t\} \le t$ for all $t \ge 0$, not only $t \in (0,1)$) — the form consumed by the
Benjamini–Hochberg / Holm assembly files, so e-values feed directly into FDR control.

**Added hypothesis (Lean-only).** Beyond the e-variable assumption, the formalization requires $E$
to be strictly positive pointwise, $E(\omega) > 0$. This rules out Lean's `1/0 = 0` convention,
which would otherwise map the no-evidence event $E = 0$ (intuitively p-value $1$) to $1/E = 0$ and
spuriously inflate $\mu\{1/E \le \alpha\}$. E-variables arising as likelihood ratios are positive,
so this is no loss of generality.

**Reference.** E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford University,
2023, Lecture 15, Proposition 3 (e-to-p calibration).

**Proof formalization notes.** Fix $\alpha \in (0,1)$. With $E > 0$ we have the equivalence
$1/E \le \alpha \iff E \ge 1/\alpha$, so Markov's inequality gives
$\mu\{E \ge 1/\alpha\} \le \alpha \cdot \mathbb{E}_\mu[E] \le \alpha$, using $\mathbb{E}_\mu[E] \le 1$.
In Lean the event is rewritten in `ENNReal.ofReal` form and closed by the extended-nonnegative
Markov bound `meas_ge_le_lintegral_div`, after which `ENNReal.div_le_div_right` together with the
e-variable bound `hE.expectation_le_one` and `ENNReal.ofReal_inv_of_pos` finishes the calc. The
super-uniform version extends the bound from $(0,1)$ to all $t \ge 0$ by separately handling $t = 0$
(where $E > 0$ makes the event $\{1/E \le 0\}$ empty).

**Bibliographic comments.** The reciprocal calibrator is due to Vladimir Vovk and Ruodu Wang,
"E-values: Calibration, combination and applications", *The Annals of Statistics* **49**(3):
1736–1754, 2021 (DOI 10.1214/20-AOS2020). There, calibrators from e-values to p-values are studied
systematically (their §2); the map $e \mapsto \min(1, 1/e)$ — equivalently the bound used here,
$\mu\{1/E \le \alpha\} \le \alpha$ — is the canonical such calibrator and follows from Markov's
inequality. The Candès lecture notes present this as the standard e-to-p conversion.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The reciprocal of an e-variable is [[`SuperUniform`]] — the null-p-value hypothesis consumed by
`benjamini_hochberg_fdr_le` / the Holm assembly. Corollary of `isPVariable_inv_of_isEVariable`
extended from `(0,1)` to all `t ≥ 0`. -/
theorem superUniform_inv_of_isEVariable {E : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    -- USER-INPUT: E is an e-variable for the null μ; Candès L15 Def. 3
    (hE : IsEVariable E μ)
    -- LEAN-ONLY: E positive (see `isPVariable_inv_of_isEVariable`)
    (hpos : ∀ ω, 0 < E ω) :
    SuperUniform (fun ω => 1 / E ω) μ := by
  intro t ht
  -- For `t = 0`: `E > 0 ⟹ 1/E > 0`, so the event is empty.
  rcases ht.eq_or_lt with rfl | ht
  · have hempty : {ω | 1 / E ω ≤ (0 : ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, one_div]
      exact inv_pos.mpr (hpos ω)
    rw [hempty, measure_empty]
    exact zero_le
  -- For `t > 0`: rewrite the event in `ofReal` form and apply lintegral Markov.
  have hset : {ω | 1 / E ω ≤ t} = {ω | ENNReal.ofReal t⁻¹ ≤ ENNReal.ofReal (E ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (hE.nonneg ω), one_div, inv_le_comm₀ (hpos ω) ht]
  rw [hset]
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (E ω)) μ :=
    (ENNReal.measurable_ofReal.comp hE.measurable).aemeasurable
  have hε0 : ENNReal.ofReal t⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr ht)).ne'
  have hεtop : ENNReal.ofReal t⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  calc μ {ω | ENNReal.ofReal t⁻¹ ≤ ENNReal.ofReal (E ω)}
      ≤ (∫⁻ ω, ENNReal.ofReal (E ω) ∂μ) / ENNReal.ofReal t⁻¹ :=
        meas_ge_le_lintegral_div hmeas hε0 hεtop
    _ ≤ 1 / ENNReal.ofReal t⁻¹ := ENNReal.div_le_div_right hE.expectation_le_one _
    _ = ENNReal.ofReal t := by rw [one_div, ENNReal.ofReal_inv_of_pos ht, inv_inv]

/-- **E-to-p conversion** (Candès, Lecture 15, Prop. 3, STAT 300C). If `E` is an e-variable for the
simple null `μ`, then `1/E` is a p-variable. Proof by Markov: `μ{E ≥ 1/α} ≤ α·Eμ[E] ≤ α`. -/
theorem isPVariable_inv_of_isEVariable {E : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    -- USER-INPUT: E is an e-variable for the null μ; Candès L15 Def. 3
    (hE : IsEVariable E μ)
    -- LEAN-ONLY: E is (pointwise) positive, so `1/E` is the genuine `(0,∞]`-valued reciprocal
    -- p-value. Lean's `1/0 = 0` convention would otherwise map the no-evidence event `E = 0`
    -- (p-value 1) to `1/E = 0`, spuriously inflating `μ{1/E ≤ α}`. E-variables arising as
    -- likelihood ratios are positive, so this is no loss of generality.
    (hpos : ∀ ω, 0 < E ω) :
    IsPVariable (fun ω => 1 / E ω) μ := by
  intro α hα _
  exact superUniform_inv_of_isEVariable hE hpos α hα.le

end StatLean.MultipleTesting
