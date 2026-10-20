module
public import StatLean.ConcentrationInequalities.Orlicz.Attainment

@[expose] public section

/-!
# Sub-exponential tail bound from the ψ₁ norm

The ψ₁ tail bound: if $\mathbb{E}\exp(|X|/K) \le 2$ (in particular if
$\|X\|_{\psi_1} \le K$), then for every $t \ge 0$
$$ \mathbb{P}\bigl(|X| \ge t\bigr) \le 2\exp(-t/K). $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.8.1 ((iii)⇒(i)) and §2.8.2.

**Proof formalization notes.** Constant `c = 1` in the exponent (frozen
numeral `1`, invisible in the statement). **Documented deviation:** direct
Markov on `exp(|X|/K)` (event identity `{t ≤ |X|} = {e^{t/K} ≤ e^{|X|/K}}`,
then `mul_meas_ge_le_lintegral₀`) gives `c = 1`, sharper than the book's
route through property (iv), which yields `K₁ = 3K₃`. Raw core for arbitrary
measures; the norm-facing wrapper derives the threshold-2 condition via the
attainment lemma and hence assumes `[IsProbabilityMeasure μ]`. Tail events
use the ≤-form `μ {ω | t ≤ |X ω|}` with `ENNReal.ofReal` right-hand side (the
`SubGaussian/TailBounds.lean` carrier convention). Named-sorry fallback of
this work item: `measure_abs_ge_le_of_lintegral_exp_abs_le_two` (only if the
Markov event-equality resists; expected to close fully).

**Bibliographic comments.** Exponential tails from exponential moments is
Markov's inequality in its oldest clothing (Bernstein 1924, Chernoff 1952).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Raw core (HDP Prop 2.8.1 (iii)⇒(i); direct Markov, `c = 1` — sharper
than the book's `K₁ = 3K₃`, see module docstring): the threshold-2 condition
gives the two-sided exponential tail. -/
theorem measure_abs_ge_le_of_lintegral_exp_abs_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-inequality regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Prop 2.8.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Prop 2.8.1(i)
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / (K : ℝ))) := by
  have hKR : (0 : ℝ) < (K : ℝ) := hK
  set ε : ℝ≥0∞ := ENNReal.ofReal (Real.exp (t / (K : ℝ))) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hεtop : ε ≠ ⊤ := by rw [hεdef]; exact ENNReal.ofReal_ne_top
  have hf_meas : AEMeasurable
      (fun ω => ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ)))) μ := by
    have hmeas : Measurable fun x : ℝ => Real.exp (|x| / (K : ℝ)) := by fun_prop
    exact (hmeas.comp_aemeasurable hX).ennreal_ofReal
  have hsub : {ω | t ≤ |X ω|}
      ⊆ {ω | ε ≤ ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ)))} := by
    intro ω hω
    have hle : t ≤ |X ω| := hω
    have h2 : t / (K : ℝ) ≤ |X ω| / (K : ℝ) := by gcongr
    rw [hεdef]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h2)
  have hmark := mul_meas_ge_le_lintegral₀ hf_meas ε
  have hchain : ε * μ {ω | t ≤ |X ω|} ≤ 2 := by
    calc ε * μ {ω | t ≤ |X ω|}
        ≤ ε * μ {ω | ε ≤ ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ)))} :=
          mul_le_mul_right (measure_mono hsub) ε
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ := hmark
      _ ≤ 2 := h
  have hr : (2 : ℝ) * Real.exp (-t / (K : ℝ)) = 2 / Real.exp (t / (K : ℝ)) := by
    rw [neg_div, Real.exp_neg]; ring
  have hRHS : ENNReal.ofReal (2 * Real.exp (-t / (K : ℝ))) = 2 / ε := by
    rw [hr, ENNReal.ofReal_div_of_pos (Real.exp_pos _), ENNReal.ofReal_ofNat, ← hεdef]
  rw [hRHS, ENNReal.le_div_iff_mul_le (Or.inl hεpos.ne') (Or.inl hεtop), mul_comm]
  exact hchain

/-- ψ₁-tail bridge (HDP §2.8.2, constant `c = 1`): a sub-exponential norm
bound gives the two-sided exponential tail. -/
theorem measure_abs_ge_le_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-inequality regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP §2.8.2
    (hK : 0 < K)
    -- USER-INPUT: sub-exponential norm bound ‖X‖_{ψ₁} ≤ K; HDP §2.8.2
    (h : subExponentialNorm X μ ≤ K)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Prop 2.8.1(i)
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / (K : ℝ))) := by
  have hcond := lintegral_exp_abs_le_two_of_subExponentialNorm_le hX hK h
  exact measure_abs_ge_le_of_lintegral_exp_abs_le_two hX hK hcond ht

end StatLean.ConcentrationInequalities
