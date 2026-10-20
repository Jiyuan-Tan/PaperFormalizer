module
public import StatLean.ConcentrationInequalities.Orlicz.Attainment

@[expose] public section

/-!
# Sub-Gaussian tail bound from the ψ₂ norm (B1)

The sub-Gaussian tail bound from the ψ₂ condition / norm: if
$\mathbb{E}\exp(X^2/K^2) \le 2$ (in particular if $\|X\|_{\psi_2} \le K$),
then for every $t \ge 0$
$$ \mathbb{P}\bigl(|X| \ge t\bigr) \le 2\exp\bigl(-t^2/K^2\bigr). $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((iii)⇒(i)) and Proposition
2.6.6(i).

**Proof formalization notes.** Constant `c = 1` in the exponent (formula:
book's unnamed `c` realized as `K₁ = K₃` exactly; frozen numeral: `1`,
invisible in the statement). Proof is Markov (`mul_meas_ge_le_lintegral₀`) on
`exp(X²/K²)` after the event identity
`{t ≤ |X|} = {exp(t²/K²) ≤ exp((X/K)²)}`. Tail events use the ≤-form
`μ {ω | t ≤ |X ω|}` with `ENNReal.ofReal` right-hand side, the carrier
convention of `SubGaussian/TailBounds.lean`; strict-< consumers weaken via
`measure_mono`. The raw core takes the book-literal threshold-2 condition and
holds for any measure; the norm-facing wrapper (the frozen B1 bridge) derives
it via the attainment lemma and hence assumes `[IsProbabilityMeasure μ]`.
Named-sorry fallback of this work item: none here — both B1 declarations must
close (the fallback lives in `Orlicz/Equivalence.lean`).

**Bibliographic comments.** Gaussian-type tails from square-exponential
moments are classical (cf. Kahane 1960; Buldygin–Kozachenko 1980); the
five-way equivalence packaging is Vershynin's Proposition 2.6.1.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Raw core (HDP Prop 2.6.1 (iii)⇒(i), `K₁ = K₃` book-exact): the
threshold-2 condition gives the two-sided Gaussian tail with constant 1. -/
theorem measure_abs_ge_le_of_lintegral_exp_sq_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-inequality regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Prop 2.6.1(i)
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K : ℝ) ^ 2)) := by
  have hKR : (0 : ℝ) < (K : ℝ) := hK
  set ε : ℝ≥0∞ := ENNReal.ofReal (Real.exp (t ^ 2 / (K : ℝ) ^ 2)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hεtop : ε ≠ ⊤ := by rw [hεdef]; exact ENNReal.ofReal_ne_top
  have hf_meas : AEMeasurable
      (fun ω => ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2))) μ := by
    have hmeas : Measurable fun x : ℝ => Real.exp ((x / (K : ℝ)) ^ 2) := by fun_prop
    exact (hmeas.comp_aemeasurable hX).ennreal_ofReal
  have hsub : {ω | t ≤ |X ω|}
      ⊆ {ω | ε ≤ ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2))} := by
    intro ω hω
    have hle : t ≤ |X ω| := hω
    have ht2 : t ^ 2 ≤ (X ω) ^ 2 := by
      nlinarith [sq_abs (X ω), abs_nonneg (X ω), hle, ht]
    have h2 : t ^ 2 / (K : ℝ) ^ 2 ≤ (X ω / (K : ℝ)) ^ 2 := by rw [div_pow]; gcongr
    rw [hεdef]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h2)
  have hmark := mul_meas_ge_le_lintegral₀ hf_meas ε
  have hchain : ε * μ {ω | t ≤ |X ω|} ≤ 2 := by
    calc ε * μ {ω | t ≤ |X ω|}
        ≤ ε * μ {ω | ε ≤ ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2))} :=
          mul_le_mul_right (measure_mono hsub) ε
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ := hmark
      _ ≤ 2 := h
  have hr : (2 : ℝ) * Real.exp (-t ^ 2 / (K : ℝ) ^ 2)
      = 2 / Real.exp (t ^ 2 / (K : ℝ) ^ 2) := by
    rw [neg_div, Real.exp_neg]; ring
  have hRHS : ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K : ℝ) ^ 2)) = 2 / ε := by
    rw [hr, ENNReal.ofReal_div_of_pos (Real.exp_pos _), ENNReal.ofReal_ofNat, ← hεdef]
  rw [hRHS, ENNReal.le_div_iff_mul_le (Or.inl hεpos.ne') (Or.inl hεtop), mul_comm]
  exact hchain

/-- **B1** (HDP Proposition 2.6.6(i), constant `c = 1`): a sub-Gaussian norm
bound gives the two-sided Gaussian tail. -/
theorem measure_abs_ge_le_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-inequality regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.6
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Prop 2.6.6
    (h : subGaussianNorm X μ ≤ K)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Prop 2.6.6(i)
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K : ℝ) ^ 2)) := by
  have hcond := lintegral_exp_sq_le_two_of_subGaussianNorm_le hX hK h
  exact measure_abs_ge_le_of_lintegral_exp_sq_le_two hX hK hcond ht

/-- Convenience corollary of B1 at `K = (subGaussianNorm X μ).toNNReal`
(HDP Proposition 2.6.6(i) with the norm itself in the exponent). -/
theorem measure_abs_ge_le_subGaussianNorm
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-inequality regularity
    (hX : AEMeasurable X μ)
    -- USER-INPUT: nondegenerate norm; excludes X = 0 a.e. (toReal of 0 junk)
    (h0 : subGaussianNorm X μ ≠ 0)
    -- USER-INPUT: X sub-Gaussian (finite ψ₂ norm); HDP Prop 2.6.6 standing hypothesis
    (htop : subGaussianNorm X μ ≠ ⊤)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Prop 2.6.6(i)
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|}
      ≤ ENNReal.ofReal
          (2 * Real.exp (-t ^ 2 / (subGaussianNorm X μ).toReal ^ 2)) := by
  set K := (subGaussianNorm X μ).toNNReal with hKdef
  have hKpos : 0 < K := by rw [hKdef]; exact ENNReal.toNNReal_pos h0 htop
  have hle : subGaussianNorm X μ ≤ (K : ℝ≥0∞) := by
    rw [hKdef, ENNReal.coe_toNNReal htop]
  have hmain := measure_abs_ge_le_of_subGaussianNorm_le hX hKpos hle ht
  have hKR : (K : ℝ) = (subGaussianNorm X μ).toReal := by rw [hKdef]; rfl
  rwa [hKR] at hmain

end StatLean.ConcentrationInequalities
