module
public import StatLean.ConcentrationInequalities.SubExponential.Defs
public import StatLean.ConcentrationInequalities.Orlicz.Attainment
public import StatLean.ConcentrationInequalities.ForMathlib.ExpTaylorBounds

@[expose] public section

/-!
# Restricted-range MGF bound from the ψ₁ norm

The ψ₁ analogue of B2 (HDP Prop 2.8.1 (iii)⇒(iv)): if $\mathbb{E}X = 0$ and
$\|X\|_{\psi_1} \le K$, then
$$ \mathbb{E}\,e^{\lambda X} \le \exp\bigl(4\lambda^2 K^2\bigr)
   \qquad \text{for } |\lambda| \le \tfrac{1}{2K}, $$
with the bridge into the existing project carrier `IsSubExponential` at
parameter $\alpha = 2\sqrt{2}\,K$ — the engine Bernstein 2.9.1 consumes.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.8.1 ((iii)⇒(iv)).

**Proof formalization notes.** Constants: `K₄ = 2K` book-exact (MGF bound
`exp(4λ²K²)` on `|λ| ≤ 1/(2K)`; frozen numerals `4` and `2`); carrier bridge
`α = 2√2·K` exact (frozen `2 * NNReal.sqrt 2 * K`; formula: `4λ²K² = λ²α²/2`
forces `α² = 8K²`, and `1/α = 1/(2√2·K) ≤ 1/(2K)` keeps the range inside the
proven one). The proof splits `E e^{λX} ≤ 1 + λ·EX + (λ²/2)·E X²e^{|λX|}`
(`exp_le_one_add_add_sq_half_mul_exp_abs`), kills the middle term with
`hmean`, and bounds `X²e^{|λX|}` using `sq_le_exp` on the restricted range.
This ψ₁-norm sub-exponential coexists with the Lu-BDA α-form carrier in
`SubExponential/Defs.lean`: our bridge lands exactly in that structure,
discharging both of its fields (`mgf_le` and `integrable_exp_mul`).
Integrability is derived, not laundered (`e^{lx} ≤ e^{|x|/K}` on the range;
`|x|/K ≤ e^{|x|/K}`). Named-sorry fallback of this work item:
`mgf_le_of_lintegral_exp_abs_le_two`, with the norm wrapper and the
`IsSubExponential` bridge derived from it.

**Bibliographic comments.** Restricted-range MGF control of sub-exponential
variables goes back to S. N. Bernstein's 1924 inequality; the modern
two-parameter formulation is in Wainwright (*High-Dimensional Statistics*,
2019, §2.1.3).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The dominating function `e^{|X|/K}` is integrable: its `∫⁻ ‖·‖` equals the
book-form ψ₁ integral, which is `≤ 2 < ∞`. -/
private theorem integrable_exp_abs_div_of_lintegral_le_two {X : Ω → ℝ} {μ : Measure Ω}
    (hX : AEMeasurable X μ) {K : ℝ≥0}
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2) :
    Integrable (fun ω => Real.exp (|X ω| / (K : ℝ))) μ := by
  refine ⟨((continuous_abs.measurable.comp_aemeasurable hX).div_const
    (K : ℝ)).exp.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hpt : ∀ ω, ‖Real.exp (|X ω| / (K : ℝ))‖ₑ
      = ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) :=
    fun ω => Real.enorm_eq_ofReal (Real.exp_pos _).le
  simp_rw [hpt]
  exact lt_of_le_of_lt h (by norm_num)

/-- Integrability of `exp(l·X)` on the restricted range from the ψ₁ condition
(domination `e^{lx} ≤ e^{|x|/K}` for `|l| ≤ 1/K`); discharges the
`IsSubExponential.integrable_exp_mul` field — no hypothesis laundering. -/
theorem integrable_exp_mul_of_lintegral_exp_abs_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; integrability regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Prop 2.8.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2)
    {l : ℝ}
    -- USER-INPUT: restricted range |l| ≤ 1/K; HDP Prop 2.8.1(iv) range convention
    (hl : |l| ≤ 1 / (K : ℝ)) :
    Integrable (fun ω => Real.exp (l * X ω)) μ := by
  have hg := integrable_exp_abs_div_of_lintegral_le_two hX h
  have hbound : ∀ ω, ‖Real.exp (l * X ω)‖ ≤ Real.exp (|X ω| / (K : ℝ)) := by
    intro ω
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    calc l * X ω ≤ |l * X ω| := le_abs_self _
      _ = |l| * |X ω| := abs_mul _ _
      _ ≤ (1 / (K : ℝ)) * |X ω| := by
          exact mul_le_mul_of_nonneg_right hl (abs_nonneg _)
      _ = |X ω| / (K : ℝ) := by ring
  exact Integrable.mono' hg (hX.const_mul l).exp.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- First-moment integrability from the ψ₁ condition (`|x|/K ≤ e^{|x|/K}`
pointwise); makes `hmean` a claim about a genuine Bochner integral. -/
theorem integrable_of_lintegral_exp_abs_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; integrability regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Prop 2.8.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2) :
    Integrable X μ := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hg := integrable_exp_abs_div_of_lintegral_le_two hX h
  have hbound : ∀ ω, ‖X ω‖ ≤ (K : ℝ) * Real.exp (|X ω| / (K : ℝ)) := by
    intro ω
    rw [Real.norm_eq_abs]
    have h1 : |X ω| / (K : ℝ) ≤ Real.exp (|X ω| / (K : ℝ)) := by
      have := Real.add_one_le_exp (|X ω| / (K : ℝ)); linarith
    calc |X ω| = (K : ℝ) * (|X ω| / (K : ℝ)) := by field_simp
      _ ≤ (K : ℝ) * Real.exp (|X ω| / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hKR)
  exact Integrable.mono' (hg.const_mul (K : ℝ)) hX.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Raw core (HDP Prop 2.8.1 (iii)⇒(iv), `K₄ = 2K₃` book-exact): mean zero +
threshold-2 condition give the restricted-range MGF bound
`E e^{λX} ≤ exp(4λ²K²)` for `|λ| ≤ 1/(2K)`. -/
theorem mgf_le_of_lintegral_exp_abs_le_two
    -- LEAN-ONLY: probability measure; HDP §2.8 standing assumption
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Prop 2.8.1(iii)
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2)
    -- USER-INPUT: mean zero; HDP Prop 2.8.1(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0)
    {l : ℝ}
    -- USER-INPUT: restricted range |λ| ≤ 1/(2K); HDP Prop 2.8.1(iv)
    (hl : |l| ≤ 1 / (2 * (K : ℝ))) :
    ProbabilityTheory.mgf X μ l ≤ Real.exp (4 * l ^ 2 * (K : ℝ) ^ 2) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  -- integrability bricks
  have hg_int : Integrable (fun ω => Real.exp (|X ω| / (K : ℝ))) μ :=
    integrable_exp_abs_div_of_lintegral_le_two hX hcond
  have hX_int : Integrable X μ := integrable_of_lintegral_exp_abs_le_two hX hK hcond
  have hlK : |l| ≤ 1 / (K : ℝ) :=
    hl.trans (by apply one_div_le_one_div_of_le hKR; nlinarith [hKR])
  have hexp_int : Integrable (fun ω => Real.exp (l * X ω)) μ :=
    integrable_exp_mul_of_lintegral_exp_abs_le_two hX hK hcond hlK
  -- pointwise Taylor bound `e^{lX} ≤ 1 + lX + 2l²K² e^{|X|/K}`
  have hpt : ∀ ω, Real.exp (l * X ω)
      ≤ 1 + l * X ω + 2 * l ^ 2 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (K : ℝ)) := by
    intro ω
    have taylor := exp_le_one_add_add_sq_half_mul_exp_abs (l * X ω)
    -- `|lX| ≤ |X|/(2K)`
    have habs : |l * X ω| ≤ |X ω| / (2 * (K : ℝ)) := by
      rw [abs_mul]
      calc |l| * |X ω| ≤ (1 / (2 * (K : ℝ))) * |X ω| :=
            mul_le_mul_of_nonneg_right hl (abs_nonneg _)
        _ = |X ω| / (2 * (K : ℝ)) := by ring
    have hexp_mono : Real.exp |l * X ω| ≤ Real.exp (|X ω| / (2 * (K : ℝ))) :=
      Real.exp_le_exp.mpr habs
    -- `X² ≤ 4K² e^{|X|/(2K)}` via `y² ≤ e^y`
    have e1 : (|X ω| / (2 * (K : ℝ))) ^ 2 = (X ω) ^ 2 / (4 * (K : ℝ) ^ 2) := by
      rw [div_pow, sq_abs, mul_pow]; norm_num
    have hsq : (X ω) ^ 2 ≤ 4 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (2 * (K : ℝ))) := by
      have h0 := sq_le_exp (show (0 : ℝ) ≤ |X ω| / (2 * (K : ℝ)) by positivity)
      rw [e1] at h0
      have h4 : (0 : ℝ) < 4 * (K : ℝ) ^ 2 := by positivity
      calc (X ω) ^ 2 = 4 * (K : ℝ) ^ 2 * ((X ω) ^ 2 / (4 * (K : ℝ) ^ 2)) := by
            field_simp
        _ ≤ 4 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (2 * (K : ℝ))) :=
            mul_le_mul_of_nonneg_left h0 (le_of_lt h4)
    -- combine into the quadratic term bound
    set A := Real.exp (|X ω| / (2 * (K : ℝ))) with hA
    have hAA : A * A = Real.exp (|X ω| / (K : ℝ)) := by
      rw [hA, ← Real.exp_add]; congr 1; field_simp; ring
    have hprod : (X ω) ^ 2 * Real.exp |l * X ω| ≤ (4 * (K : ℝ) ^ 2 * A) * A :=
      mul_le_mul hsq hexp_mono (Real.exp_pos _).le (by positivity)
    have hquad : (l * X ω) ^ 2 / 2 * Real.exp |l * X ω|
        ≤ 2 * l ^ 2 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (K : ℝ)) := by
      calc (l * X ω) ^ 2 / 2 * Real.exp |l * X ω|
          = l ^ 2 / 2 * ((X ω) ^ 2 * Real.exp |l * X ω|) := by ring
        _ ≤ l ^ 2 / 2 * ((4 * (K : ℝ) ^ 2 * A) * A) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 2 * l ^ 2 * (K : ℝ) ^ 2 * (A * A) := by ring
        _ = 2 * l ^ 2 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (K : ℝ)) := by rw [hAA]
    linarith [taylor, hquad]
  -- integrate the pointwise bound
  have hRHS_int : Integrable
      (fun ω => 1 + l * X ω + 2 * l ^ 2 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (K : ℝ))) μ :=
    ((integrable_const (1 : ℝ)).add (hX_int.const_mul l)).add
      (hg_int.const_mul (2 * l ^ 2 * (K : ℝ) ^ 2))
  have hmono : (∫ ω, Real.exp (l * X ω) ∂μ)
      ≤ ∫ ω, (1 + l * X ω + 2 * l ^ 2 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (K : ℝ))) ∂μ :=
    integral_mono hexp_int hRHS_int hpt
  -- evaluate the RHS integral
  have hg_le : (∫ ω, Real.exp (|X ω| / (K : ℝ)) ∂μ) ≤ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))
        hg_int.aestronglyMeasurable]
    have hmono2 := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hcond
    simpa using hmono2
  have hRHS_eq : (∫ ω, (1 + l * X ω
        + 2 * l ^ 2 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (K : ℝ))) ∂μ)
      = 1 + 2 * l ^ 2 * (K : ℝ) ^ 2 * (∫ ω, Real.exp (|X ω| / (K : ℝ)) ∂μ) := by
    have h1 : Integrable (fun ω => 1 + l * X ω) μ :=
      (integrable_const (1 : ℝ)).add (hX_int.const_mul l)
    have h2 : Integrable
        (fun ω => 2 * l ^ 2 * (K : ℝ) ^ 2 * Real.exp (|X ω| / (K : ℝ))) μ :=
      hg_int.const_mul _
    rw [integral_add h1 h2, integral_add (integrable_const (1 : ℝ)) (hX_int.const_mul l),
      integral_const_mul, integral_const_mul, hmean, mul_zero]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def, measure_univ,
      ENNReal.toReal_one, add_zero]
  -- assemble
  change (∫ ω, Real.exp (l * X ω) ∂μ) ≤ Real.exp (4 * l ^ 2 * (K : ℝ) ^ 2)
  have hc : (0 : ℝ) ≤ 2 * l ^ 2 * (K : ℝ) ^ 2 := by positivity
  have hchain : (∫ ω, Real.exp (l * X ω) ∂μ) ≤ 1 + 4 * l ^ 2 * (K : ℝ) ^ 2 := by
    rw [hRHS_eq] at hmono
    nlinarith [hmono, hg_le, hc]
  refine hchain.trans ?_
  have := Real.add_one_le_exp (4 * l ^ 2 * (K : ℝ) ^ 2)
  linarith

/-- ψ₁-analogue of B2 (HDP Prop 2.8.1(iv)): a sub-exponential norm bound
gives the restricted-range MGF bound. -/
theorem mgf_le_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1
    (hK : 0 < K)
    -- USER-INPUT: sub-exponential norm bound ‖X‖_{ψ₁} ≤ K; HDP Definition 2.8.4
    (h : subExponentialNorm X μ ≤ K)
    -- USER-INPUT: mean zero; HDP Prop 2.8.1(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0)
    {l : ℝ}
    -- USER-INPUT: restricted range |λ| ≤ 1/(2K); HDP Prop 2.8.1(iv)
    (hl : |l| ≤ 1 / (2 * (K : ℝ))) :
    ProbabilityTheory.mgf X μ l ≤ Real.exp (4 * l ^ 2 * (K : ℝ) ^ 2) := by
  have hcond := lintegral_exp_abs_le_two_of_subExponentialNorm_le hX hK h
  exact mgf_le_of_lintegral_exp_abs_le_two hX hK hcond hmean hl

/-- Bridge into the project carrier (`α = 2√2·K` exact: `4λ²K² = λ²α²/2` and
`[−1/α, 1/α] ⊆ [−1/(2K), 1/(2K)]`); discharges both `IsSubExponential`
fields. -/
theorem isSubExponential_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1
    (hK : 0 < K)
    -- USER-INPUT: sub-exponential norm bound ‖X‖_{ψ₁} ≤ K; HDP Definition 2.8.4
    (h : subExponentialNorm X μ ≤ K)
    -- USER-INPUT: mean zero; HDP Prop 2.8.1(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0) :
    IsSubExponential X (2 * NNReal.sqrt 2 * K) μ := by
  set α : ℝ≥0 := 2 * NNReal.sqrt 2 * K with hαdef
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hαc : (α : ℝ) = 2 * Real.sqrt 2 * (K : ℝ) := by
    rw [hαdef]; push_cast; ring
  have hα2 : (α : ℝ) ^ 2 = 8 * (K : ℝ) ^ 2 := by
    rw [hαc, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have hαpos : (0 : ℝ) < (α : ℝ) := by rw [hαc]; positivity
  -- `2K ≤ α`, hence the range `|l| ≤ 1/α` sits inside `|l| ≤ 1/(2K)`
  have hge : 2 * (K : ℝ) ≤ (α : ℝ) := by
    rw [hαc]
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [hKR, h1]
  have hrange : ∀ l : ℝ, |l| ≤ 1 / (α : ℝ) → |l| ≤ 1 / (2 * (K : ℝ)) :=
    fun l hl => hl.trans (one_div_le_one_div_of_le (by positivity) hge)
  have hcent : (fun ω => X ω - ∫ x, X x ∂μ) = X := by
    funext ω; rw [hmean, sub_zero]
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [hcent]
    have hbnd := mgf_le_of_subExponentialNorm_le hX hK h hmean (hrange l hl)
    refine hbnd.trans (le_of_eq (congrArg Real.exp ?_))
    rw [hα2]; ring
  · intro l hl
    have hcond := lintegral_exp_abs_le_two_of_subExponentialNorm_le hX hK h
    have hlK : |l| ≤ 1 / (K : ℝ) :=
      (hrange l hl).trans (one_div_le_one_div_of_le hKR (by nlinarith [hKR]))
    have hfun : (fun ω => Real.exp (l * (X ω - ∫ x, X x ∂μ)))
        = (fun ω => Real.exp (l * X ω)) := by funext ω; rw [hmean, sub_zero]
    rw [hfun]
    exact integrable_exp_mul_of_lintegral_exp_abs_le_two hX hK hcond hlK

end StatLean.ConcentrationInequalities
