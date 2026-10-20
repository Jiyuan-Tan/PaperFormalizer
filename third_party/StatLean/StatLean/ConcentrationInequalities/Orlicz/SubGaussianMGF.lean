module
public import StatLean.ConcentrationInequalities.SubGaussian.Defs
public import StatLean.ConcentrationInequalities.Orlicz.Attainment
public import StatLean.ConcentrationInequalities.ForMathlib.ExpTaylorBounds

@[expose] public section

/-!
# Sub-Gaussian MGF bound from the ψ₂ norm (B2)

Mean-zero + ψ₂ condition/norm ⇒ MGF bound: if $\mathbb{E}X = 0$ and
$\|X\|_{\psi_2} \le K$ then
$$ \mathbb{E}\,e^{\lambda X} \le \exp\Bigl(\tfrac{3}{2}\,K^2\lambda^2\Bigr)
   \qquad \text{for all } \lambda \in \mathbb{R}, $$
i.e. `ProbabilityTheory.HasSubgaussianMGF X (3·K²) μ`, plus the
`IsSubGaussian` project-carrier corollary.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((iii)⇒(iv)) and Proposition
2.6.6(iv).

**Proof formalization notes.** Variance-proxy constant `C = 3` (**frozen**:
`3 * K ^ 2`; formula: book's `K₄ = √(3/2)·K₃` exactly, since Mathlib's proxy
convention `E e^{λX} ≤ e^{cλ²/2}` gives `c = 2K₄² = 3K₃²`). The proof splits
`E e^{λX} ≤ 1 + λ·EX + (λ²/2)·E X²e^{|λX|}` via the ForMathlib brick
`exp_le_one_add_add_sq_half_mul_exp_abs`, kills the middle term with `hmean`,
and bounds the remainder by the ψ₂ condition. No hypothesis laundering:
`Integrable X μ` (so `hmean` is about a genuine integral) and the
`HasSubgaussianMGF` integrability field are *derived* from the ψ₂ condition
(`|x|/K ≤ e^{(x/K)²}` resp. `e^{lx} ≤ e^{l²K²/2}·e^{(x/K)²}` pointwise) in the
two named integrability lemmas. Book Remark 2.6.2 / Exercise 2.23 ("(iv)
forces mean zero") is not formalized — scope note. Named-sorry fallback of
this work item: `integrable_exp_mul_of_lintegral_exp_sq_le_two` (domination
bookkeeping), with the MGF bound closed modulo it.

**Bibliographic comments.** The MGF characterization of sub-Gaussian
variables is due to J.-P. Kahane (1960) and Buldygin–Kozachenko (1980).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Elementary pointwise bricks (private) -/

/-- Weighted AM–GM `t·(kk·y) ≤ t²kk²/2 + y²/2`. -/
private lemma amgm (kk t y : ℝ) : t * (kk * y) ≤ t ^ 2 * kk ^ 2 / 2 + y ^ 2 / 2 := by
  nlinarith [sq_nonneg (t * kk - y)]

/-- AM–GM exponential domination `e^{tx} ≤ e^{t²kk²/2}·e^{(x/kk)²/2}`. -/
private lemma exp_mul_le_half {kk : ℝ} (hkk : 0 < kk) (t x : ℝ) :
    Real.exp (t * x) ≤ Real.exp (t ^ 2 * kk ^ 2 / 2) * Real.exp ((x / kk) ^ 2 / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hkk' : kk ≠ 0 := ne_of_gt hkk
  have hxy : kk * (x / kk) = x := by field_simp
  have h := amgm kk t (x / kk)
  rw [hxy] at h
  linarith [h]

/-- `e^{v/2} ≤ (e^v + 1)/2` (AM–GM on `√(e^v · 1)`). -/
private lemma exp_half_le (v : ℝ) : Real.exp (v / 2) ≤ (Real.exp v + 1) / 2 := by
  have hw : Real.exp v = Real.exp (v / 2) * Real.exp (v / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith [sq_nonneg (Real.exp (v / 2) - 1), Real.exp_pos (v / 2), hw]

/-- Weighted-power concavity `p^θ ≤ θ·p + (1-θ)` for `0 ≤ θ ≤ 1`, `p ≥ 0`. -/
private lemma geom_pointwise {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (p : ℝ) (hp : 0 ≤ p) :
    p ^ θ ≤ θ * p + (1 - θ) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := θ) (w₂ := 1 - θ) (p₁ := p) (p₂ := 1)
    hθ0 (by linarith) hp zero_le_one (by ring)
  simpa [Real.one_rpow] using h

/-- Interpolation bound `e^{(tx)²} ≤ t²kk²·e^{(x/kk)²} + (1 - t²kk²)` for `t²kk² ≤ 1`. -/
private lemma exp_tsq_le {kk : ℝ} (hkk : 0 < kk) (t x : ℝ) (hθ1 : t ^ 2 * kk ^ 2 ≤ 1) :
    Real.exp ((t * x) ^ 2)
      ≤ t ^ 2 * kk ^ 2 * Real.exp ((x / kk) ^ 2) + (1 - t ^ 2 * kk ^ 2) := by
  have hθ0 : 0 ≤ t ^ 2 * kk ^ 2 := by positivity
  have hp : (0 : ℝ) ≤ Real.exp ((x / kk) ^ 2) := (Real.exp_pos _).le
  have hg := geom_pointwise hθ0 hθ1 (Real.exp ((x / kk) ^ 2)) hp
  have hpow : Real.exp ((x / kk) ^ 2) ^ (t ^ 2 * kk ^ 2) = Real.exp ((t * x) ^ 2) := by
    rw [← Real.exp_mul]; congr 1
    have hkk' : kk ≠ 0 := ne_of_gt hkk
    field_simp
  rwa [hpow] at hg

/-- Vershynin's key pointwise bound `e^u ≤ u + e^{u²}`, all `u ∈ ℝ`. -/
private lemma exp_le_add_exp_sq (u : ℝ) : Real.exp u ≤ u + Real.exp (u ^ 2) := by
  rcases le_or_gt 1 u with hu | hu
  · have h1 : u ≤ u ^ 2 := by nlinarith
    linarith [Real.exp_le_exp.2 h1]
  · rcases le_or_gt u 0 with hu0 | hu0
    · have hbrick := exp_le_one_add_add_sq_half_of_nonpos hu0
      have hexp : 1 + u ^ 2 ≤ Real.exp (u ^ 2) := by linarith [Real.add_one_le_exp (u ^ 2)]
      nlinarith [hbrick, hexp, sq_nonneg u]
    · have hb : Real.exp u ≤ 1 + u + u ^ 2 := by
        calc Real.exp u ≤ _ := Real.exp_bound' hu0.le hu.le zero_lt_three
          _ ≤ 1 + u + u ^ 2 := by
            rw [show 3 = 1 + 1 + 1 from rfl]
            repeat rw [Finset.sum_range_succ]
            norm_num [Nat.factorial]
            nlinarith
      have hexp : 1 + u ^ 2 ≤ Real.exp (u ^ 2) := by linarith [Real.add_one_le_exp (u ^ 2)]
      linarith [hb, hexp]

/-! ### ψ₂-condition integrability/bound bricks (private) -/

/-- `AEStronglyMeasurable` of `ω ↦ e^{(X ω/kk)²}`. -/
private lemma aesm_expSq {X : Ω → ℝ} (hX : AEMeasurable X μ) {kk : ℝ} :
    AEStronglyMeasurable (fun ω => Real.exp ((X ω / kk) ^ 2)) μ :=
  (Real.measurable_exp.comp_aemeasurable ((hX.div_const _).pow_const 2)).aestronglyMeasurable

/-- `Integrable (e^{(X/K)²})` from the ψ₂ condition. -/
private lemma expSq_integrable {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ≥0}
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2) :
    Integrable (fun ω => Real.exp ((X ω / (K : ℝ)) ^ 2)) μ := by
  refine ⟨aesm_expSq hX, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => (Real.exp_pos _).le)]
  exact lt_of_le_of_lt hcond (by simp)

/-- `∫ e^{(X/K)²} ≤ 2` from the ψ₂ condition. -/
private lemma expSq_integral_le {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ≥0}
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2) :
    ∫ ω, Real.exp ((X ω / (K : ℝ)) ^ 2) ∂μ ≤ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (Real.exp_pos _).le) (aesm_expSq hX)]
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ).toReal
      ≤ (2 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hcond
    _ = 2 := by simp

/-- `Integrable (e^{(X/K)²/2})` from the ψ₂ condition (dominated by `e^{(X/K)²}`). -/
private lemma expHalfSq_integrable {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ≥0}
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2) :
    Integrable (fun ω => Real.exp ((X ω / (K : ℝ)) ^ 2 / 2)) μ := by
  refine (expSq_integrable hX hcond).mono'
    (Real.measurable_exp.comp_aemeasurable
      (((hX.div_const _).pow_const 2).div_const 2)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.2 (by linarith [sq_nonneg (X ω / (K : ℝ))])

/-- `∫ e^{(X/K)²/2} ≤ 3/2` from the ψ₂ condition. -/
private lemma expHalfSq_integral_le [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2) :
    ∫ ω, Real.exp ((X ω / (K : ℝ)) ^ 2 / 2) ∂μ ≤ 3 / 2 := by
  calc ∫ ω, Real.exp ((X ω / (K : ℝ)) ^ 2 / 2) ∂μ
      ≤ ∫ ω, (Real.exp ((X ω / (K : ℝ)) ^ 2) + 1) / 2 ∂μ := by
        refine integral_mono (expHalfSq_integrable hX hcond)
          (((expSq_integrable hX hcond).add (integrable_const 1)).div_const 2) ?_
        exact fun ω => exp_half_le _
    _ = (∫ ω, Real.exp ((X ω / (K : ℝ)) ^ 2) ∂μ + 1) / 2 := by
        rw [integral_div, integral_add (expSq_integrable hX hcond) (integrable_const 1),
          integral_const]
        simp
    _ ≤ (2 + 1) / 2 := by linarith [expSq_integral_le hX hcond]
    _ = 3 / 2 := by norm_num

/-- `Integrable (e^{(tX)²})` for `t²K² ≤ 1` from the ψ₂ condition. -/
private lemma exp_tsq_integrable [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEMeasurable X μ)
    {K : ℝ≥0} (hK : 0 < K)
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    (t : ℝ) (htk : t ^ 2 * (K : ℝ) ^ 2 ≤ 1) :
    Integrable (fun ω => Real.exp ((t * X ω) ^ 2)) μ := by
  refine ((expSq_integrable hX hcond).const_mul (t ^ 2 * (K : ℝ) ^ 2)).add
    (integrable_const (1 - t ^ 2 * (K : ℝ) ^ 2)) |>.mono'
    (Real.measurable_exp.comp_aemeasurable ((hX.const_mul t).pow_const 2)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact exp_tsq_le (by exact_mod_cast hK) t (X ω) htk

/-- Integrability of `exp(l·X)` from the ψ₂ condition (domination
`e^{lx} ≤ e^{l²K²/2}·e^{(x/K)²}`); discharges the `HasSubgaussianMGF`
integrability field — no hypothesis laundering. -/
theorem integrable_exp_mul_of_lintegral_exp_sq_le_two
    -- LEAN-ONLY: probability measure; finite dominating mass in the comparison
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; integrability regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    (l : ℝ) :
    Integrable (fun ω => Real.exp (l * X ω)) μ := by
  have hkk : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  refine ((expHalfSq_integrable hX h).const_mul
    (Real.exp (l ^ 2 * (K : ℝ) ^ 2 / 2))).mono'
    (Real.measurable_exp.comp_aemeasurable (hX.const_mul l)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact exp_mul_le_half hkk l (X ω)

/-- First-moment integrability from the ψ₂ condition
(`|x|/K ≤ e^{(x/K)²}` pointwise); makes `hmean` a claim about a genuine
Bochner integral — no hypothesis laundering. -/
theorem integrable_of_lintegral_exp_sq_le_two
    -- LEAN-ONLY: probability measure; finite dominating mass in the comparison
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; integrability regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2) :
    Integrable X μ := by
  have hkk : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  refine ((expSq_integrable hX h).const_mul (K : ℝ)).mono' hX.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  set y := |X ω| / (K : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y ≤ Real.exp (y ^ 2) := by
    nlinarith [Real.add_one_le_exp (y ^ 2), sq_nonneg (y - 1)]
  have hyx : (K : ℝ) * y = |X ω| := by rw [hy]; field_simp
  have hysq : y ^ 2 = (X ω / (K : ℝ)) ^ 2 := by rw [hy, div_pow, div_pow, sq_abs]
  calc |X ω| = (K : ℝ) * y := hyx.symm
    _ ≤ (K : ℝ) * Real.exp (y ^ 2) := by exact mul_le_mul_of_nonneg_left h1 hkk.le
    _ = (K : ℝ) * Real.exp ((X ω / (K : ℝ)) ^ 2) := by rw [hysq]

/-- Raw core (HDP Prop 2.6.1 (iii)⇒(iv), `K₄ = √(3/2)·K₃` book-exact,
variance proxy `2K₄² = 3K²`): mean zero + threshold-2 condition give the
Mathlib sub-Gaussian MGF predicate. -/
theorem hasSubgaussianMGF_of_lintegral_exp_sq_le_two
    -- LEAN-ONLY: probability measure; HDP §2.6 standing assumption
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF-predicate regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    -- USER-INPUT: mean zero; HDP Prop 2.6.1(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0) :
    ProbabilityTheory.HasSubgaussianMGF X (3 * K ^ 2) μ := by
  set kk := (K : ℝ) with hkkdef
  have hkk : (0 : ℝ) < kk := by rw [hkkdef]; exact_mod_cast hK
  have hcoe : ((3 * K ^ 2 : ℝ≥0) : ℝ) = 3 * kk ^ 2 := by rw [hkkdef]; push_cast; ring
  refine ⟨fun t => integrable_exp_mul_of_lintegral_exp_sq_le_two hX hK hcond t, fun t => ?_⟩
  show mgf X μ t ≤ Real.exp (((3 * K ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2)
  rw [hcoe, mgf]
  have hXint : Integrable (fun ω => Real.exp (t * X ω)) μ :=
    integrable_exp_mul_of_lintegral_exp_sq_le_two hX hK hcond t
  rcases le_or_gt (t ^ 2 * kk ^ 2) 1 with htk | htk
  · -- Small-t regime: `e^u ≤ u + e^{u²}` + interpolation.
    have hstep : ∫ ω, Real.exp (t * X ω) ∂μ
        ≤ ∫ ω, (t * X ω + Real.exp ((t * X ω) ^ 2)) ∂μ := by
      refine integral_mono hXint
        ((((integrable_of_lintegral_exp_sq_le_two hX hK hcond).const_mul t)).add
          (exp_tsq_integrable hX hK hcond t htk)) ?_
      exact fun ω => exp_le_add_exp_sq (t * X ω)
    have hsplit : ∫ ω, (t * X ω + Real.exp ((t * X ω) ^ 2)) ∂μ
        = ∫ ω, Real.exp ((t * X ω) ^ 2) ∂μ := by
      rw [integral_add ((integrable_of_lintegral_exp_sq_le_two hX hK hcond).const_mul t)
        (exp_tsq_integrable hX hK hcond t htk), integral_const_mul, hmean]
      ring
    have hbnd : ∫ ω, Real.exp ((t * X ω) ^ 2) ∂μ ≤ 1 + t ^ 2 * kk ^ 2 := by
      calc ∫ ω, Real.exp ((t * X ω) ^ 2) ∂μ
          ≤ ∫ ω, (t ^ 2 * kk ^ 2 * Real.exp ((X ω / kk) ^ 2) + (1 - t ^ 2 * kk ^ 2)) ∂μ := by
            refine integral_mono (exp_tsq_integrable hX hK hcond t htk)
              (((expSq_integrable hX hcond).const_mul _).add (integrable_const _)) ?_
            exact fun ω => exp_tsq_le hkk t (X ω) htk
        _ = t ^ 2 * kk ^ 2 * (∫ ω, Real.exp ((X ω / kk) ^ 2) ∂μ) + (1 - t ^ 2 * kk ^ 2) := by
            rw [integral_add ((expSq_integrable hX hcond).const_mul _) (integrable_const _),
              integral_const_mul, integral_const, probReal_univ, one_smul]
        _ ≤ t ^ 2 * kk ^ 2 * 2 + (1 - t ^ 2 * kk ^ 2) := by
            have := expSq_integral_le hX hcond
            nlinarith [this, mul_nonneg (sq_nonneg t) (sq_nonneg kk)]
        _ = 1 + t ^ 2 * kk ^ 2 := by ring
    calc ∫ ω, Real.exp (t * X ω) ∂μ ≤ ∫ ω, Real.exp ((t * X ω) ^ 2) ∂μ := hstep.trans_eq hsplit
      _ ≤ 1 + t ^ 2 * kk ^ 2 := hbnd
      _ ≤ Real.exp (t ^ 2 * kk ^ 2) := by linarith [Real.add_one_le_exp (t ^ 2 * kk ^ 2)]
      _ ≤ Real.exp (3 * kk ^ 2 * t ^ 2 / 2) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg kk)])
  · -- Large-t regime: AM–GM domination.
    calc ∫ ω, Real.exp (t * X ω) ∂μ
        ≤ ∫ ω, Real.exp (t ^ 2 * kk ^ 2 / 2) * Real.exp ((X ω / kk) ^ 2 / 2) ∂μ := by
          refine integral_mono hXint ((expHalfSq_integrable hX hcond).const_mul _) ?_
          exact fun ω => exp_mul_le_half hkk t (X ω)
      _ = Real.exp (t ^ 2 * kk ^ 2 / 2) * ∫ ω, Real.exp ((X ω / kk) ^ 2 / 2) ∂μ :=
          integral_const_mul _ _
      _ ≤ Real.exp (t ^ 2 * kk ^ 2 / 2) * (3 / 2) :=
          mul_le_mul_of_nonneg_left (expHalfSq_integral_le hX hcond) (Real.exp_pos _).le
      _ ≤ Real.exp (3 * kk ^ 2 * t ^ 2 / 2) := by
          rw [show (3 : ℝ) * kk ^ 2 * t ^ 2 / 2 = t ^ 2 * kk ^ 2 / 2 + t ^ 2 * kk ^ 2 by ring,
            Real.exp_add]
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          calc (3 : ℝ) / 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
            _ ≤ Real.exp (t ^ 2 * kk ^ 2) := Real.exp_le_exp.2 htk.le

/-- **B2** (HDP Proposition 2.6.6(iv), frozen proxy `C = 3`): mean zero +
sub-Gaussian norm bound `‖X‖_{ψ₂} ≤ K` give
`HasSubgaussianMGF X (3·K²) μ`. -/
theorem hasSubgaussianMGF_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF-predicate regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.6
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Prop 2.6.6
    (h : subGaussianNorm X μ ≤ K)
    -- USER-INPUT: mean zero; HDP Prop 2.6.6(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0) :
    ProbabilityTheory.HasSubgaussianMGF X (3 * K ^ 2) μ := by
  have hcond := lintegral_exp_sq_le_two_of_subGaussianNorm_le hX hK h
  exact hasSubgaussianMGF_of_lintegral_exp_sq_le_two hX hK hcond hmean

/-- B2 in the project carrier: `IsSubGaussian X (3·K²) μ` (centered = raw via
`hmean` + `sub_zero` + `HasSubgaussianMGF.congr`). -/
theorem isSubGaussian_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF-predicate regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.6
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Prop 2.6.6
    (h : subGaussianNorm X μ ≤ K)
    -- USER-INPUT: mean zero; HDP Prop 2.6.6(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0) :
    IsSubGaussian X (3 * K ^ 2) μ := by
  rw [isSubGaussian_iff, hmean]
  simp only [sub_zero]
  exact hasSubgaussianMGF_of_subGaussianNorm_le hX hK h hmean

end StatLean.ConcentrationInequalities
