module
public import StatLean.ConcentrationInequalities.Orlicz.Basic
public import StatLean.ConcentrationInequalities.Orlicz.Attainment
public import StatLean.ConcentrationInequalities.ForMathlib.ExpTaylorBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# ψ₂ norm from moment growth

The converse moment direction (HDP Prop 2.6.1 (ii)⇒(iii)): if
$\|X\|_{L^p} \le K\sqrt{p}$ for all $p \ge 1$, then
$$ \|X\|_{\psi_2} \le 2\sqrt{e}\, K, $$
by the exponential-series / geometric-sum argument
$\mathbb{E}\,e^{\lambda^2 X^2} = \sum_n \lambda^{2n}\,\mathbb{E}X^{2n}/n!$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((ii)⇒(iii)).

**Proof formalization notes.** Constant `K₃ = 2√e·K₂` book-exact (frozen as
`ENNReal.ofReal (2 * Real.sqrt (Real.exp 1))` — the one constant in this
cluster not encodable as `NNReal.sqrt` of a rational; formula: at
`λ² = 1/(4eK₂²)` the series has geometric ratio `2eλ²K₂² = 1/2`, so it sums
to `2`). The tsum/lintegral swap is `MeasureTheory.lintegral_tsum` +
`ENNReal.ofReal_tsum_of_nonneg`; the factorial lower bound `n! ≥ (n/e)^n` is
the ForMathlib brick `pow_div_exp_pow_le_factorial`. The moment hypothesis is
consumed only at even integers `p = 2n` through the unpacking helper
`lintegral_pow_le_of_eLpNorm_le`, so the rpow/coercion conversion is confined
there. Named-sorry fallback of this work item:
`subGaussianNorm_le_of_eLpNorm_le` (the tsum/geometric-series swap), with the
unpacking helper closed.

**Bibliographic comments.** The series argument converting moment growth into
square-exponential integrability is classical (Khinchin; Buldygin–Kozachenko
1980).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `eLpNorm` unpacking at even integers: `‖X‖_{2n} ≤ K·√(2n)` gives the
plain even-moment bound `E X^{2n} ≤ (K·√(2n))^{2n} = K^{2n}·(2n)^n`. -/
lemma lintegral_pow_le_of_eLpNorm_le {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; eLpNorm-unpacking regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0} {n : ℕ}
    -- LEAN-ONLY: n ≥ 1; matches the p ≥ 1 range of the moment hypothesis
    (hn : 1 ≤ n)
    -- USER-INPUT: L^{2n} moment bound ‖X‖_{2n} ≤ K√(2n); HDP Prop 2.6.1(ii)
    (h : MeasureTheory.eLpNorm X (2 * n) μ
      ≤ ENNReal.ofReal ((K : ℝ) * Real.sqrt (2 * n))) :
    ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * n)) ∂μ
      ≤ ENNReal.ofReal ((K : ℝ) ^ (2 * n) * (2 * n : ℝ) ^ n) := by
  have hnpos : 0 < n := hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnpos.ne'
  set p : ℝ≥0∞ := 2 * n with hp_def
  have hp_ne_zero : p ≠ 0 := by rw [hp_def]; exact mul_ne_zero (by norm_num) hn0
  have hp_ne_top : p ≠ ∞ := by
    rw [hp_def]; exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n)
  have hptr : p.toReal = 2 * (n : ℝ) := by
    rw [hp_def, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  have hptr2 : p.toReal = ((2 * n : ℕ) : ℝ) := by rw [hptr]; push_cast; ring
  have hpr : 0 < p.toReal := by
    rw [hptr]
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    positivity
  have key : ∫⁻ ω, ‖X ω‖ₑ ^ p.toReal ∂μ = (eLpNorm X p μ) ^ p.toReal := by
    rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top, lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr]
  have hpt : ∀ ω, ENNReal.ofReal ((X ω) ^ (2 * n)) = ‖X ω‖ₑ ^ p.toReal := by
    intro ω
    rw [hptr2, Real.enorm_eq_ofReal_abs, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow (abs_nonneg _), (even_two_mul n).pow_abs (X ω)]
  have hc_nonneg : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  have hval : ((K : ℝ) * Real.sqrt (2 * n)) ^ p.toReal
      = (K : ℝ) ^ (2 * n) * (2 * n : ℝ) ^ n := by
    have e1 : ((K : ℝ) * Real.sqrt (2 * n)) ^ p.toReal
        = ((K : ℝ) * Real.sqrt (2 * n)) ^ (2 * n) := by
      rw [hptr2, Real.rpow_natCast]
    rw [e1, mul_pow]
    congr 1
    rw [pow_mul, Real.sq_sqrt hc_nonneg]
  calc ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * n)) ∂μ
      = ∫⁻ ω, ‖X ω‖ₑ ^ p.toReal ∂μ := lintegral_congr hpt
    _ = (eLpNorm X p μ) ^ p.toReal := key
    _ ≤ (ENNReal.ofReal ((K : ℝ) * Real.sqrt (2 * n))) ^ p.toReal :=
        ENNReal.rpow_le_rpow h hpr.le
    _ = ENNReal.ofReal (((K : ℝ) * Real.sqrt (2 * n)) ^ p.toReal) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hpr.le]
    _ = ENNReal.ofReal ((K : ℝ) ^ (2 * n) * (2 * n : ℝ) ^ n) := by rw [hval]

/-- **Norm from moments** (HDP Proposition 2.6.1 (ii)⇒(iii), `K₃ = 2√e·K₂`
book-exact): moment growth `‖X‖_p ≤ K√p` for all `p ≥ 1` bounds the
sub-Gaussian norm by `2√e·K`. -/
theorem subGaussianNorm_le_of_eLpNorm_le
    -- LEAN-ONLY: probability measure; the geometric series sums against μ(univ) = 1
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; series/lintegral-swap regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive moment scale; HDP Prop 2.6.1(ii)
    (hK : 0 < K)
    -- USER-INPUT: moment growth ‖X‖_p ≤ K√p for all p ≥ 1; HDP Prop 2.6.1(ii)
    (hmom : ∀ p : ℝ, 1 ≤ p →
      MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal ((K : ℝ) * Real.sqrt p)) :
    subGaussianNorm X μ
      ≤ ENNReal.ofReal (2 * Real.sqrt (Real.exp 1) * (K : ℝ)) := by
  set Cr : ℝ := 2 * Real.sqrt (Real.exp 1) * (K : ℝ) with hCr_def
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsqe : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos 1)
  have hCr : 0 < Cr := by rw [hCr_def]; exact mul_pos (mul_pos two_pos hsqe) hKr
  have hCrNN : 0 < Cr.toNNReal := Real.toNNReal_pos.mpr hCr
  have hcoe : (Cr.toNNReal : ℝ) = Cr := Real.coe_toNNReal Cr hCr.le
  rw [show ENNReal.ofReal Cr = ((Cr.toNNReal : ℝ≥0) : ℝ≥0∞) from rfl]
  apply subGaussianNorm_le_of_lintegral_exp_sq_le_two hCrNN
  simp only [hcoe]
  -- Reduced to the book form `E exp(X²/Cr²) ≤ 2` at `Cr = 2√e·K`.
  -- Measurability of each series term.
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun ω => ENNReal.ofReal ((X ω / Cr) ^ (2 * k) / (k.factorial : ℝ))) μ := by
    intro k
    exact (((hX.div_const Cr).pow_const (2 * k)).div_const (k.factorial : ℝ)).ennreal_ofReal
  -- Pointwise expansion of `exp((X/Cr)²)` as the even Taylor series.
  have hpt1 : ∀ ω, ENNReal.ofReal (Real.exp ((X ω / Cr) ^ 2))
      = ∑' k : ℕ, ENNReal.ofReal ((X ω / Cr) ^ (2 * k) / (k.factorial : ℝ)) := by
    intro ω
    have hexp : Real.exp ((X ω / Cr) ^ 2)
        = ∑' k : ℕ, ((X ω / Cr) ^ 2) ^ k / (k.factorial : ℝ) := by
      rw [Real.exp_eq_exp_ℝ]
      exact (NormedSpace.expSeries_div_hasSum_exp ((X ω / Cr) ^ 2)).tsum_eq.symm
    rw [hexp, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          (Real.summable_pow_div_factorial _)]
    exact tsum_congr (fun k => by rw [pow_mul])
  -- Swap `∫⁻` and `∑'` (nonneg terms; `lintegral_tsum`).
  have hint : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / Cr) ^ 2)) ∂μ
      = ∑' k : ℕ, ∫⁻ ω, ENNReal.ofReal ((X ω / Cr) ^ (2 * k) / (k.factorial : ℝ)) ∂μ := by
    simp_rw [hpt1]
    rw [lintegral_tsum hmeas]
  -- `Cr² = 4e·K²`.
  have hsq : Real.sqrt (Real.exp 1) ^ 2 = Real.exp 1 := Real.sq_sqrt (Real.exp_pos 1).le
  have hCr2 : Cr ^ 2 = 4 * Real.exp 1 * (K : ℝ) ^ 2 := by
    rw [hCr_def, mul_pow, mul_pow, hsq]; ring
  -- Per-term geometric bound `term n ≤ (1/2)^n`.
  have hbound : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((X ω / Cr) ^ (2 * n) / (n.factorial : ℝ)) ∂μ
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      have h1 : (fun ω => ENNReal.ofReal ((X ω / Cr) ^ (2 * 0) / ((0 : ℕ).factorial : ℝ)))
          = (fun _ => (1 : ℝ≥0∞)) := by funext ω; simp
      rw [h1, lintegral_one, measure_univ, pow_zero, ENNReal.ofReal_one]
    · have hn1' : 1 ≤ n := hn1
      have hD : (0 : ℝ) < Cr ^ (2 * n) * (n.factorial : ℝ) :=
        mul_pos (pow_pos hCr (2 * n)) (by exact_mod_cast n.factorial_pos)
      have hcn_nonneg : (0 : ℝ) ≤ 1 / (Cr ^ (2 * n) * (n.factorial : ℝ)) :=
        (one_div_pos.mpr hD).le
      have hpt2 : ∀ ω, ENNReal.ofReal ((X ω / Cr) ^ (2 * n) / (n.factorial : ℝ))
          = ENNReal.ofReal (1 / (Cr ^ (2 * n) * (n.factorial : ℝ)))
              * ENNReal.ofReal ((X ω) ^ (2 * n)) := by
        intro ω
        rw [← ENNReal.ofReal_mul hcn_nonneg]
        congr 1
        rw [div_pow]; ring
      have hmomn : MeasureTheory.eLpNorm X (2 * n) μ
          ≤ ENNReal.ofReal ((K : ℝ) * Real.sqrt (2 * n)) := by
        have h2n1 : (1 : ℝ) ≤ 2 * (n : ℝ) := by
          have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
          linarith
        have hmm := hmom (2 * (n : ℝ)) h2n1
        rwa [show ENNReal.ofReal (2 * (n : ℝ)) = (2 * (n : ℝ≥0∞)) by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
              ENNReal.ofReal_natCast]] at hmm
      have hhelp := lintegral_pow_le_of_eLpNorm_le hX hn1' hmomn
      have hn_pow : (n : ℝ) ^ n ≤ Real.exp 1 ^ n * (n.factorial : ℝ) := by
        have hbrick : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) :=
          pow_div_exp_pow_le_factorial n
        rw [div_pow, div_le_iff₀ (by positivity)] at hbrick
        rw [mul_comm (Real.exp 1 ^ n) (n.factorial : ℝ)]
        exact hbrick
      have hCr2n : Cr ^ (2 * n) = (4 * Real.exp 1 * (K : ℝ) ^ 2) ^ n := by
        rw [pow_mul, hCr2]
      have hLHS : (K : ℝ) ^ (2 * n) * (2 * n : ℝ) ^ n
          = (2 * (K : ℝ) ^ 2) ^ n * (n : ℝ) ^ n := by
        rw [pow_mul, mul_pow, mul_pow]; ring
      have e42 : (1 / 2 : ℝ) ^ n * (4 : ℝ) ^ n = 2 ^ n := by
        rw [← mul_pow]; norm_num
      have hRHS : (1 / 2 : ℝ) ^ n * (Cr ^ (2 * n) * (n.factorial : ℝ))
          = (2 * (K : ℝ) ^ 2) ^ n * (Real.exp 1 ^ n * (n.factorial : ℝ)) := by
        rw [hCr2n, mul_pow (4 * Real.exp 1) ((K : ℝ) ^ 2) n, mul_pow (4 : ℝ) (Real.exp 1) n,
            mul_pow 2 ((K : ℝ) ^ 2) n, ← e42]
        ring
      have key_real : (K : ℝ) ^ (2 * n) * (2 * n : ℝ) ^ n
          ≤ (1 / 2 : ℝ) ^ n * (Cr ^ (2 * n) * (n.factorial : ℝ)) := by
        rw [hLHS, hRHS]
        exact mul_le_mul_of_nonneg_left hn_pow (by positivity)
      calc ∫⁻ ω, ENNReal.ofReal ((X ω / Cr) ^ (2 * n) / (n.factorial : ℝ)) ∂μ
          = ENNReal.ofReal (1 / (Cr ^ (2 * n) * (n.factorial : ℝ)))
              * ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * n)) ∂μ := by
            simp_rw [hpt2]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (1 / (Cr ^ (2 * n) * (n.factorial : ℝ)))
              * ENNReal.ofReal ((K : ℝ) ^ (2 * n) * (2 * n : ℝ) ^ n) :=
            mul_le_mul_right hhelp _
        _ = ENNReal.ofReal ((1 / (Cr ^ (2 * n) * (n.factorial : ℝ)))
              * ((K : ℝ) ^ (2 * n) * (2 * n : ℝ) ^ n)) := by
            rw [← ENNReal.ofReal_mul hcn_nonneg]
        _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
            apply ENNReal.ofReal_le_ofReal
            rw [one_div (Cr ^ (2 * n) * (n.factorial : ℝ)), ← div_eq_inv_mul,
                div_le_iff₀ hD]
            exact key_real
  -- Assemble: series ≤ geometric sum = 2.
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / Cr) ^ 2)) ∂μ
      = ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal ((X ω / Cr) ^ (2 * n) / (n.factorial : ℝ)) ∂μ := hint
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (∑' n : ℕ, (1 / 2 : ℝ) ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two).symm
    _ = ENNReal.ofReal 2 := by rw [tsum_geometric_two]
    _ = 2 := by rw [ENNReal.ofReal_ofNat]

end StatLean.ConcentrationInequalities
