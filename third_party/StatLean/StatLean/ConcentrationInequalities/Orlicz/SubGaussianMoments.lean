module
public import StatLean.ConcentrationInequalities.Orlicz.Attainment
public import StatLean.ConcentrationInequalities.ForMathlib.ExpTaylorBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# Moment growth from the ψ₂ norm

Moment growth from the ψ₂ condition (HDP Prop 2.6.1 (iii)⇒(ii) / Prop
2.6.6(ii)): if $\|X\|_{\psi_2} \le K$ then for all $p \ge 1$
$$ \|X\|_{L^p} \le \sqrt{3}\, K \sqrt{p}, $$
via the even-moment core $\mathbb{E}|X|^{2n} \le 2\,n!\,K^{2n}$ and
`eLpNorm` exponent monotonicity — no Gamma function anywhere.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((iii)⇒(ii)) and Proposition
2.6.6(ii).

**Proof formalization notes.** Constant `C = √3` (frozen numeral
`Real.sqrt 3`; formula: even-moment bound gives `(2·n!)^{1/(2n)}·K·1 ≤
√2·√n·K`, then the reduction `‖X‖_p ≤ ‖X‖_{2⌈p/2⌉}` with `2⌈p/2⌉ ≤ 3p`-slack
absorbed into `√3`). The book's route through `Γ(p/2 + 1)` is avoided: the
even-moment core is the termwise comparison `|x|^{2n} ≤ K^{2n}·n!·e^{(x/K)²}`
(`pow_div_factorial_le_exp`), and real `p ≥ 1` reduces to the even integer
`2⌈p/2⌉` via `MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le` (needs
`[IsProbabilityMeasure μ]`). Statement language: `eLpNorm` at
`ENNReal.ofReal p`; the raw core is a plain lintegral-of-pow bound so the
rpow/coercion conversion is confined to one private helper at proof time.
Named-sorry fallback of this work item: `eLpNorm_le_of_subGaussianNorm_le`
(the real-`p` reduction); the even-moment core must close.

**Bibliographic comments.** Moment growth `‖X‖_p ≍ √p` as the second face of
sub-Gaussianity is classical (Khinchin-type inequalities; Buldygin–Kozachenko
1980).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Even-moment core (HDP §2.6.1): `E|X|^{2n} ≤ 2·n!·K^{2n}` from the
threshold-2 condition, by the termwise bound
`|x|^{2n} ≤ K^{2n}·n!·e^{(x/K)²}` (`pow_div_factorial_le_exp`). -/
theorem lintegral_pow_le_of_lintegral_exp_sq_le_two {X : Ω → ℝ} {μ : Measure Ω}
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 * n)) ∂μ
      ≤ ENNReal.ofReal (2 * n.factorial * (K : ℝ) ^ (2 * n)) := by
  have hKR : (0 : ℝ) < (K : ℝ) := hK
  -- Termwise: `|X ω|^{2n} ≤ K^{2n}·n!·e^{(X ω/K)²}`.
  have hpt : ∀ ω, ENNReal.ofReal (|X ω| ^ (2 * n))
      ≤ ENNReal.ofReal ((K : ℝ) ^ (2 * n) * n.factorial)
        * ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) := by
    intro ω
    have hx2 : (|X ω| / (K : ℝ)) ^ 2 = (X ω / (K : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, sq_abs]
    have hterm := pow_div_factorial_le_exp (sq_nonneg (|X ω| / (K : ℝ))) n
    have e1 : ((|X ω| / (K : ℝ)) ^ 2) ^ n = |X ω| ^ (2 * n) / (K : ℝ) ^ (2 * n) := by
      rw [← pow_mul, div_pow]
    rw [e1, hx2, div_div, div_le_iff₀ (by positivity)] at hterm
    have key : |X ω| ^ (2 * n)
        ≤ (K : ℝ) ^ (2 * n) * n.factorial * Real.exp ((X ω / (K : ℝ)) ^ 2) := by
      calc |X ω| ^ (2 * n)
          ≤ Real.exp ((X ω / (K : ℝ)) ^ 2) * ((K : ℝ) ^ (2 * n) * n.factorial) := hterm
        _ = (K : ℝ) ^ (2 * n) * n.factorial * Real.exp ((X ω / (K : ℝ)) ^ 2) := by ring
    calc ENNReal.ofReal (|X ω| ^ (2 * n))
        ≤ ENNReal.ofReal ((K : ℝ) ^ (2 * n) * n.factorial
            * Real.exp ((X ω / (K : ℝ)) ^ 2)) := ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal ((K : ℝ) ^ (2 * n) * n.factorial)
            * ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 * n)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal ((K : ℝ) ^ (2 * n) * n.factorial)
          * ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal ((K : ℝ) ^ (2 * n) * n.factorial)
          * ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((K : ℝ) ^ (2 * n) * n.factorial) * 2 := mul_le_mul_right h _
    _ = ENNReal.ofReal (2 * n.factorial * (K : ℝ) ^ (2 * n)) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- Even-exponent `eLpNorm` bridge: `‖X‖_{2n} ≤ √2·√n·K` from the even-moment
core (`(2·n!)^{1/(2n)} ≤ √2·√n`). -/
theorem eLpNorm_two_mul_le_of_lintegral_exp_sq_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; eLpNorm regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    (n : ℕ)
    -- LEAN-ONLY: n ≥ 1; the p = 0 exponent is excluded (eLpNorm degenerates)
    (hn : 1 ≤ n) :
    MeasureTheory.eLpNorm X (2 * n) μ
      ≤ ENNReal.ofReal (Real.sqrt 2 * Real.sqrt n * (K : ℝ)) := by
  set c : ℝ := Real.sqrt 2 * Real.sqrt n * (K : ℝ) with hcdef
  have hcnn : 0 ≤ c := by positivity
  have hcore := lintegral_pow_le_of_lintegral_exp_sq_le_two hK h n
  have hp0 : (2 * (n : ℝ≥0∞)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hptop : (2 * (n : ℝ≥0∞)) ≠ ∞ := by finiteness
  set q : ℝ := (2 * (n : ℝ≥0∞)).toReal with hqdef
  have hr : q = ((2 * n : ℕ) : ℝ) := by
    rw [hqdef, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
    push_cast; ring
  have hqpos : 0 < q := by rw [hr]; positivity
  -- Rewrite the enorm integrand as `ofReal (|X ·|^{2n})`.
  have hptwise : ∀ a, ‖X a‖ₑ ^ q = ENNReal.ofReal (|X a| ^ (2 * n)) := by
    intro a
    rw [Real.enorm_eq_ofReal_abs, hr, ENNReal.rpow_natCast, ENNReal.ofReal_pow (abs_nonneg _)]
  have hint : (∫⁻ a, ‖X a‖ₑ ^ q ∂μ)
      ≤ ENNReal.ofReal (2 * n.factorial * (K : ℝ) ^ (2 * n)) := by
    rw [lintegral_congr hptwise]; exact hcore
  -- Real bound: `2·n!·K^{2n} ≤ c^{2n}`.
  have hc_pow : c ^ (2 * n) = (2 : ℝ) ^ n * (n : ℝ) ^ n * (K : ℝ) ^ (2 * n) := by
    rw [hcdef, mul_pow, mul_pow, pow_mul (Real.sqrt 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      pow_mul (Real.sqrt n), Real.sq_sqrt (Nat.cast_nonneg n)]
  have hcreal : 2 * (n.factorial : ℝ) * (K : ℝ) ^ (2 * n) ≤ c ^ (2 * n) := by
    rw [hc_pow]
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hfac : 2 * (n.factorial : ℝ) ≤ (2 : ℝ) ^ n * (n : ℝ) ^ n :=
      mul_le_mul h2 h1 (Nat.cast_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hfac (by positivity)
  -- Assemble via `eLpNorm'` and rpow monotonicity.
  rw [eLpNorm_eq_eLpNorm' hp0 hptop, eLpNorm'_eq_lintegral_enorm, ← hqdef]
  have hfin : (ENNReal.ofReal (c ^ (2 * n))) ^ (1 / q) = ENNReal.ofReal c := by
    rw [ENNReal.ofReal_pow hcnn, ← ENNReal.rpow_natCast (ENNReal.ofReal c) (2 * n),
      ← ENNReal.rpow_mul, hr, mul_one_div, div_self (by positivity), ENNReal.rpow_one]
  calc (∫⁻ a, ‖X a‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ (ENNReal.ofReal (2 * n.factorial * (K : ℝ) ^ (2 * n))) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ ≤ (ENNReal.ofReal (c ^ (2 * n))) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hcreal) (by positivity)
    _ = ENNReal.ofReal c := hfin

/-- **Moment growth** (HDP Proposition 2.6.6(ii), `C = √3`): a sub-Gaussian
norm bound gives `‖X‖_{L^p} ≤ √3·K·√p` for every real `p ≥ 1`. -/
theorem eLpNorm_le_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; exponent monotonicity of eLpNorm needs it
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; eLpNorm regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.6
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Prop 2.6.6
    (h : subGaussianNorm X μ ≤ K)
    {p : ℝ}
    -- USER-INPUT: moment order p ≥ 1; HDP Prop 2.6.6(ii)
    (hp : 1 ≤ p) :
    MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (Real.sqrt 3 * (K : ℝ) * Real.sqrt p) := by
  have hcond := lintegral_exp_sq_le_two_of_subGaussianNorm_le hX hK h
  set n := ⌈p / 2⌉₊ with hndef
  have hp2pos : 0 < p / 2 := by linarith
  have hn1 : 1 ≤ n := Nat.one_le_ceil_iff.mpr hp2pos
  have hpn : p ≤ 2 * (n : ℝ) := by
    have := Nat.le_ceil (p / 2); rw [← hndef] at this; linarith
  have hexp : ENNReal.ofReal p ≤ 2 * (n : ℝ≥0∞) := by
    rw [show (2 * (n : ℝ≥0∞)) = ENNReal.ofReal (2 * n) by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]]
    exact ENNReal.ofReal_le_ofReal hpn
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le hexp hX.aestronglyMeasurable
  have hbound := eLpNorm_two_mul_le_of_lintegral_exp_sq_le_two hX hK hcond n hn1
  refine (hmono.trans hbound).trans (ENNReal.ofReal_le_ofReal ?_)
  have h2n3p : 2 * (n : ℝ) ≤ 3 * p := by
    have := Nat.ceil_lt_add_one (le_of_lt hp2pos); rw [← hndef] at this; linarith
  calc Real.sqrt 2 * Real.sqrt n * (K : ℝ)
      = Real.sqrt (2 * n) * (K : ℝ) := by rw [Real.sqrt_mul (by norm_num)]
    _ ≤ Real.sqrt (3 * p) * (K : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h2n3p) (by positivity)
    _ = Real.sqrt 3 * (K : ℝ) * Real.sqrt p := by rw [Real.sqrt_mul (by norm_num)]; ring

end StatLean.ConcentrationInequalities
