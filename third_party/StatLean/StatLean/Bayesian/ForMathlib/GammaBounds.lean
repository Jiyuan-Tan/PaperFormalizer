module
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Distributions.Gamma

@[expose] public section

/-!
# Elementary two-sided bounds on the Gamma function

The handful of numeric Gamma-function estimates the Dirichlet–Laplace marginal-density analysis
needs: the range of `Γ(1 + a)` for `a ∈ [0, 1]`, the derived bounds on `Γ(a)`, `Γ(1 − a)`, and the
half-integer factorial bound `Γ(q/2 + 1) ≤ (q + 1)^{q+1}`. Plus the (measure-theoretic) fact that
the Gamma law puts no mass on the nonpositive half-line.

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*
(arXiv:1401.5398), Lemma 3.3 and §6 ball-volume bookkeeping, which invoke these **elementary Gamma
bounds** (there stated without proof, and — see below — with one erroneous constant). All estimates
here are classical facts about `Γ` on `(0, 2]`.

**Proof formalization notes (deviation D6).** We prove everything from the single range
`Γ(1 + a) ∈ [e⁻¹, 2]` for `a ∈ [0, 1]` (`exp_neg_one_le_Gamma_one_add`, `Gamma_one_add_le_two`),
obtained by convexity/monotonicity of `Γ` on `[1, 2]` together with `Γ(1) = Γ(2) = 1` — **avoiding
Alzer's inequality** (which the paper's sketch leans on and which is not in Mathlib). The
recurrence `Γ(a) = Γ(1 + a)/a` then gives `Γ(a) ≤ 2/a` and `Γ(a) ≥ 1/(e·a)` on `(0, 1]`; note the
paper's "`Γ(x) ≥ 1/x`" is **false as stated** (e.g. `Γ(1) = 1 = 1/1` is not a strict lower bound and
`Γ` dips below `1/x` for small `x` only up to the `e` factor), so we carry the correct
`Γ(a) ≥ 1/(e·a)`. `Gamma_one_sub_le_four` uses `1 − a ∈ [1/2, 1]` with `Γ(1/2) = √π < 4`;
`Gamma_half_add_one_le` chains `Γ(q/2 + 1) ≤ Γ(q + 1) = q!` (monotonicity on `[2, ∞)`,
`Real.Gamma_nat_eq_factorial`) with `q! ≤ (q + 1)^{q+1}`. `gammaMeasure_Iic_eq_zero` holds because
`gammaPDFReal` is `0` on `x < 0` and `{0}` is Lebesgue-null.

**Bibliographic comments.** The convexity/log-convexity of `Γ` and its characterization on `[1, 2]`
are the Bohr–Mollerup theorem (H. Bohr, J. Mollerup, 1922); the factorial identity `Γ(n + 1) = n!`
is Euler's (1729).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- Uniform lower bound `e⁻¹ ≤ Γ(x)` for `x ≥ 1`, via the integral representation:
`Γ(x) = ∫_{Ioi 0} e^{−t} t^{x−1} ≥ ∫_{Ioi 1} e^{−t} t^{x−1} ≥ ∫_{Ioi 1} e^{−t} = e^{−1}`
(using `t^{x−1} ≥ 1` on `[1, ∞)` since `x − 1 ≥ 0`). -/
private theorem exp_neg_one_le_Gamma_aux {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-1) ≤ Real.Gamma x := by
  have hs : (0 : ℝ) < x := by linarith
  have hconv : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (x - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent hs
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (by norm_num)
  have hconv1 : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (x - 1)) (Set.Ioi 1) :=
    hconv.mono_set hsub
  rw [Real.Gamma_eq_integral hs]
  calc Real.exp (-1)
      = ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) := (integral_exp_neg_Ioi 1).symm
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (x - 1) := by
        refine setIntegral_mono_on (integrableOn_exp_neg_Ioi 1) hconv1 measurableSet_Ioi ?_
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_rpow ht1 (by linarith))
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1) := by
        refine setIntegral_mono_set hconv ?_ (ae_of_all _ fun t ht => hsub ht)
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
        have : (0 : ℝ) < t := ht
        positivity

/-- `Γ(1 + a) ≤ 2` for `a ∈ [0, 1]` (in fact `Γ(1 + a) ≤ 1` there, by convexity with
`Γ(1) = Γ(2) = 1`; the looser bound `2` is all downstream needs). Deviation D6. -/
theorem Gamma_one_add_le_two {a : ℝ}
    -- LEAN-ONLY: a ≥ 0, so 1 + a ∈ [1, 2] where Γ ≤ 1 (convexity on [1,2])
    (ha0 : 0 ≤ a)
    -- LEAN-ONLY: a ≤ 1, upper end of the [1,2] window
    (ha1 : a ≤ 1) :
    Real.Gamma (1 + a) ≤ 2 := by
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc (x := (1 : ℝ)) (y := 2)
    (by norm_num) (by norm_num)
    (show (1 + a) ∈ Set.Icc (1 : ℝ) 2 from ⟨by linarith, by linarith⟩)
  rw [Real.Gamma_one, Real.Gamma_two, max_self] at h
  linarith

/-- `e⁻¹ ≤ Γ(1 + a)` for `a ∈ [0, 1]` (the minimum of `Γ` on `[1, 2]` is `≈ 0.886 > e⁻¹`).
Deviation D6. -/
theorem exp_neg_one_le_Gamma_one_add {a : ℝ}
    -- LEAN-ONLY: a ≥ 0, so 1 + a ∈ [1, 2] where Γ ≥ e⁻¹
    (ha0 : 0 ≤ a)
    -- LEAN-ONLY: a ≤ 1, upper end of the [1,2] window
    (ha1 : a ≤ 1) :
    Real.exp (-1) ≤ Real.Gamma (1 + a) :=
  exp_neg_one_le_Gamma_aux (by linarith)

/-- `Γ(a) ≤ 2/a` on `(0, 1]`, from `Γ(a) = Γ(1 + a)/a` and `Γ(1 + a) ≤ 2`. -/
theorem Gamma_le_two_div {a : ℝ}
    -- LEAN-ONLY: a > 0, so the recurrence Γ(a) = Γ(1+a)/a is valid and a⁻¹ > 0
    (ha0 : 0 < a)
    -- LEAN-ONLY: a ≤ 1, the range on which Γ(1+a) ≤ 2 holds
    (ha1 : a ≤ 1) :
    Real.Gamma a ≤ 2 / a := by
  have hga : Real.Gamma (a + 1) = a * Real.Gamma a := Real.Gamma_add_one ha0.ne'
  have h2 : Real.Gamma (1 + a) ≤ 2 := Gamma_one_add_le_two ha0.le ha1
  rw [add_comm] at hga
  rw [hga] at h2
  rw [le_div_iff₀ ha0, mul_comm]
  exact h2

/-- `1/(e·a) ≤ Γ(a)` on `(0, 1]`, from `Γ(a) = Γ(1 + a)/a` and `Γ(1 + a) ≥ e⁻¹`. This is the
correct form of the paper's (erroneous) `Γ(x) ≥ 1/x`; deviation D6. -/
theorem inv_e_mul_le_Gamma {a : ℝ}
    -- LEAN-ONLY: a > 0, so the recurrence Γ(a) = Γ(1+a)/a is valid
    (ha0 : 0 < a)
    -- LEAN-ONLY: a ≤ 1, the range on which Γ(1+a) ≥ e⁻¹ holds
    (ha1 : a ≤ 1) :
    1 / (Real.exp 1 * a) ≤ Real.Gamma a := by
  have hga : Real.Gamma (a + 1) = a * Real.Gamma a := Real.Gamma_add_one ha0.ne'
  have hlow : Real.exp (-1) ≤ Real.Gamma (1 + a) := exp_neg_one_le_Gamma_one_add ha0.le ha1
  rw [add_comm] at hga
  rw [hga, Real.exp_neg] at hlow
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have key : (1 : ℝ) ≤ Real.exp 1 * (a * Real.Gamma a) := by
    have := mul_le_mul_of_nonneg_left hlow he.le
    rwa [mul_inv_cancel₀ he.ne'] at this
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.exp 1 * a),
    show Real.Gamma a * (Real.exp 1 * a) = Real.exp 1 * (a * Real.Gamma a) by ring]
  exact key

/-- `e⁻¹ ≤ Γ(x)` for `x ≥ 1` (uniform lower bound on `[1, ∞)`): on `[1, 2]` this is
`exp_neg_one_le_Gamma_one_add`; on `[2, ∞)` monotonicity of `Γ` gives `Γ(x) ≥ Γ(2) = 1 ≥ e⁻¹`. -/
theorem exp_neg_one_le_Gamma {x : ℝ}
    -- LEAN-ONLY: x ≥ 1; below 1 the Γ pole makes Γ arbitrarily large but the bound is not needed
    (hx : 1 ≤ x) :
    Real.exp (-1) ≤ Real.Gamma x :=
  exp_neg_one_le_Gamma_aux hx

/-- `Γ(1 − a) ≤ 4` for `a ∈ [0, 1/2]` (`1 − a ∈ [1/2, 1]`, where `Γ ≤ Γ(1/2) = √π < 4`). The
`a ≤ 1/2` ceiling is deviation D8 (the density upper bound genuinely needs it: `Γ(1 − a)` blows up as
`a → 1`). -/
theorem Gamma_one_sub_le_four {a : ℝ}
    -- LEAN-ONLY: a ≥ 0, so 1 − a ≤ 1 stays in the bounded window
    (ha0 : 0 ≤ a)
    -- USER-INPUT: a ≤ 1/2 keeps Γ(1−a) finite (Γ(1−a)→∞ as a→1); BPPD Lemma 3.2 (D8)
    (ha1 : a ≤ 1 / 2) :
    Real.Gamma (1 - a) ≤ 4 := by
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc (x := (1 / 2 : ℝ)) (y := 1)
    (by norm_num) (by norm_num)
    (show (1 - a) ∈ Set.Icc (1 / 2 : ℝ) 1 from ⟨by linarith, by linarith⟩)
  rw [Real.Gamma_one_half_eq, Real.Gamma_one] at h
  have hpi : Real.sqrt Real.pi ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt Real.pi_le_four
  calc Real.Gamma (1 - a) ≤ max (Real.sqrt Real.pi) 1 := h
    _ ≤ 4 := max_le (by linarith) (by norm_num)

/-- `Γ(q/2 + 1) ≤ (q + 1)^{q+1}` for natural `q` (a crude factorial bound for the ball-volume
denominators): `Γ(q/2 + 1) ≤ Γ(q + 1) = q! ≤ (q + 1)^{q+1}`. -/
theorem Gamma_half_add_one_le (q : ℕ) :
    Real.Gamma ((q : ℝ) / 2 + 1) ≤ ((q : ℝ) + 1) ^ (q + 1) := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q
    · simp only [Nat.cast_zero, zero_div, zero_add, Real.Gamma_one]; norm_num
    · -- q = 1: Γ(3/2) = (1/2)√π ≤ (1/2)·2 = 1 ≤ 4 = 2²
      have hval : Real.Gamma ((1 : ℝ) / 2 + 1) = (1 / 2) * Real.sqrt Real.pi := by
        rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      have hpi : Real.sqrt Real.pi ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt Real.pi_le_four
      rw [Nat.cast_one, hval]
      have : (0 : ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
      norm_num
      nlinarith [hpi, this]
  · -- q ≥ 2: monotonicity on [2, ∞) then factorial bound
    have hmono : Real.Gamma ((q : ℝ) / 2 + 1) ≤ Real.Gamma ((q : ℝ) + 1) := by
      refine Real.Gamma_strictMonoOn_Ici.monotoneOn ?_ ?_ ?_
      · exact Set.mem_Ici.mpr (by
          have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
          linarith)
      · exact Set.mem_Ici.mpr (by
          have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
          linarith)
      · have : (0 : ℝ) ≤ (q : ℝ) := by positivity
        linarith
    have hfac : Real.Gamma ((q : ℝ) + 1) = (Nat.factorial q : ℝ) := by
      rw [Real.Gamma_nat_eq_factorial]
    have hnat : Nat.factorial q ≤ (q + 1) ^ (q + 1) := by
      calc Nat.factorial q ≤ q ^ q := Nat.factorial_le_pow q
        _ ≤ (q + 1) ^ q := Nat.pow_le_pow_left (by omega) q
        _ ≤ (q + 1) ^ (q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc Real.Gamma ((q : ℝ) / 2 + 1) ≤ Real.Gamma ((q : ℝ) + 1) := hmono
      _ = (Nat.factorial q : ℝ) := hfac
      _ ≤ ((q + 1) ^ (q + 1) : ℕ) := by exact_mod_cast hnat
      _ = ((q : ℝ) + 1) ^ (q + 1) := by push_cast; ring

/-- The Gamma law puts no mass on the nonpositive half-line: `gammaMeasure a r (Iic 0) = 0`.
(`gammaPDFReal` is `0` on `x < 0`, and `{0}` is Lebesgue-null.) Needed for the probability-measure
instance on the Dirichlet–Laplace mixture. -/
theorem gammaMeasure_Iic_eq_zero {a r : ℝ}
    -- LEAN-ONLY: a > 0, shape of a genuine Gamma law
    (ha : 0 < a)
    -- LEAN-ONLY: r > 0, rate of a genuine Gamma law
    (hr : 0 < r) :
    gammaMeasure a r (Set.Iic 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iic,
    setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm]
  exact lintegral_gammaPDF_of_nonpos le_rfl

end StatLean.Bayesian
