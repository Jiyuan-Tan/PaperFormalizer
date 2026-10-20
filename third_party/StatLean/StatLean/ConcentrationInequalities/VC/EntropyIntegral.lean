module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

@[expose] public section

/-!
# The Dudley entropy integral for VC classes

The entropy-integral evaluation used in Theorem 8.3.15's proof: with the
sample-independent covering bound
$N(T', \varepsilon) \le (4/\varepsilon)^{22 d}$ on $(0, 2)$,
$$ \int_0^2 \sqrt{22\, d \, \log\bigl(4/\varepsilon\bigr)}\;d\varepsilon
   \;\le\; 27 \sqrt{d}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.6 — the "bounded entropy integral" step in
the proof of Theorem 8.3.15 (the book leaves the integral as an unnamed
absolute constant).

**Proof formalization notes.** VC owns its own entropy integral (batch
decision R7): this file is self-contained interval-integral analysis with no
stub dependencies, and `VC/LawOfLargeNumbers.lean` plugs it into the
chaining cluster's `dudley_inequality_abs` directly. The `22` (not the
covering theorem's `21`) absorbs the factor-2 covering loss from the
symmetrized index set `T' = empProj '' F ∪ (−(empProj '' F))`, and the
`4/ε` (not `2/ε`) extends the bound to the full diameter range
`ε ∈ (0, 2)`. Evaluation is by the crude comparison `log y ≤ y − 1 ≤ y`
(`Real.log_le_sub_one_of_pos`), giving
`√(log(4/ε)) ≤ 2/√ε`, and `∫₀² ε^{−1/2} dε = 2√2`; the frozen numeral is
`27` from `√22 · 2 · 2√2 = 8√44 ≈ 26.53 ≤ 27`. Integrability of the
integrand near `0` is by domination by `ε^{−1/2}` (integrable rpow,
exponent `> −1`). Edge behavior: the integrand is junk (`log` of a
nonpositive argument) outside `(0, 4)`, but the interval of integration is
`(0, 2)`. Named-sorry fallback of this work item: `entropyIntegral_le`
(keep the two helper lemmas real; sorry only the final interval-integral
assembly).

**Bibliographic comments.** The entropy integral is R. M. Dudley's ("The
sizes of compact subsets of Hilbert space and continuity of Gaussian
processes," *J. Funct. Anal.* 1 (1967), 290–330); its finiteness for VC
classes — the fact that `∫₀² √(d·log(4/ε)) dε ≍ √d` — is the engine of the
uniform CLT/LLN for VC classes.
-/

open MeasureTheory intervalIntegral

namespace StatLean.ConcentrationInequalities

/-- Crude entropy-integrand comparison `√(log(4/ε)) ≤ 2/√ε` on `(0, 2]`
(LEAN-ONLY: `log y ≤ y` via `Real.log_le_sub_one_of_pos`; no book
content). -/
lemma sqrt_log_le_two_div_sqrt {ε : ℝ}
    -- LEAN-ONLY: the comparison's domain; matches the integration interval.
    (hε : 0 < ε) (hε2 : ε ≤ 2) :
    Real.sqrt (Real.log (4 / ε)) ≤ 2 / Real.sqrt ε := by
  have hε' : (0:ℝ) < 4 / ε := by positivity
  have hlog : Real.log (4 / ε) ≤ 4 / ε := by
    have := Real.log_le_sub_one_of_pos hε'
    linarith
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc Real.sqrt (Real.log (4 / ε)) ≤ Real.sqrt (4 / ε) := Real.sqrt_le_sqrt hlog
    _ = 2 / Real.sqrt ε := by
        rw [Real.sqrt_div' 4 hε.le, hsqrt4]

/-- Interval integrability of the VC entropy integrand on `(0, 2)`
(LEAN-ONLY: domination by `ε^{−1/2}`, integrable rpow with exponent
`> −1`). -/
lemma intervalIntegrable_sqrt_log_mul {c : ℝ}
    -- LEAN-ONLY: nonnegative multiplier so `√(c·log)` factors through `√c`.
    (hc : 0 ≤ c) :
    IntervalIntegrable (fun ε => Real.sqrt (c * Real.log (4 / ε)))
      MeasureTheory.volume 0 2 := by
  -- Dominating function `2√c · ε^(-1/2)`, integrable rpow (exponent > -1).
  have hdom : IntervalIntegrable (fun ε => 2 * Real.sqrt c * ε ^ (-(1/2) : ℝ))
      MeasureTheory.volume 0 2 :=
    (intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1/2))).const_mul _
  refine hdom.mono_fun' ?_ ?_
  · -- measurability of the integrand
    apply Measurable.aestronglyMeasurable
    exact Real.continuous_sqrt.measurable.comp
      (measurable_const.mul (Real.measurable_log.comp
        (measurable_const.div measurable_id)))
  · -- pointwise domination on `Ι 0 2 = Ioc 0 2`
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with ε hε
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hε
    obtain ⟨hε0, hε2⟩ := hε
    have hcs : Real.sqrt (c * Real.log (4 / ε))
        = Real.sqrt c * Real.sqrt (Real.log (4 / ε)) := Real.sqrt_mul hc _
    have hbound : Real.sqrt (Real.log (4 / ε)) ≤ 2 / Real.sqrt ε :=
      sqrt_log_le_two_div_sqrt hε0 hε2
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hcs]
    have hrpow : ε ^ (-(1/2) : ℝ) = 1 / Real.sqrt ε := by
      rw [Real.rpow_neg hε0.le, ← Real.sqrt_eq_rpow, one_div]
    rw [hrpow]
    have hsc : (0:ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
    calc Real.sqrt c * Real.sqrt (Real.log (4 / ε))
        ≤ Real.sqrt c * (2 / Real.sqrt ε) := by
          apply mul_le_mul_of_nonneg_left hbound hsc
      _ = 2 * Real.sqrt c * (1 / Real.sqrt ε) := by ring

/-- **Entropy integral bound for VC classes** (HDP §8.3.6, Theorem 8.3.15
proof step): `∫₀² √(22·d·log(4/ε)) dε ≤ 27·√d`. Frozen numeral `27` from
`√22 · 2 · 2√2 = 8√44 ≈ 26.53`. -/
theorem entropyIntegral_le {d : ℕ}
    -- USER-INPUT: 1 ≤ d (nondegenerate VC dimension); HDP §8.3.6.
    (hd1 : 1 ≤ d) :
    ∫ ε in (0 : ℝ)..2, Real.sqrt (22 * d * Real.log (4 / ε))
      ≤ 27 * Real.sqrt d := by
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  -- Integrability of LHS integrand (c = 22 d ≥ 0).
  have hInt : IntervalIntegrable
      (fun ε => Real.sqrt (22 * (d:ℝ) * Real.log (4 / ε)))
      MeasureTheory.volume 0 2 := by
    exact intervalIntegrable_sqrt_log_mul (c := 22 * (d:ℝ)) (by positivity)
  -- Bounding function `√(22 d) · (2 / √ε)`, whose integral we compute.
  set K : ℝ := Real.sqrt (22 * (d:ℝ)) with hK
  have hKnn : 0 ≤ K := Real.sqrt_nonneg _
  -- The dominating function `fun ε => K * (2 / √ε) = 2K * ε^(-1/2)`.
  have hgInt : IntervalIntegrable (fun ε => 2 * K * ε ^ (-(1/2) : ℝ))
      MeasureTheory.volume 0 2 :=
    (intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1/2))).const_mul _
  -- Pointwise: LHS integrand ≤ bounding function on (0,2].
  have hmono : ∀ ε ∈ Set.Ioo (0:ℝ) 2,
      Real.sqrt (22 * (d:ℝ) * Real.log (4 / ε)) ≤ 2 * K * ε ^ (-(1/2) : ℝ) := by
    intro ε hε
    obtain ⟨hε0, hε2⟩ := hε
    have hε2 : ε ≤ 2 := hε2.le
    have hfac : Real.sqrt (22 * (d:ℝ) * Real.log (4 / ε))
        = K * Real.sqrt (Real.log (4 / ε)) := by
      rw [hK, ← Real.sqrt_mul (by positivity)]
    have hb : Real.sqrt (Real.log (4 / ε)) ≤ 2 / Real.sqrt ε :=
      sqrt_log_le_two_div_sqrt hε0 hε2
    have hrpow : ε ^ (-(1/2) : ℝ) = 1 / Real.sqrt ε := by
      rw [Real.rpow_neg hε0.le, ← Real.sqrt_eq_rpow, one_div]
    rw [hfac, hrpow]
    calc K * Real.sqrt (Real.log (4 / ε))
        ≤ K * (2 / Real.sqrt ε) := mul_le_mul_of_nonneg_left hb hKnn
      _ = 2 * K * (1 / Real.sqrt ε) := by ring
  -- Compare integrals.
  have hcmp : (∫ ε in (0:ℝ)..2, Real.sqrt (22 * (d:ℝ) * Real.log (4 / ε)))
      ≤ ∫ ε in (0:ℝ)..2, 2 * K * ε ^ (-(1/2) : ℝ) := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hInt hgInt hmono
  -- Compute `∫₀² ε^(-1/2) dε = 2√2` and hence `∫₀² 2K ε^(-1/2) = 4√2 K`.
  have hrpowInt : (∫ ε in (0:ℝ)..2, ε ^ (-(1/2) : ℝ)) = 2 * Real.sqrt 2 := by
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
    have he : (-(1/2 : ℝ) + 1) = (1/2 : ℝ) := by ring
    rw [he, Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
    rw [sub_zero]
    ring
  have hgval : (∫ ε in (0:ℝ)..2, 2 * K * ε ^ (-(1/2) : ℝ)) = 4 * Real.sqrt 2 * K := by
    rw [intervalIntegral.integral_const_mul, hrpowInt]; ring
  rw [hgval] at hcmp
  -- Now bound `4√2 · K = 4√2 · √(22 d) ≤ 27 √d`.
  have hKval : 4 * Real.sqrt 2 * K = 4 * Real.sqrt 2 * Real.sqrt 22 * Real.sqrt d := by
    rw [hK, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 22)]; ring
  have hfinal : 4 * Real.sqrt 2 * Real.sqrt 22 * Real.sqrt d ≤ 27 * Real.sqrt d := by
    have hsd : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    have hcoef : 4 * Real.sqrt 2 * Real.sqrt 22 ≤ 27 := by
      have h2 : Real.sqrt 2 * Real.sqrt 22 = Real.sqrt 44 := by
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
      rw [mul_assoc, h2]
      -- `4 √44 ≤ 27` ⟺ `√44 ≤ 27/4` ⟺ `44 ≤ (27/4)²`.
      have h44 : Real.sqrt 44 ≤ 27 / 4 := by
        rw [show (27:ℝ)/4 = Real.sqrt ((27/4)^2) by
          rw [Real.sqrt_sq (by norm_num)]]
        apply Real.sqrt_le_sqrt; norm_num
      linarith
    exact mul_le_mul_of_nonneg_right hcoef hsd
  calc (∫ ε in (0:ℝ)..2, Real.sqrt (22 * (d:ℝ) * Real.log (4 / ε)))
      ≤ 4 * Real.sqrt 2 * K := hcmp
    _ = 4 * Real.sqrt 2 * Real.sqrt 22 * Real.sqrt d := hKval
    _ ≤ 27 * Real.sqrt d := hfinal

end StatLean.ConcentrationInequalities
