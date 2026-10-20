module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Tail-to-expectation conversion for Gaussian-type tails

Layer-cake analytics converting a high-probability bound into an expectation
bound: if a nonnegative random variable $Z$ satisfies
$$ \mathbb{P}(Z > a + b u) \;\le\; 2 e^{-u^2} \qquad \text{for all } u \ge 0, $$
then
$$ \mathbb{E}[Z] \;\le\; a + \sqrt{\pi}\, b. $$
This is the analytic step from the tail form (8.15) of Dudley's inequality
back to the expectation form (8.14), and the last step of the generic
chaining bound (Theorem 8.5.2). Pure real analysis and measure theory; no
process content.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, the Remark 8.1.6 ⇒ Theorem 8.1.5 step (and
§8.5.2, last step of Theorem 8.5.2); the Gaussian tail estimates are §2.5
folklore (cf. Proposition 2.1.2).

**Proof formalization notes.** The constant is exact:
$\int_0^\infty 2 e^{-u^2}\,du = \sqrt{\pi}$ (half of Mathlib's
`integral_gaussian` by evenness), so `E Z ≤ a + √π·b` with `√π` a frozen
symbolic constant (no numeral rounding). The layer-cake step uses
`lintegral_eq_lintegral_meas_lt` on the `ℝ≥0∞` side; the Bochner form
`integral_le_of_tail_le` DERIVES integrability of `Z` from the finiteness of
the lintegral bound (never hypothesizes it). The auxiliary
`integral_exp_neg_mul_sq_Ioi_le` (tail of the Gaussian integral,
$\int_a^\infty e^{-\beta s^2} ds \le e^{-\beta a^2}/(2\beta a)$ via the
$s/a \ge 1$ majorization) is exported for the split-point optimization in
`Chaining/PsiTwoMaximal.lean`. Named-sorry fallback of this work item:
`integral_le_of_tail_le` (the Bochner wrapper), with the `∫⁻` version
`lintegral_ofReal_le_of_tail_le` proved.

**Bibliographic comments.** The layer-cake (Cavalieri) representation of the
expectation is classical measure theory; its use to integrate chaining tail
bounds is standard since Dudley (1967) and is presented in Talagrand, *Upper
and Lower Bounds for Stochastic Processes*, Springer 2014, §2.2. Gaussian
tail estimates of the form used here go back to Laplace.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Gaussian tail integral bound
`∫_a^∞ exp(−β s²) ds ≤ exp(−β a²)/(2 β a)`, via the `s/a ≥ 1` majorization
and the exact antiderivative of `s · exp(−β s²)`. -/
lemma integral_exp_neg_mul_sq_Ioi_le {a β : ℝ}
    -- LEAN-ONLY: positive split point, so the majorization s/a ≥ 1 applies
    (ha : 0 < a)
    -- LEAN-ONLY: positive Gaussian rate; degenerate β ≤ 0 has no finite tail
    (hβ : 0 < β) :
    ∫ x in Set.Ioi a, Real.exp (-β * x ^ 2)
      ≤ Real.exp (-β * a ^ 2) / (2 * β * a) := by
  -- antiderivative `g s = -(2β)⁻¹ exp(-β s²)` with derivative `s·exp(-β s²)`
  have hderiv : ∀ x ∈ Set.Ici a,
      HasDerivAt (fun s : ℝ => -(2 * β)⁻¹ * Real.exp (-β * s ^ 2))
        (x * Real.exp (-β * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => -β * s ^ 2) (-β * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (-β)
    have h2 := (h1.exp).const_mul (-(2 * β)⁻¹)
    convert! h2 using 1
    field_simp
  have htend : Filter.Tendsto (fun s : ℝ => -(2 * β)⁻¹ * Real.exp (-β * s ^ 2))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => -β * s ^ 2) Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) (Filter.tendsto_pow_atTop two_ne_zero)
    have h2 : Filter.Tendsto (fun s : ℝ => Real.exp (-β * s ^ 2)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul (-(2 * β)⁻¹)
  have hgpos : ∀ x ∈ Set.Ioi a, 0 ≤ x * Real.exp (-β * x ^ 2) := fun x hx =>
    mul_nonneg (le_of_lt (lt_trans ha (Set.mem_Ioi.mp hx))) (Real.exp_pos _).le
  have hInt_x : MeasureTheory.IntegrableOn
      (fun x => x * Real.exp (-β * x ^ 2)) (Set.Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hgpos htend
  have hInt_exp : MeasureTheory.IntegrableOn
      (fun x => Real.exp (-β * x ^ 2)) (Set.Ioi a) :=
    (integrable_exp_neg_mul_sq hβ).integrableOn
  have hval : ∫ x in Set.Ioi a, x * Real.exp (-β * x ^ 2)
      = (2 * β)⁻¹ * Real.exp (-β * a ^ 2) := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hgpos htend]; ring
  have hmono : ∫ x in Set.Ioi a, Real.exp (-β * x ^ 2)
      ≤ ∫ x in Set.Ioi a, a⁻¹ * (x * Real.exp (-β * x ^ 2)) := by
    apply MeasureTheory.setIntegral_mono_on hInt_exp (hInt_x.const_mul a⁻¹) measurableSet_Ioi
    intro x hx
    have hx' : a < x := Set.mem_Ioi.mp hx
    have hxa : 1 ≤ a⁻¹ * x := by rw [inv_mul_eq_div, le_div_iff₀ ha]; linarith
    calc Real.exp (-β * x ^ 2) = 1 * Real.exp (-β * x ^ 2) := (one_mul _).symm
      _ ≤ a⁻¹ * x * Real.exp (-β * x ^ 2) :=
          mul_le_mul_of_nonneg_right hxa (Real.exp_pos _).le
      _ = a⁻¹ * (x * Real.exp (-β * x ^ 2)) := by ring
  rw [MeasureTheory.integral_const_mul, hval] at hmono
  refine hmono.trans_eq ?_
  rw [eq_div_iff (by positivity)]
  field_simp

/-- Exact half-Gaussian integral `∫_0^∞ 2 exp(−u²) du = √π` (halved
`integral_gaussian` by evenness). -/
lemma integral_exp_neg_sq_Ioi_le_sqrt_pi :
    ∫ u in Set.Ioi (0 : ℝ), 2 * Real.exp (-u ^ 2) = Real.sqrt Real.pi := by
  rw [MeasureTheory.integral_const_mul]
  have h : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2)) = Real.sqrt Real.pi / 2 := by
    have hg := integral_gaussian_Ioi 1
    simpa [neg_one_mul, div_one] using hg
  rw [h]; ring

/-- **Tail-to-expectation, lintegral form** (HDP §8.1, the Remark 8.1.6 ⇒
Theorem 8.1.5 step): a Gaussian-type tail at thresholds `a + b·u` integrates
to `∫⁻ Z ≤ a + √π·b`, via the layer-cake formula
`lintegral_eq_lintegral_meas_lt` and the substitution `s = a + b u`. -/
theorem lintegral_ofReal_le_of_tail_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability for the layer-cake formula
    (hZm : AEMeasurable Z μ)
    -- LEAN-ONLY: nonnegativity of the supremand being integrated; HDP §8.1
    (hZ0 : 0 ≤ᵐ[μ] Z)
    {a b : ℝ}
    -- LEAN-ONLY: nonnegative threshold offsets (true at every call site)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    -- USER-INPUT: Gaussian-type high-probability bound; HDP §8.1, Eq (8.15)
    (htail : ∀ u : ℝ, 0 ≤ u →
      μ {ω | a + b * u < Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2))) :
    ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ
      ≤ ENNReal.ofReal (a + Real.sqrt Real.pi * b) := by
  rw [MeasureTheory.lintegral_eq_lintegral_meas_lt μ hZ0 hZm,
      ← Set.Ioc_union_Ioi_eq_Ioi ha,
      MeasureTheory.lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
  -- Part 1: on `(0, a]` bound each slice measure by 1.
  have hpart1 : ∫⁻ t in Set.Ioc 0 a, μ {ω | t < Z ω} ≤ ENNReal.ofReal a := by
    calc ∫⁻ t in Set.Ioc 0 a, μ {ω | t < Z ω}
        ≤ ∫⁻ _ in Set.Ioc 0 a, 1 :=
          lintegral_mono fun t => (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      _ = volume (Set.Ioc 0 a) := MeasureTheory.setLIntegral_one _
      _ = ENNReal.ofReal a := by rw [Real.volume_Ioc, sub_zero]
  -- Part 2: on `(a, ∞)` integrate the Gaussian tail.
  have hpart2 : ∫⁻ t in Set.Ioi a, μ {ω | t < Z ω}
      ≤ ENNReal.ofReal (Real.sqrt Real.pi * b) := by
    rcases hb.eq_or_lt with hb0 | hbpos
    · -- degenerate scale `b = 0`: the slice measure vanishes past `a`
      have hbz : b = 0 := hb0.symm
      subst hbz
      have hazero : μ {ω | a < Z ω} = 0 := by
        have hle : ∀ u : ℝ, 0 ≤ u →
            μ {ω | a < Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
          intro u hu; simpa using htail u hu
        have h1 : Filter.Tendsto (fun u : ℝ => -u ^ 2) Filter.atTop Filter.atBot := by
          simpa using Filter.Tendsto.const_mul_atTop_of_neg (show (-1 : ℝ) < 0 by norm_num)
            (Filter.tendsto_pow_atTop (two_ne_zero))
        have htends : Filter.Tendsto (fun u : ℝ => ENNReal.ofReal (2 * Real.exp (-u ^ 2)))
            Filter.atTop (nhds 0) := by
          rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
          apply ENNReal.tendsto_ofReal
          have h2 : Filter.Tendsto (fun u : ℝ => Real.exp (-u ^ 2)) Filter.atTop (nhds 0) :=
            Real.tendsto_exp_atBot.comp h1
          simpa using h2.const_mul 2
        exact le_antisymm (ge_of_tendsto htends
          (Filter.eventually_atTop.mpr ⟨0, hle⟩)) (zero_le)
      have hzero_on : ∀ t ∈ Set.Ioi a, μ {ω | t < Z ω} = 0 := fun t ht =>
        le_antisymm ((measure_mono fun ω hω =>
          lt_trans (Set.mem_Ioi.mp ht) hω).trans hazero.le) (zero_le)
      have hae : (fun t => μ {ω | t < Z ω}) =ᵐ[volume.restrict (Set.Ioi a)] 0 :=
        (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall fun t ht => by simpa using hzero_on t ht)
      rw [MeasureTheory.lintegral_congr_ae hae]; simp
    · -- nondegenerate `b > 0`: substitute `t = a + b·u`
      have hbne : b ≠ 0 := hbpos.ne'
      have hbound : ∀ t ∈ Set.Ioi a,
          μ {ω | t < Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-((t - a) / b) ^ 2)) := by
        intro t ht
        have ht' : a < t := Set.mem_Ioi.mp ht
        have hu : 0 ≤ (t - a) / b := div_nonneg (by linarith) hbpos.le
        have hht := htail ((t - a) / b) hu
        rwa [show a + b * ((t - a) / b) = t by field_simp; ring] at hht
      have hψ_int : MeasureTheory.Integrable (fun s : ℝ => 2 * Real.exp (-(s / b) ^ 2)) := by
        have hβ' : (0 : ℝ) < 1 / b ^ 2 := by positivity
        have harg : ∀ s : ℝ, -(s / b) ^ 2 = -(1 / b ^ 2) * s ^ 2 := fun s => by
          rw [div_pow]; ring
        have heq : (fun s : ℝ => 2 * Real.exp (-(s / b) ^ 2))
            = (fun s : ℝ => 2 * Real.exp (-(1 / b ^ 2) * s ^ 2)) := by
          funext s; rw [harg]
        rw [heq]
        exact (integrable_exp_neg_mul_sq hβ').const_mul 2
      have hφ_int : MeasureTheory.IntegrableOn
          (fun t : ℝ => 2 * Real.exp (-((t - a) / b) ^ 2)) (Set.Ioi a) :=
        (hψ_int.comp_sub_right a).integrableOn
      have hφ_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi a)]
          fun t : ℝ => 2 * Real.exp (-((t - a) / b) ^ 2) :=
        Filter.Eventually.of_forall fun t => by positivity
      have hval : (∫ t in Set.Ioi a, 2 * Real.exp (-((t - a) / b) ^ 2))
          = b * Real.sqrt Real.pi := by
        have step_trans : (∫ t in Set.Ioi a, 2 * Real.exp (-((t - a) / b) ^ 2))
            = ∫ s in Set.Ioi (0 : ℝ), 2 * Real.exp (-(s / b) ^ 2) := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
              ← MeasureTheory.integral_indicator measurableSet_Ioi]
          have hind : (Set.Ioi a).indicator (fun t => 2 * Real.exp (-((t - a) / b) ^ 2))
              = fun t => (Set.Ioi (0 : ℝ)).indicator
                  (fun s => 2 * Real.exp (-(s / b) ^ 2)) (t - a) := by
            funext t
            by_cases ht : t ∈ Set.Ioi a
            · have ht0 : t - a ∈ Set.Ioi (0 : ℝ) := by
                simp only [Set.mem_Ioi] at ht ⊢; linarith
              rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht0]
            · have ht0 : t - a ∉ Set.Ioi (0 : ℝ) := by
                simp only [Set.mem_Ioi] at ht ⊢; linarith
              rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht0]
          rw [hind]
          exact integral_sub_right_eq_self _ a
        rw [step_trans]
        have hb0inv : (0 : ℝ) < b⁻¹ := inv_pos.mpr hbpos
        have hcomp := integral_comp_mul_left_Ioi (fun u => 2 * Real.exp (-u ^ 2)) 0 hb0inv
        simp only [mul_zero, inv_inv, smul_eq_mul] at hcomp
        rw [integral_exp_neg_sq_Ioi_le_sqrt_pi] at hcomp
        rw [← hcomp]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        simp only [div_eq_inv_mul]
      calc ∫⁻ t in Set.Ioi a, μ {ω | t < Z ω}
          ≤ ∫⁻ t in Set.Ioi a, ENNReal.ofReal (2 * Real.exp (-((t - a) / b) ^ 2)) := by
            refine MeasureTheory.lintegral_mono_ae ?_
            exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
              (Filter.Eventually.of_forall fun t ht => hbound t ht)
        _ = ENNReal.ofReal (∫ t in Set.Ioi a, 2 * Real.exp (-((t - a) / b) ^ 2)) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφ_int hφ_nn).symm
        _ = ENNReal.ofReal (Real.sqrt Real.pi * b) := by rw [hval, mul_comm]
  rw [ENNReal.ofReal_add ha (mul_nonneg (Real.sqrt_nonneg _) hb)]
  exact add_le_add hpart1 hpart2

/-- **Tail-to-expectation, Bochner form**: `E Z ≤ a + √π·b`. Integrability of
`Z` is DERIVED from the finite lintegral bound of
`lintegral_ofReal_le_of_tail_le` — not hypothesized. -/
theorem integral_le_of_tail_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability for the layer-cake formula
    (hZm : AEMeasurable Z μ)
    -- LEAN-ONLY: nonnegativity of the supremand being integrated; HDP §8.1
    (hZ0 : 0 ≤ᵐ[μ] Z)
    {a b : ℝ}
    -- LEAN-ONLY: nonnegative threshold offsets (true at every call site)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    -- USER-INPUT: Gaussian-type high-probability bound; HDP §8.1, Eq (8.15)
    (htail : ∀ u : ℝ, 0 ≤ u →
      μ {ω | a + b * u < Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2))) :
    ∫ ω, Z ω ∂μ ≤ a + Real.sqrt Real.pi * b := by
  have hlint := lintegral_ofReal_le_of_tail_le hZm hZ0 ha hb htail
  rw [integral_eq_lintegral_of_nonneg_ae hZ0 hZm.aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ).toReal
      ≤ (ENNReal.ofReal (a + Real.sqrt Real.pi * b)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = a + Real.sqrt Real.pi * b :=
        ENNReal.toReal_ofReal (add_nonneg ha (mul_nonneg (Real.sqrt_nonneg _) hb))

end StatLean.ConcentrationInequalities
