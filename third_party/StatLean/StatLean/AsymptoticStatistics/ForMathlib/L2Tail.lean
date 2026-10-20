module
public import StatLean.AsymptoticStatistics.ForMathlib.L2Asymptotics

@[expose] public section

/-!
# Tail controls from an L² approximation

Reusable Markov and uniform-integrability estimates for a family
`Wₜ = qₜ + zₜ`, where `qₜ` is `o(sₜ)` in L² and `zₜ` is dominated by
`sₜ g`.  The five declarations mirror the five estimates used in the
population log-likelihood Taylor remainder.
-/

open MeasureTheory Filter Topology Asymptotics

namespace AsymptoticStatistics.L2Utils

variable {α 𝒳 : Type*} [MeasurableSpace 𝒳]

set_option linter.unusedVariables false in
/-- Markov control: vanishing second moment makes every fixed `|W|` tail have
vanishing probability. -/
lemma l2_markov_tail_tendsto
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W : α → 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (hW_sq_zero : Tendsto (fun t => ∫ x, W t x ^ 2 ∂P) l (𝓝 0))
    (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun t => P {x | delta ≤ |W t x|}) l (𝓝 0) := by
  have hu : Tendsto
      (fun t => ENNReal.ofReal ((delta ^ 2)⁻¹ * ∫ x, W t x ^ 2 ∂P)) l (nhds 0) := by
    have ht : Tendsto (fun t => (delta ^ 2)⁻¹ * ∫ x, W t x ^ 2 ∂P) l (nhds 0) := by
      simpa using hW_sq_zero.const_mul (delta ^ 2)⁻¹
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using!
      (ENNReal.continuous_ofReal.tendsto 0).comp ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hW_mem] with t hwm
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun x => W t x ^ 2)
    (Eventually.of_forall fun _ => sq_nonneg _) hwm.integrable_sq (delta ^ 2)
  have hset : {x | delta ^ 2 ≤ W t x ^ 2} = {x | delta ≤ |W t x|} := by
    ext x
    simp only [Set.mem_setOf_eq]
    simpa [sq_abs] using (sq_le_sq₀ hdelta.le (abs_nonneg (W t x)))
  rw [hset] at hm
  have hreal : P.real {x | delta ≤ |W t x|} ≤
      (delta ^ 2)⁻¹ * ∫ x, W t x ^ 2 ∂P := by
    have hd2 : 0 < delta ^ 2 := sq_pos_of_pos hdelta
    calc
      P.real {x | delta ≤ |W t x|} ≤
          (∫ x, W t x ^ 2 ∂P) / delta ^ 2 :=
        (le_div_iff₀ hd2).2 (by simpa [mul_comm] using hm)
      _ = (delta ^ 2)⁻¹ * ∫ x, W t x ^ 2 ∂P := by rw [div_eq_inv_mul]
  rw [← ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal]
  · simpa [measureReal_def] using hreal
  · exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)

set_option linter.unusedVariables false in
/-- The square tail is `o(s²)` when `W = q + z`, the approximation error
has `o(s²)` squared norm, and `z² ≤ s² g` for an integrable envelope. -/
lemma l2_square_tail_isLittleO
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W q z : α → 𝒳 → ℝ) (s : α → ℝ) (g : 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (hq_mem : ∀ᶠ t in l, MemLp (q t) 2 P)
    (hqO : (fun t => ∫ x, q t x ^ 2 ∂P) =o[l] (fun t => s t ^ 2))
    (hg : Integrable g P)
    (hg_nonneg : ∀ᵐ x ∂P, 0 ≤ g x)
    (hs_nonneg : ∀ t, 0 ≤ s t)
    (hdecomp : ∀ t x, W t x = q t x + z t x)
    (hz_sq_le : ∀ t x, z t x ^ 2 ≤ s t ^ 2 * g x)
    (delta : ℝ) (hdelta : 0 < delta)
    (htail_prob : Tendsto (fun t => P {x | delta ≤ |W t x|}) l (𝓝 0)) :
    (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
      =o[l] (fun t => s t ^ 2) := by
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hgtail : Tendsto (fun t => ∫ x in B t, g x ∂P) l (nhds 0) := by
    apply hg.tendsto_setIntegral_nhds_zero
    simpa only [Function.comp_apply, B] using! htail_prob
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hqbd := (Asymptotics.isLittleO_iff.mp hqO) (show 0 < c / 8 by positivity)
  have hgbd := hgtail.eventually (Iio_mem_nhds (show 0 < c / 8 by positivity))
  filter_upwards [hW_mem, hq_mem, hqbd, hgbd] with t hwm hqm hqbd hgbd
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hqbd ⊢
  have hmajor : IntegrableOn
      (fun x => 2 * q t x ^ 2 + 2 * (s t ^ 2 * g x)) (B t) P :=
    ((hqm.integrable_sq.const_mul 2).add
      ((hg.const_mul (s t ^ 2)).const_mul 2)).integrableOn
  have hle : ∫ x in B t, W t x ^ 2 ∂P ≤
      2 * (∫ x, q t x ^ 2 ∂P) + 2 * (s t ^ 2 * ∫ x in B t, g x ∂P) := by
    calc
      ∫ x in B t, W t x ^ 2 ∂P ≤
          ∫ x in B t, 2 * q t x ^ 2 + 2 * (s t ^ 2 * g x) ∂P := by
        refine setIntegral_mono_ae_restrict hwm.integrable_sq.integrableOn hmajor ?_
        filter_upwards with x
        calc
          W t x ^ 2 = (q t x + z t x) ^ 2 := by rw [hdecomp]
          _ ≤ 2 * q t x ^ 2 + 2 * z t x ^ 2 := sq_add_le_two_mul_sq _ _
          _ ≤ 2 * q t x ^ 2 + 2 * (s t ^ 2 * g x) := by
            gcongr
            exact hz_sq_le t x
      _ = 2 * (∫ x in B t, q t x ^ 2 ∂P) +
          2 * (s t ^ 2 * ∫ x in B t, g x ∂P) := by
        have h₁ : IntegrableOn (fun x => 2 * q t x ^ 2) (B t) P :=
          (hqm.integrable_sq.const_mul 2).integrableOn
        have h₂ : IntegrableOn (fun x => 2 * (s t ^ 2 * g x)) (B t) P :=
          ((hg.const_mul (s t ^ 2)).const_mul 2).integrableOn
        rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul,
          integral_const_mul]
      _ ≤ 2 * (∫ x, q t x ^ 2 ∂P) +
          2 * (s t ^ 2 * ∫ x in B t, g x ∂P) := by
        have hqle := setIntegral_le_integral (s := B t) hqm.integrable_sq
          (Eventually.of_forall fun _ => sq_nonneg _)
        nlinarith
  have hprod : s t ^ 2 * ∫ x in B t, g x ∂P ≤ s t ^ 2 * (c / 8) :=
    mul_le_mul_of_nonneg_left (le_of_lt hgbd) (sq_nonneg _)
  exact hle.trans (by nlinarith [sq_nonneg (s t), hs_nonneg t])

/-- A positive threshold converts an `o(s²)` square-tail bound into the
same rate for the real-valued tail probability. -/
lemma l2_tail_measureReal_isLittleO
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W : α → 𝒳 → ℝ) (s : α → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (delta : ℝ) (hdelta : 0 < delta)
    (hW_tail : (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
      =o[l] (fun t => s t ^ 2)) :
    (fun t => P.real {x | delta ≤ |W t x|}) =o[l] (fun t => s t ^ 2) := by
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hBmeas (t : α) : MeasurableSet (B t) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hW_meas t))
  have hbound : (fun t => P.real (B t)) =O[l]
      (fun t => ∫ x in B t, W t x ^ 2 ∂P) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(delta ^ 2)⁻¹, ?_⟩
    filter_upwards [hW_mem] with t hwm
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    have hm : delta ^ 2 * P.real (B t) ≤ ∫ x in B t, W t x ^ 2 ∂P := by
      have hcint : IntegrableOn (fun _ : 𝒳 => delta ^ 2) (B t) P :=
        (integrable_const (delta ^ 2)).integrableOn
      have hwint : IntegrableOn (fun x => W t x ^ 2) (B t) P :=
        hwm.integrable_sq.integrableOn
      have hpt : ∀ᵐ x ∂P.restrict (B t), delta ^ 2 ≤ W t x ^ 2 := by
        filter_upwards [ae_restrict_mem (hBmeas t)] with x hx
        exact ((sq_le_sq₀ hdelta.le (abs_nonneg _)).2 hx).trans_eq (sq_abs _)
      have := setIntegral_mono_ae_restrict hcint hwint hpt
      simpa [setIntegral_const, smul_eq_mul, mul_comm] using this
    have hd2 : 0 < delta ^ 2 := sq_pos_of_pos hdelta
    calc
      P.real (B t) ≤ (delta ^ 2)⁻¹ * (∫ x in B t, W t x ^ 2 ∂P) := by
        rw [← div_eq_inv_mul]
        exact (le_div_iff₀ hd2).2 (by simpa [mul_comm] using hm)
      _ = _ := rfl
  apply hbound.trans_isLittleO
  simpa only [B] using hW_tail

set_option linter.unusedVariables false in
/-- L² uniform integrability of an envelope, combined with an `o(s²)` tail
probability, controls `s · ∫_tail |m|` at order `o(s²)`. -/
lemma l2_envelope_tail_isLittleO
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W : α → 𝒳 → ℝ) (s : α → ℝ) (m : 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hm : MemLp m 2 P)
    (hs_nonneg : ∀ t, 0 ≤ s t)
    (delta : ℝ) (hdelta : 0 < delta)
    (htail_prob : Tendsto (fun t => P {x | delta ≤ |W t x|}) l (𝓝 0))
    (htail_rate : (fun t => P.real {x | delta ≤ |W t x|})
      =o[l] (fun t => s t ^ 2)) :
    (fun t => s t * ∫ x in {x | delta ≤ |W t x|}, |m x| ∂P)
      =o[l] (fun t => s t ^ 2) := by
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hBmeas (t : α) : MeasurableSet (B t) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hW_meas t))
  let A : α → ℝ := fun t => ∫ x in B t, |m x| ^ 2 ∂P
  let Q : α → ℝ := fun t => P.real (B t)
  have hm2 : Integrable (fun x => |m x| ^ 2) P := by
    simpa [sq_abs] using hm.integrable_sq
  have hA0 : Tendsto A l (nhds 0) :=
    hm2.tendsto_setIntegral_nhds_zero (by
      simpa only [Function.comp_apply, B] using! htail_prob)
  have hAO : A =o[l] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hA0
  have hQO : Q =o[l] (fun t => s t ^ 2) := by
    simpa only [Q, B] using htail_rate
  have hAs : (fun t => Real.sqrt (A t)) =o[l] (fun _ => (1 : ℝ)) := by
    convert hAO.sqrt (Eventually.of_forall fun _ => zero_le_one) using 1
    simp
  have hQs : (fun t => Real.sqrt (Q t)) =o[l] s := by
    convert hQO.sqrt (Eventually.of_forall fun t => sq_nonneg (s t)) using 1
    funext t
    exact (Real.sqrt_sq (hs_nonneg t)).symm
  have hprod : (fun t => Real.sqrt (A t) * Real.sqrt (Q t)) =o[l] s := by
    convert! hAs.mul hQs using 1
    simp
  have hcross : (fun t => ∫ x in B t, |m x| ∂P) =O[l]
      (fun t => Real.sqrt (A t) * Real.sqrt (Q t)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, Eventually.of_forall fun t => ?_⟩
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    let a : 𝒳 → ℝ := (B t).indicator fun x => |m x|
    let b : 𝒳 → ℝ := (B t).indicator fun _ => 1
    have ha : MemLp a 2 P := hm.norm.indicator (hBmeas t)
    have hb : MemLp b 2 P := memLp_indicator_const 2 (hBmeas t) 1
      (Or.inr (measure_ne_top P _))
    have hcs := abs_integral_mul_le_sqrt_integral_sq P ha hb
    have hab : (∫ x, a x * b x ∂P) = ∫ x in B t, |m x| ∂P := by
      rw [← integral_indicator (hBmeas t)]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ B t <;> simp [a, b, hx]
    have ha2 : (∫ x, a x ^ 2 ∂P) = A t := by
      change (∫ x, a x ^ 2 ∂P) = ∫ x in B t, |m x| ^ 2 ∂P
      rw [← integral_indicator (hBmeas t)]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ B t <;> simp [a, hx]
    have hb2 : (∫ x, b x ^ 2 ∂P) = Q t := by
      change (∫ x, b x ^ 2 ∂P) = P.real (B t)
      rw [show (fun x => b x ^ 2) = (B t).indicator (fun _ => (1 : ℝ)) by
        funext x
        by_cases hx : x ∈ B t <;> simp [b, hx]]
      simpa only [Pi.one_apply] using! (integral_indicator_one (μ := P) (hBmeas t))
    simpa [hab, ha2, hb2] using hcs
  have hcO := hcross.trans_isLittleO hprod
  have hmul := (Asymptotics.isBigO_refl s l).mul_isLittleO hcO
  convert! hmul using 1
  funext t
  ring

/-- On a tail above a positive threshold, the first absolute moment is
bounded by a constant times the second moment. -/
lemma l2_abs_tail_isLittleO
    (l : Filter α) (P : Measure 𝒳)
    (W : α → 𝒳 → ℝ) (s : α → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (delta : ℝ) (hdelta : 0 < delta)
    (hW_tail : (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
      =o[l] (fun t => s t ^ 2)) :
    (fun t => ∫ x in {x | delta ≤ |W t x|}, |W t x| ∂P)
      =o[l] (fun t => s t ^ 2) := by
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hBmeas (t : α) : MeasurableSet (B t) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hW_meas t))
  have hbound : (fun t => ∫ x in B t, |W t x| ∂P) =O[l]
      (fun t => ∫ x in B t, W t x ^ 2 ∂P) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨delta⁻¹, ?_⟩
    filter_upwards [hW_mem] with t hwm
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    have hpoint : ∀ᵐ x ∂P.restrict (B t), |W t x| ≤ delta⁻¹ * W t x ^ 2 := by
      filter_upwards [ae_restrict_mem (hBmeas t)] with x hx
      have habs := abs_nonneg (W t x)
      have hmul := mul_le_mul_of_nonneg_right hx habs
      rw [← sq_abs]
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hdelta).2 (by nlinarith)
    have habs_int : IntegrableOn (fun x => |W t x|) (B t) P :=
      Integrable.mono' (hwm.integrable_sq.const_mul delta⁻¹).integrableOn
        ((continuous_abs.measurable.comp (hW_meas t)).aestronglyMeasurable.restrict) (by
          filter_upwards [hpoint] with x hx
          simpa only [Real.norm_eq_abs, abs_abs] using hx)
    have hle : ∫ x in B t, |W t x| ∂P ≤
        ∫ x in B t, delta⁻¹ * W t x ^ 2 ∂P := by
      refine setIntegral_mono_ae_restrict
        habs_int
        (hwm.integrable_sq.const_mul delta⁻¹).integrableOn ?_
      exact hpoint
    rw [integral_const_mul] at hle
    exact hle
  apply hbound.trans_isLittleO
  simpa only [B] using hW_tail

/-- The complete five-part L² tail package used by the integrated logarithmic
Taylor remainder.  Every clause is explicit so downstream users do not hide
analytic debt behind a provider predicate. -/
lemma l2_tail_controls_of_approx
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W q z : α → 𝒳 → ℝ) (s : α → ℝ) (g : 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (hW_sq_zero : Tendsto (fun t => ∫ x, W t x ^ 2 ∂P) l (𝓝 0))
    (hq_mem : ∀ᶠ t in l, MemLp (q t) 2 P)
    (hqO : (fun t => ∫ x, q t x ^ 2 ∂P) =o[l] (fun t => s t ^ 2))
    (hg : Integrable g P) (hg_nonneg : ∀ᵐ x ∂P, 0 ≤ g x)
    (hs_nonneg : ∀ t, 0 ≤ s t)
    (hdecomp : ∀ t x, W t x = q t x + z t x)
    (hz_sq_le : ∀ t x, z t x ^ 2 ≤ s t ^ 2 * g x)
    (m : 𝒳 → ℝ) (hm : MemLp m 2 P)
    (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun t => P {x | delta ≤ |W t x|}) l (𝓝 0) ∧
      (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
        =o[l] (fun t => s t ^ 2) ∧
      (fun t => P.real {x | delta ≤ |W t x|}) =o[l] (fun t => s t ^ 2) ∧
      (fun t => s t * ∫ x in {x | delta ≤ |W t x|}, |m x| ∂P)
        =o[l] (fun t => s t ^ 2) ∧
      (fun t => ∫ x in {x | delta ≤ |W t x|}, |W t x| ∂P)
        =o[l] (fun t => s t ^ 2) := by
  have hprob := l2_markov_tail_tendsto l P W hW_meas hW_mem hW_sq_zero delta hdelta
  have hsq := l2_square_tail_isLittleO l P W q z s g hW_meas hW_mem hq_mem hqO hg
    hg_nonneg hs_nonneg hdecomp hz_sq_le delta hdelta hprob
  have hreal := l2_tail_measureReal_isLittleO l P W s hW_meas hW_mem delta hdelta hsq
  have henv := l2_envelope_tail_isLittleO l P W s m hW_meas hm hs_nonneg delta hdelta
    hprob hreal
  have habs := l2_abs_tail_isLittleO l P W s hW_meas hW_mem delta hdelta hsq
  exact ⟨hprob, hsq, hreal, henv, habs⟩

end AsymptoticStatistics.L2Utils
