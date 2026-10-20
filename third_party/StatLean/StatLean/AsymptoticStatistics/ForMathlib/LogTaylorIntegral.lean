module
public import StatLean.AsymptoticStatistics.ForMathlib.L2Tail
public import StatLean.AsymptoticStatistics.ForMathlib.LogTaylor

@[expose] public section

/-! # Integrated logarithmic Taylor remainders -/

open MeasureTheory Filter Topology Asymptotics

namespace AsymptoticStatistics.ForMathlib

/-- Integrate the logarithmic Taylor remainder by splitting into a small
`|W|` region and its complement.  The three tail hypotheses are stated in
full: square tail, Lipschitz-envelope tail, and absolute first-moment tail.
There is no packaged/provider tail predicate in this interface. -/
lemma integral_logTaylorRemainder_isLittleO
    {α 𝒳 : Type*} [MeasurableSpace 𝒳]
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W L : α → 𝒳 → ℝ) (s : α → ℝ) (m : 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (hL_int : ∀ᶠ t in l, Integrable (L t) P)
    (hm : MemLp m 2 P)
    (hs_nonneg : ∀ t, 0 ≤ s t)
    (hL_bound : ∀ᶠ t in l, ∀ x, |L t x| ≤ s t * |m x|)
    (hTaylor : ∀ᶠ t in l, ∀ᵐ x ∂P, |W t x| < 1 →
      L t x - W t x + W t x ^ 2 / 4 =
        W t x ^ 2 / 2 * logTaylorRemainder (W t x))
    (hW_sq : (fun t => ∫ x, W t x ^ 2 ∂P) =O[l] (fun t => s t ^ 2))
    (hW_tail : ∀ delta, 0 < delta →
      (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
        =o[l] (fun t => s t ^ 2))
    (hm_tail : ∀ delta, 0 < delta →
      (fun t => s t * ∫ x in {x | delta ≤ |W t x|}, |m x| ∂P)
        =o[l] (fun t => s t ^ 2))
    (hW_abs_tail : ∀ delta, 0 < delta →
      (fun t => ∫ x in {x | delta ≤ |W t x|}, |W t x| ∂P)
        =o[l] (fun t => s t ^ 2)) :
    (fun t => ∫ x, (L t x - W t x + W t x ^ 2 / 4) ∂P)
      =o[l] (fun t => s t ^ 2) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hW_sq
  let D : ℝ := |K| + 1
  have hD : 0 < D := add_pos_of_nonneg_of_pos (abs_nonneg K) one_pos
  have hW_sq_bd : ∀ᶠ t in l, ∫ x, W t x ^ 2 ∂P ≤ D * s t ^ 2 := by
    filter_upwards [hK] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (show K ≤ D by dsimp only [D]; linarith [le_abs_self K]) (sq_nonneg _))
  let eta : ℝ := c / (16 * D)
  have heta : 0 < eta := div_pos hc (mul_pos (by norm_num) hD)
  obtain ⟨d, hd, hrem⟩ :=
    Metric.tendsto_nhds_nhds.mp logTaylorRemainder_tendsto_zero eta heta
  let delta : ℝ := min d 1
  have hdelta : 0 < delta := lt_min hd one_pos
  have hdelta_le : delta ≤ 1 := min_le_right _ _
  have hrem_small {w : ℝ} (hw : |w| < delta) :
      |logTaylorRemainder w| < eta := by
    have hw' : dist w 0 < d := by
      simpa [Real.dist_eq] using hw.trans_le (min_le_left d 1)
    simpa [Real.dist_eq] using hrem hw'
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hB_meas (t : α) : MeasurableSet (B t) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hW_meas t))
  have htail_sq := (Asymptotics.isLittleO_iff.mp (hW_tail delta hdelta))
    (show 0 < c / 16 by positivity)
  have htail_m := (Asymptotics.isLittleO_iff.mp (hm_tail delta hdelta))
    (show 0 < c / 16 by positivity)
  have htail_abs := (Asymptotics.isLittleO_iff.mp (hW_abs_tail delta hdelta))
    (show 0 < c / 16 by positivity)
  have hm_abs : Integrable (fun x => |m x|) P :=
    (hm.integrable one_le_two).abs
  filter_upwards [hW_sq_bd, htail_sq, htail_m, htail_abs, hW_mem,
    hL_int, hL_bound, hTaylor] with t hsq htsq htm htabs hwm hli hlb htaylor
  let Bad : 𝒳 → ℝ := fun x => (B t).indicator (fun x =>
    s t * |m x| + |W t x| + W t x ^ 2 / 4) x
  let G : 𝒳 → ℝ := fun x => eta / 2 * W t x ^ 2 + Bad x
  have hpoint : ∀ᵐ x ∂P,
      |L t x - W t x + W t x ^ 2 / 4| ≤ G x := by
    filter_upwards [htaylor] with x htx
    dsimp only [G, Bad]
    by_cases hx : x ∈ B t
    · rw [Set.indicator_of_mem hx]
      have hetaW : 0 ≤ eta / 2 * W t x ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      calc
        |L t x - W t x + W t x ^ 2 / 4| ≤
            |L t x| + |W t x| + W t x ^ 2 / 4 := by
          calc
            |L t x - W t x + W t x ^ 2 / 4| ≤
                |L t x - W t x| + |W t x ^ 2 / 4| := abs_add_le _ _
            _ ≤ (|L t x| + |W t x|) + W t x ^ 2 / 4 := by
              gcongr
              · simpa [sub_eq_add_neg] using abs_add_le (L t x) (-W t x)
              · rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
            _ = |L t x| + |W t x| + W t x ^ 2 / 4 := by ring
        _ ≤ eta / 2 * W t x ^ 2 +
            (s t * |m x| + |W t x| + W t x ^ 2 / 4) := by
          linarith [hlb x]
    · rw [Set.indicator_of_notMem hx, add_zero]
      have hw : |W t x| < delta := lt_of_not_ge hx
      have hexact : L t x - W t x + W t x ^ 2 / 4 =
          W t x ^ 2 / 2 * logTaylorRemainder (W t x) := by
        exact htx (hw.trans_le hdelta_le)
      have hR : |logTaylorRemainder (W t x)| ≤ eta := (hrem_small hw).le
      rw [hexact, abs_mul,
        abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
      calc
        W t x ^ 2 / 2 * |logTaylorRemainder (W t x)| ≤
            W t x ^ 2 / 2 * eta :=
          mul_le_mul_of_nonneg_left hR
            (div_nonneg (sq_nonneg _) (by norm_num))
        _ = eta / 2 * W t x ^ 2 := by ring
  have hw : Integrable (W t) P := hwm.integrable one_le_two
  have hw_abs : Integrable (fun x => |W t x|) P := hw.abs
  have hw_sq : Integrable (fun x => W t x ^ 2) P := hwm.integrable_sq
  have hquarter : Integrable (fun x => W t x ^ 2 / 4) P := by
    simpa [div_eq_mul_inv, mul_comm] using hw_sq.const_mul (4 : ℝ)⁻¹
  have htarget : Integrable (fun x => L t x - W t x + W t x ^ 2 / 4) P :=
    (hli.sub hw).add hquarter
  have htarget_abs : Integrable
      (fun x => |L t x - W t x + W t x ^ 2 / 4|) P := by
    simpa only [Real.norm_eq_abs] using htarget.norm
  have hlocal_int : Integrable (fun x => eta / 2 * W t x ^ 2) P :=
    hw_sq.const_mul (eta / 2)
  have henv_int : Integrable (fun x => s t * |m x|) P :=
    hm_abs.const_mul (s t)
  have hbad_int : Integrable Bad P :=
    ((henv_int.add hw_abs).add hquarter).indicator (hB_meas t)
  have hG_int : Integrable G P := hlocal_int.add hbad_int
  have hmain : |∫ x, (L t x - W t x + W t x ^ 2 / 4) ∂P| ≤
      eta / 2 * ∫ x, W t x ^ 2 ∂P +
        s t * ∫ x in B t, |m x| ∂P +
        ∫ x in B t, |W t x| ∂P +
        (1 / 4 : ℝ) * ∫ x in B t, W t x ^ 2 ∂P := by
    calc
      |∫ x, (L t x - W t x + W t x ^ 2 / 4) ∂P| ≤
          ∫ x, |L t x - W t x + W t x ^ 2 / 4| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x, G x ∂P := integral_mono_ae htarget_abs hG_int hpoint
      _ = eta / 2 * ∫ x, W t x ^ 2 ∂P +
          s t * ∫ x in B t, |m x| ∂P +
          ∫ x in B t, |W t x| ∂P +
          (1 / 4 : ℝ) * ∫ x in B t, W t x ^ 2 ∂P := by
        dsimp only [G, Bad]
        rw [integral_add hlocal_int hbad_int, integral_const_mul,
          integral_indicator (hB_meas t)]
        have hi₁ : IntegrableOn (fun x => s t * |m x|) (B t) P :=
          henv_int.integrableOn
        have hi₂ : IntegrableOn (fun x => |W t x|) (B t) P :=
          hw_abs.integrableOn
        have hi₃ : IntegrableOn (fun x => W t x ^ 2 / 4) (B t) P :=
          hquarter.integrableOn
        have hform : (fun x => s t * |m x| + |W t x| + W t x ^ 2 / 4) =
            fun x => s t * |m x| + (|W t x| + W t x ^ 2 / 4) := by
          funext x
          ring
        have hsplit₂₃ : (∫ x in B t, |W t x| + W t x ^ 2 / 4 ∂P) =
            (∫ x in B t, |W t x| ∂P) + ∫ x in B t, W t x ^ 2 / 4 ∂P :=
          integral_add hi₂ hi₃
        have hsplit₁₂₃ :
            (∫ x in B t, s t * |m x| + (|W t x| + W t x ^ 2 / 4) ∂P) =
              (∫ x in B t, s t * |m x| ∂P) +
                ∫ x in B t, |W t x| + W t x ^ 2 / 4 ∂P :=
          integral_add hi₁ (hi₂.add hi₃)
        rw [hform, hsplit₁₂₃, hsplit₂₃, integral_const_mul]
        simp_rw [div_eq_mul_inv]
        rw [integral_mul_const]
        ring
  have hs : 0 ≤ s t := hs_nonneg t
  have htsq' : ∫ x in B t, W t x ^ 2 ∂P ≤ c / 16 * s t ^ 2 := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at htsq
    exact htsq
  have htm' : s t * ∫ x in B t, |m x| ∂P ≤ c / 16 * s t ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs
        (integral_nonneg fun _ => abs_nonneg _)),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at htm
    exact htm
  have htabs' : ∫ x in B t, |W t x| ∂P ≤ c / 16 * s t ^ 2 := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at htabs
    exact htabs
  have hlocal : eta / 2 * ∫ x, W t x ^ 2 ∂P ≤ c / 32 * s t ^ 2 := by
    calc
      eta / 2 * ∫ x, W t x ^ 2 ∂P ≤ eta / 2 * (D * s t ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = c / 32 * s t ^ 2 := by
        have : eta / 2 * D = c / 32 := by
          dsimp only [eta]
          field_simp [hD.ne']
          norm_num
        rw [← mul_assoc, this]
  rw [show ‖∫ x, (L t x - W t x + W t x ^ 2 / 4) ∂P‖ =
        |∫ x, (L t x - W t x + W t x ^ 2 / 4) ∂P| by rfl,
    show ‖s t ^ 2‖ = |s t ^ 2| by rfl,
    abs_of_nonneg (sq_nonneg (s t))]
  exact hmain.trans (by nlinarith [sq_nonneg (s t)])

end AsymptoticStatistics.ForMathlib
