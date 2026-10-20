module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.OuterPeeling

@[expose] public section

/-!
# Metric-space rates for M-estimators

Formalization of van der Vaart Theorem 5.52 (book pp. 75--76),
including the official erratum replacing the impossible ball supremum by the
annulus `δ / 2 < dist θ θ₀ < δ`.
-/

namespace AsymptoticStatistics.MEstimator

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology

set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false in set_option maxHeartbeats 800000 in
/-- The geometric-shell tail estimate in vdV Theorem 5.52.  This is the
analytic peeling estimate; the outer-probability theorem below packages its
eventual tail as `O_P(1)`. -/
theorem metricRate_shell_tail
    {Ω Θ Ξ : Type*} [MeasurableSpace Ω] [MetricSpace Θ] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (m : Θ → Ω → ℝ) (θ₀ : Θ)
    -- LEAN-ONLY: measurability of the criterion functions.
    (hm_meas : ∀ θ, Measurable (m θ))
    (X : ℕ → Ξ → Ω)
    (θhat : ℕ → Ξ → Θ) (R : ℕ → Ξ → ℝ)
    (α β C ρ : ℝ)
    -- The proof additionally requires `α > 0`; vdV states only `α > β`.
    (hα : 0 < α)
    -- The modulus exponent is strictly smaller than the curvature exponent.
    (hβα : β < α)
    -- A common positive constant is used in the two local bounds.
    (hC : 0 < C)
    -- The hypotheses hold for all sufficiently small radii.
    (hρ : 0 < ρ)
    -- Local integrability on the same neighborhood as the curvature and modulus bounds.
    (hm_int : ∀ θ, dist θ θ₀ < ρ → Integrable (fun ω => m θ ω - m θ₀ ω) P)
    -- The official erratum on p. 75 uses curvature on
    -- `δ / 2 < dist θ θ₀ < δ`.
    (hcurv : ∀ δ, 0 < δ → δ < ρ → ∀ θ,
      δ / 2 < dist θ θ₀ → dist θ θ₀ < δ →
      ∫ ω, (m θ ω - m θ₀ ω) ∂P ≤ -C * Real.rpow δ α)
    -- Outer expectation controls the localized empirical-process modulus.
    (hmod : ∀ δ, 0 < δ → δ < ρ → ∀ n,
      outerExpectation μ (fun ξ =>
        ⨆ θ : {θ : Θ // dist θ θ₀ < δ}, ENNReal.ofReal
          |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ)
            (fun ω => m θ.1 ω - m θ₀ ω)|) ≤
        ENNReal.ofReal (C * Real.rpow δ β))
    -- The estimator nearly maximizes the empirical criterion pointwise.
    (hNearMax : ∀ n ξ,
      empiricalAvg (m (θhat n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) ≥
        empiricalAvg (m θ₀) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) - R n ξ)
    -- The near-maximality remainder is nonnegative.
    (hR_nonneg : ∀ n ξ, 0 ≤ R n ξ)
    -- The remainder satisfies `R_n = O_P(r_n^{-α})` in outer probability.
    (hR : IsBoundedInOuterProbScalar μ (fun n ξ =>
      Real.rpow (rateScale α β n) α * R n ξ))
    -- Outer consistency does not require measurability of `θhat`.
    (hcons : TendstoZeroInOuterProbScalar μ (fun n ξ => dist (θhat n ξ) θ₀)) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      μ.outerMeasureStar {ξ | M < rateScale α β n * dist (θhat n ξ) θ₀} ≤
        ENNReal.ofReal η := by
  intro η hη
  let q : ℝ := 4 / 3; let a : ℝ := 3 / 2
  have ⟨hq0, hq1⟩ : 0 < q ∧ 1 < q := by constructor <;> norm_num [q]
  have ha1 : 1 < a := by norm_num [a]
  have ⟨haq, ha2⟩ : q < a ∧ a < 2 := by constructor <;> norm_num [q, a]
  let b : ℝ := Real.rpow q α; let u : ℝ := Real.rpow q (β - α)
  have hb1 : 1 < b := Real.one_lt_rpow hq1 hα
  have hu0 : 0 ≤ u := (Real.rpow_pos_of_pos hq0 _).le
  have hu1 : u < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (sub_neg.mpr hβα)
  obtain ⟨K₀, hK₀⟩ := hR (η / 6) (by positivity); let K : ℝ := max K₀ 0 + 1
  have hKlim : limsup (fun n => μ.outerMeasureStar {ξ | K < |Real.rpow (rateScale α β n) α * R n ξ|}) atTop ≤ ENNReal.ofReal (η / 6) := by
    refine le_trans (limsup_le_limsup (Eventually.of_forall fun n => outerMeasureStar_mono μ ?_)
      isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hK₀; intro ξ hξ; exact (le_max_left K₀ 0).trans_lt ((lt_add_one _).trans hξ)
  have hKevent : ∀ᶠ n in atTop, μ.outerMeasureStar {ξ | K < |Real.rpow (rateScale α β n) α * R n ξ|} < ENNReal.ofReal (η / 3) := by
    exact Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hKlim
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))) (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
  have hDevent : ∀ᶠ n in atTop, μ.outerMeasureStar {ξ | ρ / 2 ≤ dist (θhat n ξ) θ₀} < ENNReal.ofReal (η / 3) := by
    filter_upwards [(hcons (ρ / 4) (by positivity)).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (show 0 < η / 3 by positivity)))] with n hn
    exact lt_of_le_of_lt (outerMeasureStar_mono μ (fun ξ hξ => by
      have hh : ρ / 4 < dist (θhat n ξ) θ₀ := lt_of_lt_of_le (by linarith) hξ; simpa [abs_of_nonneg dist_nonneg] using hh)) hn
  have htail : Tendsto (fun J : ℕ => 2 * u ^ J / (1 - u)) atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).const_mul 2).div_const (1 - u)
  have hslack : ∀ᶠ J : ℕ in atTop, 2 * K / C < b ^ J := (tendsto_pow_atTop_atTop_of_one_lt hb1).eventually (eventually_gt_atTop _)
  have hgeom : ∀ᶠ J : ℕ in atTop, 2 * u ^ J / (1 - u) < η / 3 := htail.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨J, hJslack, hJgeom⟩ := (hslack.and hgeom).exists; obtain ⟨N, hN⟩ := eventually_atTop.mp (hKevent.and hDevent)
  refine ⟨q ^ J, N, fun n hn => ?_⟩; have hnGood := hN n hn
  let s : ℝ := rateScale α β n; have hs0 : 0 < s := Real.rpow_pos_of_pos (by positivity) _
  have hsqrt : Real.sqrt ((n + 1 : ℕ) : ℝ) = Real.rpow s (α - β) := by
    calc Real.sqrt ((n + 1 : ℕ) : ℝ) = Real.rpow s α / Real.rpow s β := (eq_div_iff (Real.rpow_pos_of_pos hs0 β).ne').2 (rpow_rate_shell_identity α β n hβα)
      _ = Real.rpow s (α - β) := (Real.rpow_sub hs0 α β).symm
  have hrpow_pow (x : ℝ) (j : ℕ) : Real.rpow (q ^ j) x = Real.rpow q x ^ j := by
    calc Real.rpow (q ^ j) x = Real.rpow (Real.rpow q (j : ℝ)) x := by
          congr 1; exact (Real.rpow_natCast q j).symm
      _ = Real.rpow q ((j : ℝ) * x) := (Real.rpow_mul hq0.le _ _).symm
      _ = Real.rpow q (x * (j : ℝ)) := by rw [mul_comm]
      _ = Real.rpow (Real.rpow q x) (j : ℝ) := Real.rpow_mul hq0.le _ _
      _ = Real.rpow q x ^ j := Real.rpow_natCast _ _
  let A : Set Ξ := {ξ | q ^ J < s * dist (θhat n ξ) θ₀}; let D : Set Ξ := {ξ | ρ / 2 ≤ dist (θhat n ξ) θ₀}
  let B : Set Ξ := {ξ | K < |Real.rpow s α * R n ξ|}; let Good : Set Ξ := (D ∪ B)ᶜ
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (s * (ρ / 2)) hq1; let Sh : ℕ → Set Ξ := fun k => {ξ | q ^ (J + k) ≤ s * dist (θhat n ξ) θ₀ ∧ s * dist (θhat n ξ) θ₀ < q ^ (J + k + 1)}
  have hcover : A ∩ Good ⊆ ⋃ k ∈ Finset.range L, Sh k ∩ Good := by
    rintro ξ ⟨hξA, hξG⟩
    have hvtop : s * dist (θhat n ξ) θ₀ < q ^ L := by
      have hd : dist (θhat n ξ) θ₀ < ρ / 2 := by simp only [Good, D, B, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hξG; exact hξG.1
      exact (mul_lt_mul_of_pos_left hd hs0).trans hL
    have hex : ∃ k : ℕ, s * dist (θhat n ξ) θ₀ < q ^ (J + k + 1) := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (s * dist (θhat n ξ) θ₀) hq1; exact ⟨k, hk.trans_le (pow_le_pow_right₀ hq1.le (by omega))⟩
    let k := Nat.find hex; have hkhi := Nat.find_spec hex
    have hklo : q ^ (J + k) ≤ s * dist (θhat n ξ) θ₀ := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · simpa [hk] using hξA.le
      · have hmin := Nat.find_min hex (show k - 1 < k by omega)
        rw [show J + (k - 1) + 1 = J + k by omega] at hmin; exact not_lt.mp hmin
    have hkL : k < L := by by_contra h; have hp := pow_le_pow_right₀ hq1.le (show L ≤ J + k by omega); linarith
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hkL, ⟨⟨hklo, hkhi⟩, hξG⟩⟩⟩
  have hshell : ∀ k : ℕ, μ.outerMeasureStar (Sh k ∩ Good) ≤ ENNReal.ofReal (2 * u ^ (J + k)) := by
    intro k; by_cases hne : (Sh k ∩ Good).Nonempty
    · obtain ⟨ξ₀, hξ₀S, hξ₀G⟩ := hne
      let j := J + k; let δ : ℝ := a * q ^ j / s; have hδpos : 0 < δ := by dsimp [δ]; positivity
      have hδρ : δ < ρ := by
        have hd : dist (θhat n ξ₀) θ₀ < ρ / 2 := by simp only [Good, D, B, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hξ₀G; exact hξ₀G.1
        have hlo := hξ₀S.1
        have : q ^ j / s ≤ dist (θhat n ξ₀) θ₀ := (div_le_iff₀ hs0).2 (by simpa [j, mul_comm] using hlo)
        have hbase : q ^ j / s < ρ / 2 := this.trans_lt hd
        calc a * q ^ j / s = a * (q ^ j / s) := by ring
          _ < a * (ρ / 2) := mul_lt_mul_of_pos_left hbase (by positivity)
          _ < ρ := by dsimp [a]; nlinarith
      have hbmono : b ^ J ≤ b ^ j := pow_le_pow_right₀ hb1.le (by simp [j])
      have hKbj : K ≤ C / 2 * b ^ j := by
        have hh := (div_lt_iff₀ hC).1 hJslack; nlinarith
      have haα : 1 ≤ Real.rpow a α := Real.one_le_rpow ha1.le hα.le
      have hscaleδ : Real.rpow s α * Real.rpow δ α = Real.rpow a α * b ^ j := by
        calc Real.rpow s α * Real.rpow δ α = Real.rpow (s * δ) α := (Real.mul_rpow hs0.le hδpos.le).symm
          _ = Real.rpow (a * q ^ j) α := by congr 1; dsimp [δ]; field_simp
          _ = Real.rpow a α * Real.rpow (q ^ j) α := Real.mul_rpow (le_trans zero_le_one ha1.le) (pow_nonneg hq0.le _)
          _ = Real.rpow a α * b ^ j := by rw [hrpow_pow]
      have hKδ : K ≤ C / 2 * (Real.rpow s α * Real.rpow δ α) := by
        rw [hscaleδ]; exact hKbj.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (pow_nonneg (le_trans zero_le_one hb1.le) _) haα) (by positivity))
      let t : ℝ := Real.sqrt ((n + 1 : ℕ) : ℝ) * (C / 2) * Real.rpow δ α
      have ht : 0 < t := by dsimp [t]; positivity
      have hincl : Sh k ∩ Good ⊆ {ξ | ENNReal.ofReal t ≤ ⨆ θ : {θ : Θ // dist θ θ₀ < δ},
          ENNReal.ofReal |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ) (fun ω => m θ.1 ω - m θ₀ ω)|} := by
        rintro ξ ⟨hξS, hξG⟩
        change q ^ (J + k) ≤ s * dist (θhat n ξ) θ₀ ∧ s * dist (θhat n ξ) θ₀ < q ^ (J + k + 1) at hξS
        simp only [Good, D, B, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hξG
        have hdlo : δ / 2 < dist (θhat n ξ) θ₀ := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2)]; change a * q ^ j / s < dist (θhat n ξ) θ₀ * 2
          rw [div_lt_iff₀ hs0]; have := hξS.1; nlinarith [pow_pos hq0 j]
        have hdhi : dist (θhat n ξ) θ₀ < δ := by
          change dist (θhat n ξ) θ₀ < a * q ^ j / s; rw [lt_div_iff₀ hs0]
          have hpow : q ^ (j + 1) = q ^ j * q := pow_succ q j
          rw [hpow] at hξS; nlinarith [pow_pos hq0 j]
        have hpop := hcurv δ hδpos hδρ (θhat n ξ) hdlo hdhi
        have hscaled : Real.rpow s α * R n ξ ≤ K := by
          have hnon : 0 ≤ Real.rpow s α * R n ξ := mul_nonneg (Real.rpow_nonneg hs0.le _) (hR_nonneg n ξ)
          simpa only [not_lt, abs_of_nonneg hnon] using hξG.2
        have hRle : R n ξ ≤ C / 2 * Real.rpow δ α := le_of_mul_le_mul_left
          (hscaled.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hKδ)) (Real.rpow_pos_of_pos hs0 α)
        let xs : Fin (n + 1) → Ω := fun i => X i.val ξ; let g : Ω → ℝ := fun ω => m (θhat n ξ) ω - m θ₀ ω
        let c : ℝ := ∫ ω, g ω ∂P; let gc : Ω → ℝ := fun ω => g ω - c
        have hg_int : Integrable g P := by
          refine ⟨((hm_meas (θhat n ξ)).sub (hm_meas θ₀)).aestronglyMeasurable, ?_⟩
          exact (hm_int (θhat n ξ) (hdhi.trans hδρ)).hasFiniteIntegral
        have hgc_mean : ∫ ω, gc ω ∂P = 0 := by
          dsimp [gc]
          rw [integral_sub hg_int (integrable_const c), integral_const, probReal_univ, one_smul]
          dsimp [c]; ring
        have hc_avg : empiricalAvg (fun _ : Ω => c) (n + 1) xs = c := by
          unfold empiricalAvg
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
        have hgc_avg : empiricalAvg gc (n + 1) xs = empiricalAvg g (n + 1) xs - c := by
          calc
            empiricalAvg gc (n + 1) xs = empiricalAvg g (n + 1) xs -
                empiricalAvg (fun _ : Ω => c) (n + 1) xs := by
              dsimp [gc]; unfold empiricalAvg; rw [Finset.sum_sub_distrib, mul_sub]
            _ = empiricalAvg g (n + 1) xs - c := by rw [hc_avg]
        have hcenter : empiricalProcess P (n + 1) xs gc = empiricalProcess P (n + 1) xs g := by
          dsimp [gc]
          rw [empiricalProcess_sub P (n + 1) xs g (fun _ => c) hg_int (integrable_const c)]
          have hc_ep : empiricalProcess P (n + 1) xs (fun _ => c) = 0 := by
            unfold empiricalProcess; rw [hc_avg, integral_const, probReal_univ, one_smul, sub_self, mul_zero]
          rw [hc_ep, sub_zero]
        have hE : empiricalAvg g (n + 1) xs = empiricalAvg (m (θhat n ξ)) (n + 1) xs - empiricalAvg (m θ₀) (n + 1) xs := by
          unfold empiricalAvg g; rw [Finset.sum_sub_distrib, mul_sub]
        have hnear := hNearMax n ξ
        have hG : t ≤ empiricalProcess P (n + 1) xs g := by
          rw [← hcenter, empiricalProcess, hgc_avg, hgc_mean, sub_zero, hE]
          have hinner : C / 2 * Real.rpow δ α ≤ empiricalAvg (m (θhat n ξ)) (n + 1) xs -
              empiricalAvg (m θ₀) (n + 1) xs - ∫ ω, (m (θhat n ξ) ω - m θ₀ ω) ∂P := by
            nlinarith [hnear, hpop, hRle]
          dsimp [t, c, g]
          calc Real.sqrt ((n + 1 : ℕ) : ℝ) * (C / 2) * Real.rpow δ α = Real.sqrt ((n + 1 : ℕ) : ℝ) * (C / 2 * Real.rpow δ α) := by ring
            _ ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * (empiricalAvg (m (θhat n ξ)) (n + 1) xs - empiricalAvg (m θ₀) (n + 1) xs -
                ∫ ω, (m (θhat n ξ) ω - m θ₀ ω) ∂P) := mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg _)
        calc ENNReal.ofReal t ≤ ENNReal.ofReal |empiricalProcess P (n + 1) xs g| := ENNReal.ofReal_le_ofReal (hG.trans (le_abs_self _))
          _ ≤ ⨆ θ : {θ : Θ // dist θ θ₀ < δ}, ENNReal.ofReal |empiricalProcess P (n + 1) xs (fun ω => m θ.1 ω - m θ₀ ω)| :=
            le_iSup (fun θ : {θ : Θ // dist θ θ₀ < δ} => ENNReal.ofReal |empiricalProcess P (n + 1) xs (fun ω => m θ.1 ω - m θ₀ ω)|) ⟨θhat n ξ, hdhi⟩
      have hratio : C * Real.rpow δ β / t ≤ 2 * u ^ j := by
        have haexp : Real.rpow a (β - α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha1.le (sub_nonpos.mpr hβα.le)
        have hsneg : Real.rpow s (β - α) = 1 / Real.rpow s (α - β) := by
          rw [show β - α = -(α - β) by ring]; simpa [one_div] using Real.rpow_neg hs0.le (α - β)
        have htdef : t = Real.sqrt ((n + 1 : ℕ) : ℝ) * (C / 2) * Real.rpow δ α := rfl
        have hsqrtpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
        calc C * Real.rpow δ β / t = 2 * (Real.rpow δ β / Real.rpow δ α) / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
              rw [htdef]; field_simp [hC.ne', (Real.rpow_pos_of_pos hδpos α).ne', hsqrtpos.ne']
          _ = 2 * Real.rpow δ (β - α) / Real.rpow s (α - β) := by
            rw [hsqrt]; congr 2; exact (Real.rpow_sub hδpos β α).symm
          _ = 2 * (Real.rpow δ (β - α) * Real.rpow s (β - α)) := by
            rw [hsneg]; ring
          _ = 2 * (Real.rpow s (β - α) * Real.rpow δ (β - α)) := by ring
          _ = 2 * Real.rpow (s * δ) (β - α) := by
            congr 1; exact (Real.mul_rpow hs0.le hδpos.le).symm
          _ = 2 * Real.rpow (a * q ^ j) (β - α) := by
            congr 2; dsimp [δ]; field_simp
          _ = 2 * (Real.rpow a (β - α) * Real.rpow (q ^ j) (β - α)) := by
            congr 1; exact Real.mul_rpow (le_trans zero_le_one ha1.le) (pow_nonneg hq0.le _)
          _ = 2 * (Real.rpow a (β - α) * u ^ j) := by rw [hrpow_pow (β - α) j]
          _ ≤ 2 * u ^ j := by
            have hh := mul_le_mul_of_nonneg_right haexp (pow_nonneg hu0 j)
            calc 2 * (Real.rpow a (β - α) * u ^ j) ≤ 2 * (1 * u ^ j) := mul_le_mul_of_nonneg_left hh (by norm_num)
              _ = 2 * u ^ j := by ring
      calc μ.outerMeasureStar (Sh k ∩ Good) ≤ μ.outerMeasureStar {ξ | ENNReal.ofReal t ≤ ⨆ θ : {θ : Θ // dist θ θ₀ < δ},
              ENNReal.ofReal |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ) (fun ω => m θ.1 ω - m θ₀ ω)|} := outerMeasureStar_mono μ hincl
        _ ≤ outerExpectation μ (fun ξ => ⨆ θ : {θ : Θ // dist θ θ₀ < δ}, ENNReal.ofReal
              |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ) (fun ω => m θ.1 ω - m θ₀ ω)|) / ENNReal.ofReal t :=
            outerExpectation_markov _ (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (C * Real.rpow δ β) / ENNReal.ofReal t := ENNReal.div_le_div_right (hmod δ hδpos hδρ n) _
        _ = ENNReal.ofReal (C * Real.rpow δ β / t) := (ENNReal.ofReal_div_of_pos ht).symm
        _ ≤ ENNReal.ofReal (2 * u ^ (J + k)) := ENNReal.ofReal_le_ofReal (by simpa [j] using hratio)
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]; exact zero_le
  calc μ.outerMeasureStar A
      ≤ μ.outerMeasureStar (A ∩ Good) + μ.outerMeasureStar D + μ.outerMeasureStar B := by
        have hsub : A ⊆ (A ∩ Good) ∪ D ∪ B := by
          intro ξ hξA
          by_cases hξD : ξ ∈ D; · exact Or.inl (Or.inr hξD)
          by_cases hξB : ξ ∈ B; · exact Or.inr hξB
          · have hξG : ξ ∈ Good := by
              simpa only [Good, Set.mem_compl_iff, Set.mem_union, not_or] using And.intro hξD hξB
            exact Or.inl (Or.inl ⟨hξA, hξG⟩)
        refine le_trans (outerMeasureStar_mono μ hsub) ?_; exact (outerMeasureStar_union_le μ _ _).trans (add_le_add (outerMeasureStar_union_le μ _ _) le_rfl)
    _ ≤ (∑ k ∈ Finset.range L, ENNReal.ofReal (2 * u ^ (J + k))) +
        ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) := by
      have hAG : μ.outerMeasureStar (A ∩ Good) ≤ ∑ k ∈ Finset.range L, ENNReal.ofReal (2 * u ^ (J + k)) :=
        (outerMeasureStar_mono μ hcover).trans ((outerMeasureStar_finset_iUnion_le μ _ _).trans (Finset.sum_le_sum fun k _ => hshell k))
      exact add_le_add (add_le_add hAG hnGood.2.le) hnGood.1.le
    _ ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) := by
      have hshift_nonneg : ∀ k : ℕ, 0 ≤ 2 * u ^ (J + k) := fun k => by positivity
      have hshift_sum : Summable (fun k : ℕ => 2 * u ^ (J + k)) := by
        have hg := summable_geometric_of_lt_one hu0 hu1
        rw [show (fun k : ℕ => 2 * u ^ (J + k)) = fun k => (2 * u ^ J) * u ^ k by
          funext k; rw [pow_add]; ring]; exact hg.mul_left (2 * u ^ J)
      have hshift_tsum : (∑' k : ℕ, 2 * u ^ (J + k)) = 2 * u ^ J / (1 - u) := by
        calc (∑' k : ℕ, 2 * u ^ (J + k)) = ∑' k : ℕ, (2 * u ^ J) * u ^ k := by
                congr 1; funext k; rw [pow_add]; ring
          _ = (2 * u ^ J) * (∑' k : ℕ, u ^ k) := tsum_mul_left
          _ = 2 * u ^ J / (1 - u) := by rw [tsum_geometric_of_lt_one hu0 hu1]; rfl
      have hsum : (∑ k ∈ Finset.range L, ENNReal.ofReal (2 * u ^ (J + k))) ≤ ENNReal.ofReal (η / 3) := by
        calc (∑ k ∈ Finset.range L, ENNReal.ofReal (2 * u ^ (J + k))) ≤ ∑' k : ℕ, ENNReal.ofReal (2 * u ^ (J + k)) := ENNReal.sum_le_tsum _
        _ = ENNReal.ofReal (∑' k : ℕ, 2 * u ^ (J + k)) := (ENNReal.ofReal_tsum_of_nonneg hshift_nonneg hshift_sum).symm
        _ = ENNReal.ofReal (2 * u ^ J / (1 - u)) := congrArg ENNReal.ofReal hshift_tsum
        _ ≤ ENNReal.ofReal (η / 3) := ENNReal.ofReal_le_ofReal hJgeom.le
      exact add_le_add (add_le_add hsum le_rfl) le_rfl
    _ = ENNReal.ofReal η := by
      have hη3 : 0 ≤ η / 3 := (div_pos hη (by norm_num)).le
      rw [← ENNReal.ofReal_add hη3 hη3, ← ENNReal.ofReal_add (add_nonneg hη3 hη3) hη3]; congr 1; ring

/-- Outer-probability core of vdV Theorem 5.52. -/
theorem mEstimator_rate_of_convergence_outer
    {Ω Θ Ξ : Type*} [MeasurableSpace Ω] [MetricSpace Θ] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (m : Θ → Ω → ℝ) (θ₀ : Θ)
    -- The criterion functions in vdV Theorem 5.52 are measurable.
    (hm_meas : ∀ θ, Measurable (m θ))
    (X : ℕ → Ξ → Ω)
    (θhat : ℕ → Ξ → Θ) (R : ℕ → Ξ → ℝ)
    (α β C ρ : ℝ) (hα : 0 < α) (hβα : β < α) (hC : 0 < C) (hρ : 0 < ρ)
    -- Local integrability on the same neighborhood as the curvature and modulus bounds.
    (hm_int : ∀ θ, dist θ θ₀ < ρ → Integrable (fun ω => m θ ω - m θ₀ ω) P)
    (hcurv : ∀ δ, 0 < δ → δ < ρ → ∀ θ,
      δ / 2 < dist θ θ₀ → dist θ θ₀ < δ →
      ∫ ω, (m θ ω - m θ₀ ω) ∂P ≤ -C * Real.rpow δ α)
    (hmod : ∀ δ, 0 < δ → δ < ρ → ∀ n,
      outerExpectation μ (fun ξ =>
        ⨆ θ : {θ : Θ // dist θ θ₀ < δ}, ENNReal.ofReal
          |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ)
            (fun ω => m θ.1 ω - m θ₀ ω)|) ≤
        ENNReal.ofReal (C * Real.rpow δ β))
    (hNearMax : ∀ n ξ,
      empiricalAvg (m (θhat n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) ≥
        empiricalAvg (m θ₀) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) - R n ξ)
    (hR_nonneg : ∀ n ξ, 0 ≤ R n ξ)
    (hR : IsBoundedInOuterProbScalar μ (fun n ξ =>
      Real.rpow (rateScale α β n) α * R n ξ))
    (hcons : TendstoZeroInOuterProbScalar μ (fun n ξ => dist (θhat n ξ) θ₀)) :
    IsBoundedInOuterProbScalar μ (fun n ξ => rateScale α β n * dist (θhat n ξ) θ₀) := by
  apply outer_geometric_peeling μ _
  intro η hη
  obtain ⟨M, N, hMN⟩ := metricRate_shell_tail P μ m θ₀ hm_meas X θhat R α β C ρ
    hα hβα hC hρ hm_int hcurv hmod hNearMax hR_nonneg hR hcons η hη
  refine ⟨M, N, fun n hn => ?_⟩
  have heq : {ξ | M < |rateScale α β n * dist (θhat n ξ) θ₀|} = {ξ | M < rateScale α β n * dist (θhat n ξ) θ₀} := by
    ext ξ; simp only [Set.mem_setOf_eq]
    have hp : 0 ≤ rateScale α β n * dist (θhat n ξ) θ₀ := mul_nonneg (Real.rpow_nonneg (by positivity) _) dist_nonneg
    constructor <;> intro h <;> simpa only [abs_of_nonneg hp] using h
  rw [heq]; exact hMN n hn

/-- **vdV Theorem 5.52 (Rate of convergence).**  The remainder is measurable
and nonnegative and satisfies ordinary `O_P`; the estimator itself need not be
measurable. -/
theorem mEstimator_rate_of_convergence
    {Ω Θ Ξ : Type*} [MeasurableSpace Ω] [MetricSpace Θ] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (m : Θ → Ω → ℝ) (θ₀ : Θ)
    -- LEAN-ONLY: the criterion functions in vdV Theorem 5.52 are measurable.
    (hm_meas : ∀ θ, Measurable (m θ))
    (X : ℕ → Ξ → Ω)
    (θhat : ℕ → Ξ → Θ) (R : ℕ → Ξ → ℝ)
    -- LEAN-ONLY: remainder measurability converts ordinary `O_P` to outer probability.
    (hR_meas : ∀ n, Measurable (R n))
    (α β C ρ : ℝ)
    -- USER-INPUT: exponent ordering and positive local constants in the rate
    -- calculation; the formal statement records the required `α > 0` explicitly.
    (hα : 0 < α) (hβα : β < α) (hC : 0 < C) (hρ : 0 < ρ)
    -- LEAN-ONLY: local integrability on the same neighborhood as the curvature and modulus bounds.
    (hm_int : ∀ θ, dist θ θ₀ < ρ → Integrable (fun ω => m θ ω - m θ₀ ω) P)
    -- USER-INPUT: local population curvature and empirical-process modulus;
    -- vdV Theorem 5.52.
    (hcurv : ∀ δ, 0 < δ → δ < ρ → ∀ θ,
      δ / 2 < dist θ θ₀ → dist θ θ₀ < δ →
      ∫ ω, (m θ ω - m θ₀ ω) ∂P ≤ -C * Real.rpow δ α)
    (hmod : ∀ δ, 0 < δ → δ < ρ → ∀ n,
      outerExpectation μ (fun ξ =>
        ⨆ θ : {θ : Θ // dist θ θ₀ < δ}, ENNReal.ofReal
          |empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ)
            (fun ω => m θ.1 ω - m θ₀ ω)|) ≤
        ENNReal.ofReal (C * Real.rpow δ β))
    -- USER-INPUT: approximate maximization, as in vdV Theorem 5.52.
    (hNearMax : ∀ n ξ,
      empiricalAvg (m (θhat n ξ)) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) ≥
        empiricalAvg (m θ₀) (n + 1) (fun i : Fin (n + 1) => X i.val ξ) - R n ξ)
    -- LEAN-ONLY: the approximation remainder is represented as nonnegative.
    (hR_nonneg : ∀ n ξ, 0 ≤ R n ξ)
    -- USER-INPUT: the scaled remainder is `O_P(1)` and the estimator is consistent;
    -- vdV Theorem 5.52.
    (hR : IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      Real.rpow (rateScale α β n) α * R n ξ))
    (hcons : TendstoZeroInOuterProbScalar μ (fun n ξ => dist (θhat n ξ) θ₀)) :
    IsBoundedInOuterProbScalar μ (fun n ξ => rateScale α β n * dist (θhat n ξ) θ₀) := by
  have hR_outer : IsBoundedInOuterProbScalar μ (fun n ξ =>
      Real.rpow (rateScale α β n) α * R n ξ) := by
    intro η hη
    obtain ⟨M, hM⟩ := hR η hη
    refine ⟨M, ?_⟩
    have hZ_meas : ∀ n, Measurable (fun ξ => Real.rpow (rateScale α β n) α * R n ξ) :=
      fun n => measurable_const.mul (hR_meas n)
    have htail_meas : ∀ n, MeasurableSet
        {ξ | M < |Real.rpow (rateScale α β n) α * R n ξ|} :=
      fun n => measurableSet_lt measurable_const (hZ_meas n).abs
    have hbound : ∀ n, μ.outerMeasureStar
        {ξ | M < |Real.rpow (rateScale α β n) α * R n ξ|} ≤ ENNReal.ofReal η := by
      intro n
      calc
        μ.outerMeasureStar {ξ | M < |Real.rpow (rateScale α β n) α * R n ξ|}
            = μ {ξ | M < |Real.rpow (rateScale α β n) α * R n ξ|} :=
              outerMeasureStar_eq_measure (htail_meas n)
        _ = ENNReal.ofReal (μ.real
              {ξ | M < |Real.rpow (rateScale α β n) α * R n ξ|}) := by
            rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by
              simpa only [Real.norm_eq_abs] using hM n)
    calc
      limsup (fun n => μ.outerMeasureStar
          {ξ | M < |Real.rpow (rateScale α β n) α * R n ξ|}) atTop
          ≤ limsup (fun _ : ℕ => ENNReal.ofReal η) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      _ = ENNReal.ofReal η := limsup_const _
  exact mEstimator_rate_of_convergence_outer P μ m θ₀ hm_meas X θhat R α β C ρ hα hβα hC
    hρ hm_int hcurv hmod hNearMax hR_nonneg hR_outer hcons

end AsymptoticStatistics.MEstimator
