module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.OuterPeeling

@[expose] public section

/-!
# M-estimator rates with nuisance parameters

Formalization of van der Vaart Theorem 5.55 (book pp. 78--79).
The discrepancy functions are deliberately arbitrary nonnegative functions;
neither parameter set is required to carry a metric structure.
-/

namespace AsymptoticStatistics.MEstimator

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology

/-- Internal notation for the positive-sample empirical criterion.  At `n=0`
it uses the first observation, matching the global `n+1` reindexing. -/
noncomputable def nuisanceEmpiricalCriterion
    {Ω Θ H Ξ : Type*} [MeasurableSpace Ω]
    (m : Θ → H → Ω → ℝ) (X : ℕ → Ξ → Ω)
    (n : ℕ) (ξ : Ξ) (θ : Θ) (η : H) : ℝ :=
  empiricalAvg (m θ η) (n + 1) (fun i : Fin (n + 1) => X i.val ξ)

/-- Internal notation for the positive-sample empirical process of the
fixed-nuisance criterion difference. -/
noncomputable def nuisanceCenteredProcess
    {Ω Θ H Ξ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : Θ → H → Ω → ℝ) (X : ℕ → Ξ → Ω)
    (θ₀ : Θ) (n : ℕ) (ξ : Ξ) (θ : Θ) (η : H) : ℝ :=
  empiricalProcess P (n + 1) (fun i : Fin (n + 1) => X i.val ξ)
    (fun ω => m θ η ω - m θ₀ η ω)

/-- Local readout of the induced outer measure as the ambient measure's
outer-measure evaluation. -/
private theorem outerMeasureStar_eq_measure_all
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (A : Set Ξ) :
    μ.outerMeasureStar A = μ A := by
  apply le_antisymm
  · rw [measure_eq_iInf]
    refine le_iInf fun t => le_iInf fun hAt => le_iInf fun ht => ?_
    rw [Measure.outerMeasureStar, outerExpectation]
    calc
      (⨅ U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U},
          ∫⁻ ξ, (U : Ξ → ℝ≥0∞) ξ ∂μ) ≤ ∫⁻ ξ, t.indicator 1 ξ ∂μ :=
        iInf_le (fun U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U} =>
          ∫⁻ ξ, (U : Ξ → ℝ≥0∞) ξ ∂μ)
          ⟨t.indicator 1, measurable_one.indicator ht, fun ξ => by
            by_cases hξ : ξ ∈ A
            · simp [hξ, hAt hξ]
            · simp [hξ]⟩
      _ = μ t := lintegral_indicator_one ht
  · rw [Measure.outerMeasureStar, outerExpectation]
    refine le_iInf fun U => ?_
    set t : Set Ξ := {ξ | (1 : ℝ≥0∞) ≤ U.1 ξ}
    have ht : MeasurableSet t := measurableSet_le measurable_const U.2.1
    calc
      μ A ≤ μ t := measure_mono fun ξ hξ => by
        change (1 : ℝ≥0∞) ≤ U.1 ξ
        simpa [hξ] using U.2.2 ξ
      _ = ∫⁻ ξ, t.indicator 1 ξ ∂μ := (lintegral_indicator_one ht).symm
      _ ≤ ∫⁻ ξ, U.1 ξ ∂μ := lintegral_mono fun ξ => by
        by_cases hξ : ξ ∈ t
        · rw [Set.indicator_of_mem hξ]
          exact hξ
        · rw [Set.indicator_of_notMem hξ]
          exact zero_le

/-- Deterministic shell geometry used in the nuisance peeling
argument. -/
theorem nuisance_shell_geometry
    {Θ H : Type*} (dΘ : Θ → Θ → NNReal) (dH : H → H → NNReal)
    (θ θ₀ : Θ) (η η₀ : H) (δ : ℝ) (j M : ℕ)
    -- Membership in the `j`th parameter shell.
    (hlo : Real.rpow 2 (j : ℝ) * δ ≤ (dΘ θ θ₀ : ℝ))
    -- The nuisance discrepancy is relatively small on the shell.
    (hη : (dH η η₀ : ℝ) ≤ Real.rpow 2 (-(M : ℝ)) * (dΘ θ θ₀ : ℝ)) :
    (dH η η₀ : ℝ) ^ 2 ≤
      Real.rpow 2 (-2 * (M : ℝ)) * (dΘ θ θ₀ : ℝ) ^ 2 := by
  by_cases hshell : Real.rpow 2 (j : ℝ) * δ ≤ (dΘ θ θ₀ : ℝ)
  · have hH : (0 : ℝ) ≤ (dH η η₀ : ℝ) := NNReal.coe_nonneg _
    calc
      (dH η η₀ : ℝ) ^ 2 ≤ (Real.rpow 2 (-(M : ℝ)) * (dΘ θ θ₀ : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hH hη 2
      _ = Real.rpow 2 (-2 * (M : ℝ)) * (dΘ θ θ₀ : ℝ) ^ 2 := by
        rw [mul_pow]
        congr 1
        calc
          Real.rpow 2 (-(M : ℝ)) ^ 2 =
              Real.rpow 2 (-(M : ℝ)) * Real.rpow 2 (-(M : ℝ)) := by rw [sq]
          _ =
              Real.rpow 2 ((-(M : ℝ)) + (-(M : ℝ))) :=
            (Real.rpow_add (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2) _ _).symm
          _ = Real.rpow 2 (-2 * (M : ℝ)) := by congr 1; ring
  · exact (hshell hlo).elim

/-- The shell-tail estimate used for vdV Theorem 5.55. -/
theorem nuisanceRate_shell_tail
    {Ω Θ H Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (m : Θ → H → Ω → ℝ) (θ₀ : Θ) (η₀ : H)
    -- The criterion functions are measurable.
    (hm_meas : ∀ θ η, Measurable (m θ η))
    (X : ℕ → Ξ → Ω)
    (Θn : ℕ → Set Θ) (Hn : ℕ → Set H)
    -- Integrability on the same local domain as the drift and modulus bounds.
    (hm_int : ∀ n θ, θ ∈ Θn n → ∀ η, η ∈ Hn n →
      Integrable (fun ω => m θ η ω - m θ₀ η ω) P)
    (dΘ : ℕ → Θ → Θ → NNReal) (dH : H → H → NNReal)
    (e : ℕ → Θ → H → ℝ) (φ : ℕ → ℝ → ℝ)
    (β : ℝ) (hβ : β < 2)
    (hφanti : ∀ n, AntitoneOn (fun δ => φ n δ / Real.rpow δ β) (Set.Ioi 0))
    (δn : ℕ → ℝ) (hδn : ∀ n, 0 < δn n)
    (hbalance : ∀ n, φ n (δn n) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * (δn n) ^ 2)
    (hdet : ∀ n θ, θ ∈ Θn n → ∀ η, η ∈ Hn n →
      (∫ ω, (m θ η ω - m θ₀ η ω) ∂P) + e n θ η ≤
        -(dΘ n θ θ₀ : ℝ) ^ 2 + (dH η η₀ : ℝ) ^ 2)
    (hmod : ∀ n δ, 0 < δ →
      outerExpectation μ (fun ξ =>
        ⨆ θ : {θ : Θ // θ ∈ Θn n ∧ (dΘ n θ θ₀ : ℝ) < δ},
          ⨆ η : {η : H // η ∈ Hn n}, ENNReal.ofReal
            |nuisanceCenteredProcess P m X θ₀ n ξ θ.1 η.1 -
                Real.sqrt ((n + 1 : ℕ) : ℝ) * e n θ.1 η.1|) ≤
        ENNReal.ofReal (φ n δ))
    (θhat : ℕ → Ξ → Θ) (ηhat : ℕ → Ξ → H)
    (hmem : TendstoInnerProbOne μ (fun n =>
      {ξ | θhat n ξ ∈ Θn n ∧ ηhat n ξ ∈ Hn n}))
    (R : ℕ → Ξ → ℝ) (hR_nonneg : ∀ n ξ, 0 ≤ R n ξ)
    (hNearMax : ∀ n ξ,
      nuisanceEmpiricalCriterion m X n ξ (θhat n ξ) (ηhat n ξ) ≥
        nuisanceEmpiricalCriterion m X n ξ θ₀ (ηhat n ξ) - R n ξ)
    -- Outer `O_P` permits the shell estimate to use a nonmeasurable error term.
    (hR : IsBoundedInOuterProbScalar μ (fun n ξ => R n ξ / (δn n) ^ 2)) :
    ∀ γ : ℝ, 0 < γ → ∃ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      μ.outerMeasureStar {ξ |
        M * (δn n + (dH (ηhat n ξ) η₀ : ℝ)) <
          |(dΘ n (θhat n ξ) θ₀ : ℝ)|} ≤ ENNReal.ofReal γ := by
  intro γ hγ
  obtain ⟨K₀, hK₀⟩ := hR (γ / 8) (by positivity)
  set K : ℝ := max K₀ 0 + 1
  have hK : 0 < K := by dsimp [K]; linarith [le_max_right K₀ 0]
  have hK₀K : K₀ < K := by dsimp [K]; linarith [le_max_left K₀ 0]
  have hKlim : limsup (fun n => μ.outerMeasureStar
      {ξ | K < |R n ξ / (δn n) ^ 2|}) atTop ≤ ENNReal.ofReal (γ / 8) := by
    refine (limsup_le_limsup (Eventually.of_forall fun n => outerMeasureStar_mono μ ?_)
      isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)).trans hK₀
    exact fun ξ hξ => lt_trans hK₀K hξ
  have hKev : ∀ᶠ n in atTop,
      μ.outerMeasureStar {ξ | K < |R n ξ / (δn n) ^ 2|} < ENNReal.ofReal (γ / 4) :=
    eventually_lt_of_limsup_lt (hKlim.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)))
  have hmemev : ∀ᶠ n in atTop, μ.outerMeasureStar
      ({ξ | θhat n ξ ∈ Θn n ∧ ηhat n ξ ∈ Hn n}ᶜ) < ENNReal.ofReal (γ / 4) :=
    (EmpiricalProcess.TendstoInnerProbOne.tendsto_outerMeasureStar_compl hmem).eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  set q : ℝ := Real.rpow 2 (β - 2)
  set Cβ : ℝ := 2 * Real.rpow 2 β
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := by
    rw [show (1 : ℝ) = Real.rpow 2 0 by simp, show q = Real.rpow 2 (β - 2) by rfl]
    exact Real.strictMono_rpow_of_base_gt_one (by norm_num) (sub_neg.mpr hβ)
  have hCβ : 0 < Cβ := mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have htail : Tendsto (fun j : ℕ => Cβ * q ^ j / (1 - q)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul Cβ).div_const
      (1 - q)
  obtain ⟨Jt, hJt⟩ := eventually_atTop.mp
    (htail.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < γ / 4)))
  obtain ⟨Js, hJs⟩ := pow_unbounded_of_one_lt (4 * K) (by norm_num : (1 : ℝ) < 2)
  set J : ℕ := max 1 (max Jt Js)
  have hJ1 : 1 ≤ J := le_max_left _ _
  have hJt' : Jt ≤ J := (le_max_left Jt Js).trans (le_max_right 1 _)
  have hJs' : Js ≤ J := (le_max_right Jt Js).trans (le_max_right 1 _)
  have hsumJ : Cβ * q ^ J / (1 - q) < γ / 4 := hJt J hJt'
  have hcoef : Real.rpow 2 (-2 * (J : ℝ)) ≤ 1 / 4 := by
    have hJ1' : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
    have he : -2 * (J : ℝ) ≤ (-2 : ℝ) := by linarith
    calc
      Real.rpow 2 (-2 * (J : ℝ)) ≤ Real.rpow 2 (-2 : ℝ) :=
        (Real.strictMono_rpow_of_base_gt_one (by norm_num)).monotone he
      _ = 1 / 4 := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  obtain ⟨Nm, hNm⟩ := eventually_atTop.mp hmemev
  obtain ⟨NK, hNK⟩ := eventually_atTop.mp hKev
  refine ⟨(2 : ℝ) ^ J, max Nm NK, fun n hn => ?_⟩
  let A : Set Ξ := {ξ | (2 : ℝ) ^ J * (δn n + (dH (ηhat n ξ) η₀ : ℝ)) <
    (dΘ n (θhat n ξ) θ₀ : ℝ)}
  let S : Set Ξ := {ξ | θhat n ξ ∈ Θn n ∧ ηhat n ξ ∈ Hn n}
  let B : Set Ξ := {ξ | K < |R n ξ / (δn n) ^ 2|}
  let Sh : ℕ → Set Ξ := fun j => A ∩ S ∩ Bᶜ ∩
    {ξ | (2 : ℝ) ^ j * δn n ≤ (dΘ n (θhat n ξ) θ₀ : ℝ) ∧
      (dΘ n (θhat n ξ) θ₀ : ℝ) < (2 : ℝ) ^ (j + 1) * δn n}
  have hshell : ∀ j, J ≤ j → μ.outerMeasureStar (Sh j) ≤ ENNReal.ofReal (Cβ * q ^ j) := by
    intro j hj
    set D : ℝ := (2 : ℝ) ^ (j + 1) * δn n
    set t : ℝ := Real.sqrt ((n + 1 : ℕ) : ℝ) / 2 * ((2 : ℝ) ^ j * δn n) ^ 2
    have hbase : 0 < (2 : ℝ) ^ j * δn n := mul_pos (pow_pos (by norm_num) _) (hδn n)
    have hsqrt : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hD : 0 < D := by dsimp [D]; exact mul_pos (pow_pos (by norm_num) _) (hδn n)
    have ht : 0 < t := by
      dsimp [t]
      exact mul_pos (div_pos hsqrt (by norm_num)) (sq_pos_of_pos hbase)
    let Z : Ξ → ℝ≥0∞ := fun ξ =>
      ⨆ θ : {θ : Θ // θ ∈ Θn n ∧ (dΘ n θ θ₀ : ℝ) < D},
        ⨆ η : {η : H // η ∈ Hn n}, ENNReal.ofReal
          |nuisanceCenteredProcess P m X θ₀ n ξ θ.1 η.1 -
            Real.sqrt ((n + 1 : ℕ) : ℝ) * e n θ.1 η.1|
    have hincl : Sh j ⊆ {ξ | ENNReal.ofReal t ≤ Z ξ} := by
      rintro ξ ⟨⟨⟨hA, hS⟩, hB⟩, hlo, hup⟩
      have hη : (dH (ηhat n ξ) η₀ : ℝ) ≤ Real.rpow 2 (-(J : ℝ)) *
          (dΘ n (θhat n ξ) θ₀ : ℝ) := by
        have hp : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
        have hh : (2 : ℝ) ^ J * (dH (ηhat n ξ) η₀ : ℝ) <
            (dΘ n (θhat n ξ) θ₀ : ℝ) :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (hδn n).le) hp.le) hA
        rw [show Real.rpow 2 (-(J : ℝ)) = ((2 : ℝ) ^ J)⁻¹ by
          calc
            Real.rpow 2 (-(J : ℝ)) = (Real.rpow 2 (J : ℝ))⁻¹ :=
              Real.rpow_neg (x := (2 : ℝ)) (by norm_num) _
            _ = ((2 : ℝ) ^ J)⁻¹ := congrArg Inv.inv (Real.rpow_natCast 2 J)]
        rw [inv_mul_eq_div, le_div_iff₀ hp]
        simpa [mul_comm] using hh.le
      have hlo' : Real.rpow 2 (j : ℝ) * δn n ≤ (dΘ n (θhat n ξ) θ₀ : ℝ) := by
        change (2 : ℝ) ^ (j : ℝ) * δn n ≤ (dΘ n (θhat n ξ) θ₀ : ℝ)
        rwa [Real.rpow_natCast]
      have hgeom := nuisance_shell_geometry (dΘ n) dH (θhat n ξ) θ₀ (ηhat n ξ) η₀
        (δn n) j J hlo' hη
      have hdHsq : (dH (ηhat n ξ) η₀ : ℝ) ^ 2 ≤
          (1 / 4 : ℝ) * (dΘ n (θhat n ξ) θ₀ : ℝ) ^ 2 :=
        hgeom.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
      have hRsmall : R n ξ ≤ K * (δn n) ^ 2 := by
        have habs : |R n ξ / (δn n) ^ 2| ≤ K := not_lt.mp hB
        rw [abs_of_nonneg (div_nonneg (hR_nonneg n ξ) (sq_nonneg _))] at habs
        exact (div_le_iff₀ (sq_pos_of_pos (hδn n))).mp habs
      have hKpow : 4 * K ≤ (2 : ℝ) ^ (2 * j) := by
        exact (le_of_lt hJs).trans (pow_le_pow_right₀ (by norm_num)
          (show Js ≤ 2 * j by omega))
      have hRshell : R n ξ ≤ (1 / 4 : ℝ) * ((2 : ℝ) ^ j * δn n) ^ 2 := by
        calc
          R n ξ ≤ K * (δn n) ^ 2 := hRsmall
          _ ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (2 * j) * (δn n) ^ 2 := by nlinarith
          _ = (1 / 4 : ℝ) * ((2 : ℝ) ^ j * δn n) ^ 2 := by
            rw [mul_pow, ← pow_mul]; ring
      have hdet' := hdet n (θhat n ξ) hS.1 (ηhat n ξ) hS.2
      have hnear := hNearMax n ξ
      let xs : Fin (n + 1) → Ω := fun i => X i.val ξ
      let g : Ω → ℝ := fun ω => m (θhat n ξ) (ηhat n ξ) ω - m θ₀ (ηhat n ξ) ω
      let c : ℝ := ∫ ω, g ω ∂P
      let gc : Ω → ℝ := fun ω => g ω - c
      have hg_int : Integrable g P := by
        refine ⟨((hm_meas (θhat n ξ) (ηhat n ξ)).sub
          (hm_meas θ₀ (ηhat n ξ))).aestronglyMeasurable, ?_⟩
        exact (hm_int n (θhat n ξ) hS.1 (ηhat n ξ) hS.2).hasFiniteIntegral
      have hgc_mean : ∫ ω, gc ω ∂P = 0 := by
        dsimp [gc]
        rw [integral_sub hg_int (integrable_const c), integral_const, probReal_univ,
          one_smul]
        dsimp [c]
        ring
      have hc_avg : empiricalAvg (fun _ : Ω => c) (n + 1) xs = c := by
        unfold empiricalAvg
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      have hgc_avg : empiricalAvg gc (n + 1) xs = empiricalAvg g (n + 1) xs - c := by
        calc
          empiricalAvg gc (n + 1) xs = empiricalAvg g (n + 1) xs -
              empiricalAvg (fun _ : Ω => c) (n + 1) xs := by
            dsimp [gc]
            unfold empiricalAvg
            rw [Finset.sum_sub_distrib, mul_sub]
          _ = empiricalAvg g (n + 1) xs - c := by rw [hc_avg]
      have hcenter : empiricalProcess P (n + 1) xs gc = empiricalProcess P (n + 1) xs g := by
        dsimp [gc]
        rw [empiricalProcess_sub P (n + 1) xs g (fun _ => c) hg_int
          (integrable_const c)]
        have hc_ep : empiricalProcess P (n + 1) xs (fun _ => c) = 0 := by
          unfold empiricalProcess
          rw [hc_avg, integral_const, probReal_univ, one_smul, sub_self, mul_zero]
        rw [hc_ep, sub_zero]
      have havg : empiricalAvg g (n + 1) xs =
          nuisanceEmpiricalCriterion m X n ξ (θhat n ξ) (ηhat n ξ) -
            nuisanceEmpiricalCriterion m X n ξ θ₀ (ηhat n ξ) := by
        dsimp [g, xs]
        unfold nuisanceEmpiricalCriterion empiricalAvg
        rw [Finset.sum_sub_distrib, mul_sub]
      have hproc : t ≤ nuisanceCenteredProcess P m X θ₀ n ξ (θhat n ξ) (ηhat n ξ) -
          Real.sqrt ((n + 1 : ℕ) : ℝ) * e n (θhat n ξ) (ηhat n ξ) := by
        unfold nuisanceCenteredProcess
        change t ≤ empiricalProcess P (n + 1) xs g -
          Real.sqrt ((n + 1 : ℕ) : ℝ) * e n (θhat n ξ) (ηhat n ξ)
        rw [← hcenter, empiricalProcess, hgc_avg, hgc_mean, sub_zero, havg]
        have hsqrt : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
        have hdlo : ((2 : ℝ) ^ j * δn n) ^ 2 ≤
            (dΘ n (θhat n ξ) θ₀ : ℝ) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (pow_nonneg (by norm_num) _) (hδn n).le) hlo 2
        dsimp [t, c, g]
        nlinarith [hdHsq, hRshell, hdet', hnear]
      exact le_trans (ENNReal.ofReal_le_ofReal (hproc.trans (le_abs_self _)))
        (le_iSup_of_le ⟨θhat n ξ, hS.1, by simpa [D] using hup⟩
          (le_iSup_of_le ⟨ηhat n ξ, hS.2⟩ le_rfl))
    have hφ : φ n D ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * (δn n) ^ 2 *
        Real.rpow 2 (((j + 1 : ℕ) : ℝ) * β) := by
      have hδD : δn n ≤ D := by
        rw [show δn n = 1 * δn n by ring, show D = (2 : ℝ) ^ (j + 1) * δn n by rfl]
        exact mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (hδn n).le
      have hr := hφanti n (hδn n) hD hδD
      have hpδ := Real.rpow_pos_of_pos (hδn n) β
      have hpD := Real.rpow_pos_of_pos hD β
      have h1 : φ n D ≤ (φ n (δn n) / Real.rpow (δn n) β) * Real.rpow D β :=
        (div_le_iff₀ hpD).mp hr
      calc
        φ n D ≤ (Real.sqrt ((n + 1 : ℕ) : ℝ) * (δn n) ^ 2 /
            Real.rpow (δn n) β) * Real.rpow D β := h1.trans (by
              gcongr
              exact hbalance n)
        _ = Real.sqrt ((n + 1 : ℕ) : ℝ) * (δn n) ^ 2 *
            Real.rpow 2 (((j + 1 : ℕ) : ℝ) * β) := by
          rw [show D = (2 : ℝ) ^ (j + 1) * δn n by rfl]
          have hmul : Real.rpow ((2 : ℝ) ^ (j + 1) * δn n) β =
              Real.rpow ((2 : ℝ) ^ (j + 1)) β * Real.rpow (δn n) β := by
            change (((2 : ℝ) ^ (j + 1) * δn n) ^ β) =
              ((2 : ℝ) ^ (j + 1)) ^ β * (δn n) ^ β
            exact Real.mul_rpow (by positivity) (hδn n).le
          rw [hmul, show Real.rpow ((2 : ℝ) ^ (j + 1)) β =
              Real.rpow 2 (((j + 1 : ℕ) : ℝ) * β) by
            rw [show (2 : ℝ) ^ (j + 1) = Real.rpow 2 (((j + 1 : ℕ) : ℝ)) from
              (Real.rpow_natCast 2 (j + 1)).symm]
            exact (Real.rpow_mul (x := (2 : ℝ)) (by norm_num) _ _).symm]
          field_simp [hpδ.ne']
    have hratio : Real.rpow 2 (((j + 1 : ℕ) : ℝ) * β) /
        ((1 / 2 : ℝ) * ((2 : ℝ) ^ j) ^ 2) = Cβ * q ^ j := by
      dsimp [Cβ, q]
      change ((2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * β)) /
          ((1 / 2 : ℝ) * ((2 : ℝ) ^ j) ^ 2) =
        (2 * (2 : ℝ) ^ β) * (((2 : ℝ) ^ (β - 2)) ^ j)
      rw [show (((j + 1 : ℕ) : ℝ) * β) = β + (j : ℝ) * β by push_cast; ring,
        Real.rpow_add (x := (2 : ℝ)) (by norm_num)]
      have hj2 : ((2 : ℝ) ^ j) ^ 2 = Real.rpow 2 ((j : ℝ) * 2) := by
        calc
          ((2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ (j * 2) := by rw [pow_mul]
          _ = Real.rpow 2 (((j * 2 : ℕ) : ℝ)) := (Real.rpow_natCast 2 (j * 2)).symm
          _ = Real.rpow 2 ((j : ℝ) * 2) := by norm_num
      rw [hj2]
      change (Real.rpow 2 β * Real.rpow 2 ((j : ℝ) * β)) /
          (1 / 2 * Real.rpow 2 ((j : ℝ) * 2)) =
        2 * Real.rpow 2 β * (Real.rpow 2 (β - 2)) ^ j
      have hs : Real.rpow 2 ((j : ℝ) * β) / Real.rpow 2 ((j : ℝ) * 2) =
          Real.rpow 2 ((j : ℝ) * (β - 2)) := by
        change ((2 : ℝ) ^ ((j : ℝ) * β)) / ((2 : ℝ) ^ ((j : ℝ) * 2)) =
          (2 : ℝ) ^ ((j : ℝ) * (β - 2))
        rw [← Real.rpow_sub (x := (2 : ℝ)) (by norm_num)]
        congr 1; ring
      have hm : Real.rpow 2 ((j : ℝ) * (β - 2)) = (Real.rpow 2 (β - 2)) ^ j := by
        calc
          Real.rpow 2 ((j : ℝ) * (β - 2)) = Real.rpow 2 ((β - 2) * (j : ℝ)) := by
            congr 1; ring
          _ = (Real.rpow 2 (β - 2)) ^ (j : ℝ) := Real.rpow_mul (x := (2 : ℝ)) (by norm_num) _ _
          _ = (Real.rpow 2 (β - 2)) ^ j := Real.rpow_natCast _ _
      rw [show (Real.rpow 2 β * Real.rpow 2 ((j : ℝ) * β)) /
          (1 / 2 * Real.rpow 2 ((j : ℝ) * 2)) =
          2 * Real.rpow 2 β *
            (Real.rpow 2 ((j : ℝ) * β) / Real.rpow 2 ((j : ℝ) * 2)) by
          field_simp, hs, hm]
    calc
      μ.outerMeasureStar (Sh j) ≤ μ.outerMeasureStar {ξ | ENNReal.ofReal t ≤ Z ξ} :=
        outerMeasureStar_mono μ hincl
      _ ≤ outerExpectation μ Z / ENNReal.ofReal t :=
        outerExpectation_markov _ (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (φ n D) / ENNReal.ofReal t :=
        ENNReal.div_le_div_right (hmod n D hD) _
      _ ≤ ENNReal.ofReal (Real.sqrt ((n + 1 : ℕ) : ℝ) * (δn n) ^ 2 *
          Real.rpow 2 (((j + 1 : ℕ) : ℝ) * β)) / ENNReal.ofReal t :=
        ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hφ) _
      _ = ENNReal.ofReal (Cβ * q ^ j) := by
        rw [← ENNReal.ofReal_div_of_pos ht]
        congr 1
        dsimp [t]
        calc
          (Real.sqrt ((n + 1 : ℕ) : ℝ) * (δn n) ^ 2 *
              Real.rpow 2 (((j + 1 : ℕ) : ℝ) * β)) /
              (Real.sqrt ((n + 1 : ℕ) : ℝ) / 2 * ((2 : ℝ) ^ j * δn n) ^ 2) =
              Real.rpow 2 (((j + 1 : ℕ) : ℝ) * β) /
                ((1 / 2 : ℝ) * ((2 : ℝ) ^ j) ^ 2) := by
            field_simp [hsqrt.ne', (hδn n).ne']
          _ = Cβ * q ^ j := hratio
  have hcover : A ⊆ Sᶜ ∪ (B ∪ ⋃ k, Sh (J + k)) := by
    intro ξ hA
    by_cases hS : ξ ∈ S
    · by_cases hB : ξ ∈ B
      · exact Or.inr (Or.inl hB)
      · right; right
        have hv : 1 ≤ (dΘ n (θhat n ξ) θ₀ : ℝ) / δn n := by
          rw [le_div_iff₀ (hδn n)]
          exact (mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
            (hδn n).le).trans (le_of_lt (lt_of_le_of_lt
              (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (NNReal.coe_nonneg _))
                (by positivity)) hA))
        obtain ⟨j, hjlo, hjup⟩ := exists_nat_pow_near hv (by norm_num : (1 : ℝ) < 2)
        have hJj : J ≤ j := by
          by_contra hh
          have hjJ : j < J := Nat.lt_of_not_ge hh
          have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J :=
            pow_le_pow_right₀ (by norm_num) (Nat.succ_le_iff.mpr hjJ)
          have hAj : (2 : ℝ) ^ J < (dΘ n (θhat n ξ) θ₀ : ℝ) / δn n := by
            rw [lt_div_iff₀ (hδn n)]
            exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (NNReal.coe_nonneg _)) (by positivity)) hA
          linarith
        refine Set.mem_iUnion.mpr ⟨j - J, ?_⟩
        rw [show J + (j - J) = j by omega]
        refine ⟨⟨⟨hA, hS⟩, hB⟩, ?_, ?_⟩
        · rwa [le_div_iff₀ (hδn n)] at hjlo
        · rwa [div_lt_iff₀ (hδn n)] at hjup
    · exact Or.inl hS
  have hseries : ∑' k : ℕ, Cβ * q ^ (J + k) = Cβ * q ^ J / (1 - q) := by
    rw [show (fun k : ℕ => Cβ * q ^ (J + k)) = fun k => (Cβ * q ^ J) * q ^ k by
      funext k; rw [pow_add]; ring, tsum_mul_left,
      tsum_geometric_of_lt_one hq0.le hq1, div_eq_mul_inv]
  have hsummable : Summable (fun k : ℕ => Cβ * q ^ (J + k)) := by
    simpa [pow_add, mul_assoc] using
      (summable_geometric_of_lt_one hq0.le hq1).mul_left (Cβ * q ^ J)
  have hUnion : μ.outerMeasureStar (⋃ k, Sh (J + k)) ≤ ENNReal.ofReal (γ / 4) := by
    calc
      μ.outerMeasureStar (⋃ k, Sh (J + k)) = μ (⋃ k, Sh (J + k)) :=
        outerMeasureStar_eq_measure_all μ _
      _ ≤ ∑' k, μ (Sh (J + k)) := measure_iUnion_le _
      _ = ∑' k, μ.outerMeasureStar (Sh (J + k)) := by
        congr 1; funext k; rw [outerMeasureStar_eq_measure_all]
      _ ≤ ∑' k, ENNReal.ofReal (Cβ * q ^ (J + k)) :=
        ENNReal.tsum_le_tsum fun k => hshell (J + k) (Nat.le_add_right _ _)
      _ = ENNReal.ofReal (∑' k, Cβ * q ^ (J + k)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun k => mul_nonneg hCβ.le (pow_nonneg hq0.le _)) hsummable).symm
      _ = ENNReal.ofReal (Cβ * q ^ J / (1 - q)) := by rw [hseries]
      _ ≤ ENNReal.ofReal (γ / 4) := ENNReal.ofReal_le_ofReal hsumJ.le
  have hsub := outerMeasureStar_mono μ hcover
  rw [show {ξ | (2 : ℝ) ^ J * (δn n + (dH (ηhat n ξ) η₀ : ℝ)) <
      |(dΘ n (θhat n ξ) θ₀ : ℝ)|} = A by
    ext ξ; simp only [Set.mem_setOf_eq, A, abs_of_nonneg (NNReal.coe_nonneg _)]]
  calc
    μ.outerMeasureStar A ≤ μ.outerMeasureStar (Sᶜ ∪ (B ∪ ⋃ k, Sh (J + k))) := hsub
    _ ≤ μ.outerMeasureStar Sᶜ + (μ.outerMeasureStar B +
        μ.outerMeasureStar (⋃ k, Sh (J + k))) :=
      (outerMeasureStar_union_le μ _ _).trans (add_le_add le_rfl (outerMeasureStar_union_le μ _ _))
    _ ≤ ENNReal.ofReal (γ / 4) + (ENNReal.ofReal (γ / 4) + ENNReal.ofReal (γ / 4)) :=
      add_le_add (le_of_lt (hNm n (le_trans (le_max_left _ _) hn)))
        (add_le_add (le_of_lt (hNK n (le_trans (le_max_right _ _) hn))) hUnion)
    _ ≤ ENNReal.ofReal γ := by
      have hγ4 : 0 ≤ γ / 4 := (div_pos hγ (by norm_num)).le
      have hγ8 : 0 ≤ γ / 4 + γ / 4 := add_nonneg hγ4 hγ4
      calc
        ENNReal.ofReal (γ / 4) +
            (ENNReal.ofReal (γ / 4) + ENNReal.ofReal (γ / 4)) =
            ENNReal.ofReal (γ / 4) + ENNReal.ofReal (γ / 4 + γ / 4) :=
          congrArg (ENNReal.ofReal (γ / 4) + ·) (ENNReal.ofReal_add hγ4 hγ4).symm
        _ = ENNReal.ofReal (γ / 4 + (γ / 4 + γ / 4)) :=
          (ENNReal.ofReal_add hγ4 hγ8).symm
        _ ≤ ENNReal.ofReal γ := ENNReal.ofReal_le_ofReal (by linarith)

/-- Outer-probability assembly of vdV Theorem 5.55. -/
theorem mEstimator_nuisance_rate_outer
    {Ω Θ H Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (m : Θ → H → Ω → ℝ) (θ₀ : Θ) (η₀ : H)
    -- The criterion functions are measurable.
    (hm_meas : ∀ θ η, Measurable (m θ η))
    (X : ℕ → Ξ → Ω)
    (Θn : ℕ → Set Θ) (Hn : ℕ → Set H)
    -- Integrability on the same local domain as the drift and modulus bounds.
    (hm_int : ∀ n θ, θ ∈ Θn n → ∀ η, η ∈ Hn n →
      Integrable (fun ω => m θ η ω - m θ₀ η ω) P)
    (dΘ : ℕ → Θ → Θ → NNReal) (dH : H → H → NNReal)
    (e : ℕ → Θ → H → ℝ) (φ : ℕ → ℝ → ℝ)
    (β : ℝ) (hβ : β < 2)
    (hφanti : ∀ n, AntitoneOn (fun δ => φ n δ / Real.rpow δ β) (Set.Ioi 0))
    (δn : ℕ → ℝ) (hδn : ∀ n, 0 < δn n)
    (hbalance : ∀ n, φ n (δn n) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * (δn n) ^ 2)
    (hdet : ∀ n θ, θ ∈ Θn n → ∀ η, η ∈ Hn n →
      (∫ ω, (m θ η ω - m θ₀ η ω) ∂P) + e n θ η ≤
        -(dΘ n θ θ₀ : ℝ) ^ 2 + (dH η η₀ : ℝ) ^ 2)
    (hmod : ∀ n δ, 0 < δ →
      outerExpectation μ (fun ξ =>
        ⨆ θ : {θ : Θ // θ ∈ Θn n ∧ (dΘ n θ θ₀ : ℝ) < δ},
          ⨆ η : {η : H // η ∈ Hn n}, ENNReal.ofReal
            |nuisanceCenteredProcess P m X θ₀ n ξ θ.1 η.1 -
                Real.sqrt ((n + 1 : ℕ) : ℝ) * e n θ.1 η.1|) ≤
        ENNReal.ofReal (φ n δ))
    (θhat : ℕ → Ξ → Θ) (ηhat : ℕ → Ξ → H)
    (hmem : TendstoInnerProbOne μ (fun n =>
      {ξ | θhat n ξ ∈ Θn n ∧ ηhat n ξ ∈ Hn n}))
    (R : ℕ → Ξ → ℝ) (hR_nonneg : ∀ n ξ, 0 ≤ R n ξ)
    (hNearMax : ∀ n ξ,
      nuisanceEmpiricalCriterion m X n ξ (θhat n ξ) (ηhat n ξ) ≥
        nuisanceEmpiricalCriterion m X n ξ θ₀ (ηhat n ξ) - R n ξ)
    -- Outer-probability form of the estimate.
    (hR : IsBoundedInOuterProbScalar μ (fun n ξ => R n ξ / (δn n) ^ 2)) :
    IsBoundedInOuterProbScalarWt μ
      (fun n ξ => δn n + (dH (ηhat n ξ) η₀ : ℝ))
      (fun n ξ => (dΘ n (θhat n ξ) θ₀ : ℝ)) := by
  intro γ hγ
  obtain ⟨M, N, hN⟩ := nuisanceRate_shell_tail P μ m θ₀ η₀ hm_meas X Θn Hn hm_int
    dΘ dH e φ β hβ hφanti δn hδn hbalance hdet hmod
    θhat ηhat hmem R hR_nonneg hNearMax hR γ hγ
  refine ⟨M, ?_⟩
  calc
    limsup (fun n => μ.outerMeasureStar { ξ |
        M * (δn n + (dH (ηhat n ξ) η₀ : ℝ)) < |(dΘ n (θhat n ξ) θ₀ : ℝ)|}) atTop
        ≤ limsup (fun _ : ℕ => ENNReal.ofReal γ) atTop :=
      limsup_le_limsup (eventually_atTop.mpr ⟨N, hN⟩) isCobounded_le_of_bot
        (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ = ENNReal.ofReal γ := limsup_const _

/-- **vdV Theorem 5.55 (rate with a nuisance parameter).**
it assumes neither a nuisance rate nor the conclusion rate. -/
theorem mEstimator_nuisance_rate
    {Ω Θ H Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (m : Θ → H → Ω → ℝ) (θ₀ : Θ) (η₀ : H)
    -- LEAN-ONLY: measurability of the criterion functions.
    (hm_meas : ∀ θ η, Measurable (m θ η))
    (X : ℕ → Ξ → Ω)
    (Θn : ℕ → Set Θ) (Hn : ℕ → Set H)
    -- LEAN-ONLY: integrability on the local parameter sets.
    (hm_int : ∀ n θ, θ ∈ Θn n → ∀ η, η ∈ Hn n →
      Integrable (fun ω => m θ η ω - m θ₀ η ω) P)
    (dΘ : ℕ → Θ → Θ → NNReal) (dH : H → H → NNReal)
    (e : ℕ → Θ → H → ℝ) (φ : ℕ → ℝ → ℝ)
    -- USER-INPUT: rate exponent, modulus monotonicity, and balancing sequence;
    -- vdV Theorem 5.55.
    (β : ℝ) (hβ : β < 2)
    (hφanti : ∀ n, AntitoneOn (fun δ => φ n δ / Real.rpow δ β) (Set.Ioi 0))
    (δn : ℕ → ℝ) (hδn : ∀ n, 0 < δn n)
    (hbalance : ∀ n, φ n (δn n) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * (δn n) ^ 2)
    -- USER-INPUT: deterministic drift and empirical-process modulus bounds;
    -- vdV Theorem 5.55.
    (hdet : ∀ n θ, θ ∈ Θn n → ∀ η, η ∈ Hn n →
      (∫ ω, (m θ η ω - m θ₀ η ω) ∂P) + e n θ η ≤
        -(dΘ n θ θ₀ : ℝ) ^ 2 + (dH η η₀ : ℝ) ^ 2)
    (hmod : ∀ n δ, 0 < δ →
      outerExpectation μ (fun ξ =>
        ⨆ θ : {θ : Θ // θ ∈ Θn n ∧ (dΘ n θ θ₀ : ℝ) < δ},
          ⨆ η : {η : H // η ∈ Hn n}, ENNReal.ofReal
            |nuisanceCenteredProcess P m X θ₀ n ξ θ.1 η.1 -
                Real.sqrt ((n + 1 : ℕ) : ℝ) * e n θ.1 η.1|) ≤
        ENNReal.ofReal (φ n δ))
    (θhat : ℕ → Ξ → Θ) (ηhat : ℕ → Ξ → H)
    -- USER-INPUT: the estimators eventually lie in the local parameter sets;
    -- vdV Theorem 5.55.
    (hmem : TendstoInnerProbOne μ (fun n =>
      {ξ | θhat n ξ ∈ Θn n ∧ ηhat n ξ ∈ Hn n}))
    (R : ℕ → Ξ → ℝ)
    -- LEAN-ONLY: measurability and a nonnegative representation of the remainder.
    (hR_meas : ∀ n, Measurable (R n))
    (hR_nonneg : ∀ n ξ, 0 ≤ R n ξ)
    -- USER-INPUT: approximate maximization and an `O_P(δₙ²)` remainder;
    -- vdV Theorem 5.55.
    (hNearMax : ∀ n ξ,
      nuisanceEmpiricalCriterion m X n ξ (θhat n ξ) (ηhat n ξ) ≥
        nuisanceEmpiricalCriterion m X n ξ θ₀ (ηhat n ξ) - R n ξ)
    (hR : IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ => R n ξ / (δn n) ^ 2)) :
    IsBoundedInOuterProbScalarWt μ
      (fun n ξ => δn n + (dH (ηhat n ξ) η₀ : ℝ))
      (fun n ξ => (dΘ n (θhat n ξ) θ₀ : ℝ)) := by
  have hR_outer : IsBoundedInOuterProbScalar μ (fun n ξ => R n ξ / (δn n) ^ 2) := by
    intro γ hγ
    obtain ⟨M, hM⟩ := hR γ hγ
    refine ⟨M, ?_⟩
    have hZ_meas : ∀ n, Measurable (fun ξ => R n ξ / (δn n) ^ 2) :=
      fun n => (hR_meas n).div_const ((δn n) ^ 2)
    have htail_meas : ∀ n, MeasurableSet { ξ | M < |R n ξ / (δn n) ^ 2|} :=
      fun n => measurableSet_lt measurable_const (hZ_meas n).abs
    have hbound : ∀ n, μ.outerMeasureStar { ξ | M < |R n ξ / (δn n) ^ 2|} ≤
        ENNReal.ofReal γ := by
      intro n
      calc
        μ.outerMeasureStar { ξ | M < |R n ξ / (δn n) ^ 2|} =
            μ { ξ | M < |R n ξ / (δn n) ^ 2|} :=
          outerMeasureStar_eq_measure (htail_meas n)
        _ = ENNReal.ofReal (μ.real { ξ | M < |R n ξ / (δn n) ^ 2|}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        _ ≤ ENNReal.ofReal γ := ENNReal.ofReal_le_ofReal (by
          simpa only [Real.norm_eq_abs] using hM n)
    calc
      limsup (fun n => μ.outerMeasureStar { ξ | M < |R n ξ / (δn n) ^ 2|}) atTop ≤
          limsup (fun _ : ℕ => ENNReal.ofReal γ) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      _ = ENNReal.ofReal γ := limsup_const _
  exact mEstimator_nuisance_rate_outer P μ m θ₀ η₀ hm_meas X Θn Hn hm_int
    dΘ dH e φ β hβ hφanti δn hδn hbalance hdet hmod θhat ηhat hmem R hR_nonneg
    hNearMax hR_outer

end AsymptoticStatistics.MEstimator
