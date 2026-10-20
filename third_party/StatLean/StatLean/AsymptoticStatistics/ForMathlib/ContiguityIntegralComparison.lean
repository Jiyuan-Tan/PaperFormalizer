module
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

@[expose] public section

/-!
# Contiguity from asymptotic integral comparison

Le Cam first-lemma formulations for a sequence of probability
experiments whose exponential likelihood weights compare asymptotically with the
second sequence of measures.  Unlike the exact-density interfaces in
`ForMathlib.Contiguity`, these statements require neither an exact Radon--Nikodym
identity nor a common-support assumption.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.Contiguity

private lemma integrable_of_abs_le
    {β : Type*} [MeasurableSpace β] (mu : Measure β) [IsFiniteMeasure mu]
    {f : β → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f mu :=
  ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)⟩

private lemma measureReal_le_lowerTail_add_exp_mul_setIntegral
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (L : S → ℝ) (hL : Measurable L) (h_exp : Integrable (fun ω => Real.exp (L ω)) P)
    (A : Set S) (hA : MeasurableSet A) (K : ℝ) :
    P.real A ≤ P.real {ω | L ω ≤ -K} + Real.exp K * ∫ ω in A, Real.exp (L ω) ∂P := by
  let B : Set S := A ∩ {ω | -K < L ω}
  have hB : MeasurableSet B := hA.inter (measurableSet_lt measurable_const hL)
  have hcover : A ⊆ {ω | L ω ≤ -K} ∪ B := by
    intro ω hω
    by_cases hlow : L ω ≤ -K
    · exact Or.inl hlow
    · exact Or.inr ⟨hω, lt_of_not_ge hlow⟩
  have hB_bound : P.real B ≤ Real.exp K * ∫ ω in A, Real.exp (L ω) ∂P := by
    calc
      P.real B = ∫ _ in B, (1 : ℝ) ∂P := by rw [setIntegral_const]; simp
      _ ≤ ∫ ω in B, Real.exp K * Real.exp (L ω) ∂P := by
        refine setIntegral_mono_on (integrable_const 1).restrict
          (h_exp.const_mul (Real.exp K)).restrict hB (fun ω hω => ?_)
        rw [← Real.exp_add]
        exact Real.one_le_exp (by
          have := hω.2
          change -K < L ω at this
          linarith)
      _ = Real.exp K * ∫ ω in B, Real.exp (L ω) ∂P := by rw [integral_const_mul]
      _ ≤ Real.exp K * ∫ ω in A, Real.exp (L ω) ∂P := by
        exact mul_le_mul_of_nonneg_left
          (setIntegral_mono_set (s := B) (t := A) h_exp.restrict
            (Eventually.of_forall fun ω => (Real.exp_pos _).le)
            (Eventually.of_forall fun _ hω => hω.1)) (Real.exp_pos K).le
  exact (measureReal_mono hcover).trans <|
    (measureReal_union_le _ _).trans (add_le_add (le_refl _) hB_bound)

private lemma eventually_measureReal_lowerTail_lt_of_weakConverges
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (L : ∀ n, Ω n → ℝ) (hL : ∀ n, Measurable (L n))
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hweak : WeakConverges (fun n => (P n).map (L n)) nu) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ᶠ n in atTop, (P n).real {ω | L n ω ≤ -(K : ℝ)} < ε := by
  let pn : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(P n).map (L n), Measure.isProbabilityMeasure_map (hL n).aemeasurable⟩
  let pnu : ProbabilityMeasure ℝ := ⟨nu, inferInstance⟩
  have ht : Tendsto pn atTop (nhds pnu) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak
  let C : ℕ → Set ℝ := fun K => Set.Iic (-(K : ℝ))
  have hCmeas : ∀ K, MeasurableSet (C K) := fun _ => measurableSet_Iic
  have hCanti : Antitone C := by
    intro a b hab x hx
    simp only [C, Set.mem_Iic] at hx ⊢
    exact hx.trans (neg_le_neg (by exact_mod_cast hab : (a : ℝ) ≤ (b : ℝ)))
  have hCinter : ⋂ K, C K = (∅ : Set ℝ) := by
    ext x
    simp only [C, Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
      not_forall, not_le]
    obtain ⟨K, hK⟩ := exists_nat_gt (-x)
    exact ⟨K, by linarith⟩
  have htail : Tendsto (fun K => nu (C K)) atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop (μ := nu) (fun K => (hCmeas K).nullMeasurableSet)
      hCanti ⟨0, measure_ne_top nu _⟩
    simpa [hCinter] using! h
  obtain ⟨K, hK⟩ := (htail.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto ht
    (isClosed_Iic : IsClosed (C K))
  have hlim : limsup (fun n => (P n) {ω | L n ω ≤ -(K : ℝ)}) atTop < ENNReal.ofReal ε := by
    calc
      _ = limsup (fun n => (pn n : Measure ℝ) (C K)) atTop := by
        apply limsup_congr
        exact Eventually.of_forall fun n => by
          change (P n) ((L n) ⁻¹' C K) = ((P n).map (L n)) (C K)
          exact (Measure.map_apply (hL n) (hCmeas K)).symm
      _ ≤ (pnu : Measure ℝ) (C K) := hport
      _ < ENNReal.ofReal ε := hK
  have hev := eventually_lt_of_limsup_lt hlim
  refine ⟨K, hev.mono (fun n hn => ?_)⟩
  simpa [Measure.real, ENNReal.toReal_ofReal hε.le] using
    (ENNReal.toReal_lt_toReal (measure_ne_top (P n) _) ENNReal.ofReal_ne_top).mpr hn

/-- **Forward contiguity from asymptotic log-normality and event-integral comparison.**

If the laws of `L n` under `P n` converge weakly to `N(-v/2, v)`, the exponential
weights have asymptotic mass one, and their integrals over every measurable event
approximate the corresponding `Q n` probabilities with a uniform vanishing error,
then `Q` is contiguous with respect to `P`.

The proof route is the usual truncated-exponential uniform-integrability argument;
the comparison error is added after bounding the weighted event integral.
-/
theorem contiguous_of_asymptotically_log_normal_of_integral_comparison
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    -- the reference sequence of probability measures.
    (P : ∀ n, Measure (Ω n))
    -- the comparison sequence of probability measures.
    (Q : ∀ n, Measure (Ω n))
    -- both sequences consist of probability measures.
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    -- the supplied asymptotic log-likelihood statistic.
    (L : ∀ n, Ω n → ℝ)
    -- measurability of the supplied log statistic.
    (hL_meas : ∀ n, Measurable (L n))
    -- exponential weights are integrable at every sample size.
    (h_exp_int : ∀ n, Integrable (fun ω => Real.exp (L n ω)) (P n))
    -- the exponential weights have asymptotic total mass one.
    (h_mass : Tendsto (fun n => ∫ ω, Real.exp (L n ω) ∂(P n)) atTop (𝓝 1))
    -- uniform measurable-event comparison with vanishing error.
    (h_integral_comparison : ∃ ρ : ℕ → ℝ,
      Tendsto ρ atTop (𝓝 0) ∧
      ∀ A : ∀ n, Set (Ω n), (∀ n, MeasurableSet (A n)) → ∀ n,
        |(Q n).real (A n) - ∫ ω in A n, Real.exp (L n ω) ∂(P n)| ≤ ρ n)
    -- variance parameter of the limiting log-normal experiment.
    (v : NNReal)
    -- asymptotic log-normality under the reference measures.
    (h_weak : WeakConverges (fun n => (P n).map (L n))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    Contiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  intro A hA hPA
  obtain ⟨ρ, hρ, hcomp⟩ := h_integral_comparison
  have hPA_real : Tendsto (fun n => (P n).real (A n)) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff fun n => measure_ne_top (P n) _).mpr hPA
  let I : ℕ → ℝ := fun n => ∫ ω in A n, Real.exp (L n ω) ∂(P n)
  have hI : Tendsto I atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM, N₁, hN₁⟩ :=
      uniform_integrability_exp_L_of_integral_tendsto_one P Q L hL_meas h_exp_int
        h_mass v h_weak (ε / 2) (by linarith)
    have hPA_ev := (Metric.tendsto_nhds.mp hPA_real)
      (ε / (2 * (M + 1))) (by positivity)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hPA_ev
    refine eventually_atTop.mpr ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn₁ : N₁ ≤ n := le_of_max_le_left hn
    have hn₂ : N₂ ≤ n := le_of_max_le_right hn
    have hmin : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
      refine (h_exp_int n).mono' (((Real.continuous_exp.measurable.comp
        (hL_meas n)).min measurable_const).aestronglyMeasurable) ?_
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hM)]
      exact min_le_left _ _
    have hres := (h_exp_int n).sub hmin
    have hres_nn : 0 ≤ᵐ[P n] fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M :=
      Eventually.of_forall fun ω => sub_nonneg.mpr (min_le_left _ _)
    have hdecomp : I n =
        ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n) +
          ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) := by
      change (∫ ω in A n, Real.exp (L n ω) ∂(P n)) = _
      calc
        _ = ∫ ω in A n, min (Real.exp (L n ω)) M +
            (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun ω => by ring
        _ = _ := integral_add hmin.restrict hres.restrict
    have hmin_bound : ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n) ≤
        M * (P n).real (A n) := by
      calc
        _ ≤ ∫ _ in A n, M ∂(P n) :=
          setIntegral_mono_on hmin.restrict (integrable_const M).restrict (hA n)
            (fun _ _ => min_le_right _ _)
        _ = _ := by rw [setIntegral_const]; simp [smul_eq_mul, mul_comm]
    have hres_bound : ∫ ω in A n,
        Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε / 2 :=
      (setIntegral_le_integral hres hres_nn).trans (hN₁ n hn₁)
    have hPsmall : (P n).real (A n) < ε / (2 * (M + 1)) := by
      simpa [Real.dist_eq, abs_of_nonneg measureReal_nonneg] using hN₂ n hn₂
    have hInn : 0 ≤ I n := integral_nonneg_of_ae <|
      ae_restrict_of_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hInn]
    rw [hdecomp]
    have hMratio : M * (ε / (2 * (M + 1))) ≤ ε / 2 := by
      have : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      calc
        _ = (M / (M + 1)) * (ε / 2) := by field_simp
        _ ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right this (by linarith)
        _ = _ := one_mul _
    rcases hM.eq_or_lt with rfl | hMpos
    · linarith
    · have := mul_lt_mul_of_pos_left hPsmall hMpos
      linarith
  have hQ_real : Tendsto (fun n => (Q n).real (A n)) atTop (nhds 0) := by
    have hupper : Tendsto (fun n => I n + ρ n) atTop (nhds 0) := by
      simpa using hI.add hρ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      hupper (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    exact Eventually.of_forall fun n => by
      have hb := (abs_le.mp (hcomp A hA n)).2
      dsimp [I]
      linarith
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top (Q n) (A n))).mp hQ_real

/-- **Reverse contiguity from a lower-tail bound and event-integral comparison.**

Under the same log-normal weak limit and measurable-event comparison, `P` is
contiguous with respect to `Q`.  For fixed `K > 0`, split an event according to
`L ≤ -K` and use
`P(A) ≤ P(L ≤ -K) + exp K * ∫_A exp L dP`.  Portmanteau controls the closed
left tail, while the comparison and `Q(A) → 0` control the weighted integral.

This direction does not need exponential integrability or a separate total-mass
limit, so those forward-only assumptions are deliberately absent.
-/
theorem reverse_contiguous_of_asymptotically_log_normal_of_integral_comparison
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    -- the reference sequence of probability measures.
    (P : ∀ n, Measure (Ω n))
    -- the comparison sequence of probability measures.
    (Q : ∀ n, Measure (Ω n))
    -- both sequences consist of probability measures.
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    -- the supplied asymptotic log-likelihood statistic.
    (L : ∀ n, Ω n → ℝ)
    -- measurability of the supplied log statistic.
    (hL_meas : ∀ n, Measurable (L n))
    -- uniform measurable-event comparison with vanishing error.
    (h_integral_comparison : ∃ ρ : ℕ → ℝ,
      Tendsto ρ atTop (𝓝 0) ∧
      ∀ A : ∀ n, Set (Ω n), (∀ n, MeasurableSet (A n)) → ∀ n,
        |(Q n).real (A n) - ∫ ω in A n, Real.exp (L n ω) ∂(P n)| ≤ ρ n)
    -- variance parameter of the limiting log-normal experiment.
    (v : NNReal)
    -- asymptotic log-normality under the reference measures.
    (h_weak : WeakConverges (fun n => (P n).map (L n))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    Contiguous (ι := ℕ) (Ω := Ω) atTop Q P := by
  intro A hA hQA
  obtain ⟨ρ, hρ, hcomp⟩ := h_integral_comparison
  have hQA_real : Tendsto (fun n => (Q n).real (A n)) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff fun n => measure_ne_top (Q n) _).mpr hQA
  have h_exp_ev : ∀ᶠ n in atTop, Integrable (fun ω => Real.exp (L n ω)) (P n) := by
    let U : ∀ n, Set (Ω n) := fun _ => Set.univ
    have hU := hcomp U (fun _ => MeasurableSet.univ)
    filter_upwards [hρ.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    by_contra hnot
    have hz : ∫ ω, Real.exp (L n ω) ∂(P n) = 0 := integral_undef hnot
    have hb := hU n
    simp only [U, probReal_univ, setIntegral_univ, hz, sub_zero, abs_one] at hb
    linarith
  let I : ℕ → ℝ := fun n => ∫ ω in A n, Real.exp (L n ω) ∂(P n)
  have hI : Tendsto I atTop (nhds 0) := by
    have hupper : Tendsto (fun n => (Q n).real (A n) + ρ n) atTop (nhds 0) := by
      simpa using hQA_real.add hρ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      hupper ?_ ?_
    · exact h_exp_ev.mono fun n hn => integral_nonneg_of_ae <|
        ae_restrict_of_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le)
    · exact Eventually.of_forall fun n => by
        have hb := (abs_le.mp (hcomp A hA n)).1
        dsimp [I]
        linarith
  apply (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top (P n) (A n))).mp
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, htail⟩ := eventually_measureReal_lowerTail_lt_of_weakConverges
    P L hL_meas (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) h_weak
    (show 0 < ε / 2 by linarith)
  have hscaled_ev : ∀ᶠ n in atTop, Real.exp (K : ℝ) * I n < ε / 2 :=
    (show Tendsto (fun n => Real.exp (K : ℝ) * I n) atTop (nhds 0) from
      by simpa using hI.const_mul (Real.exp (K : ℝ))).eventually
      (Iio_mem_nhds (by linarith))
  filter_upwards [htail, hscaled_ev, h_exp_ev] with n hn_tail hn_I hn_exp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have hbound := measureReal_le_lowerTail_add_exp_mul_setIntegral
    (P n) (L n) (hL_meas n) hn_exp (A n) (hA n) (K : ℝ)
  change (P n).real (A n) < ε
  dsimp [I] at hn_I
  linarith

/-- **Mutual contiguity from asymptotic log-normality and integral comparison.**

Packages the forward truncated-exponential argument and the reverse lower-tail
argument.  The statement is support-free: it assumes only the two probability
sequences, the measurable log statistic, exponential integrability and mass
normalization needed by the forward direction, the vanishing event-comparison
error, and the log-normal weak limit.
-/
theorem mutuallyContiguous_of_asymptotically_log_normal_of_integral_comparison
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    -- the reference sequence of probability measures.
    (P : ∀ n, Measure (Ω n))
    -- the comparison sequence of probability measures.
    (Q : ∀ n, Measure (Ω n))
    -- both sequences consist of probability measures.
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    -- the supplied asymptotic log-likelihood statistic.
    (L : ∀ n, Ω n → ℝ)
    -- measurability of the supplied log statistic.
    (hL_meas : ∀ n, Measurable (L n))
    -- exponential weights are integrable at every sample size.
    (h_exp_int : ∀ n, Integrable (fun ω => Real.exp (L n ω)) (P n))
    -- the exponential weights have asymptotic total mass one.
    (h_mass : Tendsto (fun n => ∫ ω, Real.exp (L n ω) ∂(P n)) atTop (𝓝 1))
    -- uniform measurable-event comparison with vanishing error.
    (h_integral_comparison : ∃ ρ : ℕ → ℝ,
      Tendsto ρ atTop (𝓝 0) ∧
      ∀ A : ∀ n, Set (Ω n), (∀ n, MeasurableSet (A n)) → ∀ n,
        |(Q n).real (A n) - ∫ ω in A n, Real.exp (L n ω) ∂(P n)| ≤ ρ n)
    -- variance parameter of the limiting log-normal experiment.
    (v : NNReal)
    -- asymptotic log-normality under the reference measures.
    (h_weak : WeakConverges (fun n => (P n).map (L n))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    MutuallyContiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  exact ⟨contiguous_of_asymptotically_log_normal_of_integral_comparison
      P Q L hL_meas h_exp_int h_mass h_integral_comparison v h_weak,
    reverse_contiguous_of_asymptotically_log_normal_of_integral_comparison
      P Q L hL_meas h_integral_comparison v h_weak⟩

/-- Le Cam's first lemma when change of measure is given by a uniform asymptotic
comparison of bounded measurable integrals. -/
theorem mutuallyContiguous_of_log_normal_of_integral_comparison
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ)
    (hL_meas : ∀ n, Measurable (L n))
    (h_comparison : ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
      ∀ (g : ∀ n, Ω n → ℝ) (C : ℝ), (∀ n, Measurable (g n)) → 0 ≤ C →
        (∀ n ω, |g n ω| ≤ C) → ∀ n,
        |∫ ω, g n ω ∂(Q n) - ∫ ω, g n ω * Real.exp (L n ω) ∂(P n)| ≤ C * ρ n)
    (v : NNReal)
    (h_weak : WeakConverges (fun n => (P n).map (L n))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    MutuallyContiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  obtain ⟨ρ, hρ_tendsto, hρ⟩ := h_comparison
  have hρ_nonneg : ∀ n, 0 ≤ ρ n := by
    intro n
    have h := hρ (fun _ _ => (0 : ℝ)) 1 (fun _ => measurable_const) zero_le_one
      (fun _ _ => by simp) n
    simpa using h
  have h_ind : ∀ (A : ∀ n, Set (Ω n)), (∀ n, MeasurableSet (A n)) → ∀ n,
      |(Q n).real (A n) - ∫ ω in A n, Real.exp (L n ω) ∂(P n)| ≤ ρ n := by
    intro A hA n
    have hmeas : ∀ m, Measurable ((A m).indicator (fun _ => (1 : ℝ))) :=
      fun m => measurable_const.indicator (hA m)
    have hbnd : ∀ (m : ℕ) (ω : Ω m), |(A m).indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
      intro m ω
      by_cases hω : ω ∈ A m <;> simp [hω]
    have h := hρ (fun m => (A m).indicator (fun _ => (1 : ℝ))) 1 hmeas
      zero_le_one hbnd n
    have hQ : ∫ ω, (A n).indicator (fun _ => (1 : ℝ)) ω ∂(Q n) = (Q n).real (A n) := by
      rw [integral_indicator (hA n), setIntegral_const]
      simp [measureReal_def]
    have hP : ∫ ω, (A n).indicator (fun _ => (1 : ℝ)) ω * Real.exp (L n ω) ∂(P n)
        = ∫ ω in A n, Real.exp (L n ω) ∂(P n) := by
      have hpt : ∀ ω : Ω n,
          (A n).indicator (fun _ => (1 : ℝ)) ω * Real.exp (L n ω) =
            (A n).indicator (fun ω => Real.exp (L n ω)) ω := by
        intro ω
        by_cases hω : ω ∈ A n <;> simp [hω]
      simp_rw [hpt]
      rw [integral_indicator (hA n)]
    simpa only [hQ, hP, one_mul] using h
  have h_trunc_le : ∀ (k n : ℕ),
      ∫ ω, min (Real.exp (L n ω)) (k : ℝ) ∂(P n) ≤ 1 + ρ n := by
    intro k n
    let g : ∀ m, Ω m → ℝ := fun m ω => min 1 ((k : ℝ) * Real.exp (-(L m ω)))
    have hg_meas : ∀ m, Measurable (g m) := fun m =>
      measurable_const.min (measurable_const.mul
        (Real.measurable_exp.comp (hL_meas m).neg))
    have hg_bound : ∀ (m : ℕ) (ω : Ω m), |g m ω| ≤ 1 := by
      intro m ω
      dsimp [g]
      have h0 : (0 : ℝ) ≤ (k : ℝ) * Real.exp (-(L m ω)) :=
        mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
      rw [abs_of_nonneg (le_min zero_le_one h0)]
      exact min_le_left _ _
    have hmul : ∀ ω : Ω n,
        g n ω * Real.exp (L n ω) = min (Real.exp (L n ω)) (k : ℝ) := by
      intro ω
      dsimp [g]
      have ht : 0 < Real.exp (L n ω) := Real.exp_pos _
      rw [Real.exp_neg]
      rcases le_total (1 : ℝ) ((k : ℝ) * (Real.exp (L n ω))⁻¹) with h | h
      · have hk : Real.exp (L n ω) ≤ (k : ℝ) := by
          have := mul_le_mul_of_nonneg_right h ht.le
          rwa [one_mul, inv_mul_cancel_right₀ ht.ne'] at this
        rw [min_eq_left h, one_mul, min_eq_left hk]
      · have hk : (k : ℝ) ≤ Real.exp (L n ω) := by
          have := mul_le_mul_of_nonneg_right h ht.le
          rwa [one_mul, inv_mul_cancel_right₀ ht.ne'] at this
        rw [min_eq_right h, min_eq_right hk, inv_mul_cancel_right₀ ht.ne']
    have hQ_le : ∫ ω, g n ω ∂(Q n) ≤ 1 := by
      have hle := integral_mono
        (integrable_of_abs_le (Q n) (hg_meas n) 1 (hg_bound n))
        (integrable_const (1 : ℝ)) (fun ω => min_le_left _ _)
      simpa [measureReal_def, g] using hle
    have hcmp := hρ g 1 hg_meas zero_le_one hg_bound n
    rw [integral_congr_ae (Eventually.of_forall hmul)] at hcmp
    have habs := (abs_le.mp (by simpa using hcmp)).1
    linarith [hQ_le, hρ_nonneg n]
  have h_exp_int : ∀ n, Integrable (fun ω => Real.exp (L n ω)) (P n) := by
    intro n
    refine ⟨(Real.continuous_exp.measurable.comp (hL_meas n)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ω => (Real.exp_pos (L n ω)).le)]
    have hfun : (fun ω => ENNReal.ofReal (Real.exp (L n ω))) =
        fun ω => ⨆ k : ℕ, ENNReal.ofReal (min (Real.exp (L n ω)) (k : ℝ)) := by
      funext ω
      refine le_antisymm ?_ (iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      refine le_iSup_of_le ⌈Real.exp (L n ω)⌉₊ ?_
      exact le_of_eq (by rw [min_eq_left (Nat.le_ceil _)])
    have hbound : ∫⁻ ω, ENNReal.ofReal (Real.exp (L n ω)) ∂(P n) ≤
        ENNReal.ofReal (1 + ρ n) := by
      rw [hfun, lintegral_iSup]
      · refine iSup_le fun k => ?_
        have hint : Integrable (fun ω => min (Real.exp (L n ω)) (k : ℝ)) (P n) :=
          integrable_of_abs_le (P n)
            ((Real.continuous_exp.measurable.comp (hL_meas n)).min measurable_const) k
            (fun ω => by
              rw [abs_of_nonneg (le_min (Real.exp_pos _).le (Nat.cast_nonneg _))]
              exact min_le_right _ _)
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun ω => le_min (Real.exp_pos _).le (Nat.cast_nonneg _))]
        exact ENNReal.ofReal_le_ofReal (h_trunc_le k n)
      · exact fun k => ENNReal.measurable_ofReal.comp
          ((Real.continuous_exp.measurable.comp (hL_meas n)).min measurable_const)
      · intro a b hab ω
        exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hab))
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have h_mass : Tendsto (fun n => ∫ ω, Real.exp (L n ω) ∂(P n)) atTop (𝓝 1) := by
    have hkey : ∀ n, ‖(∫ ω, Real.exp (L n ω) ∂(P n)) - 1‖ ≤ ρ n := by
      intro n
      have h := hρ (fun _ _ => (1 : ℝ)) 1 (fun _ => measurable_const) zero_le_one
        (fun _ _ => le_of_eq abs_one) n
      rw [Real.norm_eq_abs, abs_sub_comm]
      simpa [measureReal_def] using h
    have h0 : Tendsto (fun n => (∫ ω, Real.exp (L n ω) ∂(P n)) - 1) atTop (𝓝 0) :=
      squeeze_zero_norm hkey hρ_tendsto
    simpa using h0.add (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)))
  exact mutuallyContiguous_of_asymptotically_log_normal_of_integral_comparison
    P Q L hL_meas h_exp_int h_mass ⟨ρ, hρ_tendsto, h_ind⟩ v h_weak

end AsymptoticStatistics.Contiguity
