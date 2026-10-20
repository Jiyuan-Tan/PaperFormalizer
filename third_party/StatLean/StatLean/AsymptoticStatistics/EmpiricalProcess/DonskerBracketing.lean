module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EquicontinuityChaining
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChainingAssembly
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Theorem 19.5: Donsker via bracketing entropy integral

Every class `F` of measurable functions with `J_{[]}(1, F, L_2(P)) < ∞` is
`P`-Donsker. The proof splits `IsPDonsker = IsMarginalCLT ∧
IsAsymptoticallyEquicontinuous`: the marginal-CLT half is provable from
Mathlib's iid CLT; the equicontinuity half derives and consumes the localized
universal-constant bound of Lemma 19.34
(`localizedChainBound_of_finiteEntropy`). The crude, `n`-dependent estimates
in `Maximal.lean` are separate auxiliary results.

vdV §19.2 Theorem 19.5.

Principal declaration: `isPDonsker_of_finite_bracketing_entropy_integral`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Bracket-extraction step for the marginal-CLT half of Theorem 19.5**.

If the bracketing entropy integral `J_{[]}(1, F, L²(P))` is finite, then
there exists at least one scale `ε ∈ (0, 1]` at which the bracketing
number is finite (and hence `F` admits a finite ε-bracketing cover at
that scale).

**Proof.** Contrapositive: if `bracketingNumber ε F 2 P = ⊤` for every
`ε ∈ (0, 1]`, then the integrand of `bracketingEntropyIntegral` is
identically `⊤` on `(0, 1]`, so the lintegral equals `⊤ · volume((0,1])
= ⊤ · 1 = ⊤`, contradicting the finiteness hypothesis. -/
private lemma exists_finite_bracketingNumber_of_integral_lt_top
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) 1 ∧ bracketingNumber ε F 2 P < ⊤ := by
  by_contra h_no
  push Not at h_no
  have h_int_top : bracketingEntropyIntegral 1 F P = ⊤ := by
    unfold bracketingEntropyIntegral
    rw [setLIntegral_congr_fun (μ := volume) (s := Set.Ioc (0:ℝ) 1)
        (g := fun _ => (⊤ : ℝ≥0∞)) measurableSet_Ioc (by
          intro ε hε
          have h_top : bracketingNumber ε F 2 P = ⊤ := top_unique (h_no ε hε)
          simp [h_top])]
    rw [setLIntegral_const, Real.volume_Ioc]
    simp
  rw [h_int_top] at h_int
  exact (lt_irrefl _ h_int).elim

/-- **Auxiliary closed: marginal-CLT half of Theorem 19.5**.

From the finiteness of `J_{[]}(1, F, L²(P))` we extract a finite
ε-bracketing cover at some scale `ε ∈ (0, 1]`, find a bracket
`[l, u]` containing each `f ∈ F`, and bound `|f x| ≤ |l x| + |u x|`
pointwise to deduce `MemLp f 2 P` from `MemLp (l) 2 P` and
`MemLp (u) 2 P` via `MemLp.of_le_mul`. -/
private lemma marginalCLT_of_finite_bracketing_entropy_integral_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_meas : ∀ f ∈ F, AEMeasurable f P)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    IsMarginalCLT F P := by
  refine isMarginalCLT_of_memLp ?_
  intro f hf
  obtain ⟨ε, _hε, hN⟩ := exists_finite_bracketingNumber_of_integral_lt_top h_int
  obtain ⟨k, l, u, hbr, hcov⟩ := bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mp hN
  obtain ⟨i, hi⟩ := hcov f hf
  have hl_mem : MemLp (l i) 2 P := (hbr i).memLp_lower
  have hu_mem : MemLp (u i) 2 P := (hbr i).memLp_upper
  have h_f_strong : AEStronglyMeasurable f P := (h_meas f hf).aestronglyMeasurable
  refine MemLp.of_le_mul (c := 1) (hl_mem.abs.add hu_mem.abs) h_f_strong ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have h_nn : 0 ≤ |l i x| + |u i x| := by positivity
  change ‖f x‖ ≤ 1 * ‖|l i x| + |u i x|‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_nn, one_mul]
  obtain ⟨h1, h2⟩ := hi x
  rcases le_or_gt 0 (f x) with hf_pos | hf_neg
  · calc |f x|
        = f x := abs_of_nonneg hf_pos
      _ ≤ u i x := h2
      _ ≤ |u i x| := le_abs_self _
      _ ≤ |l i x| + |u i x| := by linarith [abs_nonneg (l i x)]
  · calc |f x|
        = -f x := abs_of_neg hf_neg
      _ ≤ -l i x := by linarith
      _ ≤ |l i x| := neg_le_abs _
      _ ≤ |l i x| + |u i x| := by linarith [abs_nonneg (u i x)]

/-- **Markov: L¹-integral convergence implies probability concentration**.

Given a sequence `ψ n : Ξ → ℝ≥0∞` of nonnegative measurable functions
with `∫⁻ ψ n dμ → 0`, then for every `ε > 0`,
`μ {ξ | ε ≤ ψ n ξ} → 0`.

For the random-pair application in the equicontinuity proof, the L²-vanishing
hypothesis `∫ ξ, ‖fhat n ξ − ghat n
ξ‖²_{L²(P)} ∂μ → 0` is converted, by this lemma applied to
`ψ n ξ = ENNReal.ofReal (‖fhat n ξ − ghat n ξ‖²_{L²(P)})`, into the
probability bound `μ{ξ | δ² ≤ ‖fhat − ghat‖²_{L²(P)}} → 0`: exactly
the "L²-consistency in probability" form that controls the bad-set
of the random pair.

The proof goes via `meas_ge_le_lintegral_div` (Markov in ENNReal form)
and the squeeze `0 ≤ μ{·} ≤ ε⁻¹ · ∫⁻ ψ → 0`. -/
private lemma tendsto_meas_le_of_tendsto_integral_zero
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ψ : ℕ → Ξ → ℝ≥0∞) (hψ_meas : ∀ n, Measurable (ψ n))
    (h_int : Tendsto (fun n => ∫⁻ ξ, ψ n ξ ∂μ) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) (hε_top : ε < ⊤) :
    Tendsto (fun n => μ {ξ | ε ≤ ψ n ξ}) atTop (𝓝 0) := by
  -- Markov in ENNReal form: `μ{ξ | ε ≤ ψ n ξ} ≤ (∫⁻ ψ n dμ) / ε`.
  -- The upper bound tends to `0 / ε = 0`; squeeze.
  have hε_ne : ε ≠ 0 := hε.ne'
  have hε_top_ne : ε ≠ ⊤ := hε_top.ne
  have h_markov : ∀ n, μ {ξ | ε ≤ ψ n ξ} ≤ (∫⁻ ξ, ψ n ξ ∂μ) / ε :=
    fun n => meas_ge_le_lintegral_div (hψ_meas n).aemeasurable hε_ne hε_top_ne
  have h_div : Tendsto (fun n => (∫⁻ ξ, ψ n ξ ∂μ) / ε) atTop (𝓝 (0 / ε)) :=
    ENNReal.Tendsto.div_const h_int (Or.inr hε_ne)
  rw [ENNReal.zero_div] at h_div
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_div
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall h_markov)

/-- **Envelope extraction from a finite bracketing-entropy integral** (file-local).

From `J_{[]}(1, F, L²(P)) < ⊤`, extract a finite bracketing cover at some scale
`ε ∈ (0,1]` and read off the measurable, `L²`-integrable envelope
`Φ := ∑_i (|l i| + |u i|)`, which dominates every `f ∈ F` pointwise. -/
private theorem chaining_envelope_from_bracket'
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ Φ : Ω → ℝ, Measurable Φ ∧ IsEnvelope F Φ ∧ MemLp Φ 2 P := by
  obtain ⟨ε, _hε, hN⟩ := exists_finite_bracketingNumber_of_integral_lt_top h_int
  obtain ⟨N, l, u, hbracket, hcover⟩ :=
    bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mp hN
  refine ⟨fun x => ∑ i : Fin N, (|l i x| + |u i x|), ?_, ?_, ?_⟩
  · refine Finset.measurable_sum _ ?_
    intro i _
    have hl : Measurable fun x => |l i x| :=
      continuous_abs.measurable.comp (hbracket i).measurable_lower
    have hu : Measurable fun x => |u i x| :=
      continuous_abs.measurable.comp (hbracket i).measurable_upper
    exact hl.add hu
  · intro f hf x
    obtain ⟨i, hbi⟩ := hcover f hf
    have hli : l i x ≤ f x := (hbi x).1
    have hui : f x ≤ u i x := (hbi x).2
    have h_abs_le : |f x| ≤ |l i x| + |u i x| := by
      rcases le_or_gt 0 (f x) with hfx | hfx
      · rw [abs_of_nonneg hfx]
        have h1 : f x ≤ |u i x| := hui.trans (le_abs_self _)
        linarith [abs_nonneg (l i x)]
      · rw [abs_of_neg hfx]
        have h3 : -(l i x) ≤ |l i x| := neg_le_abs _
        linarith [abs_nonneg (u i x)]
    refine h_abs_le.trans ?_
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin N)), 0 ≤ |l j x| + |u j x| :=
      fun j _ => by positivity
    exact Finset.single_le_sum (f := fun j => |l j x| + |u j x|)
      h_nonneg (Finset.mem_univ i)
  · refine memLp_finset_sum _ ?_
    intro i _
    exact (MemLp.abs (hbracket i).memLp_lower).add
      (MemLp.abs (hbracket i).memLp_upper)

/-- **Chain sequence extraction** (file-local).

From `J_{[]}(1, F, L²(P)) < ⊤`, build a localization scale sequence `δ_q ↓ 0` with
`δ_q ∈ (0, 1/4]` and `J_{[]}(δ_q, F, L²(P)) → 0`. The scale `δ_q := 1/(4(q+1))`;
`J(δ_q) → 0` because `J(1)` is finite and the lintegral over the shrinking window
`Ioc 0 δ_q` vanishes (`tendsto_setLIntegral_zero`). -/
private lemma equi_chain_chain_sequence_exists'
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ δ : ℕ → ℝ, (∀ q, 0 < δ q) ∧ (∀ q, δ q ≤ 1 / 4) ∧
      Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun q => bracketingEntropyIntegral (δ q) F P) atTop (𝓝 0) := by
  refine ⟨fun q => 1 / (4 * ((q : ℝ) + 1)), ?_, ?_, ?_, ?_⟩
  · intro q; positivity
  · intro q
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have h4 : (1 : ℝ) / 4 = 1 / (4 * (0 + 1)) := by norm_num
    rw [h4]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 4 : ℝ)
    simp only [mul_zero] at h
    refine h.congr (fun q => ?_)
    rw [one_div, one_div, ← mul_inv]; norm_num
  · set g : ℝ → ℝ≥0∞ := fun ε =>
      ENat.recTopCoe (⊤ : ℝ≥0∞)
        (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (1 + (n : ℝ)))))
        (bracketingNumber ε F 2 P) with hg_def
    have h_restrict_eq : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∫⁻ ε in Set.Ioc 0 δ, g ε ∂volume =
          ∫⁻ ε in Set.Ioc 0 δ, g ε
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      intro δ hδ_pos hδ_le_one
      rw [Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc,
        max_self (0 : ℝ), min_eq_left hδ_le_one]
    have h_J1_finite :
        ∫⁻ ε, g ε ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ ∞ := by
      have : ∫⁻ ε, g ε ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) =
          bracketingEntropyIntegral 1 F P := rfl
      rw [this]; exact h_int.ne
    have h_meas_tendsto : Tendsto
        (fun q : ℕ => (volume.restrict (Set.Ioc (0 : ℝ) 1))
          (Set.Ioc 0 ((1 : ℝ) / (4 * ((q : ℝ) + 1))))) atTop (𝓝 0) := by
      have h_vol_eq : ∀ q : ℕ,
          (volume.restrict (Set.Ioc (0 : ℝ) 1))
              (Set.Ioc 0 ((1 : ℝ) / (4 * ((q : ℝ) + 1)))) =
            ENNReal.ofReal ((1 : ℝ) / (4 * ((q : ℝ) + 1))) := by
        intro q
        have hpos : (0 : ℝ) < 1 / (4 * ((q : ℝ) + 1)) := by positivity
        have hle : (1 : ℝ) / (4 * ((q : ℝ) + 1)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
          nlinarith
        rw [Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc,
          max_self (0 : ℝ), min_eq_left hle,
          Real.volume_Ioc, sub_zero]
      have h_ofReal_tendsto : Tendsto
          (fun q : ℕ => ENNReal.ofReal ((1 : ℝ) / (4 * ((q : ℝ) + 1))))
          atTop (𝓝 (ENNReal.ofReal 0)) := by
        refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 4 : ℝ)
        simp only [mul_zero] at h
        refine h.congr (fun q => ?_)
        rw [one_div, one_div, ← mul_inv]; norm_num
      rw [ENNReal.ofReal_zero] at h_ofReal_tendsto
      refine h_ofReal_tendsto.congr (fun q => (h_vol_eq q).symm)
    have h_set_tendsto : Tendsto
        (fun q : ℕ => ∫⁻ ε in Set.Ioc 0 ((1 : ℝ) / (4 * ((q : ℝ) + 1))), g ε
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) :=
      tendsto_setLIntegral_zero h_J1_finite h_meas_tendsto
    refine h_set_tendsto.congr (fun q => ?_)
    have hpos : (0 : ℝ) < 1 / (4 * ((q : ℝ) + 1)) := by positivity
    have hle : (1 : ℝ) / (4 * ((q : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      nlinarith
    exact (h_restrict_eq _ hpos hle).symm

/-- **Strong-iid equicontinuity under finite
bracketing entropy**.

Same conclusion as
`equicontinuity_consumer_step_finite_entropy` (vdV §19.2 chaining),
but with **mutual** independence (`iIndepFun X μ`) replacing
the pairwise hypothesis exposed by the predicate
`IsAsymptoticallyEquicontinuous`. The textbook chaining argument
genuinely consumes mutual independence (for the per-level
`finite_sup_bound` invocation in the localized chaining argument, which
factorises the empirical-process variance into a sum of
per-summand variances).

**Proof structure (vdV §19.2).**
1. Pick `δ ↓ 0` along a sequence `δ_q ↓ 0` with
   `J_{[]}(δ_q, F − F, L²) → 0`.
2. By `hasFiniteBracketingCover_difference_class`, the
   difference class `F − F` inherits finite bracketing-entropy at every
   scale; choose envelope `Φ` from the level-1 bracket cover (concretely
   `Φ = max_i (|l i| + |u i|)` from a finite cover at scale 1).
3. Apply `localizedChainBound_of_finiteEntropy` to the difference slice
   `F_δ := {f − g ∈ F − F : ‖f − g‖_{L²} ≤ δ_q}`, giving universal `K`:
     `∫⁻ supNormOver F_δ (G_n) ∂μ ≤ K · (J_{[]}(δ_q, F − F, L²) +
       √n · envelope_tail)`.
4. Markov (`tendsto_meas_le_of_tendsto_integral_zero`) converts the
   lintegral bound to a probability bound on
   `μ{ξ | η < supNormOver F_δ (G_n)(ω(ξ))}`.
5. The L²-consistency hypothesis combined with Markov pushes the event
   `‖fhat n − ghat n‖_{L²(P)} > δ_q` to μ-measure 0; on its complement
   `(fhat n ξ − ghat n ξ) ∈ F_{δ_q}`, so the deviation is controlled by
   step 4.
6. Diagonal `δ_q ↓ 0` drives the maximal-inequality bound to 0.

The chain construction, envelope extraction, Markov bound, and diagonal limit
are summarized by `equicontinuity_chaining_assembly_brick`. -/
private lemma equicontinuity_consumer_step_strong_iid
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (h_fhat_in : ∀ n ξ, fhat n ξ ∈ F)
    (h_ghat_in : ∀ n ξ, ghat n ξ ∈ F)
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (h_l2 : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0))
    -- The δq-LOCALIZED chaining bound (vdV Lemma 19.34, localized form); see
    -- `chaining_integral_universal_K` in `Maximal.lean`.
    (hChainBound_outer :
      ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
          ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
                  (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
              ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) :=
  equicontinuity_chaining_assembly_brick F P h_int μ X hX_meas hX_iindep hX_id
    hX_law fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in h_l2_int h_l2
    hChainBound_outer η hη

/-- **Tendsto form of equicontinuity under finite bracketing entropy**.

This is the vdV §19.2 chaining conclusion in the form used by
`IsAsymptoticallyEquicontinuous`. It follows from
`equicontinuity_consumer_step_strong_iid`.

`IsAsymptoticallyEquicontinuous` (`Donsker.lean`) takes `iIndepFun`
directly; for example, `Measure.infinitePi` and `iIndepFun_infinitePi`
provide this hypothesis for the canonical iid sample. -/
private lemma equicontinuity_consumer_step_finite_entropy
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (h_fhat_in : ∀ n ξ, fhat n ξ ∈ F)
    (h_ghat_in : ∀ n ξ, ghat n ξ ∈ F)
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (h_l2 : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0))
    -- The δq-LOCALIZED chaining bound (vdV Lemma 19.34, localized form); see
    -- `chaining_integral_universal_K` in `Maximal.lean`.
    (hChainBound_outer :
      ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
          ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
                  (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
              ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) :=
  equicontinuity_consumer_step_strong_iid F P h_int μ X hX_meas hX_iindep
    hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in
    h_l2_int h_l2 hChainBound_outer η hη

/-- **Equicontinuity half of Theorem 19.5**.

Unfolds the universal quantifiers of `IsAsymptoticallyEquicontinuous` and applies
`equicontinuity_consumer_step_finite_entropy`, which forwards to
`equicontinuity_consumer_step_strong_iid` (vdV §19.2 chaining under
mutual independence). The two textbook ingredients
`hasFiniteBracketingCover_difference_class` (vdV Lemma 19.31) and
`tendsto_meas_le_of_tendsto_integral_zero` = Markov bridge from
L²-vanishing to probability concentration are used in this argument. -/
private lemma asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    IsAsymptoticallyEquicontinuous F P := by
  classical
  -- Enter the modulus: fix the sample space, the iid sample, and `ε, η`.
  intro Ξ _ μ _ X hX_meas hX_iindep hX_id hX_law ε η hε hη
  -- Every `f ∈ F` is `L²(P)` (marginal-CLT half), used for integrability of pairs.
  have hmemLp : ∀ f ∈ F, MemLp f 2 P :=
    (marginalCLT_of_finite_bracketing_entropy_integral_aux F P
      (fun f hf => (hF_meas f hf).aemeasurable) h_int).memLp
  -- The class-`F` envelope `Φ`; upgrade to the difference-class envelope `Φ₂ := 2Φ`.
  obtain ⟨Φ, hΦ_meas, hΦ_env, hΦ_L2⟩ := chaining_envelope_from_bracket' h_int
  set Φ₂ : Ω → ℝ := fun x => 2 * Φ x with hΦ₂_def
  have hΦ₂_meas : Measurable Φ₂ := measurable_const.mul hΦ_meas
  have hΦ₂_env : IsEnvelope (differenceClass F) Φ₂ := isEnvelope_differenceClass_two hΦ_env
  have hΦ₂_L2 : MemLp Φ₂ 2 P := hΦ_L2.const_mul 2
  -- The chain sequence `δq → 0` with `J(δq, F, P) → 0` (entropy-integral finiteness).
  obtain ⟨δseq, hδ_pos, hδ_le_quarter, _hδ_to_zero, hδ_J_to_zero⟩ :=
    equi_chain_chain_sequence_exists' h_int
  -- The measurable-majorant chaining bound (universal `c`).
  obtain ⟨c, hc_pos, hMaj⟩ :=
    localizedChainBound_measurableMajorant_of_finiteEntropy hF_ne hF_meas
      h_int μ X hX_meas hX_iindep hX_id hX_law
  -- `ofReal ε` is a positive, finite ℝ≥0∞ — Markov divisor.
  have hεE_pos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hεE_ne : ENNReal.ofReal ε ≠ 0 := hεE_pos.ne'
  have hεE_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Choose the localization scale `δq := δseq q` so the bracketing-entropy term
  -- `c·J(δq)` is below `(ofReal η)·(ofReal ε)`; then `c·J(δq)/ofReal ε ≤ ofReal η`.
  have hKJ_tendsto : Tendsto
      (fun q => (ENNReal.ofReal c) * bracketingEntropyIntegral (δseq q) F P)
      atTop (𝓝 0) := by
    have h : Tendsto
        (fun q => (ENNReal.ofReal c) * bracketingEntropyIntegral (δseq q) F P)
        atTop (𝓝 (ENNReal.ofReal c * 0)) :=
      ENNReal.Tendsto.const_mul hδ_J_to_zero
        (Or.inr (ENNReal.ofReal_ne_top (r := c)))
    rwa [mul_zero] at h
  obtain ⟨q₀, hq₀⟩ := (ENNReal.tendsto_atTop_zero.mp hKJ_tendsto)
    (ENNReal.ofReal η * ENNReal.ofReal ε)
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hη).ne' hεE_ne)
  have hJbound : (ENNReal.ofReal c) * bracketingEntropyIntegral (δseq q₀) F P
      ≤ ENNReal.ofReal η * ENNReal.ofReal ε := hq₀ q₀ le_rfl
  set δq : ℝ := δseq q₀ with hδq_def
  have hδq_pos : 0 < δq := hδ_pos q₀
  have hδq_le : δq ≤ 1 / 4 := hδ_le_quarter q₀
  -- At scale `δq`, choose a uniform clamp `M` and measurable majorants `Maj n`.
  obtain ⟨M, hM_pos, hMajn⟩ := hMaj Φ₂ hΦ₂_meas hΦ₂_env hΦ₂_L2 hδq_pos hδq_le
  refine ⟨δq, hδq_pos, ?_⟩
  -- Abbreviate the localized class and the close-pair modulus event.
  set G := localizedDifferenceClass F P δq with hG_def
  set Bev : ℕ → Set Ξ := fun n =>
    {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δq ∧
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|}
    with hBev_def
  -- The RHS bound at each `n`, as an ℝ≥0∞ sequence.
  set Tail : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.sqrt n)
      * ∫⁻ ω, ENNReal.ofReal (|Φ₂ ω|)
          * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω ∂P with hTail_def
  set RHS : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal c * bracketingEntropyIntegral δq F P + ENNReal.ofReal c * Tail n
    with hRHS_def
  -- STEP 3+4: for each `n`, `μ* (Bev n) ≤ RHS n / ofReal ε`.
  have hkey : ∀ n, μ.outerMeasureStar (Bev n) ≤ RHS n / ENNReal.ofReal ε := by
    intro n
    obtain ⟨Maj, hMaj_meas, hMaj_dom, hMaj_int⟩ := hMajn n
    -- The close-pair event lands in the measurable superlevel set `{ofReal ε ≤ Maj}`.
    have hsub : Bev n ⊆ {ξ | ENNReal.ofReal ε ≤ Maj ξ} := by
      rintro ξ ⟨s, t, hclose, hosc⟩
      -- `s − t ∈ localizedDifferenceClass F P δq`.
      have hs_mem : MemLp (s : Ω → ℝ) 2 P := hmemLp s s.2
      have ht_mem : MemLp (t : Ω → ℝ) 2 P := hmemLp t t.2
      have hst_mem : MemLp (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P := hs_mem.sub ht_mem
      have hne_top : eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P ≠ ⊤ :=
        hst_mem.eLpNorm_lt_top.ne
      have hradius : eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P
          ≤ ENNReal.ofReal δq := by
        have htoReal_lt : (eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P).toReal
            < δq := hclose
        calc eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P
            = ENNReal.ofReal
                (eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P).toReal := by
              rw [ENNReal.ofReal_toReal hne_top]
          _ ≤ ENNReal.ofReal δq := ENNReal.ofReal_le_ofReal htoReal_lt.le
      have hst_in : (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) ∈ G :=
        mem_localizedDifferenceClass s.2 t.2 hradius
      -- `ofReal ε ≤ ofReal |G_n(s−t)| ≤ supNormOver G (G_n) ≤ Maj ξ`.
      have hlin : empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x)
          = empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ) :=
        empiricalProcess_sub P n _ _ _ (hs_mem.integrable one_le_two)
          (ht_mem.integrable one_le_two)
      have hosc' : ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x)| := by rw [hlin]; exact hosc
      have hle_g : ENNReal.ofReal ε ≤ supNormOver G
          (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) := by
        calc ENNReal.ofReal ε
            ≤ ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x)| :=
              ENNReal.ofReal_le_ofReal hosc'.le
          _ ≤ supNormOver G
                (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) :=
              le_supNormOver hst_in
      exact le_trans hle_g (hMaj_dom ξ)
    -- Outer-measure monotone + measurable superlevel collapses to genuine measure.
    have hms : MeasurableSet {ξ | ENNReal.ofReal ε ≤ Maj ξ} :=
      measurableSet_le measurable_const hMaj_meas
    calc μ.outerMeasureStar (Bev n)
        ≤ μ.outerMeasureStar {ξ | ENNReal.ofReal ε ≤ Maj ξ} :=
          outerMeasureStar_mono μ hsub
      _ = μ {ξ | ENNReal.ofReal ε ≤ Maj ξ} := outerMeasureStar_eq_measure hms
      _ ≤ (∫⁻ ξ, Maj ξ ∂μ) / ENNReal.ofReal ε :=
          meas_ge_le_lintegral_div hMaj_meas.aemeasurable hεE_ne hεE_ne_top
      _ ≤ RHS n / ENNReal.ofReal ε := by
          apply ENNReal.div_le_div_right
          rw [hRHS_def, hTail_def]; exact hMaj_int
  -- STEP 5: `limsupₙ (μ* (Bev n)) ≤ limsupₙ (RHS n / ofReal ε) ≤ ofReal η`.
  have hRHS_div : (fun n => RHS n / ENNReal.ofReal ε)
      = fun n => (ENNReal.ofReal c * bracketingEntropyIntegral δq F P) / ENNReal.ofReal ε
          + (ENNReal.ofReal c * Tail n) / ENNReal.ofReal ε := by
    funext n; rw [hRHS_def, ENNReal.add_div]
  -- The constant term is `≤ ofReal η`.
  have hconst_le : (ENNReal.ofReal c * bracketingEntropyIntegral δq F P)
        / ENNReal.ofReal ε ≤ ENNReal.ofReal η := by
    rw [ENNReal.div_le_iff hεE_ne hεE_ne_top]
    exact hJbound
  -- The `√n·tail` term → 0 (DCT on the `L²` envelope).
  have hTail_tendsto : Tendsto Tail atTop (𝓝 0) := by
    have h_tendsto := tendsto_envelope_tail_const_threshold P hΦ₂_meas hΦ₂_L2 hM_pos
    have h_set_eq : ∀ n : ℕ,
        (fun ω => ENNReal.ofReal (|Φ₂ ω|)
            * Set.indicator {x | M * Real.sqrt n < |Φ₂ x|} 1 ω)
        = (fun ω => ENNReal.ofReal (|Φ₂ ω|)
            * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω) := by
      intro n; simp_rw [mul_comm M (Real.sqrt n)]
    refine (h_tendsto.congr (fun n => ?_))
    rw [hTail_def]; rw [h_set_eq n]
  have hVf_tendsto : Tendsto (fun n => (ENNReal.ofReal c * Tail n) / ENNReal.ofReal ε)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal c * Tail n) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul hTail_tendsto
        (Or.inr (ENNReal.ofReal_ne_top (r := c)))
      rwa [mul_zero] at h
    have h2 : Tendsto (fun n => (ENNReal.ofReal c * Tail n) / ENNReal.ofReal ε)
        atTop (𝓝 (0 / ENNReal.ofReal ε)) :=
      ENNReal.Tendsto.div_const h1 (Or.inr hεE_ne)
    rwa [ENNReal.zero_div] at h2
  -- Combine: `limsup (const + Vf) ≤ const` since `Vf → 0`.
  have hRHSdiv_limsup : limsup (fun n => RHS n / ENNReal.ofReal ε) atTop
      ≤ ENNReal.ofReal η := by
    rw [hRHS_div]
    refine le_trans (limsup_add_tendsto_zero_le
      (fun _ => (ENNReal.ofReal c * bracketingEntropyIntegral δq F P) / ENNReal.ofReal ε)
      (fun n => (ENNReal.ofReal c * Tail n) / ENNReal.ofReal ε) _ ?_ hVf_tendsto) hconst_le
    exact le_of_eq (limsup_const _)
  refine le_trans (limsup_le_limsup (Eventually.of_forall hkey)
    isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hRHSdiv_limsup

/-- **Auxiliary for Theorem 19.5**: combines the marginal-CLT
half (`marginalCLT_of_finite_bracketing_entropy_integral_aux`) with the
equicontinuity half
(`asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux`)
into the `IsPDonsker` conjunction. The marginal-CLT conjunct is closed
via bracket extraction + `MemLp.of_le_mul`; the equicontinuity conjunct
delegates via `exact` to a sub-lemma carrying the textbook chaining
content. -/
private lemma isPDonsker_of_finite_bracketing_entropy_integral_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    IsPDonsker F P :=
  ⟨marginalCLT_of_finite_bracketing_entropy_integral_aux F P
     (fun f hf => (hF_meas f hf).aemeasurable) h_int,
   asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux F P
     hF_ne hF_meas h_int⟩

/-- **Theorem 19.5 (Donsker via bracketing entropy integral)**.

Every class `F` of measurable functions with `J_{[]}(1, F, L_2(P)) < ⊤`
is `P`-Donsker.

vdV §19.2 Theorem 19.5.

**Proof outline** (vdV §19.2):
1. Split `IsPDonsker = IsMarginalCLT ∧ IsAsymptoticallyEquicontinuous`.
2. **Marginal CLT half**: extract any single ε-bracket from the finite
   cover at a scale where `bracketingNumber < ⊤` (available because
   `J_{[]}(1, F, L²(P)) < ⊤`); for `f ∈ F` find a containing bracket
   `[l, u]` with `|f| ≤ |l| + (u − l)`; apply
   `IsEpsBracket.memLp_lower`/`memLp_upper` to conclude `MemLp f 2 P`.
3. **Equicontinuity half**: derives the universal constant and localized
   difference-class bound from `localizedChainBound_of_finiteEntropy`.
For each small `δq`, Lemma 19.34 gives
   `∫⁻ supNormOver (localizedDifferenceClass F P δq) (G_n)
      ≤ c · J_{[]}(δq,F) + c · √n · envelope_tail`.
   The envelope tail vanishes and `J_{[]}(δq,F) → 0` as `δq ↓ 0`.
   Markov converts the lintegral bound to a probability bound on
   `μ {ξ | η < |G_n(fhat) - G_n(ghat)|}`.

The marginal-CLT half uses bracket extraction
(`exists_finite_bracketingNumber_of_integral_lt_top`) and `MemLp.of_le_mul`.
For equicontinuity, on the `L²`-good event the random difference belongs to
`localizedDifferenceClass F P δq`; its empirical-process norm is therefore
bounded by the localized supremum supplied by
`localizedChainBound_of_finiteEntropy` (vdV Lemma 19.34).

No separate positivity assumption on the entropy integral is required. The
nonempty case obtains positivity from
`bracketingEntropyIntegral_pos_of_nonempty`; the empty class is Donsker
vacuously. Thus the hypotheses are precisely measurability and finiteness of
`J_{[]}(1, F, L²(P))`, as in vdV Theorem 19.5. -/
theorem isPDonsker_of_finite_bracketing_entropy_integral
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    IsPDonsker F P := by
  classical
  by_cases hF_ne : F.Nonempty
  · exact isPDonsker_of_finite_bracketing_entropy_integral_aux F P
      hF_ne hF_meas h_int
  · have hF_empty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF_ne
    subst F
    refine ⟨isMarginalCLT_of_memLp (fun f hf => (Set.notMem_empty f hf).elim), ?_⟩
    intro Ξ _ μ _ X _ _ _ _ ε η _ hη
    refine ⟨1, one_pos, ?_⟩
    calc
      limsup (fun n => μ.outerMeasureStar
          {ξ | ∃ s t : ↥(∅ : Set (Ω → ℝ)),
            distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < 1 ∧
              ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ) -
                empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|}) atTop
          ≤ limsup (fun _ : ℕ => ENNReal.ofReal η) atTop := by
            refine limsup_le_limsup (Eventually.of_forall (fun n => ?_))
              isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
            have hEvent :
                {ξ | ∃ s t : ↥(∅ : Set (Ω → ℝ)),
                  distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < 1 ∧
                    ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (s : Ω → ℝ) - empiricalProcess P n
                        (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} = ∅ := by
              rw [Set.eq_empty_iff_forall_notMem]
              rintro ξ ⟨s, -⟩
              exact (Set.notMem_empty (s : Ω → ℝ) s.2).elim
            change μ.outerMeasureStar
              {ξ | ∃ s t : ↥(∅ : Set (Ω → ℝ)),
                distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < 1 ∧
                  ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (s : Ω → ℝ) - empiricalProcess P n
                      (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} ≤ ENNReal.ofReal η
            rw [hEvent, outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
            exact zero_le
      _ = ENNReal.ofReal η := limsup_const _

end AsymptoticStatistics.EmpiricalProcess
