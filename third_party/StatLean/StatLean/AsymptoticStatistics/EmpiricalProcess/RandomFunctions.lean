module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.EquicontTightness
public import StatLean.AsymptoticStatistics.EmpiricalProcess.IIDChebyshev
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterSlutsky
public import Mathlib.Probability.IdentDistrib

@[expose] public section

/-!
# Random functions in a Donsker class (Lemma 19.24)

If `F` is a `P`-Donsker class and `f̂_n` is a sequence of random functions
taking values in `F` whose `L²(P)` distance from `f₀ ∈ L²(P)` tends to zero in
outer probability, then the empirical-process difference
`G_n(f̂_n) − G_n(f₀)` tends to zero in probability.

vdV §19.4 Lemma 19.24. vdV's proof uses the continuous-mapping theorem on
`ℓ^∞(F) × F → ℝ` together with Lemma 18.15 (almost all sample paths of the
limiting Gaussian process are continuous on `(F, ‖·‖_{P,2})`); the proof here
routes directly through the random-pair-in-probability form of
`IsAsymptoticallyEquicontinuous`, with no `ℓ^∞(F)`-topology infrastructure.

Declarations:
* `donsker_random_function_consistency_core` is the faithful process-difference
  statement of Lemma 19.24.
* `exists_mem_distL2_lt_of_outer_consistency` extracts deterministic anchors
  in `F` approaching the possibly external `L²(P)` limit `f₀`.
* `donsker_random_function_consistency` is an expectation-form corollary under
  stronger expectation and measurability assumptions.
* `empiricalProcessMarginalGaussian` is the scalar Brownian-bridge marginal law
  obtained by projecting the one-function Gaussian marginal.
* `empiricalProcess_weakConvergesOuter_marginalGaussian_of_memLp` is the direct
  fixed-function marginal result; the unsuffixed declaration derives its
  `L²(P)` premise from class membership.
* `donsker_random_function_consistency_weakConvergesOuter` combines the
  consistency result with the fixed-function marginal result to give the outer weak
  convergence form of Lemma 19.24.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ENNReal
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Outer measure is bounded by the ambient measure for every set. -/
private theorem outerMeasureStar_le_measure_local
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (A : Set Ξ) :
    μ.outerMeasureStar A ≤ μ A := by
  rw [measure_eq_iInf]
  refine le_iInf fun t => le_iInf fun hAt => le_iInf fun ht => ?_
  rw [Measure.outerMeasureStar, outerExpectation]
  calc
    (⨅ U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U},
        ∫⁻ ω, (U : Ξ → ℝ≥0∞) ω ∂μ)
        ≤ ∫⁻ ω, t.indicator 1 ω ∂μ :=
      iInf_le (fun U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U} =>
        ∫⁻ ω, (U : Ξ → ℝ≥0∞) ω ∂μ)
        ⟨t.indicator 1, measurable_one.indicator ht, fun ω => by
          by_cases hω : ω ∈ A
          · simp [hω, hAt hω]
          · simp [hω]⟩
    _ = μ t := lintegral_indicator_one ht

/-- **Deterministic anchor extracted from outer `L²` consistency.** If random
functions always take values in `F` and converge in outer probability to `f₀`
for `distL2 P`, then every positive `L²` neighbourhood of `f₀` meets `F`.

Otherwise the tail event at half the radius is the whole probability space for
every `n`, contradicting convergence of its outer probability to zero. -/
lemma exists_mem_distL2_lt_of_outer_consistency
    (F : Set (Ω → ℝ)) (P : Measure Ω) (f₀ : Ω → ℝ)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f_hat : ℕ → Ξ → (Ω → ℝ))
    (h_range : ∀ n ξ, f_hat n ξ ∈ F)
    (h_l2_consistent : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) f₀}) atTop (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ g ∈ F, distL2 P g f₀ < ρ := by
  have htend := h_l2_consistent (ρ / 2) (half_pos hρ)
  have hev : ∀ᶠ n in atTop,
      μ.outerMeasureStar {ξ | ρ / 2 < distL2 P (f_hat n ξ) f₀} < 1 :=
    htend (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  obtain ⟨n, hn⟩ := hev.exists
  by_contra hnone
  push Not at hnone
  have hset : {ξ | ρ / 2 < distL2 P (f_hat n ξ) f₀} = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro ξ
    exact lt_of_lt_of_le (half_lt_self hρ) (hnone (f_hat n ξ) (h_range n ξ))
  rw [hset] at hn
  have hle := measure_le_outerMeasureStar μ (Set.univ : Set Ξ)
  rw [measure_univ] at hle
  exact (not_lt_of_ge hle hn)

set_option maxHeartbeats 2000000 in
-- reason: the three-event outer-measure `limsup` split carries large empirical-process terms.
/-- **Lemma 19.24 (faithful process-difference core).**

Suppose `F` is `P`-Donsker, `f₀ ∈ L²(P)`, and the random functions `f_hat n`
take values in `F`. If `distL2 P (f_hat n) f₀` tends to zero in explicit
outer probability, then for every `η > 0` the probability that the empirical
processes at `f_hat n` and `f₀` differ by more than `η` tends to zero.

This is the process-difference claim used in vdV §19.4 Lemma 19.24. The proof
derives deterministic anchors `g ∈ F` arbitrarily close to `f₀`, rather than
using vdV's informal WLOG replacement of `F` by `F ∪ {f₀}`. -/
theorem donsker_random_function_consistency_core
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_donsker : IsPDonsker F P)
    -- vdV Lemma 19.24 assumes that `F` is `P`-Donsker.
    (f₀ : Ω → ℝ) (hf₀ : MemLp f₀ 2 P)
    -- vdV Lemma 19.24 assumes `f₀ ∈ L²(P)`.
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- these clauses encode the iid `P` sample underlying `G_n`.
    (f_hat : ℕ → Ξ → (Ω → ℝ))
    (h_range : ∀ n ξ, f_hat n ξ ∈ F)
    -- vdV Lemma 19.24 assumes the random functions take values in `F`.
    (h_l2_consistent : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) f₀}) atTop (𝓝 0))
    -- this is vdV's `∫(f̂_n-f₀)² dP →_P 0`, in explicit outer-probability form.
    : ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
                  empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}) atTop (𝓝 0) := by
  intro η hη
  set u : ℕ → ℝ≥0∞ := fun n =>
    μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
      empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} with hu
  suffices hlimsup : ∀ ε : ℝ, 0 < ε → limsup u atTop ≤ ENNReal.ofReal ε by
    have hsup0 : limsup u atTop ≤ 0 := by
      refine ENNReal.le_of_forall_pos_le_add fun ε hεpos _ => ?_
      rw [zero_add]
      have := hlimsup (ε : ℝ) (by exact_mod_cast hεpos)
      rwa [ENNReal.ofReal_coe_nnreal] at this
    have hsup0' : limsup u atTop = 0 := le_antisymm hsup0 bot_le
    refine tendsto_of_le_liminf_of_limsup_le bot_le hsup0'.le ?_ ?_
    · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
    · exact isBoundedUnder_of ⟨0, fun _ => bot_le⟩
  intro ε hε
  have hη2 : 0 < η / 2 := half_pos hη
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδpos, hBlimsup⟩ :=
    h_donsker.asymptoticallyEquicontinuous μ X hX_meas hX_iindep hX_idem hX_law
      (η / 2) (ε / 2) hη2 hε2
  set ρ : ℝ := min (δ / 2) ((η / 2) * Real.sqrt (ε / 2)) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact lt_min (half_pos hδpos) (mul_pos hη2 (Real.sqrt_pos.mpr hε2))
  obtain ⟨g, hg, hgclose⟩ :=
    exists_mem_distL2_lt_of_outer_consistency F P f₀ μ f_hat h_range h_l2_consistent hρpos
  have hg_L2 : MemLp g 2 P := h_donsker.marginalCLT.memLp g hg
  have hg_delta : distL2 P g f₀ < δ / 2 :=
    hgclose.trans_le (by rw [hρ]; exact min_le_left _ _)
  have hg_small : distL2 P g f₀ < (η / 2) * Real.sqrt (ε / 2) :=
    hgclose.trans_le (by rw [hρ]; exact min_le_right _ _)
  have hfixed_bound : distL2 P g f₀ ^ 2 / (η / 2) ^ 2 ≤ ε / 2 := by
    have hd_nonneg : 0 ≤ distL2 P g f₀ := ENNReal.toReal_nonneg
    have hsq_le : distL2 P g f₀ ^ 2 ≤ ((η / 2) * Real.sqrt (ε / 2)) ^ 2 :=
      pow_le_pow_left₀ hd_nonneg hg_small.le 2
    have hsqrt_sq : Real.sqrt (ε / 2) ^ 2 = ε / 2 := Real.sq_sqrt hε2.le
    calc
      distL2 P g f₀ ^ 2 / (η / 2) ^ 2
          ≤ ((η / 2) * Real.sqrt (ε / 2)) ^ 2 / (η / 2) ^ 2 :=
        div_le_div_of_nonneg_right hsq_le (sq_nonneg _)
      _ = ε / 2 := by rw [mul_pow, hsqrt_sq]; field_simp
  set Bev : ℕ → Set Ξ := fun n =>
    {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
      η / 2 < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ) -
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} with hBev
  set Tev : ℕ → Set Ξ := fun n =>
    {ξ | δ / 4 < distL2 P (f_hat n ξ) f₀} with hTev
  set Cev : ℕ → Set Ξ := fun n =>
    {ξ | η / 2 ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ) g -
      empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} with hCev
  clear_value Bev Tev Cev
  have hsplit : ∀ n,
      {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
        empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} ⊆
        (Bev n ∪ Tev n) ∪ Cev n := by
    intro n ξ hξ
    rw [hBev, hTev, hCev]
    change η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
      empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀| at hξ
    by_cases htail : δ / 4 < distL2 P (f_hat n ξ) f₀
    · exact Or.inl (Or.inr htail)
    · have hclose₀ : distL2 P (f_hat n ξ) f₀ ≤ δ / 4 := not_lt.mp htail
      have hfhat_L2 : MemLp (f_hat n ξ) 2 P :=
        h_donsker.marginalCLT.memLp (f_hat n ξ) (h_range n ξ)
      have hclose_g : distL2 P (f_hat n ξ) g < δ := by
        have htri := distL2_triangle_of_memLp hfhat_L2 hf₀ hg_L2
        rw [distL2_comm f₀ g] at htri
        linarith
      by_cases hfg : η / 2 <
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
            empiricalProcess P n (fun i : Fin n => X i.val ξ) g|
      · exact Or.inl (Or.inl (bulk_osc_mem (h_range n ξ) hg hclose_g hfg))
      · refine Or.inr ?_
        rw [not_lt] at hfg
        have htri_abs := abs_sub_le
          (empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ))
          (empiricalProcess P n (fun i : Fin n => X i.val ξ) g)
          (empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀)
        have hfixed_lt : η / 2 <
            |empiricalProcess P n (fun i : Fin n => X i.val ξ) g -
              empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀| := by
          nlinarith [hξ, htri_abs, hfg]
        exact hfixed_lt.le
  set Uf : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar (Bev n) with hUf
  set Vf : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar (Tev n) with hVf
  set Wf : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar (Cev n) with hWf
  have hbound : ∀ n, u n ≤ (Uf n + Vf n) + Wf n := by
    intro n
    rw [hu, hUf, hVf, hWf]
    calc
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}
          ≤ μ.outerMeasureStar
              {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
                empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} :=
            measure_le_outerMeasureStar μ _
      _ ≤ μ.outerMeasureStar ((Bev n ∪ Tev n) ∪ Cev n) :=
        outerMeasureStar_mono μ (hsplit n)
      _ ≤ μ.outerMeasureStar (Bev n ∪ Tev n) + μ.outerMeasureStar (Cev n) :=
        outerMeasureStar_union_le μ _ _
      _ ≤ (μ.outerMeasureStar (Bev n) + μ.outerMeasureStar (Tev n)) +
          μ.outerMeasureStar (Cev n) := by
        exact add_le_add_left (outerMeasureStar_union_le μ _ _) _
  have hVf0 : Tendsto Vf atTop (𝓝 0) := by
    rw [hVf]
    simp only [hTev]
    exact h_l2_consistent (δ / 4) (by positivity)
  have hBlimsup' : limsup Uf atTop ≤ ENNReal.ofReal (ε / 2) := by
    rw [hUf]
    simp only [hBev]
    exact hBlimsup
  have hWbound : ∀ n, Wf n ≤ ENNReal.ofReal (ε / 2) := by
    intro n
    rw [hWf, hCev]
    calc
      μ.outerMeasureStar {ξ | η / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) g -
            empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}
          ≤ μ {ξ | η / 2 ≤
              |empiricalProcess P n (fun i : Fin n => X i.val ξ) g -
                empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} :=
            outerMeasureStar_le_measure_local μ _
      _ ≤ ENNReal.ofReal (distL2 P g f₀ ^ 2 / (η / 2) ^ 2) :=
        empiricalProcess_sub_chebyshev_tail P μ X hX_meas hX_iindep hX_idem hX_law
          n g f₀ hg_L2 hf₀ hη2
      _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal hfixed_bound
  have hBT : limsup (fun n => Uf n + Vf n) atTop ≤ ENNReal.ofReal (ε / 2) :=
    limsup_add_tendsto_zero_le Uf Vf _ hBlimsup' hVf0
  have hWlimsup : limsup Wf atTop ≤ ENNReal.ofReal (ε / 2) := by
    calc
      limsup Wf atTop ≤ limsup (fun _ : ℕ => ENNReal.ofReal (ε / 2)) atTop :=
        limsup_le_limsup (Eventually.of_forall hWbound)
          isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      _ = ENNReal.ofReal (ε / 2) := limsup_const _
  clear_value u Uf Vf Wf
  calc
    limsup u atTop ≤ limsup (fun n => (Uf n + Vf n) + Wf n) atTop :=
      limsup_le_limsup (Eventually.of_forall hbound)
        isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      limsup_add_le_of_le _ _ _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hBT hWlimsup
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hε2.le hε2.le]
      congr 1
      ring

/-- **Lemma 19.24 with asymptotic class membership.**

This is the form used in vdV Theorem 25.77.  The random function need only
belong to the fixed Donsker class with probability tending to one.  A supplied
anchor in the class is used to localize the function on the exceptional event;
the anchor does not restrict the theorem, since asymptotic membership already
forces the class to be nonempty.

The `L²(P)` consistency premise is stated in the explicit outer-probability form
of `donsker_random_function_consistency_core`. -/
theorem donsker_random_function_consistency_wpa
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_donsker : IsPDonsker F P)
    (f₀ : Ω → ℝ) (hf₀ : MemLp f₀ 2 P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f_hat : ℕ → Ξ → (Ω → ℝ))
    (anchor : Ω → ℝ) (hanchor : anchor ∈ F)
    (h_range_bad : Tendsto (fun n =>
      μ {ξ | f_hat n ξ ∉ F}) atTop (𝓝 0))
    (h_l2_consistent : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) f₀}) atTop (𝓝 0)) :
    ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
                  empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}) atTop (𝓝 0) := by
  classical
  let f_loc : ℕ → Ξ → (Ω → ℝ) := fun n ξ =>
    if f_hat n ξ ∈ F then f_hat n ξ else anchor
  have hloc_range : ∀ n ξ, f_loc n ξ ∈ F := by
    intro n ξ
    simp only [f_loc]
    split_ifs with hmem
    · exact hmem
    · exact hanchor
  have hloc_l2 : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (f_loc n ξ) f₀}) atTop (𝓝 0) := by
    intro δ hδ
    have hsum := (h_l2_consistent δ hδ).add h_range_bad
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hsum) (Eventually.of_forall fun _ => bot_le)
      (Eventually.of_forall fun n => ?_)
    calc
      μ.outerMeasureStar {ξ | δ < distL2 P (f_loc n ξ) f₀}
          ≤ μ.outerMeasureStar
              ({ξ | δ < distL2 P (f_hat n ξ) f₀} ∪ {ξ | f_hat n ξ ∉ F}) :=
        outerMeasureStar_mono μ (by
          intro ξ hξ
          by_cases hmem : f_hat n ξ ∈ F
          · left
            change δ < distL2 P (f_loc n ξ) f₀ at hξ
            rw [show f_loc n ξ = f_hat n ξ by simp [f_loc, hmem]] at hξ
            exact hξ
          · exact Or.inr hmem)
      _ ≤ μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) f₀} +
            μ.outerMeasureStar {ξ | f_hat n ξ ∉ F} := outerMeasureStar_union_le μ _ _
      _ ≤ μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) f₀} +
            μ {ξ | f_hat n ξ ∉ F} :=
        add_le_add_right (outerMeasureStar_le_measure_local μ _) _
  intro η hη
  have hloc := donsker_random_function_consistency_core F P h_donsker f₀ hf₀ μ
    X hX_meas hX_iindep hX_idem hX_law f_loc hloc_range hloc_l2 η hη
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hloc.add h_range_bad)
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
  calc
    μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}
        ≤ μ.outerMeasureStar
            {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
              empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} :=
      measure_le_outerMeasureStar μ _
    _ ≤ μ.outerMeasureStar
          ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_loc n ξ) -
              empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} ∪
            {ξ | f_hat n ξ ∉ F}) := outerMeasureStar_mono μ (by
      intro ξ hξ
      by_cases hmem : f_hat n ξ ∈ F
      · left
        change η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀| at hξ
        change η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_loc n ξ) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|
        rw [show f_loc n ξ = f_hat n ξ by simp [f_loc, hmem]]
        exact hξ
      · exact Or.inr hmem)
    _ ≤ μ.outerMeasureStar
          {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_loc n ξ) -
              empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} +
            μ.outerMeasureStar {ξ | f_hat n ξ ∉ F} := outerMeasureStar_union_le μ _ _
    _ ≤ μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_loc n ξ) -
              empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} +
            μ {ξ | f_hat n ξ ∉ F} := add_le_add
      (outerMeasureStar_le_measure_local μ _) (outerMeasureStar_le_measure_local μ _)

/-- **Expectation-form corollary of Lemma 19.24.**

Suppose `F` is a `P`-Donsker class of measurable functions and `f_hat n`
is a sequence of jointly measurable random functions taking values in
`F` such that `E_μ[∫ (f_hat n − f₀)² dP] → 0` for some `f₀ ∈ F` with
`f₀ ∈ L²(P)`. Then for every `η > 0`,
`μ{ξ | η < |G_n(f_hat n ξ) − G_n(f₀)|} → 0`,
i.e. `G_n(f_hat n) − G_n(f₀) →_P 0`.

The expectation, integrability, and joint-measurability hypotheses imply the
explicit outer-probability premise of
`donsker_random_function_consistency_core`. They are stronger than the
corresponding assumptions of that theorem.

Hypotheses:
* `h_donsker` — vdV §19.4 Lemma 19.24: `F` is `P`-Donsker.
* `_hf₀_in_F` — the stronger assumption `f₀ ∈ F`; the process-difference
  core derives anchors in `F` and does not use membership of the limit itself.
* `_hf₀` — vdV §19.4's assumption `f₀ ∈ L²(P)`.
* `h_range` — vdV §19.4: random functions take values in `F`.
* `h_l2_int`, `h_l2_consistent` — integrability and expectation convergence of
  the squared `L²(P)` distance, which imply the outer-probability tail bound.
* `hf₀_meas`, `h_fhat_meas` — joint measurability assumptions used to apply
  equicontinuity at the random pair `(f_hat n, const f₀)`.
* `hX_*` — iid hypotheses on the sample (empirical-process setup). -/
theorem donsker_random_function_consistency
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    -- USER-INPUT: `F` is `P`-Donsker and contains the square-integrable limit;
    -- vdV Lemma 19.24.
    (h_donsker : IsPDonsker F P)
    (f₀ : Ω → ℝ) (_hf₀ : MemLp f₀ 2 P)
    (_hf₀_in_F : f₀ ∈ F)
    -- LEAN-ONLY: a measurable representative of the limit function.
    (hf₀_meas : Measurable f₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- LEAN-ONLY: measurability of each sample coordinate.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: iid observations with common law `P`; vdV Lemma 19.24.
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f_hat : ℕ → Ξ → (Ω → ℝ))
    -- LEAN-ONLY: joint measurability of each random function.
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (f_hat n)))
    -- USER-INPUT: class membership and mean-square `L²(P)` consistency;
    -- vdV Lemma 19.24.
    (h_range : ∀ n ω, f_hat n ω ∈ F)
    -- Expectation of squared L²-distance. Markov converts this stronger input
    -- to the explicit outer tail used by the process-difference theorem.
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (f_hat n ξ x - f₀ x) ^ 2 ∂P) μ)
    (h_l2_consistent :
      Tendsto (fun n =>
        ∫ ω, (∫ x, (f_hat n ω x - f₀ x) ^ 2 ∂P) ∂μ) atTop (𝓝 0)) :
    ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
                  empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}) atTop (𝓝 0) := by
  have hconst_meas : ∀ n, Measurable
      (Function.uncurry ((fun _ : ℕ => fun _ : Ξ => f₀) n)) := by
    intro n
    exact hf₀_meas.comp measurable_snd
  have h_outer_tail : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) f₀}) atTop (𝓝 0) := by
    intro δ hδ
    have htail : Tendsto (fun n =>
        μ {ξ | δ ≤ distL2 P (f_hat n ξ) ((fun _ : ℕ => fun _ : Ξ => f₀) n ξ)})
        atTop (𝓝 0) := by
      exact markov_distL2_tail (F := F) μ f_hat (fun _ _ => f₀)
        h_fhat_meas hconst_meas
        (fun n => by simpa using h_l2_int n)
        (by simpa using h_l2_consistent) hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
    calc
      μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) f₀}
          ≤ μ.outerMeasureStar {ξ | δ ≤ distL2 P (f_hat n ξ) f₀} :=
            outerMeasureStar_mono μ (by
              intro ξ hξ
              change δ < distL2 P (f_hat n ξ) f₀ at hξ
              change δ ≤ distL2 P (f_hat n ξ) f₀
              exact le_of_lt hξ)
      _ ≤ μ {ξ | δ ≤ distL2 P (f_hat n ξ) f₀} :=
        outerMeasureStar_le_measure_local μ _
  exact donsker_random_function_consistency_core F P h_donsker f₀ _hf₀ μ
    X hX_meas hX_iindep hX_idem hX_law f_hat h_range h_outer_tail

/-! ## Weak-convergence form -/

/-- The scalar Gaussian law obtained from the `k = 1` marginal CLT by reading
coordinate `0`. This is the law of the Brownian-bridge marginal `G_P f`.

The definition also covers zero variance: `multivariateGaussian` supplies the
degenerate Gaussian law and the continuous coordinate projection preserves it. -/
noncomputable def empiricalProcessMarginalGaussian
    (P : Measure Ω) (f : Ω → ℝ) : Measure ℝ :=
  (ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P ![f])).map
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1))

/-- **Direct scalar marginal convergence.** The iid multivariate CLT at `k = 1`,
followed by coordinate `0`, gives outer weak convergence of the fixed-function
empirical process to `empiricalProcessMarginalGaussian P f`.

This formulation needs only the selected representative's measurability and
`L²(P)` membership; no ambient function class is involved. -/
theorem empiricalProcess_weakConvergesOuter_marginalGaussian_of_memLp
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf_meas : Measurable f) (hf_memLp : MemLp f 2 P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)
      (empiricalProcessMarginalGaussian P f) := by
  classical
  obtain ⟨Y, hY_law, hY_tend⟩ := marginalCLT_fdd_of_iid (F := {f}) μ X hX_meas hX_iindep hX_idem
    hX_law (k := 1) ![f] (fun i => by fin_cases i; exact hf_memLp)
  set stdSeq : ℕ → Ξ → EuclideanSpace ℝ (Fin 1) := fun n ξ =>
    (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec ![f] (X i ξ)
      - n • ∫ ξ, tupleVec ![f] (X 0 ξ) ∂μ) with hstdSeq
  have hstd_tend : MeasureTheory.TendstoInDistribution stdSeq atTop Y (fun _ => μ)
      (ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P ![f])) := by
    simpa only [hstdSeq] using hY_tend
  set L := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) with hL
  have hcomp := hstd_tend.continuous_comp L.continuous
  have hlimit_map :
      (ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P ![f])).map (L ∘ Y) =
        empiricalProcessMarginalGaussian P f := by
    rw [empiricalProcessMarginalGaussian,
      ← AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable
        hY_law.aemeasurable, hY_law.map_eq]
  have hpt : ∀ n ξ, L (stdSeq n ξ) =
      empiricalProcess P n (fun i : Fin n => X i.val ξ) f := by
    intro n ξ
    rw [hL, hstdSeq]
    exact proj_std_eq_empiricalProcess μ X hX_meas hX_law f hf_meas hf_memLp n ξ
  have hscalar_tend := hcomp.congr
    (fun n => Eventually.of_forall fun ξ => hpt n ξ)
    (Eventually.of_forall fun _ => rfl)
  have hweak : WeakConverges
      (fun n => μ.map (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
      (empiricalProcessMarginalGaussian P f) := by
    haveI : IsProbabilityMeasure (empiricalProcessMarginalGaussian P f) := by
      rw [empiricalProcessMarginalGaussian]
      exact Measure.isProbabilityMeasure_map L.continuous.measurable.aemeasurable
    have hlim_eq :
        (⟨(ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P ![f])).map (L ∘ Y),
            Measure.isProbabilityMeasure_map hscalar_tend.aemeasurable_limit⟩ :
              ProbabilityMeasure ℝ) =
          ⟨empiricalProcessMarginalGaussian P f, inferInstance⟩ :=
      Subtype.ext hlimit_map
    intro g
    have hbridge := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (hlim_eq ▸ hscalar_tend.tendsto)) g
    simpa only [ProbabilityMeasure.coe_mk] using hbridge
  refine (weakConvergesOuter_of_measurable ?_).2 hweak
  intro n
  unfold empiricalProcess empiricalAvg
  exact measurable_const.mul ((measurable_const.mul
    (Finset.measurable_sum _ fun i _ => hf_meas.comp (hX_meas i.val))).sub measurable_const)

/-- **Class-based scalar marginal convergence.** For `f ∈ F`, the marginal CLT in
the `P`-Donsker assumption supplies the selected function's `L²(P)` membership,
and the direct fixed-function result gives the claimed outer weak convergence. -/
theorem empiricalProcess_weakConvergesOuter_marginalGaussian
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_donsker : IsPDonsker F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (f : Ω → ℝ) (hf : f ∈ F)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)
      (empiricalProcessMarginalGaussian P f) :=
  empiricalProcess_weakConvergesOuter_marginalGaussian_of_memLp P f (hF_meas f hf)
    (h_donsker.marginalCLT.memLp f hf) μ X hX_meas hX_iindep hX_idem hX_law

/-- **Lemma 19.24 (final weak-convergence form).** If `F` is `P`-Donsker and
`f_hat n` is `L²(P)`-consistent in outer probability for `f₀ ∈ L²(P)`, then the
random-index empirical process `Gₙ(f_hat n)` converges weakly in outer
expectation to the scalar Brownian-bridge marginal at `f₀`.

The representative measurability premise is used only by the direct scalar
marginal result; the process-difference theorem needs only `f₀ ∈ L²(P)`. -/
theorem donsker_random_function_consistency_weakConvergesOuter
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    -- USER-INPUT: `F` is `P`-Donsker and `f₀` is square-integrable;
    -- vdV Lemma 19.24.
    (h_donsker : IsPDonsker F P)
    (f₀ : Ω → ℝ) (hf₀ : MemLp f₀ 2 P)
    -- LEAN-ONLY: a measurable representative of the limit function.
    (hf₀_meas : Measurable f₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- LEAN-ONLY: measurability of each sample coordinate.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: iid observations with common law `P`; vdV Lemma 19.24.
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f_hat : ℕ → Ξ → (Ω → ℝ))
    -- USER-INPUT: class membership and `L²(P)` consistency in outer probability;
    -- vdV Lemma 19.24.
    (h_range : ∀ n ξ, f_hat n ξ ∈ F)
    (h_l2_consistent : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (f_hat n ξ) f₀}) atTop (𝓝 0))
    : WeakConvergesOuter (fun _ => μ)
        (fun n ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ))
        (empiricalProcessMarginalGaussian P f₀) := by
  haveI : IsProbabilityMeasure (empiricalProcessMarginalGaussian P f₀) := by
    unfold empiricalProcessMarginalGaussian
    exact Measure.isProbabilityMeasure_map
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.measurable.aemeasurable
  have hfixed := empiricalProcess_weakConvergesOuter_marginalGaussian_of_memLp P f₀
    hf₀_meas hf₀ μ X hX_meas hX_iindep hX_idem hX_law
  refine WeakConvergesOuter.slutsky_of_tendstoInOuterProbability_dist hfixed ?_
  intro δ hδ
  have htail := donsker_random_function_consistency_core F P h_donsker f₀ hf₀ μ
    X hX_meas hX_iindep hX_idem hX_law f_hat h_range h_l2_consistent (δ / 2)
      (half_pos hδ)
  have htailReal : Tendsto (fun n => μ.real
      {ξ | δ / 2 < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
        empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}) atTop (𝓝 0) := by
    simp only [Measure.real]
    have hcomp := (ENNReal.tendsto_toReal (by simp)).comp htail
    rwa [ENNReal.toReal_zero] at hcomp
  have hbound : ∀ n, μ.real {ξ | δ ≤ dist
        (empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀)
        (empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ))} ≤
      μ.real {ξ | δ / 2 <
        |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|} := by
    intro n
    refine measureReal_mono ?_ (measure_ne_top μ _)
    intro ξ hξ
    change δ ≤ dist
        (empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀)
        (empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ)) at hξ
    change δ / 2 < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
      empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|
    rw [Real.dist_eq, abs_sub_comm] at hξ
    exact lt_of_lt_of_le (half_lt_self hδ) hξ
  exact squeeze_zero (fun _ => measureReal_nonneg) hbound htailReal

end AsymptoticStatistics.EmpiricalProcess
