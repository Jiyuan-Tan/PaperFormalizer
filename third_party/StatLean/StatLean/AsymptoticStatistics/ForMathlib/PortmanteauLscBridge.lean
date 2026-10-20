module
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Probability.Kernel.Composition.Comp

@[expose] public section

/-!
# Portmanteau under weak convergence: lower semicontinuous integrand

Mathlib's `lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`
(in `MeasureTheory.Measure.Portmanteau`) takes the integrand to be continuous
nonneg. The only place continuity is used is to show that `{a | t < f a}` is open,
which is exactly the characterization of lower semicontinuity, so weakening
`Continuous f` to `LowerSemicontinuous f` is a mechanical port: the rest of the
proof (layer cake + Fatou over the level parameter) goes through unchanged.

The lsc form is what is needed when the integrand is the lower semicontinuous
envelope of a bowl-shaped loss: bowl-shaped losses need not be lsc (their sublevel
sets are convex but may not be closed), so the envelope is what Portmanteau is
applied to.

Headline declarations:
`lintegral_le_liminf_lintegral_of_lsc_of_forall_isOpen_measure_le_liminf_measure`
(ℝ-valued), its `ℝ≥0∞`-valued counterpart, and
`liminf_avgRisk_kernel_seq_le_liminf_bayesRisk`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- **LSC Portmanteau, lintegral version.** If `f : Ω → ℝ` is nonneg lsc and
the family of measures `μs` satisfies the open-set inequality `μ G ≤ liminf μs G`
for every open `G` (the standard Portmanteau premise for weak convergence), then

  `∫⁻ ENNReal.ofReal (f x) ∂μ ≤ liminf ∫⁻ ENNReal.ofReal (f x) ∂(μs i)`.

Mechanical port of Mathlib's continuous version
`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`,
weakening `Continuous f` to `LowerSemicontinuous f`. The continuity in
Mathlib's proof is used only to assert that `{a | t < f a}` is open, which
is the lsc characterization (`lowerSemicontinuous_iff_isOpen_preimage`).

Measurability of `f` follows from `LowerSemicontinuous.measurable` (Borel
machinery on the codomain `ℝ`). -/
lemma lintegral_le_liminf_lintegral_of_lsc_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ}
    (f_lsc : LowerSemicontinuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn)
              f_lsc.measurable.aemeasurable]
  calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a}) := by
        refine lintegral_mono (fun t ↦ ?_)
        exact h_opens _ ((lowerSemicontinuous_iff_isOpen_preimage.mp f_lsc) t)
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a}) := by
        exact lintegral_liminf_le (fun _ ↦ Antitone.measurable
                (fun _ _ hst ↦ measure_mono (fun _ hω ↦ lt_of_le_of_lt hst hω)))

/-- **LSC Portmanteau, ENNReal-valued lintegral version.** Same statement as the
ℝ-valued bridge above, but the integrand is itself `ℝ≥0∞`-valued (no `ENNReal.ofReal`
wrapper). Reduces to the ℝ-valued bridge by truncating `f` at each natural `N`:
the truncation `(min N (f x)).toReal` is lsc nonneg via Mathlib's `truncateToReal`,
applying the ℝ bridge per `N` and taking `⨆ N` recovers `f` by MCT, with the
sup-liminf swap closed by `Filter.iSup_liminf_le_liminf_iSup`. -/
lemma lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ≥0∞}
    (f_lsc : LowerSemicontinuous f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, f x ∂μ ≤
      atTop.liminf (fun i ↦ ∫⁻ x, f x ∂(μs i)) := by
  set f_trunc : ℕ → Ω → ℝ≥0∞ := fun N x => f x ⊓ (N : ℝ≥0∞) with hf_trunc_def
  have h_sup_eq : ∀ x, ⨆ N : ℕ, f_trunc N x = f x := by
    intro x
    simp only [hf_trunc_def]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have h_mono : Monotone f_trunc := by
    intro N M hNM x
    refine inf_le_inf_left _ ?_
    exact_mod_cast hNM
  have h_meas : ∀ N, Measurable (f_trunc N) := by
    intro N
    exact f_lsc.measurable.inf measurable_const
  have h_LHS : ∫⁻ x, f x ∂μ = ⨆ N : ℕ, ∫⁻ x, f_trunc N x ∂μ := by
    have hcong : (fun x => f x) = (fun x => ⨆ N : ℕ, f_trunc N x) := by
      funext x; exact (h_sup_eq x).symm
    rw [hcong, lintegral_iSup h_meas h_mono]
  have h_RHS_per_i : ∀ i, ∫⁻ x, f x ∂(μs i) = ⨆ N : ℕ, ∫⁻ x, f_trunc N x ∂(μs i) := by
    intro i
    have hcong : (fun x => f x) = (fun x => ⨆ N : ℕ, f_trunc N x) := by
      funext x; exact (h_sup_eq x).symm
    rw [hcong, lintegral_iSup h_meas h_mono]
  have h_per_N : ∀ N : ℕ, ∫⁻ x, f_trunc N x ∂μ
                  ≤ atTop.liminf (fun i ↦ ∫⁻ x, f_trunc N x ∂(μs i)) := by
    intro N
    set g_N : Ω → ℝ := fun x => ENNReal.truncateToReal (N : ℝ≥0∞) (f x) with hg_def
    have hN_top : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
    have h_g_lsc : LowerSemicontinuous g_N := by
      have h_cont : Continuous (ENNReal.truncateToReal (N : ℝ≥0∞)) :=
        ENNReal.continuous_truncateToReal hN_top
      have h_mon_t : Monotone (ENNReal.truncateToReal (N : ℝ≥0∞)) :=
        ENNReal.monotone_truncateToReal hN_top
      exact h_cont.comp_lowerSemicontinuous f_lsc h_mon_t
    have h_g_nn : 0 ≤ g_N := fun _ => ENNReal.truncateToReal_nonneg
    have h_ofReal_eq : ∀ x, ENNReal.ofReal (g_N x) = f_trunc N x := by
      intro x
      simp only [hg_def, hf_trunc_def, ENNReal.truncateToReal]
      rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top hN_top (min_le_left _ _))]
      exact min_comm _ _
    have h_R := lintegral_le_liminf_lintegral_of_lsc_of_forall_isOpen_measure_le_liminf_measure
                  h_g_lsc h_g_nn h_opens
    simp_rw [h_ofReal_eq] at h_R
    exact h_R
  rw [h_LHS]
  refine iSup_le fun N => ?_
  refine (h_per_N N).trans ?_
  refine Filter.liminf_le_liminf ?_
  refine Filter.Eventually.of_forall fun i => ?_
  rw [h_RHS_per_i i]
  exact le_iSup (fun N => ∫⁻ x, f_trunc N x ∂(μs i)) N

-- Glue lemma consumed by `bayes_risk_lan_limit_gaussianTauPrior` to translate
-- per-`h` weak convergence of the kernel-bind sequence into a `liminf` bound on
-- the average kernel risk.
section W80VdVDirectB6

variable {Ω 𝓨 : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
variable [MeasurableSpace 𝓨] [TopologicalSpace 𝓨] [OpensMeasurableSpace 𝓨]

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [TopologicalSpace 𝓨] [OpensMeasurableSpace 𝓨] in
/-- **Liminf of average kernel risk bounded by Bayes risk via Portmanteau-lsc.**

For any prior `π` on `Ω`, any data-kernel sequence `μ_n : Kernel Ω 𝓨` weakly
convergent per-`h` to a limit kernel-bind family, any estimator-kernel sequence
`κ_n : Kernel 𝓨 Ω'` whose composition with `μ_n` is weakly convergent per-`h`,
and any nonneg lsc loss `f : Ω → Ω' → ℝ≥0∞`, the `liminf` of the π-averaged
composite-kernel risks bounds the limit risk.

A glue lemma (no project-specific kernel data): the signature is stated abstractly
so the body relies only on the lsc-Portmanteau bridge above + Fubini.

Proof outline:
1. Per-`h`: apply
`lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure`
   to the composite measure `(κ_n ∘ₖ μ_n) h` and the nonneg lsc `fun y => f h y`.
   Yields `∫⁻ y, f h y ∂((κLim ∘ₖ μLim) h) ≤ liminf_n ∫⁻ y, f h y ∂((κ_n ∘ₖ μ_n) h)`.
2. π-average: integrate against `π`. The liminf-on-the-RHS commutes through
   the π-integral via Fatou (right direction: `∫ liminf ≤ liminf ∫`). -/
theorem liminf_avgRisk_kernel_seq_le_liminf_bayesRisk
    (π : Measure Ω)
    -- data-kernel sequence (vdV §8.5: the experiment measures, viewed as a `Kernel`).
    (μ_n : ∀ n : ℕ, Kernel Ω 𝓨)
    -- limit kernel-bind family (e.g. `h ↦ multivariateGaussian h J⁻¹`).
    (μLim : Kernel Ω 𝓨)
    -- estimator kernel, generalised to `Kernel 𝓨 Ω'` for any output type.
    {Ω' : Type*} [MeasurableSpace Ω'] [TopologicalSpace Ω'] [OpensMeasurableSpace Ω']
    (κ_n : ∀ n : ℕ, Kernel 𝓨 Ω') (κLim : Kernel 𝓨 Ω')
    -- per-`h` weak convergence (vdV §8.5: obtained via Prohorov tightness + Le Cam
    -- contiguity + diagonal subsequence).
    (h_weak : ∀ h : Ω,
      ∀ G : Set Ω', IsOpen G →
        ((κLim ∘ₖ μLim) h) G ≤
          atTop.liminf (fun n : ℕ => ((κ_n n ∘ₖ μ_n n) h) G))
    -- joint lsc loss (bowl-shaped lsc `L` + continuous translation ⇒ joint lsc).
    (f : Ω → Ω' → ℝ≥0∞) (hf_lsc : ∀ h : Ω, LowerSemicontinuous (f h))
    (h_meas_seq : ∀ n : ℕ, Measurable
      (fun h : Ω => ∫⁻ y, f h y ∂((κ_n n ∘ₖ μ_n n) h)))
    (_h_meas_inf : Measurable (fun h : Ω => ∫⁻ y, f h y ∂((κLim ∘ₖ μLim) h))) :
    ∫⁻ h, ∫⁻ y, f h y ∂((κLim ∘ₖ μLim) h) ∂π
      ≤ atTop.liminf
        (fun n : ℕ => ∫⁻ h, ∫⁻ y, f h y ∂((κ_n n ∘ₖ μ_n n) h) ∂π) := by
  -- Step 1: per-`h`, apply the ENNReal LSC-Portmanteau bridge
  -- to the composite measures `(κLim ∘ₖ μLim) h` and `(κ_n n ∘ₖ μ_n n) h`,
  -- with the fixed lsc integrand `fun y => f h y`.
  have h_per_h : ∀ h : Ω,
      ∫⁻ y, f h y ∂((κLim ∘ₖ μLim) h) ≤
        atTop.liminf (fun n : ℕ => ∫⁻ y, f h y ∂((κ_n n ∘ₖ μ_n n) h)) := by
    intro h
    exact lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure
      (hf_lsc h) (h_weak h)
  -- Step 2: integrate the pointwise bound against `π` via `lintegral_mono`,
  -- then apply Fatou (`lintegral_liminf_le`) to push the `liminf` outside.
  calc ∫⁻ h, ∫⁻ y, f h y ∂((κLim ∘ₖ μLim) h) ∂π
      ≤ ∫⁻ h, atTop.liminf
            (fun n : ℕ => ∫⁻ y, f h y ∂((κ_n n ∘ₖ μ_n n) h)) ∂π :=
        lintegral_mono h_per_h
    _ ≤ atTop.liminf
            (fun n : ℕ => ∫⁻ h, ∫⁻ y, f h y ∂((κ_n n ∘ₖ μ_n n) h) ∂π) :=
        lintegral_liminf_le h_meas_seq

end W80VdVDirectB6

end AsymptoticStatistics
