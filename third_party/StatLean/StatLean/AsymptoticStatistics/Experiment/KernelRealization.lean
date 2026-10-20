module
public import Mathlib.Probability.Kernel.Disintegration.CondCDF
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

/-!
# Kernel realization of conditional distributions (vdV Lemma 7.11)

vdV §7 Lemma 7.11: given a random vector `(S, Δ)` valued in `ℝ^d × ℝ^k` and an
independent `Uniform[0,1]^d` vector `U`, there exists a jointly measurable
`T : ℝ^k × [0,1]^d → ℝ^d` with `(T(Δ, U), Δ)` equal in distribution to `(S, Δ)`.

This is recast at the kernel level: the kernel `κ : Kernel ℝ^k ℝ^d` furnished by
`ProbabilityTheory.condDistrib` admits a measurable `U`-realization. The construction
proceeds by inverse-transform sampling of the 1D quantile (`StieltjesFunction.leftInverse`),
joint measurability of the parametrised quantile, a 1D kernel realisation
(`hasUniformRealization_1d`), and coordinate-by-coordinate recursion via conditional CDFs
(`hasUniformRealization`).

Headline declarations: `hasUniformRealization` (multi-dimensional kernel realisation) and
`kernel_realization_of_joint_distribution` (the vdV corollary).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics
namespace KernelRealization

/-! ## Step 1 — One-dimensional quantile (generalized inverse of a Stieltjes function)

For a `StieltjesFunction` `F : ℝ → ℝ` that is a CDF (i.e. `F → 0` at `-∞` and `F → 1`
at `+∞`), the left-continuous inverse
`F.leftInverse u = sInf { x : u ≤ F x }`
transports `Lebesgue` restricted to `(0,1)` to the Stieltjes measure of `F`.
-/

/-- Generalized (left-continuous) inverse of a real Stieltjes function:
`F.leftInverse u = sInf { x | u ≤ F x }`.

Defined on all of `ℝ`; behaves well on `(0,1)` when `F` is a CDF
(i.e. tends to `0` at `-∞` and to `1` at `+∞`). -/
noncomputable def _root_.StieltjesFunction.leftInverse (F : StieltjesFunction ℝ) (u : ℝ) : ℝ :=
  sInf { x : ℝ | u ≤ F x }

/-- The set used to define `leftInverse` is bounded below for `u > 0`, provided
`F → 0` at `-∞`. -/
lemma leftInverse_set_bddBelow (F : StieltjesFunction ℝ)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    {u : ℝ} (hu : 0 < u) :
    BddBelow { x : ℝ | u ≤ F x } := by
  obtain ⟨N, hN⟩ :=
    eventually_atBot.mp (hF_atBot.eventually (gt_mem_nhds hu))
  refine ⟨N, fun x hx => ?_⟩
  by_contra h_lt
  push Not at h_lt
  exact absurd hx (not_le.mpr (hN x h_lt.le))

/-- The set used to define `leftInverse` is nonempty for `u < 1`, provided
`F → 1` at `+∞`. -/
lemma leftInverse_set_nonempty (F : StieltjesFunction ℝ)
    (hF_atTop : Tendsto F atTop (𝓝 1))
    {u : ℝ} (hu' : u < 1) :
    { x : ℝ | u ≤ F x }.Nonempty := by
  obtain ⟨N, hN⟩ :=
    eventually_atTop.mp (hF_atTop.eventually (lt_mem_nhds hu'))
  exact ⟨N, (hN N le_rfl).le⟩

/-- **Galois-type characterisation** of `leftInverse` on `(0,1)`:
`F.leftInverse u ≤ x ↔ u ≤ F x` (for `u ∈ (0,1)` and `F` a CDF).

This is the key monotone/measurability engine: `leftInverse` is the left adjoint
of the (monotone, right-continuous) CDF `F`. -/
lemma leftInverse_le_iff (F : StieltjesFunction ℝ)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    (hF_atTop : Tendsto F atTop (𝓝 1))
    {u x : ℝ} (hu : 0 < u) (hu' : u < 1) :
    F.leftInverse u ≤ x ↔ u ≤ F x := by
  have hS_ne : { y : ℝ | u ≤ F y }.Nonempty :=
    leftInverse_set_nonempty F hF_atTop hu'
  have hS_bb : BddBelow { y : ℝ | u ≤ F y } :=
    leftInverse_set_bddBelow F hF_atBot hu
  refine ⟨fun h => ?_, fun h => csInf_le hS_bb h⟩
  have h_all_gt : ∀ r : ℝ, x < r → u ≤ F r := by
    intro r hr
    obtain ⟨y, hy_mem, hy_lt⟩ :=
      exists_lt_of_csInf_lt hS_ne (lt_of_le_of_lt h hr)
    exact hy_mem.trans (F.mono hy_lt.le)
  haveI : Nonempty (Set.Ioi x) := ⟨⟨x + 1, show x < x + 1 by linarith⟩⟩
  calc u ≤ ⨅ r : Set.Ioi x, F r := le_ciInf (fun r => h_all_gt r.1 r.2)
    _ = F x := F.iInf_Ioi_eq x

/-- `leftInverse` is `MonotoneOn` the open interval `(0, 1)` under the CDF hypothesis.
(Global `Monotone` fails because `sInf ∅ = 0` in Mathlib's convention, so the map
can jump at `u ≤ 0`.) -/
lemma leftInverse_monotoneOn (F : StieltjesFunction ℝ)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    (hF_atTop : Tendsto F atTop (𝓝 1)) :
    MonotoneOn F.leftInverse (Set.Ioo (0 : ℝ) 1) := by
  intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv
  have hu2 : u < 1 := lt_of_le_of_lt huv hv2
  have hv1 : 0 < v := lt_of_lt_of_le hu1 huv
  -- v ≤ F (F.leftInverse v): instantiate the iff at x := F.leftInverse v, w := v.
  have h_v_self : v ≤ F (F.leftInverse v) :=
    (leftInverse_le_iff F hF_atBot hF_atTop hv1 hv2).mp le_rfl
  -- Then leftInverse u ≤ leftInverse v via the iff at w := u, x := F.leftInverse v.
  exact (leftInverse_le_iff F hF_atBot hF_atTop hu1 hu2).mpr (huv.trans h_v_self)

/-- For a CDF `F`, `F.leftInverse u = 0` whenever `u ≤ 0` (the defining set is all of `ℝ`
since `F ≥ 0` globally, and `sInf (univ : Set ℝ) = 0` by Mathlib's convention). -/
lemma leftInverse_of_nonpos (F : StieltjesFunction ℝ)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    {u : ℝ} (hu : u ≤ 0) : F.leftInverse u = 0 := by
  have hF_nonneg : ∀ x, 0 ≤ F x := fun x =>
    le_of_tendsto hF_atBot ((eventually_le_atBot x).mono fun z hz => F.mono hz)
  have h_set : { x : ℝ | u ≤ F x } = Set.univ :=
    Set.eq_univ_of_forall fun x => hu.trans (hF_nonneg x)
  have h_nbb : ¬ BddBelow (Set.univ : Set ℝ) := fun ⟨b, hb⟩ =>
    absurd (hb (Set.mem_univ (b - 1))) (by linarith)
  change sInf _ = 0
  rw [h_set]; exact Real.sInf_of_not_bddBelow h_nbb

/-- For a CDF `F`, `F.leftInverse u = 0` whenever `u > 1` (the defining set is empty
since `F ≤ 1` globally, and `sInf (∅ : Set ℝ) = 0` by Mathlib's convention). -/
lemma leftInverse_of_one_lt (F : StieltjesFunction ℝ)
    (hF_atTop : Tendsto F atTop (𝓝 1))
    {u : ℝ} (hu : 1 < u) : F.leftInverse u = 0 := by
  have hF_le_one : ∀ x, F x ≤ 1 := fun x =>
    ge_of_tendsto hF_atTop ((eventually_ge_atTop x).mono fun z hz => F.mono hz)
  have h_set : { x : ℝ | u ≤ F x } = ∅ :=
    Set.eq_empty_of_forall_notMem fun x hx =>
      absurd (hx.trans (hF_le_one x)) (not_le.mpr hu)
  change sInf _ = 0
  rw [h_set]; exact Real.sInf_empty

/-- `leftInverse` is measurable (as a function `ℝ → ℝ`) under the CDF hypotheses.

Proof strategy: compute the preimage `F.leftInverse ⁻¹' Iic y` as a union of three pieces:
  * `Ioo 0 1 ∩ Iic (F y)` — by the Galois iff.
  * Constant-0 region (`Iic 0 ∪ Ioi 1`) when `0 ≤ y`, empty otherwise.
  * The singleton `{1}` when `F.leftInverse 1 ≤ y`, empty otherwise.
All three are measurable. -/
lemma leftInverse_measurable (F : StieltjesFunction ℝ)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    (hF_atTop : Tendsto F atTop (𝓝 1)) :
    Measurable F.leftInverse := by
  apply measurable_of_Iic
  intro y
  have h_eq : F.leftInverse ⁻¹' Set.Iic y =
      (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (F y))
        ∪ (if (0 : ℝ) ≤ y then Set.Iic 0 ∪ Set.Ioi 1 else ∅)
        ∪ (if F.leftInverse 1 ≤ y then ({1} : Set ℝ) else ∅) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
      Set.mem_Ioo]
    constructor
    · intro h_li_le
      rcases lt_trichotomy u 1 with hu1 | hu1 | hu1
      · rcases le_or_gt u 0 with hu0 | hu0
        · -- u ≤ 0: leftInverse u = 0, so 0 ≤ y.
          rw [leftInverse_of_nonpos F hF_atBot hu0] at h_li_le
          left; right; rw [if_pos h_li_le]; left; exact hu0
        · -- 0 < u < 1: Galois iff.
          left; left
          exact ⟨⟨hu0, hu1⟩,
            (leftInverse_le_iff F hF_atBot hF_atTop hu0 hu1).mp h_li_le⟩
      · -- u = 1.
        subst hu1
        right; rw [if_pos h_li_le]; rfl
      · -- u > 1: leftInverse u = 0, so 0 ≤ y.
        rw [leftInverse_of_one_lt F hF_atTop hu1] at h_li_le
        left; right; rw [if_pos h_li_le]; right; exact hu1
    · rintro ((h_gal | h_outside) | h_one)
      · obtain ⟨⟨hu0, hu1⟩, h_fy⟩ := h_gal
        exact (leftInverse_le_iff F hF_atBot hF_atTop hu0 hu1).mpr h_fy
      · split_ifs at h_outside with h_sy
        · rcases h_outside with hu0 | hu1
          · rw [leftInverse_of_nonpos F hF_atBot hu0]; exact h_sy
          · rw [leftInverse_of_one_lt F hF_atTop hu1]; exact h_sy
        · exact absurd h_outside (Set.notMem_empty u)
      · split_ifs at h_one with h_ly
        · rw [Set.mem_singleton_iff.mp h_one]; exact h_ly
        · exact absurd h_one (Set.notMem_empty u)
  rw [h_eq]
  refine MeasurableSet.union (MeasurableSet.union ?_ ?_) ?_
  · exact measurableSet_Ioo.inter measurableSet_Iic
  · split_ifs
    · exact measurableSet_Iic.union measurableSet_Ioi
    · exact MeasurableSet.empty
  · split_ifs
    · exact measurableSet_singleton 1
    · exact MeasurableSet.empty

/-- **Inverse-transform sampling (1D).** Push-forward of `Uniform[0,1]` (i.e. Lebesgue
restricted to `(0,1)`) under `F.leftInverse` equals the Stieltjes measure of `F`,
when `F` is a CDF. -/
lemma leftInverse_map_uniform (F : StieltjesFunction ℝ)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    (hF_atTop : Tendsto F atTop (𝓝 1)) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).map F.leftInverse = F.measure := by
  have h_meas := leftInverse_measurable F hF_atBot hF_atTop
  have hF_nonneg : ∀ x, 0 ≤ F x := fun x =>
    le_of_tendsto hF_atBot ((eventually_le_atBot x).mono fun z hz => F.mono hz)
  have hF_le_one : ∀ x, F x ≤ 1 := fun x =>
    ge_of_tendsto hF_atTop ((eventually_ge_atTop x).mono fun z hz => F.mono hz)
  haveI : IsProbabilityMeasure F.measure := F.isProbabilityMeasure hF_atBot hF_atTop
  haveI : IsFiniteMeasure ((volume.restrict (Set.Ioo (0 : ℝ) 1)).map F.leftInverse) := by
    refine ⟨?_⟩
    rw [Measure.map_apply h_meas MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_lt_top
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply h_meas measurableSet_Iic,
    Measure.restrict_apply (h_meas measurableSet_Iic),
    F.measure_Iic hF_atBot a, sub_zero]
  -- Preimage on Ioo 0 1: Galois iff gives F.leftInverse ⁻¹' Iic a ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (F a).
  have h_preimage : F.leftInverse ⁻¹' Set.Iic a ∩ Set.Ioo (0 : ℝ) 1
                  = Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (F a) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h_li_le, hu0, hu1⟩
      exact ⟨⟨hu0, hu1⟩,
        (leftInverse_le_iff F hF_atBot hF_atTop hu0 hu1).mp h_li_le⟩
    · rintro ⟨⟨hu0, hu1⟩, h_fy⟩
      exact ⟨(leftInverse_le_iff F hF_atBot hF_atTop hu0 hu1).mpr h_fy, hu0, hu1⟩
  rw [h_preimage]
  -- volume (Ioo 0 1 ∩ Iic (F a)) = ENNReal.ofReal (F a)
  rcases eq_or_lt_of_le (hF_le_one a) with h_eq | h_lt
  · -- F a = 1: intersection = Ioo 0 1 (since Ioo 0 1 ⊆ Iic 1).
    rw [h_eq]
    have h_set : Set.Ioo (0 : ℝ) 1 ∩ Set.Iic 1 = Set.Ioo 0 1 := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, and_iff_left_iff_imp]
      exact fun h => h.2.le
    rw [h_set, Real.volume_Ioo, sub_zero]
  · -- F a < 1: intersection = Ioc 0 (F a).
    have h_set : Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (F a) = Set.Ioc (0 : ℝ) (F a) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans_lt h_lt⟩, h2⟩
    rw [h_set, Real.volume_Ioc, sub_zero]

/-! ## Step 2 — Joint measurability of the parametrised quantile

In the conditional setting, we want the *parametrised* quantile `(a, u) ↦ (F a).leftInverse u`
to be jointly measurable in `(a, u)`, when `a ↦ F a` is a measurable family of Stieltjes
functions in the sense used by Mathlib's conditional-CDF machinery (namely, `a ↦ F a r`
is measurable for every `r : ℝ`). -/

/-- Joint measurability of a parametric **clamped** quantile: if every pointwise
evaluation `a ↦ F a r` is measurable and each `F a` is a CDF, then the clamped quantile
`(a, u) ↦ if u ∈ (0, 1) then (F a).leftInverse u else 0` is jointly measurable in `(a, u)`.

*Why the clamp?* The un-clamped `(F a).leftInverse u` is globally measurable in `u`
only after observing a singleton `{1}` correction (see `leftInverse_measurable`). The
corresponding parametric correction `a ↦ (F a).leftInverse 1` is **not** recoverable
from the pointwise hypothesis `∀ r, Measurable (a ↦ F a r)`. Since `Uniform[0,1]` does
not charge `{1}`, clamping to `0` at the boundary is harmless for pushforwards. -/
lemma parametric_leftInverse_measurable {α : Type*} [MeasurableSpace α]
    (F : α → StieltjesFunction ℝ)
    (hF_meas : ∀ r : ℝ, Measurable fun a => F a r)
    (hF_atBot : ∀ a, Tendsto (F a) atBot (𝓝 0))
    (hF_atTop : ∀ a, Tendsto (F a) atTop (𝓝 1)) :
    Measurable
      (fun p : α × ℝ =>
        if p.2 ∈ Set.Ioo (0 : ℝ) 1 then (F p.1).leftInverse p.2 else 0) := by
  apply measurable_of_Iic
  intro y
  change MeasurableSet
      {p : α × ℝ |
        (if p.2 ∈ Set.Ioo (0 : ℝ) 1 then (F p.1).leftInverse p.2 else 0) ≤ y}
  -- The preimage decomposes into:
  --   (1) { p | p.2 ∈ Ioo 0 1 ∧ p.2 ≤ F p.1 y }    (via Galois iff)
  --   (2) if 0 ≤ y then { p | p.2 ∉ Ioo 0 1 } else ∅
  have h_eq :
      {p : α × ℝ |
        (if p.2 ∈ Set.Ioo (0 : ℝ) 1 then (F p.1).leftInverse p.2 else 0) ≤ y}
      = {p : α × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ≤ F p.1 y}
        ∪ (if (0 : ℝ) ≤ y then {p : α × ℝ | p.2 ∉ Set.Ioo (0 : ℝ) 1} else ∅) := by
    ext ⟨a, u⟩
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hu : u ∈ Set.Ioo (0 : ℝ) 1
      · rw [if_pos hu] at h
        obtain ⟨hu0, hu1⟩ := hu
        exact Or.inl ⟨⟨hu0, hu1⟩,
          (leftInverse_le_iff (F a) (hF_atBot a) (hF_atTop a) hu0 hu1).mp h⟩
      · rw [if_neg hu] at h
        exact Or.inr (by rw [if_pos h]; exact hu)
    · rintro (⟨⟨hu0, hu1⟩, h_fy⟩ | h_out)
      · rw [if_pos ⟨hu0, hu1⟩]
        exact (leftInverse_le_iff (F a) (hF_atBot a) (hF_atTop a) hu0 hu1).mpr h_fy
      · split_ifs at h_out with h_0y
        · rw [if_neg h_out]; exact h_0y
        · exact absurd h_out (Set.notMem_empty _)
  rw [h_eq]
  refine MeasurableSet.union ?_ ?_
  · -- { p | p.2 ∈ Ioo 0 1 ∧ p.2 ≤ F p.1 y } is measurable.
    have h_Ioo : MeasurableSet {p : α × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1} :=
      measurable_snd measurableSet_Ioo
    have h_le : MeasurableSet {p : α × ℝ | p.2 ≤ F p.1 y} :=
      measurableSet_le measurable_snd ((hF_meas y).comp measurable_fst)
    convert! h_Ioo.inter h_le using 1
  · split_ifs
    · exact (measurable_snd measurableSet_Ioo).compl
    · exact MeasurableSet.empty

/-! ## Step 3 — 1D kernel has a uniform realisation

For a jointly measurable family of CDFs `F : α → StieltjesFunction ℝ`, we get a measurable
`T : α × ℝ → ℝ` such that `T(a, ·)` pushes `Uniform[0,1]` to `(F a).measure`. The Kernel
form (`hasUniformRealization_1d` below) is a 5-line wrapper once one extracts such an `F`
from the kernel (via Mathlib's `IsMeasurableRatCDF.stieltjesFunction` infrastructure).
-/

/-- **1D uniform realisation for a Stieltjes family.** Given a jointly measurable family
`F : α → StieltjesFunction ℝ` of CDFs, there is a measurable `T : α × ℝ → ℝ` such that
for every `a`, the push-forward of `Uniform[0,1]` under `T(a, ·)` equals `(F a).measure`.
-/
lemma hasUniformRealization_1d_of_stieltjes {α : Type*} [MeasurableSpace α]
    (F : α → StieltjesFunction ℝ)
    (hF_meas : ∀ r : ℝ, Measurable fun a => F a r)
    (hF_atBot : ∀ a, Tendsto (F a) atBot (𝓝 0))
    (hF_atTop : ∀ a, Tendsto (F a) atTop (𝓝 1)) :
    ∃ T : α × ℝ → ℝ,
      Measurable T ∧
      ∀ a, (volume.restrict (Set.Ioo (0 : ℝ) 1)).map (fun u => T (a, u)) = (F a).measure := by
  refine ⟨fun p => if p.2 ∈ Set.Ioo (0 : ℝ) 1 then (F p.1).leftInverse p.2 else 0, ?_, ?_⟩
  · exact parametric_leftInverse_measurable F hF_meas hF_atBot hF_atTop
  · intro a
    -- Clamp-vs-raw leftInverse agree on the support `Ioo 0 1` of the source measure.
    have h_ae_eq :
        (fun u : ℝ => if u ∈ Set.Ioo (0 : ℝ) 1 then (F a).leftInverse u else 0)
          =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (F a).leftInverse := by
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ ?_)
      intro u hu
      exact if_pos hu
    rw [Measure.map_congr h_ae_eq]
    exact leftInverse_map_uniform (F a) (hF_atBot a) (hF_atTop a)

/-- **1D kernel `U`-realisation.** For a Markov kernel `κ : Kernel α ℝ`, there
exists a jointly measurable `T : α × ℝ → ℝ` such that for every `a : α`, the
push-forward of `Uniform[0,1]` (i.e. `volume.restrict (Ioo 0 1)`) under `T(a, ·)`
equals `κ a`.

Proof: combine `hasUniformRealization_1d_of_stieltjes` with the bridge
`Kernel α ℝ → (F : α → StieltjesFunction ℝ)` that extracts the pointwise CDF
of a Markov kernel's components. The bridge sits on top of Mathlib's `IsMeasurableRatCDF`:
define `f a q := ((κ a) (Iic q)).toReal` and check the structure, then feed to
`IsMeasurableRatCDF.stieltjesFunction`; the `(F a).measure = κ a` step closes via
`Measure.ext_of_Iic` since both sides agree on `Iic q` for rational `q`. -/
lemma hasUniformRealization_1d {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [IsMarkovKernel κ] :
    ∃ T : α × ℝ → ℝ,
      Measurable T ∧
      ∀ a, (volume.restrict (Set.Ioo (0 : ℝ) 1)).map (fun u => T (a, u)) = κ a := by
  -- Step 1: rational CDF `f a q := ((κ a)(Iic q)).toReal`.
  let f : α → ℚ → ℝ := fun a q => ((κ a) (Set.Iic (q : ℝ))).toReal
  have hf_meas : Measurable f := measurable_pi_iff.mpr fun q =>
    (Kernel.measurable_coe κ measurableSet_Iic).ennreal_toReal
  -- Cast ℚ → ℝ sends atTop to atTop and atBot to atBot.
  have h_cast_atTop : Tendsto ((↑) : ℚ → ℝ) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨q, hq⟩ := exists_rat_gt b
    exact ⟨q, fun q' hqq' => le_of_lt hq |>.trans (by exact_mod_cast hqq')⟩
  have h_cast_atBot : Tendsto ((↑) : ℚ → ℝ) atBot atBot := by
    rw [Filter.tendsto_atBot_atBot]
    intro b
    obtain ⟨q, hq⟩ := exists_rat_lt b
    exact ⟨q, fun q' hqq' => (by exact_mod_cast hqq' : (q' : ℝ) ≤ q).trans hq.le⟩
  -- Step 2: each `f a` is a rat-Stieltjes point.
  have hf_point : ∀ a : α, IsRatStieltjesPoint f a := by
    intro a
    -- atBot limit of κ a on Iic: `⋂ x, Iic x = ∅` so the measure tends to 0.
    have h_iInter_Iic : ⋂ x : ℝ, Set.Iic x = (∅ : Set ℝ) := by
      ext y
      simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      exact ⟨y - 1, by linarith⟩
    have h_meas_Iic_atBot : Tendsto (fun x : ℝ => (κ a) (Set.Iic x)) atBot (𝓝 0) := by
      have := tendsto_measure_iInter_atBot
        (μ := κ a) (s := (Set.Iic : ℝ → Set ℝ))
        (fun _ => measurableSet_Iic.nullMeasurableSet) monotone_Iic
        ⟨0, (measure_ne_top _ _)⟩
      rw [h_iInter_Iic, measure_empty] at this
      exact this
    have h_meas_Iic_atTop : Tendsto (fun x : ℝ => (κ a) (Set.Iic x)) atTop (𝓝 1) := by
      have := tendsto_measure_Iic_atTop (κ a)
      rwa [measure_univ] at this
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- mono
      intro q r hqr
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact measure_mono (Set.Iic_subset_Iic.mpr (by exact_mod_cast hqr))
    · -- tendsto atTop 1
      have h_ennreal : Tendsto (fun q : ℚ => (κ a) (Set.Iic (q : ℝ))) atTop (𝓝 1) :=
        h_meas_Iic_atTop.comp h_cast_atTop
      simpa using! (ENNReal.tendsto_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).comp h_ennreal
    · -- tendsto atBot 0
      have h_ennreal : Tendsto (fun q : ℚ => (κ a) (Set.Iic (q : ℝ))) atBot (𝓝 0) :=
        h_meas_Iic_atBot.comp h_cast_atBot
      simpa using! (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp h_ennreal
    · -- iInf right-continuity: ⨅ r : Ioi t, f a r = f a t.
      intro t
      -- Step A: the intersection of `Iic r` for rationals r > t equals `Iic t` (in ℝ).
      have h_iInter :
          (⋂ r : Set.Ioi t, Set.Iic ((r : ℚ) : ℝ)) = Set.Iic (t : ℝ) := by
        ext x
        simp only [Set.mem_iInter, Set.mem_Iic, Subtype.forall, Set.mem_Ioi]
        refine ⟨fun h => le_of_forall_lt_rat_imp_le fun q htq => h q (by exact_mod_cast htq),
               fun hxt r htr => hxt.trans (by exact_mod_cast htr.le)⟩
      -- Step B: measure of intersection = ⨅ of measures (downward continuity).
      have h_meas_iInter :
          (κ a) (⋂ r : Set.Ioi t, Set.Iic ((r : ℚ) : ℝ))
            = ⨅ r : Set.Ioi t, (κ a) (Set.Iic ((r : ℚ) : ℝ)) := by
        refine Monotone.measure_iInter ?_ ?_ ?_
        · intro r₁ r₂ h
          exact Set.Iic_subset_Iic.mpr (by exact_mod_cast h)
        · exact fun _ => measurableSet_Iic.nullMeasurableSet
        · refine ⟨⟨t + 1, ?_⟩, measure_ne_top _ _⟩
          change t < t + 1
          exact lt_add_one t
      rw [h_iInter] at h_meas_iInter
      -- Step C: toReal commutes with iInf on bounded ENNReal family.
      change ⨅ r : Set.Ioi t, (κ a (Set.Iic ((r : ℚ) : ℝ))).toReal
        = (κ a (Set.Iic (t : ℝ))).toReal
      rw [h_meas_iInter, ENNReal.toReal_iInf (fun _ => measure_ne_top _ _)]
  -- Step 3: Stieltjes family.
  have hf_cdf : IsMeasurableRatCDF f := ⟨hf_point, hf_meas⟩
  let F : α → StieltjesFunction ℝ := fun a => hf_cdf.stieltjesFunction a
  have hF_meas_pt : ∀ r : ℝ, Measurable fun a => F a r :=
    IsMeasurableRatCDF.measurable_stieltjesFunction hf_cdf
  have hF_atBot : ∀ a, Tendsto (F a) atBot (𝓝 0) :=
    IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot hf_cdf
  have hF_atTop : ∀ a, Tendsto (F a) atTop (𝓝 1) :=
    IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop hf_cdf
  -- Step 4: `(F a).measure = κ a` via π-system of rational Iic's.
  have h_measure_eq : ∀ a, (F a).measure = κ a := by
    intro a
    refine MeasureTheory.ext_of_generate_finite (⋃ q : ℚ, {Set.Iic (q : ℝ)})
        (BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Iic_rat)
        Real.isPiSystem_Iic_rat ?_ ?_
    · rintro s hs
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
      obtain ⟨q, rfl⟩ := hs
      rw [IsMeasurableRatCDF.measure_stieltjesFunction_Iic,
        IsMeasurableRatCDF.stieltjesFunction_eq hf_cdf a q]
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)
    · rw [IsMeasurableRatCDF.measure_stieltjesFunction_univ, measure_univ]
  -- Step 5: combine.
  obtain ⟨T, hT_meas, hT_law⟩ :=
    hasUniformRealization_1d_of_stieltjes F hF_meas_pt hF_atBot hF_atTop
  exact ⟨T, hT_meas, fun a => (hT_law a).trans (h_measure_eq a)⟩

/-! ## Step 4 — Multi-dimensional kernel `U`-realisation

Take `d` independent uniforms up-front, then iterate the 1D realization plus
conditional disintegration. The `ℝ ≃ᵐ ℝ × ℝ` "split one uniform into two"
construction (needed only to match vdV's strict one-`U` form) is the optional
add-on in §5 below.

We build `T : α × (Fin d → ℝ) → (Fin d → ℝ)` by induction on `d`:

* `d = 0`: `Fin 0 → ℝ` is the singleton type (the empty function). Every
  probability measure on it is the Dirac on that point; `T` returns the empty
  function. Pushforward of the empty product measure under the constant map is
  Dirac on the empty point, matching `κ a`.
* `d = n + 1`: apply 1D realization (`hasUniformRealization_1d`) to the first
  marginal of `κ`; condition on the first coordinate's realized value to get a
  kernel for the remaining `n` coordinates; apply induction hypothesis; combine
  via `Fin.cons`. -/

/-- **Multi-d kernel `U`-realisation.** For a Markov kernel
`κ : Kernel α (Fin d → ℝ)`, there exists a jointly measurable
`T : α × (Fin d → ℝ) → (Fin d → ℝ)` such that for every `a : α`, the push-forward
of `(Uniform[0,1])^d` under `T(a, ·)` equals `κ a`. -/
lemma hasUniformRealization {α : Type*} [MeasurableSpace α] {d : ℕ}
    (κ : Kernel α (Fin d → ℝ)) [IsMarkovKernel κ] :
    ∃ T : α × (Fin d → ℝ) → (Fin d → ℝ),
      Measurable T ∧
      ∀ a, (Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioo (0 : ℝ) 1))).map
              (fun U => T (a, U)) = κ a := by
  induction d generalizing α with
  | zero =>
    -- `Fin 0 → ℝ` is a singleton (the empty function); every probability measure
    -- on it is the Dirac there, so both sides coincide regardless of `T`.
    refine ⟨fun p => p.2, measurable_snd, fun a => ?_⟩
    rw [show (fun U : Fin 0 → ℝ => (fun p : α × (Fin 0 → ℝ) => p.2) (a, U)) = id from rfl,
        Measure.map_id, Measure.pi_of_empty]
    -- Goal: Measure.dirac isEmptyElim = κ a.  Both are probability measures on
    -- a Subsingleton type, so equal.
    symm
    apply Measure.ext
    intro s _
    rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp
    · have hs : s = Set.univ :=
        Set.eq_univ_of_forall fun y => (Subsingleton.elim y x).symm ▸ hx
      rw [hs, measure_univ, Measure.dirac_apply_of_mem (Set.mem_univ _)]
  | succ n ih =>
    -- View `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)` (head/tail).
    let e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    -- Map κ through e; first marginal; conditional kernel for the rest.
    let κ' : Kernel α (ℝ × (Fin n → ℝ)) := κ.map e
    haveI : IsMarkovKernel κ' := Kernel.IsMarkovKernel.map κ e.measurable
    let κ₀ : Kernel α ℝ := κ'.fst
    let κ_rest : Kernel (α × ℝ) (Fin n → ℝ) := κ'.condKernel
    -- Recursive realizations.
    obtain ⟨T₁, hT₁_meas, hT₁_law⟩ := hasUniformRealization_1d κ₀
    obtain ⟨T_rest, hT_rest_meas, hT_rest_law⟩ := ih κ_rest
    -- Combine: T(a, U) = Fin.cons (T₁(a, U 0)) (T_rest((a, x₀), tail U))
    -- where x₀ := T₁(a, U 0).
    refine ⟨fun p : α × (Fin (n + 1) → ℝ) =>
      Fin.cons (T₁ (p.1, p.2 0))
        (T_rest ((p.1, T₁ (p.1, p.2 0)), Fin.tail p.2)), ?_, ?_⟩
    · -- Measurability of T: compose the pair (x₀, T_rest-output) with `e.symm`
      -- (`e.symm (x, v) = Fin.cons x v`, i.e. `Fin.insertNth 0 x v`).
      have h_u₀ : Measurable fun p : α × (Fin (n + 1) → ℝ) => p.2 0 :=
        (measurable_pi_apply 0).comp measurable_snd
      have h_tail : Measurable fun p : α × (Fin (n + 1) → ℝ) => Fin.tail p.2 :=
        measurable_pi_lambda _ fun i =>
          (measurable_pi_apply (Fin.succ i)).comp measurable_snd
      have h_x₀ : Measurable fun p : α × (Fin (n + 1) → ℝ) => T₁ (p.1, p.2 0) :=
        hT₁_meas.comp (measurable_fst.prodMk h_u₀)
      have h_rest : Measurable fun p : α × (Fin (n + 1) → ℝ) =>
          T_rest ((p.1, T₁ (p.1, p.2 0)), Fin.tail p.2) :=
        hT_rest_meas.comp ((measurable_fst.prodMk h_x₀).prodMk h_tail)
      -- `Fin.cons x v = e.symm (x, v)` for our `e = piFinSuccAbove _ 0`.
      have h_pair : Measurable fun p : α × (Fin (n + 1) → ℝ) =>
          (T₁ (p.1, p.2 0),
            T_rest ((p.1, T₁ (p.1, p.2 0)), Fin.tail p.2)) :=
        h_x₀.prodMk h_rest
      convert e.symm.measurable.comp h_pair using 1
      funext p
      simp only [Function.comp, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv_zero, Equiv.coe_fn_mk, Fin.consEquiv]
    · -- Pushforward: (Unif^{n+1}).map T(a, ·) = κ a.
      intro a
      set μ₀ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1) with hμ₀
      set μ_rest : Measure (Fin n → ℝ) :=
        Measure.pi (fun _ : Fin n => volume.restrict (Set.Ioo (0 : ℝ) 1)) with hμ_rest
      -- Named measurability witnesses to avoid `Measurable.comp` / β-reduction issues.
      have h_T₁_sec : Measurable (fun u : ℝ => T₁ (a, u)) :=
        hT₁_meas.comp (measurable_const.prodMk measurable_id)
      have h_T_rest_sec : ∀ y, Measurable (fun U : Fin n → ℝ => T_rest ((a, y), U)) :=
        fun y => hT_rest_meas.comp (measurable_const.prodMk measurable_id)
      -- The sequential map `T_a' : ℝ × (Fin n → ℝ) → ℝ × (Fin n → ℝ)`.
      set T_a' : ℝ × (Fin n → ℝ) → ℝ × (Fin n → ℝ) := fun p =>
        (T₁ (a, p.1), T_rest ((a, T₁ (a, p.1)), p.2)) with hT_a'_def
      have hT_a'_meas : Measurable T_a' :=
        (h_T₁_sec.comp measurable_fst).prodMk
          (hT_rest_meas.comp
            ((measurable_const.prodMk (h_T₁_sec.comp measurable_fst)).prodMk measurable_snd))
      -- Source factorization: `Measure.pi μ₀^{n+1} = (μ₀.prod μ_rest).map e.symm`.
      have h_source : Measure.pi (fun _ : Fin (n + 1) =>
            volume.restrict (Set.Ioo (0 : ℝ) 1)) = (μ₀.prod μ_rest).map e.symm := by
        have hmp := (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => volume.restrict (Set.Ioo (0 : ℝ) 1)) 0).symm
        exact hmp.map_eq.symm
      -- Sequential Fubini: `(μ₀.prod μ_rest).map T_a' = κ' a`.
      have h_fubini : (μ₀.prod μ_rest).map T_a' = κ' a := by
        have h_to_compProd :
            (μ₀.prod μ_rest).map T_a' = (κ₀ a) ⊗ₘ Kernel.sectR κ_rest a := by
          apply Measure.ext
          intro s hs
          rw [Measure.map_apply hT_a'_meas hs, Measure.prod_apply (hT_a'_meas hs),
            Measure.compProd_apply hs]
          -- LHS integrand: `μ_rest (Prod.mk u₀ ⁻¹' (T_a' ⁻¹' s))`.
          -- Rewrite as a pushforward of `T_rest`:
          have h_inner : ∀ u₀,
              μ_rest (Prod.mk u₀ ⁻¹' (T_a' ⁻¹' s))
                = κ_rest (a, T₁ (a, u₀)) (Prod.mk (T₁ (a, u₀)) ⁻¹' s) := by
            intro u₀
            have hrewrite : Prod.mk u₀ ⁻¹' (T_a' ⁻¹' s)
                = (fun U => T_rest ((a, T₁ (a, u₀)), U)) ⁻¹' (Prod.mk (T₁ (a, u₀)) ⁻¹' s) := rfl
            rw [hrewrite,
              ← Measure.map_apply (h_T_rest_sec _) (measurable_prodMk_left hs),
              hT_rest_law (a, T₁ (a, u₀))]
          simp_rw [h_inner, Kernel.sectR_apply]
          -- Change of variables: ∫⁻ u₀, f (T₁(a, u₀)) dμ₀ = ∫⁻ x₀, f x₀ d(κ₀ a).
          rw [← hT₁_law a,
            lintegral_map (Kernel.measurable_kernel_prodMk_left' hs a) h_T₁_sec]
        rw [h_to_compProd]
        rw [← Kernel.compProd_apply_eq_compProd_sectR κ₀ κ_rest a]
        -- Disintegration: κ'.fst ⊗ₖ κ'.condKernel = κ'.
        change (κ'.fst ⊗ₖ κ'.condKernel) a = κ' a
        rw [Kernel.disintegrate]
      -- Align T(a, ·) with `e.symm ∘ T_a' ∘ e`.
      have hT_meas : Measurable (fun U : Fin (n + 1) → ℝ =>
          (Fin.cons (T₁ (a, U 0)) (T_rest ((a, T₁ (a, U 0)), Fin.tail U)) :
            Fin (n + 1) → ℝ)) := by
        have h_u₀ : Measurable fun U : Fin (n + 1) → ℝ => U 0 := measurable_pi_apply 0
        have h_tail : Measurable fun U : Fin (n + 1) → ℝ => Fin.tail U :=
          measurable_pi_lambda _ fun i => measurable_pi_apply (Fin.succ i)
        have h_x₀ : Measurable fun U : Fin (n + 1) → ℝ => T₁ (a, U 0) :=
          h_T₁_sec.comp h_u₀
        have h_rest_val : Measurable fun U : Fin (n + 1) → ℝ =>
            T_rest ((a, T₁ (a, U 0)), Fin.tail U) :=
          hT_rest_meas.comp ((measurable_const.prodMk h_x₀).prodMk h_tail)
        have h_pair : Measurable fun U : Fin (n + 1) → ℝ =>
            (T₁ (a, U 0), T_rest ((a, T₁ (a, U 0)), Fin.tail U)) :=
          h_x₀.prodMk h_rest_val
        convert e.symm.measurable.comp h_pair using 1
        funext U
        simp only [Function.comp, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv_zero, Equiv.coe_fn_mk, Fin.consEquiv]
      have h_T_eq : (fun U : Fin (n + 1) → ℝ =>
            Fin.cons (T₁ (a, U 0)) (T_rest ((a, T₁ (a, U 0)), Fin.tail U))) ∘ e.symm
            = e.symm ∘ T_a' := by
        funext p
        obtain ⟨u₀, U_rest⟩ := p
        simp only [Function.comp, e, T_a', MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv_zero, Equiv.coe_fn_mk, Fin.consEquiv,
          Fin.cons_zero, Fin.tail_cons]
      -- Final chain.  (The Lean-level T is in un-β-reduced form `fun p => … (a, U)`;
      -- `change` normalises to the β-reduced version `fun U => Fin.cons …`.)
      change Measure.map
          (fun U : Fin (n + 1) → ℝ =>
            Fin.cons (T₁ (a, U 0)) (T_rest ((a, T₁ (a, U 0)), Fin.tail U)))
          (Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Set.Ioo (0 : ℝ) 1))) = κ a
      rw [h_source, Measure.map_map hT_meas e.symm.measurable, h_T_eq,
        ← Measure.map_map e.symm.measurable hT_a'_meas, h_fubini]
      -- Goal: (κ' a).map e.symm = κ a.
      change (Kernel.map κ e a).map e.symm = κ a
      rw [Kernel.map_apply _ e.measurable,
        Measure.map_map e.symm.measurable e.measurable,
        show (⇑e.symm ∘ ⇑e : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) = id from
          e.symm_comp_self, Measure.map_id]

/-! ## Step 5 — Uniform splitting (only for vdV-original corollary)

The multi-dimensional realization uses `d` uniforms directly. The splitting
`ℝ ≃ᵐ ℝ × ℝ` supplies `kernel_realization_of_joint_distribution`, the
single-uniform form of vdV Lemma 7.11. It rests on binary-digit independence,
a standalone measure-theoretic construction.

The measure-preservation property is essential: any `ℝ ≃ᵐ ℝ × ℝ` (e.g.
via `PolishSpace.measurableEquivOfNotCountable`) is easy to write, but a
generic one does *not* push `Uniform[0,1]` to the product uniform. The joint
existence is captured by `exists_unifSplit_measurePreserving`, from which
`unifSplit` / `unifSplit_map_uniform` follow.

The substantive ingredient is the binary-digit construction (cf. the
Rademacher functions / Borel-Cantelli identification of `Uniform[0,1]` with
`Bernoulli(1/2)^ℕ` via base-2 expansion). -/

/-! ### Binary-digit splitting infrastructure

The splitting of `Uniform[0,1]` proceeds via its binary digits:

* `binDigit n x` extracts the `(n+1)`-st binary digit of `Int.fract x`.
* `binStream x` packages the digits into a stream `ℕ → Bool`.
* `deinterleave` splits a Cantor-space stream into even/odd substreams.

The substantive fact is that the binary digits of a uniform-on-`(0,1)` random
variable are i.i.d. fair coins (Billingsley §1.3). -/

/-- The `n`-th binary digit of `x : ℝ`, computed from the fractional part:
`⌊2^(n+1) · {x}⌋ mod 2`. -/
noncomputable def binDigit (n : ℕ) (x : ℝ) : Bool :=
  decide (⌊(2 : ℝ) ^ (n + 1) * Int.fract x⌋ % 2 = 1)

lemma measurable_binDigit (n : ℕ) : Measurable (binDigit n) := by
  classical
  -- Since `Bool` is countable, it suffices that the underlying integer-valued
  -- function `⌊2^(n+1) * fract x⌋ % 2` is measurable.
  have h₁ : Measurable fun x : ℝ => ⌊(2 : ℝ) ^ (n + 1) * Int.fract x⌋ :=
    Int.measurable_floor.comp (measurable_const.mul measurable_fract)
  have hcomp : Measurable fun z : ℤ => decide (z % 2 = 1) := measurable_of_countable _
  exact hcomp.comp h₁

/-- The binary-digit stream of a real number. -/
noncomputable def binStream (x : ℝ) : ℕ → Bool := fun n => binDigit n x

lemma measurable_binStream : Measurable binStream :=
  measurable_pi_iff.mpr measurable_binDigit

/-- Pure reindexing equivalence on the Cantor space: split a stream
`(b_n)_n` into its even-indexed and odd-indexed substreams. -/
def deinterleave : (ℕ → Bool) ≃ᵐ (ℕ → Bool) × (ℕ → Bool) where
  toFun b := (fun n => b (2 * n), fun n => b (2 * n + 1))
  invFun p := fun n => if n % 2 = 0 then p.1 (n / 2) else p.2 (n / 2)
  left_inv b := by
    funext n
    rcases Nat.even_or_odd n with h | h
    · obtain ⟨k, rfl⟩ := h
      have hmod : (k + k) % 2 = 0 := by omega
      have hdiv : (k + k) / 2 = k := by omega
      have hkk : 2 * k = k + k := two_mul k
      simp [hmod, hdiv, hkk]
    · obtain ⟨k, rfl⟩ := h
      have hmod : (2 * k + 1) % 2 = 1 := by omega
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simp [hmod, hdiv]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext n
      have hmod : (2 * n) % 2 = 0 := by omega
      have hdiv : (2 * n) / 2 = n := by omega
      simp [hmod, hdiv]
    · funext n
      have hmod : (2 * n + 1) % 2 = 1 := by omega
      have hdiv : (2 * n + 1) / 2 = n := by omega
      simp [hmod, hdiv]
  measurable_toFun := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr fun n => measurable_pi_apply (2 * n)
    · exact measurable_pi_iff.mpr fun n => measurable_pi_apply (2 * n + 1)
  measurable_invFun := by
    refine measurable_pi_iff.mpr fun n => ?_
    change Measurable (fun p : (ℕ → Bool) × (ℕ → Bool) =>
      if n % 2 = 0 then p.1 (n / 2) else p.2 (n / 2))
    by_cases h : n % 2 = 0
    · simp_rw [if_pos h]
      exact (measurable_pi_apply (n / 2)).comp measurable_fst
    · simp_rw [if_neg h]
      exact (measurable_pi_apply (n / 2)).comp measurable_snd

/-! ### Halmos / Lebesgue–Bernoulli isomorphism

The substantive measure-theoretic content needed for §5 is the
**Halmos / Billingsley §1.3** isomorphism: the standard Borel space `ℝ` with
Lebesgue measure restricted to `(0,1)` is measure-isomorphic to the Cantor
space `ℕ → Bool` with the infinite-product fair-coin (Bernoulli(1/2)) measure.

We define `bernoulliHalf`, the fair-coin measure on `Bool`, and
`cantorBernoulli`, the infinite-product of fair-coins on `ℕ → Bool`. The
Halmos isomorphism itself is `exists_realCantorEquiv_lebesgueBernoulli`; the
remaining results follow from it. -/

/-- The fair-coin (Bernoulli(½)) probability measure on `Bool`. -/
noncomputable def bernoulliHalf : Measure Bool :=
  (1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true

instance : IsProbabilityMeasure bernoulliHalf := by
  refine ⟨?_⟩
  classical
  change ((1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true) Set.univ = 1
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    MeasureTheory.measure_univ, mul_one]
  -- Goal: `1/2 + 1/2 = 1`
  exact ENNReal.add_halves 1

/-- The infinite-product fair-coin measure on `ℕ → Bool`. -/
noncomputable def cantorBernoulli : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => bernoulliHalf)

instance : IsProbabilityMeasure cantorBernoulli := by
  unfold cantorBernoulli; infer_instance
/-- Splitting `infinitePi` over a disjoint-union index
`ι ⊕ ι'` via `MeasurableEquiv.sumPiEquivProdPi` lands on the product of the two
infinite-product measures.  The proof goes via `Measure.eq_infinitePi`: it
suffices to check the cylinder formula on `Set.pi s t`, which reduces to a
clean rectangle decomposition `(toLeft × toRight)` of `s`. -/
private lemma infinitePi_sum_map_sumPiEquivProdPi_symm_const
    {ι ι' X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ((Measure.infinitePi (fun _ : ι => μ)).prod
        (Measure.infinitePi (fun _ : ι' => μ))).map
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι' => X)).symm
      = Measure.infinitePi (fun _ : ι ⊕ ι' => μ) := by
  classical
  refine Measure.eq_infinitePi (μ := fun _ : ι ⊕ ι' => μ) ?_
  intro s t ht
  -- Preimage under `sumPiEquivProdPi.symm` of `Set.pi s t` is a rectangle
  -- `(Set.pi s.toLeft (t ∘ inl)) ×ˢ (Set.pi s.toRight (t ∘ inr))`.
  have hpre : (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι' => X)).symm ⁻¹'
      (Set.pi (↑s : Set (ι ⊕ ι')) t) =
        (Set.pi (↑s.toLeft : Set ι) (fun i => t (.inl i))) ×ˢ
        (Set.pi (↑s.toRight : Set ι') (fun i' => t (.inr i'))) := by
    ext ⟨g, h⟩
    constructor
    · intro H
      refine ⟨fun i hi => ?_, fun i' hi' => ?_⟩
      · have : Sum.inl i ∈ s := Finset.mem_toLeft.mp hi
        have hH := H (Sum.inl i) this
        simpa [MeasurableEquiv.coe_sumPiEquivProdPi_symm,
          Equiv.sumPiEquivProdPi_symm_apply] using hH
      · have : Sum.inr i' ∈ s := Finset.mem_toRight.mp hi'
        have hH := H (Sum.inr i') this
        simpa [MeasurableEquiv.coe_sumPiEquivProdPi_symm,
          Equiv.sumPiEquivProdPi_symm_apply] using hH
    · rintro ⟨H₁, H₂⟩ a ha
      cases a with
      | inl i =>
        have hi : i ∈ s.toLeft := Finset.mem_toLeft.mpr ha
        have := H₁ i hi
        simpa [MeasurableEquiv.coe_sumPiEquivProdPi_symm,
          Equiv.sumPiEquivProdPi_symm_apply] using this
      | inr i' =>
        have hi' : i' ∈ s.toRight := Finset.mem_toRight.mpr ha
        have := H₂ i' hi'
        simpa [MeasurableEquiv.coe_sumPiEquivProdPi_symm,
          Equiv.sumPiEquivProdPi_symm_apply] using this
  rw [MeasurableEquiv.map_apply, hpre, Measure.prod_prod,
    Measure.infinitePi_pi (μ := fun _ : ι => μ) (fun i _ => ht (.inl i)),
    Measure.infinitePi_pi (μ := fun _ : ι' => μ) (fun i' _ => ht (.inr i')),
    ← Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight s (fun a => μ (t a))]

/-- `deinterleave` is measure-preserving from `cantorBernoulli` to
`cantorBernoulli ×ₘ cantorBernoulli`.  Standard product-measure
identification: pushing `infinitePi μ` along the even/odd split lands
on `infinitePi μ_even ×ₘ infinitePi μ_odd`, both equal to
`infinitePi μ` since `μ` is constant. -/
lemma deinterleave_map_cantorBernoulli :
    cantorBernoulli.map deinterleave = cantorBernoulli.prod cantorBernoulli := by
  classical
  -- Two Mathlib equivs whose composition equals `deinterleave`.
  -- `e_perm.symm : (ℕ → Bool) ≃ᵐ (ℕ ⊕ ℕ → Bool)` via `Equiv.natSumNatEquivNat`.
  set e_perm : (ℕ ⊕ ℕ → Bool) ≃ᵐ (ℕ → Bool) :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ => Bool) Equiv.natSumNatEquivNat with he_perm_def
  -- `e_split : (ℕ ⊕ ℕ → Bool) ≃ᵐ (ℕ → Bool) × (ℕ → Bool)` via `sumPiEquivProdPi`.
  set e_split : (ℕ ⊕ ℕ → Bool) ≃ᵐ (ℕ → Bool) × (ℕ → Bool) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : ℕ ⊕ ℕ => Bool) with he_split_def
  -- Step 1: `deinterleave = e_split ∘ e_perm.symm` as functions.
  have hdei : (deinterleave : (ℕ → Bool) → (ℕ → Bool) × (ℕ → Bool)) =
      (e_split : (ℕ ⊕ ℕ → Bool) → (ℕ → Bool) × (ℕ → Bool)) ∘
        (e_perm.symm : (ℕ → Bool) → (ℕ ⊕ ℕ → Bool)) := by
    funext b
    -- `e_perm.symm b a = b (natSumNatEquivNat a)` by `piCongrLeft_symm_apply`.
    -- `e_split f = (f ∘ inl, f ∘ inr)`.
    refine Prod.ext ?_ ?_
    · funext n
      -- LHS: `deinterleave b |>.1 n = b (2 * n)` by defn.
      -- RHS via `piCongrLeft_symm_apply`:
      --   `e_split (e_perm.symm b) |>.1 n = e_perm.symm b (.inl n) = b (2 * n)`.
      change b (2 * n) =
        (e_perm.symm b : ℕ ⊕ ℕ → Bool) (Sum.inl n)
      rw [he_perm_def]
      change b (2 * n) =
        (Equiv.piCongrLeft (fun _ : ℕ => Bool) Equiv.natSumNatEquivNat).symm b (Sum.inl n)
      rw [Equiv.piCongrLeft_symm_apply]
      simp [Equiv.natSumNatEquivNat_apply]
    · funext n
      change b (2 * n + 1) =
        (e_perm.symm b : ℕ ⊕ ℕ → Bool) (Sum.inr n)
      rw [he_perm_def]
      change b (2 * n + 1) =
        (Equiv.piCongrLeft (fun _ : ℕ => Bool) Equiv.natSumNatEquivNat).symm b (Sum.inr n)
      rw [Equiv.piCongrLeft_symm_apply]
      simp [Equiv.natSumNatEquivNat_apply]
  rw [hdei, ← Measure.map_map e_split.measurable e_perm.symm.measurable]
  -- Step 2: `cantorBernoulli.map e_perm.symm = infinitePi (fun _ : ℕ ⊕ ℕ => bernoulliHalf)`.
  -- Use `infinitePi_map_piCongrLeft` (forward direction is `e_perm`).
  have hperm : cantorBernoulli.map e_perm.symm =
      Measure.infinitePi (fun _ : ℕ ⊕ ℕ => bernoulliHalf) := by
    have h := Measure.infinitePi_map_piCongrLeft (μ := fun _ : ℕ => bernoulliHalf)
      (Equiv.natSumNatEquivNat)
    -- h : (infinitePi (fun i : ℕ ⊕ ℕ ↦ bernoulliHalf)).map (piCongrLeft _ natSumNatEquivNat) =
    --       infinitePi (fun _ : ℕ => bernoulliHalf) = cantorBernoulli
    -- Convert to: cantorBernoulli.map e_perm.symm = infinitePi (fun _ : ℕ⊕ℕ => bernoulliHalf)
    -- via `map_apply_eq_iff_map_symm_apply_eq`.
    have heq := (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e_perm).mp h
    -- heq : infinitePi (fun _ : ℕ⊕ℕ => bernoulliHalf) = cantorBernoulli.map e_perm.symm
    exact heq.symm
  rw [hperm]
  -- Step 3: apply the helper `infinitePi_sum_map_sumPiEquivProdPi_symm_const`.
  have hsplit := infinitePi_sum_map_sumPiEquivProdPi_symm_const
    (ι := ℕ) (ι' := ℕ) (X := Bool) bernoulliHalf
  -- hsplit : (M.prod M).map e_split.symm = infinitePi (fun _ : ℕ⊕ℕ => bernoulliHalf)
  -- where M = infinitePi (fun _ : ℕ => bernoulliHalf) = cantorBernoulli.
  -- Goal: (infinitePi _).map e_split = cantorBernoulli.prod cantorBernoulli
  have hM : Measure.infinitePi (fun _ : ℕ => bernoulliHalf) = cantorBernoulli := rfl
  rw [show e_split = MeasurableEquiv.sumPiEquivProdPi (fun _ : ℕ ⊕ ℕ => Bool) from rfl]
  rw [← hsplit, ← hM]
  -- Goal: ((M.prod M).map e_split.symm).map e_split = M.prod M
  rw [Measure.map_map e_split.measurable e_split.symm.measurable,
    show ((e_split : (ℕ ⊕ ℕ → Bool) → (ℕ → Bool) × (ℕ → Bool)) ∘
        (e_split.symm : (ℕ → Bool) × (ℕ → Bool) → (ℕ ⊕ ℕ → Bool))) = id from
      e_split.self_comp_symm,
    Measure.map_id]
/-! ## Step 6 — vdV's randomized statistic corollary

Specialising Step 4 to `κ := condDistrib S Δ` yields the kernel form
directly; vdV's strict one-`U` form (a single `Uniform[0,1]` rather than `d`
independent uniforms) needs the splitting (§5) to pre-process `U` into
`(U_1, …, U_d)`. The version below takes `d` uniforms. -/

/-- vdV Lemma 7.11, kernel-form. Given `(S, Δ) : Ω → ℝ^d × ℝ^k` (jointly measurable)
and an independent `U ~ (Uniform[0,1])^d`, there exists a measurable
`T : ℝ^k × (Fin d → ℝ) → ℝ^d` such that the pair `(T(Δ, U), Δ)` has the same law
as `(S, Δ)`. (The strict one-`U` vdV form is recovered by pre-composing with
`unifSplit`.)

**Proof sketch.** Take `κ := condDistrib S Δ P`, a Markov kernel from `ℝ^k` to `ℝ^d`.
Step 4 (`hasUniformRealization`) yields a measurable `T` with
`(Uniform[0,1]^d).map (T(δ, ·)) = κ δ` for every `δ`. Using `IndepFun.comp` to
project the joint independence `(S, Δ) ⫫ U` to `Δ ⫫ U`, the joint law of
`(Δ, U)` factors as `P_Δ × P_U`, so the law of `(T(Δ, U), Δ)` swapped is
`(P_Δ × P_U).map (δ, u) ↦ (δ, T(δ, u))`. Fubini + `hT_law` rewrites this as
`P_Δ ⊗ₘ κ`, which by `compProd_map_condDistrib` equals `P.map (fun ω ↦ (Δ ω, S ω))`.
Swap back to conclude. -/
lemma kernel_realization_of_joint_distribution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d k : ℕ}
    (S : Ω → (Fin d → ℝ)) (hS : Measurable S)
    (Δ : Ω → (Fin k → ℝ)) (hΔ : Measurable Δ)
    (U : Ω → (Fin d → ℝ)) (hU : Measurable U)
    (hU_unif : P.map U = Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hU_indep : IndepFun (fun ω => (S ω, Δ ω)) U P) :
    ∃ T : (Fin k → ℝ) × (Fin d → ℝ) → (Fin d → ℝ),
      Measurable T ∧
      P.map (fun ω => (T (Δ ω, U ω), Δ ω)) = P.map (fun ω => (S ω, Δ ω)) := by
  -- Step 1.  The conditional distribution `κ := condDistrib S Δ P`, a Markov kernel.
  set κ : Kernel (Fin k → ℝ) (Fin d → ℝ) := condDistrib S Δ P with hκ_def
  haveI : IsMarkovKernel κ := by rw [hκ_def]; infer_instance
  -- Step 2.  Step 4 — pull a measurable realization `T` of `κ` from `(Uniform[0,1])^d`.
  obtain ⟨T, hT_meas, hT_law⟩ := hasUniformRealization κ
  refine ⟨T, hT_meas, ?_⟩
  -- Step 3.  Derive `Δ ⫫ U` from `(S, Δ) ⫫ U` by applying the second projection.
  have hΔU_indep : IndepFun Δ U P := by
    have := IndepFun.comp hU_indep (φ := Prod.snd) (ψ := id) measurable_snd measurable_id
    -- `(Prod.snd ∘ fun ω => (S ω, Δ ω)) = Δ`, `id ∘ U = U`.
    simpa using! this
  -- Step 4.  Joint law of `(Δ, U)` factors as `P_Δ × P_U`.
  have hΔU_law : P.map (fun ω => (Δ ω, U ω)) = (P.map Δ).prod (P.map U) :=
    (indepFun_iff_map_prod_eq_prod_map_map hΔ.aemeasurable hU.aemeasurable).mp hΔU_indep
  -- Step 5.  Reduce the target to an equality after composing with `Prod.swap`.
  -- Define the assembly map `g : (δ, u) ↦ (T(δ, u), δ)`.
  set g : (Fin k → ℝ) × (Fin d → ℝ) → (Fin d → ℝ) × (Fin k → ℝ) :=
    fun p => (T (p.1, p.2), p.1) with hg_def
  have hg_meas : Measurable g :=
    (hT_meas.prodMk measurable_fst)
  -- Rewrite LHS as a pushforward through `(Δ, U)`.
  have hLHS_eq : P.map (fun ω => (T (Δ ω, U ω), Δ ω))
      = ((P.map Δ).prod (P.map U)).map g := by
    rw [show (fun ω => (T (Δ ω, U ω), Δ ω))
          = g ∘ (fun ω => (Δ ω, U ω)) from rfl,
        ← Measure.map_map hg_meas (hΔ.prodMk hU), hΔU_law]
  -- Rewrite RHS as a swap of the `compProd` form via `compProd_map_condDistrib`.
  have hSwap_eq : P.map (fun ω => (S ω, Δ ω))
      = (P.map (fun ω => (Δ ω, S ω))).map Prod.swap := by
    rw [Measure.map_map measurable_swap (hΔ.prodMk hS)]
    rfl
  have hcompProd : (P.map Δ) ⊗ₘ κ = P.map (fun ω => (Δ ω, S ω)) := by
    simpa [hκ_def] using compProd_map_condDistrib (X := Δ) (Y := S) hS.aemeasurable
  rw [hLHS_eq, hSwap_eq, ← hcompProd]
  -- Step 6.  Show `((P.map Δ).prod (P.map U)).map g = ((P.map Δ) ⊗ₘ κ).map Prod.swap`.
  -- Both sides are probability measures; check equality on rectangles via `Measure.ext_prod`.
  haveI : IsProbabilityMeasure (P.map Δ) := Measure.isProbabilityMeasure_map hΔ.aemeasurable
  haveI : IsProbabilityMeasure (P.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  haveI : IsProbabilityMeasure ((P.map Δ).prod (P.map U)) := inferInstance
  haveI : IsProbabilityMeasure (((P.map Δ).prod (P.map U)).map g) :=
    Measure.isProbabilityMeasure_map hg_meas.aemeasurable
  refine Measure.ext_prod (μ := ((P.map Δ).prod (P.map U)).map g)
    (ν := ((P.map Δ) ⊗ₘ κ).map Prod.swap) ?_
  intro A B hA hB
  -- RHS(A × B):
  --   ((P.map Δ) ⊗ₘ κ).map Prod.swap (A × B)
  --   = ((P.map Δ) ⊗ₘ κ) (Prod.swap ⁻¹' (A × B))
  --   = ((P.map Δ) ⊗ₘ κ) (B × A)
  --   = ∫⁻ δ in B, κ δ A ∂(P.map Δ)
  -- LHS(A × B):
  --   ((P.map Δ).prod (P.map U)).map g (A × B)
  --   = ((P.map Δ).prod (P.map U)) (g ⁻¹' (A × B))
  --   = ((P.map Δ).prod (P.map U)) {(δ, u) | T(δ, u) ∈ A ∧ δ ∈ B}
  --   = ∫⁻ δ in B, (P.map U) {u | T(δ, u) ∈ A} ∂(P.map Δ)
  --   = ∫⁻ δ in B, ((P.map U).map (T (δ, ·))) A ∂(P.map Δ)
  --   = ∫⁻ δ in B, κ δ A ∂(P.map Δ)   (by hT_law, since P.map U = Unif^d)
  have hRHS_swap :
      ((P.map Δ) ⊗ₘ κ).map Prod.swap (A ×ˢ B)
        = ∫⁻ δ in B, κ δ A ∂(P.map Δ) := by
    rw [Measure.map_apply measurable_swap (hA.prod hB),
        Set.preimage_swap_prod, Measure.compProd_apply_prod hB hA]
  have hT_sec_meas : ∀ δ : Fin k → ℝ, Measurable (fun u => T (δ, u)) :=
    fun δ => hT_meas.comp (measurable_const.prodMk measurable_id)
  have hg_measSet : MeasurableSet (g ⁻¹' (A ×ˢ B)) :=
    hg_meas (hA.prod hB)
  have hLHS_compute :
      ((P.map Δ).prod (P.map U)).map g (A ×ˢ B)
        = ∫⁻ δ in B, (P.map U) {u | T (δ, u) ∈ A} ∂(P.map Δ) := by
    rw [Measure.map_apply hg_meas (hA.prod hB)]
    have h_eq : ((P.map Δ).prod (P.map U)) (g ⁻¹' (A ×ˢ B))
        = ∫⁻ δ, (P.map U) (Prod.mk δ ⁻¹' (g ⁻¹' (A ×ˢ B))) ∂(P.map Δ) := by
      rw [Measure.prod_apply hg_measSet]
    rw [h_eq, ← lintegral_indicator hB]
    congr 1
    funext δ
    by_cases hδ : δ ∈ B
    · simp only [hδ, Set.indicator_of_mem]
      congr 1
      ext u
      simp [hg_def, hδ]
    · simp only [hδ, Set.indicator_of_notMem, not_false_eq_true]
      have hpre : Prod.mk δ ⁻¹' (g ⁻¹' (A ×ˢ B)) = ∅ := by
        ext u
        simp [hg_def, hδ]
      rw [hpre]; simp
  rw [hLHS_compute, hRHS_swap]
  -- Final step: identify (P.map U).map (T(δ, ·)) A with κ δ A, using hT_law and hU_unif.
  refine setLIntegral_congr_fun hB ?_
  intro δ _hδ
  change (P.map U) {u | T (δ, u) ∈ A} = (κ δ) A
  have h_pushforward : (P.map U) {u | T (δ, u) ∈ A}
      = ((P.map U).map (fun u => T (δ, u))) A := by
    rw [Measure.map_apply (hT_sec_meas δ) hA]; rfl
  rw [h_pushforward, hU_unif, hT_law δ]

end KernelRealization
end AsymptoticStatistics
