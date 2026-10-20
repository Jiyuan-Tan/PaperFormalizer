module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import StatLean.AsymptoticStatistics.Core.MassMethod
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# Multi-dim parametric submodel from a family of bounded mean-zero scores

Given `g_P : Fin m → ↥(L2ZeroMean P)` with each `g_P i` essentially
bounded (an `IsBoundedMixtureScore`), this file produces a
`ParametricFamily Ω (EuclideanSpace ℝ (Fin m))` whose density is the
truncated linear perturbation `1 + ⟨θ, g_P ·⟩` for `‖θ‖` small (and `1`
otherwise). The construction adapts `Core/MassMethod.boundedDensityPath`
from 1-D to multi-dim: the sole subtlety is that the truncation
threshold `δ` shrinks with the dimension (by a factor `m`) to keep
`|⟨θ, g_P ω⟩| < 1`.

Construction note: `ParametricFamily.density_meas` requires a *plain*
`Measurable` density, but `Lp ℝ 2 P`'s coercion is only
`AEStronglyMeasurable`. The density is therefore defined using the
strongly-measurable representatives `(Lp.aestronglyMeasurable (g_P i)).mk`
rather than the bare coercions; the two agree `P`-a.e., and all integral
identities (mean-zero, normalisation) carry over via `integral_congr_ae`.

Reference: van der Vaart §25.5 (parametric submodels through scores).
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal BigOperators

namespace AsymptoticStatistics.ParametricFamily

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.MassMethod

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Multi-dim bounded mixture scores -/

/-- A family `g_P : Fin m → ↥(L2ZeroMean P)` is a **bounded mixture-score
family** when each component is *essentially bounded* in `L²₀(P)`
(see `IsEssBoundedMixtureScore`).

Only essential boundedness is demanded (no `g_P i ≥ -1` a.e. clause):
non-negativity of the truncated density is enforced by `max 0` plus
`‖θ‖ < truncRadius ⇒ |linPerturb| < 1` strictly (see
`linPerturb_truncated_nonneg`). This relaxation lets
`IsBoundedMixtureScores` be preserved under Gram-Schmidt and linear
combinations. -/
def IsBoundedMixtureScores
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)) : Prop :=
  ∀ i : Fin m, IsEssBoundedMixtureScore (g_P i)

namespace IsBoundedMixtureScores

variable {m : ℕ} {g_P : Fin m → ↥(L2ZeroMean P)}

/-- A uniform a.e. bound for all components, measurable choice given by
maxing the per-component witnesses with `0`. The resulting `M` is `≥ 0`
by construction (when `m > 0`). -/
noncomputable def uniformBound (hg : IsBoundedMixtureScores g_P) : ℝ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then
    Finset.univ.sup' h (fun i : Fin m => max 0 (Classical.choose (hg i)))
  else 0

lemma uniformBound_nonneg (hg : IsBoundedMixtureScores g_P) :
    0 ≤ hg.uniformBound := by
  classical
  unfold uniformBound
  by_cases h : (Finset.univ : Finset (Fin m)).Nonempty
  · rw [dif_pos h]
    obtain ⟨i, hi_mem⟩ := h
    -- max 0 (Classical.choose (hg i)) ≤ sup' …
    have hi : (fun j : Fin m => max 0 (Classical.choose (hg j))) i ≤
        Finset.univ.sup' ⟨i, hi_mem⟩
          (fun j : Fin m => max 0 (Classical.choose (hg j))) :=
      Finset.le_sup' (f := fun j : Fin m => max 0 (Classical.choose (hg j)))
        hi_mem
    -- The sup' on RHS uses ⟨i, hi_mem⟩, but our goal uses the original h : Nonempty.
    -- These are equal by Subsingleton on Finset.Nonempty instance / dependent type
    -- (data of Nonempty doesn't matter for sup'). Convert via change.
    change 0 ≤ Finset.univ.sup' (⟨i, hi_mem⟩ : (Finset.univ : Finset (Fin m)).Nonempty)
        (fun j : Fin m => max 0 (Classical.choose (hg j)))
    exact (le_max_left _ _).trans hi
  · rw [dif_neg h]

/-- Each component is a.e. bounded by the uniform bound. -/
lemma ae_abs_le_uniformBound (hg : IsBoundedMixtureScores g_P) (i : Fin m) :
    ∀ᵐ ω ∂P, |((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ hg.uniformBound := by
  classical
  have hChoose : ∀ᵐ ω ∂P,
      |((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ Classical.choose (hg i) :=
    Classical.choose_spec (hg i)
  filter_upwards [hChoose] with ω hω
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i, Finset.mem_univ i⟩
  have h1 : Classical.choose (hg i) ≤
      max 0 (Classical.choose (hg i)) := le_max_right _ _
  have h2 : (fun j : Fin m => max 0 (Classical.choose (hg j))) i ≤
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩
        (fun j : Fin m => max 0 (Classical.choose (hg j))) :=
    Finset.le_sup' (f := fun j : Fin m => max 0 (Classical.choose (hg j)))
      (Finset.mem_univ i)
  -- Identify `hg.uniformBound` with the nonempty `dif_pos` branch.
  have h3 : hg.uniformBound =
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩
        (fun j : Fin m => max 0 (Classical.choose (hg j))) := by
    unfold uniformBound; rw [dif_pos hne]
  rw [h3]
  exact hω.trans (h1.trans h2)

end IsBoundedMixtureScores

/-! ## Strongly-measurable representatives of `g_P i`

`Lp ℝ 2 P` coercions are `AEStronglyMeasurable` but not `Measurable` in
general. To obtain `ParametricFamily.density_meas` (which requires
plain `Measurable`), use the canonical strongly-measurable
representatives `gMk i := (Lp.aestronglyMeasurable (g_P i)).mk _`. They
agree with the bare coercions `P`-a.e. -/

section ScoreRepresentatives

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))

/-- Strongly-measurable representative of `(g_P i : Lp ℝ 2 P) : Ω → ℝ`. -/
noncomputable def gMk (i : Fin m) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (g_P i : Lp ℝ 2 P)).mk _

lemma gMk_meas (i : Fin m) : Measurable (gMk g_P i) :=
  (Lp.aestronglyMeasurable (g_P i : Lp ℝ 2 P)).stronglyMeasurable_mk.measurable

lemma gMk_ae_eq (i : Fin m) :
    gMk g_P i =ᵐ[P] ((g_P i : Lp ℝ 2 P) : Ω → ℝ) :=
  (Lp.aestronglyMeasurable (g_P i : Lp ℝ 2 P)).ae_eq_mk.symm

lemma ae_abs_gMk_le {hg : IsBoundedMixtureScores g_P} (i : Fin m) :
    ∀ᵐ ω ∂P, |gMk g_P i ω| ≤ hg.uniformBound := by
  filter_upwards [hg.ae_abs_le_uniformBound i, gMk_ae_eq g_P i] with ω hω hae
  rw [hae]; exact hω

end ScoreRepresentatives

/-! ## Pointwise sum of scores against a parameter -/

section LinearPerturbation

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))

/-- The pointwise linear perturbation `ω ↦ Σᵢ θ i · gMk i ω`, using the
strongly-measurable representatives `gMk` of the `g_P i`. -/
noncomputable def linPerturb
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  ∑ i, θ i * gMk g_P i ω

lemma linPerturb_meas (θ : EuclideanSpace ℝ (Fin m)) :
    Measurable (linPerturb g_P θ) := by
  classical
  unfold linPerturb
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (measurable_const).mul (gMk_meas g_P i)

lemma linPerturb_integrable (θ : EuclideanSpace ℝ (Fin m)) :
    Integrable (linPerturb g_P θ) P := by
  classical
  unfold linPerturb
  refine integrable_finset_sum _ (fun i _ => ?_)
  -- Integrability via a.e.-equality with `(g_P i : Ω → ℝ)`, which is
  -- integrable from `Lp.memLp.integrable`.
  have hg_int : Integrable (((g_P i : Lp ℝ 2 P) : Ω → ℝ)) P :=
    (Lp.memLp (g_P i : Lp ℝ 2 P)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hae : gMk g_P i =ᵐ[P] ((g_P i : Lp ℝ 2 P) : Ω → ℝ) := gMk_ae_eq g_P i
  have hg_int_mk : Integrable (gMk g_P i) P := hg_int.congr hae.symm
  exact hg_int_mk.const_mul (θ i)

/-- Each `gMk i` integrates to 0, since `g_P i ∈ L2ZeroMean P` and
`gMk i =ᵐ[P] (g_P i : Ω → ℝ)`. -/
lemma integral_gMk_eq_zero (i : Fin m) :
    ∫ ω, gMk g_P i ω ∂P = 0 := by
  -- Step 1: ∫ (g_P i : Ω → ℝ) ∂P = 0 (g_P i ∈ ker integralL2).
  have h_mem : (g_P i : Lp ℝ 2 P) ∈ L2ZeroMean P := (g_P i).2
  change (g_P i : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at h_mem
  rw [LinearMap.mem_ker] at h_mem
  have h_inner : ⟪oneL2 P, (g_P i : Lp ℝ 2 P)⟫_ℝ = 0 := h_mem
  rw [MeasureTheory.L2.inner_def] at h_inner
  have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  have h_int_eq :
      ∫ a, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
              ((g_P i : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ ∂P
        = ∫ a, ((g_P i : Lp ℝ 2 P) : Ω → ℝ) a ∂P := by
    apply integral_congr_ae
    filter_upwards [h_one_ae] with a ha
    have hcomm :
        ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
          ((g_P i : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
          = ((g_P i : Lp ℝ 2 P) : Ω → ℝ) a
              * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
    rw [hcomm, ha, mul_one]
  rw [h_int_eq] at h_inner
  -- Step 2: bridge to gMk via a.e.-equality.
  have h_gmk_int : ∫ ω, gMk g_P i ω ∂P
      = ∫ ω, ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω ∂P :=
    integral_congr_ae (gMk_ae_eq g_P i)
  rw [h_gmk_int]; exact h_inner

lemma integral_linPerturb_eq_zero (θ : EuclideanSpace ℝ (Fin m)) :
    ∫ ω, linPerturb g_P θ ω ∂P = 0 := by
  classical
  unfold linPerturb
  rw [integral_finset_sum]
  · simp [integral_const_mul, integral_gMk_eq_zero g_P]
  · intro i _
    have hg_int : Integrable (((g_P i : Lp ℝ 2 P) : Ω → ℝ)) P :=
      (Lp.memLp (g_P i : Lp ℝ 2 P)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hae : gMk g_P i =ᵐ[P] ((g_P i : Lp ℝ 2 P) : Ω → ℝ) := gMk_ae_eq g_P i
    exact (hg_int.congr hae.symm).const_mul (θ i)

end LinearPerturbation

/-! ## The truncation radius -/

section Submodel

variable {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
variable (hg : IsBoundedMixtureScores g_P)

/-- The truncation threshold for the parametric submodel: when
`‖θ‖ < truncRadius`, the linear perturbation `Σᵢ θ i · g_P i ω` has
absolute value `< 1`, so the density `1 + ⟨θ, g_P⟩` is non-negative.

Concretely: `truncRadius := 1 / (M·m + 1)` where `M = uniformBound hg`
and `m = Fintype.card (Fin m)`. The constant `+1` keeps the radius
positive even when `M = 0` or `m = 0`. -/
noncomputable def truncRadius : ℝ :=
  1 / (hg.uniformBound * m + 1)

lemma truncRadius_pos : 0 < truncRadius g_P hg := by
  classical
  have hM : 0 ≤ hg.uniformBound := hg.uniformBound_nonneg
  have hm : (0 : ℝ) ≤ m := by positivity
  unfold truncRadius
  apply div_pos one_pos
  have : 0 ≤ hg.uniformBound * m := mul_nonneg hM hm
  linarith

/-- Pointwise bound: `|Σᵢ θ i · gMk i ω| ≤ ‖θ‖ · m · M` a.e. (under `P`),
where `M = hg.uniformBound`. The proof uses `|θ i| ≤ ‖θ‖` (from
`PiLp.norm_apply_le`). -/
lemma abs_linPerturb_le
    (θ : EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ ω ∂P,
      |linPerturb g_P θ ω| ≤ ‖θ‖ * m * hg.uniformBound := by
  classical
  have h_each : ∀ i : Fin m, ∀ᵐ ω ∂P,
      |gMk g_P i ω| ≤ hg.uniformBound :=
    fun i => ae_abs_gMk_le (hg := hg) g_P i
  have h_all : ∀ᵐ ω ∂P, ∀ i : Fin m,
      |gMk g_P i ω| ≤ hg.uniformBound :=
    ae_all_iff.mpr h_each
  filter_upwards [h_all] with ω hω
  -- Bound: |Σᵢ θ i · gMk i ω| ≤ Σᵢ |θ i| · |gMk i ω| ≤ Σᵢ ‖θ‖·M = m·‖θ‖·M.
  have h1 : |∑ i, θ i * gMk g_P i ω| ≤
      ∑ i, |θ i * gMk g_P i ω| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      |θ i * gMk g_P i ω| ≤ ‖θ‖ * hg.uniformBound := by
    intro i _
    rw [abs_mul]
    have hθi : |θ i| ≤ ‖θ‖ := by
      have := PiLp.norm_apply_le (β := fun _ : Fin m => ℝ) (p := 2) θ i
      simpa using this
    have hgi := hω i
    have hgi_nn : 0 ≤ |gMk g_P i ω| := abs_nonneg _
    calc |θ i| * |gMk g_P i ω|
        ≤ ‖θ‖ * |gMk g_P i ω| :=
          mul_le_mul_of_nonneg_right hθi hgi_nn
      _ ≤ ‖θ‖ * hg.uniformBound := by
          have hθ_nn : 0 ≤ ‖θ‖ := norm_nonneg _
          exact mul_le_mul_of_nonneg_left hgi hθ_nn
  have h3 : (∑ i, |θ i * gMk g_P i ω|) ≤
      ∑ _i : Fin m, ‖θ‖ * hg.uniformBound :=
    Finset.sum_le_sum h2
  have h4 : (∑ _i : Fin m, ‖θ‖ * hg.uniformBound)
      = m * (‖θ‖ * hg.uniformBound) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h5 : |∑ i, θ i * gMk g_P i ω| ≤
      m * (‖θ‖ * hg.uniformBound) := by
    calc |∑ i, θ i * gMk g_P i ω|
        ≤ ∑ i, |θ i * gMk g_P i ω| := h1
      _ ≤ ∑ _i : Fin m, ‖θ‖ * hg.uniformBound := h3
      _ = m * (‖θ‖ * hg.uniformBound) := h4
  have h6 : (m : ℝ) * (‖θ‖ * hg.uniformBound) = ‖θ‖ * m * hg.uniformBound := by
    ring
  change |∑ i, θ i * gMk g_P i ω| ≤ ‖θ‖ * m * hg.uniformBound
  rw [← h6]
  exact h5

/-- For `‖θ‖ < truncRadius`, the linear perturbation is a.e. `> -1`,
hence the density `1 + ⟨θ, g_P ω⟩` is a.e. non-negative. -/
lemma linPerturb_truncated_nonneg
    (θ : EuclideanSpace ℝ (Fin m)) (hθ : ‖θ‖ < truncRadius g_P hg) :
    ∀ᵐ ω ∂P, 0 ≤ 1 + linPerturb g_P θ ω := by
  classical
  by_cases hm0 : m = 0
  · -- m = 0: linPerturb is the empty sum, identically 0.
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hempty : (linPerturb g_P θ ω) = 0 := by
      unfold linPerturb
      subst hm0
      simp
    rw [hempty]; norm_num
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have hM_nn : 0 ≤ hg.uniformBound := hg.uniformBound_nonneg
    have h_bound := abs_linPerturb_le g_P hg θ
    filter_upwards [h_bound] with ω hω
    -- |linPerturb θ ω| ≤ ‖θ‖ * m * M.
    -- Want: ‖θ‖ * m * M < 1.
    have hθ_nn : 0 ≤ ‖θ‖ := norm_nonneg _
    have hm_nn : (0 : ℝ) ≤ m := by positivity
    have h_target : ‖θ‖ * m * hg.uniformBound < 1 := by
      have htm_nn : 0 ≤ hg.uniformBound * m := mul_nonneg hM_nn hm_nn
      have hpos : (0 : ℝ) < hg.uniformBound * m + 1 := by linarith
      have hθlt : ‖θ‖ < 1 / (hg.uniformBound * m + 1) := hθ
      -- Step 1: ‖θ‖ * m * M ≤ truncRadius * m * M.
      have h_step1 : ‖θ‖ * m * hg.uniformBound ≤
          (1 / (hg.uniformBound * m + 1)) * m * hg.uniformBound := by
        have hmM_nn : 0 ≤ (m : ℝ) * hg.uniformBound := mul_nonneg hm_nn hM_nn
        have hθle : ‖θ‖ ≤ 1 / (hg.uniformBound * m + 1) := le_of_lt hθlt
        nlinarith [hθle, hθ_nn, hmM_nn,
          mul_nonneg hm_nn hM_nn, (one_div_pos.mpr hpos).le]
      -- Step 2: simplify (1/(M·m+1))·m·M = (M·m)/(M·m+1).
      have h_simp : (1 / (hg.uniformBound * m + 1)) * m * hg.uniformBound
          = (hg.uniformBound * m) / (hg.uniformBound * m + 1) := by
        field_simp
      rw [h_simp] at h_step1
      have h_lt_one : (hg.uniformBound * m) / (hg.uniformBound * m + 1) < 1 := by
        rw [div_lt_one hpos]; linarith
      exact lt_of_le_of_lt h_step1 h_lt_one
    have hbound : |linPerturb g_P θ ω| < 1 := lt_of_le_of_lt hω h_target
    have hgt : -1 < linPerturb g_P θ ω := (abs_lt.mp hbound).1
    linarith

/-! ## Density definition -/

/-- Density definition: truncated linear perturbation. For `‖θ‖ <
truncRadius`, the density is `1 + Σᵢ θ i · gMk i ω`; otherwise the
density falls back to `1` (so the family stays well-defined globally).

The fallback at `‖θ‖ ≥ truncRadius` extends the local family globally without
changing it near `0`. The truncation `truncRadius = 1 / (M·m + 1)` keeps the
density pointwise non-negative. -/
noncomputable def submodelDensity
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  if ‖θ‖ < truncRadius g_P hg then 1 + linPerturb g_P θ ω else 1

lemma submodelDensity_meas
    (θ : EuclideanSpace ℝ (Fin m)) :
    Measurable (submodelDensity g_P hg θ) := by
  classical
  by_cases hθ : ‖θ‖ < truncRadius g_P hg
  · -- Show the function equals `fun ω => 1 + linPerturb g_P θ ω`.
    have h_eq : submodelDensity g_P hg θ = fun ω => 1 + linPerturb g_P θ ω := by
      funext ω; unfold submodelDensity; rw [if_pos hθ]
    rw [h_eq]
    exact (measurable_const).add (linPerturb_meas g_P θ)
  · have h_eq : submodelDensity g_P hg θ = fun _ => (1 : ℝ) := by
      funext ω; unfold submodelDensity; rw [if_neg hθ]
    rw [h_eq]
    exact measurable_const

/-- Pointwise-everywhere non-negative density: take the max with `0`. This is
a.e.-equal to `submodelDensity` (since `submodelDensity ≥ 0` a.e. for
`‖θ‖ < truncRadius`, and `= 1` otherwise) and is the density used by
`paramSubmodel`. -/
noncomputable def submodelDensityNN
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  max 0 (submodelDensity g_P hg θ ω)

lemma submodelDensityNN_meas
    (θ : EuclideanSpace ℝ (Fin m)) :
    Measurable (submodelDensityNN g_P hg θ) :=
  measurable_const.max (submodelDensity_meas g_P hg θ)

lemma submodelDensityNN_nonneg
    (θ : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    0 ≤ submodelDensityNN g_P hg θ ω :=
  le_max_left _ _

/-- a.e.-equality between `submodelDensityNN` and `submodelDensity`. The
two differ only on the (null) set where `1 + linPerturb < 0`, which has
`P`-measure zero by `linPerturb_truncated_nonneg`. -/
lemma submodelDensityNN_ae_eq
    (θ : EuclideanSpace ℝ (Fin m)) :
    submodelDensityNN g_P hg θ =ᵐ[P] submodelDensity g_P hg θ := by
  classical
  by_cases hθ : ‖θ‖ < truncRadius g_P hg
  · -- For ‖θ‖ < δ: submodelDensity = 1 + linPerturb, which is ≥ 0 a.e.
    have h_nn := linPerturb_truncated_nonneg g_P hg θ hθ
    filter_upwards [h_nn] with ω hω
    change max 0 (submodelDensity g_P hg θ ω) = submodelDensity g_P hg θ ω
    have h_eq : submodelDensity g_P hg θ ω = 1 + linPerturb g_P θ ω := by
      unfold submodelDensity; rw [if_pos hθ]
    rw [h_eq]; exact max_eq_right hω
  · -- For ‖θ‖ ≥ δ: submodelDensity = 1 ≥ 0 pointwise.
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change max 0 (submodelDensity g_P hg θ ω) = submodelDensity g_P hg θ ω
    have h_eq : submodelDensity g_P hg θ ω = 1 := by
      unfold submodelDensity; rw [if_neg hθ]
    rw [h_eq]; norm_num

/-- ∫ submodelDensity θ ∂P = 1 a.e. for `‖θ‖ < truncRadius`. Mean-zero of
`linPerturb` reduces the integral to `∫ 1 ∂P = 1`. -/
lemma integral_submodelDensity_eq_one
    (θ : EuclideanSpace ℝ (Fin m)) :
    ∫ ω, submodelDensity g_P hg θ ω ∂P = 1 := by
  classical
  by_cases hθ : ‖θ‖ < truncRadius g_P hg
  · have h_eq : ∀ ω, submodelDensity g_P hg θ ω = 1 + linPerturb g_P θ ω := by
      intro ω; unfold submodelDensity; rw [if_pos hθ]
    simp_rw [h_eq]
    rw [integral_add (integrable_const _) (linPerturb_integrable g_P θ)]
    rw [integral_const, integral_linPerturb_eq_zero g_P θ]
    simp
  · have h_eq : ∀ ω, submodelDensity g_P hg θ ω = 1 := by
      intro ω; unfold submodelDensity; rw [if_neg hθ]
    simp_rw [h_eq]
    simp

lemma submodelDensity_integrable
    (θ : EuclideanSpace ℝ (Fin m)) :
    Integrable (submodelDensity g_P hg θ) P := by
  classical
  by_cases hθ : ‖θ‖ < truncRadius g_P hg
  · have h_eq : submodelDensity g_P hg θ = fun ω => 1 + linPerturb g_P θ ω := by
      funext ω; unfold submodelDensity; rw [if_pos hθ]
    rw [h_eq]
    exact (integrable_const _).add (linPerturb_integrable g_P θ)
  · have h_eq : submodelDensity g_P hg θ = fun _ => (1 : ℝ) := by
      funext ω; unfold submodelDensity; rw [if_neg hθ]
    rw [h_eq]
    exact integrable_const _

/-- `∫ submodelDensityNN θ ∂P = 1`. -/
lemma integral_submodelDensityNN_eq_one
    (θ : EuclideanSpace ℝ (Fin m)) :
    ∫ ω, submodelDensityNN g_P hg θ ω ∂P = 1 := by
  rw [integral_congr_ae (submodelDensityNN_ae_eq g_P hg θ)]
  exact integral_submodelDensity_eq_one g_P hg θ

lemma submodelDensityNN_integrable
    (θ : EuclideanSpace ℝ (Fin m)) :
    Integrable (submodelDensityNN g_P hg θ) P := by
  refine Integrable.congr (submodelDensity_integrable g_P hg θ)
    (submodelDensityNN_ae_eq g_P hg θ).symm

end Submodel

/-! ## The parametric submodel -/

/-- Multi-dim parametric submodel from a bounded orthonormal score family.

The density at parameter `θ` is `1 + Σᵢ θ i · g_P i` (truncated to keep
non-negativity for small `‖θ‖`, falling back to `1` outside the
truncation radius and additionally clipped pointwise via `max 0`).

The orthonormality hypothesis is not needed to define the density; it records
the score normalization used later to identify the Fisher information with
`I_m`. -/
noncomputable def paramSubmodel
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (_h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    ParametricFamily Ω (EuclideanSpace ℝ (Fin m)) where
  density := submodelDensityNN g_P hg
  density_meas := submodelDensityNN_meas g_P hg
  density_nonneg := submodelDensityNN_nonneg g_P hg

/-- The parametric submodel is a probability-density family with respect
to `P`. -/
theorem paramSubmodel_isPDFOf
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    IsPDFOf (paramSubmodel g_P hg h_orth) P where
  density_integral_eq_one := integral_submodelDensityNN_eq_one g_P hg
  density_integrable := submodelDensityNN_integrable g_P hg

/-! ## Density properties -/

/-- Density at `θ = 0` is identically `1` (everywhere). -/
theorem paramSubmodel_density_at_zero
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ω : Ω) :
    (paramSubmodel g_P hg h_orth).density 0 ω = 1 := by
  classical
  -- With θ = 0: ‖0‖ = 0 < truncRadius (positive), and linPerturb = 0.
  have h_pos : 0 < truncRadius g_P hg := truncRadius_pos g_P hg
  have h0 : ‖(0 : EuclideanSpace ℝ (Fin m))‖ < truncRadius g_P hg := by
    rw [norm_zero]; exact h_pos
  -- submodelDensity at θ=0: 1 + linPerturb, with linPerturb = 0.
  have h_lin0 : linPerturb g_P (0 : EuclideanSpace ℝ (Fin m)) ω = 0 := by
    unfold linPerturb
    simp [zero_mul]
  have h_sd : submodelDensity g_P hg (0 : EuclideanSpace ℝ (Fin m)) ω = 1 := by
    unfold submodelDensity
    rw [if_pos h0, h_lin0]; norm_num
  change submodelDensityNN g_P hg (0 : EuclideanSpace ℝ (Fin m)) ω = 1
  unfold submodelDensityNN
  rw [h_sd]; norm_num

/-- The "score" of the submodel at `θ = 0`: the linear-in-`θ` term of
the density expansion is exactly `Σᵢ θ i · gMk i ω = linPerturb θ ω`.

Used when proving DQM and Fisher information. -/
theorem paramSubmodel_score_at_zero
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (θ : EuclideanSpace ℝ (Fin m)) (hθ : ‖θ‖ < truncRadius g_P hg) :
    ∀ᵐ ω ∂P, (paramSubmodel g_P hg h_orth).density θ ω
      = 1 + linPerturb g_P θ ω := by
  classical
  -- For ‖θ‖ < δ, submodelDensity = 1 + linPerturb; submodelDensityNN agrees a.e.
  have h_eq_sd : submodelDensityNN g_P hg θ =ᵐ[P] submodelDensity g_P hg θ :=
    submodelDensityNN_ae_eq g_P hg θ
  filter_upwards [h_eq_sd] with ω hω
  change submodelDensityNN g_P hg θ ω = 1 + linPerturb g_P θ ω
  rw [hω]
  unfold submodelDensity
  rw [if_pos hθ]

/-- **Joint measurability of the parametric-submodel density.**

The density `(paramSubmodel g_P hg h_orth).density θ ω` unfolds as

```
density θ ω = max 0 (if ‖θ‖ < truncRadius then 1 + linPerturb θ ω else 1)
```

so joint measurability in `(θ, ω)` follows from:

* `Measurable.ite` on the open condition `‖θ‖ < truncRadius` (open in `θ`),
* `Finset.measurable_sum` over `linPerturb = ∑ i, θ_i · gMk_i`,
* the joint measurability of each coordinate factor (`measurable_pi_apply`
  composed with `WithLp.measurable_ofLp` to bridge `EuclideanSpace ℝ (Fin m)
  = WithLp 2 (Fin m → ℝ)`).

This gives joint measurability of the submodel density in its parameter and
sample arguments. -/
theorem paramSubmodel_density_joint_meas
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    Measurable
      (Function.uncurry (paramSubmodel g_P hg h_orth).density) := by
  change Measurable (fun p : EuclideanSpace ℝ (Fin m) × Ω =>
    (paramSubmodel g_P hg h_orth).density p.1 p.2)
  unfold paramSubmodel
  change Measurable (fun p : EuclideanSpace ℝ (Fin m) × Ω =>
    submodelDensityNN g_P hg p.1 p.2)
  unfold submodelDensityNN
  refine Measurable.max measurable_const ?_
  unfold submodelDensity
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt (measurable_norm.comp measurable_fst) measurable_const
  · refine measurable_const.add ?_
    unfold linPerturb
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.mul ?_ ?_
    · have h1 : Measurable (WithLp.ofLp ∘ (Prod.fst :
          EuclideanSpace ℝ (Fin m) × Ω → EuclideanSpace ℝ (Fin m))) :=
        (WithLp.measurable_ofLp 2 (Fin m → ℝ)).comp measurable_fst
      exact (measurable_pi_apply i).comp h1
    · exact (gMk_meas g_P i).comp measurable_snd

end AsymptoticStatistics.ParametricFamily
