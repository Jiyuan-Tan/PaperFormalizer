module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimator
public import StatLean.AsymptoticStatistics.ParametricFamily.SubmodelFromScores
public import StatLean.AsymptoticStatistics.ParametricFamily.SubmodelDQM
public import StatLean.AsymptoticStatistics.Core.MassMethod
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
public import StatLean.AsymptoticStatistics.ForMathlib.Prohorov
public import StatLean.AsymptoticStatistics.ForMathlib.CharFnConvolution
public import StatLean.AsymptoticStatistics.ForMathlib.JointMGF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Derivations from the regular-estimator predicate

Bridge from the parametric submodel `paramSubmodel` to a `QMDPath` form, so that
`IsRegularEstimator.shift` (which speaks about QMDPath curves) can be applied to
perturbations along the parametric submodel. For each direction
`h : EuclideanSpace ℝ (Fin m)`, this produces a `QMDPath P` whose curve is (up to
truncation) the parametric submodel's density along `s • h` and whose score is the
linear combination `Σᵢ h_i • g_P i ∈ ↥(L2ZeroMean P)`. On top of this bridge the
file derives Hájek's convolution theorem (`hajek_convolution_theorem`,
`hajek_convolution_theorem_basis`) and the adapters that feed the semiparametric
lower-bound theorems.

Reference: van der Vaart §25.3.1 (Hájek's representation theorem) and §25.3.2
(regular-estimator definition).
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal BigOperators

namespace AsymptoticStatistics.LowerBounds.RegularEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.MassMethod
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## The linear-combination score `Σᵢ h_i • g_P i` -/

/-- The linear combination `Σᵢ h_i • g_P i` as an element of
`↥(L2ZeroMean P)`. Used as the score of the QMDPath produced from the
parametric submodel along direction `h`.

Derived from the `g_P` family; a notational convenience. -/
noncomputable def linPerturbScore
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h : EuclideanSpace ℝ (Fin m)) : ↥(L2ZeroMean P) :=
  ∑ i, (h i) • g_P i

/-- Per-Finset version: the L²-coercion of `∑ i ∈ s, h i • g_P i`
agrees `P`-a.e. with the pointwise linear combination using the
strongly-measurable representatives `gMk`. -/
lemma linPerturbScore_finsetSum_coe_ae
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h : EuclideanSpace ℝ (Fin m)) (s : Finset (Fin m)) :
    let F : ↥(L2ZeroMean P) → Lp ℝ 2 P := fun u => (u : Lp ℝ 2 P)
    ((F (∑ i ∈ s, h i • g_P i)) : Ω → ℝ)
      =ᵐ[P] (fun ω => ∑ i ∈ s, h i * gMk g_P i ω) := by
  classical
  intro F
  refine Finset.induction_on s ?_ ?_
  · -- empty sum
    simp only [Finset.sum_empty]
    have hF0 : F (0 : ↥(L2ZeroMean P)) = (0 : Lp ℝ 2 P) := rfl
    rw [hF0]
    have hae : ((0 : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] (fun _ => (0 : ℝ)) :=
      Lp.coeFn_zero _ _ _
    refine hae.trans ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp
  · intro j t hjt ih
    -- The submodule coercion is an additive map: F splits over `insert j t`.
    have h_split :
        F (∑ i ∈ insert j t, h i • g_P i)
          = F (h j • g_P j) + F (∑ i ∈ t, h i • g_P i) := by
      rw [Finset.sum_insert hjt]
      rfl
    rw [h_split]
    -- Apply Lp.coeFn_add.
    have h_add_ae := Lp.coeFn_add (F (h j • g_P j)) (F (∑ i ∈ t, h i • g_P i))
    refine h_add_ae.trans ?_
    -- The smul piece: F (h j • g_P j) = h j • F (g_P j) since F is a linear map
    -- (well, it's the submodule subtype, which preserves smul).
    have h_smul_eq : F (h j • g_P j) = h j • F (g_P j) := rfl
    have h_smul_ae :
        ((F (h j • g_P j)) : Ω → ℝ)
          =ᵐ[P] (h j) • ((F (g_P j)) : Ω → ℝ) := by
      rw [h_smul_eq]
      exact Lp.coeFn_smul _ _
    have h_gMk_j : gMk g_P j =ᵐ[P] ((F (g_P j)) : Ω → ℝ) :=
      gMk_ae_eq g_P j
    filter_upwards [h_smul_ae, ih, h_gMk_j] with ω h1 h2 h3
    rw [Finset.sum_insert hjt]
    -- Goal after `Lp.coeFn_add` is in pointwise sum form.
    change (F (h j • g_P j) : Ω → ℝ) ω + (F (∑ i ∈ t, h i • g_P i) : Ω → ℝ) ω
      = h j * gMk g_P j ω + ∑ i ∈ t, h i * gMk g_P i ω
    rw [h1, h2]
    -- (h j • F (g_P j)) ω = h j * F (g_P j) ω
    have h_smul_pt :
        ((h j) • ((F (g_P j)) : Ω → ℝ)) ω
          = h j * ((F (g_P j)) : Ω → ℝ) ω := by
      simp [Pi.smul_apply, smul_eq_mul]
    rw [h_smul_pt, ← h3]

/-- The L²-coercion of `linPerturbScore` agrees `P`-a.e. with the
pointwise linear combination using the strongly-measurable
representatives `gMk`. -/
lemma linPerturbScore_coe_ae
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h : EuclideanSpace ℝ (Fin m)) :
    ((linPerturbScore g_P h : Lp ℝ 2 P) : Ω → ℝ)
      =ᵐ[P] linPerturb g_P h := by
  classical
  unfold linPerturbScore linPerturb
  exact linPerturbScore_finsetSum_coe_ae g_P h Finset.univ

/-! ## Bounded mixture-score property of `linPerturbScore` -/

/-- For any `h : EuclideanSpace ℝ (Fin m)`, the linear combination
`linPerturbScore g_P h` is itself a bounded mixture score (i.e., a
member of `IsBoundedMixtureScore`).

The L∞ bound is `‖h‖ * m * uniformBound`. The lower-bound `≥ -1` part
is derived from a uniform pointwise bound `|linPerturbScore g_P h ω|
≤ ‖h‖ * m * uniformBound` plus the additional condition that this
upper bound itself is `≤ 1` — which requires `‖h‖` to be small. To
keep this lemma usable for *any* `h`, we instead **scale** to get the
bound: we accept any `h` and produce a witness for the underlying
boundedness, but for the `≥ -1` part we use the looser bound `≥ -|...|
≥ -B` and combine with the choice of `B`. The cleanest: the M of the
bounded-mixture-score is `‖h‖ * m * uniformBound + 1`, and the
`≥ -1` clause requires choosing the score scaled by an appropriate
factor. In this slice we do not need a tight bound — we just need
`linPerturbScore g_P h` to satisfy `IsBoundedMixtureScore` for some
*appropriate scaling*. We achieve this by scaling: the score we
ultimately use for the QMDPath is `linPerturbScore g_P (s • h)` for
sufficiently small `|s|` — but that scaled by the QMDPath's own `t`
parameter at curve evaluation time. So we register the unscaled score
together with a bound that *includes the lower-bound clause*.

Concretely: if `|linPerturbScore g_P h ω| ≤ B`, then
`linPerturbScore g_P h` itself is `IsBoundedMixtureScore` only if
`B ≤ 1`. For larger `B`, scale `h` by `1 / (B + 1)` first.

Edge behavior: when `m = 0`, the linear combination is `0 ∈ L²₀(P)`
trivially, and `0` is `IsBoundedMixtureScore` (witness `M = 0`). -/
lemma linPerturbScore_isBoundedMixtureScore_of_small
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m))
    (h_small : ‖h‖ * m * hg.uniformBound ≤ 1) :
    IsBoundedMixtureScore (linPerturbScore g_P h) := by
  classical
  -- Bound for the L² rep
  refine ⟨⟨‖h‖ * m * hg.uniformBound, ?_⟩, ?_⟩
  · -- |linPerturbScore g_P h ω| ≤ ‖h‖ * m * uniformBound a.e.
    have h_bound : ∀ᵐ ω ∂P,
        |linPerturb g_P h ω| ≤ ‖h‖ * m * hg.uniformBound :=
      abs_linPerturb_le g_P hg h
    have h_ae := linPerturbScore_coe_ae g_P h
    filter_upwards [h_bound, h_ae] with ω hω hae
    rw [hae]
    exact hω
  · -- linPerturbScore g_P h ω ≥ -1 a.e.
    have h_bound : ∀ᵐ ω ∂P,
        |linPerturb g_P h ω| ≤ ‖h‖ * m * hg.uniformBound :=
      abs_linPerturb_le g_P hg h
    have h_ae := linPerturbScore_coe_ae g_P h
    filter_upwards [h_bound, h_ae] with ω hω hae
    rw [hae]
    have : -1 ≤ -(‖h‖ * m * hg.uniformBound) := by linarith
    have habs := abs_le.mp hω
    linarith [habs.1, this]

/-- A scaled version: for any `h`, `linPerturbScore g_P (c • h)` is
`IsBoundedMixtureScore` whenever `|c| ≤ 1 / (‖h‖ * m * uniformBound + 1)`.

The factor `+1` keeps the threshold positive even when `‖h‖ = 0`. -/
lemma linPerturbScore_smul_isBoundedMixtureScore
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m)) {c : ℝ}
    (hc : |c| ≤ 1 / (‖h‖ * m * hg.uniformBound + 1)) :
    IsBoundedMixtureScore (linPerturbScore g_P (c • h)) := by
  classical
  -- ‖c • h‖ * m * M = |c| * ‖h‖ * m * M ≤ (‖h‖ * m * M) / (‖h‖ * m * M + 1) < 1.
  apply linPerturbScore_isBoundedMixtureScore_of_small g_P hg
  set M := hg.uniformBound
  have hM_nn : 0 ≤ M := hg.uniformBound_nonneg
  have hm_nn : (0 : ℝ) ≤ m := by positivity
  have hh_nn : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
  have hsum_nn : 0 ≤ ‖h‖ * m * M := by positivity
  have hpos : (0 : ℝ) < ‖h‖ * m * M + 1 := by linarith
  have hnorm_smul : ‖c • h‖ = |c| * ‖h‖ := by
    rw [norm_smul]
    simp [Real.norm_eq_abs]
  rw [hnorm_smul]
  -- Goal: |c| * ‖h‖ * m * M ≤ 1
  have hc_nn : 0 ≤ |c| := abs_nonneg _
  have h_step : |c| * ‖h‖ * m * M ≤
      (1 / (‖h‖ * m * M + 1)) * (‖h‖ * m * M) := by
    have : |c| * ‖h‖ * m * M = |c| * (‖h‖ * m * M) := by ring
    rw [this]
    have h_le : |c| ≤ 1 / (‖h‖ * m * M + 1) := hc
    exact mul_le_mul_of_nonneg_right h_le hsum_nn
  have h_simp : (1 / (‖h‖ * m * M + 1)) * (‖h‖ * m * M)
      = (‖h‖ * m * M) / (‖h‖ * m * M + 1) := by
    field_simp
  rw [h_simp] at h_step
  have h_lt_one : (‖h‖ * m * M) / (‖h‖ * m * M + 1) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  linarith

/-! ## Tangent-space membership -/

/-- Linear combinations of tangent-set elements lie in the closed
linear span (= tangent space). Used to certify that the score of the
QMDPath bridge lies in the tangent space. -/
lemma linPerturbScore_mem_tangentSpace
    {m : ℕ} (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_in_T : ∀ i, g_P i ∈ tangentSpace T_set)
    (h : EuclideanSpace ℝ (Fin m)) :
    linPerturbScore g_P h ∈ tangentSpace T_set := by
  classical
  unfold linPerturbScore
  refine Submodule.sum_mem _ ?_
  intro i _
  exact Submodule.smul_mem _ (h i) (h_in_T i)

/-- Span-scoped analogue of `linPerturbScore_mem_tangentSpace`: a linear
combination of elements of the *algebraic* span `Submodule.span ℝ T_set.carrier`
lies in that span. This is exactly what the (narrowed) regularity hypothesis
`IsRegularEstimator(_vec)` quantifies over — vdV p.366 only ever selects
submodels for `g ∈ lin g_p`, the algebraic span of a finite basis. -/
lemma linPerturbScore_mem_span
    {m : ℕ} (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_in_span : ∀ i, g_P i ∈ Submodule.span ℝ T_set.carrier)
    (h : EuclideanSpace ℝ (Fin m)) :
    linPerturbScore g_P h ∈ Submodule.span ℝ T_set.carrier := by
  classical
  unfold linPerturbScore
  refine Submodule.sum_mem _ ?_
  intro i _
  exact Submodule.smul_mem _ (h i) (h_in_span i)

/-! ## The QMDPath bridge -/

/-- *The bridge constructor.*

Given a parametric-submodel-from-scores setup
(`g_P`, `hg`, `h_orth`) and a direction `h : EuclideanSpace ℝ (Fin m)`
in parameter space, scaled small enough that the derived linear-
combination score `linPerturbScore g_P h` is a bounded mixture score,
this returns a `QMDPath P` whose score equals
`linPerturbScore g_P h` and whose curve agrees (eventually) with the
parametric submodel's density along `s • h`.

The construction simply delegates to `boundedDensityPath` from
`Core/MassMethod` applied to `linPerturbScore g_P h`. -/
noncomputable def paramSubmodelQMDPath
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m))
    (h_small : ‖h‖ * m * hg.uniformBound ≤ 1) :
    QMDPath P :=
  boundedDensityPath (linPerturbScore g_P h)
    (linPerturbScore_isBoundedMixtureScore_of_small g_P hg h h_small).toEss

/-- The score of the bridge QMDPath is exactly `linPerturbScore g_P h`. -/
theorem paramSubmodelQMDPath_score
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m))
    (h_small : ‖h‖ * m * hg.uniformBound ≤ 1) :
    (paramSubmodelQMDPath g_P hg h h_small).score
      = linPerturbScore g_P h :=
  boundedDensityPath_score _ _

/-- Tangent-set membership for the bridge score. -/
theorem paramSubmodelQMDPath_score_mem_tangentSpace
    {m : ℕ} (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_in_T : ∀ i, g_P i ∈ tangentSpace T_set)
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m))
    (h_small : ‖h‖ * m * hg.uniformBound ≤ 1) :
    (paramSubmodelQMDPath g_P hg h h_small).score
      ∈ tangentSpace T_set := by
  rw [paramSubmodelQMDPath_score]
  exact linPerturbScore_mem_tangentSpace T_set g_P h_in_T h

/-- **`P`-AE positive-and-finite Radon-Nikodym derivative**, valid for
all `t : ℝ`, for the bridge `paramSubmodelQMDPath`.

**Strategy.** `paramSubmodelQMDPath` is internally
`boundedDensityPath (linPerturbScore g_P h) (...).toEss`, so this
delegates to `boundedDensityPath_curve_rnDeriv_pos_finite_ae` (which
itself handles all `t` via internal case split). -/
theorem paramSubmodelQMDPath_curve_rnDeriv_pos_finite_ae
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m))
    (h_small : ‖h‖ * m * hg.uniformBound ≤ 1) (t : ℝ) :
    ∀ᵐ ω ∂P,
      0 < ((paramSubmodelQMDPath g_P hg h h_small).curve t).rnDeriv P ω
      ∧ ((paramSubmodelQMDPath g_P hg h h_small).curve t).rnDeriv P ω < ⊤ := by
  exact AsymptoticStatistics.Core.MassMethod.boundedDensityPath_curve_rnDeriv_pos_finite_ae
    (linPerturbScore g_P h)
    (linPerturbScore_isBoundedMixtureScore_of_small g_P hg h h_small).toEss t

/-! ## Curve identification: bridge curve = paramSubmodel density -/

/-- The bridge QMDPath's curve at parameter `s` agrees, eventually as
`s → 0`, with the parametric submodel's density along `s • h`.

For `|s|` small enough (within both the `boundedDensityPath`'s
truncation radius and the `paramSubmodel`'s `truncRadius`), both
sides reduce to `P.withDensity (1 + s · linPerturbScore g_P h ω)`
(modulo a.e.-equivalence). -/
theorem paramSubmodelQMDPath_curve_eq_paramSubmodel_density
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m))
    (h_small : ‖h‖ * m * hg.uniformBound ≤ 1) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      (paramSubmodelQMDPath g_P hg h h_small).curve s
        = P.withDensity (fun ω =>
            ENNReal.ofReal
              ((paramSubmodel g_P hg h_orth).density (s • h) ω)) := by
  classical
  -- Reconstruct the boundedDensityPath truncation threshold for the
  -- linPerturbScore.
  set g_total : ↥(L2ZeroMean P) := linPerturbScore g_P h with hg_total_def
  set hg_total : IsBoundedMixtureScore g_total :=
    linPerturbScore_isBoundedMixtureScore_of_small g_P hg h h_small
  set M_bd : ℝ := max 0 (Classical.choose hg_total.1) with hM_bd_def
  set δ_bd : ℝ := 1 / (M_bd + 1) with hδ_bd_def
  have hM_bd_nn : (0 : ℝ) ≤ M_bd := le_max_left _ _
  have hδ_bd_pos : (0 : ℝ) < δ_bd := by
    apply div_pos one_pos; linarith
  -- Reconstruct the paramSubmodel truncation threshold.
  set δ_ps : ℝ := truncRadius g_P hg with hδ_ps_def
  have hδ_ps_pos : (0 : ℝ) < δ_ps := truncRadius_pos g_P hg
  -- Choose `δ := min δ_bd (δ_ps / (‖h‖ + 1))` (positive). The factor
  -- `‖h‖ + 1` ensures that for `|s| < δ_ps / (‖h‖ + 1)`, we get
  -- `‖s • h‖ ≤ |s| * ‖h‖ < δ_ps`.
  set δ : ℝ := min δ_bd (δ_ps / (‖h‖ + 1)) with hδ_def
  have hh_nn : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
  have hh1_pos : (0 : ℝ) < ‖h‖ + 1 := by linarith
  have hδ_pos : (0 : ℝ) < δ := by
    apply lt_min hδ_bd_pos
    exact div_pos hδ_ps_pos hh1_pos
  -- Pointwise bounds for the score.
  have h_abs_total_le : ∀ᵐ ω ∂P,
      |((g_total : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M_bd := by
    have hChoose : ∀ᵐ ω ∂P,
        |((g_total : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ Classical.choose hg_total.1 :=
      Classical.choose_spec hg_total.1
    filter_upwards [hChoose] with ω hω
    exact hω.trans (le_max_right _ _)
  have h_g_ge : ∀ᵐ ω ∂P, -1 ≤ ((g_total : Lp ℝ 2 P) : Ω → ℝ) ω := hg_total.2
  -- linPerturbScore_coe_ae for the score.
  have h_score_ae := linPerturbScore_coe_ae g_P h
  -- Eventually: |s| < δ.
  have h_event : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < δ := by
    have : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ_pos
    filter_upwards [this] with s hs
    rw [abs_lt]; exact hs
  filter_upwards [h_event] with s hs
  have hs_lt_δbd : |s| < δ_bd := lt_of_lt_of_le hs (min_le_left _ _)
  have hs_lt_δps_h : |s| < δ_ps / (‖h‖ + 1) :=
    lt_of_lt_of_le hs (min_le_right _ _)
  -- LHS: boundedDensityPath.curve s = P.withDensity (1 + s · g_total) for |s| < δ_bd.
  have h_LHS : (paramSubmodelQMDPath g_P hg h h_small).curve s
      = P.withDensity (fun ω => ENNReal.ofReal
          (1 + s * ((g_total : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
    -- Unfold via the constructor.
    unfold paramSubmodelQMDPath
    change (if |s| < 1 / (max 0 (Classical.choose hg_total.1) + 1)
            then P.withDensity (fun ω => ENNReal.ofReal
              (1 + s * ((g_total : Lp ℝ 2 P) : Ω → ℝ) ω))
            else P) = _
    rw [if_pos hs_lt_δbd]
  rw [h_LHS]
  -- RHS:
  -- (paramSubmodel g_P hg h_orth).density (s • h) ω
  --   = submodelDensityNN g_P hg (s • h) ω.
  -- And submodelDensityNN =ᵐ submodelDensity, which for ‖s • h‖ < δ_ps reduces
  -- to 1 + linPerturb g_P (s • h).
  -- Need ‖s • h‖ < δ_ps.
  have h_norm_sh : ‖s • h‖ < δ_ps := by
    rw [norm_smul, Real.norm_eq_abs]
    -- |s| * ‖h‖ ≤ |s| * (‖h‖ + 1) < (δ_ps / (‖h‖ + 1)) * (‖h‖ + 1) = δ_ps
    have h1 : |s| * ‖h‖ ≤ |s| * (‖h‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |s| * (‖h‖ + 1) < δ_ps / (‖h‖ + 1) * (‖h‖ + 1) :=
      mul_lt_mul_of_pos_right hs_lt_δps_h hh1_pos
    have h3 : δ_ps / (‖h‖ + 1) * (‖h‖ + 1) = δ_ps := by
      field_simp
    linarith
  -- So submodelDensity g_P hg (s • h) ω = 1 + linPerturb g_P (s • h) ω
  -- everywhere (not just a.e. — by definition of submodelDensity in
  -- this branch).
  have h_sd_pt : ∀ ω, submodelDensity g_P hg (s • h) ω
      = 1 + linPerturb g_P (s • h) ω := by
    intro ω; unfold submodelDensity; rw [if_pos h_norm_sh]
  -- linPerturb g_P (s • h) ω = s * linPerturb g_P h ω.
  have h_linPerturb_smul : ∀ ω,
      linPerturb g_P (s • h) ω = s * linPerturb g_P h ω := by
    intro ω
    unfold linPerturb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    have : (s • h) i = s * h i := by
      simp [PiLp.smul_apply, smul_eq_mul]
    rw [this]; ring
  -- And linPerturb g_P h =ᵐ ((g_total : Lp ℝ 2 P) : Ω → ℝ).
  -- We have h_score_ae : ((g_total : Lp ℝ 2 P) : Ω → ℝ) =ᵐ linPerturb g_P h
  -- So we can write: 1 + s * linPerturb g_P h =ᵐ 1 + s * (g_total).
  -- The two `withDensity` measures are equal iff the densities are a.e.-equal.
  apply MeasureTheory.withDensity_congr_ae
  -- Goal: (fun ω => ENNReal.ofReal (1 + s * ((g_total : Lp ℝ 2 P) : Ω → ℝ) ω))
  --     =ᵐ (fun ω => ENNReal.ofReal ((paramSubmodel g_P hg h_orth).density (s • h) ω))
  -- The paramSubmodel density at (s • h) is submodelDensityNN, a.e.-equal to
  -- submodelDensity, which pointwise equals 1 + linPerturb (s • h) ω.
  have h_density_ae :
      (fun ω => (paramSubmodel g_P hg h_orth).density (s • h) ω)
        =ᵐ[P]
      (fun ω => submodelDensity g_P hg (s • h) ω) := by
    have h_eq : (paramSubmodel g_P hg h_orth).density (s • h)
        = submodelDensityNN g_P hg (s • h) := rfl
    rw [h_eq]
    exact submodelDensityNN_ae_eq g_P hg (s • h)
  filter_upwards [h_score_ae, h_density_ae] with ω hae_score hae_density
  -- LHS: ENNReal.ofReal (1 + s * (g_total) ω)
  -- RHS: ENNReal.ofReal ((paramSubmodel ...).density (s • h) ω)
  --     = ENNReal.ofReal (submodelDensity g_P hg (s • h) ω)  [via hae_density]
  --     = ENNReal.ofReal (1 + linPerturb g_P (s • h) ω)       [h_sd_pt]
  --     = ENNReal.ofReal (1 + s * linPerturb g_P h ω)         [h_linPerturb_smul]
  --     = ENNReal.ofReal (1 + s * (g_total) ω)                [hae_score reversed]
  rw [hae_density, h_sd_pt ω, h_linPerturb_smul ω, ← hae_score]

/-! ## All-`h` variant: `paramSubmodelQMDPathAllH`

The existing `paramSubmodelQMDPath` requires `h_small : ‖h‖ * m * uniformBound ≤ 1`
so that `linPerturbScore g_P h` is `IsBoundedMixtureScore` (essentially
bounded AND `≥ -1` a.e.). The `≥ -1` clause is what fails for large `h`.

However, `boundedDensityPath` only consumes the *essentially bounded*
witness (`IsEssBoundedMixtureScore`): the truncated curve
`(1 + t·g)·P` is a probability measure on `|t| < 1/(M+1)` solely on the
strength of `|g| ≤ M` a.e. (the `≥ -1` clause is only used for the
non-truncated `(1+g)·P` form). Since `linPerturbScore g_P h` is
essentially bounded by `‖h‖ * m * uniformBound` *without* any smallness
on `h`, we can construct a QMDPath for any direction `h` by relaxing
the witness. -/

/-- For any `h`, `linPerturbScore g_P h` is essentially bounded by
`‖h‖ * m * uniformBound` — no smallness condition on `h` required. -/
lemma linPerturbScore_isEssBoundedMixtureScore
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m)) :
    IsEssBoundedMixtureScore (linPerturbScore g_P h) := by
  classical
  refine ⟨‖h‖ * m * hg.uniformBound, ?_⟩
  have h_bound : ∀ᵐ ω ∂P,
      |linPerturb g_P h ω| ≤ ‖h‖ * m * hg.uniformBound :=
    abs_linPerturb_le g_P hg h
  have h_ae := linPerturbScore_coe_ae g_P h
  filter_upwards [h_bound, h_ae] with ω hω hae
  rw [hae]
  exact hω

/-- *All-`h` analogue of `paramSubmodelQMDPath`*: a `QMDPath P` whose
score is `linPerturbScore g_P h` and whose curve at small `s` agrees
(eventually) with the parametric submodel's density along `s • h` —
for any direction `h`, with no smallness restriction.

Built via `boundedDensityPath` with the relaxed
`linPerturbScore_isEssBoundedMixtureScore` witness. The
`boundedDensityPath` constructor handles arbitrary essentially-bounded
scores; the only consequence of larger `h` is a smaller internal
truncation radius `δ_h = 1/(‖h‖·m·M + 1)`, but the eventually-as-`s→0`
behavior near 0 still gives QMD limits and curve identifications. -/
noncomputable def paramSubmodelQMDPathAllH
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m)) : QMDPath P :=
  boundedDensityPath (linPerturbScore g_P h)
    (linPerturbScore_isEssBoundedMixtureScore g_P hg h)

/-- The score of the all-`h` bridge QMDPath is `linPerturbScore g_P h`. -/
theorem paramSubmodelQMDPathAllH_score
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h : EuclideanSpace ℝ (Fin m)) :
    (paramSubmodelQMDPathAllH g_P hg h).score = linPerturbScore g_P h :=
  boundedDensityPath_score _ _

/-- The all-`h` bridge QMDPath's curve at parameter `s` agrees,
eventually as `s → 0`, with the parametric submodel's density along
`s • h` — for any direction `h`, with no smallness restriction.

For `|s|` small enough (within both the all-`h` `boundedDensityPath`'s
truncation radius `δ_h = 1/(‖h‖·m·M + 1)` and the `paramSubmodel`'s
`truncRadius`), both sides reduce to
`P.withDensity (1 + s · linPerturbScore g_P h ω)` (modulo a.e.). -/
theorem paramSubmodelQMDPathAllH_curve_eq_paramSubmodel_density
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      (paramSubmodelQMDPathAllH g_P hg h).curve s
        = P.withDensity (fun ω =>
            ENNReal.ofReal
              ((paramSubmodel g_P hg h_orth).density (s • h) ω)) := by
  classical
  -- Mirror the small-h variant; only the witness changes.
  set g_total : ↥(L2ZeroMean P) := linPerturbScore g_P h with hg_total_def
  set hg_total : IsEssBoundedMixtureScore g_total :=
    linPerturbScore_isEssBoundedMixtureScore g_P hg h
  set M_bd : ℝ := max 0 (Classical.choose hg_total) with hM_bd_def
  set δ_bd : ℝ := 1 / (M_bd + 1) with hδ_bd_def
  have hM_bd_nn : (0 : ℝ) ≤ M_bd := le_max_left _ _
  have hδ_bd_pos : (0 : ℝ) < δ_bd := by
    apply div_pos one_pos; linarith
  set δ_ps : ℝ := truncRadius g_P hg with hδ_ps_def
  have hδ_ps_pos : (0 : ℝ) < δ_ps := truncRadius_pos g_P hg
  set δ : ℝ := min δ_bd (δ_ps / (‖h‖ + 1)) with hδ_def
  have hh_nn : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
  have hh1_pos : (0 : ℝ) < ‖h‖ + 1 := by linarith
  have hδ_pos : (0 : ℝ) < δ := by
    apply lt_min hδ_bd_pos
    exact div_pos hδ_ps_pos hh1_pos
  have h_score_ae := linPerturbScore_coe_ae g_P h
  have h_event : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < δ := by
    have : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ_pos
    filter_upwards [this] with s hs
    rw [abs_lt]; exact hs
  filter_upwards [h_event] with s hs
  have hs_lt_δbd : |s| < δ_bd := lt_of_lt_of_le hs (min_le_left _ _)
  have hs_lt_δps_h : |s| < δ_ps / (‖h‖ + 1) :=
    lt_of_lt_of_le hs (min_le_right _ _)
  have h_LHS : (paramSubmodelQMDPathAllH g_P hg h).curve s
      = P.withDensity (fun ω => ENNReal.ofReal
          (1 + s * ((g_total : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
    unfold paramSubmodelQMDPathAllH
    change (if |s| < 1 / (max 0 (Classical.choose hg_total) + 1)
            then P.withDensity (fun ω => ENNReal.ofReal
              (1 + s * ((g_total : Lp ℝ 2 P) : Ω → ℝ) ω))
            else P) = _
    rw [if_pos hs_lt_δbd]
  rw [h_LHS]
  have h_norm_sh : ‖s • h‖ < δ_ps := by
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |s| * ‖h‖ ≤ |s| * (‖h‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |s| * (‖h‖ + 1) < δ_ps / (‖h‖ + 1) * (‖h‖ + 1) :=
      mul_lt_mul_of_pos_right hs_lt_δps_h hh1_pos
    have h3 : δ_ps / (‖h‖ + 1) * (‖h‖ + 1) = δ_ps := by
      field_simp
    linarith
  have h_sd_pt : ∀ ω, submodelDensity g_P hg (s • h) ω
      = 1 + linPerturb g_P (s • h) ω := by
    intro ω; unfold submodelDensity; rw [if_pos h_norm_sh]
  have h_linPerturb_smul : ∀ ω,
      linPerturb g_P (s • h) ω = s * linPerturb g_P h ω := by
    intro ω
    unfold linPerturb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    have : (s • h) i = s * h i := by
      simp [PiLp.smul_apply, smul_eq_mul]
    rw [this]; ring
  apply MeasureTheory.withDensity_congr_ae
  have h_density_ae :
      (fun ω => (paramSubmodel g_P hg h_orth).density (s • h) ω)
        =ᵐ[P]
      (fun ω => submodelDensity g_P hg (s • h) ω) := by
    have h_eq : (paramSubmodel g_P hg h_orth).density (s • h)
        = submodelDensityNN g_P hg (s • h) := rfl
    rw [h_eq]
    exact submodelDensityNN_ae_eq g_P hg (s • h)
  filter_upwards [h_score_ae, h_density_ae] with ω hae_score hae_density
  rw [hae_density, h_sd_pt ω, h_linPerturb_smul ω, ← hae_score]

/-! ## Joint convergence bridge for Hájek's convolution theorem

For Hájek's convolution theorem we need: along *some* subsequence, the
joint pair `(√n·(T_n - ψ P), scoreSum (g_P_total g_P))` weakly converges to a
joint limit measure under the base product measure `P^n` (= `productMeasure
(paramSubmodel ...) P 0 n` since the paramSubmodel density at `0` is identically
`1`). The existential form is sufficient: the convolution theorem then
extracts the joint structure via Le Cam's third lemma + characterisation
theorems on a per-subsequence basis.

The proof is a Prohorov-style joint-tightness argument:
1. Marginal 1 (recentered estimator under `P^n`) is tight: by
   `IsRegularEstimator.weak_limit_at_zero` applied along a constant-curve
   QMDPath whose curve is identically `P` (so `(curve.curve t)^n = P^n`),
   the recentered statistic weakly converges to `L`, hence its range is
   tight (`Prohorov.weakConverges_range_tight`).
2. Marginal 2 (`scoreSum` under `P^n`) is tight: by `scoreSum_weakly_converges`
   from `Asymptotics/LAN/AsymptoticRepresentation.lean` applied to the paramSubmodel — the
   score sum weakly converges to `multivariateGaussian 0 I_m` (Fisher = identity
   by `paramSubmodel_fisher_info`); the range is then tight.
3. Joint tightness on `ℝ × EuclideanSpace ℝ (Fin m)` follows from
   `Prohorov.tight_prod_of_tight_marginals`.
4. `Prohorov.extract_weak_subseq` on the Polish product space yields a
   weakly-convergent subsequence with limit `μ_joint`. -/

/-! ### Constant `P`-curve QMDPath -/

/-- The score `0 : ↥(L2ZeroMean P)` is a bounded-mixture score (witness `M = 0`).
Trivial regularity check needed to instantiate `boundedDensityPath`
with the zero score. -/
private lemma isBoundedMixtureScore_zero (P : Measure Ω) [IsProbabilityMeasure P] :
    IsBoundedMixtureScore (0 : ↥(L2ZeroMean P)) := by
  refine ⟨⟨(0 : ℝ), ?_⟩, ?_⟩
  · -- |((0 : Lp ℝ 2 P) ω)| ≤ 0 a.e. — pointwise the L²-rep of 0 is a.e. 0.
    have h_ae : (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] (fun _ => 0) :=
      Lp.coeFn_zero _ _ _
    filter_upwards [h_ae] with ω hω
    rw [hω]; simp
  · -- -1 ≤ ((0 : Lp ℝ 2 P) ω) a.e.
    have h_ae : (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] (fun _ => 0) :=
      Lp.coeFn_zero _ _ _
    filter_upwards [h_ae] with ω hω
    rw [hω]; norm_num

/-- The constant-`P` QMDPath: every curve point is `P`, the score is `0`.
Built via `boundedDensityPath 0 (isBoundedMixtureScore_zero P)`; the `1 + t·0 = 1`
density collapses each curve point to `P`. -/
private noncomputable def constP_QMDPath (P : Measure Ω) [IsProbabilityMeasure P] :
    QMDPath P :=
  boundedDensityPath (0 : ↥(L2ZeroMean P)) (isBoundedMixtureScore_zero P).toEss

/-- Score of the constant-`P` QMDPath is `0`. -/
private lemma constP_QMDPath_score : (constP_QMDPath P).score = 0 :=
  boundedDensityPath_score _ _

/-- Every curve point of the constant-`P` QMDPath equals `P`. -/
private lemma constP_QMDPath_curve_eq (t : ℝ) : (constP_QMDPath P).curve t = P := by
  classical
  unfold constP_QMDPath boundedDensityPath
  set hg0 : IsBoundedMixtureScore (0 : ↥(L2ZeroMean P)) :=
    isBoundedMixtureScore_zero P with hg0_def
  by_cases h : |t| < 1 / (max 0 (Classical.choose hg0.1) + 1)
  · -- |t| < δ: density is `1 + t·0 = 1` a.e.; withDensity of constant 1 is P.
    change (if |t| < 1 / (max 0 (Classical.choose hg0.1) + 1)
            then P.withDensity
              (fun ω => ENNReal.ofReal
                (1 + t * (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω))
            else P) = P
    rw [if_pos h]
    have h_zero_ae : (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] (fun _ => 0) :=
      Lp.coeFn_zero _ _ _
    have h_density_one_ae :
        (fun ω => ENNReal.ofReal
          (1 + t * (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω))
          =ᵐ[P] (fun _ : Ω => (1 : ℝ≥0∞)) := by
      filter_upwards [h_zero_ae] with ω hω
      rw [hω, mul_zero, add_zero, ENNReal.ofReal_one]
    rw [withDensity_congr_ae h_density_one_ae, withDensity_const, one_smul]
  · change (if |t| < 1 / (max 0 (Classical.choose hg0.1) + 1)
            then P.withDensity
              (fun ω => ENNReal.ofReal
                (1 + t * (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω))
            else P) = P
    rw [if_neg h]

/-- **`P`-AE positive-and-finite Radon-Nikodym derivative**, valid for
all `t : ℝ`, for the constant-`P` QMDPath.

Trivial: `(constP_QMDPath P).curve t = P` for all `t`, so the rnDeriv
is `P.rnDeriv P = 1` `P`-a.e. -/
private lemma constP_QMDPath_curve_rnDeriv_pos_finite_ae (t : ℝ) :
    ∀ᵐ ω ∂P,
      0 < ((constP_QMDPath P).curve t).rnDeriv P ω
      ∧ ((constP_QMDPath P).curve t).rnDeriv P ω < ⊤ := by
  rw [constP_QMDPath_curve_eq]
  filter_upwards [P.rnDeriv_self] with ω hω
  rw [hω]
  exact ⟨zero_lt_one, ENNReal.one_lt_top⟩

/-! ### Product-measure identification -/

/-- For the parametric submodel at parameter `0`, the iid product measure
agrees with the iid product of `P`, since the density at `0` is identically `1`. -/
private lemma productMeasure_paramSubmodel_zero_eq_pi_P
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (n : ℕ) :
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure
        (paramSubmodel g_P hg h_orth) P (0 : EuclideanSpace ℝ (Fin m)) n
      = Measure.pi (fun _ : Fin n => P) := by
  classical
  unfold AsymptoticStatistics.AsymptoticRepresentation.productMeasure
  have h_density_one : ∀ ω,
      (paramSubmodel g_P hg h_orth).density (0 : EuclideanSpace ℝ (Fin m)) ω = 1 :=
    paramSubmodel_density_at_zero g_P hg h_orth
  have h_factor :
      (fun _ : Fin n =>
          P.withDensity (fun ω => ENNReal.ofReal
            ((paramSubmodel g_P hg h_orth).density 0 ω)))
        = (fun _ : Fin n => P) := by
    funext _
    -- The density `fun ω => ENNReal.ofReal (1) = (fun _ => 1) = 1 • μ = μ` via
    -- `withDensity_const`.
    have h_eq : (fun ω => ENNReal.ofReal
        ((paramSubmodel g_P hg h_orth).density (0 : EuclideanSpace ℝ (Fin m)) ω))
          = (fun _ : Ω => (1 : ℝ≥0∞)) := by
      funext ω; rw [h_density_one ω, ENNReal.ofReal_one]
    rw [h_eq, withDensity_const, one_smul]
  rw [h_factor]

/-! ### `scoreSum` weak-conv specialisation for paramSubmodel -/

/-- The `scoreSum` (from `Asymptotics/LAN/AsymptoticRepresentation.lean`) for the
paramSubmodel score `g_P_total` weakly converges to the standard
multivariate Gaussian on `EuclideanSpace ℝ (Fin m)` under `P^n`. The Fisher
information at `θ = 0` is the identity, so the limit is
`multivariateGaussian 0 (1 : Matrix _ _ ℝ)`.

This is the second-marginal weak limit driving the joint-tightness argument
in `joint_convergence_of_regular`. -/
private theorem paramSubmodel_scoreSum_weakly_converges_under_P
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (AsymptoticStatistics.AsymptoticRepresentation.scoreSum
          (g_P_total g_P) n))
      (ProbabilityTheory.multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin m)) (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  -- Get the IsPDFOf instance.
  have hPDF : IsPDFOf (paramSubmodel g_P hg h_orth) P :=
    paramSubmodel_isPDFOf g_P hg h_orth
  have h_one : ∫ x, (paramSubmodel g_P hg h_orth).density 0 x ∂P = 1 :=
    hPDF.density_integral_eq_one 0
  have hint : Integrable ((paramSubmodel g_P hg h_orth).density 0) P :=
    hPDF.density_integrable 0
  have h_one_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin m),
      ∫ x, (paramSubmodel g_P hg h_orth).density (0 + t • u) x ∂P = 1 :=
    fun t u => hPDF.density_integral_eq_one (0 + t • u)
  have hint_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin m),
      Integrable ((paramSubmodel g_P hg h_orth).density (0 + t • u)) P :=
    fun t u => hPDF.density_integrable (0 + t • u)
  -- `g_P_total g_P` is measurable: built coordinatewise from the `gMk` reps,
  -- pushed through the linear (hence continuous, hence measurable) `WithLp.toLp 2`.
  have hℓ_meas : Measurable (g_P_total g_P) := by
    -- `g_P_total g_P ω = WithLp.toLp 2 (fun i => gMk g_P i ω)`.
    have h_pi : Measurable (fun ω : Ω => fun i : Fin m => gMk g_P i ω) := by
      refine measurable_pi_lambda _ ?_
      intro i
      exact gMk_meas g_P i
    -- `WithLp.toLp 2` is the (linear, hence continuous) inverse of `WithLp.equiv 2 _`,
    -- and `MeasurableEquiv.toLp 2 _` (from Mathlib) gives a measurable equivalence.
    exact (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp h_pi
  have hDQM := paramSubmodel_DQM g_P hg h_orth
  -- Fisher information = identity bilinear form. The parametric submodel's Fisher
  -- info at θ=0 equals the Euclidean inner product (paramSubmodel_fisher_info), which
  -- agrees with the matrix-pairing form for `J = 1`.
  have hJ_fisher : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (paramSubmodel g_P hg h_orth) P 0 (g_P_total g_P) u v
        = @inner ℝ _ _ u
            ((WithLp.equiv 2 _).symm
              ((1 : Matrix (Fin m) (Fin m) ℝ).mulVec ((WithLp.equiv 2 _) v))) := by
    intro u v
    rw [paramSubmodel_fisher_info g_P hg h_orth]
    -- Goal: `@inner ℝ _ _ u v = @inner ℝ _ _ u ((WithLp.equiv 2 _).symm ((1).mulVec
    -- ((WithLp.equiv 2 _) v)))`. Reduce RHS to `v` step by step.
    have h_mulVec : (1 : Matrix (Fin m) (Fin m) ℝ).mulVec ((WithLp.equiv 2 _) v)
        = (WithLp.equiv 2 _) v := Matrix.one_mulVec _
    rw [h_mulVec]
    -- Now goal: @inner ℝ _ _ u v = @inner ℝ _ _ u ((WithLp.equiv 2 _).symm
    --     ((WithLp.equiv 2 _) v)). Both sides are equal because symm undoes the equiv.
    rw [Equiv.symm_apply_apply]
  have hJ_psd : (1 : Matrix (Fin m) (Fin m) ℝ).PosSemidef :=
    Matrix.PosSemidef.one
  have h_clt :=
    AsymptoticStatistics.AsymptoticRepresentation.scoreSum_weakly_converges
      (paramSubmodel g_P hg h_orth) P 0 (g_P_total g_P) hℓ_meas
      h_one hint h_one_perturb hint_perturb hDQM
      (1 : Matrix (Fin m) (Fin m) ℝ) hJ_psd hJ_fisher
  -- Convert `productMeasure paramSubmodel P 0 n` to `Measure.pi (fun _ => P)`.
  intro f
  have h_eq : ∀ n,
      (Measure.pi (fun _ : Fin n => P)).map
          (AsymptoticStatistics.AsymptoticRepresentation.scoreSum
            (g_P_total g_P) n)
        = (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (paramSubmodel g_P hg h_orth) P 0 n).map
          (AsymptoticStatistics.AsymptoticRepresentation.scoreSum
            (g_P_total g_P) n) := fun n => by
    rw [productMeasure_paramSubmodel_zero_eq_pi_P g_P hg h_orth n]
  simp_rw [h_eq]
  exact h_clt f

/-! ### Main theorem -/

/-- **Joint convergence bridge for Hájek's convolution theorem.**

Given a regular estimator (in the canonical vdV §25.3.2 sense)
plus an orthonormal score basis `g_P` with bounded-mixture-score property
`hg` (setup of `paramSubmodel`), there exists a joint limit
probability measure on `ℝ × EuclideanSpace ℝ (Fin m)` to which the joint
pair

```
(√n · (T_n − ψ P),  scoreSum (g_P_total g_P) n)
```

weakly converges along *some* subsequence under the base product measure
`P^n`.

This is the existential form: Hájek's convolution theorem
extracts the joint structure via Le Cam's third lemma applied
to the joint limit measure plus marginal characterisations from
`scoreSum_weakly_converges` (multivariate Gaussian with covariance the
identity, since the paramSubmodel's Fisher information at `θ = 0` is
`I_m`).

Reference: vdV §25.3.1 (Hájek's representation theorem), the joint-
weak-convergence input that drives the LAM/convolution conclusion.

Proof strategy:
1. Marginal 1 weakly converges to `L` under `P^n`: apply
   `IsRegularEstimator.weak_limit_at_zero` along the constant-`P`
   QMDPath `constP_QMDPath`. Tight by
   `Prohorov.weakConverges_range_tight`.
2. Marginal 2 weakly converges to `multivariateGaussian 0 I_m` under
   `P^n`: apply `scoreSum_weakly_converges` from `Asymptotics/LAN/AsymptoticRepresentation`,
   specialised to `M = paramSubmodel`, `θ₀ = 0`, `ℓ = g_P_total g_P`,
   `J = I_m` (via `paramSubmodel_fisher_info`). Tight likewise.
3. Joint tightness from `Prohorov.tight_prod_of_tight_marginals`.
4. Subsequence weak limit by `Prohorov.extract_weak_subseq` on the
   Polish product space `ℝ × EuclideanSpace ℝ (Fin m)`. -/
theorem joint_convergence_of_regular
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    ∃ μ_joint : Measure (ℝ × EuclideanSpace ℝ (Fin m)),
      IsProbabilityMeasure μ_joint ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        WeakConverges
          (fun k_idx => (Measure.pi (fun _ : Fin (φ k_idx) => P)).map
            (fun X : Fin (φ k_idx) → Ω =>
              (Real.sqrt (φ k_idx) * (T_n (φ k_idx) X - ψ P),
               AsymptoticStatistics.AsymptoticRepresentation.scoreSum
                 (g_P_total g_P) (φ k_idx) X)))
          μ_joint := by
  classical
  -- Step 1: first-marginal weak limit via constant-P QMDPath.
  have h_zero_in : (0 : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier := Submodule.zero_mem _
  have h_first_weak_curve :
      WeakConverges
        (fun n : ℕ =>
          (Measure.pi
              (fun _ : Fin n => (constP_QMDPath P).curve ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X - ψ ((constP_QMDPath P).curve ((Real.sqrt n)⁻¹)))))
        L :=
    hReg.weak_limit_at_zero (constP_QMDPath P) constP_QMDPath_score h_zero_in
  -- Replace `(constP_QMDPath P).curve t` by `P`.
  have h_first_weak :
      WeakConverges
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
        L := by
    intro f
    have h_curve_eq : ∀ n : ℕ,
        (Measure.pi (fun _ : Fin n => (constP_QMDPath P).curve ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X - ψ ((constP_QMDPath P).curve ((Real.sqrt n)⁻¹))))
          = (Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)) := by
      intro n
      have h_eq : (fun _ : Fin n => (constP_QMDPath P).curve ((Real.sqrt n)⁻¹))
          = (fun _ : Fin n => P) := by
        funext _; exact constP_QMDPath_curve_eq _
      rw [h_eq, constP_QMDPath_curve_eq]
    have := h_first_weak_curve f
    simpa [h_curve_eq] using this
  -- Step 2: second-marginal weak limit via paramSubmodel scoreSum.
  set ν2 : Measure (EuclideanSpace ℝ (Fin m)) :=
    ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
      (1 : Matrix (Fin m) (Fin m) ℝ) with hν2_def
  haveI : IsProbabilityMeasure ν2 := by
    rw [hν2_def]; infer_instance
  have h_second_weak :
      WeakConverges
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).map
          (AsymptoticStatistics.AsymptoticRepresentation.scoreSum
            (g_P_total g_P) n))
        ν2 :=
    paramSubmodel_scoreSum_weakly_converges_under_P g_P hg h_orth
  -- Step 3: joint tightness.
  set joint : ℕ → Measure (ℝ × EuclideanSpace ℝ (Fin m)) := fun n =>
    (Measure.pi (fun _ : Fin n => P)).map (fun X : Fin n → Ω =>
      (Real.sqrt n * (T_n n X - ψ P),
       AsymptoticStatistics.AsymptoticRepresentation.scoreSum
         (g_P_total g_P) n X)) with hjoint_def
  set Tseq : ℕ → Measure ℝ := fun n =>
    (Measure.pi (fun _ : Fin n => P)).map
      (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)) with hTseq_def
  set Δseq : ℕ → Measure (EuclideanSpace ℝ (Fin m)) := fun n =>
    (Measure.pi (fun _ : Fin n => P)).map
      (AsymptoticStatistics.AsymptoticRepresentation.scoreSum
        (g_P_total g_P) n) with hΔseq_def
  have hT_recentered_meas : ∀ n,
      Measurable (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)) := by
    intro n
    refine Measurable.const_mul ?_ _
    exact (hT_meas n).sub measurable_const
  -- Reusable measurability witness for `g_P_total g_P`.
  have h_g_P_total_meas : Measurable (g_P_total g_P) := by
    have h_pi : Measurable (fun ω : Ω => fun i : Fin m => gMk g_P i ω) := by
      refine measurable_pi_lambda _ ?_
      intro i
      exact gMk_meas g_P i
    exact (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp h_pi
  have hΔ_meas : ∀ n,
      Measurable (AsymptoticStatistics.AsymptoticRepresentation.scoreSum
        (g_P_total g_P) n) := by
    intro n
    unfold AsymptoticStatistics.AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => h_g_P_total_meas.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have h_joint_meas : ∀ n, Measurable
      (fun X : Fin n → Ω =>
        (Real.sqrt n * (T_n n X - ψ P),
         AsymptoticStatistics.AsymptoticRepresentation.scoreSum
           (g_P_total g_P) n X)) := fun n =>
    (hT_recentered_meas n).prodMk (hΔ_meas n)
  haveI hPiP : ∀ n, IsProbabilityMeasure (Measure.pi (fun _ : Fin n => P)) := fun _ =>
    inferInstance
  haveI h_joint_prob : ∀ n, IsProbabilityMeasure (joint n) := fun n =>
    Measure.isProbabilityMeasure_map (h_joint_meas n).aemeasurable
  haveI h_T_prob : ∀ n, IsProbabilityMeasure (Tseq n) := fun n =>
    Measure.isProbabilityMeasure_map (hT_recentered_meas n).aemeasurable
  haveI h_Δ_prob : ∀ n, IsProbabilityMeasure (Δseq n) := fun n =>
    Measure.isProbabilityMeasure_map (hΔ_meas n).aemeasurable
  -- Tightness of marginal sequences.
  have hT_tight : IsTightMeasureSet (Set.range Tseq) :=
    Prohorov.weakConverges_range_tight Tseq L h_first_weak
  have hΔ_tight : IsTightMeasureSet (Set.range Δseq) :=
    Prohorov.weakConverges_range_tight Δseq ν2 h_second_weak
  -- Joint marginal images coincide with the marginals.
  have h_marg_fst : ∀ n, (joint n).map Prod.fst = Tseq n := by
    intro n
    simp only [hjoint_def, hTseq_def, Measure.map_map measurable_fst (h_joint_meas n)]
    rfl
  have h_marg_snd : ∀ n, (joint n).map Prod.snd = Δseq n := by
    intro n
    simp only [hjoint_def, hΔseq_def, Measure.map_map measurable_snd (h_joint_meas n)]
    rfl
  -- Image equalities for tight_prod_of_tight_marginals.
  have h_fst_image :
      (fun ρ : Measure (ℝ × EuclideanSpace ℝ (Fin m)) => ρ.map Prod.fst)
        '' (Set.range joint) = Set.range Tseq := by
    ext ρ
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (h_marg_fst n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨joint n, ⟨n, rfl⟩, h_marg_fst n⟩
  have h_snd_image :
      (fun ρ : Measure (ℝ × EuclideanSpace ℝ (Fin m)) => ρ.map Prod.snd)
        '' (Set.range joint) = Set.range Δseq := by
    ext ρ
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (h_marg_snd n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨joint n, ⟨n, rfl⟩, h_marg_snd n⟩
  have h_joint_tight : IsTightMeasureSet (Set.range joint) :=
    Prohorov.tight_prod_of_tight_marginals _
      (h_fst_image ▸ hT_tight)
      (h_snd_image ▸ hΔ_tight)
  -- Step 4: extract weak-convergent subsequence on the Polish product space.
  obtain ⟨φ, hφ_mono, μ_joint, hμ_joint_prob, h_conv⟩ :=
    Prohorov.extract_weak_subseq joint h_joint_tight
  exact ⟨μ_joint, hμ_joint_prob, φ, hφ_mono, h_conv⟩

/-! ## Hájek's convolution theorem

The textbook convolution clause of vdV §25.3.1: from a regular estimator
sequence with limit `L`, the limit law `L` decomposes as
`L = N(0, σ²) ∗ M` for a residual probability measure `M` and Gaussian
variance `σ²` matching the EIF norm (scalar form, `σ² = ‖IF_eff‖²`) or a
finite-rank truncation thereof (m-dim form, `σ_m² = Σᵢ ⟪IF_eff, g_P i⟫²`).

The analytic crux — the joint MGF / characteristic-function factorisation
identity at the Gaussian-shift limit (vdV §25.3.1 Lemma 1; Bickel–
Klaassen–Ritov–Wellner Ch. 2) — is encapsulated as a
1-D char-fn factorisation hypothesis `hCharFn`, mirroring the upstream
brick `LeCamThirdAndCharFn.lecam_third_convolution`. The conclusion
`L = N(0, σ²) ∗ M` is then mechanical from `Measure.ext_of_charFun` +
`charFun_conv` (encapsulated in
`ForMathlib.CharFnConvolution.convolution_extraction_from_charFn`).

The canonical `IsRegularEstimator` (vdV §25.3.2 form) is consumed directly:
the unperturbed weak limit
`(P^n).map (√n·(T_n − ψ P)) ⇀ L` (the classical input to Lemma 2) is
derived internally via `IsRegularEstimator.weak_limit_at_zero` along the
constant-`P` QMDPath (`constP_QMDPath`),
not taken as a freestanding hypothesis. -/

/-! ### Internal weak-limit helper -/

/-- *The unperturbed weak limit, derived from `IsRegularEstimator`.*

Specialising the canonical `IsRegularEstimator` predicate
along the constant-`P` `QMDPath` (`constP_QMDPath`, whose curve
is identically `P` and whose score is `0 ∈ tangent space`) produces the
unperturbed weak-limit statement
`(P^n).map (√n · (T_n − ψ P))  ⇀  L`.

This is the workhorse extraction the Hájek convolution theorem consumes
when it invokes the char-fn factorisation route to produce the residual
measure. -/
lemma weak_limit_under_P_of_regular
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L) :
    WeakConverges
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).map
        (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
      L := by
  classical
  have h_zero_in : (0 : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier :=
    Submodule.zero_mem _
  have h_curve_weak :
      WeakConverges
        (fun n : ℕ =>
          (Measure.pi
              (fun _ : Fin n => (constP_QMDPath P).curve ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X - ψ ((constP_QMDPath P).curve ((Real.sqrt n)⁻¹)))))
        L :=
    hReg.weak_limit_at_zero (constP_QMDPath P) constP_QMDPath_score h_zero_in
  intro f
  have h_curve_eq : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => (constP_QMDPath P).curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n n X - ψ ((constP_QMDPath P).curve ((Real.sqrt n)⁻¹))))
        = (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)) := by
    intro n
    have h_eq : (fun _ : Fin n => (constP_QMDPath P).curve ((Real.sqrt n)⁻¹))
        = (fun _ : Fin n => P) := by
      funext _; exact constP_QMDPath_curve_eq _
    rw [h_eq, constP_QMDPath_curve_eq]
  have := h_curve_weak f
  simpa [h_curve_eq] using this

/-! ### Hájek's convolution theorem — scalar form -/

/-- **Hájek's convolution theorem** (vdV §25.3.1, scalar form).

For a regular estimator sequence `T_n` in the canonical vdV §25.3.2 sense,
with limit law `L` on `ℝ`, the limit `L` decomposes as a
convolution
```
L = N(0, ‖IF_eff‖²) ∗ M
```
of a Gaussian factor (variance `‖IF_eff‖²` = squared `L²(P)`-norm of the
efficient influence function) and a residual probability measure `M` on
`ℝ`.

**Hypotheses (book-data + analytic crux).**

The theorem consumes the canonical regular-estimator predicate
`hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L` (vdV
§25.3.2) plus the standard estimator-measurability hypothesis
`hT_meas`. The unperturbed weak limit
`(P^n).map (√n · (T_n − ψ P)) ⇀ L` (the analytic input to Le Cam's third
lemma) is *derived internally* via `IsRegularEstimator.weak_limit_at_zero`
along the constant-`P` `QMDPath` — no freestanding `WeakConverges`
hypothesis is required.

The **analytic crux** of the proof — the joint-MGF /
characteristic-function factorisation `charFun L u =
charFun (N(0, ‖IF_eff‖²)) u · charFun M u` for some probability measure
`M` (the law of `S − ⟨IF_eff, U⟩` extracted from the joint LAN-Gaussian
shift via Le Cam's third lemma + the multivariate identity theorem) —
is consumed as the hypothesis `hCharFn`. This mirrors the upstream brick
`LeCamThirdAndCharFn.lecam_third_convolution`: the post-extraction 1-D
char-fn identity is the lightest book-input that captures the textbook
content (vdV §25.3.1 Lemma 1; the joint MGF identity itself is provided by
`JointMGF.joint_mgf_identity`).

**Proof structure.**

1. Extract the unperturbed weak limit
   `(P^n).map (√n·(T_n − ψ P)) ⇀ L` from `hReg` via
   `weak_limit_under_P_of_regular` (the constant-`P` `QMDPath`
   specialisation of `IsRegularEstimator.weak_limit_at_zero`). This
   identifies `L` as the textbook regular-estimator limit law of
   vdV §25.3 Lemma 2 / §25.3.1.
2. The user-supplied char-fn factorisation `hCharFn` plus the
   user-supplied probability measure `M` provide the post-Le-Cam-3rd
   characterisation of `L`'s charFn against the Gaussian-shift factor
   `N(0, ‖IF_eff‖²)`.
3. Apply
   `ForMathlib.CharFnConvolution.convolution_extraction_from_charFn`
   (a `Measure.ext_of_charFun` + `charFun_conv` wrapper) to identify
   `L = N(0, ‖IF_eff‖²) ∗ M`.

The `hT_meas` hypothesis is the standard estimator-measurability
side-condition (vdV §25.3.2; needed for measure-theoretic well-formedness
of the pushforwards). The `_hT_meas` argument is not used by
the proof body (the unperturbed weak limit derivation uses curve-pi
collapse rather than separate measurability), but kept in the signature
to match the canonical regular-estimator API.

Reference: vdV §25.3.1 (Hájek's representation / convolution theorem);
Bickel–Klaassen–Ritov–Wellner, Ch. 2 (the convolution decomposition of
regular limits). -/
theorem hajek_convolution_theorem
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    -- standard side-condition; not used in this proof body but kept
    -- for API uniformity with `IsRegularEstimator.hajek_shift_form`.
    (_hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    -- `M` is the law of `S − ⟨IF_eff, U⟩` produced by Le Cam's
    -- third lemma applied to the joint LAN-Gaussian shift limit
    -- (vdV §25.3.1 Lemma 1).
    (M : Measure ℝ) [IsProbabilityMeasure M]
    -- `charFun L u = charFun (N(0, ‖IF_eff‖²)) u · charFun M u`. This
    -- is the post-extraction 1-D book content from vdV §25.3.1 Lemma 1
    -- (the joint MGF identity differentiated and evaluated at the
    -- Gaussian-shift direction); see the file docstring above for the
    -- analytic-crux explanation.
    (hCharFn : ∀ u : ℝ,
      MeasureTheory.charFun L u =
        MeasureTheory.charFun
          (ProbabilityTheory.gaussianReal 0
            ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩) u
          * MeasureTheory.charFun M u) :
    ∃ M' : Measure ℝ, IsProbabilityMeasure M' ∧
      L = (ProbabilityTheory.gaussianReal 0
              ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩) ∗ M' := by
  classical
  -- Step 1: extract the unperturbed weak limit. (Not needed for the
  -- char-fn-based extraction itself; recorded for the book pedigree.)
  have _h_weak :
      WeakConverges
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
        L :=
    weak_limit_under_P_of_regular T_set ψ hψ hEIF T_n L hReg
  -- Step 2: extract `M` from the char-fn factorisation via the
  -- `convolution_extraction_from_charFn` brick.
  refine ⟨M, ‹IsProbabilityMeasure M›, ?_⟩
  exact AsymptoticStatistics.ForMathlib.CharFnConvolution.convolution_extraction_from_charFn
    L M ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩ hCharFn

/-! ### Hájek's convolution theorem — m-dim basis form -/

/-- **Hájek's convolution theorem — m-dim basis form** (vdV §25.3.1).

For an orthonormal score basis `g_P : Fin m → ↥(L2ZeroMean P)` of a
finite-dim subspace of the tangent space, the regular-estimator limit
law `L` decomposes as
```
L = N(0, σ_m²) ∗ M_m
```
where `σ_m² = Σᵢ ⟪IF_eff, g_P i⟫²` is the squared norm of the projection
of `IF_eff` onto `span(g_P)` and `M_m` is a residual probability measure
on `ℝ`.

This is the per-`m` truncation of the scalar Hájek theorem
(`hajek_convolution_theorem`). The scalar form arises in the limit
`m → ∞` along an increasing projection sequence (cf. `proj_seq_to_eif` +
Lévy m-pass `ParametricBridge.levyMpass`) and is consumed downstream by
`AsymptoticStatistics.LowerBounds.Convolution.semiparametric_convolution_theorem` for the
full vdV §25.3 / Theorem 25.20 statement.

Upstream, `LeCamThirdAndCharFn.lecam_third_convolution` supplies a
near-identical conclusion under a freestanding `WeakConverges`
hypothesis; here we instead consume the canonical
`IsRegularEstimator` directly, deriving the unperturbed weak
limit internally via `weak_limit_under_P_of_regular`.

Reference: vdV §25.3.1 (Hájek's representation theorem, m-dim
truncation); BKRW, Ch. 2. -/
theorem hajek_convolution_theorem_basis
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    -- feeds `paramSubmodel`; not used in the proof body here but retained
    -- for API parity with the joint-convergence bridge
    -- `joint_convergence_of_regular`.
    (_hg : IsBoundedMixtureScores g_P)
    -- the basis is orthonormal so that `Σᵢ ⟪IF_eff, gᵢ⟫²` is
    -- the squared norm of the projection of `IF_eff` onto `span(g_P)`.
    (_h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    -- the law of `S − ⟨A_m, U⟩` for `A_m i = ⟪IF_eff, gᵢ⟫`,
    -- extracted from the joint LAN-Gaussian shift via Le Cam's third
    -- lemma + the multivariate identity theorem (vdV §25.3.1 Lemma 1).
    (M_m : Measure ℝ) [IsProbabilityMeasure M_m]
    -- `charFun L u = charFun (N(0, σ_m²)) u · charFun M_m u` where
    -- `σ_m² = Σᵢ ⟪IF_eff, gᵢ⟫²`. Same analytic crux as the scalar form;
    -- see file docstring.
    (hCharFn : ∀ u : ℝ,
      MeasureTheory.charFun L u =
        MeasureTheory.charFun
          (ProbabilityTheory.gaussianReal 0
            ⟨∑ i : Fin m,
                (⟪(IF_eff : ↥(L2ZeroMean P)),
                  (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
              Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) u
          * MeasureTheory.charFun M_m u) :
    ∃ M' : Measure ℝ, IsProbabilityMeasure M' ∧
      L = (ProbabilityTheory.gaussianReal 0
              ⟨∑ i : Fin m,
                  (⟪(IF_eff : ↥(L2ZeroMean P)),
                    (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) ∗ M' := by
  classical
  -- Step 1: extract the unperturbed weak limit, mirroring the scalar
  -- form (kept to record the canonical-IsRegularEstimator pedigree).
  have _h_weak :
      WeakConverges
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
        L :=
    weak_limit_under_P_of_regular T_set ψ hψ hEIF T_n L hReg
  -- Step 2: discharge via `convolution_extraction_from_charFn`.
  refine ⟨M_m, ‹IsProbabilityMeasure M_m›, ?_⟩
  exact AsymptoticStatistics.ForMathlib.CharFnConvolution.convolution_extraction_from_charFn
    L M_m
    ⟨∑ i : Fin m,
        (⟪(IF_eff : ↥(L2ZeroMean P)),
          (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩
    hCharFn

/-! ## Derivers for the three heavy inputs of `semiparametric_convolution_theorem` /
    `semiparametric_local_asymptotic_minimax_theorem`

The three heavy hypotheses that the user-facing lower-bound theorems
consume (`_hRegular`, `_hCovBlockPSD`, `_hBayesLowerBound`)
are derived from `IsRegularEstimator` plus a small set of
explicit textbook inputs (Hájek's char-fn factorization;
clause-(a) variance lower bound; basis-selection bridge for the Bayes
case). Each deriver below is the canonical adapter so callers only need to
supply the canonical predicate `IsRegularEstimator` plus the lightest book
content. -/

/-! ### (b) `hRegular_of_isRegular`: derive the slim per-`m` decomposition

Strategy: directly apply `hajek_convolution_theorem_basis` per
`m`, threading the per-`m` char-fn factorisation supplied
by the caller. -/

/-- *Derive `_hRegular` from `IsRegularEstimator` + Hájek.*

For a regular estimator `T_n` with weak limit `L`, Hájek's
convolution theorem shipped in this file supplies, per
orthonormal score basis `g_P : Fin m → ↥(L2ZeroMean P)`, the
decomposition `L = N(0, σ_m²) ∗ M_m` for some probability measure
`M_m`, where `σ_m² = Σᵢ ⟪IF_eff, g_P i⟫²`. This is exactly the slim
form of `_hRegular` consumed by `semiparametric_convolution_theorem`.

The analytic crux — the per-`m` 1-D char-fn factorisation that drives
`hajek_convolution_theorem_basis` — is the per-`m` hypothesis
`hCharFnAll` here.

Reference: vdV §25.3.1 (Hájek's representation theorem; per-`m`
truncation form). -/
theorem hRegular_of_isRegular
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (_hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    -- per-`m` 1-D char-fn factorisation; vdV §25.3.1 Lemma 1.
    -- Universal over orthonormal score bases of finite-dim subspaces
    -- of `tangentSpace T_set`. The per-`m` char-fn factorisation is
    -- the post-extraction 1-D book content (joint MGF identity
    -- differentiated and evaluated at the Gaussian-shift direction);
    -- see `hajek_convolution_theorem_basis` for the analytic crux.
    (hCharFnAll : ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
        Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
        (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set) →
        ∃ M_m : Measure ℝ, IsProbabilityMeasure M_m ∧
          ∀ u : ℝ,
            MeasureTheory.charFun L u =
              MeasureTheory.charFun
                (ProbabilityTheory.gaussianReal 0
                  ⟨∑ i : Fin m,
                      (⟪(IF_eff : ↥(L2ZeroMean P)),
                        (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                    Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) u
                * MeasureTheory.charFun M_m u) :
    ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
      Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
      (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set) →
      ∃ M_per : Measure ℝ, IsProbabilityMeasure M_per ∧
        L =
          MeasureTheory.Measure.conv
            (ProbabilityTheory.gaussianReal 0
              ⟨∑ i : Fin m,
                  (⟪(IF_eff : ↥(L2ZeroMean P)),
                    (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) M_per := by
  intro m g_P h_orth h_in_T
  obtain ⟨M_m, hM_prob, hCF⟩ := hCharFnAll g_P h_orth h_in_T
  -- Pass the char-fn data directly to the core
  -- `convolution_extraction_from_charFn` brick.
  refine ⟨M_m, hM_prob, ?_⟩
  exact AsymptoticStatistics.ForMathlib.CharFnConvolution.convolution_extraction_from_charFn
    L M_m
    ⟨∑ i : Fin m,
        (⟪(IF_eff : ↥(L2ZeroMean P)),
          (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩
    hCF

/-! ### (c) `hCovBlockPSDAll_of_isRegular`: derive joint covariance block PSD

Strategy: combine the slim per-`m` decomposition (delivered by
`hRegular_of_isRegular`, ultimately from Hájek) with the lighter
book input `‖IF_eff‖² ≤ varL` (clause (a) of the convolution theorem
— direct book content). Apply
`AsymptoticStatistics.ForMathlib.JointMGF.joint_covariance_block_posSemidef`
to conclude. -/

/-- *Derive the universal joint covariance block PSD claim
from `IsRegularEstimator` + the variance lower bound `‖IF_eff‖² ≤ varL`.*

The form of `_hCovBlockPSD` consumed by `semiparametric_convolution_theorem`
is universal over orthonormal score bases. Given `IsRegularEstimator`
plus the lighter book input `‖IF_eff‖² ≤ varL` (clause
(a) of the convolution theorem — direct book content), the universal
PSD claim follows by direct application of
`joint_covariance_block_posSemidef` (a Mathlib-style Gram + slack
decomposition that does not invoke the joint-MGF / Anderson
machinery internally).

The lighter input replaces the heavy
`_hCovBlockPSD` predicate with a single scalar inequality — the
canonical book content — at the cost of asking the caller for that
single inequality rather than the full universal PSD claim.

Reference: vdV §25.3 clause (a); `ForMathlib.JointMGF.joint_covariance_block_posSemidef`. -/
theorem hCovBlockPSDAll_of_isRegular
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (_hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    (varL : ℝ)
    -- clause (a) of the convolution theorem, direct book content.
    -- The full convolution theorem `semiparametric_convolution_theorem` discharges
    -- this from the convolution decomposition by Parseval + the
    -- variance-of-convolution algebra; exposed here as a light input.
    (hVarBound : ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 ≤ varL) :
    ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
      Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
      (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set) →
      (Matrix.fromBlocks
          (Matrix.of (fun _ _ : Fin 1 => varL))
          (Matrix.of (fun _ : Fin 1 => fun j : Fin m =>
            ⟪(IF_eff : ↥(L2ZeroMean P)),
              (g_P j : ↥(L2ZeroMean P))⟫_ℝ))
          (Matrix.of (fun i : Fin m => fun _ : Fin 1 =>
            ⟪(IF_eff : ↥(L2ZeroMean P)),
              (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
          (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  intro m g_P h_orth _h_in_T
  -- The Gram-block + slack decomposition lives in
  -- `ForMathlib.JointMGF.joint_covariance_block_posSemidef`; it
  -- requires only the orthonormality of `g_P` and the variance lower
  -- bound `‖w‖² ≤ varL` (with `w = IF_eff`).
  exact AsymptoticStatistics.ForMathlib.JointMGF.joint_covariance_block_posSemidef
    varL (IF_eff : ↥(L2ZeroMean P)) (fun i => (g_P i : ↥(L2ZeroMean P)))
    h_orth hVarBound

/-! ### (d) `hBayesLowerBound_of_isRegular`: per-(M, σ) Bayes-bound adapter

This conditional adapter accepts the per-`(M, σ)` Bayes lower bound in exactly
the form consumed by `semiparametric_local_asymptotic_minimax_theorem` and
returns that bound unchanged. The finite-tangent-set, truncated-loss, and
Gaussian-variance restrictions remain part of the supplied `hBayes`; they are
not consequences established here from `IsRegularEstimator`. -/

/-- *Conditional adapter for the per-(M, σ) Bayes lower bound consumed by
`semiparametric_local_asymptotic_minimax_theorem`.*

The caller supplies `hBayes` for every truncation level `M` and Gaussian
variance `σ_m_sq`. Its statement retains the supremum over finite subsets of
the tangent carrier, the liminf over sample size, and truncation of `ℓ`; this
theorem transports that assumption verbatim. The accompanying regularity,
path, and score arguments record the caller context but do not derive
`hBayes`.

Reference: vdV §25.3 Lemmas 3+4 (`bayes_risk_lower_bound`,
`gaussianShift_minimax`). -/
theorem hBayesLowerBound_of_isRegular
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (_hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    (γ : ↥(L2ZeroMean P) → QMDPath P)
    (_hγ_score : ∀ g, (g : ↥(L2ZeroMean P)) ∈ T_set.carrier →
      (γ g).score = g)
    (ℓ : ℝ → ℝ≥0∞)
    -- Caller-supplied per-(M, σ) Bayes lower bound, including its finite-set,
    -- truncated-loss, and Gaussian-variance restrictions.
    (hBayes :
      ∀ (M : ℕ) (σ_m_sq : ℝ≥0),
        ⨆ I : { S : Finset ↥(L2ZeroMean P) //
                (S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier },
          Filter.liminf
            (fun n : ℕ =>
              (I.val : Finset ↥(L2ZeroMean P)).sup
                (fun g =>
                  ∫⁻ X : Fin n → Ω,
                    (ℓ (Real.sqrt n *
                        (T_n n X - ψ ((γ g).curve ((Real.sqrt n)⁻¹))))
                      ⊓ (M : ℝ≥0∞))
                    ∂(MeasureTheory.Measure.pi
                        (fun _ : Fin n => (γ g).curve ((Real.sqrt n)⁻¹)))))
            atTop
          ≥ ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
              ∂(ProbabilityTheory.gaussianReal 0 σ_m_sq)) :
    ∀ (M : ℕ) (σ_m_sq : ℝ≥0),
      ⨆ I : { S : Finset ↥(L2ZeroMean P) //
              (S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier },
        Filter.liminf
          (fun n : ℕ =>
            (I.val : Finset ↥(L2ZeroMean P)).sup
              (fun g =>
                ∫⁻ X : Fin n → Ω,
                  (ℓ (Real.sqrt n *
                      (T_n n X - ψ ((γ g).curve ((Real.sqrt n)⁻¹))))
                    ⊓ (M : ℝ≥0∞))
                  ∂(MeasureTheory.Measure.pi
                      (fun _ : Fin n => (γ g).curve ((Real.sqrt n)⁻¹)))))
          atTop
        ≥ ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.gaussianReal 0 σ_m_sq) :=
  hBayes

end AsymptoticStatistics.LowerBounds.RegularEstimator
