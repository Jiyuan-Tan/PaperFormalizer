module
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

@[expose] public section

/-!
Asymptotic Statistics — Cramér–Wold device for joint weak convergence on
`ℝ × EuclideanSpace ℝ (Fin m)`.

This file ships a single theorem closing a Mathlib gap: *joint* weak convergence
on a finite-dimensional inner-product product space is determined by
per-direction linear projections. The statement uses the form needed downstream:
a real coordinate `t · p.1` plus a Euclidean coordinate `⟪h, p.2⟫_ℝ`.

## Strategy

Bridge the joint law to `WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))` (a
finite-dim real inner-product space) via the measurable equivalence
`MeasurableEquiv.toLp 2 _`, which is also a homeomorphism. On the
inner-product side, Mathlib's Lévy continuity theorem
`ProbabilityMeasure.tendsto_iff_tendsto_charFun` reduces weak convergence
to pointwise convergence of `charFun`. Each evaluation point `v` in
`WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))` corresponds, via
`WithLp.prod_inner_apply` and real-inner symmetry, to a per-direction
projection `fun p ↦ t · p.1 + ⟪h, p.2⟫_ℝ` with `(t, h) := WithLp.ofLp v`,
evaluated at the scalar 1. The per-direction Lévy theorem on ℝ delivers
that scalar charFun convergence.

The whole argument is roughly:
* per-direction `WeakConverges` ⇒ per-direction charFun convergence at 1
* ⇒ pointwise charFun convergence on the inner-product side
* ⇒ joint `WeakConverges` on the inner-product side
* ⇒ joint `WeakConverges` on the original product (`toLp` is a measurable
  homeomorphism, `WeakConverges` is preserved by continuous-mapping under
  the inverse).

## Public API

* `cramerWold_weakConverges` — the Cramér–Wold device.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal InnerProductSpace

namespace AsymptoticStatistics.ForMathlib

namespace CramerWold

variable {m : ℕ}

local notation "𝕊" => ℝ × EuclideanSpace ℝ (Fin m)
local notation "𝕊L" => WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))

/-- The per-direction projection `(t, h) ↦ (fun p ↦ t · p.1 + ⟪h, p.2⟫_ℝ)`,
viewed as a continuous (in fact linear) map `𝕊 → ℝ`. We pull characteristic
functions back through this projection to bridge per-direction Lévy with the
joint Lévy theorem on `𝕊L`. -/
@[simp] noncomputable def proj (t : ℝ) (h : EuclideanSpace ℝ (Fin m)) : 𝕊 → ℝ :=
  fun p => t * p.1 + ⟪h, p.2⟫_ℝ

lemma continuous_proj (t : ℝ) (h : EuclideanSpace ℝ (Fin m)) :
    Continuous (proj (m := m) t h) := by
  refine Continuous.add ?_ ?_
  · exact continuous_const.mul continuous_fst
  · exact (continuous_const.inner continuous_snd)

lemma measurable_proj (t : ℝ) (h : EuclideanSpace ℝ (Fin m)) :
    Measurable (proj (m := m) t h) :=
  (continuous_proj (m := m) t h).measurable

/-- Inner-product identity on `WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))`:
`⟪toLp p, v⟫_ℝ = (ofLp v).1 · p.1 + ⟪(ofLp v).2, p.2⟫_ℝ`. -/
lemma inner_toLp_eq_proj (p : 𝕊) (v : 𝕊L) :
    ⟪(WithLp.toLp 2 p : 𝕊L), v⟫_ℝ
      = (WithLp.ofLp v).1 * p.1 + ⟪(WithLp.ofLp v).2, p.2⟫_ℝ := by
  -- Use the L2-product inner-product formula.
  rw [WithLp.prod_inner_apply]
  -- After unfolding, the underlying components of `toLp p` are `p.1, p.2`.
  -- The first summand is `⟪p.1, (ofLp v).1⟫_ℝ` (real inner on `ℝ`),
  -- which equals `p.1 * (ofLp v).1`.
  -- The second summand is `⟪p.2, (ofLp v).2⟫_ℝ`, which by symmetry equals
  -- `⟪(ofLp v).2, p.2⟫_ℝ`.
  have h_eq1 : (⟪((WithLp.ofLp (WithLp.toLp 2 p : 𝕊L)).1 : ℝ),
        (WithLp.ofLp v).1⟫_ℝ : ℝ)
      = (WithLp.ofLp v).1 * p.1 := by
    -- Inner on `ℝ` is multiplication on real scalars; first component of
    -- `toLp p` is `p.1`.
    change inner ℝ p.1 (WithLp.ofLp v).1 = (WithLp.ofLp v).1 * p.1
    -- For real scalars, `⟪a, b⟫_ℝ = b * a` (definitional via `re` on ℝ).
    simp [inner, RCLike.re, mul_comm]
  have h_eq2 :
      (⟪((WithLp.ofLp (WithLp.toLp 2 p : 𝕊L)).2 : EuclideanSpace ℝ (Fin m)),
        (WithLp.ofLp v).2⟫_ℝ : ℝ)
      = ⟪(WithLp.ofLp v).2, p.2⟫_ℝ := by
    change ⟪p.2, (WithLp.ofLp v).2⟫_ℝ = _
    exact real_inner_comm _ _
  rw [h_eq1, h_eq2]

/-- Push-forward characterisation of `charFun` on `𝕊L`: at any `v : 𝕊L`,
`charFun (μ.map (toLp 2)) v` equals `charFun` of the projected scalar
measure `μ.map (proj t h)` evaluated at `1`, where
`(t, h) := WithLp.ofLp v`. -/
lemma charFun_map_toLp_eq
    {μ : Measure 𝕊} [SFinite μ] (v : 𝕊L) :
    charFun (μ.map (WithLp.toLp 2 (V := ℝ × EuclideanSpace ℝ (Fin m)))) v
      = charFun (μ.map (proj (m := m) (WithLp.ofLp v).1 (WithLp.ofLp v).2)) 1 := by
  classical
  set t : ℝ := (WithLp.ofLp v).1 with ht
  set h : EuclideanSpace ℝ (Fin m) := (WithLp.ofLp v).2 with hh
  -- `charFun (μ.map (toLp 2)) v = ∫ x, exp(⟪x, v⟫ * I) ∂μ.map toLp`.
  rw [charFun_apply]
  have h_toLp_meas : Measurable (WithLp.toLp 2 (V := ℝ × EuclideanSpace ℝ (Fin m))) :=
    WithLp.measurable_toLp _ _
  -- AEStronglyMeasurable witness for the integrand on `𝕊L`.
  have h_int_meas : AEStronglyMeasurable
      (fun x : 𝕊L => cexp (⟪x, v⟫_ℝ * I)) (μ.map (WithLp.toLp 2)) := by
    refine Continuous.aestronglyMeasurable ?_
    -- `cexp ∘ ((⟪·, v⟫_ℝ : ℝ → ℂ) * I)` is continuous.
    fun_prop
  -- Push the integral back through the measurable map `toLp`.
  rw [integral_map h_toLp_meas.aemeasurable h_int_meas]
  -- Replace the inner-product integrand with the projection integrand.
  have h_eq : ∀ p : 𝕊,
      cexp (⟪(WithLp.toLp 2 p : 𝕊L), v⟫_ℝ * I)
        = cexp ((proj (m := m) t h p) * I) := by
    intro p
    have := inner_toLp_eq_proj (m := m) p v
    simp only [proj]
    rw [this]
  have h_rewrite : ∫ p : 𝕊, cexp (⟪(WithLp.toLp 2 p : 𝕊L), v⟫_ℝ * I) ∂μ
      = ∫ p : 𝕊, cexp ((proj (m := m) t h p) * I) ∂μ := by
    refine integral_congr_ae (.of_forall fun p => ?_)
    exact h_eq p
  rw [h_rewrite]
  -- RHS: `charFun (μ.map (proj t h)) 1 = ∫ y, exp(1 * y * I) ∂(μ.map (proj t h))`
  --    = ∫ p, exp(1 * (proj t h p) * I) ∂μ = ∫ p, exp((proj t h p) * I) ∂μ.
  rw [charFun_apply_real]
  have h_int_meas_R : AEStronglyMeasurable
      (fun y : ℝ => cexp ((1 : ℝ) * y * I)) (μ.map (proj (m := m) t h)) :=
    Continuous.aestronglyMeasurable (by fun_prop)
  rw [integral_map (measurable_proj (m := m) t h).aemeasurable h_int_meas_R]
  -- Now both sides are integrals over `μ` differing in scalar 1*x vs x.
  refine integral_congr_ae (.of_forall fun p => ?_)
  -- `cexp ((proj t h p) * I) = cexp (1 * (proj t h p) * I)`.
  push_cast
  ring_nf

/-! ### The Cramér–Wold device -/

/-- **Cramér–Wold device** for `ℝ × EuclideanSpace ℝ (Fin m)` joint weak
convergence (intermediate form, in terms of `proj t h`). See the public
top-level `cramerWold_weakConverges` for the unfolded form. -/
theorem cramerWold_weakConverges_proj
    {μ_n : ℕ → Measure 𝕊}
    {μ : Measure 𝕊}
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure μ]
    (h_per_dir : ∀ (t : ℝ) (h : EuclideanSpace ℝ (Fin m)),
      WeakConverges
        (fun n => (μ_n n).map (proj (m := m) t h))
        (μ.map (proj (m := m) t h))) :
    WeakConverges μ_n μ := by
  classical
  let toLp_fun : 𝕊 → 𝕊L :=
    WithLp.toLp 2 (V := ℝ × EuclideanSpace ℝ (Fin m))
  have h_toLp_meas : Measurable toLp_fun := WithLp.measurable_toLp _ _
  -- Probability-measure structure on the lifted measures.
  haveI h_prob_n : ∀ n, IsProbabilityMeasure ((μ_n n).map toLp_fun) := fun n =>
    Measure.isProbabilityMeasure_map h_toLp_meas.aemeasurable
  haveI h_prob_lim : IsProbabilityMeasure (μ.map toLp_fun) :=
    Measure.isProbabilityMeasure_map h_toLp_meas.aemeasurable
  -- Bundle as `ProbabilityMeasure` for Lévy.
  let pn : ℕ → ProbabilityMeasure 𝕊L := fun n => ⟨(μ_n n).map toLp_fun, h_prob_n n⟩
  let pLim : ProbabilityMeasure 𝕊L := ⟨μ.map toLp_fun, h_prob_lim⟩
  -- The lifted measures converge weakly via Lévy.
  have h_lift_conv : Tendsto pn atTop (𝓝 pLim) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun ?_
    intro v
    set t : ℝ := (WithLp.ofLp v).1 with ht
    set h : EuclideanSpace ℝ (Fin m) := (WithLp.ofLp v).2 with hh
    -- Per-direction Lévy on ℝ, applied to `(t, h)`.
    haveI h_prob_proj_n : ∀ n, IsProbabilityMeasure
        ((μ_n n).map (proj (m := m) t h)) := fun n =>
      Measure.isProbabilityMeasure_map (measurable_proj (m := m) t h).aemeasurable
    haveI h_prob_proj_lim : IsProbabilityMeasure
        (μ.map (proj (m := m) t h)) :=
      Measure.isProbabilityMeasure_map (measurable_proj (m := m) t h).aemeasurable
    let qn : ℕ → ProbabilityMeasure ℝ := fun n =>
      ⟨(μ_n n).map (proj (m := m) t h), h_prob_proj_n n⟩
    let qLim : ProbabilityMeasure ℝ :=
      ⟨μ.map (proj (m := m) t h), h_prob_proj_lim⟩
    have h_proj_conv : Tendsto qn atTop (𝓝 qLim) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      change Tendsto (fun n => ∫ x, f x ∂((μ_n n).map (proj (m := m) t h))) _ _
      exact h_per_dir t h f
    -- Apply Lévy on ℝ.
    have h_charFun_conv :
        ∀ s : ℝ, Tendsto (fun n => charFun (qn n : Measure ℝ) s) atTop
                  (𝓝 (charFun (qLim : Measure ℝ) s)) :=
      fun s => (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h_proj_conv) s
    -- Bridge `charFun` on `𝕊L` and on ℝ.
    have h_bridge_n : ∀ n, charFun ((pn n : Measure 𝕊L)) v
        = charFun ((qn n : Measure ℝ)) 1 := fun n => by
      change charFun ((μ_n n).map toLp_fun) v
        = charFun ((μ_n n).map (proj (m := m) t h)) 1
      exact charFun_map_toLp_eq v
    have h_bridge_lim : charFun ((pLim : Measure 𝕊L)) v
        = charFun ((qLim : Measure ℝ)) 1 := by
      change charFun (μ.map toLp_fun) v
        = charFun (μ.map (proj (m := m) t h)) 1
      exact charFun_map_toLp_eq v
    rw [h_bridge_lim]
    simp_rw [h_bridge_n]
    exact h_charFun_conv 1
  -- Convert to `WeakConverges` on the inner-product side.
  have h_lift_weak :
      WeakConverges (fun n => (μ_n n).map toLp_fun) (μ.map toLp_fun) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h_lift_conv
    intro f
    exact h_lift_conv f
  -- Push back via `ofLp`.
  have h_ofLp_meas : Measurable (WithLp.ofLp : 𝕊L → 𝕊) := WithLp.measurable_ofLp _ _
  have h_ofLp_cont : Continuous (WithLp.ofLp : 𝕊L → 𝕊) :=
    WithLp.prod_continuous_ofLp _ _ _
  have h_pushed :=
    h_lift_weak.map (E := 𝕊L) (F := 𝕊) h_ofLp_cont h_ofLp_meas
  -- Simplify: `(μ.map toLp).map ofLp = μ`.
  have h_id_n : ∀ n, ((μ_n n).map toLp_fun).map (WithLp.ofLp : 𝕊L → 𝕊) = μ_n n := by
    intro n
    rw [Measure.map_map h_ofLp_meas h_toLp_meas]
    have h_id : (WithLp.ofLp : 𝕊L → 𝕊) ∘ toLp_fun = id := by
      funext x; simp [toLp_fun]
    rw [h_id, Measure.map_id]
  have h_id_lim : (μ.map toLp_fun).map (WithLp.ofLp : 𝕊L → 𝕊) = μ := by
    rw [Measure.map_map h_ofLp_meas h_toLp_meas]
    have h_id : (WithLp.ofLp : 𝕊L → 𝕊) ∘ toLp_fun = id := by
      funext x; simp [toLp_fun]
    rw [h_id, Measure.map_id]
  -- Substitute and conclude.
  intro f
  have h_f := h_pushed f
  simp only [h_id_n, h_id_lim] at h_f
  exact h_f

end CramerWold

/-- **Cramér–Wold device** for joint weak convergence on
`ℝ × EuclideanSpace ℝ (Fin m)`.

If, for every direction `(t, h) : ℝ × EuclideanSpace ℝ (Fin m)`, the
push-forward `(μ_n).map (fun p ↦ t * p.1 + ⟪h, p.2⟫_ℝ)` weakly converges
to `μ.map (fun p ↦ t * p.1 + ⟪h, p.2⟫_ℝ)`, then `μ_n` weakly converges to
`μ` jointly on `ℝ × EuclideanSpace ℝ (Fin m)`.

Proof: bridge to `WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))` via the
measurable homeomorphism `WithLp.toLp 2 _` and apply Mathlib's Lévy
continuity theorem. Pointwise `charFun` convergence on the inner-product
side reduces, via `WithLp.prod_inner_apply` and real-inner symmetry, to
per-direction `charFun` convergence on ℝ, which is the per-direction Lévy
criterion applied to the hypothesis. -/
theorem cramerWold_weakConverges
    {m : ℕ}
    {μ_n : ℕ → Measure (ℝ × EuclideanSpace ℝ (Fin m))}
    {μ : Measure (ℝ × EuclideanSpace ℝ (Fin m))}
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure μ]
    (h_per_dir : ∀ (t : ℝ) (h : EuclideanSpace ℝ (Fin m)),
      WeakConverges
        (fun n => (μ_n n).map (fun p => t * p.1 + ⟪h, p.2⟫_ℝ))
        (μ.map (fun p => t * p.1 + ⟪h, p.2⟫_ℝ))) :
    WeakConverges μ_n μ :=
  CramerWold.cramerWold_weakConverges_proj (m := m) (μ_n := μ_n) (μ := μ)
    (fun t h => h_per_dir t h)

end AsymptoticStatistics.ForMathlib
