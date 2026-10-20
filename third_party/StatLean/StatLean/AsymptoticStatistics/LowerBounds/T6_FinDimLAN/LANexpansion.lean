module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Core.TangentAbstract
public import StatLean.AsymptoticStatistics.ForMathlib.LogTaylor
public import StatLean.AsymptoticStatistics.ForMathlib.MeanVarConvergence
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.Abstract1DLAN
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# LAN expansion for finite-dimensional submodels

This file provides `lanExpansion_at_basis_and_h`, the LAN-remainder existence
result consumed by `finDimSubmodel_lan`.

For an `L²(P)`-orthonormal basis `g_P : Fin m → ↥(L2ZeroMean P)` of a
finite-dim subspace of the tangent set, and a QMDPath family
`γ : (Fin m → ℝ) → QMDPath P` whose score is `Σᵢ hᵢ · g_P i`, the LAN
remainder

```text
R_lan n X = (Σⱼ log(p_{1/√n}/p_0)(Xⱼ)) − (1/√n)·Σⱼ ⟨h', score1D(Xⱼ)⟩
            + (1/2)·I_{γ h}(h',h')
```

with `h' := EuclideanSpace.single 0 1`,
`p_t(x) := ((γ h).curve t).rnDeriv (γ h).dominating x`, and
`I_{γ h}` the Fisher information of the 1D `to1DParametricFamily (γ h)`,
satisfies

```text
∀ ε > 0, P^n {X | ε ≤ |R_lan n X|} → 0  as n → ∞.
```

## Strategy

The proof leverages `QMDPath.lanExpansion1D` applied to the 1-D path `γ h`.
Setup:

* **External sample space**: `Ω' := ℕ → Ω` with `P' := infinitePi (fun _ => P)`.
* **iid sequence**: `X i ω := ω i` (canonical projections), discharging
  `hindep` / `hident` / `hlaw` / `hX_meas` from the canonical infinite
  product structure (`ProbabilityTheory.iIndepFun_infinitePi` +
  `Measure.infinitePi_map_eval`).
* **1-D shift**: `h' := EuclideanSpace.single 0 1`, `h_n := fun _ => h'`.
  Then `(1/√n) • h_n n = (1/√n) • h'` enters the density at time
  `t = 1/√n`, matching the m-dim score-direction shift.

`lanExpansion1D` then gives `TendstoInMeasure (infinitePi P) (F n) atTop 0`
where `F n` is the same expression as `lanRemainder` below but
parameterised by `(ω i)` for `ω : ℕ → Ω`. Since `F n` depends only on
`(ω 0, …, ω (n-1))`, it factors through `truncate_n` as
`F n = lanRemainder _ _ _ n ∘ truncate_n`. The bridge
`pi_const_eq_infinitePi_map` + `tendstoInMeasure_of_tendstoInMeasure_comp`
transports `TendstoInMeasure (infinitePi P) F` to
`TendstoInMeasure P^n (lanRemainder _ _ _)`. Finally
`TendstoInMeasure` unfolds to the
`(P^n) {ε ≤ |lanRemainder _ _ _ n X|} → 0` form via direct manipulation
of `edist`.

The witness `R_lan` matches the book formula `R_n(γ h, X)` of
vdV §7.2 / §25.3, modulo the Fisher information naming on the
deterministic quadratic term.

Headline declarations: `lanRemainder`, `lanExpansion1D_to_PnProb_bridge`,
`lanExpansion_at_basis_and_h`.

Reference: vdV §7.2, §25.3.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## The LAN remainder

The 1-D LAN expansion delivered by
`QMDPath.lanExpansion1D` produces, for any path
`γ' : QMDPath P` and shift `h' ∈ EuclideanSpace ℝ (Fin 1)`, a quantity
that converges to `0` in `infinitePi P`-probability.

Specialising to `γ' := γ h` and `h' := EuclideanSpace.single 0 1`, this
becomes the book LAN remainder. We define
`lanRemainder g_P γ h n X` to be the `Fin n`-restriction of that
expression — definitionally equal to the `lanExpansion1D` output's
`F n` evaluated at any `ω : ℕ → Ω` extending `X`.
-/

/-- **The LAN remainder at a finite-dim score basis.**

Pointwise on `X : Fin n → Ω`:

```text
R_lan g_P γ h n X
  = (∑ⱼ : Fin n, log(p_{1/√n}/p_0)(X j))
    − (1/√n)·∑ⱼ : Fin n, ⟪h', score1D (γ h) (X j)⟫
    + (1/2)·I_{γ h}(h', h')
```

with `h' := EuclideanSpace.single (0 : Fin 1) 1`,
`p_t(ω) := ((γ h).curve t).rnDeriv (γ h).dominating ω` packaged as
`to1DParametricFamily (γ h)`, and `I_{γ h}` the Fisher information of
the 1-D parametric family at `θ = 0` w.r.t. the score `score1D (γ h)`.

This is precisely the function delivered by
`Abstract1DLAN.lanExpansion1D` on the `(γ h)`-derived 1-D parametric
family, restricted to `Fin n`-indexed samples. -/
noncomputable def lanRemainder
    {m : ℕ} (_g_P_unused : Fin m → ↥(L2ZeroMean P))
    (γ : (Fin m → ℝ) → QMDPath P) (h : Fin m → ℝ)
    (n : ℕ) (X : Fin n → Ω) : ℝ :=
  let h' : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  (∑ j : Fin n,
      Real.log
        ((QMDPath.to1DParametricFamily (γ h)).density
            (0 + (Real.sqrt n)⁻¹ • h') (X j) /
          (QMDPath.to1DParametricFamily (γ h)).density 0 (X j)))
    - (Real.sqrt n)⁻¹ * ∑ j : Fin n,
        @inner ℝ _ _ h' (QMDPath.score1D (γ h) (X j))
    + (1/2 : ℝ) *
      AsymptoticStatistics.fisherInformation
        (QMDPath.to1DParametricFamily (γ h)) (γ h).dominating 0
        (QMDPath.score1D (γ h)) h' h'

/-! ## Main theorem -/

/-- **Bridging lemma**: `Abstract1DLAN.lanExpansion1D` delivers
`TendstoInMeasure` on `infinitePi P`. The bridge to the
`P^n {ε ≤ |R_lan n X|} → 0` form factors through:

1. Construct the 1-D iid setup on `Ω' := ℕ → Ω` with
   `P' := infinitePi (fun _ => P)`, `X i ω := ω i`. Discharge `hindep`
   from `ProbabilityTheory.iIndepFun_infinitePi`; `hident` from
   `Measure.infinitePi_map_eval`; `hlaw` from `withDensity_rnDeriv_eq`
   applied to `(γ h).curve_at_zero` + `(γ h).curve_absContinuous 0`.
   `hℓ_meas` from `Lp.stronglyMeasurable` of the score, lifted through
   `EuclideanSpace.single`.

2. Apply `Abstract1DLAN.QMDPath.lanExpansion1D` to obtain
   `TendstoInMeasure (infinitePi P) (F n) atTop (fun _ => 0)`.

3. Observe `F n` factors through
   `truncate_n : (ℕ → Ω) → (Fin n → Ω)` as
   `F n = lanRemainder g_P γ h n ∘ truncate_n` (definitionally — both
   sides are `Fin n`-indexed sums of the same integrand).

4. Apply `AsymptoticStatistics.tendstoInMeasure_of_tendstoInMeasure_comp`
   with `φ = truncate_n` and `pi_const_eq_infinitePi_map` to get
   `TendstoInMeasure P^n (lanRemainder g_P γ h n) atTop (fun _ => 0)`.

5. Unfold `TendstoInMeasure` (the `edist` form on ℝ reduces to
   `|R_lan n X| ≥ ε` via `Real.edist_eq` + `ENNReal.ofReal_le_ofReal`). -/
theorem lanExpansion1D_to_PnProb_bridge
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (γ : (Fin m → ℝ) → QMDPath P)
    (hγ_score : ∀ h : Fin m → ℝ,
      (γ h).score = ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)))
    (h : Fin m → ℝ) :
    ∀ ε > 0,
      Tendsto (fun n : ℕ =>
        (MeasureTheory.Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ |lanRemainder g_P γ h n X|})
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  let _ := hγ_score
  -- Step 1: set up the canonical iid space `Ω' := ℕ → Ω`.
  set h' : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hh'_def
  set P' : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hP'_def
  haveI : IsProbabilityMeasure P' := by
    rw [hP'_def]; infer_instance
  set X : ℕ → (ℕ → Ω) → Ω := fun i ω => ω i with hX_def
  have hX_meas : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  -- Independence: from `iIndepFun_infinitePi` + `iIndepFun.indepFun`.
  have hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P' := by
    have h_iindep :
        ProbabilityTheory.iIndepFun (fun i ω => (id : Ω → Ω) (ω i))
          (Measure.infinitePi (fun _ : ℕ => P)) :=
      ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
    intro i j hij
    exact h_iindep.indepFun hij
  -- Identical distribution: `(X i).map P' = P` for all `i` (by `infinitePi_map_eval`),
  -- so all are identically distributed.
  have hX_map : ∀ i, Measure.map (X i) P' = P := by
    intro i
    rw [hX_def, hP'_def]
    exact MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => P) i
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P' P' := by
    intro i
    refine ⟨(hX_meas i).aemeasurable, (hX_meas 0).aemeasurable, ?_⟩
    rw [hX_map i, hX_map 0]
  -- Law of `X 0`: matches the `to1DParametricFamily (γ h)` density at `θ = 0`.
  have hlaw_target_eq :
      (γ h).dominating.withDensity
          (fun x => ENNReal.ofReal
            ((QMDPath.to1DParametricFamily (γ h)).density 0 x))
        = P := by
    -- Density at `θ = 0` is `((γ h).curve 0).rnDeriv (γ h).dominating ω |>.toReal`.
    -- Since `(γ h).curve 0 = P`, this is `(P.rnDeriv (γ h).dominating ω).toReal`.
    -- The `ENNReal.ofReal ∘ toReal` rewraps to `P.rnDeriv (γ h).dominating` a.e.
    -- (because rnDeriv is a.e. finite), and `withDensity_rnDeriv_eq` closes.
    haveI hac : P ≪ (γ h).dominating := by
      have := (γ h).curve_absContinuous 0
      rw [(γ h).curve_at_zero] at this
      exact this
    have h_density_eq : ∀ x,
        (QMDPath.to1DParametricFamily (γ h)).density 0 x
          = ((P.rnDeriv (γ h).dominating) x).toReal := by
      intro x
      change (((γ h).curve 0).rnDeriv (γ h).dominating x).toReal = _
      rw [(γ h).curve_at_zero]
    have h_ae_eq :
        (fun x => ENNReal.ofReal
            ((QMDPath.to1DParametricFamily (γ h)).density 0 x))
          =ᵐ[(γ h).dominating]
        (P.rnDeriv (γ h).dominating) := by
      filter_upwards [Measure.rnDeriv_lt_top P (γ h).dominating] with x hx
      rw [h_density_eq x, ENNReal.ofReal_toReal hx.ne]
    rw [MeasureTheory.withDensity_congr_ae h_ae_eq,
      Measure.withDensity_rnDeriv_eq P (γ h).dominating hac]
  have hlaw : Measure.map (X 0) P'
      = (γ h).dominating.withDensity
          (fun x => ENNReal.ofReal
            ((QMDPath.to1DParametricFamily (γ h)).density 0 x)) := by
    rw [hX_map 0]; exact hlaw_target_eq.symm
  -- Score measurability: `score1D γ ω = EuclideanSpace.single 0 (γ.score ω)`.
  -- `EuclideanSpace.single 0 : ℝ → EuclideanSpace ℝ (Fin 1)` is continuous
  -- (since `EuclideanSpace.single 0` is a continuous linear map).
  have hℓ_meas : Measurable (QMDPath.score1D (γ h)) := by
    have h_score_sm : StronglyMeasurable
        (fun ω => (((γ h).score : Lp ℝ 2 P) : Ω → ℝ) ω) :=
      Lp.stronglyMeasurable _
    have h_inner_meas : Measurable
        (fun ω => (((γ h).score : Lp ℝ 2 P) : Ω → ℝ) ω) :=
      h_score_sm.measurable
    -- `EuclideanSpace.single 0` is continuous as a composition.
    have h_single_cont :
        Continuous (fun a : ℝ => EuclideanSpace.single (0 : Fin 1) a) := by
      -- Continuity follows since `EuclideanSpace.single i` is a linear map between
      -- finite-dimensional spaces. Equivalently, view it through the CLE
      -- `PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 => ℝ)`.
      have h_pi_single :
          Continuous (fun a : ℝ => (Pi.single (0 : Fin 1) a : Fin 1 → ℝ)) := by
        refine continuous_pi (fun j => ?_)
        by_cases hj : j = 0
        · subst hj
          have : (fun a : ℝ => (Pi.single (0 : Fin 1) a : Fin 1 → ℝ) 0) = id := by
            funext a; simp
          rw [this]; exact continuous_id
        · have : (fun a : ℝ => (Pi.single (0 : Fin 1) a : Fin 1 → ℝ) j)
              = (fun _ : ℝ => (0 : ℝ)) := by
            funext a; simp [hj]
          rw [this]; exact continuous_const
      -- The `PiLp.continuousLinearEquiv 2 ℝ (·)` swaps `PiLp 2 _ ↔ ∀ i, _`;
      -- precomposing with `Pi.single 0` gives `EuclideanSpace.single 0`.
      have h_eq :
          (fun a : ℝ => EuclideanSpace.single (0 : Fin 1) a)
            = (fun y : Fin 1 → ℝ =>
                (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 => ℝ)).symm y)
              ∘ (fun a : ℝ => (Pi.single (0 : Fin 1) a : Fin 1 → ℝ)) := by
        funext a
        simp
      rw [h_eq]
      exact (PiLp.continuousLinearEquiv 2 ℝ
              (fun _ : Fin 1 => ℝ)).symm.continuous.comp h_pi_single
    exact h_single_cont.measurable.comp h_inner_meas
  -- Step 2: apply `Abstract1DLAN.QMDPath.lanExpansion1D` with `h_n := fun _ => h'`.
  have h_const_tendsto : Tendsto (fun _ : ℕ => h') atTop (𝓝 h') := tendsto_const_nhds
  have hLAN := AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.lanExpansion1D
    (γ h) h' (fun _ : ℕ => h') h_const_tendsto P' X hX_meas hindep hident hlaw hℓ_meas
  -- Step 3+4: `F n` factors as `lanRemainder (γ h) n ∘ truncate_n`.
  -- Set `F n ω := lanRemainder _ γ h n (fun j : Fin n => ω j.val)`.
  -- We show `F n ω = the lanExpansion1D output expression for sample (X i ω)_i`.
  -- The two differ only by `Finset.range n` vs `Finset.univ : Finset (Fin n)`,
  -- which we equate via `Fin.sum_univ_eq_sum_range`.
  set F : ℕ → (ℕ → Ω) → ℝ := fun n ω =>
    lanRemainder g_P γ h n (fun j : Fin n => ω j.val) with hF_def
  have hF_eq : ∀ n ω,
      F n ω
        = (∑ i ∈ Finset.range n,
            Real.log
              ((QMDPath.to1DParametricFamily (γ h)).density
                  (0 + (Real.sqrt n)⁻¹ • h') (X i ω) /
                (QMDPath.to1DParametricFamily (γ h)).density 0 (X i ω)))
          - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
              @inner ℝ _ _ h' (QMDPath.score1D (γ h) (X i ω))
          + (1/2 : ℝ) *
            AsymptoticStatistics.fisherInformation
              (QMDPath.to1DParametricFamily (γ h)) (γ h).dominating 0
              (QMDPath.score1D (γ h)) h' h' := by
    intro n ω
    change lanRemainder g_P γ h n (fun j : Fin n => ω j.val) = _
    unfold lanRemainder
    -- Reduce body via reindexing `∑ j : Fin n, f j.val = ∑ i ∈ Finset.range n, f i`.
    have h_log_reindex :
        (∑ j : Fin n,
            Real.log
              ((QMDPath.to1DParametricFamily (γ h)).density
                  (0 + (Real.sqrt n)⁻¹ • h') (ω j.val) /
                (QMDPath.to1DParametricFamily (γ h)).density 0 (ω j.val)))
          = ∑ i ∈ Finset.range n,
            Real.log
              ((QMDPath.to1DParametricFamily (γ h)).density
                  (0 + (Real.sqrt n)⁻¹ • h') (ω i) /
                (QMDPath.to1DParametricFamily (γ h)).density 0 (ω i)) :=
      Fin.sum_univ_eq_sum_range
        (fun i =>
          Real.log
            ((QMDPath.to1DParametricFamily (γ h)).density
                (0 + (Real.sqrt n)⁻¹ • h') (ω i) /
              (QMDPath.to1DParametricFamily (γ h)).density 0 (ω i))) n
    have h_inner_reindex :
        (∑ j : Fin n,
            @inner ℝ _ _ h' (QMDPath.score1D (γ h) (ω j.val)))
          = ∑ i ∈ Finset.range n,
            @inner ℝ _ _ h' (QMDPath.score1D (γ h) (ω i)) :=
      Fin.sum_univ_eq_sum_range
        (fun i => @inner ℝ _ _ h' (QMDPath.score1D (γ h) (ω i))) n
    -- Substitute the let-binding `h'` and apply reindexing.
    change (∑ j : Fin n,
            Real.log
              ((QMDPath.to1DParametricFamily (γ h)).density
                  (0 + (Real.sqrt n)⁻¹ • h') (ω j.val) /
                (QMDPath.to1DParametricFamily (γ h)).density 0 (ω j.val)))
          - (Real.sqrt n)⁻¹ * ∑ j : Fin n,
              @inner ℝ _ _ h' (QMDPath.score1D (γ h) (ω j.val))
          + (1/2 : ℝ) *
            AsymptoticStatistics.fisherInformation
              (QMDPath.to1DParametricFamily (γ h)) (γ h).dominating 0
              (QMDPath.score1D (γ h)) h' h' = _
    rw [h_log_reindex, h_inner_reindex]
  have hLAN' : TendstoInMeasure P' F atTop (fun _ => (0 : ℝ)) := by
    intro ε hε
    have hLAN_at_ε := hLAN ε hε
    -- Build pointwise set equality: replace the RHS expression by `F n ω`.
    have h_set_eq : ∀ n,
        {x | ε ≤ edist
          ((∑ i ∈ Finset.range n,
              Real.log
                ((QMDPath.to1DParametricFamily (γ h)).density
                    (0 + (Real.sqrt n)⁻¹ • h') (X i x) /
                  (QMDPath.to1DParametricFamily (γ h)).density 0 (X i x)))
            - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
                @inner ℝ _ _ h' (QMDPath.score1D (γ h) (X i x))
            + (1/2 : ℝ) *
              AsymptoticStatistics.fisherInformation
                (QMDPath.to1DParametricFamily (γ h)) (γ h).dominating 0
                (QMDPath.score1D (γ h)) h' h')
          ((fun _ => (0 : ℝ)) x)}
          = {x | ε ≤ edist (F n x) ((fun _ => (0 : ℝ)) x)} := by
      intro n; ext ω
      simp only [Set.mem_setOf_eq]
      rw [hF_eq n ω]
    have h_meas_pt : (fun n =>
        P' {x | ε ≤ edist
          ((∑ i ∈ Finset.range n,
              Real.log
                ((QMDPath.to1DParametricFamily (γ h)).density
                    (0 + (Real.sqrt n)⁻¹ • h') (X i x) /
                  (QMDPath.to1DParametricFamily (γ h)).density 0 (X i x)))
            - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
                @inner ℝ _ _ h' (QMDPath.score1D (γ h) (X i x))
            + (1/2 : ℝ) *
              AsymptoticStatistics.fisherInformation
                (QMDPath.to1DParametricFamily (γ h)) (γ h).dominating 0
                (QMDPath.score1D (γ h)) h' h')
          ((fun _ => (0 : ℝ)) x)})
        = (fun n => P' {x | ε ≤ edist (F n x) ((fun _ => (0 : ℝ)) x)}) := by
      funext n
      rw [h_set_eq n]
    -- The LAN form (via `lanExpansion1D`) uses `(fun x ↦ h') n = h'` constant in `n`.
    -- After this h_n β-reduces to h', so the two expressions match.
    have hLAN_simplified := hLAN_at_ε
    simp only at hLAN_simplified
    rw [show
        (fun n =>
          P' {x | ε ≤ edist (F n x) ((fun _ => (0 : ℝ)) x)})
          = _ from h_meas_pt.symm]
    exact hLAN_simplified
  -- Step 4: transport to `Measure.pi (fun _ : Fin n => P)`.
  -- F n ω = lanRemainder n (truncate ω); use `pi_const_eq_infinitePi_map`
  -- (encoded in `pi_meas_eq_infinitePi_meas_of_truncate`) per ε.
  -- Step 5: unfold TendstoInMeasure to the |R| ≥ ε form.
  intro ε hε
  have hLAN_ε := hLAN' (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  -- `edist (F n ω) 0 = ENNReal.ofReal |F n ω|` for real `F n ω`.
  -- So `{ω | ENNReal.ofReal ε ≤ edist (F n ω) 0} = {ω | ε ≤ |F n ω|}`.
  have hset_eq : ∀ n,
      {ω : ℕ → Ω | ENNReal.ofReal ε ≤ edist (F n ω) (0 : ℝ)}
        = {ω : ℕ → Ω | ε ≤ |F n ω|} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, edist_dist, Real.dist_eq, sub_zero]
    constructor
    · intro hle
      have habs_nn : (0 : ℝ) ≤ |F n ω| := abs_nonneg _
      exact (ENNReal.ofReal_le_ofReal_iff habs_nn).mp hle
    · intro hle
      exact ENNReal.ofReal_le_ofReal hle
  -- Now translate `P' {ω | ε ≤ |F n ω|}` to `P^n {X | ε ≤ |lanRemainder n X|}`
  -- via `pi_meas_eq_infinitePi_meas_of_truncate`.
  -- Need measurability of the predicate `{X : Fin n → Ω | ε ≤ |lanRemainder g_P γ h n X|}`.
  have h_measSet : ∀ n,
      MeasurableSet {X : Fin n → Ω | ε ≤ |lanRemainder g_P γ h n X|} := by
    intro n
    -- `lanRemainder g_P γ h n` is measurable: a finite combination of
    -- `Real.log`, divisions, multiplications, additions of measurable functions
    -- of `(X j)`-evaluations (and a constant `fisherInformation` term).
    have h_dens_meas : ∀ θ, Measurable
        (fun ω : Ω => (QMDPath.to1DParametricFamily (γ h)).density θ ω) :=
      fun θ => (QMDPath.to1DParametricFamily (γ h)).density_meas θ
    have h_proj : ∀ j : Fin n, Measurable (fun X : Fin n → Ω => X j) :=
      fun j => measurable_pi_apply j
    have h_log_term : Measurable
        (fun X : Fin n → Ω =>
          ∑ j : Fin n,
            Real.log
              ((QMDPath.to1DParametricFamily (γ h)).density
                  (0 + (Real.sqrt n)⁻¹ • h') (X j) /
                (QMDPath.to1DParametricFamily (γ h)).density 0 (X j))) := by
      refine Finset.measurable_sum _ (fun j _ => ?_)
      exact ((h_dens_meas _).comp (h_proj j)).div
              ((h_dens_meas _).comp (h_proj j)) |>.log
    have h_inner_term : Measurable
        (fun X : Fin n → Ω =>
          (Real.sqrt n)⁻¹ * ∑ j : Fin n,
            @inner ℝ _ _ h' (QMDPath.score1D (γ h) (X j))) := by
      refine Measurable.const_mul ?_ _
      refine Finset.measurable_sum _ (fun j _ => ?_)
      have h_score_proj : Measurable
          (fun X : Fin n → Ω => QMDPath.score1D (γ h) (X j)) :=
        hℓ_meas.comp (h_proj j)
      exact (continuous_const.inner continuous_id).measurable.comp h_score_proj
    have h_lan_meas : Measurable (lanRemainder g_P γ h n) := by
      change Measurable (fun X : Fin n → Ω =>
        (∑ j : Fin n,
          Real.log
            ((QMDPath.to1DParametricFamily (γ h)).density
                (0 + (Real.sqrt n)⁻¹ • h') (X j) /
              (QMDPath.to1DParametricFamily (γ h)).density 0 (X j)))
        - (Real.sqrt n)⁻¹ * ∑ j : Fin n,
            @inner ℝ _ _ h' (QMDPath.score1D (γ h) (X j))
        + (1/2 : ℝ) *
          AsymptoticStatistics.fisherInformation
            (QMDPath.to1DParametricFamily (γ h)) (γ h).dominating 0
            (QMDPath.score1D (γ h)) h' h')
      exact (h_log_term.sub h_inner_term).add measurable_const
    have h_abs_meas : Measurable (fun X : Fin n → Ω => |lanRemainder g_P γ h n X|) := by
      have hh : (fun X : Fin n → Ω => |lanRemainder g_P γ h n X|)
          = (fun X : Fin n → Ω =>
              max (lanRemainder g_P γ h n X) (-(lanRemainder g_P γ h n X))) := by
        funext X; exact abs_eq_max_neg
      rw [hh]
      exact h_lan_meas.max h_lan_meas.neg
    exact measurableSet_le measurable_const h_abs_meas
  -- Convert the `Measure.pi` measure to `infinitePi` measure on the truncate set.
  have h_meas_eq : ∀ n,
      (MeasureTheory.Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ |lanRemainder g_P γ h n X|}
        = P' {ω : ℕ → Ω | ε ≤ |F n ω|} := by
    intro n
    rw [hP'_def]
    have := AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate (P) n
      (h_measSet n)
    rw [this]
    rfl
  -- Push through.
  simp_rw [h_meas_eq]
  have h_obj_eq : (fun n : ℕ => P' {ω : ℕ → Ω | ε ≤ |F n ω|})
      = (fun n : ℕ => P' {ω : ℕ → Ω | ENNReal.ofReal ε ≤ edist (F n ω) (0 : ℝ)}) := by
    funext n
    rw [hset_eq n]
  rw [h_obj_eq]
  exact hLAN_ε

/-- **LAN remainder existence at a finite-dim orthonormal score basis.**

Given an `L²(P)`-orthonormal family `g_P : Fin m → ↥(L2ZeroMean P)` of
tangent directions and a QMDPath family `γ : (Fin m → ℝ) → QMDPath P`
along the score `Σᵢ hᵢ · g_P i` for each `h ∈ ℝᵐ`, there exists a
remainder process `R_lan : (n : ℕ) → (Fin n → Ω) → ℝ` such that for
every `ε > 0`,

```text
P^n {X : Fin n → Ω | ε ≤ |R_lan n X|} → 0  as n → ∞.
```

This discharges the `hLAN_expansion` hypothesis of `finDimSubmodel_lan`.

The witness is `lanRemainder g_P γ h`, the book formula matching
`QMDPath.lanExpansion1D`'s output (vdV §7.2 / §25.3). Convergence is
delegated to the named bridging lemma `lanExpansion1D_to_PnProb_bridge`,
which factors through `lanExpansion1D` applied to `γ h`, the canonical iid
setup on `infinitePi P`, and the `pi_const_eq_infinitePi_map` transport of
`TendstoInMeasure` along `truncate_n`.

Reference: vdV §7.2, §25.3. -/
theorem lanExpansion_at_basis_and_h
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (T_set : TangentSpec P)
    (hg_in_tangent : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (γ : (Fin m → ℝ) → QMDPath P)
    (hγ_score : ∀ h : Fin m → ℝ,
      (γ h).score = ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)))
    (h : Fin m → ℝ) :
    ∃ R_lan : (n : ℕ) → (Fin n → Ω) → ℝ,
      ∀ ε > 0,
        Tendsto (fun n : ℕ =>
          (MeasureTheory.Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε ≤ |R_lan n X|})
          atTop (𝓝 (0 : ℝ≥0∞)) := by
  -- These hypotheses are retained to match the finite-dimensional LAN interface;
  -- the bridge itself uses only `hγ_score`. Suppress unused-variable lint:
  let _ := h_orth; let _ := T_set; let _ := hg_in_tangent
  refine ⟨lanRemainder g_P γ h, ?_⟩
  exact lanExpansion1D_to_PnProb_bridge g_P γ hγ_score h

end AsymptoticStatistics.LowerBounds.T6_FinDimLAN
