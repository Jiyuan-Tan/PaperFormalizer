module
public import StatLean.AsymptoticStatistics.ForMathlib.PiGaussian
public import StatLean.AsymptoticStatistics.ForMathlib.PortmanteauLscBridge
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.LocallyConvex.Separation

public import Mathlib.Probability.Distributions.Gaussian.CharFun

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-!
Asymptotic Statistics — Weak limits of multivariate Gaussians.

Two measure-theoretic facts not supplied by the imported API are proved here as
named theorems, allowing the Anderson chain (`ForMathlib/Anderson.lean`) to keep its public
interface in vdV-canonical `S.PosSemidef` form (instead of strengthening to
`S.PosDef`):

* `multivariateGaussian_weakly_tendsto_of_psd_perturb` — weak convergence under
  PSD perturbation `S → S + ε•I` as `ε → 0⁺`, via Lévy's continuity theorem
  (Mathlib has the sequential form, plus first-countability bridges arbitrary
  index filters).

* `multivariateGaussian_frontier_eq_zero_of_convex` — convex Borel sets
  containing `0` in their interior are continuity sets for any PSD
  multivariate Gaussian. Two cases:
    - `S.PosDef`: Gaussian is AC w.r.t. Lebesgue (volume), and `Convex.addHaar_frontier`
      gives `volume (frontier C) = 0` ⇒ Gaussian-null by AC.
    - `S.PosSemidef` singular: Gaussian is supported on `range (sqrt S)`; the
      boundary intersects this lower-dim subspace in a convex-set boundary,
      null in intrinsic Lebesgue measure after passing to orthonormal coordinates
      on the support subspace.

The wrapper `multivariateGaussian_tendsto_at_convex` (consumed by
`anderson_lemma_set`) is proved from these two via Mathlib's Portmanteau
theorem `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal MatrixOrder

namespace AsymptoticStatistics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Multivariate Gaussian as a bundled `ProbabilityMeasure`.**

`multivariateGaussian μ S` is always `IsProbabilityMeasure` (`IsGaussian`-derived
when `S` is PSD; `Measure.dirac μ` otherwise — also probability), so the
subtype injection lifts to any `ι, μ, S` without preconditions. -/
noncomputable def multivariateGaussianPM (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ ι) :=
  ⟨multivariateGaussian μ S, inferInstance⟩

@[simp] lemma multivariateGaussianPM_toMeasure
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    (multivariateGaussianPM μ S : Measure (EuclideanSpace ℝ ι))
      = multivariateGaussian μ S := rfl

/-- **Weak continuity of `multivariateGaussian` under PSD perturbation.**

For `S.PosSemidef`, the family `ε ↦ multivariateGaussian 0 (S + ε•I)` weakly
converges to `multivariateGaussian 0 S` as `ε → 0⁺`.

**Proof.**
1. By `Filter.tendsto_iff_seq_tendsto` (`𝓝[>] 0` is countably generated, since
   ℝ is first-countable), it suffices to check sequential weak convergence: for
   any `ε_n → 0⁺`, the sequence of measures converges weakly.
2. Apply `ProbabilityMeasure.tendsto_of_tendsto_charFun` (Mathlib's Lévy
   continuity, sequential form): pointwise `charFun` convergence ⇒ weak
   convergence.
3. Pointwise charFun convergence: by `charFun_multivariateGaussian` (PSD case),
   `charFun (multivariateGaussian 0 M) t = exp(-t⬝Mt/2)`. Both `S` and
   `S + ε_n•I` are PSD (eventually for `ε_n > 0`), so
   `charFun (multivariateGaussian 0 (S + ε_n•I)) t = exp(-t⬝(S + ε_n•I)t/2)`,
   `= exp(-t⬝St/2 - ε_n‖t‖²/2)`,
   `→ exp(-t⬝St/2) = charFun (multivariateGaussian 0 S) t`
   as `ε_n → 0⁺`, by continuity of the linear-in-ε exponent.

This is proved via Mathlib's sequential Lévy theorem
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`), bridged to a non-sequential
filter via `Filter.tendsto_iff_seq_tendsto`. -/
lemma multivariateGaussian_weakly_tendsto_of_psd_perturb
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    Tendsto (fun ε : ℝ => multivariateGaussianPM (0 : EuclideanSpace ℝ ι)
        (S + ε • (1 : Matrix ι ι ℝ)))
      (𝓝[>] 0) (𝓝 (multivariateGaussianPM 0 S)) := by
  haveI : (𝓝[>] (0 : ℝ)).IsCountablyGenerated :=
    TopologicalSpace.isCountablyGenerated_nhdsWithin 0 _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro ε_seq h_ε_seq
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro x
  -- The PSD-formula RHS of `charFun_multivariateGaussian` (at μ = 0):
  -- a continuous function of the matrix M, agreeing with `charFun` whenever M is PSD.
  -- Parenthesize `-(↑a / 2)` to match `0 - ↑a / 2` after `zero_sub` normalization.
  set rhs : Matrix ι ι ℝ → ℂ := fun M =>
    Complex.exp (-(↑(x.ofLp ⬝ᵥ M.mulVec x.ofLp) / 2)) with hrhs_def
  -- Eventually ε_seq n > 0 ⇒ S + ε_seq n • I is PosDef ⇒ PSD ⇒ formula holds.
  have h_pos : ∀ᶠ n in atTop, (0 : ℝ) < ε_seq n :=
    h_ε_seq.eventually self_mem_nhdsWithin
  have h_lhs_eq : ∀ᶠ n in atTop,
      MeasureTheory.charFun ((multivariateGaussianPM (0 : EuclideanSpace ℝ ι)
        (S + ε_seq n • (1 : Matrix ι ι ℝ))) : Measure _) x
      = rhs (S + ε_seq n • (1 : Matrix ι ι ℝ)) := by
    filter_upwards [h_pos] with n hε
    have h_psd : (S + ε_seq n • (1 : Matrix ι ι ℝ)).PosSemidef :=
      (Matrix.PosDef.posSemidef_add hS (Matrix.PosDef.one.smul hε)).posSemidef
    change MeasureTheory.charFun (multivariateGaussian _ _) x = _
    rw [charFun_multivariateGaussian h_psd]
    simp [hrhs_def, inner_zero_right]
  have h_rhs_eq : MeasureTheory.charFun
      ((multivariateGaussianPM (0 : EuclideanSpace ℝ ι) S) : Measure _) x = rhs S := by
    change MeasureTheory.charFun (multivariateGaussian _ _) x = _
    rw [charFun_multivariateGaussian hS]
    simp [hrhs_def, inner_zero_right]
  rw [h_rhs_eq]
  -- Convert `f =ᶠ g` (LHS=RHS) to `g =ᶠ f` for `Tendsto.congr'`:
  have h_lhs_eq_symm :
      (fun n => rhs (S + ε_seq n • (1 : Matrix ι ι ℝ))) =ᶠ[atTop]
        fun n => MeasureTheory.charFun ((multivariateGaussianPM (0 : EuclideanSpace ℝ ι)
          (S + ε_seq n • (1 : Matrix ι ι ℝ))) : Measure _) x := by
    filter_upwards [h_lhs_eq] with n h
    exact h.symm
  refine Tendsto.congr' h_lhs_eq_symm ?_
  -- Reduce to continuity in ε of `rhs (S + ε • 1)` at ε = 0.
  have h_to_zero : Tendsto ε_seq atTop (𝓝 (0 : ℝ)) :=
    h_ε_seq.mono_right nhdsWithin_le_nhds
  -- The exponent is `(x ⬝ S x) + ε * (x ⬝ x)`, polynomial in ε:
  have h_exp_eq : ∀ ε : ℝ,
      x.ofLp ⬝ᵥ (S + ε • (1 : Matrix ι ι ℝ)).mulVec x.ofLp
        = x.ofLp ⬝ᵥ S.mulVec x.ofLp + ε * (x.ofLp ⬝ᵥ x.ofLp) := by
    intro ε
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
  have h_cont : Continuous (fun ε : ℝ => rhs (S + ε • (1 : Matrix ι ι ℝ))) := by
    simp only [hrhs_def, h_exp_eq]
    refine Complex.continuous_exp.comp ?_
    refine (Continuous.div_const ?_ 2).neg
    refine Complex.continuous_ofReal.comp ?_
    exact continuous_const.add (continuous_id.mul continuous_const)
  have h_at_zero : rhs S = rhs (S + (0 : ℝ) • (1 : Matrix ι ι ℝ)) := by
    simp [hrhs_def]
  rw [h_at_zero]
  exact (h_cont.tendsto 0).comp h_to_zero

/-! ## Weak continuity of `multivariateGaussian` along sequences (general form)

A more flexible weak-continuity helper: if a sequence of matrices converges
entrywise (e.g. via `Tendsto` in the entry topology, equivalently
`Pi`-convergence) to a PSD matrix, and each matrix in the sequence is PSD,
then the corresponding multivariate Gaussians converge weakly. This
generalizes `_of_psd_perturb` from the specific `S + ε•I` parametrization
to arbitrary tendsto-converging matrix families. -/

/-- **Weak continuity of `multivariateGaussian` along matrix sequences (PSD)**.

For a sequence of PSD matrices `S_n → S` entrywise (with `S` itself PSD),
`multivariateGaussianPM 0 S_n → multivariateGaussianPM 0 S` weakly.

**Proof sketch**: parallels `_of_psd_perturb`.
1. Apply `ProbabilityMeasure.tendsto_of_tendsto_charFun` (Mathlib's
   sequential Lévy).
2. For each test point `x`, show pointwise `charFun (mvg 0 S_n) x →
   charFun (mvg 0 S) x`.
3. Use `charFun_multivariateGaussian` on both sides (each PSD), reducing to
   `exp(-x ⬝ S_n x / 2) → exp(-x ⬝ S x / 2)`.
4. `S_n → S` entrywise + bilinear-form continuity ⇒ `x ⬝ S_n x → x ⬝ S x`.
   Continuous exp closes.

**Proof**: parallels `_of_psd_perturb`. Apply Mathlib's sequential Lévy
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`); for each test point `x`,
charFun reduces (via `charFun_multivariateGaussian` for PSD) to
`exp(-x⬝Mx/2)`. Continuity of the bilinear form `M ↦ x⬝Mx` (via
`Continuous.matrix_mulVec` + `Continuous.dotProduct`) plus continuous `exp`
gives charFun pointwise convergence; Lévy closes. -/
lemma multivariateGaussian_weakly_tendsto_of_seq
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {S_seq : ℕ → Matrix ι ι ℝ}
    (hS_seq_psd : ∀ᶠ n in atTop, (S_seq n).PosSemidef)
    (h_tend : Tendsto S_seq atTop (𝓝 S)) :
    Tendsto (fun n => multivariateGaussianPM (0 : EuclideanSpace ℝ ι) (S_seq n))
      atTop (𝓝 (multivariateGaussianPM 0 S)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro x
  set rhs : Matrix ι ι ℝ → ℂ := fun M =>
    Complex.exp (-(↑(x.ofLp ⬝ᵥ M.mulVec x.ofLp) / 2)) with hrhs_def
  -- Eventually `S_seq n` is PSD ⇒ `charFun (mvg 0 (S_seq n)) x = rhs (S_seq n)`.
  have h_lhs_eq : ∀ᶠ n in atTop,
      MeasureTheory.charFun ((multivariateGaussianPM (0 : EuclideanSpace ℝ ι)
        (S_seq n)) : Measure _) x = rhs (S_seq n) := by
    filter_upwards [hS_seq_psd] with n h_psd
    change MeasureTheory.charFun (multivariateGaussian _ _) x = _
    rw [charFun_multivariateGaussian h_psd]
    simp [hrhs_def, inner_zero_right]
  have h_rhs_eq : MeasureTheory.charFun
      ((multivariateGaussianPM (0 : EuclideanSpace ℝ ι) S) : Measure _) x = rhs S := by
    change MeasureTheory.charFun (multivariateGaussian _ _) x = _
    rw [charFun_multivariateGaussian hS]
    simp [hrhs_def, inner_zero_right]
  rw [h_rhs_eq]
  -- Convert `f =ᶠ g` to `g =ᶠ f` for `Tendsto.congr'`.
  have h_lhs_eq_symm :
      (fun n => rhs (S_seq n)) =ᶠ[atTop]
        fun n => MeasureTheory.charFun ((multivariateGaussianPM (0 : EuclideanSpace ℝ ι)
          (S_seq n)) : Measure _) x := by
    filter_upwards [h_lhs_eq] with n h
    exact h.symm
  refine Tendsto.congr' h_lhs_eq_symm ?_
  -- Continuity of `rhs` in `M`, plus `S_seq → S`.
  have h_cont : Continuous (fun M : Matrix ι ι ℝ => rhs M) := by
    refine Complex.continuous_exp.comp ?_
    refine (Continuous.div_const ?_ 2).neg
    refine Complex.continuous_ofReal.comp ?_
    exact Continuous.dotProduct continuous_const
      (Continuous.matrix_mulVec continuous_id continuous_const)
  exact (h_cont.tendsto S).comp h_tend

/-- **Lower-semicontinuous portmanteau for converging Gaussians.**

If `S_seq m → S` (all PSD, `S` PSD) and `L_M` is a nonnegative lower-semicontinuous
function, then the integral against the limiting centered Gaussian is bounded by
the `liminf` of the integrals against the approximating Gaussians. This is the lsc
direction of the portmanteau theorem specialized to the weakly-convergent Gaussian
sequence `multivariateGaussian 0 (S_seq m) → multivariateGaussian 0 S`
(`multivariateGaussian_weakly_tendsto_of_seq`).

**Proof**: weak convergence gives, via Mathlib's `le_liminf_measure_open_of_tendsto`,
the open-set portmanteau bound `μ G ≤ liminf (μs · G)`; feed this to the lsc bridge
`lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure`.
The only friction is the `ProbabilityMeasure` ↔ `Measure` coercion, dispatched by
`multivariateGaussianPM_toMeasure`. -/
theorem multivariateGaussian_lintegral_le_liminf_of_tendsto
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {S_seq : ℕ → Matrix ι ι ℝ}
    (h_psd : ∀ m, (S_seq m).PosSemidef)
    (h_tend : Tendsto S_seq atTop (𝓝 S))
    {L_M : EuclideanSpace ℝ ι → ℝ≥0∞}
    (hL_lsc : LowerSemicontinuous L_M) :
    ∫⁻ y, L_M y ∂(multivariateGaussian 0 S)
      ≤ Filter.liminf (fun m => ∫⁻ y, L_M y ∂(multivariateGaussian 0 (S_seq m))) atTop := by
  have h_weak := multivariateGaussian_weakly_tendsto_of_seq hS
    (Filter.Eventually.of_forall h_psd) h_tend
  refine lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure
    (μ := (multivariateGaussian 0 S : Measure (EuclideanSpace ℝ ι)))
    (μs := fun m => (multivariateGaussian 0 (S_seq m) : Measure (EuclideanSpace ℝ ι)))
    hL_lsc ?_
  intro G hG
  have h_open := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h_weak hG
  simpa only [multivariateGaussianPM_toMeasure] using h_open

/-! ## Convex-set null boundary under PSD Gaussian

Sub-helper (ii) of the wrapper. Decomposed into the natural PosDef vs
singular-PSD case split. The PSD-form lemma itself becomes a pure
case-split shell. -/

/-- **Centered multivariate Gaussian with zero covariance is `Dirac 0`**.

`multivariateGaussian 0 (0 : Matrix ι ι ℝ) = Measure.dirac 0`.

Used both by `_singularPsd` (`S = 0` branch) and by `anderson_lemma_set`
(degenerate covariance branch). The `multivariateGaussian` definition
unfolds: with `μ = 0` and `S = 0`, the affine pushforward
`stdGaussian.map (μ + toEuclideanCLM (sqrt S))` collapses to
`stdGaussian.map (fun _ ↦ 0)`, which equals `Dirac 0` via `Measure.map_const`
plus the probability-measure normalization. -/
lemma multivariateGaussian_zero_cov :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) (0 : Matrix ι ι ℝ)
      = Measure.dirac (0 : EuclideanSpace ℝ ι) := by
  rw [multivariateGaussian, CFC.sqrt_zero, map_zero]
  simp only [zero_add, ContinuousLinearMap.zero_apply]
  rw [Measure.map_const, measure_univ, one_smul]

/-- **`multivariateGaussian 0 S` is supported on `range (toEuclideanCLM (sqrt S))`**.

Direct unfolding of `multivariateGaussian 0 S = stdGaussian.map T` (with
`T x = 0 + toEuclideanCLM (CFC.sqrt S) x`): the pushforward of any measure
under `T` lives on `range T`. Used by `_singularPsd` (`S ≠ 0` branch) to
reduce the frontier-null claim to a question on the support subspace. -/
lemma multivariateGaussian_apply_compl_range
    (S : Matrix ι ι ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) S
        ((LinearMap.range
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).toLinearMap :
            Submodule ℝ _) : Set _)ᶜ = 0 := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  set V : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.range T.toLinearMap with hV_def
  have h_range_closed : IsClosed (V : Set (EuclideanSpace ℝ ι)) :=
    Submodule.closed_of_finiteDimensional V
  have h_meas_preimage : MeasurableSet ((V : Set (EuclideanSpace ℝ ι))ᶜ) :=
    h_range_closed.measurableSet.compl
  rw [multivariateGaussian]
  rw [show (fun x : EuclideanSpace ℝ ι => (0 : EuclideanSpace ℝ ι) + T x) = T from
    funext fun x => zero_add (T x)]
  rw [Measure.map_apply T.continuous.measurable h_meas_preimage]
  -- `T ⁻¹' Vᶜ = ∅`: every `T x` lies in `range T = V`.
  have h_empty : (T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) ⁻¹' ((V : Set _)ᶜ) = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe,
      hV_def, LinearMap.mem_range, Set.mem_empty_iff_false, iff_false, not_not]
    exact ⟨x, rfl⟩
  rw [h_empty, measure_empty]

omit [DecidableEq ι] in
/-- **Standard Gaussian on `EuclideanSpace` is absolutely continuous w.r.t. Lebesgue**.

Reusable AC fact: `stdGaussian (EuclideanSpace ℝ ι) ≪ volume`. Proof chain:
* `stdGaussian = (Measure.pi (gaussianReal 0 1)).map (WithLp.toLp 2)` (Mathlib
  `map_pi_eq_stdGaussian`).
* `Measure.pi (gaussianReal 0 1) = (volume on ι → ℝ).withDensity ρ` where
  `ρ x = ∏ i, gaussianPDF 0 1 (x i)` (`pi_gaussianReal_eq_withDensity`).
* `volume.withDensity ρ ≪ volume` (`MeasureTheory.withDensity_absolutelyContinuous`).
* Push along the volume-preserving `WithLp.toLp 2`
  (`PiLp.volume_preserving_toLp`). -/
lemma stdGaussian_absolutelyContinuous_volume :
    (stdGaussian (EuclideanSpace ℝ ι)).AbsolutelyContinuous
      (volume : Measure (EuclideanSpace ℝ ι)) := by
  have h_toLp_preserve : MeasurePreserving (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      (volume : Measure (ι → ℝ)) (volume : Measure (EuclideanSpace ℝ ι)) :=
    PiLp.volume_preserving_toLp ι
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity]
  have h_density_ac : ((volume : Measure (ι → ℝ)).withDensity
        (fun x : ι → ℝ => ∏ i, gaussianPDF 0 1 (x i))).AbsolutelyContinuous
      (volume : Measure (ι → ℝ)) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_pushed := h_density_ac.map h_toLp_preserve.measurable
  rwa [h_toLp_preserve.map_eq] at h_pushed

/-- **Centered PosDef multivariate Gaussian is absolutely continuous w.r.t. Lebesgue**.

For `S.PosDef`, `multivariateGaussian 0 S ≪ volume`. AC chain:
1. `multivariateGaussian 0 S = stdGaussian.map T_cle` where
   `T_cle = toEuclideanCLM (CFC.sqrt S)` is a `ContinuousLinearEquiv` because
   `CFC.sqrt S` is PosDef hence invertible (`Matrix.PosDef.posDef_sqrt`).
2. `stdGaussian ≪ volume` (`stdGaussian_absolutelyContinuous_volume`).
3. `volume.map T_cle` is `IsAddHaarMeasure` (`ContinuousLinearEquiv.isAddHaarMeasure_map`).
4. Any sigma-finite left-invariant measure is AC w.r.t. any Haar measure
   on a sigma-compact, locally compact, second-countable group
   (`Measure.absolutelyContinuous_isAddHaarMeasure`).
5. Compose: `mvg 0 S = stdGaussian.map T_cle ≪ volume.map T_cle ≪ volume`. -/
lemma multivariateGaussian_absolutelyContinuous_volume_of_posDef
    {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).AbsolutelyContinuous
      (volume : Measure (EuclideanSpace ℝ ι)) := by
  -- Step 1: Build the CLE `T_cle := toEuclideanCLM (CFC.sqrt S)` from PosDef.
  have h_sqrt_unit : IsUnit (CFC.sqrt S) := hS.isStrictlyPositive.sqrt.isUnit
  have h_T_unit : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) :=
    (MulEquiv.isUnit_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι))).mpr h_sqrt_unit
  let T_cle : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
    ContinuousLinearEquiv.ofUnit h_T_unit.unit
  have h_T_meas : Measurable (T_cle : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
    T_cle.toContinuousLinearMap.continuous.measurable
  -- Step 2: `multivariateGaussian 0 S = stdGaussian.map T_cle`.
  have h_mvg : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map T_cle := by
    rw [multivariateGaussian]
    congr 1
    funext x
    rw [zero_add]
    rfl
  -- Step 3: Pushforward of Haar volume under CLE is Haar (= scalar multiple).
  haveI h_map_haar : ((volume : Measure (EuclideanSpace ℝ ι)).map T_cle).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map T_cle (volume : Measure (EuclideanSpace ℝ ι))
  haveI : SigmaFinite ((volume : Measure (EuclideanSpace ℝ ι)).map T_cle) :=
    MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite _
  -- Step 4: Two Haar measures on the same group are mutually AC.
  have h_volmap_ac : ((volume : Measure (EuclideanSpace ℝ ι)).map T_cle).AbsolutelyContinuous
      (volume : Measure (EuclideanSpace ℝ ι)) :=
    MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _
  -- Step 5: Compose AC chain.
  rw [h_mvg]
  exact (stdGaussian_absolutelyContinuous_volume.map h_T_meas).trans h_volmap_ac

/-- **Convex sets are continuity sets for positive-definite multivariate Gaussians.**

For `S.PosDef` and convex `C`, the boundary `frontier C` has zero
`multivariateGaussian 0 S`-measure.

**Proof**: AC chain through `multivariateGaussian_absolutelyContinuous_volume_of_posDef`
+ `Convex.addHaar_frontier` (which gives `volume (frontier C) = 0`). -/
lemma multivariateGaussian_frontier_eq_zero_of_convex_posDef
    {S : Matrix ι ι ℝ} (hS : S.PosDef)
    {C : Set (EuclideanSpace ℝ ι)} (hC_conv : Convex ℝ C) :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) S (frontier C) = 0 :=
  (multivariateGaussian_absolutelyContinuous_volume_of_posDef hS)
    (Convex.addHaar_frontier _ hC_conv)

omit [DecidableEq ι] in
/-- **Convex line trick + Hahn-Banach: ambient frontier ∩ V ⊆ V-frontier of V-pullback**.

For convex `C ⊆ EuclideanSpace ℝ ι` with `0 ∈ interior C` and any submodule
`V`, the ambient `frontier C` pulled back along `V.subtypeL` lies in the
V-intrinsic frontier of `V.subtypeL ⁻¹' C`. (Equivalently — taking images under
`V.subtypeL` — `frontier C ∩ V ⊆ V.subtypeL '' frontier (V.subtypeL ⁻¹' C)`.)

**Why `0 ∈ interior C` is required**: in `ℝ²` with `V = x-axis` and
`C = closed upper half-plane`, the ambient `frontier C = V`, so the LHS pulled
back is all of `↥V`; but `V.subtypeL ⁻¹' C = V` has empty `↥V`-frontier (it's
the whole space). The hypothesis fails: `0 ∈ frontier C`, not `interior C`.

**Proof**:
* (Closure side) Open segment from `↑v ∈ closure C` to `0 ∈ interior C` lies in
  `interior C` (`Convex.openSegment_interior_closure_subset_interior`); each
  segment point `θ • v` is in `↥V` (subspace), so `θ • v ∈ V.subtypeL ⁻¹' C`
  for `θ ∈ (0,1)`. Letting `θ ↑ 1` gives `v ∈ closure (V.subtypeL ⁻¹' C)`.
* (Not-interior side) Suppose `v ∈ interior (V.subtypeL ⁻¹' C)`: `∃ ε > 0,
  Metric.ball v ε ⊆ V.subtypeL ⁻¹' C`. Apply `geometric_hahn_banach_open_point`
  to `interior C` (open convex by `Convex.interior`) and `↑v` (`∉ interior C`
  since `↑v ∈ frontier C`): get `g : E →L[ℝ] ℝ` with `g a < g(↑v)` on
  `interior C`. At `a = 0 ∈ interior C`: `g(↑v) > 0`. By continuity +
  `closure_interior_eq_closure_of_nonempty_interior`: `g a ≤ g(↑v)` on `C`.
  For `w : ↥V \ {0}`, `↑v ± t • ↑w ∈ C` for small `t > 0` (ball bound), so
  `±t • g(↑w) ≤ 0`, forcing `g(↑w) = 0`. Hence `g(↑v) = 0`, contradicting
  `g(↑v) > 0`. -/
private lemma _convex_subspace_frontier_pullback_subset
    {C : Set (EuclideanSpace ℝ ι)} (hC_conv : Convex ℝ C)
    (hC_int : (0 : EuclideanSpace ℝ ι) ∈ interior C)
    (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    V.subtypeL ⁻¹' frontier C ⊆ frontier (V.subtypeL ⁻¹' C) := by
  intro v hv
  have hv_cl : (v : EuclideanSpace ℝ ι) ∈ closure C := hv.1
  have hv_not_int : (v : EuclideanSpace ℝ ι) ∉ interior C := hv.2
  refine ⟨?_, ?_⟩
  · -- (Closure side) Sequence (1 - 1/(n+2)) • v ∈ V.subtypeL ⁻¹' C tends to v.
    -- Shift to `n + 2` so `1/(n+2) ∈ (0, 1)` always (avoids `n = 0` boundary).
    let θ : ℕ → ℝ := fun n => (1 : ℝ) - 1 / ((n : ℝ) + 2)
    have h_one_div : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
        Filter.atTop (𝓝 0) := by
      have h_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop := by
        have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop
        exact h1.atTop_add tendsto_const_nhds
      have h := tendsto_const_nhds.div_atTop (a := (1 : ℝ)) h_atTop
      simpa using h
    have h_one_div_pos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 2) := fun n => by positivity
    have h_one_div_lt_one : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) < 1 := fun n => by
      have h_npos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      rw [div_lt_iff₀ h_npos, one_mul]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hθ_pos : ∀ n, 0 < θ n := fun n => sub_pos.mpr (h_one_div_lt_one n)
    have hθ_lt_one : ∀ n, θ n < 1 := fun n => sub_lt_self _ (h_one_div_pos n)
    have hθ_tendsto : Filter.Tendsto θ Filter.atTop (𝓝 (1 : ℝ)) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop)).sub h_one_div
      simp only [sub_zero] at h
      exact h
    have h_f_tendsto : Filter.Tendsto (fun n : ℕ => θ n • v) Filter.atTop (𝓝 v) := by
      simpa using hθ_tendsto.smul_const v
    have h_f_in_pred : ∀ n : ℕ, θ n • v ∈ V.subtypeL ⁻¹' C := by
      intro n
      simp only [Set.mem_preimage, Submodule.subtypeL_apply, SetLike.val_smul]
      apply interior_subset
      apply hC_conv.openSegment_interior_closure_subset_interior hC_int hv_cl
      refine ⟨1 - θ n, θ n, by linarith [hθ_lt_one n], hθ_pos n, by ring, ?_⟩
      simp
    exact mem_closure_of_tendsto h_f_tendsto (Filter.Eventually.of_forall h_f_in_pred)
  · -- (Not-interior side) Hahn-Banach + g vanishes on V (via ±t•w trick).
    intro h_int
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h_int
    obtain ⟨ε, hε, h_ball_sub⟩ := h_int
    obtain ⟨g, hg⟩ :=
      geometric_hahn_banach_open_point hC_conv.interior isOpen_interior hv_not_int
    have h_g_v_pos : 0 < g (↑v : EuclideanSpace ℝ ι) := by
      have h := hg 0 hC_int; simpa using h
    have h_le_on_C : ∀ a ∈ C, g a ≤ g (↑v : EuclideanSpace ℝ ι) := by
      intro a haC
      have h_a_cli : a ∈ closure (interior C) := by
        rw [hC_conv.closure_interior_eq_closure_of_nonempty_interior ⟨0, hC_int⟩]
        exact subset_closure haC
      exact (isClosed_le g.continuous continuous_const).closure_subset_iff.mpr
        (fun a' ha' => (hg a' ha').le) h_a_cli
    have h_g_zero_on_V : ∀ w : ↥V, g (↑w : EuclideanSpace ℝ ι) = 0 := by
      intro w
      by_cases hw_zero : (w : EuclideanSpace ℝ ι) = 0
      · simp [hw_zero, map_zero]
      · have h_w_norm_pos : 0 < ‖(w : EuclideanSpace ℝ ι)‖ := norm_pos_iff.mpr hw_zero
        let t : ℝ := ε / (2 * ‖(w : EuclideanSpace ℝ ι)‖)
        have ht_pos : 0 < t := div_pos hε (by positivity)
        have h_eq_t : t * ‖(w : EuclideanSpace ℝ ι)‖ = ε / 2 := by
          change ε / (2 * ‖(w : EuclideanSpace ℝ ι)‖) * ‖(w : EuclideanSpace ℝ ι)‖ = ε / 2
          field_simp
        have ht_lt : t * ‖(w : EuclideanSpace ℝ ι)‖ < ε := by
          rw [h_eq_t]; linarith
        have h_norm_in_V : ‖(t • w : ↥V)‖ = t * ‖(w : EuclideanSpace ℝ ι)‖ := by
          change ‖t • (w : EuclideanSpace ℝ ι)‖ = t * ‖(w : EuclideanSpace ℝ ι)‖
          rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
        have h_ball_pos : v + t • w ∈ Metric.ball v ε := by
          rw [Metric.mem_ball]
          calc dist (v + t • w) v
              = ‖(v + t • w) - v‖ := dist_eq_norm _ _
            _ = ‖(t • w : ↥V)‖ := by rw [add_sub_cancel_left]
            _ = t * ‖(w : EuclideanSpace ℝ ι)‖ := h_norm_in_V
            _ < ε := ht_lt
        have h_ball_neg : v - t • w ∈ Metric.ball v ε := by
          rw [Metric.mem_ball]
          calc dist (v - t • w) v
              = ‖(v - t • w) - v‖ := dist_eq_norm _ _
            _ = ‖-(t • w : ↥V)‖ := by congr 1; abel
            _ = ‖(t • w : ↥V)‖ := norm_neg _
            _ = t * ‖(w : EuclideanSpace ℝ ι)‖ := h_norm_in_V
            _ < ε := ht_lt
        have h_C_pos : ((↑v : EuclideanSpace ℝ ι) + t • (↑w : EuclideanSpace ℝ ι)) ∈ C := by
          have hh := h_ball_sub h_ball_pos; simpa using hh
        have h_C_neg : ((↑v : EuclideanSpace ℝ ι) - t • (↑w : EuclideanSpace ℝ ι)) ∈ C := by
          have hh := h_ball_sub h_ball_neg; simpa using hh
        have h_le_pos := h_le_on_C _ h_C_pos
        have h_le_neg := h_le_on_C _ h_C_neg
        rw [g.map_add, g.map_smul, smul_eq_mul] at h_le_pos
        rw [g.map_sub, g.map_smul, smul_eq_mul] at h_le_neg
        have h1 : t * g (↑w : EuclideanSpace ℝ ι) ≤ 0 := by linarith
        have h2 : 0 ≤ t * g (↑w : EuclideanSpace ℝ ι) := by linarith
        exact (mul_eq_zero.mp (le_antisymm h1 h2)).resolve_left ht_pos.ne'
    have h_zero_v := h_g_zero_on_V v
    linarith

/-- **Subspace absolute-continuity argument for singular PSD multivariate Gaussians.**

For `S.PosSemidef` with `S ≠ 0` and `D ⊆ ↥V` convex (where `V := range(sqrt S)`),
`multivariateGaussian 0 S` evaluated on the V-image of `frontier_↥V D` is zero.

This is the intrinsic measure-theoretic component of the singular-covariance
argument. It is independent of the geometric inclusion
`frontier C ∩ V ⊆ V.subtypeL '' frontier_↥V (V.subtypeL ⁻¹' C)` and of any
`0 ∈ interior C` hypothesis on the ambient convex set.

**Proof.**

1. **OrthonormalBasis transfer**: with `r := finrank ℝ ↥V`,
   `b := stdOrthonormalBasis ℝ ↥V`, `e := b.repr : ↥V ≃ₗᵢ EuclideanSpace ℝ (Fin r)`.

2. **Pushforward setup**: `Tt := T.codRestrict V` (corestriction),
   `T'' := e.toCLE.toCLM ∘L Tt : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin r)`.
   Then `T'' = e.toCLM ∘L Tt` and `T = V.subtypeL ∘L Tt`, so
   `μ_S(V.subtypeL '' E) = (stdGaussian.map Tt)(E) = (stdGaussian.map T'')(e '' E)`
   for `E ⊆ ↥V`.

3. **Reduce to ℝ^r**: `e '' frontier_↥V D = frontier_ℝ^r (e '' D)`
   (`Homeomorph.preimage_frontier` on `e.toHomeomorph` + take image,
   using `e` is a bijection). `e '' D` is convex in ℝ^r (linear image).

4. **Identify pushed Gaussian**: `T''` is surjective (since `Tt` is, by definition
   of `V` as range of `T`). By `IsGaussian.ext` + `covarianceBilin_map`:
   `stdGaussian.map T'' = multivariateGaussian 0 SS` where
   `Σ.toEuclideanCLM = T'' ∘L T''.adjoint` (PosDef since `T''` surjective).

5. **AC chain**: by `multivariateGaussian_absolutelyContinuous_volume_of_posDef`,
   `multivariateGaussian 0 SS ≪ volume_ℝ^r`. By `Convex.addHaar_frontier`,
   `volume_ℝ^r(frontier (e '' D)) = 0`. AC ⇒ `μ' = 0` on this frontier.
-/
private lemma _multivariateGaussian_singular_image_subspaceL_frontier_eq_zero
    {S : Matrix ι ι ℝ} (_hS : S.PosSemidef) (_hS_nz : S ≠ 0)
    {D : Set ↥(LinearMap.range
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).toLinearMap)}
    (hD_conv : Convex ℝ D) :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) S
      ((LinearMap.range
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).toLinearMap).subtypeL ''
        frontier D) = 0 := by
  -- Setup with `change` to bring goal into a workable form using `T`, `V` abbreviations
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let V : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.range T.toLinearMap
  change multivariateGaussian (0 : EuclideanSpace ℝ ι) S (V.subtypeL '' frontier D) = 0
  -- Step 1: Tt : ℝⁿ →L[ℝ] ↥V (corestriction of T to V)
  have hT_mem_V : ∀ x, T x ∈ V := fun x => LinearMap.mem_range_self T.toLinearMap x
  let Tt : EuclideanSpace ℝ ι →L[ℝ] ↥V := T.codRestrict V hT_mem_V
  have hTt_surj : Function.Surjective Tt := by
    rintro ⟨y, hy_in_V⟩
    obtain ⟨x, hx⟩ := hy_in_V
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  -- Step 2: OrthonormalBasis isometry e : ↥V ≃ₗᵢ ℝ^r
  let r := Module.finrank ℝ ↥V
  let b : OrthonormalBasis (Fin r) ℝ ↥V := stdOrthonormalBasis ℝ ↥V
  let e : ↥V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := b.repr
  let e_cle : ↥V ≃L[ℝ] EuclideanSpace ℝ (Fin r) := e.toContinuousLinearEquiv
  -- Step 3: T'' : ℝⁿ →L[ℝ] ℝ^r
  let T'' : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    e_cle.toContinuousLinearMap ∘L Tt
  have hT''_surj : Function.Surjective T'' :=
    e_cle.surjective.comp hTt_surj
  -- Step 4: Reduce μ_S(V.subtypeL '' frontier D) to (stdGaussian.map T'')(e_cle '' frontier D)
  --
  -- Chain:
  --   μ_S = stdGaussian.map T (defn)
  --   T = V.subtypeL ∘L Tt
  --   So μ_S(V.subtypeL '' E) = stdGaussian(T ⁻¹' (V.subtypeL '' E))
  --                            = stdGaussian(Tt ⁻¹' E)  [V.subtypeL injective]
  --                            = (stdGaussian.map Tt)(E)
  --   Then (stdGaussian.map Tt)(E) = (stdGaussian.map T'')(e_cle '' E)
  --     since T'' = e_cle ∘L Tt and e_cle is a bijection.
  have h_meas_T : Measurable T := T.continuous.measurable
  have h_meas_Tt : Measurable Tt := Tt.continuous.measurable
  have h_meas_T'' : Measurable T'' := T''.continuous.measurable
  have h_meas_subtypeL : Measurable V.subtypeL := V.subtypeL.continuous.measurable
  have h_e_cle_meas : Measurable e_cle := e_cle.continuous.measurable
  have h_e_cle_symm_meas : Measurable e_cle.symm := e_cle.symm.continuous.measurable
  -- frontier D is closed in ↥V, hence measurable.
  have h_meas_frontD : MeasurableSet (frontier D) := isClosed_frontier.measurableSet
  -- e_cle '' frontier D = e_cle.symm ⁻¹' frontier D (e_cle is a bijection)
  have h_image_eq_preimage : e_cle '' frontier D = e_cle.symm ⁻¹' frontier D := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e_cle.symm x, hx, e_cle.apply_symm_apply x⟩
  have h_meas_e_image : MeasurableSet (e_cle '' frontier D) := by
    rw [h_image_eq_preimage]
    exact h_e_cle_symm_meas h_meas_frontD
  have hV_meas : MeasurableSet (V : Set (EuclideanSpace ℝ ι)) :=
    (Submodule.closed_of_finiteDimensional V).measurableSet
  have h_meas_emb : MeasurableEmbedding (V.subtypeL : ↥V → EuclideanSpace ℝ ι) :=
    MeasurableEmbedding.subtype_coe hV_meas
  have h_meas_subtypeL_image : MeasurableSet (V.subtypeL '' frontier D) :=
    h_meas_emb.measurableSet_image' h_meas_frontD
  -- μ_S = stdGaussian.map T (definitional unfolding of multivariateGaussian)
  have h_μ_S_def : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map T := by
    rw [multivariateGaussian]
    congr 1
    funext x
    rw [zero_add]
  -- Step 4a: μ_S(V.subtypeL '' frontier D) = (stdGaussian.map Tt)(frontier D)
  have h_step_4a :
      multivariateGaussian (0 : EuclideanSpace ℝ ι) S (V.subtypeL '' frontier D)
        = (stdGaussian (EuclideanSpace ℝ ι)).map Tt (frontier D) := by
    rw [h_μ_S_def]
    rw [Measure.map_apply h_meas_T h_meas_subtypeL_image]
    rw [Measure.map_apply h_meas_Tt h_meas_frontD]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy_front, hy_eq⟩
      have h_Ttx : Tt x = y := by
        apply Subtype.ext
        change T x = (y : EuclideanSpace ℝ ι)
        exact hy_eq.symm
      rw [h_Ttx]; exact hy_front
    · intro h_Ttx
      refine ⟨Tt x, h_Ttx, ?_⟩
      rfl
  -- Step 4b: (stdGaussian.map Tt)(frontier D) = (stdGaussian.map T'')(e_cle '' frontier D)
  have h_step_4b :
      (stdGaussian (EuclideanSpace ℝ ι)).map Tt (frontier D)
        = (stdGaussian (EuclideanSpace ℝ ι)).map T'' (e_cle '' frontier D) := by
    rw [h_image_eq_preimage]
    rw [Measure.map_apply h_meas_Tt h_meas_frontD]
    rw [Measure.map_apply h_meas_T'' (h_e_cle_symm_meas h_meas_frontD)]
    congr 1
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h_Ttx
      change e_cle.symm (T'' x) ∈ frontier D
      change e_cle.symm (e_cle.toContinuousLinearMap (Tt x)) ∈ frontier D
      rw [show e_cle.symm (e_cle.toContinuousLinearMap (Tt x)) = Tt x from
        e_cle.symm_apply_apply (Tt x)]
      exact h_Ttx
    · intro h
      change e_cle.symm (T'' x) ∈ frontier D at h
      change e_cle.symm (e_cle.toContinuousLinearMap (Tt x)) ∈ frontier D at h
      rw [show e_cle.symm (e_cle.toContinuousLinearMap (Tt x)) = Tt x from
        e_cle.symm_apply_apply (Tt x)] at h
      exact h
  rw [h_step_4a, h_step_4b]
  -- Step 5: (stdGaussian.map T'')(e_cle '' frontier D) = 0
  -- e_cle '' frontier D = frontier (e_cle '' D) (homeomorphism preserves frontier)
  have h_image_frontier : e_cle '' frontier D = frontier ((e_cle : ↥V → _) '' D) := by
    -- e_cle.symm : ℝ^r → ↥V is a homeomorphism. Apply Homeomorph.preimage_frontier:
    --   e_cle.symm ⁻¹' frontier D = frontier (e_cle.symm ⁻¹' D)
    -- And e_cle.symm ⁻¹' D = e_cle '' D (since e_cle.symm is the inverse of e_cle).
    have h_pre_eq_image : ∀ (S : Set ↥V),
        (e_cle.symm : EuclideanSpace ℝ (Fin r) → ↥V) ⁻¹' S = e_cle '' S := by
      intro S
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      refine ⟨fun hx => ⟨e_cle.symm x, hx, e_cle.apply_symm_apply x⟩, ?_⟩
      rintro ⟨y, hy, rfl⟩
      simpa using hy
    rw [← h_pre_eq_image (frontier D)]
    rw [← h_pre_eq_image D]
    exact e_cle.toHomeomorph.symm.preimage_frontier D
  -- e_cle '' D is convex in ℝ^r (linear image of convex)
  have h_image_conv : Convex ℝ ((e_cle : ↥V → _) '' D) :=
    hD_conv.linear_image e_cle.toContinuousLinearMap.toLinearMap
  rw [h_image_frontier]
  -- Step 5: AC chain.
  -- Construct Σ : Matrix (Fin r) (Fin r) ℝ via T'' ∘L T''.adjoint
  let SS : Matrix (Fin r) (Fin r) ℝ :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin r)).symm
      (T'' ∘L ContinuousLinearMap.adjoint T'')
  have hSS_toCLM : Matrix.toEuclideanCLM (𝕜 := ℝ) SS
      = T'' ∘L ContinuousLinearMap.adjoint T'' :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _
  -- T''.adjoint is injective (since T'' is surjective)
  have hT''_adj_inj : Function.Injective (ContinuousLinearMap.adjoint T'') := by
    intro a c hac
    -- T''.adjoint a = T''.adjoint c ⇒ a = c, using T''.surjective
    have h_diff : ContinuousLinearMap.adjoint T'' (a - c) = 0 := by
      rw [map_sub, hac, sub_self]
    -- For all y, ⟨T''.adjoint (a - c), y⟩ = ⟨a - c, T'' y⟩
    -- LHS = 0, so ⟨a - c, T'' y⟩ = 0 for all y
    -- T'' surjective ⇒ for any z, ∃ y, T'' y = z; so ⟨a - c, z⟩ = 0 for all z
    -- ⇒ a - c = 0 ⇒ a = c
    have h_inner_zero : ∀ y, inner ℝ (a - c) (T'' y) = 0 := fun y => by
      have h := ContinuousLinearMap.adjoint_inner_left T'' y (a - c)
      rw [h_diff, inner_zero_left] at h
      exact h.symm
    have h_z_zero : ∀ z : EuclideanSpace ℝ (Fin r), inner ℝ (a - c) z = 0 := fun z => by
      obtain ⟨y, hy⟩ := hT''_surj z
      rw [← hy]; exact h_inner_zero y
    have h_diff_eq : a - c = 0 := by
      apply ext_inner_right ℝ
      intro v
      rw [h_z_zero v, inner_zero_left]
    exact sub_eq_zero.mp h_diff_eq
  -- SS is PosDef
  have hSS_PosDef : SS.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · -- IsHermitian via the toEuclideanLin / IsSymmetric bridge:
      -- SS.IsHermitian ↔ SS.toEuclideanLin.IsSymmetric
      -- ↔ (Matrix.toEuclideanCLM SS).toLinearMap.IsSymmetric  [by
      -- coe_toEuclideanCLM_eq_toEuclideanLin]
      -- ↔ (T'' ∘L T''.adjoint).toLinearMap.IsSymmetric        [by hSS_toCLM]
      -- The last is direct from adjoint definition.
      rw [Matrix.isHermitian_iff_isSymmetric, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
        hSS_toCLM]
      intro x y
      change inner ℝ (T'' (ContinuousLinearMap.adjoint T'' x)) y
        = inner ℝ x (T'' (ContinuousLinearMap.adjoint T'' y))
      calc inner ℝ (T'' (ContinuousLinearMap.adjoint T'' x)) y
          = inner ℝ (ContinuousLinearMap.adjoint T'' x)
              (ContinuousLinearMap.adjoint T'' y) :=
            (ContinuousLinearMap.adjoint_inner_right T'' _ _).symm
        _ = inner ℝ x (T'' (ContinuousLinearMap.adjoint T'' y)) :=
            ContinuousLinearMap.adjoint_inner_left T'' _ _
    · intro x' hx'
      have h_star : (star x' : Fin r → ℝ) = x' := by funext i; simp
      rw [h_star]
      -- Goal: 0 < x' ⬝ᵥ SS.mulVec x'.
      -- Translate to inner-product form via Matrix.inner_toEuclideanCLM + hSS_toCLM.
      let x_lp : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 x'
      have h_x_lp_eq : x_lp.ofLp = x' := rfl
      have h_x_lp_ne : x_lp ≠ 0 := by
        intro h_zero
        apply hx'
        have : x_lp.ofLp = (0 : Fin r → ℝ) := by rw [h_zero]; rfl
        exact h_x_lp_eq ▸ this
      have h_T''_adj_x_ne :
          ContinuousLinearMap.adjoint T'' x_lp ≠ 0 := by
        intro h_zero
        apply h_x_lp_ne
        exact hT''_adj_inj (by rw [h_zero, map_zero])
      have h_pos : 0 < inner ℝ (ContinuousLinearMap.adjoint T'' x_lp)
          (ContinuousLinearMap.adjoint T'' x_lp) :=
        real_inner_self_pos.mpr h_T''_adj_x_ne
      -- Translate inner-product to dotProduct.
      have h_translate : x' ⬝ᵥ SS.mulVec x'
          = inner ℝ x_lp (T'' (ContinuousLinearMap.adjoint T'' x_lp)) := by
        rw [← Matrix.inner_toEuclideanCLM SS x_lp x_lp, hSS_toCLM]
        rfl
      rw [h_translate]
      calc 0 < inner ℝ (ContinuousLinearMap.adjoint T'' x_lp)
                (ContinuousLinearMap.adjoint T'' x_lp) := h_pos
        _ = inner ℝ (T'' (ContinuousLinearMap.adjoint T'' x_lp)) x_lp :=
            ContinuousLinearMap.adjoint_inner_right T'' _ _
        _ = inner ℝ x_lp (T'' (ContinuousLinearMap.adjoint T'' x_lp)) := real_inner_comm _ _
  -- Identify μ' := stdGaussian.map T'' = multivariateGaussian 0 SS via IsGaussian.ext
  haveI hμ'_gauss : IsGaussian ((stdGaussian (EuclideanSpace ℝ ι)).map T'') :=
    isGaussian_map T''
  have hμ'_eq_mvg :
      (stdGaussian (EuclideanSpace ℝ ι)).map T'' = multivariateGaussian 0 SS := by
    apply IsGaussian.ext
    · -- mean: ∫ id ∂μ' = T''(∫ id ∂stdGaussian) = T''(0) = 0; RHS = 0 by integral_id_mvg.
      have h_int : MeasureTheory.Integrable (id : EuclideanSpace ℝ ι → _)
          (stdGaussian (EuclideanSpace ℝ ι)) := by
        have h_memLp := IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ ι)) 1 (by norm_num)
        exact h_memLp.integrable le_rfl
      have h_LHS : ∫ x, id x ∂((stdGaussian (EuclideanSpace ℝ ι)).map T'')
          = (0 : EuclideanSpace ℝ (Fin r)) := by
        rw [MeasureTheory.integral_map h_meas_T''.aemeasurable
          measurable_id.aestronglyMeasurable]
        simp only [id_eq]
        rw [show (fun x => T'' x) = fun x => T'' (id x) from rfl,
          T''.integral_comp_comm h_int]
        simp only [id_eq, integral_id_stdGaussian, map_zero]
      have h_RHS : ∫ x, id x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) SS)
          = (0 : EuclideanSpace ℝ (Fin r)) := by
        simp only [id_eq, integral_id_multivariateGaussian]
      rw [h_LHS, h_RHS]
    · -- covarianceBilin equality: by ContinuousLinearMap.ext, reduces to
      -- ⟨T''.adjoint u, T''.adjoint v⟩ = u.ofLp ⬝ᵥ SS.mulVec v.ofLp
      -- via covarianceBilin_map + covarianceBilin_stdGaussian + Matrix.inner_toEuclideanCLM
      have h_memLp_2 : MeasureTheory.MemLp (id : EuclideanSpace ℝ ι → _) 2
          (stdGaussian (EuclideanSpace ℝ ι)) :=
        IsGaussian.memLp_id _ 2 (by norm_num)
      apply ContinuousLinearMap.ext; intro u
      apply ContinuousLinearMap.ext; intro v
      rw [ProbabilityTheory.covarianceBilin_map h_memLp_2 T'' u v]
      rw [show ProbabilityTheory.covarianceBilin (stdGaussian (EuclideanSpace ℝ ι))
            = innerSL ℝ from covarianceBilin_stdGaussian]
      rw [ProbabilityTheory.covarianceBilin_multivariateGaussian hSS_PosDef.posSemidef]
      rw [← Matrix.inner_toEuclideanCLM SS u v]
      rw [hSS_toCLM]
      change inner ℝ (ContinuousLinearMap.adjoint T'' u) (ContinuousLinearMap.adjoint T'' v)
        = inner ℝ u (T'' (ContinuousLinearMap.adjoint T'' v))
      exact ContinuousLinearMap.adjoint_inner_left T'' (ContinuousLinearMap.adjoint T'' v) u
  rw [hμ'_eq_mvg]
  exact (multivariateGaussian_absolutelyContinuous_volume_of_posDef hSS_PosDef)
    (Convex.addHaar_frontier _ h_image_conv)

/-- **Convex sets with `0 ∈ interior C` are continuity sets for singular PSD
multivariate Gaussians.**

For `S.PosSemidef` that is *not* `PosDef` (singular PSD), and convex
measurable `C` with `0 ∈ interior C`, the boundary `frontier C` has zero
`multivariateGaussian 0 S`-measure.

**Why `hC_int` is required**: The unconditional version (without `hC_int`)
is **false**. Counterexample: `S = 0` (PSD non-PosDef ⇒ this branch),
`multivariateGaussian 0 0 = Dirac 0`, and for `C = {x | x₁ ≤ 0}` (closed
half-space), `frontier C = {x | x₁ = 0}` contains `0`, so
`Dirac 0 (frontier C) = 1 ≠ 0`. The hypothesis `0 ∈ interior C` excludes
exactly this kind of degeneracy: it forces `0 ∉ frontier C` (since
`interior C ∩ frontier C = ∅`), so the `S = 0` case is trivially
`Dirac 0 (frontier C) = 0`. For `S ≠ 0` singular PSD, `hC_int` ensures
`0 ∈ relInterior_V (C ∩ V)` for `V = range (sqrt S)`, which is what the
intrinsic-Lebesgue argument needs.

**Proof.** If `S = 0`, the Gaussian is `Dirac 0`, while `0 ∈ interior C`
places `0` outside `frontier C`. If `S ≠ 0`, the Gaussian is supported on
`V := range (sqrt S)`, so it suffices to consider `frontier C ∩ V`. Convexity
and the interior hypothesis put this set inside the image of the intrinsic
frontier of the pullback of `C` to `V`.

Choose orthonormal coordinates on `V`, with dimension `finrank ℝ V`. In these
coordinates the induced Gaussian has positive-definite covariance: its defining
map is surjective, hence its adjoint is injective. Identifying this pushforward
with the corresponding non-degenerate multivariate Gaussian makes it absolutely
continuous with respect to Euclidean volume. The intrinsic convex frontier is
volume-null by `Convex.addHaar_frontier`, so its image, and therefore
`frontier C ∩ V`, has zero Gaussian measure. -/
lemma multivariateGaussian_frontier_eq_zero_of_convex_singularPsd
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (hS_not_posDef : ¬ S.PosDef)
    {C : Set (EuclideanSpace ℝ ι)}
    (hC_conv : Convex ℝ C) (hC_int : (0 : EuclideanSpace ℝ ι) ∈ interior C) :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) S (frontier C) = 0 := by
  -- `0 ∈ interior C` rules out `0 ∈ frontier C` (interior and frontier are disjoint).
  have h0_not_in_frontier : (0 : EuclideanSpace ℝ ι) ∉ frontier C := by
    intro h_in
    exact (Set.disjoint_iff.mp disjoint_interior_frontier) ⟨hC_int, h_in⟩
  -- `frontier C` is closed (frontier is always closed), hence measurable.
  have h_front_meas : MeasurableSet (frontier C) := isClosed_frontier.measurableSet
  by_cases hS_zero : S = 0
  · -- **Case `S = 0`**: `multivariateGaussian 0 0 = Dirac 0`
    -- (`multivariateGaussian_zero_cov`). `Dirac 0 (frontier C) = 0` since
    -- `0 ∉ frontier C` (from `0 ∈ interior C`).
    subst hS_zero
    rw [multivariateGaussian_zero_cov,
      MeasureTheory.dirac_eq_zero_iff_not_mem h_front_meas]
    exact h0_not_in_frontier
  · -- **Case `S ≠ 0` singular PSD**: support subspace `V := range(sqrt S)` is a
    -- proper non-trivial subspace. Three reductions:
    --   1. `μ_S(frontier C) = μ_S(frontier C ∩ V)` — support fact
    --      (`multivariateGaussian_apply_compl_range`).
    --   2. `frontier C ∩ V ⊆ V.subtypeL '' frontier_↥V (V.subtypeL ⁻¹' C)` —
    --      geometric Hahn-Banach (`_convex_subspace_frontier_pullback_subset`,
    --      this file).
    --   3. `μ_S(V.subtypeL '' frontier_↥V (V.subtypeL ⁻¹' C)) = 0` — V-intrinsic
    --      Lebesgue-nullity and pushforward absolute continuity, supplied by
    --      the preceding intrinsic-subspace lemma.
    set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
    set V : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.range T.toLinearMap with hV_def
    have hV_meas : MeasurableSet (V : Set (EuclideanSpace ℝ ι)) :=
      (Submodule.closed_of_finiteDimensional V).measurableSet
    -- Step 1: `μ_S(frontier C) = μ_S(frontier C ∩ V)` via support on V.
    have h_diff_zero : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
        (frontier C \ (V : Set (EuclideanSpace ℝ ι))) = 0 := by
      apply measure_mono_null _ (multivariateGaussian_apply_compl_range S)
      intro x hx
      exact hx.2
    have h_split :
        multivariateGaussian (0 : EuclideanSpace ℝ ι) S (frontier C)
        = multivariateGaussian (0 : EuclideanSpace ℝ ι) S
            (frontier C ∩ (V : Set (EuclideanSpace ℝ ι))) := by
      have h_decomp := MeasureTheory.measure_inter_add_diff
        (μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) S)
        (frontier C) hV_meas
      rw [h_diff_zero, add_zero] at h_decomp
      exact h_decomp.symm
    rw [h_split]
    -- Step 2: Helper A reduces `frontier C ∩ V ⊆ V.subtypeL '' frontier_↥V (V.subtypeL ⁻¹' C)`.
    have h_pullback_subset : V.subtypeL ⁻¹' frontier C ⊆ frontier (V.subtypeL ⁻¹' C) :=
      _convex_subspace_frontier_pullback_subset hC_conv hC_int V
    have h_image_subset :
        (frontier C ∩ (V : Set (EuclideanSpace ℝ ι))) ⊆
          V.subtypeL '' frontier (V.subtypeL ⁻¹' C) := by
      intro x hx
      refine ⟨⟨x, hx.2⟩, h_pullback_subset ?_, rfl⟩
      simpa [Submodule.subtypeL_apply] using hx.1
    -- Step 3: `μ_S(V.subtypeL '' frontier_↥V (V.subtypeL ⁻¹' C)) = 0` via the
    -- V-intrinsic AC chain (the named helper above).
    have h_image_eq_zero : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
        (V.subtypeL '' frontier (V.subtypeL ⁻¹' C)) = 0 := by
      have hD_conv : Convex ℝ (V.subtypeL ⁻¹' C) :=
        hC_conv.linear_preimage V.subtypeL.toLinearMap
      exact _multivariateGaussian_singular_image_subspaceL_frontier_eq_zero
        hS hS_zero hD_conv
    exact le_antisymm
      ((measure_mono h_image_subset).trans h_image_eq_zero.le) (zero_le)

/-- **Convex sets are continuity sets for PSD multivariate Gaussians.**

For `S.PosSemidef` and convex `C ⊂ EuclideanSpace ℝ ι` (measurable), the
boundary `frontier C` has zero `multivariateGaussian 0 S`-measure, **provided
`0 ∈ interior C`**.

The `hC_int` hypothesis is needed because the unconditional PSD-form is
**false** at singular PSD `S` (e.g. `S = 0`, `mvg 0 0 = Dirac 0`, half-space
`C` with `0` on its boundary gives `Dirac 0 (frontier C) = 1`). The
`hC_int` excludes this by forcing `0 ∉ frontier C`. For PosDef `S`, this
hypothesis is unnecessary — see `multivariateGaussian_frontier_eq_zero_of_convex_posDef`
for the unconditional PosDef-only version.

**Proof**: case-split on `S.PosDef` vs `¬ S.PosDef`, dispatching to the
named sub-sub-helpers above (the PosDef branch ignores `hC_int`). -/
lemma multivariateGaussian_frontier_eq_zero_of_convex
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {C : Set (EuclideanSpace ℝ ι)}
    (hC_conv : Convex ℝ C) (hC_int : (0 : EuclideanSpace ℝ ι) ∈ interior C) :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) S (frontier C) = 0 := by
  by_cases h_posDef : S.PosDef
  · exact multivariateGaussian_frontier_eq_zero_of_convex_posDef h_posDef hC_conv
  · exact multivariateGaussian_frontier_eq_zero_of_convex_singularPsd hS h_posDef
      hC_conv hC_int

/-- **Continuity of `multivariateGaussian` on convex measurable sets in
covariance** (perturbation form needed by `anderson_lemma_set` to extend
`_posDef` to PSD).

For `S.PosSemidef` and convex measurable `C ⊂ EuclideanSpace ℝ ι` with
`0 ∈ interior C`,
`(multivariateGaussian 0 (S + ε•I))(C) → (multivariateGaussian 0 S)(C)` as
`ε → 0⁺`.

The `hC_int` hypothesis propagates from
`multivariateGaussian_frontier_eq_zero_of_convex` (Portmanteau requires the
limit measure's frontier-null on `C`, which is false at singular PSD without
`hC_int`).

**Proof**: combine weak convergence + frontier-null via Mathlib's Portmanteau
theorem `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`. -/
lemma multivariateGaussian_tendsto_at_convex
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {C : Set (EuclideanSpace ℝ ι)}
    (hC_conv : Convex ℝ C) (hC_int : (0 : EuclideanSpace ℝ ι) ∈ interior C) :
    Tendsto (fun ε : ℝ => (multivariateGaussian 0 (S + ε • (1 : Matrix ι ι ℝ))) C)
        (𝓝[>] 0) (𝓝 ((multivariateGaussian 0 S) C)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (multivariateGaussian_weakly_tendsto_of_psd_perturb hS)
    (multivariateGaussian_frontier_eq_zero_of_convex hS hC_conv hC_int)

/-- **Feller continuity of the mean-shift Gaussian kernel** (vdV §8.5).

For a fixed PSD covariance `Σ`, the parameter-indexed family of multivariate
Gaussians `h ↦ multivariateGaussian h Σ` is *Feller continuous*: the bundled
`ProbabilityMeasure`-valued map is continuous from `EuclideanSpace ℝ ι` into
the weak topology of `ProbabilityMeasure (EuclideanSpace ℝ ι)`.

This is what supplies the `hκ_feller` hypothesis of `WeakConverges.bind_kernel`
when the kernel is the Gaussian-shift kernel `Plim h := multivariateGaussian h Σ`
that appears in `LAN_representation_kernel` / Theorem 8.11 Step B.

The covariance `S` carries its PSD regularity in `hS` (vdV §8.5). It is named
`S` rather than `Σ` only because `Σ` is not a valid Lean identifier; the math
reads `Σ` throughout the docstring.

**Proof.**
1. Apply `Filter.tendsto_iff_seq_tendsto` (countable-generation of `𝓝 h`
   from first-countability of `EuclideanSpace ℝ ι`) to reduce to sequences.
2. For `h_n → h`, apply `ProbabilityMeasure.tendsto_of_tendsto_charFun`
   (Lévy continuity, sequential form): pointwise charFun convergence ⇒
   weak convergence.
3. Pointwise charFun convergence: `charFun_multivariateGaussian` gives
   `charFun (multivariateGaussian h_n Σ) t = exp(i t⬝h_n - t⬝Σt/2)`; the
   linear shift `i t⬝h_n → i t⬝h` continuous in `h_n`, the quadratic part
   constant in `h`, so pointwise `→ charFun (multivariateGaussian h Σ) t`. -/
lemma multivariateGaussian_kernel_Feller
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    Continuous (fun h : EuclideanSpace ℝ ι =>
      multivariateGaussianPM h S) := by
  rw [continuous_iff_seqContinuous]
  intro h_seq h h_tend
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro x
  -- Target shape (Mathlib `charFun_multivariateGaussian`):
  --   charFun (mvg h S) x = exp ((↑⟪x, h⟫_ℝ : ℂ) * Complex.I
  --                              - (↑(x.ofLp ⬝ᵥ S.mulVec x.ofLp) : ℂ) / 2)
  -- Rewrite both sides via that formula then reduce to continuity in `h`.
  set rhs : EuclideanSpace ℝ ι → ℂ := fun y =>
    Complex.exp ((Complex.ofReal (inner ℝ x y)) * Complex.I
      - (Complex.ofReal (x.ofLp ⬝ᵥ S.mulVec x.ofLp)) / 2) with hrhs_def
  -- Pointwise: charFun (mvg (h_seq n) S) x = rhs (h_seq n).
  have h_lhs_eq : ∀ n,
      MeasureTheory.charFun ((multivariateGaussianPM (h_seq n) S) : Measure _) x
        = rhs (h_seq n) := by
    intro n
    change MeasureTheory.charFun (multivariateGaussian _ _) x = _
    rw [charFun_multivariateGaussian (μ := h_seq n) hS]
  have h_rhs_eq :
      MeasureTheory.charFun ((multivariateGaussianPM h S) : Measure _) x = rhs h := by
    change MeasureTheory.charFun (multivariateGaussian _ _) x = _
    rw [charFun_multivariateGaussian (μ := h) hS]
  rw [h_rhs_eq]
  refine Tendsto.congr' (.of_forall fun n => (h_lhs_eq n).symm) ?_
  -- Continuity of `rhs` in `y`: linear-in-y inner via continuous_inner,
  -- quadratic-in-x part constant.
  have h_cont : Continuous rhs := by
    simp only [hrhs_def]
    refine Complex.continuous_exp.comp ?_
    refine Continuous.sub ?_ continuous_const
    refine Continuous.mul ?_ continuous_const
    exact Complex.continuous_ofReal.comp
      (continuous_const.inner continuous_id)
  exact (h_cont.tendsto h).comp h_tend

end AsymptoticStatistics
