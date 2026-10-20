module
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Core.TangentAbstract
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.CramerWoldWeakConverges
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.LANexpansion
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Joint LR weak convergence

Joint weak convergence of the likelihood-ratio vector under the iid product
measure `Pⁿ`,

    `(L_{n,g_1}, …, L_{n,g_m}) ⇒ (exp(Δ_g − ½‖g‖²))_g  weakly under Pⁿ`,

where `(Δ_g)_g ~ N(0, A·Aᵀ)` is the multivariate Gaussian shift law with
covariance the Riesz pairing matrix `A = (⟪g_i, g_j⟫)`. Since the basis `g_P`
is orthonormal, `A·Aᵀ = I_m`, so `Δ_{n,g_i}` are independent `N(0, 1)` in the
limit.

The proof composes a per-direction CLT with the Cramér-Wold device to get joint
Δ-convergence, then a LAN expansion plus Slutsky/continuous-mapping to transfer
to the LR vector. Headline declarations: `jointLR_weakConverges` and the
combination-direction variant `combinationLR_weakConverges`, with limit law
`gaussianShiftLRLaw`.

vdV §25.3 (Lemma 3).
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped InnerProductSpace ENNReal NNReal BigOperators

namespace AsymptoticStatistics.LowerBounds.T7_AndersonClosure

namespace JointLRWeakConverges

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.LowerBounds.T6_FinDimLAN
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## The Gaussian-shift LR law on `(ℝ≥0∞)^m`

For an orthonormal `L²(P)`-basis `g_P : Fin m → ↥(L2ZeroMean P)` of a
finite-dim subspace of the tangent set, the limit law of the joint LR
vector `(L_{n,g_1}, …, L_{n,g_m})` under `Pⁿ` is the pushforward of the
multivariate standard Gaussian under componentwise
`Δ ↦ ENNReal.ofReal (exp(Δ_i − ½‖g_i‖²))`.

**Orthonormality** of `g_P` implies the Riesz pairing matrix
`A·Aᵀ = I_m`, so the multivariate Gaussian collapses to a *standard*
multivariate Gaussian (independent `N(0,1)`-components on
`EuclideanSpace ℝ (Fin m)`).
-/

/-- The componentwise LR transform on `EuclideanSpace ℝ (Fin m)`:
`Δ ↦ (i ↦ ENNReal.ofReal (exp(Δ_i − ½‖g_i‖²)))`. Continuous and
measurable; entered by `Continuous.measurable` + `ENNReal.continuous_ofReal`
+ `Real.continuous_exp` + coordinate continuity. -/
noncomputable def lrTransform {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) :
    EuclideanSpace ℝ (Fin m) → (Fin m → ℝ≥0∞) :=
  fun Δ i => ENNReal.ofReal
    (Real.exp (Δ i - (1/2 : ℝ) * ‖(g_P i : Lp ℝ 2 P)‖ ^ 2))

lemma continuous_lrTransform {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) :
    Continuous (lrTransform (P := P) g_P) := by
  refine continuous_pi (fun i : Fin m => ?_)
  refine ENNReal.continuous_ofReal.comp ?_
  refine Real.continuous_exp.comp ?_
  -- Coordinate map on `EuclideanSpace ℝ (Fin m)` is the projection in `EuclideanSpace.proj`.
  exact ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).continuous).sub
    continuous_const

lemma measurable_lrTransform {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) :
    Measurable (lrTransform (P := P) g_P) :=
  (continuous_lrTransform (P := P) g_P).measurable

/-- **The Gaussian-shift LR law on `(ℝ≥0∞)^m`.**

Pushforward of the multivariate standard Gaussian on
`EuclideanSpace ℝ (Fin m)` under the componentwise LR transform
`Δ ↦ (i ↦ ENNReal.ofReal (exp(Δ_i − ½‖g_i‖²)))`.

When `g_P` is orthonormal, the Riesz pairing matrix `A·Aᵀ = I_m`, so
the pre-pushforward Gaussian is the *standard* multivariate Gaussian
(independent `N(0,1)` components). -/
noncomputable def gaussianShiftLRLaw {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) :
    Measure (Fin m → ℝ≥0∞) :=
  (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
    (1 : Matrix (Fin m) (Fin m) ℝ)).map (lrTransform (P := P) g_P)

/-! ## Bridging lemma 1: joint `Δ_n` weak convergence via Cramér-Wold

The per-direction CLT `weakConverges_scoreSumScalar_under_pi` (shipped
in `T6_FinDimLAN/JointLAN.lean`) gives `Δ_{n,g} ⇒ N(0, ‖g‖²)` for any
`g`. Cramér-Wold (`ForMathlib/CramerWoldWeakConverges.lean`) lifts to
joint convergence by checking every linear functional projects to a
per-direction score sum.
-/

/-- The **joint score sum** `Δ_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin m)`
along an orthonormal basis `g_P : Fin m → ↥(L2ZeroMean P)`:
`Δ_n X i := (√n)⁻¹ · ∑ⱼ g_P i (X j)`. Just `JointLAN.scoreSumScalar`
collected over `i`. The result is packaged into `EuclideanSpace ℝ (Fin m)`
via `(EuclideanSpace.equiv (Fin m) ℝ).symm`. -/
noncomputable def jointScoreSum {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) (n : ℕ) :
    (Fin n → Ω) → EuclideanSpace ℝ (Fin m) :=
  fun X => (EuclideanSpace.equiv (Fin m) ℝ).symm
    (fun i =>
      AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
        (P := P) (g_P i) n X)

lemma measurable_jointScoreSum {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) (n : ℕ) :
    Measurable (jointScoreSum (P := P) g_P n) := by
  unfold jointScoreSum
  -- Per-coordinate score sums are measurable; bundle into `Fin m → ℝ`,
  -- then push through the continuous linear equiv `(EuclideanSpace.equiv).symm`.
  have h_inner : Measurable (fun X : Fin n → Ω => fun i : Fin m =>
      AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
        (P := P) (g_P i) n X) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.measurable_scoreSumScalar
      (g_P i) n
  exact ((EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable).comp h_inner

/-- The linear combination `Σⱼ h_j • g_P j` viewed in `↥(L2ZeroMean P)`.
Used as the per-direction score for the Cramér-Wold projection. -/
noncomputable def linComb {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) (h : EuclideanSpace ℝ (Fin m)) :
    ↥(L2ZeroMean P) :=
  ∑ i : Fin m, (h i) • g_P i

/-- **Per-direction reduction**: the inner product `⟪h, jointScoreSum g_P n X⟫_ℝ`
on `EuclideanSpace ℝ (Fin m)` equals `scoreSumScalar (Σⱼ h_j • g_P j) n X`,
almost everywhere on `Pⁿ`. This is the algebraic identity bridging
Cramér-Wold's per-direction projection and the per-direction CLT.

**Proof sketch**: pointwise, `⟪h, jointScoreSum g_P n X⟫_ℝ = ∑ i, h i * scoreSumScalar (g_P i) n X`
(by `PiLp.inner_apply` + real inner = multiplication). The RHS expands
as `(√n)⁻¹ · ∑ j, (linComb g_P h).coe (X j)`. The L²-coerce-of-sum
identity for `linComb` (sum of scaled `Lp` elements) holds a.e. on `P`
by `Lp.coeFn_add` / `Lp.coeFn_smul` finset induction; this lifts to
a.e. on `Pⁿ` via marginal inclusion of each coordinate. -/
lemma inner_jointScoreSum_eq_ae_scoreSumScalar {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) (h : EuclideanSpace ℝ (Fin m)) (n : ℕ) :
    (fun X : Fin n → Ω =>
        ⟪h, jointScoreSum (P := P) g_P n X⟫_ℝ)
      =ᵐ[Measure.pi (fun _ : Fin n => P)]
      (fun X : Fin n → Ω =>
        AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
          (P := P) (linComb (P := P) g_P h) n X) := by
  classical
  -- **Step A (P-AE)**: the underlying `Ω → ℝ` of `linComb g_P h` equals
  -- the pointwise sum `∑ i, h i • ((g_P i : Lp ℝ 2 P) : Ω → ℝ)` `P`-a.e.
  -- This combines `Submodule.coe_sum` + `Submodule.coe_smul` (defeq on
  -- the coercion to `Lp`) with finset-induction on `Lp.coeFn_add` /
  -- `Lp.coeFn_smul`.
  have h_linComb_coe_eq :
      (linComb (P := P) g_P h : Lp ℝ 2 P)
        = ∑ i : Fin m, h i • ((g_P i : Lp ℝ 2 P)) := by
    unfold linComb
    rw [Submodule.coe_sum]
    rfl
  have h_ae_P :
      (fun ω : Ω => ((linComb (P := P) g_P h : Lp ℝ 2 P) : Ω → ℝ) ω)
        =ᵐ[P]
      (fun ω : Ω => ∑ i : Fin m, h i * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω) := by
    -- Rewrite the LHS via `h_linComb_coe_eq` then induct on the finset.
    rw [h_linComb_coe_eq]
    -- Goal: `⇑(∑ i ∈ univ, h i • (g_P i : Lp ℝ 2 P)) =ᵐ[P]
    --       fun ω => ∑ i ∈ univ, h i * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) ω`.
    -- Finset induction: rewrite via `Lp.coeFn_add` + `Lp.coeFn_smul`.
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards with ω
      simp [Lp.coeFn_zero]
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      -- LHS: `⇑(h i • g_P i + ∑ ⋯) =ᵐ[P] (h i • g_P i) + ∑ ⋯` by `coeFn_add`.
      have h_add := Lp.coeFn_add (h i • (g_P i : Lp ℝ 2 P))
        (∑ j ∈ s, h j • ((g_P j : Lp ℝ 2 P)))
      have h_smul := Lp.coeFn_smul (h i) ((g_P i : Lp ℝ 2 P))
      filter_upwards [h_add, h_smul, ih] with ω hadd hsmul hih
      -- After unfolding `+`, `•` on the RHS:
      -- `(⇑(h i • g_P i) ω) + (⇑(∑ ⋯) ω) = h i * (g_P i ω) + ∑_{j∈s} h j * (g_P j ω)`.
      simp only [Pi.add_apply] at hadd
      simp only [Pi.smul_apply, smul_eq_mul] at hsmul
      rw [hadd, hsmul, hih]
  -- **Step B (Pⁿ-AE)**: lift `h_ae_P` to `Pⁿ`-AE for each coordinate
  -- `X j`. The lifting goes through `tendsto_eval_ae_ae` for each `j`.
  have h_ae_Pn :
      ∀ j : Fin n,
        ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
          ((linComb (P := P) g_P h : Lp ℝ 2 P) : Ω → ℝ) (X j)
            = ∑ i : Fin m, h i * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) (X j) := by
    intro j
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P) (i := j)).eventually
      h_ae_P
  -- Combine the per-`j` AE-equalities into a single `Pⁿ`-AE statement.
  have h_ae_all :
      ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
        ∀ j : Fin n,
          ((linComb (P := P) g_P h : Lp ℝ 2 P) : Ω → ℝ) (X j)
            = ∑ i : Fin m, h i * ((g_P i : Lp ℝ 2 P) : Ω → ℝ) (X j) := by
    rw [ae_all_iff]
    exact h_ae_Pn
  -- **Step C (algebra)**: assemble the LHS pointwise.
  filter_upwards [h_ae_all] with X hX
  -- Define the local `Ω → ℝ`-coercion of `g_P i` for brevity.
  set Gi : Fin m → Ω → ℝ :=
    fun i => ((g_P i : Lp ℝ 2 P) : Ω → ℝ) with hGi_def
  -- Goal (unfolded): `⟪h, jointScoreSum g_P n X⟫_ℝ = (√n)⁻¹ * ∑ j, (linComb g_P h) (X j)`.
  -- Bridge via the `PiLp.inner_apply` ⇒ scalar-sum identity.
  have h_lhs_eq :
      (⟪h, jointScoreSum (P := P) g_P n X⟫_ℝ : ℝ)
        = ∑ i : Fin m, h i *
            ((Real.sqrt n)⁻¹ * ∑ j : Fin n, Gi i (X j)) := by
    -- `⟪h, x⟫_ℝ = ∑ i, ⟪h i, x i⟫_ℝ` by `PiLp.inner_apply`.
    -- Each per-coord inner equals `(x i) * (h i) = h i * (x i)`.
    -- `(EuclideanSpace.equiv).symm v i = v i` reduces; the per-coord
    -- value is `JointLAN.scoreSumScalar (g_P i) n X = (√n)⁻¹ * ∑ j, Gi i ω`.
    have h_pi : (⟪h, jointScoreSum (P := P) g_P n X⟫_ℝ : ℝ)
        = ∑ i : Fin m,
            ⟪h i,
              ((EuclideanSpace.equiv (Fin m) ℝ).symm
                (fun i' : Fin m =>
                  AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                    (P := P) (g_P i') n X)) i⟫_ℝ := by
      change (⟪h, (EuclideanSpace.equiv (Fin m) ℝ).symm
          (fun i : Fin m =>
            AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
              (P := P) (g_P i) n X)⟫_ℝ : ℝ) = _
      rw [PiLp.inner_apply]
    rw [h_pi]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- `⟪h i, sssX i⟫_ℝ = sssX i * h i` (real inner is mul-flip);
    -- close with `change a * b = b * a; ring`.
    have h_inner_eq :
        (⟪h i,
            ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (fun i' : Fin m =>
                AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                  (P := P) (g_P i') n X)) i⟫_ℝ : ℝ)
          = ((Real.sqrt n)⁻¹ * ∑ j : Fin n, Gi i (X j))
              * h i := by
      change ((Real.sqrt n)⁻¹ * ∑ j : Fin n, Gi i (X j)) * h i
          = ((Real.sqrt n)⁻¹ * ∑ j : Fin n, Gi i (X j)) * h i
      rfl
    rw [h_inner_eq]; ring
  rw [h_lhs_eq]
  -- Now: `∑ i, h i * ((√n)⁻¹ * ∑ j, Gi i ω) = (√n)⁻¹ * ∑ j, (linComb g_P h) ω`.
  -- Algebra: distribute `(√n)⁻¹`, swap sums, then collapse via `hX j`.
  -- Unfold the RHS `scoreSumScalar` definition.
  unfold AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
  -- Goal: `∑ i, h i * ((√n)⁻¹ * ∑ j, Gi i ω) = (√n)⁻¹ * ∑ j, ((linComb g_P h) ω)`.
  -- Using `hX j`: `(linComb g_P h ω)_j = ∑ i, h i * Gi i ω`.
  have h_RHS_collapse :
      ((Real.sqrt n)⁻¹ * ∑ j : Fin n,
          ((linComb (P := P) g_P h : Lp ℝ 2 P) : Ω → ℝ) (X j) : ℝ)
        = (Real.sqrt n)⁻¹ * ∑ j : Fin n,
            ∑ i : Fin m, h i * Gi i (X j) := by
    refine congrArg ((Real.sqrt n)⁻¹ * ·) ?_
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hGi_def]
    exact hX j
  rw [h_RHS_collapse]
  -- Now goal: `∑ i, h i * ((√n)⁻¹ * ∑ j, Gi i ω) = (√n)⁻¹ * ∑ j, ∑ i, h i * Gi i ω`.
  -- Reduce both sides to the canonical form `∑ i ∑ j, (√n)⁻¹ * (h i * Gi i ω)`.
  have h_canon_L : (∑ i : Fin m, h i *
          ((Real.sqrt n)⁻¹ * ∑ j : Fin n, Gi i (X j)) : ℝ)
        = ∑ i : Fin m, ∑ j : Fin n,
            (Real.sqrt n)⁻¹ * (h i * Gi i (X j)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have h_canon_R :
      ((Real.sqrt n)⁻¹ * ∑ j : Fin n,
          ∑ i : Fin m, h i * Gi i (X j) : ℝ)
        = ∑ i : Fin m, ∑ j : Fin n,
            (Real.sqrt n)⁻¹ * (h i * Gi i (X j)) := by
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [h_canon_L, h_canon_R]

/-- **Joint Δ-convergence under `Pⁿ` (Cramér-Wold paste).**

For an orthonormal `g_P`, the joint score sum `Δ_n` converges weakly
under `Pⁿ` to the multivariate standard Gaussian on
`EuclideanSpace ℝ (Fin m)`.

**Strategy**: per-direction CLT
(`JointLAN.weakConverges_scoreSumScalar_under_pi`) gives the scalar
projection `Δ_{n,g} ⇒ N(0, ‖g‖²)` for any direction. Cramér-Wold
(`ForMathlib/CramerWoldWeakConverges.cramerWold_weakConverges`,
specialized from `ℝ × EuclideanSpace ℝ (Fin m)` to
`EuclideanSpace ℝ (Fin m)` by zeroing the first coordinate) lifts to
joint convergence: any linear functional `θ ↦ ⟪h, θ⟫` of the joint Δ
vector is itself a per-direction score sum along
`Σⱼ h_j g_P j ∈ L²₀(P)`, and orthonormality of `g_P` collapses the
limit variance to `‖h‖²`, matching the standard multivariate Gaussian. -/
lemma jointDelta_weakConverges_under_pi
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P)))) :
    WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map (jointScoreSum (P := P) g_P n))
      (ProbabilityTheory.multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin m)) (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  classical
  -- Step 1: replace `multivariateGaussian 0 1` with `stdGaussian _`.
  rw [ProbabilityTheory.multivariateGaussian_zero_one]
  -- Step 2: lift the joint statement to `ℝ × EuclideanSpace ℝ (Fin m)`
  -- by embedding the second coordinate at `0`.
  set ι : EuclideanSpace ℝ (Fin m) → ℝ × EuclideanSpace ℝ (Fin m) :=
    fun y => (0, y) with hι_def
  have h_ι_cont : Continuous ι := by
    refine continuous_prodMk.mpr ⟨continuous_const, continuous_id⟩
  have h_ι_meas : Measurable ι := h_ι_cont.measurable
  -- Lift the sequence and the limit.
  set μ_n : ℕ → Measure (EuclideanSpace ℝ (Fin m)) :=
    fun n => (Measure.pi (fun _ : Fin n => P)).map
      (jointScoreSum (P := P) g_P n) with hμn_def
  set ν : Measure (EuclideanSpace ℝ (Fin m)) :=
    ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)) with hν_def
  -- Probability-measure structure on `μ_n` and `ν`.
  haveI h_prob_μn : ∀ n, IsProbabilityMeasure (μ_n n) := by
    intro n
    rw [hμn_def]
    exact Measure.isProbabilityMeasure_map
      (measurable_jointScoreSum (P := P) g_P n).aemeasurable
  haveI h_prob_ν : IsProbabilityMeasure ν := by
    rw [hν_def]; infer_instance
  -- Step 3: apply Cramér-Wold to the lifted measures.
  haveI h_prob_lifted_n : ∀ n, IsProbabilityMeasure ((μ_n n).map ι) := fun n =>
    Measure.isProbabilityMeasure_map h_ι_meas.aemeasurable
  haveI h_prob_lifted_lim : IsProbabilityMeasure (ν.map ι) :=
    Measure.isProbabilityMeasure_map h_ι_meas.aemeasurable
  have h_lifted : WeakConverges (fun n => (μ_n n).map ι) (ν.map ι) := by
    refine AsymptoticStatistics.ForMathlib.cramerWold_weakConverges (m := m)
      (μ_n := fun n => (μ_n n).map ι) (μ := ν.map ι) ?_
    intro t hvec
    -- Per-direction projected pushforwards.
    -- Composition: `(fun p => t * p.1 + ⟪hvec, p.2⟫_ℝ) ∘ ι = fun y => ⟪hvec, y⟫_ℝ`.
    set proj : ℝ × EuclideanSpace ℝ (Fin m) → ℝ :=
      fun p => t * p.1 + ⟪hvec, p.2⟫_ℝ with hproj_def
    have h_proj_cont : Continuous proj := by
      refine Continuous.add ?_ ?_
      · exact continuous_const.mul continuous_fst
      · exact continuous_const.inner continuous_snd
    have h_proj_meas : Measurable proj := h_proj_cont.measurable
    have h_compose : ∀ y : EuclideanSpace ℝ (Fin m),
        proj (ι y) = ⟪hvec, y⟫_ℝ := by
      intro y; simp [hproj_def, hι_def]
    -- Reduce `(μ_n n).map ι .map proj = (μ_n n).map (proj ∘ ι) = (μ_n n).map (⟪hvec, ·⟫_ℝ)`.
    have h_lhs_n : ∀ n, ((μ_n n).map ι).map proj
        = (μ_n n).map (fun y => ⟪hvec, y⟫_ℝ) := by
      intro n
      rw [Measure.map_map h_proj_meas h_ι_meas]
      congr 1; funext y; exact h_compose y
    have h_lhs_lim : (ν.map ι).map proj
        = ν.map (fun y => ⟪hvec, y⟫_ℝ) := by
      rw [Measure.map_map h_proj_meas h_ι_meas]
      congr 1; funext y; exact h_compose y
    -- It now suffices to show:
    -- `WeakConverges (n => μ_n n .map (⟪hvec, ·⟫_ℝ)) (ν.map (⟪hvec, ·⟫_ℝ))`.
    -- The limit measure is `gaussianReal 0 (‖hvec‖²).toNNReal` by
    -- `IsGaussian.map_eq_gaussianReal` for `stdGaussian`.
    have h_inner_meas : Measurable
        (fun y : EuclideanSpace ℝ (Fin m) => ⟪hvec, y⟫_ℝ) :=
      (continuous_const.inner continuous_id).measurable
    -- Identify the limit on the ν side.
    have h_ν_proj :
        ν.map (fun y => ⟪hvec, y⟫_ℝ)
          = ProbabilityTheory.gaussianReal 0 (‖hvec‖ ^ 2).toNNReal := by
      -- `(innerSL ℝ hvec : E →L[ℝ] ℝ)` is a `StrongDual`.
      have h_eq_innerSL : (fun y : EuclideanSpace ℝ (Fin m) => ⟪hvec, y⟫_ℝ)
          = ⇑(innerSL ℝ hvec : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := by
        funext y; rfl
      rw [h_eq_innerSL, hν_def]
      -- Apply IsGaussian.map_eq_gaussianReal.
      rw [ProbabilityTheory.IsGaussian.map_eq_gaussianReal
        (innerSL ℝ hvec : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)]
      -- `μ[L]` for L = innerSL ℝ hvec, μ = stdGaussian: integral_strongDual_stdGaussian = 0.
      rw [ProbabilityTheory.integral_strongDual_stdGaussian]
      -- `Var[L; stdGaussian] = ‖L‖² = ‖hvec‖²`.
      rw [ProbabilityTheory.variance_dual_stdGaussian]
      rw [innerSL_apply_norm]
    -- Identify the LHS sequence: `(μ_n n).map (⟪hvec, ·⟫_ℝ) = (Pⁿ).map (scoreSumScalar (linComb g_P
    -- hvec) n)`.
    have h_lhs_id : ∀ n, (μ_n n).map (fun y => ⟪hvec, y⟫_ℝ)
        = (Measure.pi (fun _ : Fin n => P)).map
            (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
              (P := P) (linComb (P := P) g_P hvec) n) := by
      intro n
      rw [hμn_def, Measure.map_map h_inner_meas
        (measurable_jointScoreSum (P := P) g_P n)]
      -- `(Pⁿ).map (⟪hvec, ·⟫ ∘ jointScoreSum g_P n)
      --   = (Pⁿ).map (scoreSumScalar (linComb g_P hvec) n)` by a.e. equality.
      refine Measure.map_congr ?_
      have h_ae := inner_jointScoreSum_eq_ae_scoreSumScalar
        (P := P) (g_P := g_P) (h := hvec) (n := n)
      filter_upwards [h_ae] with X hX using hX
    -- The variance of the linear combination equals `‖hvec‖²` by orthonormality.
    have h_var_eq : ‖(linComb (P := P) g_P hvec : Lp ℝ 2 P)‖ ^ 2 = ‖hvec‖ ^ 2 := by
      -- `linComb g_P hvec = Σ i, hvec i • g_P i`, so
      -- `‖·‖² = Σ i j, hvec i * hvec j * ⟪g_P i, g_P j⟫`. Orthonormality
      -- collapses to `Σ i, hvec i ^ 2 = ‖hvec‖²` on EuclideanSpace.
      -- We compute via the Lp-norm-from-inner formula:
      have h_lp_eq : (linComb (P := P) g_P hvec : Lp ℝ 2 P)
          = ∑ i : Fin m, hvec i • ((g_P i : Lp ℝ 2 P)) := by
        unfold linComb
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl (fun i _ => rfl)
      rw [h_lp_eq]
      -- `‖∑ i, c i • v i‖² = ∑ i j, c i * c j * ⟪v i, v j⟫`.
      have h_norm_sq :
          ‖∑ i : Fin m, hvec i • ((g_P i : Lp ℝ 2 P))‖ ^ 2
            = ∑ i : Fin m, hvec i ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, sum_inner]
        simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
        -- Use orthonormality: `⟪g_P i, g_P j⟫ = if i=j then 1 else 0`.
        have h_inner :
            ∀ i j : Fin m,
              (⟪((g_P i : Lp ℝ 2 P)), ((g_P j : Lp ℝ 2 P))⟫_ℝ : ℝ)
                = if i = j then 1 else 0 := by
          intro i j
          -- `Orthonormal` on `↥(L2ZeroMean P)`-valued: inner equals `if i = j then 1 else 0`.
          rcases h_orth with ⟨h_norm, h_perp⟩
          by_cases hij : i = j
          · subst hij
            rw [if_pos rfl]
            -- Goal: `⟪(g_P i : Lp ℝ 2 P), (g_P i : Lp ℝ 2 P)⟫_ℝ = 1`.
            -- Bridge to submodule inner via `Submodule.coe_inner` (defeq), then
            -- `real_inner_self_eq_norm_sq` and `‖g_P i‖ = 1`.
            have h_step : (⟪((g_P i : Lp ℝ 2 P)), ((g_P i : Lp ℝ 2 P))⟫_ℝ : ℝ)
                = ‖(g_P i : ↥(L2ZeroMean P))‖ ^ 2 := by
              -- `⟪g_P i, g_P i⟫_ℝ_(Lp) = ⟪g_P i, g_P i⟫_ℝ_(↥) = ‖g_P i‖²_(↥)`.
              -- The two inners agree by `Submodule.coe_inner` (`rfl`).
              have h_coe : (⟪((g_P i : Lp ℝ 2 P)), ((g_P i : Lp ℝ 2 P))⟫_ℝ : ℝ)
                  = (⟪(g_P i : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ : ℝ) := rfl
              rw [h_coe, real_inner_self_eq_norm_sq]
            rw [h_step, h_norm i]
            norm_num
          · -- `i ≠ j`: orthogonality gives 0.
            rw [if_neg hij]
            have h_perp_ij : (⟪(g_P i : ↥(L2ZeroMean P)), (g_P j : ↥(L2ZeroMean P))⟫_ℝ : ℝ) = 0 :=
              h_perp hij
            -- Same `Submodule.coe_inner` bridge.
            have h_coe : (⟪((g_P i : Lp ℝ 2 P)), ((g_P j : Lp ℝ 2 P))⟫_ℝ : ℝ)
                = (⟪(g_P i : ↥(L2ZeroMean P)), (g_P j : ↥(L2ZeroMean P))⟫_ℝ : ℝ) := rfl
            rw [h_coe]; exact h_perp_ij
        simp_rw [h_inner]
        -- Goal: `∑ i, ∑ j, hvec i * (hvec j * (if i = j then 1 else 0)) = ∑ i, hvec i ^ 2`.
        refine Finset.sum_congr rfl (fun i _ => ?_)
        -- Inner-sum manipulation: collapse `hvec j * (if i=j then 1 else 0)` and
        -- then `hvec i * (if i=j then ... else 0)` to `if i=j then hvec i * hvec j else 0`.
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin m)) i
          (fun j => hvec i * hvec j), if_pos (Finset.mem_univ _)]
        ring
      rw [h_norm_sq, EuclideanSpace.real_norm_sq_eq]
    -- Now apply the per-direction CLT to `linComb g_P hvec`.
    have h_per_dir :=
      AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.weakConverges_scoreSumScalar_under_pi
        (P := P) (linComb (P := P) g_P hvec)
    -- `h_per_dir`: weakConverges (Pⁿ.map (scoreSumScalar (linComb g_P hvec) n))
    --   (gaussianReal 0 (‖linComb g_P hvec‖²).toNNReal).
    -- Combine with `h_var_eq` to align with `gaussianReal 0 (‖hvec‖²).toNNReal`.
    have h_eq : ProbabilityTheory.gaussianReal 0
        (‖(linComb (P := P) g_P hvec : Lp ℝ 2 P)‖ ^ 2).toNNReal
        = ProbabilityTheory.gaussianReal 0 (‖hvec‖ ^ 2).toNNReal := by
      rw [h_var_eq]
    -- Convert the per-direction CLT through `h_eq` and `h_lhs_id` to the
    -- shape after Cramér-Wold's projection.
    have h_per_dir' : WeakConverges
        (fun n =>
          (μ_n n).map (fun y : EuclideanSpace ℝ (Fin m) => ⟪hvec, y⟫_ℝ))
        (ProbabilityTheory.gaussianReal 0 (‖hvec‖ ^ 2).toNNReal) := by
      rw [← h_eq]
      have h_seq_eq : (fun n =>
          (μ_n n).map (fun y : EuclideanSpace ℝ (Fin m) => ⟪hvec, y⟫_ℝ))
          = fun n =>
            (Measure.pi (fun _ : Fin n => P)).map
              (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                (P := P) (linComb (P := P) g_P hvec) n) := by
        funext n; exact h_lhs_id n
      rw [h_seq_eq]
      exact h_per_dir
    -- Now show the goal: weakConverges of `((μ_n n).map ι).map proj` against
    -- `(ν.map ι).map proj`.  Both reduce via `h_lhs_n`/`h_lhs_lim`.
    intro f
    have h := h_per_dir' f
    -- `h : Tendsto (fun n => ∫ x, f x ∂ ((μ_n n).map (⟪hvec,·⟫))) atTop ...`.
    -- Bridge via `h_ν_proj` for the limit and `h_lhs_n`/`h_lhs_lim` for both sides.
    have h_lim_eq : ((ν.map ι).map proj) =
        ProbabilityTheory.gaussianReal 0 (‖hvec‖ ^ 2).toNNReal := by
      rw [h_lhs_lim, h_ν_proj]
    have h_seq_eq : ∀ n, ((μ_n n).map ι).map proj =
        (μ_n n).map (fun y : EuclideanSpace ℝ (Fin m) => ⟪hvec, y⟫_ℝ) := h_lhs_n
    simp_rw [h_seq_eq, h_lim_eq]
    exact h
  -- Step 4: pushback via `Prod.snd`.
  have h_snd_cont : Continuous (Prod.snd :
      ℝ × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) :=
    continuous_snd
  have h_snd_meas : Measurable (Prod.snd :
      ℝ × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) :=
    h_snd_cont.measurable
  have h_pushed := h_lifted.map h_snd_cont h_snd_meas
  -- `((μ_n n).map ι).map Prod.snd = μ_n n` since `Prod.snd ∘ ι = id`.
  have h_id_n : ∀ n, ((μ_n n).map ι).map (Prod.snd :
      ℝ × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
        = μ_n n := by
    intro n
    rw [Measure.map_map h_snd_meas h_ι_meas]
    have h_id : (Prod.snd : ℝ × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) ∘ ι = id := by
      funext y; simp [hι_def]
    rw [h_id, Measure.map_id]
  have h_id_lim : (ν.map ι).map (Prod.snd :
      ℝ × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
        = ν := by
    rw [Measure.map_map h_snd_meas h_ι_meas]
    have h_id : (Prod.snd : ℝ × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) ∘ ι = id := by
      funext y; simp [hι_def]
    rw [h_id, Measure.map_id]
  intro f
  have h_f := h_pushed f
  simp only [h_id_n, h_id_lim] at h_f
  exact h_f

/-! ## Bridging lemma 2: from joint Δ to joint LR via LAN + Slutsky

The LAN expansion (`lanRemainder` in `T6_FinDimLAN/LANexpansion.lean`) gives,
for any `g_P i ∈ ↥(L2ZeroMean P)`,

    `log L_{n,g_i}(X) = Δ_{n,g_i}(X) − ½‖g_i‖² + R_{n,g_i}(X)`

with `R_{n,g_i} → 0` in `Pⁿ`-probability. Combined with the joint Δ_n
convergence (bridging lemma 1) and the continuous mapping theorem
(continuity of `Δ ↦ exp(Δ − ½‖g‖²)`), Slutsky gives joint LR weak
convergence. The decomposition below splits this into two steps:

* `jointLAN_factorization` — the LAN identity at the *joint* level: a
  `Pⁿ`-AE pointwise factorization
  `lr_n n X i = lrTransform (jointScoreSum + R_n) X i` together with
  joint convergence `R_n →ᵖ 0` under `Pⁿ`.
* `jointSlutsky_addRemainder_to_jointDelta` — the joint Slutsky paste:
  given joint Δ-convergence to `N(0, I_m)` and `R_n →ᵖ 0`, the *adjusted*
  vector `jointScoreSum + R_n` also weakly converges to `N(0, I_m)`.

The `gaussianShiftLRLaw` definitional alignment in the conclusion is
recorded as `gaussianShiftLRLaw_eq_pushforward` (`rfl` from the def).
`jointDelta_to_jointLR_via_LAN_and_Slutsky` then composes these with
`WeakConverges.map (continuous_lrTransform g_P)` and two
`Measure.map_congr`-style rewrites (one per side of the `WeakConverges`).
-/

/-- **The `gaussianShiftLRLaw g_P` is the `lrTransform`-pushforward of
the multivariate standard Gaussian.** This is `rfl`-from-the-def; we
expose it as a named lemma so the main bridge can `rw` against it
without unfolding `gaussianShiftLRLaw` everywhere. -/
private lemma gaussianShiftLRLaw_eq_pushforward {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P)) :
    gaussianShiftLRLaw (P := P) g_P
      = (ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ)).map (lrTransform (P := P) g_P) :=
  rfl

/-- **Joint-norm convergence in probability from per-coordinate convergence.**

If a finite family of `ℝ`-valued sequences `r i : ℕ → (Fin n → Ω) → ℝ`
converges to 0 in `Pⁿ`-probability (each coordinate independently),
then the bundled `EuclideanSpace ℝ (Fin m)`-valued sequence does too in
the joint norm.

**Proof idea**: the joint norm satisfies
`‖(EuclideanSpace.equiv).symm v‖² = ∑ i, (v i)²`, so
`‖·‖ ≥ ε ⟹ ∃ i, |v i| ≥ ε / √m` (when `m ≥ 1`; when `m = 0` the joint
space is the singleton `{0}` and the statement is trivial). Apply the
union bound `Pⁿ (⋃ i, A i) ≤ ∑ i, Pⁿ (A i)` and pass each summand
through the per-coordinate convergence hypothesis. -/
private lemma pi_tendsto_of_per_coord_pi_tendsto {m : ℕ}
    (r : Fin m → (n : ℕ) → (Fin n → Ω) → ℝ)
    (hr_zero : ∀ i, ∀ ε > 0,
      Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ |r i n X|})
        atTop (𝓝 (0 : ℝ≥0∞))) :
    ∀ ε > 0,
      Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω
            | ε ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => r i n X)‖})
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  intro ε hε
  -- Set the per-coordinate threshold `δ := ε / √m` (when `m > 0`).
  -- For `m = 0`, the joint norm is identically 0, so the bad set is empty.
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: target type `EuclideanSpace ℝ (Fin 0)` is a singleton, norm is 0.
    subst hm
    have h_set_empty : ∀ n : ℕ,
        ({X : Fin n → Ω | ε ≤ ‖(EuclideanSpace.equiv (Fin 0) ℝ).symm
            (fun i => r i n X)‖} : Set (Fin n → Ω)) = ∅ := by
      intro n
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have h_norm_zero :
          ‖(EuclideanSpace.equiv (Fin 0) ℝ).symm (fun i : Fin 0 => r i n X)‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp
      rw [h_norm_zero]; exact hε
    simp_rw [h_set_empty]
    simp only [measure_empty]
    exact tendsto_const_nhds
  · -- `m > 0`: use the bound `‖v‖² = ∑ |v i|² ≥ |v j|²`, hence
    -- `‖v‖ ≥ ε ⟹ ∃ i, |v i| ≥ ε / √m`.
    have h_sqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
    set δ : ℝ := ε / Real.sqrt m with hδ_def
    have hδ_pos : 0 < δ := by positivity
    -- Pointwise bound: `‖v‖ ≥ ε ⟹ ∃ i, |v i| ≥ δ`.
    have h_norm_max : ∀ n (X : Fin n → Ω),
        ε ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => r i n X)‖
          → ∃ i : Fin m, δ ≤ |r i n X| := by
      intro n X hX
      by_contra h_neg
      push Not at h_neg
      -- Compute the norm² explicitly.
      have h_norm_sq :
          ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => r i n X)‖ ^ 2
            = ∑ i : Fin m, (r i n X) ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
        · simp [Real.norm_eq_abs, sq_abs]
        · exact Finset.sum_nonneg (fun _ _ => by positivity)
      -- So `ε² ≤ ‖·‖² = ∑ (r i)² < m · δ² = ε²`, contradiction.
      have h_le : ε ^ 2
          ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => r i n X)‖ ^ 2 := by
        have hε_le := hX
        have : ε ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => r i n X)‖ := hX
        have hε_nn : (0 : ℝ) ≤ ε := le_of_lt hε
        have h_norm_nn : (0 : ℝ) ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm
            (fun i => r i n X)‖ := norm_nonneg _
        nlinarith
      rw [h_norm_sq] at h_le
      have h_each : ∀ i : Fin m, (r i n X) ^ 2 < δ ^ 2 := by
        intro i
        have h := h_neg i
        have h1 : (0 : ℝ) ≤ |r i n X| := abs_nonneg _
        have h2 : |r i n X| ^ 2 < δ ^ 2 := by
          have : (0 : ℝ) ≤ δ := le_of_lt hδ_pos
          nlinarith
        rwa [sq_abs] at h2
      have h_sum_lt : ∑ i : Fin m, (r i n X) ^ 2 < m * δ ^ 2 := by
        have h_card : (Finset.univ : Finset (Fin m)).card = m := by
          rw [Finset.card_univ, Fintype.card_fin]
        rw [show (m : ℝ) * δ ^ 2 = ((Finset.univ : Finset (Fin m)).card : ℝ) * δ ^ 2 by
          rw [h_card]]
        haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        calc ∑ i : Fin m, (r i n X) ^ 2 < ∑ _i : Fin m, δ ^ 2 := by
              refine Finset.sum_lt_sum_of_nonempty ?_ (fun i _ => h_each i)
              exact Finset.univ_nonempty
            _ = ((Finset.univ : Finset (Fin m)).card : ℝ) * δ ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have h_eq : (m : ℝ) * δ ^ 2 = ε ^ 2 := by
        rw [hδ_def]
        field_simp
        rw [Real.sq_sqrt (Nat.cast_nonneg m)]
      linarith
    -- Subset: bad joint set ⊆ ⋃ i, bad i set at threshold δ.
    have h_subset : ∀ n,
        {X : Fin n → Ω
          | ε ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => r i n X)‖}
          ⊆ ⋃ i : Fin m, {X : Fin n → Ω | δ ≤ |r i n X|} := by
      intro n X hX
      rw [Set.mem_iUnion]
      exact h_norm_max n X hX
    -- Measure bound and union bound.
    have h_measure_bound : ∀ n,
        (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω
              | ε ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => r i n X)‖}
          ≤ ∑ i : Fin m, (Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω | δ ≤ |r i n X|} := by
      intro n
      calc (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω
              | ε ≤ ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => r i n X)‖}
          ≤ (Measure.pi (fun _ : Fin n => P))
              (⋃ i : Fin m, {X : Fin n → Ω | δ ≤ |r i n X|}) :=
            measure_mono (h_subset n)
        _ ≤ ∑ i : Fin m, (Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω | δ ≤ |r i n X|} := by
            exact MeasureTheory.measure_iUnion_fintype_le _ _
    -- Conclude: each summand → 0, sum → 0, squeeze.
    have h_sum_tendsto : Tendsto (fun n : ℕ => ∑ i : Fin m,
        (Measure.pi (fun _ : Fin n => P)) {X : Fin n → Ω | δ ≤ |r i n X|})
        atTop (𝓝 0) := by
      have h_each_tendsto : ∀ i : Fin m,
          Tendsto (fun n : ℕ =>
            (Measure.pi (fun _ : Fin n => P)) {X : Fin n → Ω | δ ≤ |r i n X|})
            atTop (𝓝 (0 : ℝ≥0∞)) := fun i => hr_zero i δ hδ_pos
      have := tendsto_finset_sum (Finset.univ : Finset (Fin m))
        (fun i _ => h_each_tendsto i)
      simpa using this
    -- Squeeze: `0 ≤ μ_n A ≤ ∑_i μ_n B_i → 0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum_tendsto
      (Eventually.of_forall (fun n => zero_le))
      (Eventually.of_forall h_measure_bound)

/-! ### Joint LAN factorization, reduced to a per-coordinate witness

`jointLAN_factorization` reduces to the existence of a *per-coordinate* LAN
factorization witness, packaged in `lan_factorization_witness_pi` below. The
coordinate-wise remainder is then bundled into an `EuclideanSpace`-valued joint
remainder by `EuclideanSpace.equiv` and `Pⁿ`-Pi norm bounds.
`lan_factorization_witness_pi` carries the LR-product-to-log-sum identity plus
the LAN expansion applied per-coordinate.
-/

/-! ### Sub-lemmas for `bridge_residue_to_witness_one` -/

/-- **Fisher-information identity.**

For any `QMDPath P` `γ_g` whose score is `g`, the Fisher information of
the induced 1-D `to1DParametricFamily γ_g` at parameter `0` and shift
`h' := single 0 1` equals `‖g‖²`.

Proof outline:
* `⟪h', score1D γ_g x⟫_ℝ = g x` (since `score1D γ_g x = single 0 (g x)`
  and `single 0 1` pairs with `single 0 a` to give `a`).
* `density 0 x = (P.rnDeriv γ_g.dominating x).toReal` (since
  `γ_g.curve 0 = P`).
* `MeasureTheory.integral_toReal_rnDeriv_mul` (with `μ := P`,
  `ν := γ_g.dominating`, `f := g²`) gives
  `∫ x, (P.rnDeriv γ_g.dominating x).toReal · g(x)² ∂γ_g.dominating
   = ∫ x, g(x)² ∂P`.
* `∫ g² dP = ‖g‖²` via `MeasureTheory.L2.inner_def` on `⟪g, g⟫ = ‖g‖²`. -/
lemma fisher_info_eq_score_norm_sq
    (g : ↥(L2ZeroMean P)) (γ_g : QMDPath P) (h_score : γ_g.score = g) :
    AsymptoticStatistics.fisherInformation
        (QMDPath.to1DParametricFamily γ_g) γ_g.dominating
        (0 : EuclideanSpace ℝ (Fin 1)) (QMDPath.score1D γ_g)
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
      = ‖(g : Lp ℝ 2 P)‖ ^ 2 := by
  classical
  set h' : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hh'
  -- Step 1: pointwise inner-product reduction.
  have h_inner_eq : ∀ x : Ω,
      (⟪h', QMDPath.score1D γ_g x⟫_ℝ : ℝ)
        = ((g : Lp ℝ 2 P) : Ω → ℝ) x := by
    intro x
    -- `score1D γ_g x = single 0 (γ_g.score x) = single 0 (g x)`.
    -- `⟪single 0 1, single 0 (g x)⟫ = g x`.
    have h_score_eq : ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x
        = ((g : Lp ℝ 2 P) : Ω → ℝ) x := by
      rw [h_score]
    -- Use the same inner-product reduction pattern as Abstract1DLAN.
    have h_inner :
        (⟪h', EuclideanSpace.single (0 : Fin 1)
            (((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x)⟫_ℝ : ℝ)
          = ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x * h' 0 := by
      rw [PiLp.inner_apply, Fin.sum_univ_one]
      have h_single : EuclideanSpace.single (0 : Fin 1)
          (((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x) (0 : Fin 1)
            = ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x := by simp
      rw [h_single]
      change ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x * h' 0
          = ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x * h' 0
      rfl
    have h_h'0 : h' 0 = (1 : ℝ) := by simp [hh']
    change (⟪h', EuclideanSpace.single (0 : Fin 1)
            (((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x)⟫_ℝ : ℝ) = _
    rw [h_inner, h_h'0, mul_one, h_score_eq]
  -- Step 2: density 0 x = (P.rnDeriv γ_g.dominating x).toReal.
  have h_density_eq : ∀ x,
      (QMDPath.to1DParametricFamily γ_g).density 0 x
        = ((P.rnDeriv γ_g.dominating) x).toReal := by
    intro x
    change (((γ_g.curve ((0 : EuclideanSpace ℝ (Fin 1)) 0)).rnDeriv
            γ_g.dominating x).toReal : ℝ) = _
    have h_zero_apply : ((0 : EuclideanSpace ℝ (Fin 1)) 0) = 0 := rfl
    rw [h_zero_apply, γ_g.curve_at_zero]
  -- Step 3: rewrite the integrand pointwise.
  unfold AsymptoticStatistics.fisherInformation
  have h_pointwise : ∀ x,
      (⟪h', QMDPath.score1D γ_g x⟫_ℝ * ⟪h', QMDPath.score1D γ_g x⟫_ℝ)
            * (QMDPath.to1DParametricFamily γ_g).density 0 x
        = ((P.rnDeriv γ_g.dominating) x).toReal
            * (((g : Lp ℝ 2 P) : Ω → ℝ) x) ^ 2 := by
    intro x
    rw [h_inner_eq x, h_density_eq x, sq]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_pointwise)]
  -- Step 4: apply `integral_toReal_rnDeriv_mul`.
  have hP_ac : P ≪ γ_g.dominating := by
    have := γ_g.curve_absContinuous 0
    rw [γ_g.curve_at_zero] at this
    exact this
  rw [MeasureTheory.integral_toReal_rnDeriv_mul hP_ac]
  -- Step 5: ∫ g² dP = ‖g‖² via L².inner_def.
  have h_inner_self :
      (⟪(g : Lp ℝ 2 P), (g : Lp ℝ 2 P)⟫_ℝ : ℝ) = ‖(g : Lp ℝ 2 P)‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  rw [MeasureTheory.L2.inner_def] at h_inner_self
  have h_pt_sq :
      (fun x => (⟪((g : Lp ℝ 2 P) : Ω → ℝ) x,
                   ((g : Lp ℝ 2 P) : Ω → ℝ) x⟫_ℝ : ℝ))
        =ᵐ[P] fun x => ((g : Lp ℝ 2 P) : Ω → ℝ) x ^ 2 := by
    filter_upwards with x
    change ((g : Lp ℝ 2 P) : Ω → ℝ) x * ((g : Lp ℝ 2 P) : Ω → ℝ) x = _
    ring
  rw [integral_congr_ae h_pt_sq] at h_inner_self
  exact h_inner_self

/-- **`Pⁿ`-AE positivity and finiteness of `lr_n`.**

Positivity and finiteness of `(γ_g.curve(1/√n)).rnDeriv γ_g.dominating` *under
the law `P`*. The `QMDPath` structure ships
`curve_absContinuous : ∀ t, curve t ≪ dominating`, which by
`Measure.rnDeriv_lt_top` gives finiteness `dominating`-a.e. and hence (since
`P ≪ dominating`) `P`-a.e. Positivity requires `P ≪ curve t` for `t ≠ 0`, which
is not a structural field of `QMDPath`, so it enters as the hypothesis `hAC`.

Proof: `Measure.rnDeriv_pos` on `(curve t)` w.r.t. `dominating` gives
`(curve t)`-a.e. positivity of `(curve t).rnDeriv dominating`; lift to `P`-a.e.
via `hAC`; combine with `Measure.rnDeriv_lt_top` for finiteness; lift each
coordinate to `Pⁿ`-a.e. via `tendsto_eval_ae_ae` + `ae_all_iff`. -/
private lemma lr_n_pos_finite_ae_pi
    (γ_g : QMDPath P) (n : ℕ)
    -- vdV §25 standing for the dominated case. Required to lift
    -- `(curve t)`-a.e. positivity of `rnDeriv` to `P`-a.e., then to
    -- `Pⁿ`-a.e. via the per-coord `tendsto_eval_ae_ae`.
    (hAC : P ≪ γ_g.curve ((Real.sqrt n)⁻¹)) :
    ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
      (∀ j : Fin n,
        0 < (γ_g.curve ((Real.sqrt n)⁻¹)).rnDeriv γ_g.dominating (X j)
        ∧ (γ_g.curve ((Real.sqrt n)⁻¹)).rnDeriv γ_g.dominating (X j) < ⊤) := by
  -- Auto-instance for HaveLebesgueDecomposition (curve t) dominating
  -- via SigmaFinite (curve t) [from IsProbabilityMeasure] +
  -- SigmaFinite dominating [from QMDPath.dominating_sigmaFinite].
  haveI _hCurveProb : IsProbabilityMeasure (γ_g.curve ((Real.sqrt n)⁻¹)) :=
    γ_g.curve_isProbability _
  haveI _hCurveSF : SigmaFinite (γ_g.curve ((Real.sqrt n)⁻¹)) := by infer_instance
  haveI _hDomSF : SigmaFinite γ_g.dominating := γ_g.dominating_sigmaFinite
  -- Step 1: `(curve t) ≪ γ_g.dominating` from QMDPath.curve_absContinuous.
  have h_curve_ac : γ_g.curve ((Real.sqrt n)⁻¹) ≪ γ_g.dominating :=
    γ_g.curve_absContinuous _
  -- Step 2: `(curve t)`-a.e. positivity of `(curve t).rnDeriv dominating`.
  have h_pos_curve : ∀ᵐ ω ∂(γ_g.curve ((Real.sqrt n)⁻¹)),
      0 < (γ_g.curve ((Real.sqrt n)⁻¹)).rnDeriv γ_g.dominating ω :=
    Measure.rnDeriv_pos h_curve_ac
  -- Step 3: Lift to `P`-a.e. via `hAC : P ≪ curve t`.
  have h_pos_P : ∀ᵐ ω ∂P,
      0 < (γ_g.curve ((Real.sqrt n)⁻¹)).rnDeriv γ_g.dominating ω :=
    hAC.ae_le h_pos_curve
  -- Step 4: `(γ_g.dominating)`-a.e. finiteness via `Measure.rnDeriv_lt_top`.
  -- Lift to `P`-a.e. via `P ≪ γ_g.dominating` (from `curve_absContinuous 0`
  -- + `curve_at_zero`).
  have h_P_ac_dom : P ≪ γ_g.dominating := by
    have h := γ_g.curve_absContinuous 0
    rw [γ_g.curve_at_zero] at h
    exact h
  have h_lt_top_P : ∀ᵐ ω ∂P,
      (γ_g.curve ((Real.sqrt n)⁻¹)).rnDeriv γ_g.dominating ω < ⊤ :=
    h_P_ac_dom.ae_le (Measure.rnDeriv_lt_top _ γ_g.dominating)
  -- Step 5: Combine pos + lt_top into `P`-a.e. conjunction.
  have h_P_ae : ∀ᵐ ω ∂P,
      0 < (γ_g.curve ((Real.sqrt n)⁻¹)).rnDeriv γ_g.dominating ω
      ∧ (γ_g.curve ((Real.sqrt n)⁻¹)).rnDeriv γ_g.dominating ω < ⊤ := by
    filter_upwards [h_pos_P, h_lt_top_P] with ω h1 h2
    exact ⟨h1, h2⟩
  -- Step 6: Lift `P`-a.e. (per coord) to `Pⁿ`-a.e. via
  -- `tendsto_eval_ae_ae` + `ae_all_iff`.
  rw [ae_all_iff]
  intro j
  have h_tendsto :
      Filter.Tendsto (fun X : Fin n → Ω => X j)
        (MeasureTheory.ae (MeasureTheory.Measure.pi (fun _ : Fin n => P)))
        (MeasureTheory.ae P) :=
    MeasureTheory.Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P) (i := j)
  exact h_tendsto.eventually h_P_ae

/-- **Sum of `log p_0` is `Pⁿ`-AE zero.**

The `QMDPath` structure does not enforce `dominating = P`. When
`dominating ≠ P`, the density `p_0(ω) := (P.rnDeriv γ_g.dominating ω).toReal`
is generically `≠ 1` on a `P`-positive set, so `Σⱼ log p_0(X j)` is not
`Pⁿ`-a.e. zero; hence the hypothesis `hDom : dominating = P`.

With `dominating = P`: `P.rnDeriv P = 1` `P`-a.e. by `rnDeriv_self`, so
`p_0 = 1` `P`-a.e., so `log p_0 = 0` `P`-a.e., hence `Pⁿ`-a.e. -/
private lemma sum_log_p_0_zero_ae_pi
    (γ_g : QMDPath P) (n : ℕ)
    -- dominated case; otherwise `Σⱼ log p_0(X j)` is generically
    -- nonzero on a `P`-positive set.
    (hDom : γ_g.dominating = P) :
    ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
      ∑ j : Fin n,
        Real.log ((P.rnDeriv γ_g.dominating (X j)).toReal) = 0 := by
  -- With `γ_g.dominating = P`: `P.rnDeriv P = 1` `P`-a.e. by
  -- `Measure.rnDeriv_self`, so `log 1 = 0` and the sum collapses.
  have h_rnDeriv_eq_one : ∀ᵐ ω ∂P, P.rnDeriv γ_g.dominating ω = 1 := by
    rw [hDom]
    exact Measure.rnDeriv_self P
  -- Lift `P`-AE per coord to `Pⁿ`-AE via `tendsto_eval_ae_ae`.
  have h_per_coord :
      ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
        ∀ j : Fin n, P.rnDeriv γ_g.dominating (X j) = 1 := by
    rw [ae_all_iff]
    intro j
    have h_tendsto :
        Filter.Tendsto (fun X : Fin n → Ω => X j)
          (MeasureTheory.ae (MeasureTheory.Measure.pi (fun _ : Fin n => P)))
          (MeasureTheory.ae P) :=
      MeasureTheory.Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P) (i := j)
    exact h_tendsto.eventually h_rnDeriv_eq_one
  filter_upwards [h_per_coord] with X hX
  simp only [hX, ENNReal.toReal_one, Real.log_one, Finset.sum_const_zero]

/-- **`Pⁿ`-AE positivity and finiteness of `p_0`.**

For the `log a − log b = log(a/b)` identity to hold pointwise on the
AE-good set in the `r → 0` decomposition, we need `p_0(ω) > 0`
`P`-a.e. (AE positivity of the rnDeriv at `θ = 0`).

Proof:
* `hP_ac : P ≪ γ_g.dominating` from `curve_absContinuous 0 + curve_at_zero`.
* `Measure.rnDeriv_pos hP_ac : 0 < P.rnDeriv γ_g.dominating` `P`-a.e.
* `Measure.rnDeriv_lt_top` gives `< ⊤` `γ_g.dominating`-a.e., hence
  `P`-a.e. (since `P ≪ γ_g.dominating`).
* Lift `P`-a.e. ⇒ `Pⁿ`-a.e. via `Measure.tendsto_eval_ae_ae` per coordinate,
  combining over `j : Fin n` via `ae_all_iff`. -/
private lemma p_0_pos_finite_ae_pi
    (γ_g : QMDPath P) (n : ℕ) :
    ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
      ∀ j : Fin n,
        0 < P.rnDeriv γ_g.dominating (X j)
        ∧ P.rnDeriv γ_g.dominating (X j) < ⊤ := by
  -- Step 1: `P ≪ γ_g.dominating` from the QMDPath structure
  -- (`curve_at_zero` + `curve_absContinuous 0`).
  have h_P_ac : P ≪ γ_g.dominating := by
    have h := γ_g.curve_absContinuous 0
    rw [γ_g.curve_at_zero] at h
    exact h
  -- Step 2: `P`-AE positivity + finiteness of the rnDeriv.
  have h_P_ae : ∀ᵐ ω ∂P,
      0 < P.rnDeriv γ_g.dominating ω
      ∧ P.rnDeriv γ_g.dominating ω < ⊤ := by
    have h_pos : ∀ᵐ ω ∂P, 0 < P.rnDeriv γ_g.dominating ω :=
      Measure.rnDeriv_pos h_P_ac
    have h_lt_top : ∀ᵐ ω ∂P, P.rnDeriv γ_g.dominating ω < ⊤ :=
      h_P_ac.ae_le (Measure.rnDeriv_lt_top P γ_g.dominating)
    filter_upwards [h_pos, h_lt_top] with ω h1 h2
    exact ⟨h1, h2⟩
  -- Step 3: Lift `P`-AE (per coord) to `Pⁿ`-AE (joint), then combine
  -- over all `j : Fin n` via `ae_all_iff`.
  rw [ae_all_iff]
  intro j
  -- Lift `P`-AE on coordinate `j` to `Pⁿ`-AE via `tendsto_eval_ae_ae`.
  have h_tendsto :
      Filter.Tendsto (fun X : Fin n → Ω => X j)
        (MeasureTheory.ae (MeasureTheory.Measure.pi (fun _ : Fin n => P)))
        (MeasureTheory.ae P) :=
    MeasureTheory.Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P) (i := j)
  exact h_tendsto.eventually h_P_ae

/-- **Bridge-output → witness-shape transformer.**

Supplies the mathematical content of `lan_factorization_witness_one`. The body
composes:

* `lanExpansion1D`: gives a `TendstoInMeasure` on `infinitePi P` for the
  LAN expression at `γ_g`.
* `pi_meas_eq_infinitePi_meas_of_truncate`: transports `TendstoInMeasure`
  from `infinitePi P` to `Pⁿ`.
* `fisher_info_eq_score_norm_sq`: identifies `I_{γ_g}(h', h') = ‖g‖²`.
* `lr_n_pos_finite_ae_pi`: provides `Pⁿ`-AE positivity + finiteness for the
  factorization step.
* `sum_log_p_0_zero_ae_pi`: provides `Σⱼ log p_0(X j) = 0` `Pⁿ`-a.e.

The witness is `r n X := Real.log (γ_g.lr_n n X).toReal − scoreSumScalar
g n X + ½‖g‖²`. Algebraically, on the AE-positive-and-finite set,

```
r n X − lanRemainder n X = Σⱼ Real.log p_0(X j) + ½(‖g‖² − I_{γ_g}(h',h'))
                        = 0 + 0 = 0  Pⁿ-a.e.
```

so `r → 0` follows from `lanRemainder → 0`. -/
private lemma bridge_residue_to_witness_one
    (g : ↥(L2ZeroMean P)) (γ_g : QMDPath P) (h_score : γ_g.score = g)
    -- `sum_log_p_0_zero_ae_pi` to collapse `Σⱼ log p_0(X j) = 0` Pⁿ-a.e.
    (hDom : γ_g.dominating = P)
    -- `lr_n_pos_finite_ae_pi` to lift `(curve t)`-a.e. positivity to `P`-a.e.
    (hAC : ∀ n, P ≪ γ_g.curve ((Real.sqrt n)⁻¹)) :
    ∃ r : (n : ℕ) → (Fin n → Ω) → ℝ,
      (∀ n, Measurable (r n)) ∧
      (∀ n,
        (fun X : Fin n → Ω => γ_g.lr_n n X)
          =ᵐ[Measure.pi (fun _ : Fin n => P)]
          (fun X : Fin n → Ω =>
            ENNReal.ofReal (Real.exp
              (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                  (P := P) g n X
                - (1/2 : ℝ) * ‖(g : Lp ℝ 2 P)‖ ^ 2
                + r n X)))) ∧
      (∀ ε > 0,
        Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε ≤ |r n X|})
          atTop (𝓝 (0 : ℝ≥0∞))) := by
  classical
  -- Set the witness.
  let r : (n : ℕ) → (Fin n → Ω) → ℝ := fun n X =>
    Real.log (γ_g.lr_n n X).toReal
      - AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
          (P := P) g n X
      + (1/2 : ℝ) * ‖(g : Lp ℝ 2 P)‖ ^ 2
  have hr_def : ∀ n X, r n X = Real.log (γ_g.lr_n n X).toReal
        - AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
            (P := P) g n X
        + (1/2 : ℝ) * ‖(g : Lp ℝ 2 P)‖ ^ 2 := fun _ _ => rfl
  refine ⟨r, ?_, ?_, ?_⟩
  · -- Measurability of `r n`.
    intro n
    refine ((Measurable.log ?_).sub ?_).add measurable_const
    · exact ((QMDPath.measurable_lr_n γ_g n).ennreal_toReal)
    · exact AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.measurable_scoreSumScalar g n
  · -- Factorization (point 2).
    intro n
    -- On the Pⁿ-AE set where each rnDeriv is positive and finite,
    -- `lr_n n X = ENNReal.ofReal (lr_n n X).toReal` and
    -- `Real.exp (Real.log (lr_n n X).toReal) = (lr_n n X).toReal`.
    filter_upwards [lr_n_pos_finite_ae_pi (P := P) γ_g n (hAC n)] with X hX
    -- `(lr_n n X).toReal > 0` from product of positive finite reals.
    have h_lr_pos : (0 : ℝ) < (γ_g.lr_n n X).toReal := by
      rw [QMDPath.lr_n_eq]
      rw [ENNReal.toReal_prod]
      refine Finset.prod_pos (fun j _ => ?_)
      have hj := (hX j).1
      have hj_lt := (hX j).2
      exact ENNReal.toReal_pos hj.ne' hj_lt.ne
    have h_lr_lt : (γ_g.lr_n n X) ≠ ⊤ := by
      rw [QMDPath.lr_n_eq]
      refine ENNReal.prod_ne_top fun j _ => ?_
      exact (hX j).2.ne
    -- exp(scoreSumScalar - ½‖g‖² + r n X) = exp(log lr_n.toReal) = lr_n.toReal.
    have h_arg :
        AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
            (P := P) g n X
          - (1/2 : ℝ) * ‖(g : Lp ℝ 2 P)‖ ^ 2 + r n X
          = Real.log (γ_g.lr_n n X).toReal := by
      rw [hr_def]; ring
    rw [h_arg, Real.exp_log h_lr_pos]
    rw [ENNReal.ofReal_toReal h_lr_lt]
  · -- `r → 0` in Pⁿ-probability (point 3).
    -- Strategy: write `r = lanRemainderTerm + (corrections vanishing Pⁿ-a.e.)`,
    -- where `lanRemainderTerm → 0` by `lanExpansion1D` + truncate transport.
    -- We work with the `lanExpansion1D` output expression directly (not via
    -- the private bridge). Boilerplate adapted from
    -- `T6_FinDimLAN/LANexpansion.lean::lanExpansion1D_to_PnProb_bridge`.
    set h' : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hh'_def
    set P' : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hP'_def
    haveI : IsProbabilityMeasure P' := by rw [hP'_def]; infer_instance
    set X' : ℕ → (ℕ → Ω) → Ω := fun i ω => ω i with hX'_def
    have hX'_meas : ∀ i, Measurable (X' i) := fun i => measurable_pi_apply i
    -- iid setup boilerplate (cf. lanExpansion1D_to_PnProb_bridge body).
    have hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X' i) (X' j) P' := by
      have h_iindep :
          ProbabilityTheory.iIndepFun (fun i ω => (id : Ω → Ω) (ω i))
            (Measure.infinitePi (fun _ : ℕ => P)) :=
        ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
      intro i j hij
      exact h_iindep.indepFun hij
    have hX'_map : ∀ i, Measure.map (X' i) P' = P := by
      intro i
      rw [hX'_def, hP'_def]
      exact MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => P) i
    have hident : ∀ i, ProbabilityTheory.IdentDistrib (X' i) (X' 0) P' P' := by
      intro i
      refine ⟨(hX'_meas i).aemeasurable, (hX'_meas 0).aemeasurable, ?_⟩
      rw [hX'_map i, hX'_map 0]
    -- Law-as-density boilerplate.
    have hlaw_target_eq :
        γ_g.dominating.withDensity
            (fun x => ENNReal.ofReal
              ((QMDPath.to1DParametricFamily γ_g).density 0 x))
          = P := by
      haveI hac : P ≪ γ_g.dominating := by
        have := γ_g.curve_absContinuous 0
        rw [γ_g.curve_at_zero] at this
        exact this
      have h_density_eq : ∀ x,
          (QMDPath.to1DParametricFamily γ_g).density 0 x
            = ((P.rnDeriv γ_g.dominating) x).toReal := by
        intro x
        change ((γ_g.curve 0).rnDeriv γ_g.dominating x).toReal = _
        rw [γ_g.curve_at_zero]
      have h_ae_eq :
          (fun x => ENNReal.ofReal
              ((QMDPath.to1DParametricFamily γ_g).density 0 x))
            =ᵐ[γ_g.dominating]
          (P.rnDeriv γ_g.dominating) := by
        filter_upwards [Measure.rnDeriv_lt_top P γ_g.dominating] with x hx
        rw [h_density_eq x, ENNReal.ofReal_toReal hx.ne]
      rw [MeasureTheory.withDensity_congr_ae h_ae_eq,
        Measure.withDensity_rnDeriv_eq P γ_g.dominating hac]
    have hlaw : Measure.map (X' 0) P'
        = γ_g.dominating.withDensity
            (fun x => ENNReal.ofReal
              ((QMDPath.to1DParametricFamily γ_g).density 0 x)) := by
      rw [hX'_map 0]; exact hlaw_target_eq.symm
    -- Score measurability.
    have hℓ_meas : Measurable (QMDPath.score1D γ_g) := by
      have h_score_sm : StronglyMeasurable
          (fun ω => ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) ω) :=
        Lp.stronglyMeasurable _
      have h_inner_meas : Measurable
          (fun ω => ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) ω) :=
        h_score_sm.measurable
      have h_single_cont :
          Continuous (fun a : ℝ => EuclideanSpace.single (0 : Fin 1) a) := by
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
        have h_eq :
            (fun a : ℝ => EuclideanSpace.single (0 : Fin 1) a)
              = (fun y : Fin 1 → ℝ =>
                  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 => ℝ)).symm y)
                ∘ (fun a : ℝ => (Pi.single (0 : Fin 1) a : Fin 1 → ℝ)) := by
          funext a; simp
        rw [h_eq]
        exact (PiLp.continuousLinearEquiv 2 ℝ
                (fun _ : Fin 1 => ℝ)).symm.continuous.comp h_pi_single
      exact h_single_cont.measurable.comp h_inner_meas
    -- Apply lanExpansion1D.
    have h_const_tendsto : Tendsto (fun _ : ℕ => h') atTop (𝓝 h') := tendsto_const_nhds
    have hLAN := AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.lanExpansion1D
      γ_g h' (fun _ : ℕ => h') h_const_tendsto P' X' hX'_meas hindep hident hlaw hℓ_meas
    -- Define `F n ω` to be the lanExpansion1D output:
    set F : ℕ → (ℕ → Ω) → ℝ := fun n ω =>
      (∑ i ∈ Finset.range n,
          Real.log
            ((QMDPath.to1DParametricFamily γ_g).density
                (0 + (Real.sqrt n)⁻¹ • h') (X' i ω) /
              (QMDPath.to1DParametricFamily γ_g).density 0 (X' i ω)))
      - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
          @inner ℝ _ _ h' (QMDPath.score1D γ_g (X' i ω))
      + (1/2 : ℝ) *
        AsymptoticStatistics.fisherInformation
          (QMDPath.to1DParametricFamily γ_g) γ_g.dominating 0
          (QMDPath.score1D γ_g) h' h' with hF_def
    -- hLAN says F → 0 in P'-measure.
    have hLAN' : TendstoInMeasure P' F atTop (fun _ => (0 : ℝ)) := hLAN
    -- Per-n algebraic identity: under Pⁿ-AE good set, `r n (truncate ω) = F n ω`.
    -- Goal: ∀ ε > 0, Tendsto (Pⁿ {ε ≤ |r n X|}) atTop (𝓝 0).
    intro ε hε
    -- Define F' n ω := r n (truncate ω). This relates to F n ω via
    -- `F n ω = F' n ω - Σⱼ log p_0(X' j ω) + ½(I - ‖g‖²)`.
    -- After applying B2c (Fisher-info = ‖g‖²) and B2b (sum of log p_0 = 0 P-a.e.),
    -- we get `F n ω = F' n ω` Pⁿ-a.e.
    -- Approach: show `Pⁿ {ε ≤ |r n X|} ≤ Pⁿ {ε ≤ |F n (extend X)|} + 0`,
    -- equivalently work via TendstoInMeasure on `F'`.
    -- 1. `F'` measurable.
    have hr_meas_n : ∀ n, Measurable (r n) := by
      intro n
      refine ((Measurable.log ?_).sub ?_).add measurable_const
      · exact (QMDPath.measurable_lr_n γ_g n).ennreal_toReal
      · exact AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.measurable_scoreSumScalar g n
    -- 2. Prove the per-`n` *Pⁿ-AE* identity `F n ω = r n (truncate ω)` for the
    --    specific `n`. Use B2a, B2b, B2c.
    have hF_eq_r : ∀ k : ℕ, (fun ω : ℕ → Ω => F k ω)
        =ᵐ[P']
        (fun ω : ℕ → Ω => r k (fun j : Fin k => ω j.val)) := by
      intro k
      -- Pull all 4 AE properties from the sub-lemmas above.
      have hpos_pi : ∀ᵐ X : Fin k → Ω ∂(Measure.pi (fun _ : Fin k => P)),
          ∀ j : Fin k,
            0 < (γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (X j)
            ∧ (γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (X j) < ⊤ :=
        lr_n_pos_finite_ae_pi (P := P) γ_g k (hAC k)
      have hp0_zero_pi : ∀ᵐ X : Fin k → Ω ∂(Measure.pi (fun _ : Fin k => P)),
          ∑ j : Fin k,
            Real.log ((P.rnDeriv γ_g.dominating (X j)).toReal) = 0 :=
        sum_log_p_0_zero_ae_pi (P := P) γ_g k hDom
      have hp0_pos_pi : ∀ᵐ X : Fin k → Ω ∂(Measure.pi (fun _ : Fin k => P)),
          ∀ j : Fin k,
            0 < P.rnDeriv γ_g.dominating (X j)
            ∧ P.rnDeriv γ_g.dominating (X j) < ⊤ :=
        p_0_pos_finite_ae_pi (P := P) γ_g k
      -- Truncate-pushforward rewrite of the Pⁿ-AE properties to P'-AE properties.
      have h_truncate_eq :
          (Measure.pi (fun _ : Fin k => P))
            = P'.map (fun ω : ℕ → Ω => fun j : Fin k => ω j.val) := by
        rw [hP'_def]
        exact AsymptoticStatistics.pi_const_eq_infinitePi_map P k
      have h_trunc_meas : Measurable
          (fun ω : ℕ → Ω => fun j : Fin k => ω j.val) :=
        measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
      -- Measurability of the relevant sets.
      have hpos_set_meas : MeasurableSet
          {x : Fin k → Ω |
            ∀ j : Fin k,
              0 < (γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (x j)
              ∧ (γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (x j) < ⊤} := by
        rw [Set.setOf_forall]
        refine MeasurableSet.iInter fun j => ?_
        refine MeasurableSet.inter ?_ ?_
        · exact measurableSet_lt measurable_const
            ((Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply j))
        · exact measurableSet_lt
            ((Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply j))
            measurable_const
      have hp0_zero_set_meas : MeasurableSet
          {x : Fin k → Ω |
            ∑ j : Fin k, Real.log ((P.rnDeriv γ_g.dominating (x j)).toReal) = 0} := by
        apply measurableSet_eq_fun
        · exact Finset.measurable_sum _ (fun j _ =>
            ((Measure.measurable_rnDeriv _ _).comp
              (measurable_pi_apply j)).ennreal_toReal.log)
        · exact measurable_const
      have hp0_pos_set_meas : MeasurableSet
          {x : Fin k → Ω | ∀ j : Fin k,
            0 < P.rnDeriv γ_g.dominating (x j)
            ∧ P.rnDeriv γ_g.dominating (x j) < ⊤} := by
        rw [Set.setOf_forall]
        refine MeasurableSet.iInter fun j => ?_
        refine MeasurableSet.inter ?_ ?_
        · exact measurableSet_lt measurable_const
            ((Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply j))
        · exact measurableSet_lt
            ((Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply j))
            measurable_const
      -- P'-AE versions.
      have hpos_P' : ∀ᵐ ω : ℕ → Ω ∂P',
          ∀ j : Fin k,
            0 < (γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (ω j.val)
            ∧ (γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (ω j.val) < ⊤ := by
        rw [h_truncate_eq] at hpos_pi
        exact (ae_map_iff h_trunc_meas.aemeasurable hpos_set_meas).mp hpos_pi
      have hp0_zero_P' : ∀ᵐ ω : ℕ → Ω ∂P',
          ∑ j : Fin k,
            Real.log ((P.rnDeriv γ_g.dominating (ω j.val)).toReal) = 0 := by
        rw [h_truncate_eq] at hp0_zero_pi
        exact (ae_map_iff h_trunc_meas.aemeasurable hp0_zero_set_meas).mp hp0_zero_pi
      have hp0_pos_P' : ∀ᵐ ω : ℕ → Ω ∂P',
          ∀ j : Fin k,
            0 < P.rnDeriv γ_g.dominating (ω j.val)
            ∧ P.rnDeriv γ_g.dominating (ω j.val) < ⊤ := by
        rw [h_truncate_eq] at hp0_pos_pi
        exact (ae_map_iff h_trunc_meas.aemeasurable hp0_pos_set_meas).mp hp0_pos_pi
      filter_upwards [hpos_P', hp0_zero_P', hp0_pos_P'] with ω hpos hp0_zero hp0_pos
      -- Inner product reduction.
      have h_inner_pt : ∀ x : Ω,
          (@inner ℝ _ _ h' (QMDPath.score1D γ_g x) : ℝ)
            = ((g : Lp ℝ 2 P) : Ω → ℝ) x := by
        intro x
        have h_score_eq : ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x
            = ((g : Lp ℝ 2 P) : Ω → ℝ) x := by rw [h_score]
        have h_inner :
            (@inner ℝ _ _ h' (EuclideanSpace.single (0 : Fin 1)
                (((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x)) : ℝ)
              = ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x * h' 0 := by
          rw [PiLp.inner_apply, Fin.sum_univ_one]
          have h_single : EuclideanSpace.single (0 : Fin 1)
              (((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x) (0 : Fin 1)
                = ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x := by simp
          rw [h_single]
          change ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x * h' 0
              = ((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x * h' 0
          rfl
        have h_h'0 : h' 0 = (1 : ℝ) := by simp [hh'_def]
        change (@inner ℝ _ _ h' (EuclideanSpace.single (0 : Fin 1)
            (((γ_g.score : Lp ℝ 2 P) : Ω → ℝ) x)) : ℝ) = _
        rw [h_inner, h_h'0, mul_one, h_score_eq]
      -- Density form.
      have h_density_form : ∀ x : Ω,
          (QMDPath.to1DParametricFamily γ_g).density (0 + (Real.sqrt k)⁻¹ • h') x
            = ((γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating x).toReal := by
        intro x
        have h_apply : (0 + (Real.sqrt k)⁻¹ • h') 0 = (Real.sqrt k)⁻¹ := by
          simp [hh'_def, EuclideanSpace.single]
        change ((γ_g.curve ((0 + (Real.sqrt k)⁻¹ • h') 0)).rnDeriv γ_g.dominating x).toReal = _
        rw [h_apply]
      have h_density_zero : ∀ x : Ω,
          (QMDPath.to1DParametricFamily γ_g).density 0 x
            = ((P.rnDeriv γ_g.dominating) x).toReal := by
        intro x
        change ((γ_g.curve ((0 : EuclideanSpace ℝ (Fin 1)) 0)).rnDeriv
                γ_g.dominating x).toReal = _
        have h_zero_apply : ((0 : EuclideanSpace ℝ (Fin 1)) 0) = 0 := rfl
        rw [h_zero_apply, γ_g.curve_at_zero]
      -- Now compute F k ω and r k (truncate ω) and equate them.
      -- F k ω uses Finset.range k indexing; r uses Fin k. Reindex via
      -- Fin.sum_univ_eq_sum_range.
      simp only [hF_def, hr_def]
      have h_fisher := fisher_info_eq_score_norm_sq (P := P) g γ_g h_score
      rw [h_fisher]
      unfold AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
      -- Step 1: rewrite each `density(0 + (1/√k) • h')(X' i ω) / density 0 (X' i ω)`
      --   = (γ_g.curve((1/√k)).rnDeriv γ_g.dominating (ω i)).toReal /
      --     (P.rnDeriv γ_g.dominating (ω i)).toReal
      -- Step 2: split the log into a difference (using positivity of both factors).
      -- Step 3: collect Σ log of the p_t parts into log((γ_g.lr_n k _).toReal).
      -- Step 4: cancel Σ log of the p_0 parts via hp0_zero.
      -- Step 5: convert (1/√k) · Σ_{Fin k} score-inner to (1/√k) · Σ_{range k} g(ω i).
      -- All collapsed in a final `linarith`/`ring` closer.
      have h_pos_t : ∀ i ∈ Finset.range k,
          (0 : ℝ) < ((γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (ω i)).toReal := by
        intro i hi
        rw [Finset.mem_range] at hi
        let j : Fin k := ⟨i, hi⟩
        have hp := hpos j
        exact ENNReal.toReal_pos hp.1.ne' hp.2.ne
      have h_pos_0 : ∀ i ∈ Finset.range k,
          (0 : ℝ) < ((P.rnDeriv γ_g.dominating) (ω i)).toReal := by
        intro i hi
        rw [Finset.mem_range] at hi
        let j : Fin k := ⟨i, hi⟩
        have hp := hp0_pos j
        exact ENNReal.toReal_pos hp.1.ne' hp.2.ne
      have h_log_split :
          (∑ i ∈ Finset.range k,
              Real.log
                ((QMDPath.to1DParametricFamily γ_g).density
                    (0 + (Real.sqrt k)⁻¹ • h') (X' i ω) /
                  (QMDPath.to1DParametricFamily γ_g).density 0 (X' i ω)))
            = (∑ i ∈ Finset.range k,
                Real.log
                  ((γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (ω i)).toReal)
              - (∑ i ∈ Finset.range k,
                  Real.log ((P.rnDeriv γ_g.dominating (ω i)).toReal)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hX'app : X' i ω = ω i := rfl
        rw [hX'app, h_density_form, h_density_zero]
        rw [Real.log_div (h_pos_t i hi).ne' (h_pos_0 i hi).ne']
      rw [h_log_split]
      -- Σ log p_0 = 0 from hp0_zero (Fin k → range k reindex).
      have h_p0_sum_range :
          ∑ i ∈ Finset.range k,
            Real.log ((P.rnDeriv γ_g.dominating (ω i)).toReal) = 0 := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun i => Real.log ((P.rnDeriv γ_g.dominating (ω i)).toReal))]
        exact hp0_zero
      rw [h_p0_sum_range]
      -- Σ inner = Σ g(ω i).
      have h_sum_inner :
          (∑ i ∈ Finset.range k,
              @inner ℝ _ _ h' (QMDPath.score1D γ_g (X' i ω)))
            = ∑ i ∈ Finset.range k, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hX'app : X' i ω = ω i := rfl
        rw [hX'app]
        exact h_inner_pt _
      rw [h_sum_inner]
      -- log(γ_g.lr_n k (truncate ω)).toReal = Σ_{range k} log p_t.
      have h_lr_log : Real.log (γ_g.lr_n k (fun j : Fin k => ω j.val)).toReal
          = ∑ i ∈ Finset.range k,
              Real.log
                ((γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (ω i)).toReal := by
        rw [QMDPath.lr_n_eq, ENNReal.toReal_prod]
        rw [Real.log_prod]
        · rw [Fin.sum_univ_eq_sum_range
            (fun i => Real.log
              ((γ_g.curve ((Real.sqrt k)⁻¹)).rnDeriv γ_g.dominating (ω i)).toReal)]
        · intro j _
          refine (ENNReal.toReal_pos ?_ ?_).ne'
          · exact (hpos j).1.ne'
          · exact (hpos j).2.ne
      -- scoreSumScalar reindex.
      have h_score_sum_eq :
          (Real.sqrt k)⁻¹ * ∑ j : Fin k, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω j.val)
            = (Real.sqrt k)⁻¹ * ∑ i ∈ Finset.range k, ((g : Lp ℝ 2 P) : Ω → ℝ) (ω i) := by
        congr 1
        rw [Fin.sum_univ_eq_sum_range (fun i => ((g : Lp ℝ 2 P) : Ω → ℝ) (ω i))]
      rw [← h_lr_log, ← h_score_sum_eq]
      ring
    -- 3. Now apply transport: show `r n ∘ truncate → 0` in P'-measure
    -- (from F → 0 + AE-equality), then transport to Pⁿ.
    have hF'_zero : TendstoInMeasure P'
        (fun n ω => r n (fun j : Fin n => ω j.val)) atTop (fun _ => (0 : ℝ)) := by
      intro δ hδ
      have h_F_at_δ := hLAN' δ hδ
      -- The set `{ω | δ ≤ edist (F k ω) 0}` and `{ω | δ ≤ edist (r k (truncate ω)) 0}`
      -- have the same P'-measure (AE equality of F k = r k ∘ truncate).
      have h_set_ae : ∀ k,
          P' {ω | δ ≤ edist (F k ω) (0 : ℝ)}
            = P' {ω | δ ≤ edist (r k (fun j : Fin k => ω j.val)) (0 : ℝ)} := by
        intro k
        apply measure_congr
        filter_upwards [hF_eq_r k] with η hη
        change (δ ≤ edist (F k η) (0 : ℝ)) = (δ ≤ edist (r k _) (0 : ℝ))
        rw [hη]
      have h_eq_seq : (fun n => P' {x | δ ≤ edist (F n x) (0 : ℝ)})
          = (fun n => P' {x | δ ≤ edist (r n (fun j : Fin n => x j.val)) (0 : ℝ)}) := by
        funext n
        exact h_set_ae n
      rw [← h_eq_seq]
      exact h_F_at_δ
    -- 4. Transport to Pⁿ via pi_meas_eq_infinitePi_meas_of_truncate.
    have h_F'_at_ε := hF'_zero (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    have hset_eq : ∀ k,
        {ω : ℕ → Ω | ENNReal.ofReal ε ≤ edist (r k (fun j : Fin k => ω j.val)) (0 : ℝ)}
          = {ω : ℕ → Ω | ε ≤ |r k (fun j : Fin k => ω j.val)|} := by
      intro k
      ext ω
      simp only [Set.mem_setOf_eq, edist_dist, Real.dist_eq, sub_zero]
      constructor
      · intro hle
        have habs_nn : (0 : ℝ) ≤ |r k (fun j => ω j.val)| := abs_nonneg _
        exact (ENNReal.ofReal_le_ofReal_iff habs_nn).mp hle
      · intro hle
        exact ENNReal.ofReal_le_ofReal hle
    -- Set measurability.
    have h_measSet : ∀ k, MeasurableSet {X : Fin k → Ω | ε ≤ |r k X|} := by
      intro k
      have h_abs_meas : Measurable (fun X : Fin k → Ω => |r k X|) := by
        have hh : (fun X : Fin k → Ω => |r k X|)
            = (fun X : Fin k → Ω => max (r k X) (-(r k X))) := by
          funext X; exact abs_eq_max_neg
        rw [hh]
        exact (hr_meas_n k).max (hr_meas_n k).neg
      exact measurableSet_le measurable_const h_abs_meas
    -- pi_meas → infinitePi_meas
    have h_meas_eq : ∀ k,
        (Measure.pi (fun _ : Fin k => P))
            {X : Fin k → Ω | ε ≤ |r k X|}
          = P' {ω : ℕ → Ω | ε ≤ |r k (fun j : Fin k => ω j.val)|} := by
      intro k
      rw [hP'_def]
      have := AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate P k
        (h_measSet k)
      rw [this]
      rfl
    simp_rw [h_meas_eq]
    have h_obj_eq : (fun k : ℕ => P' {ω : ℕ → Ω | ε ≤ |r k (fun j : Fin k => ω j.val)|})
        = (fun k : ℕ => P' {ω : ℕ → Ω | ENNReal.ofReal ε ≤ edist
            (r k (fun j : Fin k => ω j.val)) (0 : ℝ)}) := by
      funext k
      rw [hset_eq k]
    rw [h_obj_eq]
    exact h_F'_at_ε

/-- **Per-coordinate `lr_n`-log factorization to LAN remainder.**

For a single score `g : ↥(L2ZeroMean P)` from a QMDPath `γ_g := γ g` with
`(γ g).score = g`, the explicit witness
`r_n X := log((γ g).lr_n n X).toReal - scoreSumScalar g n X + ½‖g‖²`
satisfies:

1. `Pⁿ`-AE factorization:
   `(γ g).lr_n n X = ENNReal.ofReal (exp (scoreSumScalar g n X − ½‖g‖² + r_n X))`.
2. `r_n →ᵖ 0` under `Pⁿ`.

Proof notes:
* The factorization step needs `Pⁿ`-AE positivity and finiteness of `lr_n n X`
  (so `ENNReal.ofReal (exp (log lr_n.toReal)) = lr_n`). Finiteness: `lr_n` is a
  finite product of rnDerivs, `Pⁿ`-AE finite via `Measure.rnDeriv_lt_top`.
  Positivity requires extra absolute-continuity hypotheses on `curve t` (see
  `lr_n_pos_finite_ae_pi`).
* `r_n →ᵖ 0` follows from the LAN remainder formula
  `lanRemainder = ∑ log(p_t/p_0) - scoreSumScalar(scoreD) + ½ I` after (i)
  cancelling `∑ log p_0(X j)` (`P`-a.e.) and (ii) the Fisher-information
  identity `I_{γ g}(h',h') = ‖g‖²` at `h' = single 0 1`.

The body forwards to `bridge_residue_to_witness_one`. -/
private lemma lan_factorization_witness_one
    (g : ↥(L2ZeroMean P)) (γ_g : QMDPath P) (h_score : γ_g.score = g)
    (hDom : γ_g.dominating = P)
    (hAC : ∀ n, P ≪ γ_g.curve ((Real.sqrt n)⁻¹)) :
    ∃ r : (n : ℕ) → (Fin n → Ω) → ℝ,
      (∀ n, Measurable (r n)) ∧
      (∀ n,
        (fun X : Fin n → Ω => γ_g.lr_n n X)
          =ᵐ[Measure.pi (fun _ : Fin n => P)]
          (fun X : Fin n → Ω =>
            ENNReal.ofReal (Real.exp
              (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                  (P := P) g n X
                - (1/2 : ℝ) * ‖(g : Lp ℝ 2 P)‖ ^ 2
                + r n X)))) ∧
      (∀ ε > 0,
        Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε ≤ |r n X|})
          atTop (𝓝 (0 : ℝ≥0∞))) :=
  bridge_residue_to_witness_one (P := P) g γ_g h_score hDom hAC

/-- **Per-coordinate LAN factorization witness (over the basis index).**

For every score `g : ↥(L2ZeroMean P)` arising from a QMDPath family
`γ : ↥(L2ZeroMean P) → QMDPath P` (with `(γ g).score = g`), there is a
1-D LAN remainder `r_g : (n : ℕ) → (Fin n → Ω) → ℝ` such that:

1. **Pointwise `Pⁿ`-AE factorization** (after taking logs and re-exping):
   ```
   (γ g).lr_n n X
     = ENNReal.ofReal (Real.exp
         (scoreSumScalar g n X − ½‖g‖² + r_g n X))
   ```
   for `Pⁿ`-AE `X`.
2. **Convergence to 0 in `Pⁿ`-probability**: for every `ε > 0`,
   `Pⁿ {X | ε ≤ |r_g n X|} → 0`.
3. **Measurability** of `r_g n` for every `n`.

The body is a single `choose`-pull from `lan_factorization_witness_one`. -/
private lemma lan_factorization_witness_pi {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P))
    (γ : ↥(L2ZeroMean P) → QMDPath P)
    (h_score : ∀ g, (γ g).score = g)
    (hDom : ∀ i, (γ (g_P i)).dominating = P)
    (hAC : ∀ i n, P ≪ (γ (g_P i)).curve ((Real.sqrt n)⁻¹)) :
    ∃ r : Fin m → (n : ℕ) → (Fin n → Ω) → ℝ,
      (∀ i n, Measurable (r i n)) ∧
      (∀ i n,
        (fun X : Fin n → Ω => (γ (g_P i)).lr_n n X)
          =ᵐ[Measure.pi (fun _ : Fin n => P)]
          (fun X : Fin n → Ω =>
            ENNReal.ofReal (Real.exp
              (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                  (P := P) (g_P i) n X
                - (1/2 : ℝ) * ‖(g_P i : Lp ℝ 2 P)‖ ^ 2
                + r i n X)))) ∧
      (∀ i, ∀ ε > 0,
        Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε ≤ |r i n X|})
          atTop (𝓝 (0 : ℝ≥0∞))) := by
  classical
  -- Per coordinate, pull the witness from the single-direction lemma.
  -- We use `Classical.choose` to get a uniform `r i := …` from per-`i` existence.
  choose r hr_meas hr_factor hr_zero using
    fun i : Fin m =>
      lan_factorization_witness_one (P := P) (g := g_P i) (γ_g := γ (g_P i))
        (h_score (g_P i)) (hDom i) (hAC i)
  exact ⟨r, hr_meas, hr_factor, hr_zero⟩

/-- **Combination-direction LAN factorization witness vector.**

Variant of `lan_factorization_witness_pi` indexed by an arbitrary finite
grid `J : Finset (Fin m → ℝ)` instead of the basis `Fin m`. For each
`j ∈ J` and the combination direction `t_j := ∑_k j.val k • g_P k`,
the per-direction LAN witness from `lan_factorization_witness_one` is
pulled via `choose`.

The hypotheses `hDom`, `hAC` are universally quantified over all
`g : ↥(L2ZeroMean P)` (vdV §25 standing AC / dominating assumptions);
`h_score_image` is image-conditional, required only at the combination
directions `t_j := ∑_k j.val k • g_P k` for `j ∈ J`. The body only
specialises `h_score` at these directions. -/
private lemma combinationLAN_factorization_witness {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P))
    (γ : ↥(L2ZeroMean P) → QMDPath P)
    (hDom : ∀ g, (γ g).dominating = P)
    (hAC : ∀ g n, P ≪ (γ g).curve ((Real.sqrt n)⁻¹))
    (J : Finset (Fin m → ℝ))
    (h_score_image : ∀ j : ↥J,
      (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).score
        = ∑ k, j.val k • (g_P k : ↥(L2ZeroMean P))) :
    ∃ r : ↥J → (n : ℕ) → (Fin n → Ω) → ℝ,
      (∀ j n, Measurable (r j n)) ∧
      (∀ j n,
        (fun X : Fin n → Ω =>
            (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).lr_n n X)
          =ᵐ[Measure.pi (fun _ : Fin n => P)]
          (fun X : Fin n → Ω =>
            ENNReal.ofReal (Real.exp
              (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                  (P := P) (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P))) n X
                - (1/2 : ℝ)
                    * ‖((∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)) :
                        ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ ^ 2
                + r j n X)))) ∧
      (∀ j, ∀ ε > 0,
        Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε ≤ |r j n X|})
          atTop (𝓝 (0 : ℝ≥0∞))) := by
  classical
  -- Per `j ∈ J`, specialise the per-direction witness at the combination
  -- direction `t_j := ∑_k j.val k • g_P k`. The image-conditional
  -- `h_score_image j` supplies the per-`j` score identity; the general
  -- `hDom`, `hAC` (over all of `↥(L2ZeroMean P)`) supply the AC + dominating
  -- side conditions.
  choose r hr_meas hr_factor hr_zero using
    fun j : ↥J =>
      lan_factorization_witness_one (P := P)
        (g := ∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))
        (γ_g := γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P))))
        (h_score_image j) (hDom _) (hAC _)
  exact ⟨r, hr_meas, hr_factor, hr_zero⟩

/-- **Joint LAN factorization.**

Per the LAN expansion `lanExpansion_at_basis_and_h` applied coordinate-wise
(across the `Fin m` index), there exists a joint remainder

    `R_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin m)`

such that:

1. **`Pⁿ`-AE pointwise factorization**: for `Pⁿ`-AE `X`, the joint LR
   vector equals the `lrTransform` applied to the *adjusted* score sum
   `jointScoreSum g_P n X + R_n X`.

2. **Joint convergence to zero**: `R_n →ᵖ 0` under `Pⁿ` in
   `EuclideanSpace ℝ (Fin m)`.

Packages the per-coordinate witness from `lan_factorization_witness_pi` into
joint `EuclideanSpace`-valued form, using `EuclideanSpace.norm_eq`
(joint-norm-from-coordinate-norms) and the `Pⁿ`-union bound to combine
per-coordinate convergence in probability into joint convergence.
-/
private lemma jointLAN_factorization {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P))
    (γ : ↥(L2ZeroMean P) → QMDPath P)
    (h_score : ∀ g, (γ g).score = g)
    (hDom : ∀ i, (γ (g_P i)).dominating = P)
    (hAC : ∀ i n, P ≪ (γ (g_P i)).curve ((Real.sqrt n)⁻¹)) :
    ∃ R_n : (n : ℕ) → (Fin n → Ω) → EuclideanSpace ℝ (Fin m),
      (∀ n, Measurable (R_n n)) ∧
      (∀ n,
        (fun X : Fin n → Ω =>
            (fun i : Fin m => (γ (g_P i)).lr_n n X))
          =ᵐ[Measure.pi (fun _ : Fin n => P)]
          (fun X : Fin n → Ω =>
            lrTransform (P := P) g_P
              (jointScoreSum (P := P) g_P n X + R_n n X))) ∧
      (∀ ε > 0,
        Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε ≤ ‖R_n n X‖})
          atTop (𝓝 (0 : ℝ≥0∞))) := by
  classical
  -- Pull the per-coordinate factorization from `lan_factorization_witness_pi`.
  obtain ⟨r, hr_meas, hr_factor, hr_zero⟩ :=
    lan_factorization_witness_pi (P := P) g_P γ h_score hDom hAC
  -- Bundle the per-coordinate `r i n X : ℝ` into joint
  -- `R_n n X : EuclideanSpace ℝ (Fin m)` via `EuclideanSpace.equiv.symm`.
  refine
    ⟨fun n X => (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => r i n X),
      ?_, ?_, ?_⟩
  · -- Measurability of joint `R_n n` from per-coord measurability.
    intro n
    have h_inner : Measurable
        (fun X : Fin n → Ω => fun i : Fin m => r i n X) :=
      measurable_pi_lambda _ (fun i => hr_meas i n)
    exact ((EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable).comp h_inner
  · -- `Pⁿ`-AE joint factorization.
    intro n
    -- Apply `ae_all_iff`: it suffices to show per-coordinate AE-equality.
    have h_per : ∀ i : Fin m, ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
        (γ (g_P i)).lr_n n X
          = ENNReal.ofReal (Real.exp
              (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                  (P := P) (g_P i) n X
                - (1/2 : ℝ) * ‖(g_P i : Lp ℝ 2 P)‖ ^ 2
                + r i n X)) := by
      intro i; exact hr_factor i n
    have h_all : ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
        ∀ i : Fin m,
          (γ (g_P i)).lr_n n X
            = ENNReal.ofReal (Real.exp
                (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
                    (P := P) (g_P i) n X
                  - (1/2 : ℝ) * ‖(g_P i : Lp ℝ 2 P)‖ ^ 2
                  + r i n X)) := by
      rw [ae_all_iff]; exact h_per
    filter_upwards [h_all] with X hX
    -- Goal: `(fun i => (γ (g_P i)).lr_n n X) =
    --         lrTransform g_P (jointScoreSum g_P n X + R_n n X)`.
    funext i
    rw [hX i]
    -- RHS unfolds to
    -- `ENNReal.ofReal (exp ((jointScoreSum + R_n n X) i − ½‖g_P i‖²))`.
    -- LHS = ENNReal.ofReal (exp (scoreSumScalar - ½‖g_P i‖² + r i n X)).
    -- Match: `(jointScoreSum n X + R_n n X) i = scoreSumScalar (g_P i) n X + r i n X`.
    show ENNReal.ofReal _ = ENNReal.ofReal _
    congr 1
    -- exp arguments match.
    show Real.exp _ = Real.exp _
    congr 1
    -- Algebra: rearrange.
    have h_jsum_i :
        (jointScoreSum (P := P) g_P n X) i
          = AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
              (P := P) (g_P i) n X := by
      change ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (fun i' : Fin m =>
            AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
              (P := P) (g_P i') n X)) i = _
      rfl
    have h_R_i :
        ((EuclideanSpace.equiv (Fin m) ℝ).symm
            (fun i' : Fin m => r i' n X)) i = r i n X := rfl
    -- Compute (jointScoreSum + R_n) i = jointScoreSum i + R_n i.
    have h_add : (jointScoreSum (P := P) g_P n X
        + (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i' : Fin m => r i' n X)) i
          = (jointScoreSum (P := P) g_P n X) i
            + ((EuclideanSpace.equiv (Fin m) ℝ).symm (fun i' : Fin m => r i' n X)) i := rfl
    rw [h_add, h_jsum_i, h_R_i]
    ring
  · -- Joint norm convergence in probability from per-coord convergence,
    -- delegated to `pi_tendsto_of_per_coord_pi_tendsto`.
    exact pi_tendsto_of_per_coord_pi_tendsto (P := P) (m := m)
      (r := r) hr_zero

/-- **Cramér–Wold device specialised to measures on `EuclideanSpace ℝ (Fin m)`.**

The project's `cramerWold_weakConverges` is stated for measures on
`ℝ × EuclideanSpace ℝ (Fin m)` (with a scalar coordinate). This thin
wrapper specialises to measures on `EuclideanSpace ℝ (Fin m)` by lifting
through `ι := fun y => ((0 : ℝ), y)` and unwinding via `Prod.snd`. -/
private lemma cramerWold_weakConverges_of_inner_proj
    {m : ℕ}
    {μ_n : ℕ → Measure (EuclideanSpace ℝ (Fin m))}
    {μ : Measure (EuclideanSpace ℝ (Fin m))}
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure μ]
    (h_per_dir : ∀ (t : EuclideanSpace ℝ (Fin m)),
      WeakConverges
        (fun n => (μ_n n).map (fun y => ⟪t, y⟫_ℝ))
        (μ.map (fun y => ⟪t, y⟫_ℝ))) :
    WeakConverges μ_n μ := by
  set ι : EuclideanSpace ℝ (Fin m) → ℝ × EuclideanSpace ℝ (Fin m) :=
    fun y => (0, y) with hι_def
  have h_ι_cont : Continuous ι :=
    continuous_prodMk.mpr ⟨continuous_const, continuous_id⟩
  have h_ι_meas : Measurable ι := h_ι_cont.measurable
  haveI h_prob_lifted_n : ∀ n, IsProbabilityMeasure ((μ_n n).map ι) := fun n =>
    Measure.isProbabilityMeasure_map h_ι_meas.aemeasurable
  haveI h_prob_lifted_lim : IsProbabilityMeasure (μ.map ι) :=
    Measure.isProbabilityMeasure_map h_ι_meas.aemeasurable
  have h_lifted : WeakConverges (fun n => (μ_n n).map ι) (μ.map ι) := by
    refine AsymptoticStatistics.ForMathlib.cramerWold_weakConverges (m := m) ?_
    intro t hvec
    set proj : ℝ × EuclideanSpace ℝ (Fin m) → ℝ :=
      fun p => t * p.1 + ⟪hvec, p.2⟫_ℝ with hproj_def
    have h_proj_cont : Continuous proj := by
      refine Continuous.add ?_ ?_
      · exact continuous_const.mul continuous_fst
      · exact continuous_const.inner continuous_snd
    have h_proj_meas : Measurable proj := h_proj_cont.measurable
    have h_compose : ∀ y : EuclideanSpace ℝ (Fin m),
        proj (ι y) = ⟪hvec, y⟫_ℝ := by
      intro y; simp [hproj_def, hι_def]
    have h_lhs_n : ∀ n, ((μ_n n).map ι).map proj
        = (μ_n n).map (fun y => ⟪hvec, y⟫_ℝ) := by
      intro n
      rw [Measure.map_map h_proj_meas h_ι_meas]
      congr 1; funext y; exact h_compose y
    have h_lhs_lim : (μ.map ι).map proj
        = μ.map (fun y => ⟪hvec, y⟫_ℝ) := by
      rw [Measure.map_map h_proj_meas h_ι_meas]
      congr 1; funext y; exact h_compose y
    have h_seq_eq : (fun n => ((μ_n n).map ι).map proj)
        = (fun n => (μ_n n).map (fun y => ⟪hvec, y⟫_ℝ)) := by
      funext n; exact h_lhs_n n
    rw [h_seq_eq, h_lhs_lim]
    exact h_per_dir hvec
  -- Push back via `Prod.snd : ℝ × E → E`. Since `Prod.snd ∘ ι = id`, the
  -- pushforwards of the lifted measures equal the original measures.
  have h_id : (Prod.snd ∘ ι) = (id : EuclideanSpace ℝ (Fin m) → _) := by
    funext y; rfl
  have h_pushed := h_lifted.map continuous_snd continuous_snd.measurable
  have h_eq_n : (fun n => ((μ_n n).map ι).map Prod.snd) = μ_n := by
    funext n
    rw [Measure.map_map continuous_snd.measurable h_ι_meas, h_id, Measure.map_id]
  have h_eq_lim : (μ.map ι).map Prod.snd = μ := by
    rw [Measure.map_map continuous_snd.measurable h_ι_meas, h_id, Measure.map_id]
  rw [h_eq_n, h_eq_lim] at h_pushed
  exact h_pushed

/-- **`WeakConverges`-Slutsky on `EuclideanSpace ℝ (Fin m)` for per-`n` Pi
product measures.**

Given:
* a sequence of measurable maps `S_n, R_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin m)`,
* `Pⁿ.map S_n ⇒ ν` weakly,
* `R_n →ᵖ 0` under `Pⁿ` (in the joint norm),

then `Pⁿ.map (S_n + R_n) ⇒ ν` weakly.

Mathlib's 1-D Slutsky `tendstoInDistribution.add_of_tendstoInMeasure_const`
needs a *single* source measure, while here the source space `Fin n → Ω`
changes with `n`. The proof reduces to 1-D via Cramér-Wold
(`cramerWold_weakConverges_of_inner_proj`), bridges the per-`n` source spaces
into one fixed `Measure.infinitePi` source (whose `n`-th coordinate pushforward
recovers each `Pⁿ`), then applies the 1-D Slutsky lemma after scalarising along
each inner-product projection `t ↦ ⟪t, ·⟫_ℝ`. -/
private lemma weakConverges_add_of_tendstoInMeasure_zero {m : ℕ}
    (S_n R_n : (n : ℕ) → (Fin n → Ω) → EuclideanSpace ℝ (Fin m))
    (hS_meas : ∀ n, Measurable (S_n n))
    (hR_meas : ∀ n, Measurable (R_n n))
    (hR_zero : ∀ ε > 0,
      Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ ‖R_n n X‖})
        atTop (𝓝 (0 : ℝ≥0∞)))
    {ν : Measure (EuclideanSpace ℝ (Fin m))} [IsProbabilityMeasure ν]
    (h_S_conv : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map (S_n n)) ν) :
    WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (fun X : Fin n → Ω => S_n n X + R_n n X)) ν := by
  -- Probability-measure instances for each per-`n` pushforward.
  haveI h_sum_prob : ∀ n, IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin n => P)).map
        (fun X : Fin n → Ω => S_n n X + R_n n X)) := fun n =>
    Measure.isProbabilityMeasure_map ((hS_meas n).add (hR_meas n)).aemeasurable
  -- 1. Cramér–Wold reduction: a multivariate weak limit on `EuclideanSpace ℝ (Fin m)`
  --    is detected by every 1-D inner-product projection `t ↦ ⟪t, ·⟫_ℝ`.
  apply cramerWold_weakConverges_of_inner_proj (m := m)
  intro t
  -- Scalarised maps `s_n := ⟪t, S_n⟫_ℝ`, `r_n := ⟪t, R_n⟫_ℝ`.
  set s_n : (n : ℕ) → (Fin n → Ω) → ℝ :=
    fun n X => ⟪t, S_n n X⟫_ℝ with hs_def
  set r_n : (n : ℕ) → (Fin n → Ω) → ℝ :=
    fun n X => ⟪t, R_n n X⟫_ℝ with hr_def
  have h_inner_meas : Measurable (fun x : EuclideanSpace ℝ (Fin m) => ⟪t, x⟫_ℝ) :=
    (continuous_const.inner continuous_id).measurable
  have hs_meas : ∀ n, Measurable (s_n n) := fun n => h_inner_meas.comp (hS_meas n)
  have hr_meas : ∀ n, Measurable (r_n n) := fun n => h_inner_meas.comp (hR_meas n)
  -- 2. Bridge varying source spaces `Fin n → Ω` into a single fixed product space
  --    `Ω_fixed := ∀ n : ℕ, Fin n → Ω` carrying the infinite product measure
  --    `μ_fixed`. Each coordinate-evaluation pushforward equals the per-`n` pi
  --    measure (`Measure.infinitePi_map_eval`).
  set μ_fixed : Measure ((n : ℕ) → (Fin n → Ω)) :=
    Measure.infinitePi (fun n : ℕ => Measure.pi (fun _ : Fin n => P)) with hμ_fixed_def
  haveI : IsProbabilityMeasure μ_fixed := by
    rw [hμ_fixed_def]; infer_instance
  have h_map_eval : ∀ n : ℕ,
      μ_fixed.map (fun X : (n : ℕ) → (Fin n → Ω) => X n)
        = Measure.pi (fun _ : Fin n => P) := by
    intro n
    rw [hμ_fixed_def]
    exact Measure.infinitePi_map_eval _ n
  -- Lifted scalar sequences on the fixed source.
  set S'_n : (n : ℕ) → ((n : ℕ) → (Fin n → Ω)) → ℝ :=
    fun n X => s_n n (X n) with hS'_def
  set R'_n : (n : ℕ) → ((n : ℕ) → (Fin n → Ω)) → ℝ :=
    fun n X => r_n n (X n) with hR'_def
  have hS'_meas : ∀ n, Measurable (S'_n n) := fun n =>
    (hs_meas n).comp (measurable_pi_apply n)
  have hR'_meas : ∀ n, Measurable (R'_n n) := fun n =>
    (hr_meas n).comp (measurable_pi_apply n)
  -- Limit measure on the scalar side: `ν.map ⟨t, ·⟩`.
  set ν' : Measure ℝ := ν.map (fun x => ⟪t, x⟫_ℝ) with hν'_def
  haveI hν'_prob : IsProbabilityMeasure ν' := by
    rw [hν'_def]; exact Measure.isProbabilityMeasure_map h_inner_meas.aemeasurable
  -- 3. `TendstoInDistribution` for the scaled `S'_n`, derived from the multivariate
  --    `WeakConverges` hypothesis via continuous-mapping + the `infinitePi` bridge.
  have h_S_1D : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map (s_n n)) ν' := by
    have h_s_map : ∀ n, (Measure.pi (fun _ : Fin n => P)).map (s_n n)
        = ((Measure.pi (fun _ : Fin n => P)).map (S_n n)).map
            (fun x : EuclideanSpace ℝ (Fin m) => ⟪t, x⟫_ℝ) := by
      intro n
      rw [Measure.map_map h_inner_meas (hS_meas n)]; rfl
    have h_seq_eq_S : (fun n => (Measure.pi (fun _ : Fin n => P)).map (s_n n))
        = (fun n => ((Measure.pi (fun _ : Fin n => P)).map (S_n n)).map
            (fun x : EuclideanSpace ℝ (Fin m) => ⟪t, x⟫_ℝ)) := by
      funext n; exact h_s_map n
    rw [h_seq_eq_S, hν'_def]
    exact h_S_conv.map (continuous_const.inner continuous_id) h_inner_meas
  have h_S'_dist : TendstoInDistribution S'_n atTop (id : ℝ → ℝ)
      (fun _ => μ_fixed) ν' := by
    refine ⟨fun n => (hS'_meas n).aemeasurable, measurable_id.aemeasurable, ?_⟩
    -- The `tendsto` field matches `WeakConverges` after the `infinitePi`-eval bridge
    -- and `Measure.map_id`.
    have h_seq_eq : (fun n => μ_fixed.map (S'_n n))
        = (fun n => (Measure.pi (fun _ : Fin n => P)).map (s_n n)) := by
      funext n
      rw [hS'_def]
      change μ_fixed.map ((s_n n) ∘ (fun X : (n : ℕ) → (Fin n → Ω) => X n)) = _
      rw [← Measure.map_map (hs_meas n) (measurable_pi_apply n), h_map_eval n]
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
    intro f
    -- The subtype-coercion of a `ProbabilityMeasure` to a `Measure` is `rfl` on
    -- integrals, so reduce both sides to underlying-measure integrals.
    have h_pointwise : ∀ n, μ_fixed.map (S'_n n)
        = (Measure.pi (fun _ : Fin n => P)).map (s_n n) := by
      intro n
      have := congrFun h_seq_eq n
      exact this
    have h_target : Tendsto (fun n => ∫ x, f x ∂(μ_fixed.map (S'_n n)))
        atTop (𝓝 (∫ x, f x ∂(ν'.map (id : ℝ → ℝ)))) := by
      rw [Measure.map_id]
      simp_rw [h_pointwise]
      exact h_S_1D f
    exact h_target
  -- 4. `TendstoInMeasure` for `R'_n → 0`, lifted from `hR_zero`.
  have h_R'_zero : TendstoInMeasure μ_fixed R'_n atTop (fun _ => (0 : ℝ)) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    by_cases ht : t = 0
    · -- If `t = 0`, then `r_n ≡ 0` so the set is empty for any `ε > 0`.
      have h_r_zero : ∀ n X, r_n n X = 0 := by
        intro n X; simp [hr_def, ht]
      have h_empty : ∀ n, {X : (n : ℕ) → (Fin n → Ω) | ε ≤ dist (R'_n n X) 0} = ∅ := by
        intro n
        ext X
        simp only [hR'_def, h_r_zero n (X n), Set.mem_setOf_eq, dist_self,
          Set.mem_empty_iff_false, iff_false, not_le]
        exact hε
      simp_rw [h_empty, measure_empty]
      exact tendsto_const_nhds
    · have ht_pos : 0 < ‖t‖ := norm_pos_iff.mpr ht
      -- Per-`n` translation: the level set on `Ω_fixed` is the `n`-th-coordinate
      -- pre-image of the level set on `Fin n → Ω`.
      have h_eq : ∀ n,
          μ_fixed {X : (n : ℕ) → (Fin n → Ω) | ε ≤ dist (R'_n n X) 0}
            = (Measure.pi (fun _ : Fin n => P))
                {X : Fin n → Ω | ε ≤ |r_n n X|} := by
        intro n
        have h_set_meas : MeasurableSet {X : Fin n → Ω | ε ≤ |r_n n X|} :=
          measurableSet_le measurable_const (hr_meas n).norm
        have h_preimage :
            {X : (n : ℕ) → (Fin n → Ω) | ε ≤ dist (R'_n n X) 0}
              = (fun X : (n : ℕ) → (Fin n → Ω) => X n) ⁻¹'
                  {X : Fin n → Ω | ε ≤ |r_n n X|} := by
          ext X
          simp [hR'_def]
        rw [h_preimage, ← Measure.map_apply (measurable_pi_apply n) h_set_meas,
          h_map_eval n]
      -- Cauchy–Schwarz on `r_n n X = ⟨t, R_n n X⟩` and dominated convergence by
      -- `hR_zero (ε / ‖t‖)`.
      have h_subset : ∀ n,
          {X : Fin n → Ω | ε ≤ |r_n n X|} ⊆
            {X : Fin n → Ω | ε / ‖t‖ ≤ ‖R_n n X‖} := by
        intro n X hX
        have hX' : ε ≤ |r_n n X| := hX
        have h_bound : |r_n n X| ≤ ‖t‖ * ‖R_n n X‖ := by
          rw [hr_def, ← Real.norm_eq_abs]
          exact abs_real_inner_le_norm t (R_n n X)
        have h_chain : ε ≤ ‖R_n n X‖ * ‖t‖ := by
          rw [mul_comm]; exact le_trans hX' h_bound
        exact (div_le_iff₀ ht_pos).mpr h_chain
      have h_tendsto := hR_zero (ε / ‖t‖) (div_pos hε ht_pos)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tendsto
        (Eventually.of_forall fun _ => zero_le)
        (Eventually.of_forall fun n => ?_)
      rw [h_eq n]
      exact measure_mono (h_subset n)
  -- 5. Mathlib's 1-D Slutsky paste.
  have h_add_dist :=
    h_S'_dist.add_of_tendstoInMeasure_const h_R'_zero
      (fun n => (hR'_meas n).aemeasurable)
  -- 6. Unwind back to per-`n` source measures and pull through the inner-product
  --    projection on the joint vector.
  have h_add_seq_eq : (fun n => μ_fixed.map (S'_n n + R'_n n))
      = (fun n => (Measure.pi (fun _ : Fin n => P)).map (fun X => s_n n X + r_n n X)) := by
    funext n
    have h_meas_add : Measurable (fun X : Fin n → Ω => s_n n X + r_n n X) :=
      (hs_meas n).add (hr_meas n)
    change μ_fixed.map ((fun X : Fin n → Ω => s_n n X + r_n n X) ∘
        (fun X : (n : ℕ) → (Fin n → Ω) => X n)) = _
    rw [← Measure.map_map h_meas_add (measurable_pi_apply n), h_map_eval n]
  have h_id_add : (fun ω : ℝ => id ω + (0 : ℝ)) = id := by
    funext x; exact add_zero x
  -- Convert the resulting `TendstoInDistribution` into our `WeakConverges` shape.
  intro f
  have h_tnd := h_add_dist.tendsto
  replace h_tnd := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_tnd
  have h_tnd_f := h_tnd f
  -- Reduce both subtype integrals to plain `∫ ⋯ ∂ ⋯`. The subtype coercion
  -- is definitional for the integrand evaluation, so a single `change` does it.
  have h_extract : Tendsto (fun n => ∫ x, f x ∂(μ_fixed.map (S'_n n + R'_n n)))
      atTop (𝓝 (∫ x, f x ∂(ν'.map (fun ω : ℝ => id ω + (0 : ℝ))))) := h_tnd_f
  rw [h_id_add, Measure.map_id] at h_extract
  -- Match the LHS sequence to the goal-shape sequence.
  have h_goal_seq_eq : (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (fun X : Fin n → Ω => ⟪t, S_n n X + R_n n X⟫_ℝ))
      = (fun n => (Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω => s_n n X + r_n n X)) := by
    funext n
    refine Measure.map_congr (Eventually.of_forall fun X => ?_)
    simp [hs_def, hr_def, inner_add_right]
  -- Push the inner-product projection through the per-`n` map.
  have h_goal_after_proj : (fun n =>
        ((Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => S_n n X + R_n n X)).map
          (fun x : EuclideanSpace ℝ (Fin m) => ⟪t, x⟫_ℝ))
      = fun n => (Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω => ⟪t, S_n n X + R_n n X⟫_ℝ) := by
    funext n
    have h_meas_vec : Measurable (fun X : Fin n → Ω => S_n n X + R_n n X) :=
      (hS_meas n).add (hR_meas n)
    rw [Measure.map_map h_inner_meas h_meas_vec]; rfl
  -- Goal at this point (after `cramerWold_weakConverges_of_inner_proj`) is the
  -- per-direction `WeakConverges`. Unfold the goal sequences to align with
  -- `h_extract`.
  rw [h_goal_after_proj, h_goal_seq_eq, ← h_add_seq_eq]
  exact h_extract

/-- **Joint Slutsky paste of joint Δ-convergence with `R_n →ᵖ 0`.**

Given:
* joint Δ-convergence `(Pⁿ).map (jointScoreSum g_P n) ⇒ N(0, I_m)`;
* a measurable joint remainder `R_n` with `R_n →ᵖ 0` in `Pⁿ`-probability;

the *adjusted* vector `jointScoreSum + R_n` also weakly converges to
`N(0, I_m)`. This is Slutsky for the `EuclideanSpace ℝ (Fin m)`-valued
joint vector, in the form: weak-conv + AS-conv-to-constant ⇒
weak-conv-of-sum.

Delegates to `weakConverges_add_of_tendstoInMeasure_zero` with the joint
score sum `S_n := jointScoreSum g_P n`. -/
private lemma jointSlutsky_addRemainder_to_jointDelta {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P))
    (R_n : (n : ℕ) → (Fin n → Ω) → EuclideanSpace ℝ (Fin m))
    (_hR_meas : ∀ n, Measurable (R_n n))
    (_hR_zero : ∀ ε > 0,
      Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ ‖R_n n X‖})
        atTop (𝓝 (0 : ℝ≥0∞)))
    (h_jointDelta :
      WeakConverges
        (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P)).map
            (jointScoreSum (P := P) g_P n))
        (ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ))) :
    WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            jointScoreSum (P := P) g_P n X + R_n n X))
      (ProbabilityTheory.multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin m))
        (1 : Matrix (Fin m) (Fin m) ℝ)) :=
  weakConverges_add_of_tendstoInMeasure_zero
    (S_n := fun n : ℕ => jointScoreSum (P := P) g_P n)
    (R_n := R_n)
    (hS_meas := fun n => measurable_jointScoreSum (P := P) g_P n)
    (hR_meas := _hR_meas) (hR_zero := _hR_zero) h_jointDelta

/-- **From joint Δ-convergence to joint LR-convergence (LAN + Slutsky).**

Given:
* joint Δ-convergence `Δ_n ⇒ N(0, I_m)` under `Pⁿ`;
* per-direction LAN remainder `R_{n,g_i} → 0` in `Pⁿ`-probability,
  from `lanExpansion_at_basis_and_h`;

the joint LR vector
`(L_{n,g_i})_i := (γ (g_P i)).lr_n n` converges weakly under `Pⁿ` to
`gaussianShiftLRLaw g_P`.

**Strategy**:
1. `jointLAN_factorization` — pick a joint remainder `R_n` with the
   `Pⁿ`-AE factorization `lr_n = lrTransform (jointScoreSum + R_n)` and
   joint `R_n →ᵖ 0`.
2. `jointSlutsky_addRemainder_to_jointDelta` — combine
   `h_jointDelta` with `R_n →ᵖ 0` to get
   `jointScoreSum + R_n ⇒ N(0, I_m)` weakly under `Pⁿ`.
3. `WeakConverges.map (continuous_lrTransform g_P)` — push through the
   `lrTransform` continuous map.
4. Align the LHS sequence via `Measure.map_congr` against the AE
   factorization, and the RHS via `gaussianShiftLRLaw_eq_pushforward`.

The orthonormality of `g_P` is consumed inside `h_jointDelta` (the
multivariate covariance is `I_m`); this lemma itself does not consume it
directly, but keeps it in the signature for alignment with
`jointLR_weakConverges`. -/
lemma jointDelta_to_jointLR_via_LAN_and_Slutsky
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (γ : ↥(L2ZeroMean P) → QMDPath P)
    (h_score : ∀ g, (γ g).score = g)
    (hDom : ∀ i, (γ (g_P i)).dominating = P)
    (hAC : ∀ i n, P ≪ (γ (g_P i)).curve ((Real.sqrt n)⁻¹))
    (h_jointDelta :
      WeakConverges
        (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P)).map
            (jointScoreSum (P := P) g_P n))
        (ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ))) :
    WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            fun i : Fin m => (γ (g_P i)).lr_n n X))
      (gaussianShiftLRLaw (P := P) g_P) := by
  let _ := h_orth
  -- Step 1: joint LAN factorization.
  obtain ⟨R_n, hR_meas, hR_factor, hR_zero⟩ :=
    jointLAN_factorization (P := P) (g_P := g_P) γ h_score hDom hAC
  -- Step 2: joint Slutsky paste.
  have h_adjusted :
      WeakConverges
        (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω =>
              jointScoreSum (P := P) g_P n X + R_n n X))
        (ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ)) :=
    jointSlutsky_addRemainder_to_jointDelta (P := P)
      (g_P := g_P) (R_n := R_n) hR_meas hR_zero h_jointDelta
  -- Step 3: continuous mapping with `lrTransform`.
  -- `WeakConverges.map` in `ForMathlib/Contiguity.lean` requires
  -- `[PseudoMetricSpace F]` on the target, which `Fin m → ℝ≥0∞` does not
  -- carry (`ℝ≥0∞` is only a pseudo-`E`-metric space). We inline the
  -- `WeakConverges`-test-function argument: for any `g : (Fin m → ℝ≥0∞) →ᵇ ℝ`,
  -- `g.compContinuous ⟨lrTransform g_P, continuous_lrTransform g_P⟩` is a
  -- bounded continuous function on `EuclideanSpace ℝ (Fin m)`, and
  -- `integral_map` gives the change-of-variable on both sides.
  have h_mapped :
      WeakConverges
        (fun n : ℕ =>
          ((Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω =>
              jointScoreSum (P := P) g_P n X + R_n n X)).map
              (lrTransform (P := P) g_P))
        ((ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ)).map
            (lrTransform (P := P) g_P)) := by
    intro f
    -- `f : (Fin m → ℝ≥0∞) →ᵇ ℝ`; precompose with the continuous `lrTransform`.
    let f_comp : EuclideanSpace ℝ (Fin m) →ᵇ ℝ :=
      f.compContinuous
        ⟨lrTransform (P := P) g_P, continuous_lrTransform (P := P) g_P⟩
    have h_meas_lrT : Measurable (lrTransform (P := P) g_P) :=
      measurable_lrTransform (P := P) g_P
    have h_int_n : ∀ n,
        ∫ y, f y ∂(((Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω =>
              jointScoreSum (P := P) g_P n X + R_n n X)).map
              (lrTransform (P := P) g_P))
          = ∫ x, f_comp x ∂((Measure.pi (fun _ : Fin n => P)).map
              (fun X : Fin n → Ω =>
                jointScoreSum (P := P) g_P n X + R_n n X)) := by
      intro n
      rw [MeasureTheory.integral_map h_meas_lrT.aemeasurable
        f.continuous.aestronglyMeasurable]
      rfl
    have h_int_lim :
        ∫ y, f y ∂((ProbabilityTheory.multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin m))
            (1 : Matrix (Fin m) (Fin m) ℝ)).map
              (lrTransform (P := P) g_P))
          = ∫ x, f_comp x ∂(ProbabilityTheory.multivariateGaussian
              (0 : EuclideanSpace ℝ (Fin m))
              (1 : Matrix (Fin m) (Fin m) ℝ)) := by
      rw [MeasureTheory.integral_map h_meas_lrT.aemeasurable
        f.continuous.aestronglyMeasurable]
      rfl
    simp_rw [h_int_n, h_int_lim]
    exact h_adjusted f_comp
  -- Step 4a: rewrite the LHS sequence via `Measure.map_map` then via
  --          `Measure.map_congr` (the AE-equality `hR_factor`).
  have h_meas_adj : ∀ n,
      Measurable
        (fun X : Fin n → Ω =>
          jointScoreSum (P := P) g_P n X + R_n n X) := by
    intro n
    exact (measurable_jointScoreSum (P := P) g_P n).add (hR_meas n)
  have h_lhs_eq : ∀ n,
      ((Measure.pi (fun _ : Fin n => P)).map
        (fun X : Fin n → Ω =>
          jointScoreSum (P := P) g_P n X + R_n n X)).map
            (lrTransform (P := P) g_P)
        = (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            (fun i : Fin m => (γ (g_P i)).lr_n n X)) := by
    intro n
    rw [Measure.map_map (measurable_lrTransform (P := P) g_P)
      (h_meas_adj n)]
    refine Measure.map_congr ?_
    -- Goal: `(lrTransform g_P) ∘ (fun X => jointScoreSum + R_n n X)`
    -- =ᵐ[Pⁿ] `(fun X => fun i => (γ (g_P i)).lr_n n X)`
    -- which is the symmetric of `hR_factor n`.
    have h := hR_factor n
    filter_upwards [h] with X hX using hX.symm
  -- Step 4b: rewrite the RHS via `gaussianShiftLRLaw_eq_pushforward`.
  rw [gaussianShiftLRLaw_eq_pushforward (P := P) g_P]
  -- Combine: rewrite the sequence using `h_lhs_eq` to match `h_mapped`.
  have h_seq_eq :
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            (fun i : Fin m => (γ (g_P i)).lr_n n X)))
        = (fun n : ℕ =>
          ((Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω =>
              jointScoreSum (P := P) g_P n X + R_n n X)).map
              (lrTransform (P := P) g_P)) := by
    funext n; exact (h_lhs_eq n).symm
  rw [h_seq_eq]
  exact h_mapped

/-! ## Main theorem -/

/-- **Joint LR weak convergence under `Pⁿ`.**

For an orthonormal `L²(P)`-basis `g_P : Fin m → ↥(L2ZeroMean P)` of a
finite-dim subspace of the tangent set, and a QMDPath family
`γ : ↥(L2ZeroMean P) → QMDPath P` with `(γ g).score = g`, the joint LR
vector

    `L_n : (Fin n → Ω) → (Fin m → ℝ≥0∞)`,
    `L_n X i := (γ (g_P i)).lr_n n X`,

converges weakly under `Pⁿ := Measure.pi (fun _ => P)` to
`gaussianShiftLRLaw g_P`, the pushforward of the multivariate standard
Gaussian under componentwise `Δ ↦ ENNReal.ofReal (exp(Δ_i − ½‖g_i‖²))`.

The body composes `jointDelta_weakConverges_under_pi` (Cramér-Wold) and
`jointDelta_to_jointLR_via_LAN_and_Slutsky` (LAN + continuous mapping). -/
theorem jointLR_weakConverges
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (γ : ↥(L2ZeroMean P) → QMDPath P)
    (h_score : ∀ g, (γ g).score = g)
    -- equals P (vdV §25 standing in the dominated case). Required by
    -- `sum_log_p_0_zero_ae_pi` deep in the call chain to collapse
    -- `Σⱼ log p_0(X j) = 0` Pⁿ-a.e.
    (hDom : ∀ i, (γ (g_P i)).dominating = P)
    -- vdV §25 standing in the dominated case. Required by
    -- `lr_n_pos_finite_ae_pi` deep in the call chain to lift
    -- `(curve t)`-a.e. positivity of `rnDeriv` to `Pⁿ`-a.e.
    (hAC : ∀ i n, P ≪ (γ (g_P i)).curve ((Real.sqrt n)⁻¹)) :
    WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            fun i : Fin m => (γ (g_P i)).lr_n n X))
      (gaussianShiftLRLaw (P := P) g_P) :=
  jointDelta_to_jointLR_via_LAN_and_Slutsky g_P h_orth γ h_score hDom hAC
    (jointDelta_weakConverges_under_pi g_P h_orth)

/-- **Slutsky-product + continuous-mapping bundle.**

Given:

* a continuous (and measurable) map
  `Φ : EuclideanSpace ℝ (Fin m) → (ι → ℝ≥0∞)` (with `ι` finite);
* sequences `S_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin m)` and
  `R_n : (Fin n → Ω) → ι → ℝ` of measurable maps;
* per-`ι`-coordinate `R_n n X i →ᵖ 0` under `Pⁿ`;
* weak convergence `Pⁿ.map (S_n n) ⇒ ν` for some probability measure
  `ν` on `EuclideanSpace ℝ (Fin m)`,

the conclusion is

  `Pⁿ.map (X ↦ fun i ↦ Φ (S_n n X) i * ofReal (exp (R_n n X i))) ⇒ ν.map Φ`

weakly on `ι → ℝ≥0∞`.

**Mathematical content**: the Slutsky product theorem composed with the
continuous-mapping theorem. The `exp`-of-remainder factor collapses to `1`
at the constant limit `0`, so the limit-side pushforward reduces to `ν.map Φ`.
The hard piece is the *joint* weak convergence `(S_n, R_n) ⇒ ν.prod δ_0` on
the product space `EuclideanSpace ℝ (Fin m) × (ι → ℝ)`, pushed through the
continuous bivariate map `Ψ (Δ, ρ) i := Φ Δ i * ofReal (exp (ρ i))`.

**Proof outline**:

1. Define `Ψ : EuclideanSpace ℝ (Fin m) × (ι → ℝ) → (ι → ℝ≥0∞)` by
   `Ψ (Δ, ρ) i := Φ Δ i * ENNReal.ofReal (Real.exp (ρ i))`, continuous on
   the product topology. At `ρ = 0`, `Ψ (Δ, 0) = Φ Δ` pointwise (since
   `exp 0 = 1` and `ofReal 1 = 1`).
2. From per-`ι` `hR_zero` (and finite `ι`) build joint convergence in
   probability `R_n →ᵖ 0` in the `sup`-norm on `ι → ℝ` via the union bound.
3. Bridge the per-`n` source spaces into one fixed `Measure.infinitePi`
   source, giving `TendstoInDistribution` for `S'_n → id` (from `h_S_conv`)
   and `TendstoInMeasure` for `R'_n → 0`.
4. Apply Mathlib's
   `tendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`
   through `Ψ`, giving `TendstoInDistribution (Ψ ∘ (S'_n, R'_n))` to `Ψ(·,0)`.
5. Identify the limit pushforward `ν.map (Ψ(·,0)) = ν.map Φ` via the pointwise
   identity `Ψ (Δ, 0) = Φ Δ`, then translate back to `WeakConverges`. -/
private lemma weakConverges_grid_product_pushforward
    {m : ℕ} {ι : Type*} [Fintype ι]
    (Φ : EuclideanSpace ℝ (Fin m) → (ι → ℝ≥0∞))
    (hΦ_cont : Continuous Φ)
    (hΦ_meas : Measurable Φ)
    (S_n : (n : ℕ) → (Fin n → Ω) → EuclideanSpace ℝ (Fin m))
    (R_n : (n : ℕ) → (Fin n → Ω) → ι → ℝ)
    (hS_meas : ∀ n, Measurable (S_n n))
    (hR_meas : ∀ n, Measurable (R_n n))
    (hR_zero : ∀ i : ι, ∀ ε > 0,
      Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ |R_n n X i|})
        atTop (𝓝 (0 : ℝ≥0∞)))
    {ν : Measure (EuclideanSpace ℝ (Fin m))} [IsProbabilityMeasure ν]
    (h_S_conv :
      WeakConverges
        (fun n => (Measure.pi (fun _ : Fin n => P)).map (S_n n)) ν) :
    WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            fun i : ι => Φ (S_n n X) i
              * ENNReal.ofReal (Real.exp (R_n n X i))))
      (ν.map Φ) := by
  classical
  -- Step 1: bivariate continuous map `Ψ : E × (ι → ℝ) → (ι → ℝ≥0∞)`.
  set Ψ : EuclideanSpace ℝ (Fin m) × (ι → ℝ) → (ι → ℝ≥0∞) :=
    fun p i => Φ p.1 i * ENNReal.ofReal (Real.exp (p.2 i)) with hΨ_def
  have hΨ_cont : Continuous Ψ := by
    refine continuous_pi (fun i => ?_)
    -- multiplication on `ℝ≥0∞` is continuous when the right factor is in `(0, ∞)`.
    refine Continuous.ennreal_mul
      ((continuous_apply i).comp (hΦ_cont.comp continuous_fst))
      (ENNReal.continuous_ofReal.comp <|
        Real.continuous_exp.comp <| (continuous_apply i).comp continuous_snd)
      (fun p => Or.inr (by
        -- `ENNReal.ofReal (Real.exp _) ≠ ∞`.
        simp [ENNReal.ofReal_ne_top]))
      (fun p => Or.inl (by
        -- `ENNReal.ofReal (Real.exp r) ≠ 0`, since `Real.exp r > 0`.
        have hpos : (0 : ℝ) < Real.exp (p.2 i) := Real.exp_pos _
        exact (ENNReal.ofReal_pos.mpr hpos).ne'))
  -- At `ρ = 0`, `Ψ(·, 0) = Φ` pointwise.
  have hΨ_at_zero : ∀ x : EuclideanSpace ℝ (Fin m),
      Ψ (x, (0 : ι → ℝ)) = Φ x := by
    intro x; funext i
    simp [hΨ_def]
  -- Step 2: bridge per-`n` source spaces into one fixed source `μ_fixed`.
  set μ_fixed : Measure ((n : ℕ) → (Fin n → Ω)) :=
    Measure.infinitePi (fun n : ℕ => Measure.pi (fun _ : Fin n => P))
    with hμ_fixed_def
  haveI : IsProbabilityMeasure μ_fixed := by
    rw [hμ_fixed_def]; infer_instance
  have h_map_eval : ∀ n : ℕ,
      μ_fixed.map (fun X : (n : ℕ) → (Fin n → Ω) => X n)
        = Measure.pi (fun _ : Fin n => P) := by
    intro n
    rw [hμ_fixed_def]
    exact Measure.infinitePi_map_eval _ n
  -- Lifted maps on the fixed source.
  set S'_n : (n : ℕ) → ((n : ℕ) → (Fin n → Ω)) → EuclideanSpace ℝ (Fin m) :=
    fun n X => S_n n (X n) with hS'_def
  set R'_n : (n : ℕ) → ((n : ℕ) → (Fin n → Ω)) → (ι → ℝ) :=
    fun n X => R_n n (X n) with hR'_def
  have hS'_meas : ∀ n, Measurable (S'_n n) := fun n =>
    (hS_meas n).comp (measurable_pi_apply n)
  have hR'_meas : ∀ n, Measurable (R'_n n) := fun n =>
    (hR_meas n).comp (measurable_pi_apply n)
  -- Step 3: `TendstoInDistribution S'_n → id` on `μ_fixed` with target `ν`.
  have h_S'_dist : TendstoInDistribution S'_n atTop
      (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
      (fun _ => μ_fixed) ν := by
    refine ⟨fun n => (hS'_meas n).aemeasurable,
            measurable_id.aemeasurable, ?_⟩
    have h_seq_eq : ∀ n, μ_fixed.map (S'_n n)
        = (Measure.pi (fun _ : Fin n => P)).map (S_n n) := by
      intro n
      change μ_fixed.map ((S_n n) ∘ (fun X : (n : ℕ) → (Fin n → Ω) => X n)) = _
      rw [← Measure.map_map (hS_meas n) (measurable_pi_apply n), h_map_eval n]
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
    intro f
    have h_target : Tendsto (fun n => ∫ x, f x ∂(μ_fixed.map (S'_n n)))
        atTop (𝓝 (∫ x, f x ∂(ν.map (id : EuclideanSpace ℝ (Fin m) → _)))) := by
      rw [Measure.map_id]
      simp_rw [h_seq_eq]
      exact h_S_conv f
    exact h_target
  -- Step 4: per-`ι` `hR_zero` ⇒ joint `TendstoInMeasure R'_n → 0` (sup-norm).
  have h_R'_zero :
      TendstoInMeasure μ_fixed R'_n atTop (fun _ => (0 : ι → ℝ)) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    -- Per-`ι` lift: each coord-level set on `μ_fixed` equals the per-`n` Pi-measure
    -- of the corresponding `Fin n → Ω` set.
    have h_per_ι : ∀ i,
        Tendsto (fun n : ℕ =>
          μ_fixed {X : (n : ℕ) → (Fin n → Ω) | ε ≤ |R_n n (X n) i|})
          atTop (𝓝 (0 : ℝ≥0∞)) := by
      intro i
      have h_set_meas : ∀ n,
          MeasurableSet {X : Fin n → Ω | ε ≤ |R_n n X i|} := fun n =>
        measurableSet_le measurable_const
          ((measurable_pi_apply i).comp (hR_meas n)).abs
      have h_preimage : ∀ n,
          {X : (n : ℕ) → (Fin n → Ω) | ε ≤ |R_n n (X n) i|}
            = (fun X : (n : ℕ) → (Fin n → Ω) => X n) ⁻¹'
                {X : Fin n → Ω | ε ≤ |R_n n X i|} := fun n => by ext X; rfl
      have h_eq : ∀ n,
          μ_fixed {X : (n : ℕ) → (Fin n → Ω) | ε ≤ |R_n n (X n) i|}
            = (Measure.pi (fun _ : Fin n => P))
                {X : Fin n → Ω | ε ≤ |R_n n X i|} := by
        intro n
        rw [h_preimage n,
            ← Measure.map_apply (measurable_pi_apply n) (h_set_meas n),
            h_map_eval n]
      simp_rw [h_eq]
      exact hR_zero i ε hε
    -- Pointwise set inclusion: `{ε ≤ ‖R'_n‖} ⊆ ⋃ i, {ε ≤ |R_n i|}`.
    have h_subset : ∀ n,
        {X : (n : ℕ) → (Fin n → Ω) | ε ≤ dist (R'_n n X) (0 : ι → ℝ)} ⊆
          ⋃ i : ι, {X | ε ≤ |R_n n (X n) i|} := by
      intro n X hX
      simp only [Set.mem_setOf_eq, dist_zero_right] at hX
      -- `hX : ε ≤ ‖R'_n n X‖`. Use contrapositive of `pi_norm_lt_iff'`.
      by_contra h_neg
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at h_neg
      -- Reduce `dist (R'_n n X) 0 < ε` to per-coord via `dist_pi_lt_iff`.
      have h_each : ∀ i, dist (R_n n (X n) i) (0 : ℝ) < ε := fun i => by
        rw [Real.dist_eq, sub_zero]; exact h_neg i
      have h_sup : dist (R_n n (X n)) (0 : ι → ℝ) < ε :=
        (dist_pi_lt_iff hε).mpr h_each
      have h_sup' : ‖R_n n (X n)‖ < ε := by
        rw [← dist_zero_right]; exact h_sup
      exact absurd hX (not_le.mpr h_sup')
    -- Union bound + each summand → 0 gives the full statement.
    have h_sum_zero : Tendsto
        (fun n : ℕ => ∑ i : ι, μ_fixed {X | ε ≤ |R_n n (X n) i|})
        atTop (𝓝 (0 : ℝ≥0∞)) := by
      have : (0 : ℝ≥0∞) = ∑ _i : ι, (0 : ℝ≥0∞) := by simp
      rw [this]
      exact tendsto_finset_sum _ (fun i _ => h_per_ι i)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum_zero
      (Eventually.of_forall fun _ => zero_le) ?_
    refine Eventually.of_forall fun n => ?_
    calc μ_fixed {X | ε ≤ dist (R'_n n X) (0 : ι → ℝ)}
        ≤ μ_fixed (⋃ i : ι, {X | ε ≤ |R_n n (X n) i|}) := measure_mono (h_subset n)
      _ ≤ ∑ i : ι, μ_fixed {X | ε ≤ |R_n n (X n) i|} :=
          measure_iUnion_fintype_le _ _
  -- Step 5: invoke Mathlib's Slutsky-product + continuous-mapping at one shot.
  have h_main : TendstoInDistribution
      (fun n X => Ψ (S'_n n X, R'_n n X)) atTop
      (fun x : EuclideanSpace ℝ (Fin m) => Ψ ((id x), (0 : ι → ℝ)))
      (fun _ => μ_fixed) ν :=
    h_S'_dist.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := Ψ) hΨ_cont h_R'_zero (fun n => (hR'_meas n).aemeasurable)
  -- Step 6: identify limit pushforward `ν.map (Ψ(·,0)) = ν.map Φ`.
  have h_target_eq :
      ν.map (fun x : EuclideanSpace ℝ (Fin m) => Ψ ((id x), (0 : ι → ℝ)))
        = ν.map Φ :=
    Measure.map_congr (Eventually.of_forall (fun x => hΨ_at_zero x))
  -- Step 7: translate `TendstoInDistribution` back to `WeakConverges`.
  intro f
  have h_tendsto := h_main.tendsto
  replace h_tendsto := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_tendsto
  have h_tendsto_f := h_tendsto f
  -- LHS sequence: μ_fixed.map (Ψ ∘ (S'_n, R'_n)) = Pⁿ.map (Ψ ∘ (S_n, R_n)).
  have h_LHS_eq : ∀ n,
      μ_fixed.map (fun X : (n : ℕ) → (Fin n → Ω) => Ψ (S'_n n X, R'_n n X))
        = (Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω =>
              fun i : ι =>
                Φ (S_n n X) i * ENNReal.ofReal (Real.exp (R_n n X i))) := by
    intro n
    have h_factor :
        (fun X : (n : ℕ) → (Fin n → Ω) => Ψ (S'_n n X, R'_n n X))
          = (fun X : Fin n → Ω => Ψ (S_n n X, R_n n X)) ∘
              (fun X : (n : ℕ) → (Fin n → Ω) => X n) := rfl
    have h_inner_meas :
        Measurable (fun X : Fin n → Ω => Ψ (S_n n X, R_n n X)) :=
      hΨ_cont.measurable.comp ((hS_meas n).prodMk (hR_meas n))
    rw [h_factor, ← Measure.map_map h_inner_meas (measurable_pi_apply n),
        h_map_eval n]
  -- The goal is integral-convergence of `f` against the LHS sequence to the
  -- integral against `ν.map Φ`. Rewrite the LHS via `h_LHS_eq` and the RHS
  -- via `h_target_eq`, then apply `h_tendsto_f`.
  rw [← h_target_eq]
  simp_rw [← h_LHS_eq]
  exact h_tendsto_f

/-- **Combination-direction LR weak convergence.**

Weak convergence of the *grid-indexed* combination-LR vector: at each `j ∈ J`,
the combination direction `t_j := ∑_k j.val k • g_P k`. The basis-indexed
`jointLR_weakConverges` does not directly compose at grid points where
`|J| > m`, so this variant is stated over the grid `J`.

* **LHS**: weak conv of the grid-indexed LR vector
  `n ↦ Pⁿ.map (X ↦ fun j : ↥J, (γ t_j).lr_n n X)` on `↥J → ℝ≥0∞`.
* **RHS limit**: pushforward of the standard multivariate Gaussian on
  `EuclideanSpace ℝ (Fin m)` under the continuous map
  `Δ ↦ (j ↦ ENNReal.ofReal (exp(⟨j.val, Δ⟩ − ½ ∑_k j.val k² ‖g_P k‖²)))`,
  i.e. the `gridLR g_P J` map. `gridLR` itself is not imported here (it would
  create an import cycle), so the conclusion inlines the formula.

**Proof outline**:

1. Apply `combinationLAN_factorization_witness` to pull per-`j` LAN witnesses
   `r_j n X` with `r_j →ᵖ 0` Pⁿ-a.e. and the per-`j` AE identity
   `(γ t_j).lr_n n X = ENNReal.ofReal (exp(scoreSumScalar (t_j) - ½‖t_j‖² + r_j))`.
2. Reduce `scoreSumScalar (t_j) =ᵃᵉ ⟪j.val, jointScoreSum g_P n X⟫_ℝ`
   via `inner_jointScoreSum_eq_ae_scoreSumScalar` applied at
   `h := j.val : EuclideanSpace ℝ (Fin m)` (defeq to `Fin m → ℝ`).
3. Pⁿ-AE identity of the LHS vector:
   `(fun j ↦ (γ t_j).lr_n n X) =ᵃᵉ
    (fun j ↦ gridLR_inline(jointScoreSum g_P n X) j * ofReal(exp(r_j n X)))`,
   using `exp(⟨j.val, Δ⟩ - ½‖t_j‖² + r) = exp(⟨j.val, Δ⟩ - ½‖t_j‖²) * exp(r)`.
4. Apply `weakConverges_grid_product_pushforward` with `S_n := jointScoreSum`,
   `R_n := r`, `ν := multivariateGaussian 0 1`, and `Φ` the inlined `gridLR`
   map, composing the joint Δ-CLT with the per-`j` `r_j →ᵖ 0`.

Under orthonormality `h_orth`, `∑_k j.val k² ‖g_P k‖² = ‖t_j‖²` by Pythagoras;
the `‖g_P k‖²` form (matching `gridLR`'s definition) is what shows up naturally.
-/
theorem combinationLR_weakConverges
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (γ : ↥(L2ZeroMean P) → QMDPath P)
    -- vdV §25 standing (dominated case). Threaded through to
    -- `combinationLAN_factorization_witness` + `sum_log_p_0_zero_ae_pi`.
    (hDom : ∀ g, (γ g).dominating = P)
    -- vdV §25 standing (dominated case). Threaded through to `lr_n_pos_finite_ae_pi`.
    (hAC : ∀ g n, P ≪ (γ g).curve ((Real.sqrt n)⁻¹))
    (J : Finset (Fin m → ℝ))
    -- Score identity at the combination directions `t_j := ∑_k j.val k • g_P k`
    -- for `j ∈ J`. Caller may discharge this from an unconditional
    -- `∀ g, (γ g).score = g` or from a conditional `∀ g ∈ C, (γ g).score = g`
    -- whenever every `t_j` lies in `C` (the cone+convex closure of the basis).
    (h_score_image : ∀ j : ↥J,
      (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).score
        = ∑ k, j.val k • (g_P k : ↥(L2ZeroMean P))) :
    WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            fun j : ↥J =>
              (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).lr_n n X))
      ((ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin m))
          (1 : Matrix (Fin m) (Fin m) ℝ)).map
        (fun Δ : EuclideanSpace ℝ (Fin m) =>
          fun j : ↥J =>
            ENNReal.ofReal (Real.exp
              (∑ k : Fin m, j.val k * Δ k
                - (1/2 : ℝ) * ∑ k : Fin m, (j.val k) ^ 2
                    * ‖(g_P k : Lp ℝ 2 P)‖ ^ 2)))) := by
  classical
  -- Step 1: per-`j` LAN factorization witnesses.
  obtain ⟨r, hr_meas, hr_factor, hr_zero⟩ :=
    combinationLAN_factorization_witness (P := P) (g_P := g_P) γ hDom hAC J h_score_image
  -- Step 2: joint Δ-CLT under `Pⁿ`.
  have h_jointDelta := jointDelta_weakConverges_under_pi (P := P) g_P h_orth
  -- Step 3: define the grid-LR pushforward map `Φ` (continuous).
  let Φ : EuclideanSpace ℝ (Fin m) → (↥J → ℝ≥0∞) := fun Δ j =>
    ENNReal.ofReal (Real.exp
      (∑ k : Fin m, j.val k * Δ k
        - (1/2 : ℝ) * ∑ k : Fin m, (j.val k) ^ 2
            * ‖(g_P k : Lp ℝ 2 P)‖ ^ 2))
  have hΦ_cont : Continuous Φ := by
    refine continuous_pi (fun j : ↥J => ?_)
    refine ENNReal.continuous_ofReal.comp ?_
    refine Real.continuous_exp.comp ?_
    refine Continuous.sub ?_ continuous_const
    refine continuous_finset_sum _ (fun k _ => ?_)
    exact continuous_const.mul
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin m) k).continuous
  have hΦ_meas : Measurable Φ := hΦ_cont.measurable
  -- Step 4: orthonormality identity — `‖t_j‖² = Σ_k (j.val k)² ‖g_P k‖²`.
  -- Inner-product expansion (`Orthonormal.inner_sum`) gives `Σ_k (j.val k)²`,
  -- and `‖g_P k‖ = 1` from `h_orth.norm_eq_one` lifts each factor to
  -- `(j.val k)² * ‖g_P k‖²`.
  have h_norm_one : ∀ k : Fin m, ‖(g_P k : Lp ℝ 2 P)‖ = 1 := by
    intro k
    have h := h_orth.1 k
    -- h : ‖g_P k‖ = 1 in ↥(L2ZeroMean P); submodule-coerce-to-Lp keeps the norm.
    exact h
  have h_norm_sq : ∀ j : ↥J,
      ‖((∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)) :
            ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ ^ 2
        = ∑ k : Fin m, (j.val k) ^ 2 * ‖(g_P k : Lp ℝ 2 P)‖ ^ 2 := by
    intro j
    -- Reduce LHS to inner-product form on `↥(L2ZeroMean P)`.
    have h_norm_coe :
        ‖((∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)) :
              ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖
          = ‖(∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)) :
                ↥(L2ZeroMean P))‖ := by
      rfl
    rw [h_norm_coe]
    rw [← @real_inner_self_eq_norm_sq ↥(L2ZeroMean P) _ _]
    rw [Orthonormal.inner_sum h_orth]
    -- Goal (after Orthonormal.inner_sum): `∑ k, conj (j.val k) * j.val k
    --   = ∑ k, (j.val k) ^ 2 * ‖g_P k‖²`. `conj` on `ℝ` is the identity.
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [starRingEnd_apply, star_trivial]
    rw [h_norm_one k, one_pow, mul_one, sq]
  -- Step 5: Pⁿ-AE identification of the LHS sequence with the Φ-product form.
  have h_LHS_AE : ∀ n,
      (fun X : Fin n → Ω =>
          fun j : ↥J =>
            (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).lr_n n X)
        =ᵐ[Measure.pi (fun _ : Fin n => P)]
        (fun X : Fin n → Ω =>
          fun j : ↥J =>
            Φ (jointScoreSum (P := P) g_P n X) j
              * ENNReal.ofReal (Real.exp (r j n X))) := by
    intro n
    have h_per : ∀ j : ↥J,
        ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
          (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).lr_n n X
            = Φ (jointScoreSum (P := P) g_P n X) j
                * ENNReal.ofReal (Real.exp (r j n X)) := by
      intro j
      have h_factor := hr_factor j n
      -- Cast `j.val : Fin m → ℝ` to `EuclideanSpace ℝ (Fin m)` via the
      -- continuous linear equiv (Mathlib's `WithLp` requires explicit
      -- conversion despite the underlying types being defeq).
      set j_eu : EuclideanSpace ℝ (Fin m) :=
        (EuclideanSpace.equiv (Fin m) ℝ).symm j.val with hj_eu
      have h_inner :=
        inner_jointScoreSum_eq_ae_scoreSumScalar (P := P) g_P j_eu n
      -- `j_eu k = j.val k` pointwise (defeq via the equiv's underlying Pi).
      have h_jeu_k : ∀ k : Fin m, j_eu k = j.val k := fun k => rfl
      -- `linComb g_P j_eu = ∑ k, j.val k • g_P k` (defeq).
      have h_linComb_eq :
          linComb (P := P) g_P j_eu
            = ∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)) := rfl
      filter_upwards [h_factor, h_inner] with X hF hI
      rw [hF]
      rw [h_norm_sq j]
      have h_inner_swap :
          (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.JointLAN.scoreSumScalar
              (P := P) (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P))) n X : ℝ)
            = (⟪j_eu, jointScoreSum (P := P) g_P n X⟫_ℝ : ℝ) := by
        -- hI : ⟪j_eu, jointScoreSum⟫ = scoreSumScalar(linComb g_P j_eu).
        -- linComb g_P j_eu = ∑ k, j.val k • g_P k (by h_linComb_eq).
        rw [← h_linComb_eq]; exact hI.symm
      rw [h_inner_swap]
      -- Unfold Φ on the RHS.
      show ENNReal.ofReal (Real.exp _)
          = ENNReal.ofReal (Real.exp _) * ENNReal.ofReal (Real.exp _)
      -- Inner product on `EuclideanSpace ℝ (Fin m)` reduces to a scalar sum.
      have h_inner_apply :
          (⟪j_eu, jointScoreSum (P := P) g_P n X⟫_ℝ : ℝ)
            = ∑ k : Fin m, j.val k * jointScoreSum (P := P) g_P n X k := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        -- `⟪a, b⟫_ℝ` for reals: `b * a`; commute to `a * b`.
        change jointScoreSum (P := P) g_P n X k * j_eu k = _
        rw [h_jeu_k]; ring
      rw [h_inner_apply]
      -- Split `exp(a + b) = exp a * exp b` then push through `ofReal`.
      rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    -- Combine per-`j` AE-equalities into a single `Pⁿ`-AE statement, then
    -- `funext` to functional AE-equality.
    have h_all :
        ∀ᵐ X : Fin n → Ω ∂(Measure.pi (fun _ : Fin n => P)),
          ∀ j : ↥J,
            (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).lr_n n X
              = Φ (jointScoreSum (P := P) g_P n X) j
                  * ENNReal.ofReal (Real.exp (r j n X)) := by
      rw [ae_all_iff]
      exact h_per
    filter_upwards [h_all] with X hX
    funext j
    exact hX j
  -- Step 6: rewrite the LHS sequence via `Measure.map_congr` against the
  -- AE-identity, producing the Φ-product form.
  have h_lhs_eq : ∀ n,
      (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            fun j : ↥J =>
              (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).lr_n n X)
        = (Measure.pi (fun _ : Fin n => P)).map
            (fun X : Fin n → Ω =>
              fun j : ↥J =>
                Φ (jointScoreSum (P := P) g_P n X) j
                  * ENNReal.ofReal (Real.exp (r j n X))) := by
    intro n
    exact Measure.map_congr (h_LHS_AE n)
  have h_seq_eq :
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω =>
            fun j : ↥J =>
              (γ (∑ k, j.val k • (g_P k : ↥(L2ZeroMean P)))).lr_n n X))
        = fun n : ℕ =>
            (Measure.pi (fun _ : Fin n => P)).map
              (fun X : Fin n → Ω =>
                fun j : ↥J =>
                  Φ (jointScoreSum (P := P) g_P n X) j
                    * ENNReal.ofReal (Real.exp (r j n X))) := by
    funext n; exact h_lhs_eq n
  rw [h_seq_eq]
  -- Step 7: target RHS is `multivariateGaussian.map Φ` (definitionally, since
  -- `Φ` inlines the same formula). Apply the Slutsky-product sub-lemma with
  -- `S_n := jointScoreSum g_P n`, `R_n := fun X j => r j n X`,
  -- `ν := multivariateGaussian 0 1`.
  have hR_meas_joint : ∀ n,
      Measurable (fun X : Fin n → Ω => fun j : ↥J => r j n X) :=
    fun n => measurable_pi_lambda _ (fun j => hr_meas j n)
  exact weakConverges_grid_product_pushforward (P := P)
    (Φ := Φ) hΦ_cont hΦ_meas
    (S_n := fun n => jointScoreSum (P := P) g_P n)
    (R_n := fun n X j => r j n X)
    (hS_meas := fun n => measurable_jointScoreSum (P := P) g_P n)
    (hR_meas := hR_meas_joint)
    (hR_zero := hr_zero)
    (ν := ProbabilityTheory.multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin m))
      (1 : Matrix (Fin m) (Fin m) ℝ))
    h_jointDelta

end JointLRWeakConverges

end AsymptoticStatistics.LowerBounds.T7_AndersonClosure
