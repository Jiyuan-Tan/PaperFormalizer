module
public import StatLean.AsymptoticStatistics.Efficiency.LocalAsymptoticMinimax
public import StatLean.AsymptoticStatistics.ParametricFamily.SubmodelDQM
public import StatLean.AsymptoticStatistics.ParametricFamily.SubmodelFromScores
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorDerivations
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Core.TangentAbstract
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import StatLean.AsymptoticStatistics.Core.Pathwise

@[expose] public section

/-!
# Bridge: from orthonormal bounded basis to the parametric local asymptotic minimax bound

This file builds the adapter pieces that reduce the **semiparametric** local
asymptotic minimax (LAM) bound to the **parametric** LAM bound by restricting to
sufficiently rich finite-dimensional submodels. Given a scalar functional
$\psi$ on a semiparametric model with tangent set $\dot{\mathcal P}$, a bounded
orthonormal system $g_1,\dots,g_m$ in the tangent space, and the efficient
influence function $\tilde\ell_\psi$, the construction does the following.

It forms the $m$-dimensional submodel spanned by $g_1,\dots,g_m$ and the lifted
parametric functional $\theta \mapsto \psi$ evaluated along that submodel
(`ψ_param`). This parametric functional is Fréchet-differentiable at $0$, with
derivative the row vector
$A = \bigl(\langle \tilde\ell_\psi, g_1\rangle,\dots,\langle \tilde\ell_\psi, g_m\rangle\bigr)$
of inner products of the efficient influence function against the basis
(`ψ_param_HasFDerivAt`). Because every direction $h \in \mathbb R^m$ corresponds
to the tangent vector $h^\top g = \sum_j h_j g_j$ — which lies in the tangent
set whenever the latter is a linear space — the parametric LAM left-hand side
(a supremum over finite subsets of $\mathbb R^m$) is dominated by the
semiparametric LAM left-hand side (a supremum over finite subsets of the tangent
set) (`paramLam_LHS_le_semiparametric_LHS`). Chaining the parametric LAM bound
through these two facts produces the per-submodel lower bound
$\int L\,\mathrm dN(0, A A^\top)$ needed for the semiparametric LAM theorem.

The multi-parameter submodel construction from a bounded orthonormal basis is
reused from `AsymptoticStatistics.ParametricFamily.SubmodelDQM` (`paramSubmodel`
and its differentiability-in-quadratic-mean / Fisher-information / support
properties).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information) and Theorem 25.21 (§25.3)
(the local asymptotic minimax theorem for semiparametric models, reducing the
semiparametric bound to parametric submodels). The submodel-reduction strategy
formalized here is exactly the device by which the convolution / minimax
theorems of §25.3 are applied to one-dimensional (and finite-dimensional)
submodels through the tangent set.

**Proof formalization notes.** The pieces added here:

* `ψ_param` — the parametric functional `θ ↦ ψ(paramSubmodel-curve at θ)`
  built from a scalar semiparametric functional `ψ : Measure Ω → ℝ`.
* `ψ_param_HasFDerivAt` — Fréchet differentiability at `0` with matrix-form
  derivative `A : Matrix (Fin 1) (Fin m) ℝ` whose single row is
  `(⟨IF_eff, g_1⟩, …, ⟨IF_eff, g_m⟩)`.
* `paramLam_LHS_le_semiparametric_LHS` — the LHS inclusion
  `parametric-LAM-LHS-at-paramSubmodel ≤ semiparametric-LAM-LHS`. The key
  argument: every `h ∈ ℝ^m` corresponds to `h^T g_P ∈ T_set.carrier`
  (linear-span case), so the parametric SUP-over-ℝ^m is a sub-SUP of the
  semiparametric SUP-over-T_set.

Two book-vs-Lean deviations are made explicit as hypotheses rather than left
implicit as vdV does. First, the differentiability argument carries a
Hadamard-style uniform-in-tangent linear-approximation remainder
(`_hψ_Hadamard_remainder`), which vdV folds into the standing regularity of
§25. Second, `paramLam_LHS_le_semiparametric_LHS` requires the tangent set to be
a linear space (not merely a cone) via `_h_linspan_in_tset`, and requires an
explicit alignment hypothesis `_h_γ_aligns` identifying the abstract path family
with the concrete `paramSubmodel`-density measures along basis-spanned
directions — an equivalence vdV's Theorem 25.21 (§25.3) proof assumes silently.

**Bibliographic comments.** The submodel-reduction technique for semiparametric
efficiency lower bounds — bounding the semiparametric minimax risk below by the
risk of richest finite-dimensional parametric submodels — originates with the
systematic theory of P. J. Bickel, C. A. J. Klaassen, Y. Ritov & J. A. Wellner,
*Efficient and Adaptive Estimation for Semiparametric Models*, Johns Hopkins
University Press, 1993 (reprinted Springer, 1998); the tangent-space / efficient
influence function calculus used here is developed there in Chapters 2–3. The
local asymptotic minimax formulation and its reduction to least-favorable
parametric submodels trace back to J. Hájek, "Local asymptotic minimax and
admissibility in estimation", *Proc. Sixth Berkeley Symp. Math. Statist.
Probab.* 1 (1972), 175–194, and to the convolution theorem of J. Hájek, "A
characterization of limiting distributions of regular estimators",
*Z. Wahrsch. Verw. Gebiete* 14 (1970), 323–330; the synthesis of these
into the semiparametric submodel argument is van der Vaart's §25.3 / Theorem 25.21 (§25.3).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics.Core.MassMethod
open AsymptoticStatistics
open AsymptoticStatistics
open scoped RealInnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.LowerBounds.RegularEstimator

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℕ}

/-- Convenience alias for the parameter type `ℝ^m`. Mirrors
`LocalAsymptoticMinimax.Θ`. -/
abbrev Θ (m : ℕ) : Type := EuclideanSpace ℝ (Fin m)

/-- **Functional adapter.** Given a scalar functional `ψ : Measure Ω
→ ℝ`, define the parametric functional `ψ_param : ℝ^m → ℝ^1` by lifting
`ψ` to the `paramSubmodel`-induced measures.

Implementation: at parameter `θ ∈ ℝ^m`, `paramSubmodel.density θ` is a
density w.r.t. `P`; the corresponding measure is `P.withDensity (...)`.
We package the scalar value `ψ` returns into a 1-D `EuclideanSpace` form. -/
noncomputable def ψ_param
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → ℝ) :
    Θ m → EuclideanSpace ℝ (Fin 1) :=
  fun θ => (WithLp.equiv 2 _).symm
    (fun _ : Fin 1 => ψ (P.withDensity
      (fun x => ENNReal.ofReal ((paramSubmodel g_P hg h_orth).density θ x))))

/-- Derivative matrix `A : Matrix (Fin 1) (Fin m) ℝ` whose single row is
`(⟨IF_eff, g_P 1⟩, …, ⟨IF_eff, g_P m⟩)`. This is the parametric form of
the EIF inner product against the basis. -/
noncomputable def ψDotMat
    (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) :
    Matrix (Fin 1) (Fin m) ℝ :=
  fun _ j => @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (g_P j)

/-- Measurability of `ψ_param` from a global measurability hypothesis on
`ψ : Measure Ω → ℝ` (using `Measure Ω`'s standard σ-algebra, generated by
`μ → μ(s)` for measurable `s`).

Proof structure:
1. `ψ_param θ = WithLp.toLp 2 (fun _ : Fin 1 => ψ (P.withDensity (density θ ·)))`.
2. `θ → P.withDensity (density θ ·)` is `Measure Ω`-valued measurable via
   `MeasureTheory.Measure.measurable_of_measurable_coe`: it suffices to check
   that for every measurable set `s`, `θ → P.withDensity (density θ ·) s` is
   measurable; this unfolds to `θ → ∫⁻ ω in s, ENNReal.ofReal (density θ ω) ∂P`,
   which is measurable by `Measurable.setLIntegral_kernel_prod_right` applied
   to the constant kernel `Kernel.const _ P` (joint measurability of the
   density-of-real is provided by `paramSubmodel_density_joint_meas`).
3. Compose with `h_ψ_meas : Measurable ψ` to get measurability of the scalar
   composition, then wrap into `Fin 1` and apply `WithLp.measurable_toLp`. -/
theorem ψ_param_measurable_of_ψ_measurable
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    {ψ : Measure Ω → ℝ} (h_ψ_meas : Measurable ψ) :
    Measurable (ψ_param g_P hg h_orth ψ) := by
  -- Joint measurability of the density.
  have h_dens_meas : Measurable
      (Function.uncurry (paramSubmodel g_P hg h_orth).density) :=
    paramSubmodel_density_joint_meas g_P hg h_orth
  have h_ofReal_meas : Measurable (fun p : Θ m × Ω =>
      ENNReal.ofReal ((paramSubmodel g_P hg h_orth).density p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp h_dens_meas
  -- Measurability of θ → P.withDensity(density θ ·) as a Measure-Ω-valued map.
  have h_withDens_meas : Measurable (fun θ : Θ m =>
      P.withDensity (fun ω => ENNReal.ofReal
        ((paramSubmodel g_P hg h_orth).density θ ω))) := by
    refine MeasureTheory.Measure.measurable_of_measurable_coe _ ?_
    intro s hs
    -- (P.withDensity f) s = ∫⁻ ω in s, f ω ∂P (by withDensity_apply).
    simp_rw [MeasureTheory.withDensity_apply _ hs]
    -- Now measurability via Measurable.setLIntegral_kernel_prod_right with
    -- the constant kernel `Kernel.const _ P`.
    exact Measurable.setLIntegral_kernel_prod_right
      (κ := ProbabilityTheory.Kernel.const _ P)
      (f := fun θ ω => ENNReal.ofReal
        ((paramSubmodel g_P hg h_orth).density θ ω))
      h_ofReal_meas hs
  -- Compose with ψ to get measurability of the scalar part.
  have h_scalar_meas : Measurable (fun θ : Θ m =>
      ψ (P.withDensity (fun ω => ENNReal.ofReal
        ((paramSubmodel g_P hg h_orth).density θ ω)))) :=
    h_ψ_meas.comp h_withDens_meas
  -- Finally wrap into `Fin 1` and apply WithLp.measurable_toLp.
  unfold ψ_param
  exact (WithLp.measurable_toLp 2 (Fin 1 → ℝ)).comp
    (measurable_pi_iff.mpr (fun _ => h_scalar_meas))

/-- Matrix-form derivative as a continuous linear map. Built
from `ψDotMat g_P IF_eff : Matrix (Fin 1) (Fin m) ℝ` via `mulVecLin` and
the `WithLp` linear equivs, then promoted to a `ContinuousLinearMap` via
the finite-dim auto-instance. -/
noncomputable def ψDot_clm
    (g_P : Fin m → ↥(L2ZeroMean P)) (IF_eff : ↥(L2ZeroMean P)) :
    Θ m →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm.toLinearMap.comp
      ((ψDotMat g_P IF_eff).mulVecLin.comp
        (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap))

/-- `ψDot_clm` applies via `(ψDotMat ⋅).mulVec`. -/
lemma ψDot_clm_apply
    (g_P : Fin m → ↥(L2ZeroMean P)) (IF_eff : ↥(L2ZeroMean P)) (h : Θ m) :
    ψDot_clm g_P IF_eff h
      = (WithLp.equiv 2 _).symm
        ((ψDotMat g_P IF_eff).mulVec ((WithLp.equiv 2 _) h)) := by
  rfl

/-- Density-bridge: for `h` near 0, the parametric
submodel density equals `1 + linPerturbScore g_P h ω` a.e.; consequently
`ψ_param` of `h` matches the Hadamard-form `ψ (P.withDensity (1 + g·))`
target. -/
private theorem ψ_param_eq_hadamard_form_eventually
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → ℝ) :
    ∀ᶠ h : Θ m in 𝓝 0,
      ((WithLp.equiv 2 _) (ψ_param g_P hg h_orth ψ h)) 0
        = ψ (P.withDensity (fun ω => ENNReal.ofReal
            (1 + ((linPerturbScore g_P h : ↥(L2ZeroMean P)) : Ω → ℝ) ω))) := by
  have h_pos : 0 < truncRadius g_P hg := truncRadius_pos g_P hg
  have h_norm_tendsto : Filter.Tendsto (fun h : Θ m => ‖h‖) (𝓝 0) (𝓝 0) := by
    simpa [norm_zero] using (continuous_norm (E := Θ m)).tendsto 0
  filter_upwards [h_norm_tendsto (Iio_mem_nhds h_pos)] with h hh
  unfold ψ_param
  simp only [Equiv.apply_symm_apply]
  congr 1
  refine MeasureTheory.withDensity_congr_ae ?_
  have h_score := paramSubmodel_score_at_zero g_P hg h_orth h hh
  have h_lin := linPerturbScore_coe_ae g_P h
  filter_upwards [h_score, h_lin] with ω h1 h2
  rw [h1, ← h2]

/-- `ψ_param 0 = ψ P` at coord 0 (since
`paramSubmodel.density 0 = 1` so the withDensity is `P` itself). -/
private theorem ψ_param_zero_eq_ψ_P
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → ℝ) :
    ((WithLp.equiv 2 _) (ψ_param g_P hg h_orth ψ 0)) 0 = ψ P := by
  unfold ψ_param
  simp only [Equiv.apply_symm_apply]
  congr 1
  -- Goal: P.withDensity (fun x => ENNReal.ofReal (density 0 x)) = P
  have h_dens : ∀ x, (paramSubmodel g_P hg h_orth).density 0 x = 1 :=
    paramSubmodel_density_at_zero g_P hg h_orth
  have h_fun_eq : (fun x => ENNReal.ofReal ((paramSubmodel g_P hg h_orth).density 0 x))
      = (1 : Ω → ℝ≥0∞) := by
    funext x; rw [h_dens]
    simp [ENNReal.ofReal_one]
  rw [h_fun_eq, MeasureTheory.withDensity_one]

/-- For small `h`, the scalar difference unfolds as
`⟪IF_eff, linPerturbScore g_P h⟫ + ε_h` with `|ε_h| ≤ ‖linPerturbScore g_P h‖ * rem(...)`.

Proof: invokes `_hψ_Hadamard_remainder` at `g := linPerturbScore g_P h`,
then identifies `P.withDensity (1 + g·) = P.withDensity (paramSubmodel.density h)`
for small `h` via `ψ_param_eq_hadamard_form_eventually`. -/
theorem ψ_param_diff_eq_inner_plus_Hellinger_remainder
    (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    -- The body only needs each basis element in `tangentSpace T_set` (the
    -- topological-closure of the span), which is weaker than `T_set.carrier`
    -- membership, so the hypothesis is stated at that level.
    (h_basis_in_tspace : ∀ j, (g_P j : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    {ψ : Measure Ω → ℝ}
    {IF_eff : ↥(L2ZeroMean P)}
    (_hψ_Hadamard_remainder :
      ∃ rem : ℝ → ℝ,
        Filter.Tendsto rem (𝓝 0) (𝓝 0) ∧ rem 0 = 0 ∧
        ∀ (g : ↥(L2ZeroMean P)),
          (g : ↥(L2ZeroMean P)) ∈ tangentSpace T_set →
          |ψ (P.withDensity (fun ω => ENNReal.ofReal
              (1 + ((g : ↥(L2ZeroMean P)) : Ω → ℝ) ω)))
            - ψ P
            - ⟪(IF_eff : ↥(L2ZeroMean P)), g⟫|
            ≤ ‖(g : ↥(L2ZeroMean P))‖ * rem ‖(g : ↥(L2ZeroMean P))‖) :
    ∃ rem : ℝ → ℝ,
      Filter.Tendsto rem (𝓝 0) (𝓝 0) ∧ rem 0 = 0 ∧
      ∀ᶠ h : Θ m in 𝓝 0,
        |((WithLp.equiv 2 _) (ψ_param g_P hg h_orth ψ h)) 0
          - ((WithLp.equiv 2 _) (ψ_param g_P hg h_orth ψ 0)) 0
          - ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫|
          ≤ ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖
              * rem ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖ := by
  obtain ⟨rem, h_rem_tendsto, h_rem_zero, h_rem_bound⟩ := _hψ_Hadamard_remainder
  refine ⟨rem, h_rem_tendsto, h_rem_zero, ?_⟩
  have h_bridge := ψ_param_eq_hadamard_form_eventually g_P hg h_orth ψ
  filter_upwards [h_bridge] with h h_bridge_h
  rw [h_bridge_h, ψ_param_zero_eq_ψ_P g_P hg h_orth ψ]
  exact h_rem_bound (linPerturbScore g_P h)
    (linPerturbScore_mem_tangentSpace T_set g_P h_basis_in_tspace h)

/-- `‖linPerturbScore g_P h‖_{L²(P)} ≤ C·‖h‖` for some `C ≥ 0`.

Proof: triangle inequality `‖∑ h_i • g_P i‖ ≤ ∑ |h_i| · ‖g_P i‖` combined
with the coord-wise bound `|h_i| ≤ ‖h‖` in `EuclideanSpace`. Sets
`C := ∑ ‖g_P i‖`. -/
theorem linPerturbScore_norm_isBigO
    (g_P : Fin m → ↥(L2ZeroMean P))
    (_h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Θ m,
      ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖ ≤ C * ‖h‖ := by
  refine ⟨∑ i : Fin m, ‖(g_P i : ↥(L2ZeroMean P))‖, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  · intro h
    unfold linPerturbScore
    refine (norm_sum_le _ _).trans ?_
    have h_each : ∀ i ∈ Finset.univ,
        ‖(h i : ℝ) • (g_P i : ↥(L2ZeroMean P))‖
          ≤ ‖h‖ * ‖(g_P i : ↥(L2ZeroMean P))‖ := by
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le h i) (norm_nonneg _)
    calc ∑ i, ‖(h i : ℝ) • (g_P i : ↥(L2ZeroMean P))‖
        ≤ ∑ i, ‖h‖ * ‖(g_P i : ↥(L2ZeroMean P))‖ :=
          Finset.sum_le_sum h_each
      _ = (∑ i : Fin m, ‖(g_P i : ↥(L2ZeroMean P))‖) * ‖h‖ := by
          rw [mul_comm (∑ i : Fin m, ‖(g_P i : ↥(L2ZeroMean P))‖) ‖h‖,
            Finset.mul_sum]

/-- Coord-0 of `ψDot_clm h` equals `⟪IF_eff, linPerturbScore g_P h⟫`. -/
theorem ψDot_clm_coord_zero_eq_inner
    (g_P : Fin m → ↥(L2ZeroMean P)) (IF_eff : ↥(L2ZeroMean P)) (h : Θ m) :
    ((WithLp.equiv 2 _) (ψDot_clm g_P IF_eff h)) 0
      = ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫ := by
  -- LHS: ψDot_clm h = (WithLp.equiv).symm (ψDotMat.mulVec ((WithLp.equiv) h)),
  -- so (WithLp.equiv) (LHS) 0 = (ψDotMat.mulVec ((WithLp.equiv) h)) 0
  --   = ∑ j, ⟨IF_eff, g_P j⟩ * ((WithLp.equiv) h) j
  -- RHS: ⟪IF_eff, ∑ j, h j • g_P j⟫ = ∑ j, h j * ⟪IF_eff, g_P j⟫.
  -- Note: (WithLp.equiv 2 (Fin m → ℝ)) h j = h j  (definitionally)
  -- so the two are equal modulo mul_comm.
  have h_lhs : ((WithLp.equiv 2 _) (ψDot_clm g_P IF_eff h)) 0
      = ∑ j : Fin m,
          (@inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (g_P j))
            * ((WithLp.equiv 2 _) h) j := by
    rw [ψDot_clm_apply, Equiv.apply_symm_apply]
    rfl
  rw [h_lhs, linPerturbScore, inner_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [inner_smul_right]
  change ⟪(IF_eff : ↥(L2ZeroMean P)), g_P j⟫ * h.ofLp j
    = h.ofLp j * ⟪(IF_eff : ↥(L2ZeroMean P)), g_P j⟫
  ring

/-- Fréchet residual is `o(‖h‖)`. Assembled from the Hadamard
remainder upper bound, the norm-of-perturbation linear bound, the coord-0
identification, and `Asymptotics.isLittleO_iff`. -/
theorem ψ_param_residual_isLittleO
    (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    -- tangentSpace membership. See `ψ_param_diff_eq_inner_plus_Hellinger_remainder`
    -- for rationale.
    (h_basis_in_tspace : ∀ j, (g_P j : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    {ψ : Measure Ω → ℝ}
    (_hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
      _hψ.derivative IF_eff)
    (_hψ_Hadamard_remainder :
      ∃ rem : ℝ → ℝ,
        Filter.Tendsto rem (𝓝 0) (𝓝 0) ∧ rem 0 = 0 ∧
        ∀ (g : ↥(L2ZeroMean P)),
          (g : ↥(L2ZeroMean P)) ∈ tangentSpace T_set →
          |ψ (P.withDensity (fun ω => ENNReal.ofReal
              (1 + ((g : ↥(L2ZeroMean P)) : Ω → ℝ) ω)))
            - ψ P
            - ⟪(IF_eff : ↥(L2ZeroMean P)), g⟫|
            ≤ ‖(g : ↥(L2ZeroMean P))‖ * rem ‖(g : ↥(L2ZeroMean P))‖) :
    (fun h : Θ m =>
        ψ_param g_P hg h_orth ψ h
          - ψ_param g_P hg h_orth ψ 0
          - ψDot_clm g_P IF_eff h)
      =o[𝓝 (0 : Θ m)] (fun h : Θ m => h) := by
  obtain ⟨rem, h_rem_tendsto, _h_rem_zero, h_2a⟩ :=
    ψ_param_diff_eq_inner_plus_Hellinger_remainder T_set g_P hg h_orth
      h_basis_in_tspace _hψ_Hadamard_remainder
  obtain ⟨C, hC_nn, h_2b⟩ := linPerturbScore_norm_isBigO g_P h_orth
  -- Reduce to scalar via dim-1 norm equality.
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hC1_pos : (0 : ℝ) < C + 1 := by linarith
  have h_eps_target : (0 : ℝ) < ε / (C + 1) := div_pos hε hC1_pos
  have h_rem_small : ∀ᶠ s in 𝓝 (0 : ℝ), |rem s| < ε / (C + 1) := by
    have := (Metric.tendsto_nhds.1 h_rem_tendsto) (ε / (C + 1)) h_eps_target
    simpa [Real.dist_eq, sub_zero] using this
  have h_lin_to_zero : Filter.Tendsto
      (fun h : Θ m => ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖)
      (𝓝 0) (𝓝 0) := by
    have h_h_to_zero : Filter.Tendsto (fun h : Θ m => ‖h‖) (𝓝 0) (𝓝 0) := by
      simpa [norm_zero] using (continuous_norm (E := Θ m)).tendsto 0
    have h_bound_to_zero : Filter.Tendsto (fun h : Θ m => C * ‖h‖) (𝓝 0) (𝓝 0) := by
      simpa [mul_zero] using h_h_to_zero.const_mul C
    exact squeeze_zero (fun _ => norm_nonneg _) h_2b h_bound_to_zero
  have h_rem_via_lin : ∀ᶠ h : Θ m in 𝓝 0,
      |rem ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖| < ε / (C + 1) :=
    h_lin_to_zero.eventually h_rem_small
  filter_upwards [h_2a, h_rem_via_lin] with h h_bound h_rem_lin
  -- The vector residual norm equals |coord 0|.
  set res : EuclideanSpace ℝ (Fin 1) :=
    ψ_param g_P hg h_orth ψ h - ψ_param g_P hg h_orth ψ 0
      - ψDot_clm g_P IF_eff h with hres_def
  have h_res_norm_eq : ‖res‖ = |((WithLp.equiv 2 _) res) 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
      Real.sqrt_sq_eq_abs]
    rfl
  rw [h_res_norm_eq]
  have h_coord0 :
      ((WithLp.equiv 2 _) res) 0
        = ((WithLp.equiv 2 _) (ψ_param g_P hg h_orth ψ h)) 0
          - ((WithLp.equiv 2 _) (ψ_param g_P hg h_orth ψ 0)) 0
          - ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫ := by
    rw [hres_def, ← ψDot_clm_coord_zero_eq_inner g_P IF_eff h]
    rfl
  rw [h_coord0]
  -- Final calc: |LHS| ≤ ‖lin‖ * |rem ‖lin‖| ≤ (C ‖h‖) · ε/(C+1) ≤ ε ‖h‖.
  have h_lin_le : ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖ ≤ C * ‖h‖ := h_2b h
  have h_lin_nn : 0 ≤ ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖ := norm_nonneg _
  have h_step1 :
      |((WithLp.equiv 2 _) (ψ_param g_P hg h_orth ψ h)) 0
        - ((WithLp.equiv 2 _) (ψ_param g_P hg h_orth ψ 0)) 0
        - ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫|
        ≤ ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖
            * |rem ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖| :=
    h_bound.trans (mul_le_mul_of_nonneg_left (le_abs_self _) h_lin_nn)
  refine h_step1.trans ?_
  have h_step2 :
      ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖
          * |rem ‖(linPerturbScore g_P h : ↥(L2ZeroMean P))‖|
        ≤ (C * ‖h‖) * (ε / (C + 1)) :=
    mul_le_mul h_lin_le h_rem_lin.le (abs_nonneg _) (mul_nonneg hC_nn (norm_nonneg _))
  refine h_step2.trans ?_
  -- (C * ‖h‖) * (ε / (C + 1)) ≤ ε * ‖h‖
  rw [show (C * ‖h‖) * (ε / (C + 1)) = (C / (C + 1)) * (ε * ‖h‖) by ring]
  refine mul_le_of_le_one_left (mul_nonneg hε.le (norm_nonneg _)) ?_
  rw [div_le_one hC1_pos]
  linarith

/-- Fréchet assembly: little-o residual ⇒ `HasFDerivAt`. -/
theorem ψ_param_HasFDerivAt_of_residual
    (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    -- tangentSpace membership.
    (h_basis_in_tspace : ∀ j, (g_P j : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    {ψ : Measure Ω → ℝ}
    (_hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
      _hψ.derivative IF_eff)
    (_hψ_Hadamard_remainder :
      ∃ rem : ℝ → ℝ,
        Filter.Tendsto rem (𝓝 0) (𝓝 0) ∧ rem 0 = 0 ∧
        ∀ (g : ↥(L2ZeroMean P)),
          (g : ↥(L2ZeroMean P)) ∈ tangentSpace T_set →
          |ψ (P.withDensity (fun ω => ENNReal.ofReal
              (1 + ((g : ↥(L2ZeroMean P)) : Ω → ℝ) ω)))
            - ψ P
            - ⟪(IF_eff : ↥(L2ZeroMean P)), g⟫|
            ≤ ‖(g : ↥(L2ZeroMean P))‖ * rem ‖(g : ↥(L2ZeroMean P))‖) :
    HasFDerivAt (ψ_param g_P hg h_orth ψ) (ψDot_clm g_P IF_eff) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h_res := ψ_param_residual_isLittleO T_set g_P hg h_orth
    h_basis_in_tspace _hψ _hEIF _hψ_Hadamard_remainder
  simpa [zero_add] using h_res

/-- **Derivative of the parametric functional.** With pathwise
differentiability of `ψ` against the tangent space containing the basis,
the efficient influence function `IF_eff`, and a Hadamard-style
uniform-in-tangent linear approximation (vdV §25 standing regularity),
the parametric functional `ψ_param g_P hg h_orth ψ` is Fréchet
differentiable at `0`, with derivative given (in matrix form) by
`ψDotMat g_P IF_eff`. -/
theorem ψ_param_HasFDerivAt
    (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    -- tangentSpace membership.
    (h_basis_in_tspace : ∀ j, (g_P j : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    {ψ : Measure Ω → ℝ}
    (_hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
      _hψ.derivative IF_eff)
    (_hψ_Hadamard_remainder :
      ∃ rem : ℝ → ℝ,
        Filter.Tendsto rem (𝓝 0) (𝓝 0) ∧ rem 0 = 0 ∧
        ∀ (g : ↥(L2ZeroMean P)),
          (g : ↥(L2ZeroMean P)) ∈ tangentSpace T_set →
          |ψ (P.withDensity (fun ω => ENNReal.ofReal
              (1 + ((g : ↥(L2ZeroMean P)) : Ω → ℝ) ω)))
            - ψ P
            - ⟪(IF_eff : ↥(L2ZeroMean P)), g⟫|
            ≤ ‖(g : ↥(L2ZeroMean P))‖ * rem ‖(g : ↥(L2ZeroMean P))‖) :
    ∃ ψDot : Θ m →L[ℝ] EuclideanSpace ℝ (Fin 1),
      HasFDerivAt (ψ_param g_P hg h_orth ψ) ψDot 0
      ∧ ∀ h : Θ m,
          ψDot h = (WithLp.equiv 2 _).symm
            ((ψDotMat g_P IF_eff).mulVec ((WithLp.equiv 2 _) h)) :=
  ⟨ψDot_clm g_P IF_eff,
    ψ_param_HasFDerivAt_of_residual T_set g_P hg h_orth
      h_basis_in_tspace _hψ _hEIF _hψ_Hadamard_remainder,
    fun h => ψDot_clm_apply g_P IF_eff h⟩

/-- Lift a scalar estimator `T_n : ∀ n, (Fin n → Ω)
→ ℝ` to its `EuclideanSpace ℝ (Fin 1)`-valued form, as required by
`LocalAsymptoticMinimax.localAsymptoticRisk`. -/
noncomputable def T_param_of
    (T_n : ∀ n, (Fin n → Ω) → ℝ) :
    ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin 1) :=
  fun n X => (WithLp.equiv 2 _).symm (fun _ : Fin 1 => T_n n X)

private lemma withLp_1d_smul_sub_apply (r : ℝ) (a b : ℝ) :
    (WithLp.equiv 2 (Fin 1 → ℝ))
        (r • ((WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => a)
            - (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => b))) 0
      = r * (a - b) := by
  change WithLp.ofLp (r • (WithLp.toLp 2 (fun _ : Fin 1 => a)
      - WithLp.toLp 2 (fun _ : Fin 1 => b))) 0 = r * (a - b)
  rw [WithLp.ofLp_smul, WithLp.ofLp_sub, WithLp.ofLp_toLp, WithLp.ofLp_toLp]
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- Lift a scalar loss `ℓ_M : ℝ → ℝ≥0∞` to its
`EuclideanSpace ℝ (Fin 1)`-valued form. -/
noncomputable def L_param_of (ℓ_M : ℝ → ℝ≥0∞) :
    EuclideanSpace ℝ (Fin 1) → ℝ≥0∞ :=
  fun y => ℓ_M ((WithLp.equiv 2 _ y) 0)

/-- **LHS inclusion.** The parametric-LAM-LHS over the parametric
submodel `paramSubmodel g_P hg h_orth` (lifted via `T_param_of`,
`ψ_param`, `L_param_of`) is bounded above by the semiparametric-LAM-LHS
over the user's tangent set `T_set`, provided each basis element
`g_P j ∈ T_set.carrier` and `T_set` is closed under linear combinations
(linear-space case), and γ aligns with `paramSubmodel`-derived measures
on basis-spanned directions.

This is the key "reduction" step in vdV Theorem 25.21 (§25.3)'s proof: every `h ∈ ℝ^m`
corresponds to `h^T g_P ∈ T_set.carrier`, so the parametric supremum
over finite `I ⊂ ℝ^m` is a sub-supremum of the semiparametric supremum
over `I ⊂ T_set.carrier`.

Chaining with `LocalAsymptoticMinimax.local_asymptotic_minimax_bound`:
```
∫⁻ L dN(0, AAᵀ) ≤ localAsymptoticRisk paramSubmodel … ≤ semiparametric-LHS
```
delivers the per-(M, m) inner bound `hBdd_inner` that
`lam_semiparametric` needs. -/
theorem paramLam_LHS_le_semiparametric_LHS
    (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (_h_basis_in_tset : ∀ j, (g_P j : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    -- stays in `T_set.carrier`. vdV Theorem 25.21 (§25.3)'s "first" assumption (tangent
    -- set is a linear space, not just a cone).
    (_h_linspan_in_tset : ∀ (θ : Θ m),
      (∑ j : Fin m, ((WithLp.equiv 2 _ θ) j) • (g_P j) :
        ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (γ : ↥(L2ZeroMean P) → QMDPath P)
    -- basis-spanned directions. Formally: for each h ∈ ℝ^m and t ∈ ℝ,
    -- (γ (h^T g_P)).curve t = P.withDensity (paramSubmodel.density (t • h)).
    -- In concrete models this holds by construction; in abstract settings
    -- this is an explicit caller obligation. vdV's proof of Theorem 25.21 (§25.3)
    -- silently assumes equivalent submodels for the reduction.
    (_h_γ_aligns :
      ∀ (h : Θ m) (t : ℝ),
        (γ (∑ j : Fin m,
            ((WithLp.equiv 2 _ h) j) • (g_P j))).curve t
          = P.withDensity (fun x => ENNReal.ofReal
              ((paramSubmodel g_P hg h_orth).density (t • h) x)))
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_hT_n : ∀ n, Measurable (T_n n))
    (ψ : Measure Ω → ℝ)
    (ℓ_M : ℝ → ℝ≥0∞) :
    LocalAsymptoticMinimax.localAsymptoticRisk
        (paramSubmodel g_P hg h_orth) P (0 : Θ m)
        (T_param_of T_n)
        (ψ_param g_P hg h_orth ψ)
        (L_param_of ℓ_M)
      ≤
    ⨆ I : { S : Finset ↥(L2ZeroMean P) //
            (S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier },
      Filter.liminf
        (fun n : ℕ =>
          (I.val : Finset ↥(L2ZeroMean P)).sup
            (fun g =>
              ∫⁻ X : Fin n → Ω,
                ℓ_M (Real.sqrt n *
                  (T_n n X - ψ ((γ g).curve ((Real.sqrt n)⁻¹))))
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin n => (γ g).curve ((Real.sqrt n)⁻¹)))))
        atTop := by
  -- The linear-combination map θ ↦ ∑ j, θ_j • g_P j sends Θ m into T_set.carrier
  -- (via `_h_linspan_in_tset`); the image of any finite I_param ⊂ Θ m is a finite
  -- I_semip ⊂ T_set.carrier. We use this image to instantiate the semiparametric
  -- supremum, then match the parametric integrand against the semip one via the
  -- alignment hypothesis `_h_γ_aligns`.
  classical
  unfold LocalAsymptoticMinimax.localAsymptoticRisk
  refine iSup_le ?_
  intro I_param
  -- The semip image of I_param under h ↦ ∑ j, h_j • g_P j.
  -- Inline the expression (no `let`) to keep simp/elaboration unconfused.
  let I_semip_set : Finset ↥(L2ZeroMean P) :=
    I_param.image (fun h : Θ m => ∑ j : Fin m, ((WithLp.equiv 2 _) h) j • g_P j)
  have hI_semip_subset : (↑I_semip_set : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier := by
    intro g hg_mem
    rcases Finset.mem_image.mp hg_mem with ⟨h_param, _, rfl⟩
    exact _h_linspan_in_tset h_param
  refine le_iSup_of_le ⟨I_semip_set, hI_semip_subset⟩ ?_
  -- liminf-mono: per-n bound suffices.
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall ?_)
  intro n
  -- Per-n: parametric ⨆ h ∈ I_param ≤ Finset.sup I_semip ...
  refine iSup_le ?_
  intro h_param
  refine iSup_le ?_
  intro h_in_I_param
  -- The corresponding semip direction `g := h_param^T g_P`.
  set g : ↥(L2ZeroMean P) :=
    ∑ j : Fin m, ((WithLp.equiv 2 _) h_param) j • g_P j with hg_def
  have hg_in_I_semip : g ∈ I_semip_set :=
    Finset.mem_image.mpr ⟨h_param, h_in_I_param, hg_def.symm⟩
  -- The semip Finset.sup target function.
  let f_semip : ↥(L2ZeroMean P) → ℝ≥0∞ := fun g' =>
    ∫⁻ X : Fin n → Ω,
      ℓ_M (Real.sqrt n *
        (T_n n X - ψ ((γ g').curve ((Real.sqrt n)⁻¹))))
      ∂(MeasureTheory.Measure.pi
          (fun _ : Fin n => (γ g').curve ((Real.sqrt n)⁻¹)))
  -- Measure equality: productMeasure unfolds to Measure.pi of `(γ g).curve _`.
  have h_measure_eq :
      AsymptoticRepresentation.productMeasure (paramSubmodel g_P hg h_orth) P
          ((0 : Θ m) + (Real.sqrt n)⁻¹ • h_param) n
        = MeasureTheory.Measure.pi
            (fun _ : Fin n => (γ g).curve (Real.sqrt n)⁻¹) := by
    unfold AsymptoticRepresentation.productMeasure
    congr 1
    funext _
    rw [zero_add, hg_def]
    exact (_h_γ_aligns h_param (Real.sqrt n)⁻¹).symm
  -- Pointwise integrand equality after the measure substitution.
  have h_integrand_eq : ∀ ω : Fin n → Ω,
      L_param_of ℓ_M
          ((Real.sqrt n) • (T_param_of T_n n ω
            - ψ_param g_P hg h_orth ψ ((0 : Θ m) + (Real.sqrt n)⁻¹ • h_param)))
        = ℓ_M (Real.sqrt n
            * (T_n n ω - ψ ((γ g).curve (Real.sqrt n)⁻¹))) := by
    intro ω
    -- Replace `(γ g).curve _` with the paramSubmodel-density measure via alignment.
    have h_curve : (γ g).curve (Real.sqrt n)⁻¹
        = P.withDensity (fun x => ENNReal.ofReal
            ((paramSubmodel g_P hg h_orth).density ((Real.sqrt n)⁻¹ • h_param) x)) := by
      rw [hg_def]; exact _h_γ_aligns h_param (Real.sqrt n)⁻¹
    rw [h_curve, zero_add]
    -- Unfold L_param_of/T_param_of/ψ_param and use the 1-D WithLp helper.
    change ℓ_M ((WithLp.equiv 2 (Fin 1 → ℝ))
                ((Real.sqrt n) • (
                  (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => T_n n ω)
                  - (WithLp.equiv 2 (Fin 1 → ℝ)).symm
                      (fun _ : Fin 1 => ψ (P.withDensity fun x =>
                        ENNReal.ofReal ((paramSubmodel g_P hg h_orth).density
                          ((Real.sqrt n)⁻¹ • h_param) x))))) 0)
          = ℓ_M (Real.sqrt n * (T_n n ω - ψ (P.withDensity fun x =>
              ENNReal.ofReal ((paramSubmodel g_P hg h_orth).density
                ((Real.sqrt n)⁻¹ • h_param) x))))
    rw [withLp_1d_smul_sub_apply]
  -- Combine: rewrite measure + integrand, then bound by Finset.sup of f_semip.
  have h_step1 : ∫⁻ ω, L_param_of ℓ_M
              ((Real.sqrt n) • (T_param_of T_n n ω
                - ψ_param g_P hg h_orth ψ ((0 : Θ m) + (Real.sqrt n)⁻¹ • h_param)))
              ∂(AsymptoticRepresentation.productMeasure (paramSubmodel g_P hg h_orth) P
                  ((0 : Θ m) + (Real.sqrt n)⁻¹ • h_param) n)
      = f_semip g := by
    rw [h_measure_eq]
    exact lintegral_congr h_integrand_eq
  rw [h_step1]
  exact Finset.le_sup (f := f_semip) hg_in_I_semip

end AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge
