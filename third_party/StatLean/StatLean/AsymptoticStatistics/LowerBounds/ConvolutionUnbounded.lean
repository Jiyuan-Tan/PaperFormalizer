module
public import StatLean.AsymptoticStatistics.LowerBounds.UnboundedSubmodelQMDPath
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimator
public import StatLean.AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge
public import StatLean.AsymptoticStatistics.Efficiency.HajekLeCamConvolution
public import StatLean.AsymptoticStatistics.ParametricFamily.RegularEstimator
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.Dirac

@[expose] public section

/-!
# Semiparametric Convolution Theorem (unbounded densities, scalar form)

This file delivers `derived_convolution_decomp_unbounded`, the scalar
($k = 1$) form of the semiparametric **convolution theorem**. Let $\psi$ be a
real-valued functional, differentiable at $P$ relative to a tangent set, with
efficient influence function $\tilde\psi_P$, and let $T_n$ be a *regular*
estimator sequence with limit law $L$. Then, for every finite orthonormal
family $g_1,\dots,g_m$ in the tangent space, the limit law decomposes as a
Gaussian convolution
$$ L \;=\; N\!\bigl(0,\ \sigma^2\bigr) * M, \qquad
   \sigma^2 \;=\; \sum_{i=1}^m \langle \tilde\psi_P,\, g_i\rangle^2, $$
for some probability distribution $M$ (the "noise" factor). In particular the
asymptotic variance of any regular estimator is bounded below by $\sigma^2$.

This is the convolution half of van der Vaart's Theorem 25.20, specialized to
$k = 1$ and to a **fixed** finite orthonormal subset of the tangent space.
The book's full statement uses $\sigma^2 = P\tilde\psi_P\tilde\psi_P^\top$,
the variance of the efficient influence function; that value is the supremum
of the displayed finite-basis quantity $\sum_i\langle\tilde\psi_P,g_i\rangle^2$
over all orthonormal subsets, attained in the Loewner-order limit. The Lean
result establishes the decomposition for each such finite basis (the inner
content of the book's proof, before the limiting step). Because the densities
along the constructed submodel are everywhere strictly positive, this route
avoids the bounded-density route's uniform-Hadamard and bounded-mixture
hypotheses, using instead an affine functional `ψ_proj` (whose Fréchet
derivative is automatic) and the sigmoid `unboundedParamSubmodel`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series
in Statistical and Probabilistic Mathematics, Cambridge University Press, 1998.
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information),
Theorem 25.20 (Convolution). Auxiliary inputs: the parametric convolution
theorem (Chapter 8, §8.5, Theorem 8.8 / Proposition 8.4) and the sigmoid
submodel construction `k(x) = 2/(1+e^{-2x})` (§25.16).

**Proof formalization notes.**

1. **Affine `ψ_proj`**: define `ψ_proj θ := EuclideanSpace.single 0 (ψ P + ⟪IF_eff, ∑i θi g_P i⟫)`.
   Because `ψ_proj` is affine in `θ`, its Fréchet derivative `ψDot_proj` is just its
   linear part, so `HasFDerivAt ψ_proj ψDot_proj 0` is trivial via
   `ContinuousLinearMap.hasFDerivAt` plus a constant offset. No Hadamard regularity needed.

2. **Per-`h` Hájek shift form**: invoke `IsRegularEstimator.hajek_shift_form` on the
   QMDPath `unboundedParamSubmodel_oneDimPath g_P h_orth h`. The shift form recenters
   at the unperturbed truth `ψ P` and yields
   `(P^n_{(√n)⁻¹·h}).map (√n · (T_n - ψ P)) ⇝ (dirac c_h) ∗ L` where
   `c_h := ⟪IF_eff, linPerturbScore g_P h⟫`. Since
   `ψ_proj ((√n)⁻¹ • h) = ψ P + (√n)⁻¹ c_h`, after rescaling by `√n`,
   `√n · (T_n - ψ_proj ((√n)⁻¹ • h)) = √n · (T_n - ψ P) - c_h`,
   so the same sequence weakly converges to `((dirac c_h) ∗ L).map (· - c_h) = L`
   (translation invariance).

3. **Apply `hajek_le_cam_convolution_theorem`** with `M := unboundedParamSubmodel g_P h_orth`,
   DQM `unboundedParamSubmodel_DQM`, identity Fisher `unboundedParamSubmodel_fisher_info`,
   `ψ = ψ_proj`, `ψDot = ψDot_proj_clm`, `T = T_param_of T_n`.
   Output: `L_vec = N(0, ψDotMat · I · ψDotMatᵀ) ∗ M_θ` where
   `L_vec := L.map (EuclideanSpace.single 0)` and `ψDotMat` has entries
   `⟪IF_eff, g_P j⟫` (single row).

4. **Scalar collapse**: push both sides through the projection
   `pr0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ`, `pr0 y := y 0`.
   `pr0 ∘ EuclideanSpace.single 0 = id` on ℝ, and the
   multivariate Gaussian on `Fin 1` projects to `gaussianReal 0 σ²` with
   `σ² = ∑ i ⟪IF_eff, g_P i⟫²` via `multivariateGaussian_map_inner_eq_gaussianReal`.

**Bibliographic comments.** The convolution theorem originates with J. Hájek,
*A characterization of limiting distributions of regular estimates*, Zeitschrift
für Wahrscheinlichkeitstheorie und Verwandte Gebiete **14** (1970), 323–330; an
equivalent characterization was obtained independently by N. Inagaki,
*On the limiting distribution of a sequence of estimators with uniformity
property*, Annals of the Institute of Statistical Mathematics **22** (1970),
1–13, and the general (local asymptotic minimax / convolution) framework is due
to L. Le Cam. The semiparametric extension formalized here — projecting the
efficient influence function onto a tangent space and applying the parametric
theorem to finite-dimensional submodels — was developed by J. M. Begun, W. J.
Hall, W.-M. Huang, and J. A. Wellner, *Information and asymptotic efficiency in
parametric–nonparametric models*, Annals of Statistics **11** (1983), 432–452;
van der Vaart's Theorem 25.20 is the textbook synthesis of that line of work.
-/

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped InnerProductSpace ENNReal NNReal BigOperators MeasureTheory

namespace AsymptoticStatistics.LowerBounds.ConvolutionUnbounded

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics.LowerBounds.RegularEstimator
open AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge
  (ψDotMat T_param_of)
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## §1 — The affine functional `ψ_proj`

For an orthonormal basis `g_P : Fin m → L²₀(P)` and an efficient influence
function `IF_eff`, define `ψ_proj θ` as the constant `ψ P` plus the inner
product `⟪IF_eff, ∑i θi g_P i⟫`, packaged into `EuclideanSpace ℝ (Fin 1)`.

Because `ψ_proj` is **affine** in `θ`, its Fréchet derivative `ψDot_proj_clm`
is its linear part `θ ↦ EuclideanSpace.single 0 (⟪IF_eff, linPerturbScore g_P θ⟫)`
— a continuous linear map — and `HasFDerivAt ψ_proj ψDot_proj_clm 0` reduces
to `HasFDerivAt.const_add`. No Hadamard regularity required.
-/

/-- The affine functional `ψ_proj : Θ m → 𝓨 1`:
`ψ_proj θ := ψ P + ⟪IF_eff, ∑i θi g_P i⟫` (packed into Fin-1 form). -/
noncomputable def ψ_proj
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) (ψ_P : ℝ) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 1) :=
  fun θ => EuclideanSpace.single (0 : Fin 1)
    (ψ_P + ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P θ⟫_ℝ)

/-- Continuous linear part of `ψ_proj`: `θ ↦ ⟪IF_eff, ∑i θi g_P i⟫` packaged
into Fin-1 form, as a continuous linear map. This is the Fréchet derivative
of `ψ_proj` at every point (since `ψ_proj` is affine). -/
noncomputable def ψDot_proj_clm
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm.toLinearMap.comp
      ((ψDotMat g_P IF_eff).mulVecLin.comp
        (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap))

/-- `ψDot_proj_clm` agrees with the matrix form `ψDotMat`. -/
lemma ψDot_proj_clm_apply
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) (h : EuclideanSpace ℝ (Fin m)) :
    ψDot_proj_clm g_P IF_eff h
      = (WithLp.equiv 2 _).symm
        ((ψDotMat g_P IF_eff).mulVec ((WithLp.equiv 2 _) h)) := rfl

/-- Coord-0 of `ψDot_proj_clm h` equals `⟪IF_eff, linPerturbScore g_P h⟫`.
Mirrors `LAMSemiparametricBridge.ψDot_clm_coord_zero_eq_inner`. -/
lemma ψDot_proj_clm_coord_zero_eq_inner
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) (h : EuclideanSpace ℝ (Fin m)) :
    (ψDot_proj_clm g_P IF_eff h).ofLp 0
      = ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫_ℝ := by
  have h_lhs : (ψDot_proj_clm g_P IF_eff h).ofLp 0
      = ∑ j : Fin m,
          (@inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (g_P j))
            * h.ofLp j := by
    rw [ψDot_proj_clm_apply]
    rfl
  rw [h_lhs, linPerturbScore, inner_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [inner_smul_right]
  change ⟪(IF_eff : ↥(L2ZeroMean P)), g_P j⟫_ℝ * h.ofLp j
    = h.ofLp j * ⟪(IF_eff : ↥(L2ZeroMean P)), g_P j⟫_ℝ
  ring

/-- `ψ_proj θ = (single 0 ψ_P) + ψDot_proj_clm θ` (algebraic affine decomp).
The shape `const + linear` is what `HasFDerivAt.const_add` needs. -/
lemma ψ_proj_eq_const_add
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) (ψ_P : ℝ) :
    ψ_proj g_P IF_eff ψ_P
      = fun θ => EuclideanSpace.single (0 : Fin 1) ψ_P
                  + ψDot_proj_clm g_P IF_eff θ := by
  funext θ
  -- Both sides are vectors in EuclideanSpace ℝ (Fin 1); compare at every coord.
  ext i
  -- Only one coord (i = 0).
  have h0 : i = (0 : Fin 1) := Fin.eq_zero i
  subst h0
  -- LHS coord 0: ψ_P + ⟪IF_eff, lin θ⟫
  have hCoord :
      (ψDot_proj_clm g_P IF_eff θ).ofLp 0
        = ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P θ⟫_ℝ :=
    ψDot_proj_clm_coord_zero_eq_inner g_P IF_eff θ
  -- LHS unfolded:
  have h_lhs :
      (ψ_proj g_P IF_eff ψ_P θ).ofLp 0
        = ψ_P + ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P θ⟫_ℝ := by
    unfold ψ_proj
    rw [PiLp.single_apply]
    simp
  -- RHS unfolded:
  have h_rhs :
      (EuclideanSpace.single (0 : Fin 1) ψ_P + ψDot_proj_clm g_P IF_eff θ).ofLp 0
        = ψ_P + ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P θ⟫_ℝ := by
    have h_add : ((EuclideanSpace.single (0 : Fin 1) ψ_P
          + ψDot_proj_clm g_P IF_eff θ).ofLp 0 : ℝ)
        = (EuclideanSpace.single (0 : Fin 1) ψ_P).ofLp 0
            + (ψDot_proj_clm g_P IF_eff θ).ofLp 0 := rfl
    rw [h_add, hCoord, PiLp.single_apply]
    simp
  -- Both sides equal at coord 0; this is what the goal needs.
  change (ψ_proj g_P IF_eff ψ_P θ).ofLp 0
    = (EuclideanSpace.single (0 : Fin 1) ψ_P + ψDot_proj_clm g_P IF_eff θ).ofLp 0
  rw [h_lhs, h_rhs]

/-- `ψ_proj` has Fréchet derivative `ψDot_proj_clm` at every point — in
particular at `0`, which is all `hajek_le_cam_convolution_theorem` requires. -/
theorem ψ_proj_HasFDerivAt
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) (ψ_P : ℝ) :
    HasFDerivAt (ψ_proj g_P IF_eff ψ_P) (ψDot_proj_clm g_P IF_eff) 0 := by
  rw [ψ_proj_eq_const_add g_P IF_eff ψ_P]
  exact (ψDot_proj_clm g_P IF_eff).hasFDerivAt.const_add _

/-- `ψ_proj 0 = EuclideanSpace.single 0 ψ_P` (since `linPerturbScore g_P 0 = 0`). -/
@[simp] lemma ψ_proj_at_zero
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) (ψ_P : ℝ) :
    ψ_proj g_P IF_eff ψ_P 0 = EuclideanSpace.single (0 : Fin 1) ψ_P := by
  unfold ψ_proj
  have h_lin : linPerturbScore g_P (0 : EuclideanSpace ℝ (Fin m)) = 0 := by
    unfold linPerturbScore
    simp
  rw [h_lin]
  simp

/-- Scalar coord-0 form of `ψ_proj θ` at parameter `θ = t • h`:
`(ψ_proj (t • h)).0 = ψ_P + t · ⟪IF_eff, linPerturbScore g_P h⟫`. -/
lemma ψ_proj_coord_zero_smul
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (IF_eff : ↥(L2ZeroMean P)) (ψ_P : ℝ)
    (t : ℝ) (h : EuclideanSpace ℝ (Fin m)) :
    (ψ_proj g_P IF_eff ψ_P (t • h)).ofLp 0
      = ψ_P + t * ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫_ℝ := by
  unfold ψ_proj
  rw [PiLp.single_apply]
  simp only [if_true]
  congr 1
  -- ⟪IF_eff, linPerturbScore g_P (t • h)⟫ = t · ⟪IF_eff, linPerturbScore g_P h⟫
  -- Because linPerturbScore is linear in h.
  have h_lin : linPerturbScore g_P (t • h) = t • linPerturbScore g_P h := by
    unfold linPerturbScore
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- (t • h) i • g_P i = t • (h i • g_P i)  (by smul_assoc and (t•h) i = t * h i)
    change ((t • h) i) • g_P i = t • (h i • g_P i)
    rw [smul_smul]
    rfl
  rw [h_lin, inner_smul_right]

/-! ## §2 — Bridging the QMDPath curve to `productMeasure`

For our `unboundedParamSubmodel_oneDimPath g_P h_orth h`, the curve at `t`
is `P.withDensity (ofReal ∘ density (t • h))`, which is exactly
`(unboundedParamSubmodel g_P h_orth).density (t • h)`'s associated measure.
So `Measure.pi (fun _ => curve.curve t) = productMeasure unboundedParamSubmodel P (t • h) n`
by `rfl` modulo the definition.
-/

/-- The `Measure.pi` of the `unboundedParamSubmodel_oneDimPath`'s curve at `t`
equals the `productMeasure` of the m-dim `unboundedParamSubmodel` at `t • h`.
Definitional equality (modulo unfolding `productMeasure` and the curve). -/
lemma pi_oneDimCurve_eq_productMeasure
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m)) (t : ℝ) (n : ℕ) :
    MeasureTheory.Measure.pi
        (fun _ : Fin n =>
          (unboundedParamSubmodel_oneDimPath g_P h_orth h).curve t)
      = AsymptoticStatistics.AsymptoticRepresentation.productMeasure
          (unboundedParamSubmodel g_P h_orth) P (t • h) n := by
  rfl

/-! ## §3 — Same-support and lifting -/

/-- `EuclideanSpace.single 0 : ℝ → EuclideanSpace ℝ (Fin 1)` is continuous. -/
lemma continuous_single_zero :
    Continuous (EuclideanSpace.single (0 : Fin 1) : ℝ → EuclideanSpace ℝ (Fin 1)) := by
  have h_fun_eq :
      (EuclideanSpace.single (0 : Fin 1) : ℝ → EuclideanSpace ℝ (Fin 1))
        = fun r : ℝ => (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => r) := by
    funext r
    ext i
    fin_cases i
    change (EuclideanSpace.single (0 : Fin 1) r).ofLp 0
      = ((WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => r)).ofLp 0
    rw [PiLp.single_apply]
    simp
  rw [h_fun_eq]
  refine (PiLp.continuous_toLp 2 (β := fun _ : Fin 1 => ℝ)).comp ?_
  exact continuous_pi (fun _ => continuous_id)

lemma measurable_single_zero :
    Measurable (EuclideanSpace.single (0 : Fin 1) : ℝ → EuclideanSpace ℝ (Fin 1)) :=
  continuous_single_zero.measurable

/-- For the unbounded sigmoid submodel, the density is strictly positive at every
`θ` and every `ω`, so the same-support hypothesis of `hajek_le_cam_convolution_theorem` is
trivially satisfied: both `density 0 ω > 0` and `density (0 + t • u) ω > 0`. -/
lemma unboundedParamSubmodel_h_same_support
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) :
    ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin m), ∀ᵐ x ∂P,
      (0 < (unboundedParamSubmodel g_P h_orth).density 0 x ↔
       0 < (unboundedParamSubmodel g_P h_orth).density (0 + t • u) x) := by
  intro t u
  refine Filter.Eventually.of_forall (fun x => ?_)
  have h_pos_zero : 0 < (unboundedParamSubmodel g_P h_orth).density 0 x :=
    unboundedParamSubmodel_density_pos g_P h_orth 0 x
  have h_pos_pert : 0 < (unboundedParamSubmodel g_P h_orth).density (0 + t • u) x :=
    unboundedParamSubmodel_density_pos g_P h_orth (0 + t • u) x
  exact ⟨fun _ => h_pos_pert, fun _ => h_pos_zero⟩

/-! ## §4 — Per-`h` scalar weak convergence (via Hájek shift form on `oneDimPath`)

For each `h : Θ m`, the Hájek shift form on `unboundedParamSubmodel_oneDimPath g_P h_orth h`
yields, under `(P^n_{(√n)⁻¹·h})` = `Measure.pi (fun _ => curve.curve ((√n)⁻¹))`:

  `√n · (T_n - ψ P)  ⇝  (dirac c_h) ∗ L`

where `c_h := ⟪IF_eff, linPerturbScore g_P h⟫`. Since
`ψ_proj (0 + (√n)⁻¹ • h) = ψ P + (√n)⁻¹ · c_h` (coord-0), after applying
`√n` to the difference `T_n - ψ_proj((√n)⁻¹ • h)`:

  `√n · (T_n - ψ_proj((√n)⁻¹ • h)) = √n · (T_n - ψ P) - c_h`

By Slutsky (continuous deterministic shift), if `√n · (T_n - ψ P) ⇝ (dirac c_h) ∗ L`,
then `√n · (T_n - ψ P) - c_h ⇝ ((dirac c_h) ∗ L).map (· - c_h) = L`.
-/

/-- The "fixed-shift" map `((dirac c) ∗ L).map (· - c) = L`. -/
private lemma map_sub_const_dirac_conv (c : ℝ) (L : Measure ℝ) [SFinite L] :
    ((MeasureTheory.Measure.dirac c) ∗ L).map (fun y : ℝ => y - c) = L := by
  -- (dirac c) ∗ L = L.map (· + c); composing with (· - c) gives id.
  rw [MeasureTheory.Measure.dirac_conv]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h_id : ((fun y : ℝ => y - c) ∘ (fun y : ℝ => c + y)) = id := by
    funext y; simp
  rw [h_id, Measure.map_id]

/-- Eventually-equal substitution for weak convergence (local copy of
`ParametricBridge.weakConverges_congr_eventually` which is `private`). -/
private theorem weakConverges_congr_eventually
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    {μ ν : ℕ → Measure E} {ρ : Measure E}
    (h_eq : ∀ᶠ n : ℕ in Filter.atTop, μ n = ν n)
    (hμ : WeakConverges μ ρ) :
    WeakConverges ν ρ := by
  intro f
  refine (hμ f).congr' ?_
  filter_upwards [h_eq] with n hn
  exact congrArg (fun μ : Measure E => ∫ x, f x ∂μ) hn

/-- Per-`h` SCALAR weak convergence under the `unboundedParamSubmodel`-derived
product measure, recentered at the **perturbed parametric truth**
`(ψ_proj ((√n)⁻¹ • h)).0` (coord-0), with vector limit `L`. -/
theorem productMeasure_unbounded_pushforward_scalar_at_perturbed_truth
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    ∀ h : EuclideanSpace ℝ (Fin m),
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X
                  - (ψ_proj g_P IF_eff (ψ P)
                      ((Real.sqrt n)⁻¹ • h)).ofLp 0)))
        L := by
  classical
  intro h
  -- The score for our oneDimPath is `linPerturbScore g_P h`, in tangentSpace.
  set c : ℝ := ⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫_ℝ with hc_def
  have hLin_in_T :
      (linPerturbScore g_P h : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier :=
    linPerturbScore_mem_span T_set g_P h_in_T h
  have hScore_eq :
      (unboundedParamSubmodel_oneDimPath g_P h_orth h).score
        = linPerturbScore g_P h := rfl
  -- Step 1: invoke Hájek shift form on the oneDimPath QMDPath.
  have h_hajek :
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n =>
                (unboundedParamSubmodel_oneDimPath g_P h_orth h).curve
                  ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
        ((MeasureTheory.Measure.dirac c) ∗ L) := by
    have := IsRegularEstimator.hajek_shift_form
      (hψ := hψ) (hEIF := hEIF) hReg hT_meas
      (linPerturbScore g_P h) hLin_in_T
      (unboundedParamSubmodel_oneDimPath g_P h_orth h) hScore_eq
    simpa [hc_def] using this
  -- Step 2: substitute Measure.pi (curve.curve _) = productMeasure ... by `rfl`.
  -- Since `unboundedParamSubmodel_oneDimPath.curve t = withDensity (...density (t • h)...)`,
  -- `Measure.pi (...curve.curve ((√n)⁻¹)) = productMeasure unboundedParamSubmodel P ((√n)⁻¹ • h) n`
  -- by `rfl`.
  have h_pi_eq : ∀ n : ℕ,
      MeasureTheory.Measure.pi
          (fun _ : Fin n =>
            (unboundedParamSubmodel_oneDimPath g_P h_orth h).curve
              ((Real.sqrt n)⁻¹))
        = AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (unboundedParamSubmodel g_P h_orth) P
            ((Real.sqrt n)⁻¹ • h) n :=
    fun n => pi_oneDimCurve_eq_productMeasure g_P h_orth h (Real.sqrt n)⁻¹ n
  -- Rewrite h_hajek using h_pi_eq.
  have h_hajek_pm :
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P
              ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
        ((MeasureTheory.Measure.dirac c) ∗ L) := by
    -- The two product-measure sequences are equal pointwise (in n) by `h_pi_eq`,
    -- so the two weak-convergence statements are equivalent.
    have h_seq_eq : (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n =>
              (unboundedParamSubmodel_oneDimPath g_P h_orth h).curve
                ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
        = (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P
              ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P))) := by
      funext n; rw [h_pi_eq n]
    rw [← h_seq_eq]
    exact h_hajek
  -- Step 3: Slutsky shift by `-c`. The map `(· - c)` applied to both sides:
  --   LHS: ((productMeasure).map (√n·(T_n - ψ P))).map (· - c)
  --        = (productMeasure).map (√n·(T_n - ψ P) - c)
  --        = (productMeasure).map (√n·(T_n - ψ P - c/√n))
  -- We need to identify  c/√n = ψ_proj((√n)⁻¹·h).0 - ψ P  (so √n*(T_n - ψ_proj.0) = √n*(T_n - ψ P)
  -- - c).
  -- By `ψ_proj_coord_zero_smul`: (ψ_proj (t • h)).0 = ψ P + t·c, so at t = (√n)⁻¹,
  --   ψ_proj((√n)⁻¹·h).0 = ψ P + (√n)⁻¹·c.
  -- Hence √n·(T_n - ψ_proj((√n)⁻¹·h).0) = √n·T_n - √n·ψ P - c = √n·(T_n - ψ P) - c.
  have h_psi_proj_coord : ∀ n : ℕ,
      (ψ_proj g_P IF_eff (ψ P)
          ((Real.sqrt n)⁻¹ • h)).ofLp 0
        = ψ P + (Real.sqrt n)⁻¹ * c := by
    intro n
    rw [ψ_proj_coord_zero_smul]
  -- The pointwise equality `√n · (T_n - ψ_proj.0) = √n · (T_n - ψ P) - c` only
  -- holds for `√n ≠ 0` (i.e., `n ≥ 1`); at `n = 0`, LHS = 0 but RHS = -c.
  -- We use congr_eventually to ignore the n = 0 case.
  have h_inv_ne_zero : ∀ᶠ n : ℕ in Filter.atTop, Real.sqrt n ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < Real.sqrt n :=
      Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hn1)
    exact hpos.ne'
  -- Restate h_diff_eq under the eventually condition: for n ≥ 1, the function equality
  -- holds pointwise.
  have h_diff_eq_ev : ∀ᶠ n : ℕ in Filter.atTop,
      (fun X : Fin n → Ω =>
        Real.sqrt n *
          (T_n n X
            - (ψ_proj g_P IF_eff (ψ P)
                ((Real.sqrt n)⁻¹ • h)).ofLp 0))
      = (fun X : Fin n → Ω =>
        Real.sqrt n * (T_n n X - ψ P) - c) := by
    filter_upwards [h_inv_ne_zero] with n hn
    funext X
    rw [h_psi_proj_coord n]
    field_simp
    ring
  -- Now apply the shift: ((dirac c) ∗ L).map (· - c) = L.
  have h_target_eq := map_sub_const_dirac_conv c L
  -- Continuous mapping theorem: weak convergence preserved under (· - c).
  have h_shifted :
      WeakConverges
        (fun n : ℕ =>
          ((AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P
              ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P))).map
              (fun y : ℝ => y - c))
        L := by
    have h_map :=
      h_hajek_pm.map (f := fun y : ℝ => y - c)
        (continuous_id.sub continuous_const) (measurable_id.sub_const c)
    intro f
    have := h_map f
    rw [show (((MeasureTheory.Measure.dirac c) ∗ L).map (fun y : ℝ => y - c) : Measure ℝ)
        = L from h_target_eq] at this
    exact this
  -- Identify ((pm.map (√n·(T_n - ψ P))).map (· - c)) with the goal's measure shape.
  have h_compose : ∀ n : ℕ,
      ((AsymptoticStatistics.AsymptoticRepresentation.productMeasure
          (unboundedParamSubmodel g_P h_orth) P
          ((Real.sqrt n)⁻¹ • h) n).map
        (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P))).map
          (fun y : ℝ => y - c)
        = (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (unboundedParamSubmodel g_P h_orth) P
            ((Real.sqrt n)⁻¹ • h) n).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P) - c) := by
    intro n
    rw [Measure.map_map (by fun_prop)]
    · rfl
    · exact ((hT_meas n).sub_const _).const_mul (Real.sqrt n)
  -- Combine: the eventually-form replaces √n·(T_n - ψ P) - c with √n·(T_n - ψ_proj.0).
  have h_compose_ev : ∀ᶠ n : ℕ in Filter.atTop,
      ((AsymptoticStatistics.AsymptoticRepresentation.productMeasure
          (unboundedParamSubmodel g_P h_orth) P
          ((Real.sqrt n)⁻¹ • h) n).map
        (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P))).map
          (fun y : ℝ => y - c)
        = (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (unboundedParamSubmodel g_P h_orth) P
            ((Real.sqrt n)⁻¹ • h) n).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n n X
                - (ψ_proj g_P IF_eff (ψ P)
                    ((Real.sqrt n)⁻¹ • h)).ofLp 0)) := by
    filter_upwards [h_diff_eq_ev] with n h_funeq
    rw [h_compose n]
    congr 1
    exact h_funeq.symm
  exact weakConverges_congr_eventually h_compose_ev h_shifted

/-! ## §5 — Vector lift of the per-`h` convergence

To feed `hajek_le_cam_convolution_theorem` (which expects `RegularEstimatorSequence`
data with `EuclideanSpace ℝ (Fin d)` target), we lift the per-`h` scalar
weak convergence above to the `EuclideanSpace ℝ (Fin 1)` target via
`WeakConverges.map` through `EuclideanSpace.single 0`.
-/

/-- Vector form of the per-`h` weak convergence (target `EuclideanSpace ℝ (Fin 1)`),
recentered at `ψ_proj_lifted ((√n)⁻¹ • h)`. Limit: `L.map (single 0)`. -/
theorem productMeasure_unbounded_pushforward_vec
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    ∀ h : EuclideanSpace ℝ (Fin m),
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (unboundedParamSubmodel g_P h_orth) P
              ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_param_of T_n n X
                  - ψ_proj g_P IF_eff (ψ P)
                      ((0 : EuclideanSpace ℝ (Fin m))
                        + (Real.sqrt n)⁻¹ • h))))
        (L.map (EuclideanSpace.single (0 : Fin 1)
            : ℝ → EuclideanSpace ℝ (Fin 1))) := by
  intro h
  classical
  -- Step 1: scalar weak conv at h.
  have h_scalar := productMeasure_unbounded_pushforward_scalar_at_perturbed_truth
    T_set hψ hEIF T_n hT_meas hReg g_P h_orth h_in_T h
  -- Step 2: push through `EuclideanSpace.single 0`.
  have h_pushed :=
    h_scalar.map continuous_single_zero measurable_single_zero
  -- Step 3: identify the pushed sequence with the goal's measure.
  -- (productMeasure …).map f, then .map (single 0) = (productMeasure …).map (single 0 ∘ f),
  -- and we want to show single 0 ∘ (√n·(T_n - .ofLp 0)) =
  --   fun X => √n • (T_param_of T_n n X - ψ_proj …).
  have h_meas_inner : ∀ n : ℕ,
      Measurable (fun X : Fin n → Ω =>
        Real.sqrt n *
          (T_n n X
            - (ψ_proj g_P IF_eff (ψ P)
                ((Real.sqrt n)⁻¹ • h)).ofLp 0)) := by
    intro n
    refine Measurable.const_mul ?_ _
    exact (hT_meas n).sub_const _
  intro f
  have := h_pushed f
  -- Re-express the pushed integral: the map factors.
  -- We use `Measure.map_map` then identify the composed function.
  -- KEY observation: at coord 0, the two functions agree:
  -- LHS f X := √n · (T_n n X - (ψ_proj …).ofLp 0)
  --   then post-compose with `EuclideanSpace.single 0`.
  -- RHS X := √n • (T_param_of T_n n X - ψ_proj …)
  -- Both are EuclideanSpace ℝ (Fin 1) -valued and agree pointwise.
  have h_pi : ∀ n : ℕ,
      ((AsymptoticStatistics.AsymptoticRepresentation.productMeasure
          (unboundedParamSubmodel g_P h_orth) P ((Real.sqrt n)⁻¹ • h) n).map
        (fun X : Fin n → Ω =>
          Real.sqrt n *
            (T_n n X
              - (ψ_proj g_P IF_eff (ψ P)
                  ((Real.sqrt n)⁻¹ • h)).ofLp 0))).map
        (EuclideanSpace.single (0 : Fin 1))
      = (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
          (unboundedParamSubmodel g_P h_orth) P
          ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h) n).map
        (fun X : Fin n → Ω =>
          Real.sqrt n •
            (T_param_of T_n n X
              - ψ_proj g_P IF_eff (ψ P)
                  ((0 : EuclideanSpace ℝ (Fin m))
                    + (Real.sqrt n)⁻¹ • h))) := by
    intro n
    rw [Measure.map_map measurable_single_zero (h_meas_inner n)]
    rw [zero_add]
    congr 1
    funext X
    -- Show: EuclideanSpace.single 0 (√n · (T_n n X - ψ_proj.ofLp 0))
    --     = √n • (T_param_of T_n n X - ψ_proj ((√n)⁻¹ • h))
    ext i
    have h0 : i = (0 : Fin 1) := Fin.eq_zero i
    subst h0
    -- At coord 0:
    -- LHS.ofLp 0 = √n · (T_n n X - ψ_proj.ofLp 0)  (by PiLp.single_apply)
    -- RHS.ofLp 0 = √n · (T_param_of T_n n X).ofLp 0 - √n · (ψ_proj …).ofLp 0
    --            = √n · (T_n n X - ψ_proj.ofLp 0)  (since T_param_of unfolds to single)
    set v : ℝ := T_n n X with hv_def
    set w : ℝ := (ψ_proj g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h)).ofLp 0 with hw_def
    -- LHS: EuclideanSpace.single 0 (√n · (v - w)) at coord 0 = √n · (v - w).
    have h_lhs :
        ((EuclideanSpace.single (0 : Fin 1) (Real.sqrt n * (v - w)))).ofLp 0
          = Real.sqrt n * (v - w) := by
      rw [PiLp.single_apply]; simp
    -- T_param_of T_n n X at coord 0 = T_n n X.
    have h_T_param_coord : (T_param_of T_n n X).ofLp 0 = T_n n X := by
      unfold T_param_of; rfl
    -- (√n • (a - b)).ofLp 0 = √n · (a.ofLp 0 - b.ofLp 0).
    have h_rhs :
        (Real.sqrt n • (T_param_of T_n n X
            - ψ_proj g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h))).ofLp 0
          = Real.sqrt n * (v - w) := by
      rw [show (Real.sqrt n • (T_param_of T_n n X
              - ψ_proj g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h))).ofLp 0
            = Real.sqrt n * ((T_param_of T_n n X
              - ψ_proj g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h)).ofLp 0) from rfl]
      rw [show ((T_param_of T_n n X
              - ψ_proj g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h)).ofLp 0)
            = (T_param_of T_n n X).ofLp 0
              - (ψ_proj g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h)).ofLp 0 from rfl]
      rw [h_T_param_coord, ← hv_def, ← hw_def]
    change ((EuclideanSpace.single (0 : Fin 1) (Real.sqrt n * (v - w)))).ofLp 0
      = (Real.sqrt n • (T_param_of T_n n X
          - ψ_proj g_P IF_eff (ψ P) ((Real.sqrt n)⁻¹ • h))).ofLp 0
    rw [h_lhs, h_rhs]
  simpa [h_pi] using this

/-! ## §6 — `RegularEstimatorSequence` constructor for `unboundedParamSubmodel` -/

/-- Package the per-`h` vector weak convergence (output of
`productMeasure_unbounded_pushforward_vec`) into the
`RegularEstimatorSequence` structure consumed by `hajek_le_cam_convolution_theorem`. -/
noncomputable def unboundedParamSubmodel_RegularEstimatorSequence
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    AsymptoticStatistics.ParametricFamily.RegularEstimatorSequence
      (unboundedParamSubmodel g_P h_orth) P (0 : EuclideanSpace ℝ (Fin m))
      (ψ_proj g_P IF_eff (ψ P)) (T_param_of T_n) where
  limitDist := L.map (EuclideanSpace.single (0 : Fin 1)
    : ℝ → EuclideanSpace ℝ (Fin 1))
  isProb := MeasureTheory.Measure.isProbabilityMeasure_map
    measurable_single_zero.aemeasurable
  tendsto := productMeasure_unbounded_pushforward_vec
    T_set hψ hEIF T_n hT_meas hReg g_P h_orth h_in_T

/-! ## §7 — Main theorem: drift-free convolution decomposition -/

/-- **Drift-free convolution decomposition.**

For any orthonormal basis `g_P : Fin m → L²₀(P)` in the tangent space,
the limit law `L` of a regular estimator decomposes as a Gaussian convolution
with mixing measure `M_per`, where the Gaussian variance is
`σ² = ∑ i ⟪IF_eff, g_P i⟫²` (vdV §25.20 scalar form).

This is the counterpart of `regular_estimator_convolution` that drops both the
`IsTangentBoundedDense` hypothesis and the `hψ_Hadamard_remainder`
uniform-remainder hypothesis. They are replaced by:
* **`unboundedParamSubmodel`** (no bounded-density needed; sigmoid construction
  works for any L²-zero-mean basis);
* **Affine `ψ_proj`** (whose Fréchet derivative is automatic, no Hadamard
  regularity) — see §1 above.

References: vdV §25.20, §8.5 Theorem 8.8, §25.16. -/
theorem derived_convolution_decomp_unbounded
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L) :
    ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
      Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
      (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) →
      ∃ M_per : Measure ℝ, IsProbabilityMeasure M_per ∧
        L = MeasureTheory.Measure.conv
              (ProbabilityTheory.gaussianReal 0
                ⟨∑ i : Fin m,
                    (⟪(IF_eff : ↥(L2ZeroMean P)),
                      (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                  Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) M_per := by
  intro m g_P h_orth h_in_T
  classical
  -- Set notation.
  set σ_sq_real : ℝ := ∑ i : Fin m,
    (⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2
    with hσ_sq_real_def
  set σ_sq_NN : ℝ≥0 := ⟨σ_sq_real, Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩
    with hσ_sq_NN_def
  -- The matrix `ψDotMat g_P IF_eff` is the 1 × m matrix with single row
  -- (⟪IF_eff, g_P j⟫)_j. Then ψDotMat · I · ψDotMatᵀ = [[σ²]] as a 1×1 matrix.
  -- ===== Step 1: build the RegularEstimatorSequence. =====
  let hReg_param := unboundedParamSubmodel_RegularEstimatorSequence
    T_set hψ hEIF T_n hT_meas hReg g_P h_orth h_in_T
  -- ===== Step 2: build hajek_le_cam_convolution_theorem inputs. =====
  -- 2a: g_P_total measurability.
  have h_gP_total_meas : Measurable (g_P_total g_P) := by
    unfold g_P_total
    exact (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp
      (measurable_pi_iff.mpr (fun i => gMk_meas g_P i))
  -- 2b: Fisher info = I_m.
  have h_paramSub_hJ_fisher :
      ∀ u v : EuclideanSpace ℝ (Fin m),
        fisherInformation
            (unboundedParamSubmodel g_P h_orth) P 0
            (g_P_total g_P) u v
          = @inner ℝ _ _ u
              ((WithLp.equiv 2 _).symm
                ((1 : Matrix (Fin m) (Fin m) ℝ).mulVec
                  ((WithLp.equiv 2 _) v))) := by
    intro u v
    rw [unboundedParamSubmodel_fisher_info g_P h_orth u v,
      Matrix.one_mulVec, Equiv.symm_apply_apply]
  -- 2c: ψ_proj is Fréchet differentiable at 0 with derivative ψDot_proj_clm.
  have hψ_diff := ψ_proj_HasFDerivAt g_P IF_eff (ψ P)
  -- 2d: T_param_of T_n is measurable.
  have hT_param_meas : ∀ n, Measurable (T_param_of T_n n) := by
    intro n
    unfold T_param_of
    exact (WithLp.measurable_toLp 2 (Fin 1 → ℝ)).comp
      (measurable_pi_iff.mpr (fun _ => hT_meas n))
  -- ===== Step 3: invoke hajek_le_cam_convolution_theorem. =====
  obtain ⟨M_θ, hM_θ_prob, hConv⟩ :=
    AsymptoticStatistics.HajekLeCamConvolution.hajek_le_cam_convolution_theorem
      (unboundedParamSubmodel g_P h_orth)
      P 0 (g_P_total g_P)
      h_gP_total_meas
      (unboundedParamSubmodel_DQM g_P h_orth)
      (1 : Matrix (Fin m) (Fin m) ℝ) Matrix.PosDef.one
      h_paramSub_hJ_fisher
      (ψ_proj g_P IF_eff (ψ P)) (ψDot_proj_clm g_P IF_eff) hψ_diff
      (ψDotMat g_P IF_eff)
      (fun h => ψDot_proj_clm_apply g_P IF_eff h)
      (T_param_of T_n) hT_param_meas hReg_param
      (unboundedParamSubmodel_isPDFOf g_P h_orth)
  haveI := hM_θ_prob
  -- hConv : hReg_param.limitDist = N(0, ψDotMat * I⁻¹ * ψDotMatᵀ) ∗ M_θ
  -- where hReg_param.limitDist = L.map (single 0).
  -- ===== Step 4: scalar collapse via pr0. =====
  set pr0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) with hpr0_def
  have hpr0_apply : ∀ y : EuclideanSpace ℝ (Fin 1),
      pr0 y = (WithLp.equiv 2 (Fin 1 → ℝ)) y 0 := by
    intro y
    change (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) y : ℝ) = _
    rw [innerSL_apply_apply, PiLp.inner_apply]
    rw [Fin.sum_univ_one]
    simp [EuclideanSpace.single]
  have hpr0_single : ∀ r : ℝ, pr0 (EuclideanSpace.single (0 : Fin 1) r) = r := by
    intro r
    rw [hpr0_apply]
    show (WithLp.equiv 2 (Fin 1 → ℝ)) (EuclideanSpace.single (0 : Fin 1) r) 0 = r
    change WithLp.ofLp (EuclideanSpace.single (0 : Fin 1) r) 0 = r
    rw [PiLp.single_apply]
    simp
  have h_single_meas := measurable_single_zero
  have h_map_LHS_eq :
      (L.map (EuclideanSpace.single (0 : Fin 1)
            : ℝ → EuclideanSpace ℝ (Fin 1))).map (pr0 : _ → ℝ) = L := by
    rw [Measure.map_map (pr0.continuous.measurable) h_single_meas]
    have h_comp_id : (pr0 ∘ EuclideanSpace.single (0 : Fin 1)
            : ℝ → ℝ) = id := by
      funext r; exact hpr0_single r
    rw [h_comp_id]
    exact Measure.map_id
  have h_map_RHS_eq :
      (MeasureTheory.Measure.conv
        (ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin 1))
          ((ψDotMat g_P IF_eff) *
            (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
            (ψDotMat g_P IF_eff).transpose))
        M_θ).map (pr0 : _ → ℝ)
      = MeasureTheory.Measure.conv
          ((ProbabilityTheory.multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin 1))
            ((ψDotMat g_P IF_eff) *
              (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
              (ψDotMat g_P IF_eff).transpose)).map pr0)
          (M_θ.map pr0) :=
    MeasureTheory.Measure.map_conv_continuousLinearMap pr0
  -- AAᵀ at (0,0) = σ_sq_real.
  have h_AAT_zero_zero :
      ((ψDotMat g_P IF_eff) *
        (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
        (ψDotMat g_P IF_eff).transpose) 0 0
      = σ_sq_real := by
    simp only [inv_one, Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply,
      ψDotMat]
    simp_rw [← sq]
    rfl
  -- AAᵀ is PSD.
  have h_AAT_psd : ((ψDotMat g_P IF_eff) *
      (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
      (ψDotMat g_P IF_eff).transpose).PosSemidef := by
    have hone_psd : (Matrix.PosSemidef
        ((1 : Matrix (Fin m) (Fin m) ℝ)⁻¹)) :=
      ((Matrix.PosDef.one).inv).posSemidef
    have h := Matrix.PosSemidef.mul_mul_conjTranspose_same hone_psd
      (ψDotMat g_P IF_eff)
    have h_eq : ((ψDotMat g_P IF_eff).conjTranspose
            : Matrix (Fin m) (Fin 1) ℝ)
        = (ψDotMat g_P IF_eff).transpose := by
      ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    rw [h_eq] at h
    exact h
  -- Apply multivariateGaussian_map_inner_eq_gaussianReal.
  have h_gauss_collapse :
      (ProbabilityTheory.multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin 1))
        ((ψDotMat g_P IF_eff) *
          (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
          (ψDotMat g_P IF_eff).transpose)).map pr0
      = ProbabilityTheory.gaussianReal 0 σ_sq_NN := by
    have h_pr0_inner_form : (fun y : EuclideanSpace ℝ (Fin 1) => pr0 y)
          = (fun y : EuclideanSpace ℝ (Fin 1) =>
            ⟪(EuclideanSpace.single (0 : Fin 1) (1 : ℝ)), y⟫_ℝ) := by
      funext y; rfl
    rw [show (pr0 : _ → ℝ) = (fun y => pr0 y) from rfl, h_pr0_inner_form]
    rw [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal _ h_AAT_psd]
    congr 1
    apply Subtype.ext
    have h_single_eq :
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)).ofLp = fun _ => (1 : ℝ) := by
      funext i
      fin_cases i
      change WithLp.ofLp (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 = 1
      simp [EuclideanSpace.single]
    rw [h_single_eq]
    have h_dot_eq :
        ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((ψDotMat g_P IF_eff) *
            (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
            (ψDotMat g_P IF_eff).transpose).mulVec
              (fun _ : Fin 1 => (1 : ℝ)))
        = σ_sq_real := by
      simp only [dotProduct, Fin.sum_univ_one, one_mul, Matrix.mulVec, mul_one]
      exact h_AAT_zero_zero
    have h_dot_nn :
        0 ≤ ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
            ((ψDotMat g_P IF_eff) *
              (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ *
              (ψDotMat g_P IF_eff).transpose).mulVec
                (fun _ : Fin 1 => (1 : ℝ))) := by
      have := h_AAT_psd.re_dotProduct_nonneg (x := (fun _ : Fin 1 => (1 : ℝ)))
      simpa using this
    rw [h_dot_eq]
    exact Real.coe_toNNReal _ (by simpa [hσ_sq_real_def] using h_dot_nn.trans_eq h_dot_eq)
  -- ===== Step 5: assemble. =====
  refine ⟨M_θ.map pr0, Measure.isProbabilityMeasure_map pr0.continuous.measurable.aemeasurable, ?_⟩
  have h_limitDist :
      hReg_param.limitDist =
        L.map (EuclideanSpace.single (0 : Fin 1) : ℝ → EuclideanSpace ℝ (Fin 1)) := rfl
  rw [h_limitDist] at hConv
  have h_apply := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 1)) =>
    μ.map (pr0 : _ → ℝ)) hConv
  rw [h_map_LHS_eq] at h_apply
  rw [h_map_RHS_eq, h_gauss_collapse] at h_apply
  exact h_apply

end AsymptoticStatistics.LowerBounds.ConvolutionUnbounded
