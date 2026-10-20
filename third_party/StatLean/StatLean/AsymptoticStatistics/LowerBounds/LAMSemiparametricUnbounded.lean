module
public import StatLean.AsymptoticStatistics.LowerBounds.LAMUnboundedBridge
public import StatLean.AsymptoticStatistics.LowerBounds.LAMUnboundedRecenter
public import StatLean.AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge
public import StatLean.AsymptoticStatistics.LowerBounds.ConvolutionUnbounded
public import StatLean.AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec
public import StatLean.AsymptoticStatistics.LowerBounds.ProjSeqToEif
public import StatLean.AsymptoticStatistics.LowerBounds.BasisFromProjSeq
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import StatLean.AsymptoticStatistics.ParametricFamily.UnboundedSubmodel
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianRealTV
public import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped
public import StatLean.AsymptoticStatistics.Efficiency.LocalAsymptoticMinimax
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
public import StatLean.AsymptoticStatistics.Core.PathwiseVec
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# Theorem 25.21 — Semiparametric Local Asymptotic Minimax

Let $\psi:\mathcal P\to\mathbb R$ be a functional that is pathwise differentiable
at $P$ relative to a tangent set $\dot{\mathcal P}_P$, with efficient influence
function $\tilde\psi_P$. For every direction $g$ in the tangent set, write
$P_{t,g}$ for a one-dimensional submodel through $P$ with score $g$ along which
$\psi$ is differentiable. Then for any estimator sequence $\{T_n\}$ and any
subconvex loss $\ell:\mathbb R\to[0,\infty]$,
$$
\sup_{I}\ \liminf_{n\to\infty}\ \sup_{g\in I}\
  \mathbb E_{P_{1/\sqrt n,\,g}}\,
  \ell\!\bigl(\sqrt n\,(T_n-\psi(P_{1/\sqrt n,\,g}))\bigr)
  \ \ge\ \int \ell\, dN\!\bigl(0,\ \|\tilde\psi_P\|^2\bigr),
$$
where the outer supremum runs over all finite subsets $I$ of the tangent set.
No estimator sequence can do asymptotically better, in local-minimax risk, than
the centered Gaussian whose variance is the squared $L^2(P)$ norm of the
efficient influence function — this norm is the scalar specialization of the
book's optimal asymptotic covariance $P\tilde\psi_P\tilde\psi_P^{\mathsf T}$.

**Deviations from the book statement.** The Lean theorem
`lam_semiparametric_unbounded` is the **scalar** ($k=1$) case: $\psi$ is
real-valued, so the limiting covariance matrix collapses to the variance
$\|\tilde\psi_P\|^2$ and the Gaussian is the one-dimensional
$N(0,\|\tilde\psi_P\|^2)$. Compared with the book's hypotheses it (i) assumes the
tangent set is a **linear space** (the book's convex-cone generality is not
formalized), (ii) carries an explicit single tightness condition on the
recentered, $\sqrt n$-scaled statistic under $P^{\otimes n}$ (the book's
"sequence $\sqrt n(T_n-\psi(P))$ is tight" hypothesis, used so that the
compactification argument can be bypassed), and (iii) makes the "subconvex loss"
hypothesis precise as `BowlShaped ℓ` together with per-truncation lower
semicontinuity of $u\mapsto \ell(u)\wedge M$, matching the book's notion of a
subconvex function. The loss may take the value $+\infty$ (the `ℝ≥0∞` target).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information),
Theorem 25.21 (LAM). The optimal-asymptotic-covariance interpretation and the
efficient-influence-function representation appear in the same section, Eq.
(25.22).

**Proof formalization notes.** This file states and proves
`lam_semiparametric_unbounded`. The headline 25.21 lower bound is obtained by
feeding the **submodel functional** `ψ_param_unb` directly to the
per-direction-shift form of Theorem 8.11,
`local_asymptotic_minimax_bound_of_pointwise_shift`, with the per-direction
shift supplied by the pathwise Gateaux limit. The hypothesis set is a
**linear-space tangent set**, a pathwise-differentiable `ψ` with efficient
influence function, an estimator sequence, a subconvex loss, and a single
tightness condition.

*Reduction in three tiers.*

1. **Inner per-`(M, m)`** : `local_asymptotic_minimax_bound_of_pointwise_shift`
   invoked on `unboundedParamSubmodel g_P h_orth` with the submodel functional
   `ψ_param_unb` / `ψDot_proj_clm` / `T_param_of` / `L_param_of`. The
   per-direction shift `hψ_shift` is `ψ_param_unb_pointwise_shift`. The LHS
   inclusion `localAsymptoticRisk(unbounded) ≤ LHS_canonical(ℓ_M)` is
   `unboundedLam_le_LHS_canonical`, exact per `n`.

2. **Outer (Loewner, `m → ∞`)** : `proj_seq_to_eif` plus Bessel plus
   Gaussian-integral continuity
   (`gaussianReal_integral_continuous_of_var_tendsto`). This is the formalized
   counterpart of the book's "choose `g_P` so that `AAᵀ` is arbitrarily close to
   `P ψ̃_P ψ̃_Pᵀ` in Loewner order".

3. **Outer (monotone convergence, `ℓ_M ↑ ℓ`)** : lifts the truncated bound to
   the full bound via `LHS_canonical_mono`.

*Basis builder.* The in-file `basis_at_proj_m_pos_unbounded` builds the
1-element bases from the projection sequence, needing only orthonormality,
carrier-membership, linear-span membership, and the variance identity
`∑ⱼ ⟨IF, gⱼ⟩² = ‖p_m‖²`.

**Bibliographic comments.** The local asymptotic minimax theorem originates with
J. Hájek, "Local asymptotic minimax and admissibility in estimation,"
*Proceedings of the Sixth Berkeley Symposium on Mathematical Statistics and
Probability*, Vol. 1, University of California Press, 1972, pp. 175–194, where
the parametric LAM bound (the $k$-dimensional analogue of vdV Theorem 8.11) is
established; the companion convolution theorem is due to J. Hájek, "A
characterization of limiting distributions of regular estimates," *Z.
Wahrsch. Verw. Gebiete* 14 (1970), 323–330, and independently N. Inagaki (1970).
The **semiparametric** generalization formalized here — passing the parametric
bound to sufficiently rich finite-dimensional submodels and optimizing over the
tangent set — is developed by J. M. Begun, W. J. Hall, W.-M. Huang, and J. A.
Wellner, "Information and asymptotic efficiency in parametric–nonparametric
models," *Annals of Statistics* 11 (1983), 432–452, building on earlier
information-bound work of C. Stein, R. Beran, B. Ya. Levit, and others; van der
Vaart's §25.3 is a textbook synthesis of this line.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics
open scoped InnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics.LowerBounds.LAMSemiparametricUnbounded

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.LowerBounds
open AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge (T_param_of L_param_of ψDotMat)
open AsymptoticStatistics.LowerBounds.LAMUnboundedBridge
  (productMeasure_unbounded_at_zero unboundedLam_le_LHS_canonical
   ψ_param_unb ψ_param_unb_at_zero ψ_param_unb_pointwise_shift)
open AsymptoticStatistics.LowerBounds.ConvolutionUnbounded
  (ψDot_proj_clm ψDot_proj_clm_apply)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Basis builder. -/

/-- **Basis from projection sequence (positive-norm case).**

Builds the 1-element basis from the projection sequence, needing only
orthonormality, carrier-membership, linear-span membership, and the variance
identity `∑ⱼ ⟨IF, gⱼ⟩² = ‖p m‖²`. The basis is the unit vector
`g_P 0 := (1/‖p m‖) • p m`. -/
private theorem basis_at_proj_m_pos_unbounded
    (T_set : TangentSpec P)
    (h_lin_smul : ∀ x ∈ T_set.carrier, ∀ t : ℝ, t • x ∈ T_set.carrier)
    (h_lin_add : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      x + y ∈ T_set.carrier)
    (h_lin_zero : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (IF_eff : ↥(L2ZeroMean P))
    (V : ℕ → Submodule ℝ ↥(L2ZeroMean P))
    (p : ℕ → ↥(L2ZeroMean P))
    (hV_span : ∀ m, ∃ S : Finset ↥(L2ZeroMean P),
      (↑S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier ∧
      V m = Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P)))
    (hV_proj : ∀ m, p m ∈ V m ∧ IF_eff - p m ∈ (V m)ᗮ)
    (m : ℕ) (h_pm_pos : 0 < ‖(p m : ↥(L2ZeroMean P))‖) :
    ∃ (m_dim : ℕ) (g_P : Fin m_dim → ↥(L2ZeroMean P))
      (_h_orth : Orthonormal ℝ
        (fun i => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P))),
      (∀ j : Fin m_dim, (g_P j : ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
      (∀ θ : EuclideanSpace ℝ (Fin m_dim),
        (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) :
          ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
      (∑ j : Fin m_dim,
        (@inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (g_P j)) ^ 2
          = ‖(p m : ↥(L2ZeroMean P))‖ ^ 2) := by
  -- Set up the carrier as a submodule using linear-closure hypotheses.
  let carrier_sub : Submodule ℝ ↥(L2ZeroMean P) :=
    { carrier := T_set.carrier
      zero_mem' := h_lin_zero
      add_mem' := fun {x y} hx hy => h_lin_add x hx y hy
      smul_mem' := fun c {x} hx => h_lin_smul x hx c }
  -- p m ∈ V m ⊆ span S_m ⊆ carrier_sub (= carrier).
  obtain ⟨S_m, hS_m_sub, hV_eq⟩ := hV_span m
  have hpm_in_VM : (p m : ↥(L2ZeroMean P)) ∈ V m := (hV_proj m).1
  have h_VM_le_car : V m ≤ carrier_sub := by
    rw [hV_eq]
    exact Submodule.span_le.mpr hS_m_sub
  have h_p_in_car : (p m : ↥(L2ZeroMean P)) ∈ T_set.carrier :=
    h_VM_le_car hpm_in_VM
  -- The unit vector u := (1/‖p m‖) • p m.
  have h_pm_norm_ne : ‖(p m : ↥(L2ZeroMean P))‖ ≠ 0 := ne_of_gt h_pm_pos
  set c : ℝ := 1 / ‖(p m : ↥(L2ZeroMean P))‖ with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  let u : ↥(L2ZeroMean P) := c • (p m)
  -- u ∈ carrier.
  have h_u_in_car : u ∈ T_set.carrier := h_lin_smul (p m) h_p_in_car c
  -- Define the 1-element basis.
  let g_P : Fin 1 → ↥(L2ZeroMean P) := fun _ => u
  -- Prove the existential.
  refine ⟨1, g_P, ?_h_orth, ?_h_basis, ?_h_linspan, ?_h_AAT⟩
  · -- Orthonormal: 1-element with ‖u‖_{Lp} = 1.
    have h_u_norm_L2 : ‖u‖ = 1 := by
      change ‖(c • (p m : ↥(L2ZeroMean P)))‖ = 1
      rw [norm_smul, hc_def, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < 1 / ‖(p m : ↥(L2ZeroMean P))‖ by positivity)]
      field_simp
    refine ⟨?_, ?_⟩
    · intro i
      change ‖((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ = 1
      have h_coe_norm :
          ‖((u : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖
            = ‖(u : ↥(L2ZeroMean P))‖ := by
        rfl
      simp [g_P, h_coe_norm, h_u_norm_L2]
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
  · -- ∀ j, g_P j ∈ T_set.carrier
    intro j
    exact h_u_in_car
  · -- ∀ θ, ∑ θ_j • g_P j ∈ T_set.carrier (sum is θ_0 • u, carrier closed under smul).
    intro θ
    have h_sum : (∑ j : Fin 1, ((WithLp.equiv 2 _) θ) j • (g_P j) :
        ↥(L2ZeroMean P))
        = ((WithLp.equiv 2 _) θ) 0 • u := by
      simp [g_P]
    rw [h_sum]
    exact h_lin_smul u h_u_in_car _
  · -- ∑ j ⟨IF_eff, g_P j⟩² = ‖p m‖².
    simp only [Fin.sum_univ_one, g_P]
    have h_inner_proj :
        @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (p m)
          = ‖(p m : ↥(L2ZeroMean P))‖ ^ 2 := by
      have h_orth : ⟪(p m : ↥(L2ZeroMean P)),
          (IF_eff : ↥(L2ZeroMean P)) - p m⟫_ℝ = 0 :=
        (Submodule.mem_orthogonal _ _).mp (hV_proj m).2 (p m) hpm_in_VM
      have h_orth_swap : ⟪(IF_eff : ↥(L2ZeroMean P)) - p m,
          (p m : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
        rw [real_inner_comm]; exact h_orth
      have h_decomp :
          @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (p m)
            = @inner ℝ _ _ ((IF_eff : ↥(L2ZeroMean P)) - p m) (p m)
              + @inner ℝ _ _ (p m : ↥(L2ZeroMean P)) (p m) := by
        rw [← inner_add_left]
        congr 1; abel
      rw [h_decomp, h_orth_swap, zero_add,
        real_inner_self_eq_norm_mul_norm, sq]
    have h_inner_u :
        @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) u
          = c * ‖(p m : ↥(L2ZeroMean P))‖ ^ 2 := by
      change @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (c • (p m))
        = c * ‖(p m : ↥(L2ZeroMean P))‖ ^ 2
      rw [inner_smul_right, h_inner_proj]
    rw [h_inner_u]
    have hc_pm : c * ‖(p m : ↥(L2ZeroMean P))‖ ^ 2 = ‖(p m : ↥(L2ZeroMean P))‖ := by
      rw [hc_def]
      field_simp
    rw [hc_pm]

/-! ## Vector basis-saturation lemma (generalizes the scalar builder to a
d-tuple EIF). -/

open AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec
  (ψDotMat_vec ψDot_proj_vec_clm ψDot_proj_vec_clm_apply T_param_of_vec)
open AsymptoticStatistics.Core.EIFVec (IsEfficientInfluenceFunction_vec)
open AsymptoticStatistics.Core.PathwiseVec (PathwiseDifferentiableAt_vec)
open AsymptoticStatistics.LowerBounds.LAMUnboundedBridge
  (ψ_param_unb_vec ψ_param_unb_at_zero_vec ψ_param_unb_pointwise_shift_vec
   unboundedLam_le_LHS_canonical_vec)

/-- **Vector basis-saturation lemma (single-`m`).**

Merges the scalar carrier / linear-span machinery
(`basis_at_proj_m_pos_unbounded`) with the d-dimensional Parseval machinery.
For a `d`-tuple EIF `IF_eff : Fin d → L²₀(P)` and a fixed projection-residual
stage `m`, with the joint projection submodel `V` and joint projection sequence
`p`, produces the `stdOrthonormalBasis` `g_P` of `V m`, its (i) carrier
membership, (ii) linear-closure membership, the d×d covariance identity
`∑_l ⟪IF i, g_l⟫ ⟪IF i', g_l⟫ = (A · Aᵀ) i i'` (with `A = ψDotMat_vec g_P IF_eff`),
and a companion `Σ_m`-entry clause `(A · Aᵀ) i i' = ⟪p m i, p m i'⟫` (consumed by
the family-level convergence companion).

The carrier route uses `V m ≤ carrier_sub` from `hV_span`; the covariance and
entry identities use the residual swap plus Parseval
(`OrthonormalBasis.sum_inner_mul_inner`). -/
private theorem basis_at_proj_m_pos_unbounded_vec
    (T_set : TangentSpec P)
    (h_lin_smul : ∀ x ∈ T_set.carrier, ∀ t : ℝ, t • x ∈ T_set.carrier)
    (h_lin_add : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      x + y ∈ T_set.carrier)
    (h_lin_zero : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    {d : ℕ} (IF_eff : Fin d → ↥(L2ZeroMean P))
    (V : ℕ → Submodule ℝ ↥(L2ZeroMean P))
    (p : ℕ → Fin d → ↥(L2ZeroMean P))
    (hV_findim : ∀ m, FiniteDimensional ℝ (V m))
    (hV_proj : ∀ m, (V m).HasOrthogonalProjection)
    (hV_span : ∀ m, ∃ S : Finset ↥(L2ZeroMean P),
      (↑S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier ∧
      V m = Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P)))
    (hp_def : ∀ m i, p m i = (V m).starProjection (IF_eff i))
    (m : ℕ) :
    ∃ (m_dim : ℕ) (g_P : Fin m_dim → ↥(L2ZeroMean P))
      (_h_orth : Orthonormal ℝ
        (fun i => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P))),
      (∀ j : Fin m_dim, (g_P j : ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
      (∀ θ : EuclideanSpace ℝ (Fin m_dim),
        (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) :
          ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
      (∀ i i' : Fin d,
        (∑ l : Fin m_dim,
          (@inner ℝ _ _ (IF_eff i : ↥(L2ZeroMean P)) (g_P l))
            * (@inner ℝ _ _ (IF_eff i' : ↥(L2ZeroMean P)) (g_P l)))
          = (ψDotMat_vec g_P IF_eff
              * (ψDotMat_vec g_P IF_eff).transpose) i i') ∧
      (∀ i i' : Fin d,
        (ψDotMat_vec g_P IF_eff
            * (ψDotMat_vec g_P IF_eff).transpose) i i'
          = ⟪(p m i : ↥(L2ZeroMean P)), (p m i' : ↥(L2ZeroMean P))⟫_ℝ) := by
  classical
  haveI := hV_findim m
  haveI := hV_proj m
  -- Carrier as a submodule.
  let carrier_sub : Submodule ℝ ↥(L2ZeroMean P) :=
    { carrier := T_set.carrier
      zero_mem' := h_lin_zero
      add_mem' := fun {x y} hx hy => h_lin_add x hx y hy
      smul_mem' := fun c {x} hx => h_lin_smul x hx c }
  obtain ⟨S_m, hS_m_sub, hV_eq⟩ := hV_span m
  have h_VM_le_car : V m ≤ carrier_sub := by
    rw [hV_eq]; exact Submodule.span_le.mpr hS_m_sub
  -- `stdOrthonormalBasis` of `V m`.
  let b : OrthonormalBasis (Fin (Module.finrank ℝ ↥(V m))) ℝ ↥(V m) :=
    stdOrthonormalBasis ℝ ↥(V m)
  let g_P : Fin (Module.finrank ℝ ↥(V m)) → ↥(L2ZeroMean P) :=
    fun i => (b i : ↥(L2ZeroMean P))
  have hg_orth : Orthonormal ℝ
      (fun i => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P)) := by
    have hb := b.orthonormal
    simpa [g_P, Function.comp] using!
      ((V m).subtypeₗᵢ.orthonormal_comp_iff).mpr hb
  -- (i) carrier membership of each basis vector.
  have hg_in_car : ∀ l, (g_P l : ↥(L2ZeroMean P)) ∈ T_set.carrier :=
    fun l => h_VM_le_car (b l).2
  -- Key fact: the matrix entry `(A·Aᵀ) i i'` equals `⟪p m i, p m i'⟫`.
  have h_entry_proj : ∀ i i' : Fin d,
      (ψDotMat_vec g_P IF_eff * (ψDotMat_vec g_P IF_eff).transpose) i i'
        = ⟪(p m i : ↥(L2ZeroMean P)), (p m i' : ↥(L2ZeroMean P))⟫_ℝ := by
    intro i i'
    -- Expand the matrix product entrywise.
    have h_mat_expand :
        (ψDotMat_vec g_P IF_eff * (ψDotMat_vec g_P IF_eff).transpose) i i'
          = ∑ l : Fin (Module.finrank ℝ ↥(V m)),
              ⟪(IF_eff i : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ
                * ⟪(IF_eff i' : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [ψDotMat_vec, Matrix.transpose_apply]
    rw [h_mat_expand]
    -- Residual orthogonality: `IF_eff i - p m i ⊥ V m`, hence `⟪g_l, IF i⟫ = ⟪g_l, p m i⟫`.
    have h_swap : ∀ (i₀ : Fin d) (l : Fin (Module.finrank ℝ ↥(V m))),
        ⟪(IF_eff i₀ : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪(p m i₀ : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ := by
      intro i₀ l
      have h_perp : (IF_eff i₀ : ↥(L2ZeroMean P)) - (p m i₀) ∈ (V m)ᗮ := by
        rw [hp_def m i₀]
        exact (V m).sub_starProjection_mem_orthogonal (IF_eff i₀)
      have h_g_in : (g_P l : ↥(L2ZeroMean P)) ∈ V m := (b l).2
      -- `g_P l ⊥ (IF_eff i₀ - p m i₀)` (membership in `(V m)ᗮ` with `g_P l ∈ V m`).
      have h_res : ⟪(g_P l : ↥(L2ZeroMean P)),
          (IF_eff i₀ : ↥(L2ZeroMean P)) - (p m i₀)⟫_ℝ = 0 :=
        (Submodule.mem_orthogonal _ _).mp h_perp _ h_g_in
      -- Expand the inner product over the subtraction (the `inner_sub_right`
      -- term-form sidesteps the `rw … at` pattern-match failure on the
      -- `L2ZeroMean` inner notation).
      have h_expand :
          ⟪(g_P l : ↥(L2ZeroMean P)), (IF_eff i₀ : ↥(L2ZeroMean P))⟫_ℝ
            - ⟪(g_P l : ↥(L2ZeroMean P)), (p m i₀ : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
        rw [← inner_sub_right]; exact h_res
      -- `⟪g_l, IF i₀⟫ = ⟪g_l, p i₀⟫`, then commute both sides to match the goal.
      have h_eq : ⟪(g_P l : ↥(L2ZeroMean P)), (IF_eff i₀ : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪(g_P l : ↥(L2ZeroMean P)), (p m i₀ : ↥(L2ZeroMean P))⟫_ℝ :=
        sub_eq_zero.mp h_expand
      -- Commute both sides (term form `real_inner_comm`, avoids the `rw … at`
      -- pattern-match failure on the `L2ZeroMean` inner notation).
      calc ⟪(IF_eff i₀ : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪(g_P l : ↥(L2ZeroMean P)), (IF_eff i₀ : ↥(L2ZeroMean P))⟫_ℝ :=
            real_inner_comm _ _
        _ = ⟪(g_P l : ↥(L2ZeroMean P)), (p m i₀ : ↥(L2ZeroMean P))⟫_ℝ := h_eq
        _ = ⟪(p m i₀ : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ :=
            real_inner_comm _ _
    -- Rewrite the sum onto the projections.
    have h_sum_rewrite :
        (∑ l : Fin (Module.finrank ℝ ↥(V m)),
            ⟪(IF_eff i : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ
              * ⟪(IF_eff i' : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ)
          = ∑ l : Fin (Module.finrank ℝ ↥(V m)),
              ⟪(p m i : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ
                * ⟪(p m i' : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [h_swap i l, h_swap i' l]
    rw [h_sum_rewrite]
    -- Lift `p m i, p m i'` into `V m` and apply Parseval.
    have hp_i_in : (p m i : ↥(L2ZeroMean P)) ∈ V m := by
      rw [hp_def m i]; exact (V m).starProjection_apply_mem (IF_eff i)
    have hp_i'_in : (p m i' : ↥(L2ZeroMean P)) ∈ V m := by
      rw [hp_def m i']; exact (V m).starProjection_apply_mem (IF_eff i')
    let qi : ↥(V m) := ⟨p m i, hp_i_in⟩
    let qi' : ↥(V m) := ⟨p m i', hp_i'_in⟩
    have h_parseval := b.sum_inner_mul_inner qi qi'
    have h_final_inner : ⟪qi, qi'⟫_ℝ
        = ⟪(p m i : ↥(L2ZeroMean P)), (p m i' : ↥(L2ZeroMean P))⟫_ℝ := rfl
    rw [show
        (∑ l, ⟪(p m i : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ
              * ⟪(p m i' : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ)
        = ∑ l, ⟪qi, b l⟫_ℝ * ⟪b l, qi'⟫_ℝ by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      have h_i : ⟪(p m i : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪qi, b l⟫_ℝ := rfl
      have h_i' : ⟪(p m i' : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪b l, qi'⟫_ℝ := by
        show ⟪(p m i' : ↥(L2ZeroMean P)), (g_P l : ↥(L2ZeroMean P))⟫_ℝ = ⟪b l, qi'⟫_ℝ
        rw [real_inner_comm]; rfl
      rw [h_i, h_i']]
    rw [h_parseval, h_final_inner]
  -- The covariance-as-sum clause: the LHS sum equals the matrix entry. The same
  -- entrywise expansion that opens `h_entry_proj` gives the sum = entry directly.
  have h_cov_sum : ∀ i i' : Fin d,
      (∑ l : Fin (Module.finrank ℝ ↥(V m)),
        (@inner ℝ _ _ (IF_eff i : ↥(L2ZeroMean P)) (g_P l))
          * (@inner ℝ _ _ (IF_eff i' : ↥(L2ZeroMean P)) (g_P l)))
        = (ψDotMat_vec g_P IF_eff
            * (ψDotMat_vec g_P IF_eff).transpose) i i' := by
    intro i i'
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [ψDotMat_vec, Matrix.transpose_apply]
  exact ⟨_, g_P, hg_orth, hg_in_car,
    (fun θ => Submodule.sum_mem carrier_sub
      (fun l _ => carrier_sub.smul_mem _ (hg_in_car l))),
    h_cov_sum, h_entry_proj⟩

/-- **Vector basis-saturation: per-`m` family + `Σ_m → Matrix.gram ℝ IF_eff` convergence.**

Hoists `basis_at_proj_m_pos_unbounded_vec` over all `m` and supplies the
convergence companion: the per-`m` covariance matrices
`Σ_m = A_m · Aᵀ_m` (with `A_m = ψDotMat_vec (g_P_m m) IF_eff`, the `1⁻¹ = 1`
collapse already applied) converge to `Matrix.gram ℝ IF_eff` as `m → ∞`. Convergence
is entrywise via Parseval-rewritten entries `⟪p m i, p m i'⟫ → ⟪IF i, IF i'⟫`
(continuity of the inner product on `H × H`, `p m i → IF_eff i`), lifted to the
matrix topology with `tendsto_pi_nhds` twice.

Returns: a per-`m` basis family `g_P_m` with all single-`m` facts (carrier,
linear span, covariance identity), the PSD of `Σ_m m`, the PSD of
`Matrix.gram ℝ IF_eff` (via `Matrix.posSemidef_gram`), and the
`Σ_m → Matrix.gram ℝ IF_eff` `Tendsto`. The main vector theorem consumes this once:
per-`(M, m)` it uses the basis / carrier / identity / PSD, and once for the
outer Loewner step it uses the `Tendsto`. -/
private theorem sigma_m_basis_family_tendsto_gramMatrix_vec
    (T_set : TangentSpec P)
    (h_lin_smul : ∀ x ∈ T_set.carrier, ∀ t : ℝ, t • x ∈ T_set.carrier)
    (h_lin_add : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      x + y ∈ T_set.carrier)
    (h_lin_zero : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    {d : ℕ} {Dψ : tangentSpace T_set →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {IF_eff : Fin d → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec Dψ IF_eff) :
    ∃ (n_m : ℕ → ℕ) (g_P_m : ∀ m, Fin (n_m m) → ↥(L2ZeroMean P))
      (_h_orth_m : ∀ m, Orthonormal ℝ
        (fun i => ((g_P_m m i : ↥(L2ZeroMean P)) : Lp ℝ 2 P))),
      (∀ m, ∀ j : Fin (n_m m), (g_P_m m j : ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
      (∀ m, ∀ θ : EuclideanSpace ℝ (Fin (n_m m)),
        (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P_m m j) :
          ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
      (∀ m, ∀ i i' : Fin d,
        (∑ l : Fin (n_m m),
          (@inner ℝ _ _ (IF_eff i : ↥(L2ZeroMean P)) (g_P_m m l))
            * (@inner ℝ _ _ (IF_eff i' : ↥(L2ZeroMean P)) (g_P_m m l)))
          = (ψDotMat_vec (g_P_m m) IF_eff
              * (ψDotMat_vec (g_P_m m) IF_eff).transpose) i i') ∧
      (∀ m, (ψDotMat_vec (g_P_m m) IF_eff
              * (ψDotMat_vec (g_P_m m) IF_eff).transpose).PosSemidef) ∧
      (Matrix.gram ℝ IF_eff).PosSemidef ∧
      Filter.Tendsto
        (fun m => ψDotMat_vec (g_P_m m) IF_eff
          * (ψDotMat_vec (g_P_m m) IF_eff).transpose)
        atTop (𝓝 (Matrix.gram ℝ IF_eff)) := by
  classical
  haveI hUG_L2 : IsUniformAddGroup ↥(L2ZeroMean P) :=
    (L2ZeroMean P).toAddSubgroup.isUniformAddGroup
  -- Per-component projection sequences.
  have h_mem : ∀ i : Fin d, (IF_eff i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set :=
    fun i => (hEIF i).2
  have h_per_comp : ∀ i : Fin d,
      ∃ V : ℕ → Submodule ℝ ↥(L2ZeroMean P),
      ∃ p : ℕ → ↥(L2ZeroMean P),
        (∀ m, ∃ S : Finset ↥(L2ZeroMean P),
                (↑S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier ∧
                V m = Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P))) ∧
        (∀ m, p m ∈ V m ∧ (IF_eff i) - p m ∈ (V m)ᗮ) ∧
        Tendsto (fun m => ‖(p m : ↥(L2ZeroMean P)) - IF_eff i‖) atTop (𝓝 0) := by
    intro i
    obtain ⟨V_i, p_i, _hV_le_i, _hV_inc_i, _hV_findim_i, hV_span_i,
              hp_proj_i, h_p_tendsto_i⟩ :=
      ProjSeqToEif.proj_seq_to_eif (P := P) T_set (h_mem i)
    exact ⟨V_i, p_i, hV_span_i, hp_proj_i, h_p_tendsto_i⟩
  choose Vc pc hVc_span hpc_proj hpc_tendsto using h_per_comp
  choose Sc hSc_sub hVc_eq using hVc_span
  -- Joint finset / subspace.
  let S : ℕ → Finset ↥(L2ZeroMean P) :=
    fun m => Finset.univ.biUnion (fun i : Fin d => Sc i m)
  let V : ℕ → Submodule ℝ ↥(L2ZeroMean P) :=
    fun m => Submodule.span ℝ (↑(S m) : Set ↥(L2ZeroMean P))
  have hS_sub : ∀ m, (↑(S m) : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier := by
    intro m x hx
    rw [Finset.mem_coe, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact hSc_sub i m hxi
  have hV_span : ∀ m, ∃ S' : Finset ↥(L2ZeroMean P),
      (↑S' : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier ∧
      V m = Submodule.span ℝ (↑S' : Set ↥(L2ZeroMean P)) :=
    fun m => ⟨S m, hS_sub m, rfl⟩
  have hVc_le_V : ∀ i m, Vc i m ≤ V m := by
    intro i m
    rw [hVc_eq i m]
    refine Submodule.span_mono ?_
    intro x hx
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hx⟩
  have hV_findim : ∀ m, FiniteDimensional ℝ (V m) :=
    fun m => FiniteDimensional.span_finset ℝ (S m)
  have hV_complete : ∀ m, CompleteSpace (V m) := fun m =>
    haveI := hV_findim m
    haveI : IsUniformAddGroup ↥(V m) := (V m).toAddSubgroup.isUniformAddGroup
    @FiniteDimensional.complete ℝ ↥(V m) _ _ _ _ _ _ _ _ _
  have hV_proj : ∀ m, (V m).HasOrthogonalProjection := fun m =>
    @Submodule.HasOrthogonalProjection.ofCompleteSpace _ _ _ _ _ (V m)
      (hV_complete m)
  -- Joint projection sequence `p m i := (V m).starProjection (IF_eff i)`.
  let p : ℕ → Fin d → ↥(L2ZeroMean P) := fun m i =>
    haveI := hV_proj m; (V m).starProjection (IF_eff i)
  have hp_def : ∀ m i, p m i = (V m).starProjection (IF_eff i) := fun _ _ => rfl
  -- Joint convergence `‖p m i - IF_eff i‖ → 0` (squeeze by per-component rate).
  have hp_tendsto : ∀ i : Fin d,
      Tendsto (fun m => ‖(p m i : ↥(L2ZeroMean P)) - IF_eff i‖) atTop (𝓝 0) := by
    intro i
    refine squeeze_zero (fun _ => norm_nonneg _) ?_ (hpc_tendsto i)
    intro m
    haveI := hV_proj m
    have hpc_in_V : pc i m ∈ V m := hVc_le_V i m (hpc_proj i m).1
    have h_norm_swap : ‖(p m i : ↥(L2ZeroMean P)) - IF_eff i‖
        = ‖IF_eff i - p m i‖ := norm_sub_rev _ _
    rw [h_norm_swap, norm_sub_rev (pc i m) (IF_eff i)]
    rw [show p m i = (V m).starProjection (IF_eff i) from rfl,
      Submodule.starProjection_minimal (IF_eff i)]
    refine ciInf_le ⟨0, ?_⟩ (⟨pc i m, hpc_in_V⟩ : V m)
    rintro _ ⟨_, rfl⟩
    exact norm_nonneg _
  -- Per-`m` basis data via the single-`m` lemma.
  have h_basis_data := fun m =>
    basis_at_proj_m_pos_unbounded_vec T_set h_lin_smul h_lin_add h_lin_zero
      IF_eff V p hV_findim hV_proj hV_span hp_def m
  choose n_m g_P_m h_orth_m h_in_m h_linspan_m h_cov_m h_entry_proj_m
    using h_basis_data
  -- Σ_m PSD: `A · Aᵀ = A · A.conjTranspose` (TrivialStar on ℝ).
  have hSigma_psd : ∀ m, (ψDotMat_vec (g_P_m m) IF_eff
      * (ψDotMat_vec (g_P_m m) IF_eff).transpose).PosSemidef := by
    intro m
    rw [show (ψDotMat_vec (g_P_m m) IF_eff).transpose
          = (ψDotMat_vec (g_P_m m) IF_eff).conjTranspose from
        (Matrix.conjTranspose_eq_transpose_of_trivial _).symm]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  -- Gram PSD via the named helper.
  have hG_psd : (Matrix.gram ℝ IF_eff).PosSemidef := Matrix.posSemidef_gram ℝ IF_eff
  -- Σ_m → Matrix.gram ℝ IF_eff: entrywise via inner-product continuity.
  have hSigma_tendsto :
      Filter.Tendsto
        (fun m => ψDotMat_vec (g_P_m m) IF_eff
          * (ψDotMat_vec (g_P_m m) IF_eff).transpose)
        atTop (𝓝 (Matrix.gram ℝ IF_eff)) := by
    have h_entry_tendsto : ∀ i i' : Fin d,
        Tendsto (fun m => (ψDotMat_vec (g_P_m m) IF_eff
            * (ψDotMat_vec (g_P_m m) IF_eff).transpose) i i')
          atTop (𝓝 ((Matrix.gram ℝ IF_eff) i i')) := by
      intro i i'
      have h_entry : ∀ m, (ψDotMat_vec (g_P_m m) IF_eff
            * (ψDotMat_vec (g_P_m m) IF_eff).transpose) i i'
            = ⟪(p m i : ↥(L2ZeroMean P)), (p m i' : ↥(L2ZeroMean P))⟫_ℝ :=
        fun m => h_entry_proj_m m i i'
      have hG_entry : (Matrix.gram ℝ IF_eff) i i'
          = ⟪(IF_eff i : ↥(L2ZeroMean P)), (IF_eff i' : ↥(L2ZeroMean P))⟫_ℝ := rfl
      have hp_i_tendsto : Tendsto (fun m => (p m i : ↥(L2ZeroMean P))) atTop
          (𝓝 (IF_eff i)) :=
        tendsto_iff_norm_sub_tendsto_zero.mpr (hp_tendsto i)
      have hp_i'_tendsto : Tendsto (fun m => (p m i' : ↥(L2ZeroMean P))) atTop
          (𝓝 (IF_eff i')) :=
        tendsto_iff_norm_sub_tendsto_zero.mpr (hp_tendsto i')
      have h_inner_tendsto :
          Tendsto (fun m => ⟪(p m i : ↥(L2ZeroMean P)),
              (p m i' : ↥(L2ZeroMean P))⟫_ℝ) atTop
            (𝓝 (⟪(IF_eff i : ↥(L2ZeroMean P)), (IF_eff i' : ↥(L2ZeroMean P))⟫_ℝ)) := by
        -- Port note (Lean v4.33): the `continuous_inner.tendsto.comp` route now times out in
        -- `whnf`; `Filter.Tendsto.inner` gives the same statement directly.
        exact hp_i_tendsto.inner hp_i'_tendsto
      have h_funeq : (fun m => (ψDotMat_vec (g_P_m m) IF_eff
            * (ψDotMat_vec (g_P_m m) IF_eff).transpose) i i')
          = (fun m => ⟪(p m i : ↥(L2ZeroMean P)),
              (p m i' : ↥(L2ZeroMean P))⟫_ℝ) := by
        funext m; exact h_entry m
      rw [h_funeq, hG_entry]
      exact h_inner_tendsto
    refine tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun i' => ?_))
    exact h_entry_tendsto i i'
  exact ⟨n_m, g_P_m, h_orth_m, h_in_m, h_linspan_m, h_cov_m,
    hSigma_psd, hG_psd, hSigma_tendsto⟩

/-! ## `LHS_canonical` monotonicity in the loss. -/

/-- **`LHS_canonical` is monotone in the loss.** If `f x ≤ g x` pointwise then
`LHS_canonical … f ≤ LHS_canonical … g`. The centering `ψ(curve)` is the same
for both; only the loss differs, so it goes through `iSup_mono` /
`liminf_le_liminf` / `Finset.sup_mono_fun` / `lintegral_mono`. -/
private lemma LHS_canonical_mono
    (T_set : TangentSpec P)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (ψ : Measure Ω → ℝ)
    {f g : ℝ → ℝ≥0∞} (hfg : ∀ x, f x ≤ g x) :
    LHS_canonical T_set T_n ψ f ≤ LHS_canonical T_set T_n ψ g := by
  unfold LHS_canonical
  refine iSup_mono ?_
  intro I
  refine Filter.liminf_le_liminf
    (Filter.Eventually.of_forall (fun n => ?_))
  refine Finset.sup_mono_fun (fun b _ => ?_)
  refine MeasureTheory.lintegral_mono (fun X => ?_)
  exact hfg _

/-! ## Main theorem. -/

-- The three-tier proof (inner 8.11 call plus the two outer passes) is a
-- single large term; elaborating the hoisted `proj_seq_to_eif` projection
-- sequence through `hBdd_inner` requires a raised heartbeat limit.
set_option maxHeartbeats 1600000 in
-- Large single elaboration term; raise the heartbeat budget.
/-- **Theorem 25.21 (semiparametric local asymptotic minimax).**

The hypothesis set is: a linear-space tangent set, a pathwise-differentiable
`ψ` with efficient influence function, an estimator sequence, a subconvex loss
(`BowlShaped` plus per-truncation lower semicontinuity, matching vdV's notion of
a subconvex loss), and a single `g_P`-independent tightness hypothesis over
`Measure.pi P` recentered on `single 0 (ψ P)`. The conclusion bounds the local
minimax risk below by the Gaussian integral `∫⁻ ℓ dN(0, ‖IF_eff‖²)`. -/
theorem lam_semiparametric_unbounded
    (T_set : TangentSpec P)
    (_hLin_smul : ∀ x ∈ T_set.carrier, ∀ t : ℝ, t • x ∈ T_set.carrier)
    (_hLin_add : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier, x + y ∈ T_set.carrier)
    (_hLin_zero : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    {ψ : Measure Ω → ℝ}
    (_hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set) _hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ) (_hT_n : ∀ n, Measurable (T_n n))
    (ℓ : ℝ → ℝ≥0∞) (_hℓ_sub : BowlShaped ℓ)
    (_hℓ_M_lsc : ∀ M : ℕ, LowerSemicontinuous (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞)))
    (_hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
            (fun ω => (Real.sqrt n) •
              (LAMSemiparametricBridge.T_param_of T_n n ω
                - EuclideanSpace.single (0 : Fin 1) (ψ P)))))) :
    LHS_canonical T_set T_n ψ ℓ
      ≥ ∫⁻ u : ℝ, ℓ u
          ∂(ProbabilityTheory.gaussianReal 0 ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩) := by
  set sigma_sq : ℝ≥0 := ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩ with hsigma_sq
  -- Hoist `proj_seq_to_eif` so the projection sequence `p_m` is in scope.
  obtain ⟨_V, p, _hV_le, _hV_inc, _hV_findim, _hV_span, hV_proj, hp_conv⟩ :=
    ProjSeqToEif.proj_seq_to_eif (P := P) T_set _hEIF.2
  -- Bessel inequality: ‖p m‖² ≤ ‖IF_eff‖² for all m.
  have h_bessel_p : ∀ m : ℕ,
      ‖(p m : ↥(L2ZeroMean P))‖ ^ 2 ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 := by
    intro m
    obtain ⟨hpm_in, hres_orth⟩ := hV_proj m
    have h_orth : ⟪(p m : ↥(L2ZeroMean P)),
        (IF_eff : ↥(L2ZeroMean P)) - p m⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hres_orth (p m) hpm_in
    have h_pyth : ‖((p m : ↥(L2ZeroMean P)) +
          ((IF_eff : ↥(L2ZeroMean P)) - p m))‖ *
          ‖((p m : ↥(L2ZeroMean P)) +
          ((IF_eff : ↥(L2ZeroMean P)) - p m))‖
        = ‖(p m : ↥(L2ZeroMean P))‖ * ‖(p m : ↥(L2ZeroMean P))‖
          + ‖(IF_eff : ↥(L2ZeroMean P)) - p m‖
            * ‖(IF_eff : ↥(L2ZeroMean P)) - p m‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h_orth
    have h_eq : (p m : ↥(L2ZeroMean P)) +
        ((IF_eff : ↥(L2ZeroMean P)) - p m) = IF_eff := by abel
    rw [h_eq] at h_pyth
    have h_pyth' : ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2
        = ‖(p m : ↥(L2ZeroMean P))‖ ^ 2
          + ‖(IF_eff : ↥(L2ZeroMean P)) - p m‖ ^ 2 := by
      simpa [sq] using h_pyth
    nlinarith [sq_nonneg ‖(IF_eff : ↥(L2ZeroMean P)) - p m‖, h_pyth']
  -- Derive the basis sequence internally (positive-norm via
  -- `basis_at_proj_m_pos_unbounded`, zero-norm via the empty basis).
  have basis_seq_v2 : ∀ m : ℕ,
      ∃ (m_dim : ℕ) (g_P : Fin m_dim → ↥(L2ZeroMean P))
        (_h_orth : Orthonormal ℝ
          (fun i => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P))),
        (∀ j : Fin m_dim, (g_P j : ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
        (∀ θ : EuclideanSpace ℝ (Fin m_dim),
          (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) :
            ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
        (∑ j : Fin m_dim,
          (@inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (g_P j)) ^ 2
            = ‖(p m : ↥(L2ZeroMean P))‖ ^ 2) := by
    intro m
    by_cases h_pm_pos : 0 < ‖(p m : ↥(L2ZeroMean P))‖
    · exact basis_at_proj_m_pos_unbounded
        T_set _hLin_smul _hLin_add _hLin_zero
        IF_eff _V p _hV_span hV_proj m h_pm_pos
    · -- ‖p m‖ = 0 ⇒ p m = 0 ⇒ ‖p m‖² = 0; empty basis works.
      have h_pm_zero : (p m : ↥(L2ZeroMean P)) = 0 := by
        have h_norm_zero : ‖(p m : ↥(L2ZeroMean P))‖ = 0 :=
          le_antisymm (not_lt.mp h_pm_pos) (norm_nonneg _)
        exact norm_eq_zero.mp h_norm_zero
      refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro i; exact i.elim0
        · intro i j _; exact i.elim0
      · intro j; exact j.elim0
      · intro θ
        simp only [Finset.univ_eq_empty, Finset.sum_empty]
        exact _hLin_zero
      · simp only [Finset.univ_eq_empty, Finset.sum_empty, h_pm_zero,
          norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]
  -- Per-(M, m) inner Bayes-risk lower bound at the proj-seq variance `σ_m_sq m := ‖p m‖²`.
  have hBdd_inner : ∀ (M : ℕ) (σ_m_sq : ℝ≥0)
      (_ : (σ_m_sq : ℝ) ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2)
      (m : ℕ)
      (_ : σ_m_sq = ⟨‖(p m : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩),
      LHS_canonical T_set T_n ψ (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))
        ≥ ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.gaussianReal 0 σ_m_sq) := by
    intro M σ_m_sq h_σ_bound m h_σ_eq
    -- Extract basis from `basis_seq_v2`, bridge variance equality via `h_σ_eq`.
    obtain ⟨m_dim, g_P, h_orth, h_basis_in, h_linspan, h_AAT_eq⟩ : ∃
        (m_dim : ℕ) (g_P : Fin m_dim → ↥(L2ZeroMean P))
        (_h_orth : Orthonormal ℝ
          (fun i => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P))),
        (∀ j : Fin m_dim, (g_P j : ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
        (∀ θ : EuclideanSpace ℝ (Fin m_dim),
          (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) :
            ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
        (∑ j : Fin m_dim,
          (@inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (g_P j)) ^ 2
            = (σ_m_sq : ℝ)) := by
      obtain ⟨m_dim, g_P, h_orth, h_basis_in, h_linspan,
              h_AAT_eq_proj⟩ := basis_seq_v2 m
      refine ⟨m_dim, g_P, h_orth, h_basis_in, h_linspan, ?_⟩
      rw [h_AAT_eq_proj, h_σ_eq]
      rfl
    -- ===== 8.11 hypothesis discharges (same as ConvolutionUnbounded.lean). =====
    have h_gP_total_meas : Measurable
        (AsymptoticStatistics.ParametricFamily.g_P_total g_P) := by
      unfold AsymptoticStatistics.ParametricFamily.g_P_total
      exact (WithLp.measurable_toLp 2 (Fin m_dim → ℝ)).comp
        (measurable_pi_iff.mpr
          (fun i => AsymptoticStatistics.ParametricFamily.gMk_meas g_P i))
    have h_unbSub_hJ_fisher :
        ∀ u v : EuclideanSpace ℝ (Fin m_dim),
          AsymptoticStatistics.fisherInformation
              (AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel g_P h_orth) P 0
              (AsymptoticStatistics.ParametricFamily.g_P_total g_P) u v
            = @inner ℝ _ _ u
                ((WithLp.equiv 2 _).symm
                  ((1 : Matrix (Fin m_dim) (Fin m_dim) ℝ).mulVec
                    ((WithLp.equiv 2 _) v))) := by
      intro u v
      rw [AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel_fisher_info g_P h_orth u v,
        Matrix.one_mulVec, Equiv.symm_apply_apply]
    have hT_param_meas : ∀ n,
        Measurable (LAMSemiparametricBridge.T_param_of T_n n) := by
      intro n
      unfold LAMSemiparametricBridge.T_param_of
      exact (WithLp.measurable_toLp 2 (Fin 1 → ℝ)).comp
        (measurable_pi_iff.mpr (fun _ => _hT_n n))
    -- BowlShaped + LSC lift for `L_param_of (ℓ ⊓ M)`.
    have hL_param_bowl : BowlShaped
        (LAMSemiparametricBridge.L_param_of
          (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))) := by
      have h_scalar : BowlShaped (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞)) :=
        _hℓ_sub.truncate (M : ℝ≥0∞)
      refine ⟨?_, ?_, ?_⟩
      · unfold LAMSemiparametricBridge.L_param_of
        exact h_scalar.measurable.comp <|
          (measurable_pi_apply 0).comp <|
            WithLp.measurable_ofLp 2 (Fin 1 → ℝ)
      · intro y
        unfold LAMSemiparametricBridge.L_param_of
        change (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))
              ((WithLp.equiv 2 (Fin 1 → ℝ)) (-y) 0)
          = (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))
              ((WithLp.equiv 2 (Fin 1 → ℝ)) y 0)
        simp only []
        exact h_scalar.symm _
      · intro c
        unfold LAMSemiparametricBridge.L_param_of
        have h_set_eq :
            {y : EuclideanSpace ℝ (Fin 1) |
              (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))
                ((WithLp.equiv 2 (Fin 1 → ℝ)) y 0) ≤ c}
            = (fun y : EuclideanSpace ℝ (Fin 1) =>
                (WithLp.equiv 2 (Fin 1 → ℝ)) y 0) ⁻¹'
              {u : ℝ | (fun u' : ℝ => ℓ u' ⊓ (M : ℝ≥0∞)) u ≤ c} := rfl
        rw [h_set_eq]
        refine (h_scalar.convex_sublevel c).linear_preimage
          { toFun := fun y => (WithLp.equiv 2 (Fin 1 → ℝ)) y 0
            map_add' := by intro x y; rfl
            map_smul' := by intro c x; rfl }
    have hL_param_lsc : LowerSemicontinuous
        (LAMSemiparametricBridge.L_param_of
          (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))) := by
      unfold LAMSemiparametricBridge.L_param_of
      exact (_hℓ_M_lsc M).comp <|
        (continuous_apply (0 : Fin 1)).comp <|
          PiLp.continuous_ofLp 2 (fun _ : Fin 1 => ℝ)
    -- Derive `hTight` from the canonical `_hTight`.
    have hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel g_P h_orth) P
              (0 : EuclideanSpace ℝ (Fin m_dim)) n).map
            (fun ω => (Real.sqrt n) •
              (LAMSemiparametricBridge.T_param_of T_n n ω
                - ψ_param_unb g_P h_orth ψ
                    (0 : EuclideanSpace ℝ (Fin m_dim)))))) := by
      have h_seq_eq :
          (fun n : ℕ =>
            (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
                (AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel g_P h_orth) P
                (0 : EuclideanSpace ℝ (Fin m_dim)) n).map
              (fun ω => (Real.sqrt n) •
                (LAMSemiparametricBridge.T_param_of T_n n ω
                  - ψ_param_unb g_P h_orth ψ
                      (0 : EuclideanSpace ℝ (Fin m_dim)))))
          = (fun n : ℕ =>
            (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
              (fun ω => (Real.sqrt n) •
                (LAMSemiparametricBridge.T_param_of T_n n ω
                  - EuclideanSpace.single (0 : Fin 1) (ψ P)))) := by
        funext n
        rw [productMeasure_unbounded_at_zero g_P h_orth n,
          ψ_param_unb_at_zero g_P h_orth ψ]
      rw [h_seq_eq]
      exact _hTight
    -- Apply Theorem 8.11's per-direction-shift form to the unbounded submodel,
    -- feeding the submodel functional `ψ_param_unb`. The per-direction shift
    -- `hψ_shift` comes from the pathwise Gateaux limit.
    have hParamLAM :=
      AsymptoticStatistics.LocalAsymptoticMinimax.local_asymptotic_minimax_bound_of_pointwise_shift
        (M := AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel g_P h_orth)
        (μ := P) (θ₀ := (0 : EuclideanSpace ℝ (Fin m_dim)))
        (ℓ := AsymptoticStatistics.ParametricFamily.g_P_total g_P)
        (hℓ := h_gP_total_meas)
        (hDQM := AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel_DQM g_P h_orth)
        (J := (1 : Matrix (Fin m_dim) (Fin m_dim) ℝ))
        (hJ := Matrix.PosDef.one)
        (hJ_fisher := h_unbSub_hJ_fisher)
        (ψ := ψ_param_unb g_P h_orth ψ)
        (ψDot := ψDot_proj_clm g_P IF_eff)
        (hψ_shift := ψ_param_unb_pointwise_shift T_set g_P h_orth h_linspan
          _hψ _hEIF)
        (ψDotMat := LAMSemiparametricBridge.ψDotMat g_P IF_eff)
        (h_ψDot_mat := fun h => ψDot_proj_clm_apply g_P IF_eff h)
        (T := LAMSemiparametricBridge.T_param_of T_n)
        (hT_meas := hT_param_meas)
        (L := LAMSemiparametricBridge.L_param_of
                (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞)))
        (hL_bowl := hL_param_bowl)
        (hL_lsc := hL_param_lsc)
        (hTight := hTight)
        (hPDF :=
          AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel_isPDFOf g_P h_orth)
    -- multivariateGaussian (Fin 1) → gaussianReal collapse.
    have h_gaussian_eq :
        ∫⁻ y : EuclideanSpace ℝ (Fin 1),
            LAMSemiparametricBridge.L_param_of (fun u => ℓ u ⊓ (M : ℝ≥0∞)) y
          ∂(ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
              ((LAMSemiparametricBridge.ψDotMat g_P IF_eff) *
                (1 : Matrix (Fin m_dim) (Fin m_dim) ℝ)⁻¹ *
                (LAMSemiparametricBridge.ψDotMat g_P IF_eff).transpose))
        = ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.gaussianReal 0 σ_m_sq) := by
      set A := LAMSemiparametricBridge.ψDotMat g_P IF_eff
        with hA_def
      set S := A * (1 : Matrix (Fin m_dim) (Fin m_dim) ℝ)⁻¹ * A.transpose
        with hS_def
      have hS_entry : S 0 0 = (σ_m_sq : ℝ) := by
        simp only [hS_def, inv_one, Matrix.mul_one]
        simp only [Matrix.mul_apply, Matrix.transpose_apply,
          ]
        simp_rw [← sq]
        exact h_AAT_eq
      have hS_psd : S.PosSemidef := by
        have hone : (Matrix.PosSemidef
            ((1 : Matrix (Fin m_dim) (Fin m_dim) ℝ)⁻¹)) := by
          rw [inv_one]; exact Matrix.PosSemidef.one
        have := hone.mul_mul_conjTranspose_same A
        simpa [hS_def, Matrix.conjTranspose_eq_transpose_of_trivial] using this
      have hMP : MeasureTheory.MeasurePreserving
          (fun x : EuclideanSpace ℝ (Fin 1) => x 0)
          (ProbabilityTheory.multivariateGaussian
              (0 : EuclideanSpace ℝ (Fin 1)) S)
          (ProbabilityTheory.gaussianReal 0 σ_m_sq) := by
        have hbase := ProbabilityTheory.measurePreserving_eval_multivariateGaussian
          (μ := (0 : EuclideanSpace ℝ (Fin 1))) (S := S) hS_psd (i := (0 : Fin 1))
        have h_var : (S 0 0).toNNReal = σ_m_sq := by
          rw [hS_entry]; exact Real.toNNReal_coe
        have h_mean : ((0 : EuclideanSpace ℝ (Fin 1)) : Fin 1 → ℝ) 0 = (0 : ℝ) := rfl
        simpa [h_mean, h_var] using hbase
      have hℓ_M_meas : Measurable (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞)) :=
        _hℓ_sub.measurable.min measurable_const
      have hcomp := hMP.lintegral_comp hℓ_M_meas
      simpa [LAMSemiparametricBridge.L_param_of] using hcomp
    -- Chain: ∫⁻ ℓ_M dN(0, σ_m_sq) ≤ localAsymptoticRisk ≤ LHS_canonical(ℓ_M).
    -- 8.11 bound: localAsymptoticRisk ≥ ∫⁻ L dN(0, ψDotMat·I⁻¹·ψDotMatᵀ).
    -- bridge: localAsymptoticRisk(unbounded, ψ_param_unb) ≤ LHS_canonical, exact
    -- per `n`.
    have h_bridge := unboundedLam_le_LHS_canonical T_set g_P h_orth
      h_basis_in h_linspan T_n _hT_n ψ
      (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))
    -- Assemble: ∫⁻ ℓ_M dN(0,σ_m²) = ∫⁻ L dN(0, ψDotMat·I⁻¹·ψDotMatᵀ)
    --   ≤ localAsymptoticRisk(unbounded) ≤ LHS_canonical(ℓ_M).
    change ∫⁻ u, ℓ u ⊓ (M : ℝ≥0∞)
          ∂(ProbabilityTheory.gaussianReal 0 σ_m_sq)
        ≤ LHS_canonical T_set T_n ψ (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))
    rw [← h_gaussian_eq]
    exact le_trans hParamLAM h_bridge
  ----------------------------------------------------------------------------
  -- Outer-1 (Loewner / `m → ∞`).
  ----------------------------------------------------------------------------
  have hBdd_lower_bound : ∀ M : ℕ,
      LHS_canonical T_set T_n ψ (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞))
        ≥ ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.gaussianReal 0
                ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩) := by
    intro M
    set v_inf : ℝ≥0 := ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩ with hv_inf_def
    set LHS_M : ℝ≥0∞ :=
      LHS_canonical T_set T_n ψ (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞)) with hLHS_def
    by_cases h_pos : 0 < v_inf
    · -- Positive variance branch.
      have hp_norm_conv : Filter.Tendsto (fun m => ‖(p m : ↥(L2ZeroMean P))‖)
          atTop (𝓝 ‖(IF_eff : ↥(L2ZeroMean P))‖) := by
        have hdist : Filter.Tendsto
            (fun m => ‖(p m : ↥(L2ZeroMean P)) - IF_eff‖) atTop (𝓝 0) := hp_conv
        have hp_to_IF : Filter.Tendsto (fun m => (p m : ↥(L2ZeroMean P))) atTop
            (𝓝 (IF_eff : ↥(L2ZeroMean P))) :=
          tendsto_iff_norm_sub_tendsto_zero.mpr hdist
        exact hp_to_IF.norm
      have hp_sq_conv : Filter.Tendsto (fun m => ‖(p m : ↥(L2ZeroMean P))‖ ^ 2)
          atTop (𝓝 (‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2)) := by
        have := hp_norm_conv.mul hp_norm_conv
        simpa [sq] using this
      let σ_m_sq : ℕ → ℝ≥0 := fun m =>
        ⟨‖(p m : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩
      have hσ_conv : Filter.Tendsto (fun m => (σ_m_sq m : ℝ)) atTop
          (𝓝 (‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2)) := by
        simpa [σ_m_sq, NNReal.coe_mk] using! hp_sq_conv
      let g : ℝ → ℝ := fun u => (ℓ u ⊓ (M : ℝ≥0∞)).toReal
      have hM_top : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
      have h_lt_top : ∀ u, ℓ u ⊓ (M : ℝ≥0∞) < ∞ := fun u =>
        lt_of_le_of_lt inf_le_right hM_top.lt_top
      have hg_meas : Measurable g :=
        (_hℓ_sub.measurable.min measurable_const).ennreal_toReal
      have hg_nn : ∀ u, 0 ≤ g u := fun u => ENNReal.toReal_nonneg
      have hg_bdd : ∀ u, |g u| ≤ (M : ℝ) := fun u => by
        have h0 : 0 ≤ g u := hg_nn u
        have h_le : g u ≤ (M : ℝ) := by
          have h1 : ℓ u ⊓ (M : ℝ≥0∞) ≤ (M : ℝ≥0∞) := inf_le_right
          have h2 : (ℓ u ⊓ (M : ℝ≥0∞)).toReal ≤ ((M : ℝ≥0∞)).toReal :=
            ENNReal.toReal_mono hM_top h1
          simpa [g, ENNReal.toReal_natCast] using h2
        rw [abs_of_nonneg h0]; exact h_le
      have hg_ofReal : ∀ u, (ℓ u ⊓ (M : ℝ≥0∞)) = ENNReal.ofReal (g u) := fun u => by
        simp [g, ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp (h_lt_top u))]
      have h_int_real :
          Filter.Tendsto (fun m => ∫ u, g u ∂(ProbabilityTheory.gaussianReal 0 (σ_m_sq m)))
            atTop (𝓝 (∫ u, g u ∂(ProbabilityTheory.gaussianReal 0 v_inf))) := by
        have h_pos_real : 0 < v_inf := h_pos
        have hσ' : Filter.Tendsto (fun m => (σ_m_sq m : ℝ)) atTop (𝓝 ((v_inf : ℝ))) := by
          simpa [v_inf, NNReal.coe_mk] using! hσ_conv
        exact ForMathlib.GaussianRealTV.gaussianReal_integral_continuous_of_var_tendsto
          h_pos_real hσ' hg_meas (M := (M : ℝ)) hg_bdd
      have h_int_lintegral_eq : ∀ ν : Measure ℝ, [IsProbabilityMeasure ν] →
          ∫⁻ u, ℓ u ⊓ (M : ℝ≥0∞) ∂ν = ENNReal.ofReal (∫ u, g u ∂ν) := by
        intro ν _
        have h_int_g : Integrable g ν :=
          Integrable.of_bound hg_meas.aestronglyMeasurable (M : ℝ)
            (Filter.Eventually.of_forall fun u => by
              rw [Real.norm_eq_abs]; exact hg_bdd u)
        have h_nn : 0 ≤ᵐ[ν] g := Filter.Eventually.of_forall hg_nn
        calc ∫⁻ u, ℓ u ⊓ (M : ℝ≥0∞) ∂ν
            = ∫⁻ u, ENNReal.ofReal (g u) ∂ν := by
              refine lintegral_congr (fun u => ?_)
              exact hg_ofReal u
          _ = ENNReal.ofReal (∫ u, g u ∂ν) :=
              (ofReal_integral_eq_lintegral_ofReal h_int_g h_nn).symm
      have h_int_conv :
          Filter.Tendsto
            (fun m => ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
                ∂(ProbabilityTheory.gaussianReal 0 (σ_m_sq m)))
            atTop
            (𝓝 (∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
                ∂(ProbabilityTheory.gaussianReal 0 v_inf))) := by
        have h_lift : Filter.Tendsto
            (fun m => ENNReal.ofReal (∫ u, g u ∂(ProbabilityTheory.gaussianReal 0 (σ_m_sq m))))
            atTop (𝓝 (ENNReal.ofReal (∫ u, g u ∂(ProbabilityTheory.gaussianReal 0 v_inf)))) :=
          (ENNReal.continuous_ofReal.tendsto _).comp h_int_real
        rw [h_int_lintegral_eq (ProbabilityTheory.gaussianReal 0 v_inf)]
        refine h_lift.congr' (Filter.Eventually.of_forall fun m => ?_)
        exact (h_int_lintegral_eq (ProbabilityTheory.gaussianReal 0 (σ_m_sq m))).symm
      have h_per_m : ∀ m : ℕ,
          ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
              ∂(ProbabilityTheory.gaussianReal 0 (σ_m_sq m)) ≤ LHS_M := by
        intro m
        have h_bess : ((σ_m_sq m : ℝ≥0) : ℝ) ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 := by
          change ‖(p m : ↥(L2ZeroMean P))‖ ^ 2 ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2
          exact h_bessel_p m
        have := hBdd_inner M (σ_m_sq m) h_bess m rfl
        simpa [LHS_M, hLHS_def] using this
      have hgoal : ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
          ∂(ProbabilityTheory.gaussianReal 0 v_inf) ≤ LHS_M :=
        le_of_tendsto' h_int_conv h_per_m
      simpa [v_inf] using hgoal
    · -- Zero-variance branch.
      have hv_zero : v_inf = 0 := le_antisymm (not_lt.mp h_pos) (zero_le)
      have h_bess0 : ((0 : ℝ≥0) : ℝ) ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 := by
        simpa using sq_nonneg ‖(IF_eff : ↥(L2ZeroMean P))‖
      have h_IF_norm_sq_zero : ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 = 0 := by
        have h_v_inf_real : (v_inf : ℝ) = 0 := by rw [hv_zero]; rfl
        exact h_v_inf_real
      have h_p0_norm_sq_zero : ‖(p 0 : ↥(L2ZeroMean P))‖ ^ 2 = 0 := by
        have h_le := h_bessel_p 0
        rw [h_IF_norm_sq_zero] at h_le
        exact le_antisymm h_le (sq_nonneg _)
      have h_σ_eq :
          (0 : ℝ≥0) = ⟨‖(p 0 : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩ := by
        apply Subtype.ext
        change (0 : ℝ) = ‖(p 0 : ↥(L2ZeroMean P))‖ ^ 2
        exact h_p0_norm_sq_zero.symm
      have h := hBdd_inner M 0 h_bess0 0 h_σ_eq
      change LHS_M ≥ ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
          ∂(ProbabilityTheory.gaussianReal 0 v_inf)
      rw [hLHS_def, hv_zero]
      exact h
  ----------------------------------------------------------------------------
  -- Outer-2 (MCT / `ℓ_M ↑ ℓ`).
  ----------------------------------------------------------------------------
  have h_sup_eq : ∀ u : ℝ, (⨆ M : ℕ, ℓ u ⊓ (M : ℝ≥0∞)) = ℓ u := by
    intro u
    have h_distrib : (⨆ M : ℕ, ℓ u ⊓ (M : ℝ≥0∞))
        = ℓ u ⊓ (⨆ M : ℕ, (M : ℝ≥0∞)) := (inf_iSup_eq _ _).symm
    rw [h_distrib, ENNReal.iSup_natCast]
    simp
  have h_mono : Monotone fun M : ℕ => fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞) := by
    intro a b hab u
    have hcast : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hab
    exact inf_le_inf_left (ℓ u) hcast
  have h_meas : ∀ M : ℕ, Measurable (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞)) := by
    intro M
    exact Measurable.min _hℓ_sub.measurable measurable_const
  have h_mct : ∫⁻ u : ℝ, ℓ u ∂(ProbabilityTheory.gaussianReal 0 sigma_sq)
      = ⨆ M : ℕ, ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
          ∂(ProbabilityTheory.gaussianReal 0 sigma_sq) := by
    calc ∫⁻ u : ℝ, ℓ u ∂(ProbabilityTheory.gaussianReal 0 sigma_sq)
        = ∫⁻ u : ℝ, (⨆ M : ℕ, ℓ u ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.gaussianReal 0 sigma_sq) := by
          refine lintegral_congr (fun u => ?_)
          exact (h_sup_eq u).symm
      _ = ⨆ M : ℕ, ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.gaussianReal 0 sigma_sq) :=
          MeasureTheory.lintegral_iSup h_meas h_mono
  have h_per_M : ∀ M : ℕ,
      ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
          ∂(ProbabilityTheory.gaussianReal 0 sigma_sq)
        ≤ LHS_canonical T_set T_n ψ ℓ := by
    intro M
    have h_le_full :
        LHS_canonical T_set T_n ψ (fun u => ℓ u ⊓ (M : ℝ≥0∞))
          ≤ LHS_canonical T_set T_n ψ ℓ :=
      LHS_canonical_mono T_set T_n ψ (fun _ => inf_le_left)
    exact le_trans (hBdd_lower_bound M) h_le_full
  change LHS_canonical T_set T_n ψ ℓ
      ≥ ∫⁻ u : ℝ, ℓ u ∂(ProbabilityTheory.gaussianReal 0 sigma_sq)
  rw [ge_iff_le, h_mct]
  exact iSup_le h_per_M

/-! ## Vector core: `LHS_canonical_vec` monotonicity + the d-dim LAM bound. -/

/-- **`LHS_canonical_vec` is monotone in the loss.** Vector-codomain sibling of
`LHS_canonical_mono`: same `iSup` / `liminf` / `Finset.sup` / `lintegral`
structure, only the loss differs (same `ψ(curve)` centering). -/
private lemma LHS_canonical_vec_mono
    {d : ℕ} (T_set : TangentSpec P)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d))
    {f g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hfg : ∀ x, f x ≤ g x) :
    LHS_canonical_vec T_set T_n ψ f ≤ LHS_canonical_vec T_set T_n ψ g := by
  unfold LHS_canonical_vec
  refine iSup_mono ?_
  intro I
  refine Filter.liminf_le_liminf
    (Filter.Eventually.of_forall (fun n => ?_))
  refine Finset.sup_mono_fun (fun b _ => ?_)
  refine MeasureTheory.lintegral_mono (fun X => ?_)
  exact hfg _

-- The three-tier vector proof (inner 8.11 call plus the two outer passes) is a
-- single large term; same heartbeat raise as the scalar core.
set_option maxHeartbeats 1600000 in
-- Large single elaboration term; raise the heartbeat budget.
/-- **Theorem 25.21 (semiparametric local asymptotic minimax, vector form).**

Vector (`ℝᵈ`) generalization of `lam_semiparametric_unbounded`: the functional
`ψ : Measure Ω → ℝᵈ`, its efficient influence function `IF_eff : Fin d → L²₀(P)`,
and the loss `ℓ : ℝᵈ → ℝ≥0∞` are all vector-valued. The Gaussian limit is the
non-degenerate multivariate Gaussian `N(0, Matrix.gram ℝ IF_eff)`: the outer Loewner
step uses the multivariate liminf-lsc bound
`multivariateGaussian_lintegral_le_liminf_of_tendsto` rather than the scalar
Gaussian-integral continuity. -/
theorem lam_semiparametric_unbounded_vec
    (T_set : TangentSpec P)
    (_hLin_smul : ∀ x ∈ T_set.carrier, ∀ t : ℝ, t • x ∈ T_set.carrier)
    (_hLin_add : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier, x + y ∈ T_set.carrier)
    (_hLin_zero : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    {d : ℕ}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (_hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin d → ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction_vec _hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (_hT_n : ∀ n, Measurable (T_n n))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (_hℓ_sub : BowlShaped ℓ)
    (_hℓ_M_lsc : ∀ M : ℕ,
      LowerSemicontinuous (fun u : EuclideanSpace ℝ (Fin d) => ℓ u ⊓ (M : ℝ≥0∞)))
    (_hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
            (fun ω => (Real.sqrt n) •
              (T_param_of_vec T_n n ω - ψ P))))) :
    LHS_canonical_vec T_set T_n ψ ℓ
      ≥ ∫⁻ y : EuclideanSpace ℝ (Fin d), ℓ y
          ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff)) := by
  -- Hoist the per-`m` basis family + `Σ_m → Matrix.gram ℝ IF_eff` convergence.
  obtain ⟨n_m, g_P_m, h_orth_m, h_carrier, h_linspan, h_cov_id,
          h_Sig_psd, h_gram_psd, h_Sig_tendsto⟩ :=
    sigma_m_basis_family_tendsto_gramMatrix_vec
      T_set _hLin_smul _hLin_add _hLin_zero (hEIF := _hEIF)
  ----------------------------------------------------------------------------
  -- Inner per-(M, m): 8.11 form on the unbounded submodel, submodel functional.
  ----------------------------------------------------------------------------
  have hBdd_inner : ∀ (M : ℕ) (m : ℕ),
      ∫⁻ y : EuclideanSpace ℝ (Fin d), (ℓ y ⊓ (M : ℝ≥0∞))
          ∂(ProbabilityTheory.multivariateGaussian 0
              (ψDotMat_vec (g_P_m m) IF_eff
                * (ψDotMat_vec (g_P_m m) IF_eff).transpose))
        ≤ LHS_canonical_vec T_set T_n ψ (fun u => ℓ u ⊓ (M : ℝ≥0∞)) := by
    intro M m
    set g_P := g_P_m m with hgP_def
    have h_orth := h_orth_m m
    have h_basis_in := h_carrier m
    have h_lspan := h_linspan m
    -- ===== 8.11 hypothesis discharges. =====
    have h_gP_total_meas : Measurable
        (AsymptoticStatistics.ParametricFamily.g_P_total (g_P_m m)) := by
      unfold AsymptoticStatistics.ParametricFamily.g_P_total
      exact (WithLp.measurable_toLp 2 (Fin (n_m m) → ℝ)).comp
        (measurable_pi_iff.mpr
          (fun i => AsymptoticStatistics.ParametricFamily.gMk_meas (g_P_m m) i))
    have h_unbSub_hJ_fisher :
        ∀ u v : EuclideanSpace ℝ (Fin (n_m m)),
          AsymptoticStatistics.fisherInformation
              (AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel (g_P_m m) h_orth) P 0
              (AsymptoticStatistics.ParametricFamily.g_P_total (g_P_m m)) u v
            = @inner ℝ _ _ u
                ((WithLp.equiv 2 _).symm
                  ((1 : Matrix (Fin (n_m m)) (Fin (n_m m)) ℝ).mulVec
                    ((WithLp.equiv 2 _) v))) := by
      intro u v
      rw [AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel_fisher_info (g_P_m m) h_orth
          u v,
        Matrix.one_mulVec, Equiv.symm_apply_apply]
    have hT_param_meas : ∀ n,
        Measurable (T_param_of_vec T_n n) := by
      intro n
      unfold AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec.T_param_of_vec
      exact _hT_n n
    have hL_bowl : BowlShaped (fun u : EuclideanSpace ℝ (Fin d) => ℓ u ⊓ (M : ℝ≥0∞)) :=
      _hℓ_sub.truncate (M : ℝ≥0∞)
    have hL_lsc : LowerSemicontinuous
        (fun u : EuclideanSpace ℝ (Fin d) => ℓ u ⊓ (M : ℝ≥0∞)) := _hℓ_M_lsc M
    -- Derive `hTight` from the canonical vector `_hTight`.
    have hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel g_P h_orth) P
              (0 : EuclideanSpace ℝ (Fin (n_m m))) n).map
            (fun ω => (Real.sqrt n) •
              (T_param_of_vec T_n n ω
                - ψ_param_unb_vec g_P h_orth ψ
                    (0 : EuclideanSpace ℝ (Fin (n_m m))))))) := by
      have h_seq_eq :
          (fun n : ℕ =>
            (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
                (AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel g_P h_orth) P
                (0 : EuclideanSpace ℝ (Fin (n_m m))) n).map
              (fun ω => (Real.sqrt n) •
                (T_param_of_vec T_n n ω
                  - ψ_param_unb_vec g_P h_orth ψ
                      (0 : EuclideanSpace ℝ (Fin (n_m m))))))
          = (fun n : ℕ =>
            (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
              (fun ω => (Real.sqrt n) •
                (T_param_of_vec T_n n ω - ψ P))) := by
        funext n
        rw [productMeasure_unbounded_at_zero g_P h_orth n,
          ψ_param_unb_at_zero_vec g_P h_orth ψ]
      rw [h_seq_eq]
      exact _hTight
    -- Apply the per-direction-shift form of Theorem 8.11.
    have hParamLAM :=
      AsymptoticStatistics.LocalAsymptoticMinimax.local_asymptotic_minimax_bound_of_pointwise_shift
        (M := AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel g_P h_orth)
        (μ := P) (θ₀ := (0 : EuclideanSpace ℝ (Fin (n_m m))))
        (ℓ := AsymptoticStatistics.ParametricFamily.g_P_total g_P)
        (hℓ := h_gP_total_meas)
        (hDQM := AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel_DQM g_P h_orth)
        (J := (1 : Matrix (Fin (n_m m)) (Fin (n_m m)) ℝ))
        (hJ := Matrix.PosDef.one)
        (hJ_fisher := h_unbSub_hJ_fisher)
        (ψ := ψ_param_unb_vec g_P h_orth ψ)
        (ψDot := ψDot_proj_vec_clm g_P IF_eff)
        (hψ_shift := ψ_param_unb_pointwise_shift_vec T_set g_P h_orth h_lspan
          _hψ _hEIF)
        (ψDotMat := ψDotMat_vec g_P IF_eff)
        (h_ψDot_mat := fun h => ψDot_proj_vec_clm_apply g_P IF_eff h)
        (T := T_param_of_vec T_n)
        (hT_meas := hT_param_meas)
        (L := fun u : EuclideanSpace ℝ (Fin d) => ℓ u ⊓ (M : ℝ≥0∞))
        (hL_bowl := hL_bowl)
        (hL_lsc := hL_lsc)
        (hTight := hTight)
        (hPDF :=
          AsymptoticStatistics.ParametricFamily.unboundedParamSubmodel_isPDFOf g_P h_orth)
    -- Collapse the 8.11 form's matrix `ψDotMat·J⁻¹·ψDotMatᵀ` (with `J = 1`)
    -- to `ψDotMat·ψDotMatᵀ` (the goal/family matrix `Σ_m`).
    have h_Sig_eq :
        (ψDotMat_vec g_P IF_eff
            * (1 : Matrix (Fin (n_m m)) (Fin (n_m m)) ℝ)⁻¹
            * (ψDotMat_vec g_P IF_eff).transpose)
          = ψDotMat_vec g_P IF_eff * (ψDotMat_vec g_P IF_eff).transpose := by
      rw [inv_one, Matrix.mul_one]
    rw [h_Sig_eq] at hParamLAM
    -- Bridge: localAsymptoticRisk(unbounded) ≤ LHS_canonical_vec(ℓ_M).
    have h_bridge := unboundedLam_le_LHS_canonical_vec T_set g_P h_orth
      h_basis_in h_lspan T_n _hT_n ψ
      (fun u : EuclideanSpace ℝ (Fin d) => ℓ u ⊓ (M : ℝ≥0∞))
    -- Chain: ∫⁻ ℓ_M dN(0,Σ_m) ≤ localAsymptoticRisk ≤ LHS_canonical_vec(ℓ_M).
    exact le_trans hParamLAM h_bridge
  ----------------------------------------------------------------------------
  -- Outer Loewner (liminf-lsc / `m → ∞`) via the multivariate Gaussian lemma.
  ----------------------------------------------------------------------------
  have hBdd_lower_bound : ∀ M : ℕ,
      ∫⁻ y : EuclideanSpace ℝ (Fin d), (ℓ y ⊓ (M : ℝ≥0∞))
          ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff))
        ≤ LHS_canonical_vec T_set T_n ψ (fun u => ℓ u ⊓ (M : ℝ≥0∞)) := by
    intro M
    have h_liminf :
        ∫⁻ y : EuclideanSpace ℝ (Fin d), (ℓ y ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff))
          ≤ Filter.liminf (fun m => ∫⁻ y : EuclideanSpace ℝ (Fin d),
              (ℓ y ⊓ (M : ℝ≥0∞))
              ∂(ProbabilityTheory.multivariateGaussian 0
                  (ψDotMat_vec (g_P_m m) IF_eff
                    * (ψDotMat_vec (g_P_m m) IF_eff).transpose))) Filter.atTop :=
      AsymptoticStatistics.multivariateGaussian_lintegral_le_liminf_of_tendsto
        h_gram_psd h_Sig_psd h_Sig_tendsto (_hℓ_M_lsc M)
    refine le_trans h_liminf ?_
    -- The per-m inner bound `∫⁻ ℓ_M dN(0,Σ_m) ≤ LHS_canonical_vec(ℓ_M)` is
    -- constant in `m`, so `liminf_m (≤ const) ≤ const`. `liminf_le_of_le`'s
    -- second arg: for any lower bound `b` eventually-below the sequence, since
    -- the sequence is eventually ≤ the constant, `b ≤ const`.
    refine Filter.liminf_le_of_le ?_ ?_
    · exact ⟨0, Filter.Eventually.of_forall (fun _ => zero_le)⟩
    · intro b hb
      obtain ⟨m, hm⟩ := (hb.and (Filter.eventually_atTop.2 ⟨0, fun m _ => hBdd_inner M m⟩)).exists
      exact le_trans hm.1 hm.2
  ----------------------------------------------------------------------------
  -- Outer-2 (MCT / `ℓ_M ↑ ℓ`).
  ----------------------------------------------------------------------------
  have h_sup_eq : ∀ u : EuclideanSpace ℝ (Fin d),
      (⨆ M : ℕ, ℓ u ⊓ (M : ℝ≥0∞)) = ℓ u := by
    intro u
    have h_distrib : (⨆ M : ℕ, ℓ u ⊓ (M : ℝ≥0∞))
        = ℓ u ⊓ (⨆ M : ℕ, (M : ℝ≥0∞)) := (inf_iSup_eq _ _).symm
    rw [h_distrib, ENNReal.iSup_natCast]
    simp
  have h_mono : Monotone fun M : ℕ => fun u : EuclideanSpace ℝ (Fin d) =>
      ℓ u ⊓ (M : ℝ≥0∞) := by
    intro a b hab u
    have hcast : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hab
    exact inf_le_inf_left (ℓ u) hcast
  have h_meas : ∀ M : ℕ,
      Measurable (fun u : EuclideanSpace ℝ (Fin d) => ℓ u ⊓ (M : ℝ≥0∞)) := by
    intro M
    exact Measurable.min _hℓ_sub.measurable measurable_const
  have h_mct :
      ∫⁻ y : EuclideanSpace ℝ (Fin d), ℓ y
          ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff))
      = ⨆ M : ℕ, ∫⁻ y : EuclideanSpace ℝ (Fin d), (ℓ y ⊓ (M : ℝ≥0∞))
          ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff)) := by
    calc ∫⁻ y, ℓ y ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff))
        = ∫⁻ y, (⨆ M : ℕ, ℓ y ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff)) := by
          refine lintegral_congr (fun u => ?_)
          exact (h_sup_eq u).symm
      _ = ⨆ M : ℕ, ∫⁻ y, (ℓ y ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff)) :=
          MeasureTheory.lintegral_iSup h_meas h_mono
  have h_per_M : ∀ M : ℕ,
      ∫⁻ y : EuclideanSpace ℝ (Fin d), (ℓ y ⊓ (M : ℝ≥0∞))
          ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff))
        ≤ LHS_canonical_vec T_set T_n ψ ℓ := by
    intro M
    have h_le_full :
        LHS_canonical_vec T_set T_n ψ (fun u => ℓ u ⊓ (M : ℝ≥0∞))
          ≤ LHS_canonical_vec T_set T_n ψ ℓ :=
      LHS_canonical_vec_mono T_set T_n ψ (fun _ => inf_le_left)
    exact le_trans (hBdd_lower_bound M) h_le_full
  change LHS_canonical_vec T_set T_n ψ ℓ
      ≥ ∫⁻ y : EuclideanSpace ℝ (Fin d), ℓ y
          ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff))
  rw [ge_iff_le, h_mct]
  exact iSup_le h_per_M

end AsymptoticStatistics.LowerBounds.LAMSemiparametricUnbounded
