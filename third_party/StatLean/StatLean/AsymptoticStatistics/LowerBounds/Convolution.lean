module
public import StatLean.AsymptoticStatistics.LowerBounds.ProjSeqToEif
public import StatLean.AsymptoticStatistics.LowerBounds.FinDimSubmodel
public import StatLean.AsymptoticStatistics.LowerBounds.LeCamThirdAndCharFn
public import StatLean.AsymptoticStatistics.LowerBounds.ParametricBridge
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorDerivations
public import StatLean.AsymptoticStatistics.LowerBounds.ConvolutionUnbounded
public import StatLean.AsymptoticStatistics.Efficiency.HajekLeCamConvolution
public import StatLean.AsymptoticStatistics.ForMathlib.VarianceOfConvolution
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Semiparametric Convolution Theorem (scalar case)

Let $\psi : \mathcal{P} \to \mathbb{R}$ be a real-valued functional that is
differentiable at $P$ relative to the tangent set $\dot{\mathcal{P}}_P$, with
efficient influence function $\tilde\psi_P$. Consider any *regular* sequence of
estimators $T_n$ for $\psi(P)$, i.e. a sequence whose rescaled errors
$\sqrt{n}\,(T_n - \psi(P_n))$ converge in distribution to one and the same limit
law $L$ along every smooth one-dimensional submodel passing through $P$. The
headline theorem `semiparametric_convolution_theorem` proves the scalar
specialisation ($k = 1$) of the convolution theorem in two clauses:

* **Clause (a) — variance lower bound.** The asymptotic variance of every such
  regular sequence is bounded below by the squared norm of the efficient
  influence function,
  $$\operatorname{Var}(L) \;\ge\; \lVert \tilde\psi_P \rVert^2 ,$$
  which is the scalar form of the book's matrix lower bound
  $P\,\tilde\psi_P\,\tilde\psi_P^{\mathsf T}$ (the Loewner order collapsing to
  the usual order on $\mathbb{R}$ when $k = 1$). In the Lean statement the
  variance is written explicitly as $\int (x - \int y\,\mathrm{d}L)^2\,\mathrm{d}L$.
* **Clause (b) — convolution decomposition.** If in addition the tangent set
  $\dot{\mathcal{P}}_P$ is a convex cone, then every limit distribution $L$ of a
  regular sequence can be written as a convolution
  $$L \;=\; N\!\bigl(0,\ \lVert \tilde\psi_P \rVert^2\bigr) * M$$
  for some probability measure $M$. Thus the best attainable limit law is the
  Gaussian $N(0, \lVert\tilde\psi_P\rVert^2)$, and any regular estimator's limit
  is that Gaussian "smeared" by independent noise $M$.

*Deviations from the book statement.* The formalization fixes the scalar case
$k = 1$ (the book states the general $\mathbb{R}^k$ version with the asymptotic
covariance matrix and the Loewner order). Clause (a) additionally carries a
finite-second-moment hypothesis on $L$ (`hL_memLp`): the book's "asymptotic
covariance matrix" notation presupposes that the limit law has a finite second
moment, so the variance lower bound is otherwise vacuous. Clause (b) carries no
moment hypothesis, matching the book verbatim — the convolution decomposition is
well-defined for any limit law $L$ and the residual $M$ inherits whatever moments
$L$ has.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information),
Theorem 25.20.

**Proof formalization notes.**

Proof of (a). Approximate $\tilde\psi_P$ by its orthogonal projections $p_m$ onto
an increasing sequence of finite-dimensional subspaces $V_m \subseteq
\dot{\mathcal{P}}_P$ spanned by tangent directions. For each $m$, equip $V_m$ with
an orthonormal score basis; the per-$m$ joint covariance block
$\begin{psmallmatrix} \operatorname{Var}(L) & A_m \\ A_m^{\mathsf T} & I_m
\end{psmallmatrix}$ is positive semidefinite (a consequence of the parametric
submodel induced by the basis), so Schur's complement gives
$\sum_i \langle \tilde\psi_P, b_{m,i}\rangle^2 \le \operatorname{Var}(L)$. The
left-hand side equals $\lVert p_m\rVert^2$ by Parseval; passing to $m \to \infty$
using $\lVert p_m - \tilde\psi_P\rVert \to 0$ yields the bound. The Lean proof of
clause (a) actually bypasses the Schur extraction entirely: it specialises the
$m$-dimensional Hájek-style decomposition (from
`ConvolutionUnbounded.derived_convolution_decomp_unbounded` via the
`unboundedParamSubmodel` route) to $m = 1$ along each unit span direction
$b = \tilde\psi_P / \lVert\tilde\psi_P\rVert$, then applies
`ForMathlib.VarianceOfConvolution.variance_id_le_variance_id_conv` to conclude
$\operatorname{Var}(L) \ge \operatorname{Var}\bigl(N(0,\lVert\tilde\psi_P\rVert^2)\bigr)
= \lVert\tilde\psi_P\rVert^2$.

Proof of (b). Apply the per-$m$ parametric convolution theorem (vdV Theorem 8.8
restricted to the cone) to obtain $L = N(0, \sigma_m^2) * M_m$ for each $m$, with
$\sigma_m^2 \to \lVert\tilde\psi_P\rVert^2$ by Parseval. Lévy's continuity theorem
applied to the mixing-measure characteristic functions $\varphi_{M_m} \to
\varphi_M$ extracts a final mixing measure $M$ with
$L = N(0, \lVert\tilde\psi_P\rVert^2) * M$. The combined endpoint
`semiparametric_convolution_theorem` packages clauses (a) and (b); the two
standalone forms `semiparametric_convolution_theorem_clause_a` and
`semiparametric_convolution_theorem_clause_b`, and the variance-only corollary
`efficient_bound_is_asympVar_lowerBound`, expose each clause separately.

**Bibliographic comments.** The convolution theorem originates with J. Hájek,
"A characterization of limiting distributions of regular estimates,"
*Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete* **14** (1970),
323–330, where it is proved for parametric (locally asymptotically normal)
models — every regular estimator's limit law is a convolution of the optimal
Gaussian with an independent residual. The result is commonly called the
*Hájek–Le Cam convolution theorem*: L. Le Cam, "Limits of experiments,"
*Proc. Sixth Berkeley Symp. Math. Statist. Probab.* **1** (1972), 245–261,
recast and generalized it within his theory of limits of experiments
(see also Inagaki, *Ann. Inst. Statist. Math.* **22** (1970), 1–13, for an
independent contemporaneous derivation). The semiparametric formulation
formalized here — phrased in terms of a tangent set, the efficient influence
function, and the abstract convolution decomposition — follows van der Vaart's
Theorem 25.20, which lifts Hájek's parametric statement to infinite-dimensional
models via finite-dimensional submodel approximation.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal Matrix

namespace AsymptoticStatistics.LowerBounds.Convolution

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Theorem 25.20 clause (a) — variance lower bound (standalone).*

Clause-(a) projection of `semiparametric_convolution_theorem`, split out
as a separate theorem so that callers needing only the variance bound do
not pay the full `(a) ∧ (b)` package overhead. The signature carries
`hL_memLp`: vdV's "asymptotic covariance matrix" notation requires the
limit `L` to have finite 2nd moment for the bound to be non-vacuous.

Conclusion: `‖IF_eff‖² ≤ ∫ (x − ∫ y ∂L)² ∂L`.

The proof bypasses the heavy form's Schur extraction entirely. It
specialises the m-dim Hájek-style decomposition (provided by
`ConvolutionUnbounded.derived_convolution_decomp_unbounded` via the
`unboundedParamSubmodel` route) to `m = 1` with
`g_P 0 := IF_eff / ‖IF_eff‖`, then applies
`ForMathlib.VarianceOfConvolution.variance_id_le_variance_id_conv` to
conclude `Var L ≥ Var (N(0, ‖IF_eff‖²)) = ‖IF_eff‖²`. No block-PSD /
no Schur / no `hCovBlockPSD` needed: the Schur machinery
(`hCovBlockPSDAll_of_isRegular`) is exclusively for building the heavy
form's `_hCovBlockPSD` input, which clause (a) bypasses.

Reference: vdV §25.3 clause (a). -/
theorem semiparametric_convolution_theorem_clause_a
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L)
    (hL_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2 L) :
    ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 ≤ (∫ x, (x - ∫ y, y ∂L)^2 ∂L) := by
  -- Step 1: derive `hRegular` (per-`m` Hájek-style decomposition)
  -- via the `unboundedParamSubmodel` route.
  have hRegular : ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
      Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
      (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) →
      ∃ M_per : Measure ℝ, IsProbabilityMeasure M_per ∧
        L =
          MeasureTheory.Measure.conv
            (ProbabilityTheory.gaussianReal 0
              ⟨∑ i : Fin m,
                  (⟪(IF_eff : ↥(L2ZeroMean P)),
                    (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) M_per :=
    AsymptoticStatistics.LowerBounds.ConvolutionUnbounded.derived_convolution_decomp_unbounded
      T_set hψ hEIF T_n hT_meas L hReg
  -- Step 2: variance lower bound via `m = 1` specialisation.
  have h_var_eq : ProbabilityTheory.variance (id : ℝ → ℝ) L =
      ∫ x, (x - ∫ y, y ∂L)^2 ∂L := by
    rw [ProbabilityTheory.variance_eq_integral (by fun_prop)]
    simp
  rw [← h_var_eq]
  by_cases h_zero : (IF_eff : ↥(L2ZeroMean P)) = 0
  · have h_norm_zero : ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 = 0 := by
      rw [h_zero]; simp
    rw [h_norm_zero]
    exact ProbabilityTheory.variance_nonneg _ _
  · -- `IF_eff ≠ 0`. Following vdV §25.3.2 (p.366), regularity is invoked only on
    -- finite algebraic-span directions; the efficient influence function, which
    -- lies in the *closed* span, is reached by a limit. We bound `⟪IF_eff, b⟫²`
    -- for every unit direction `b ∈ Submodule.span ℝ T_set.carrier`, then let `b`
    -- run along a span sequence approximating `‖IF_eff‖⁻¹ • IF_eff`.
    have h_norm_pos : 0 < ‖(IF_eff : ↥(L2ZeroMean P))‖ :=
      norm_pos_iff.mpr h_zero
    have h_norm_ne : ‖(IF_eff : ↥(L2ZeroMean P))‖ ≠ 0 := h_norm_pos.ne'
    -- Per-direction bound, via the one-dimensional submodel along the unit span
    -- direction `b` (the *only* place regularity is invoked).
    have key : ∀ b : ↥(L2ZeroMean P),
        b ∈ Submodule.span ℝ T_set.carrier →
        ‖(b : ↥(L2ZeroMean P))‖ = 1 →
        (⟪(IF_eff : ↥(L2ZeroMean P)), (b : ↥(L2ZeroMean P))⟫_ℝ) ^ 2 ≤
          ProbabilityTheory.variance (id : ℝ → ℝ) L := by
      intro b hb_span hb_norm
      let g_P : Fin 1 → ↥(L2ZeroMean P) := fun _ => b
      have h_orth : Orthonormal ℝ
          (fun i : Fin 1 => (g_P i : ↥(L2ZeroMean P))) := by
        refine ⟨fun _ => hb_norm, ?_⟩
        intro i j hij
        exact (hij (Subsingleton.elim i j)).elim
      have h_in_T : ∀ i,
          (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier :=
        fun _ => hb_span
      have h_sum :
          (∑ i : Fin 1,
              (⟪(IF_eff : ↥(L2ZeroMean P)),
                (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2) =
            (⟪(IF_eff : ↥(L2ZeroMean P)), (b : ↥(L2ZeroMean P))⟫_ℝ) ^ 2 := by
        rw [Fin.sum_univ_one]
      obtain ⟨M_1, hM_prob, hL_eq⟩ := hRegular g_P h_orth h_in_T
      -- Port note: the subtype-typed `⟨x, h⟩` variance is not seen through by instance search.
      haveI : IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0
          ⟨∑ i : Fin 1, (⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
            Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) :=
        inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 (NNReal.mk _ _)))
      have h_var_gauss :
          ProbabilityTheory.variance (id : ℝ → ℝ)
              (ProbabilityTheory.gaussianReal 0
                ⟨∑ i : Fin 1,
                    (⟪(IF_eff : ↥(L2ZeroMean P)),
                      (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                  Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) =
            (⟪(IF_eff : ↥(L2ZeroMean P)), (b : ↥(L2ZeroMean P))⟫_ℝ) ^ 2 := by
        exact ProbabilityTheory.variance_id_gaussianReal.trans h_sum
      have hL_memLp_conv :
          MeasureTheory.MemLp (id : ℝ → ℝ) 2
              ((ProbabilityTheory.gaussianReal 0
                ⟨∑ i : Fin 1,
                    (⟪(IF_eff : ↥(L2ZeroMean P)),
                      (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                  Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) ∗ M_1) := by
        rw [← hL_eq]; exact hL_memLp
      have h_var_le :
          ProbabilityTheory.variance (id : ℝ → ℝ)
              (ProbabilityTheory.gaussianReal 0
                ⟨∑ i : Fin 1,
                    (⟪(IF_eff : ↥(L2ZeroMean P)),
                      (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                  Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) ≤
            ProbabilityTheory.variance (id : ℝ → ℝ)
              ((ProbabilityTheory.gaussianReal 0
                ⟨∑ i : Fin 1,
                    (⟪(IF_eff : ↥(L2ZeroMean P)),
                      (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                  Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) ∗ M_1) :=
        AsymptoticStatistics.ForMathlib.VarianceOfConvolution.variance_id_le_variance_id_conv
          _ M_1 (ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp))
          hL_memLp_conv
      calc (⟪(IF_eff : ↥(L2ZeroMean P)), (b : ↥(L2ZeroMean P))⟫_ℝ) ^ 2
          = ProbabilityTheory.variance (id : ℝ → ℝ)
              (ProbabilityTheory.gaussianReal 0
                ⟨∑ i : Fin 1,
                    (⟪(IF_eff : ↥(L2ZeroMean P)),
                      (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                  Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) := h_var_gauss.symm
        _ ≤ ProbabilityTheory.variance (id : ℝ → ℝ)
              ((ProbabilityTheory.gaussianReal 0
                ⟨∑ i : Fin 1,
                    (⟪(IF_eff : ↥(L2ZeroMean P)),
                      (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                  Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) ∗ M_1) := h_var_le
        _ = ProbabilityTheory.variance (id : ℝ → ℝ) L := by rw [← hL_eq]
    -- Approximate `IF_eff` by a sequence `a n ∈ span carrier`, normalize to unit
    -- directions, apply `key`, and pass `⟪IF_eff, ·⟫² ≤ Var(L)` to the limit.
    obtain ⟨a, ha_span, ha_tend⟩ :=
      AsymptoticStatistics.Core.TangentAbstract.exists_seq_span_tendsto_of_mem_tangentSpace
        T_set hEIF.2
    have ha_norm :
        Filter.Tendsto (fun n => ‖a n‖) Filter.atTop
          (nhds ‖(IF_eff : ↥(L2ZeroMean P))‖) := ha_tend.norm
    have ha_inner :
        Filter.Tendsto (fun n => ⟪(IF_eff : ↥(L2ZeroMean P)), a n⟫_ℝ)
          Filter.atTop (nhds (‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2)) := by
      have h : Filter.Tendsto (fun n => ⟪(IF_eff : ↥(L2ZeroMean P)), a n⟫_ℝ)
          Filter.atTop (nhds (⟪(IF_eff : ↥(L2ZeroMean P)),
            (IF_eff : ↥(L2ZeroMean P))⟫_ℝ)) :=
        (tendsto_const_nhds (x := (IF_eff : ↥(L2ZeroMean P)))).inner ha_tend
      rwa [real_inner_self_eq_norm_sq] at h
    have hu_inner :
        Filter.Tendsto (fun n => ⟪(IF_eff : ↥(L2ZeroMean P)), ‖a n‖⁻¹ • a n⟫_ℝ)
          Filter.atTop (nhds ‖(IF_eff : ↥(L2ZeroMean P))‖) := by
      have hinv : Filter.Tendsto (fun n => ‖a n‖⁻¹) Filter.atTop
          (nhds ‖(IF_eff : ↥(L2ZeroMean P))‖⁻¹) := ha_norm.inv₀ h_norm_ne
      have hmul := hinv.mul ha_inner
      have h_simp : ‖(IF_eff : ↥(L2ZeroMean P))‖⁻¹ *
          ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 = ‖(IF_eff : ↥(L2ZeroMean P))‖ := by
        rw [pow_two, ← mul_assoc, inv_mul_cancel₀ h_norm_ne, one_mul]
      rw [h_simp] at hmul
      exact Filter.Tendsto.congr (fun n => (real_inner_smul_right _ _ _).symm) hmul
    have hu_sq :
        Filter.Tendsto (fun n => (⟪(IF_eff : ↥(L2ZeroMean P)), ‖a n‖⁻¹ • a n⟫_ℝ) ^ 2)
          Filter.atTop (nhds (‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2)) := hu_inner.pow 2
    have h_event : ∀ᶠ n in Filter.atTop,
        (⟪(IF_eff : ↥(L2ZeroMean P)), ‖a n‖⁻¹ • a n⟫_ℝ) ^ 2 ≤
          ProbabilityTheory.variance (id : ℝ → ℝ) L := by
      have h_pos : ∀ᶠ n in Filter.atTop, 0 < ‖a n‖ :=
        ha_norm.eventually (lt_mem_nhds h_norm_pos)
      filter_upwards [h_pos] with n hn
      refine key (‖a n‖⁻¹ • a n) (Submodule.smul_mem _ _ (ha_span n)) ?_
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn]
      exact inv_mul_cancel₀ hn.ne'
    exact le_of_tendsto hu_sq h_event

/-- *Theorem 25.20 clause (b) — convolution decomposition (standalone).*

Clause-(b) projection of `semiparametric_convolution_theorem`, split out
as a separate theorem **without** `hL_memLp` and **without** an external
`hWeak`. vdV §25.3 clause (b) verbatim — *"if 𝒫̇_P is a convex cone, then
every limit distribution L of a regular sequence of estimators can be
written `L = N(0, P ψ̃_P ψ̃_Pᵀ) ⋆ M` for some probability distribution
M"* — imposes **no** finite-2nd-moment condition on `L`; the
convolution decomposition is well-defined for arbitrary `L` and the
residual `M` inherits whatever moments `L` has.

Conclusion: under convex-cone proviso on `T_set.carrier`,
`∃ M, L = N(0, ‖IF_eff‖²) ⋆ M`.

The body derives `hRegular` (per-`m` Hájek-style decomposition) via
`ConvolutionUnbounded.derived_convolution_decomp_unbounded` and the
unperturbed weak limit `hWeak` via
`RegularEstimator.weak_limit_under_P_of_regular`, then inlines the
heavy-form Step 1 (basis projection sequence + per-`m` Parseval) and
Step 3 (per-`m` `ParametricBridge.perMConvDecomp` followed by the
Lévy-continuity m-pass `ParametricBridge.levyMpass`). Step 2 (Schur
extraction) is skipped entirely: that is clause (a)'s territory, not
clause (b)'s.

Reference: vdV §25.3 clause (b). -/
theorem semiparametric_convolution_theorem_clause_b
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L) :
    (∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t → t • x ∈ T_set.carrier) →
    (∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
        ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        a • x + b • y ∈ T_set.carrier) →
    let sigma_sq : ℝ≥0 :=
      ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩
    ∃ M : Measure ℝ, IsProbabilityMeasure M ∧
      L = MeasureTheory.Measure.conv
              (ProbabilityTheory.gaussianReal 0 sigma_sq) M := by
  classical
  -- Step 0a: derive the universal-`m` Hájek decomposition `hRegular`
  -- via the `unboundedParamSubmodel` route.
  have hRegular : ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
      Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
      (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) →
      ∃ M_per : Measure ℝ, IsProbabilityMeasure M_per ∧
        L =
          MeasureTheory.Measure.conv
            (ProbabilityTheory.gaussianReal 0
              ⟨∑ i : Fin m,
                  (⟪(IF_eff : ↥(L2ZeroMean P)),
                    (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) M_per :=
    AsymptoticStatistics.LowerBounds.ConvolutionUnbounded.derived_convolution_decomp_unbounded
      T_set hψ hEIF T_n hT_meas L hReg
  -- Step 0b: derive the unperturbed weak limit `hWeak`.
  have hWeak : WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P))) L :=
    AsymptoticStatistics.LowerBounds.RegularEstimator.weak_limit_under_P_of_regular
      T_set ψ hψ hEIF T_n L hReg
  -- Extract `IF_eff ∈ tangentSpace T_set` from the EIF data.
  have h_mem : (IF_eff : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := hEIF.2
  -- Step 1a: build the projection sequence + norm-sq convergence.
  obtain ⟨V, p, hV_le, _hV_inc, hV_findim, hV_span,
            hp_proj, h_p_tendsto⟩ :=
    AsymptoticStatistics.LowerBounds.ProjSeqToEif.proj_seq_to_eif T_set h_mem
  haveI hUG_L2 : IsUniformAddGroup ↥(L2ZeroMean P) :=
    (L2ZeroMean P).toAddSubgroup.isUniformAddGroup
  have h_p_norm_sq_tendsto :
      Tendsto (fun m : ℕ => ‖p m‖ ^ 2) atTop
        (𝓝 (‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2)) := by
    have h_p_tendsto_to : Tendsto (fun m : ℕ => p m) atTop
        (𝓝 (IF_eff : ↥(L2ZeroMean P))) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr h_p_tendsto
    have h_norm_tendsto :
        Tendsto (fun m : ℕ => ‖p m‖) atTop
          (𝓝 ‖(IF_eff : ↥(L2ZeroMean P))‖) :=
      (continuous_norm.tendsto _).comp h_p_tendsto_to
    exact (continuous_pow 2).tendsto _ |>.comp h_norm_tendsto
  -- Step 1b: per-`m` orthonormal basis + Parseval for `‖p m‖²`.
  have h_basis_data :
      ∀ m, ∃ (n_m : ℕ) (g_P_m : Fin n_m → ↥(L2ZeroMean P)),
        Orthonormal ℝ (fun i : Fin n_m => (g_P_m i : ↥(L2ZeroMean P))) ∧
        (∀ i, (g_P_m i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) ∧
        ‖p m‖ ^ 2 =
          ∑ i : Fin n_m,
            (⟪(IF_eff : ↥(L2ZeroMean P)),
              (g_P_m i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2 := by
    intro m
    haveI := hV_findim m
    let b : OrthonormalBasis (Fin (Module.finrank ℝ ↥(V m))) ℝ ↥(V m) :=
      stdOrthonormalBasis ℝ ↥(V m)
    let g_P : Fin (Module.finrank ℝ ↥(V m)) → ↥(L2ZeroMean P) :=
      fun i => (b i : ↥(L2ZeroMean P))
    have hg_orth : Orthonormal ℝ
        (fun i : Fin (Module.finrank ℝ ↥(V m)) =>
          (g_P i : ↥(L2ZeroMean P))) := by
      have hb := b.orthonormal
      simpa [g_P, Function.comp] using!
        ((V m).subtypeₗᵢ.orthonormal_comp_iff).mpr hb
    have hg_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier := by
      intro i
      obtain ⟨S, hS_sub, hV_eq⟩ := hV_span m
      have hgi : (g_P i : ↥(L2ZeroMean P)) ∈ V m := (b i).2
      rw [hV_eq] at hgi
      exact Submodule.span_mono hS_sub hgi
    have h_norm_sq :
        ‖p m‖ ^ 2 =
          ∑ i : Fin (Module.finrank ℝ ↥(V m)),
            (⟪(IF_eff : ↥(L2ZeroMean P)),
              (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2 := by
      have hp_in : p m ∈ V m := (hp_proj m).1
      let q : ↥(V m) := ⟨p m, hp_in⟩
      have h_norm_q : ‖q‖ = ‖p m‖ := rfl
      have h_parseval : ‖q‖ ^ 2 =
          ∑ i : Fin (Module.finrank ℝ ↥(V m)),
            ‖⟪(b i : ↥(V m)), q⟫_ℝ‖ ^ 2 :=
        b.sum_sq_norm_inner_right q |>.symm
      have h_inner_eq : ∀ i : Fin (Module.finrank ℝ ↥(V m)),
          (⟪(b i : ↥(V m)), q⟫_ℝ : ℝ) =
            ⟪(g_P i : ↥(L2ZeroMean P)),
              (p m : ↥(L2ZeroMean P))⟫_ℝ := by
        intro i; rfl
      have h_resid : ∀ i : Fin (Module.finrank ℝ ↥(V m)),
          ⟪(g_P i : ↥(L2ZeroMean P)),
              (IF_eff : ↥(L2ZeroMean P)) - p m⟫_ℝ = 0 := by
        intro i
        have h_perp := (hp_proj m).2
        have hgi_in : (g_P i : ↥(L2ZeroMean P)) ∈ V m := (b i).2
        exact (Submodule.mem_orthogonal _ _).mp h_perp _ hgi_in
      have h_inner_match : ∀ i : Fin (Module.finrank ℝ ↥(V m)),
          ⟪(g_P i : ↥(L2ZeroMean P)),
              (p m : ↥(L2ZeroMean P))⟫_ℝ =
            ⟪(g_P i : ↥(L2ZeroMean P)),
              (IF_eff : ↥(L2ZeroMean P))⟫_ℝ := by
        intro i
        have := h_resid i
        rw [inner_sub_right, sub_eq_zero] at this
        exact this.symm
      have h_swap : ∀ i : Fin (Module.finrank ℝ ↥(V m)),
          ⟪(g_P i : ↥(L2ZeroMean P)),
              (IF_eff : ↥(L2ZeroMean P))⟫_ℝ =
            ⟪(IF_eff : ↥(L2ZeroMean P)),
              (g_P i : ↥(L2ZeroMean P))⟫_ℝ := by
        intro i; exact real_inner_comm _ _
      calc ‖p m‖ ^ 2 = ‖q‖ ^ 2 := by rw [h_norm_q]
        _ = ∑ i : Fin (Module.finrank ℝ ↥(V m)),
              ‖⟪(b i : ↥(V m)), q⟫_ℝ‖ ^ 2 := h_parseval
        _ = ∑ i : Fin (Module.finrank ℝ ↥(V m)),
              ‖⟪(g_P i : ↥(L2ZeroMean P)),
                  (p m : ↥(L2ZeroMean P))⟫_ℝ‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [h_inner_eq i]
        _ = ∑ i : Fin (Module.finrank ℝ ↥(V m)),
              ‖⟪(g_P i : ↥(L2ZeroMean P)),
                  (IF_eff : ↥(L2ZeroMean P))⟫_ℝ‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [h_inner_match i]
        _ = ∑ i : Fin (Module.finrank ℝ ↥(V m)),
              ‖⟪(IF_eff : ↥(L2ZeroMean P)),
                  (g_P i : ↥(L2ZeroMean P))⟫_ℝ‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [h_swap i]
        _ = ∑ i : Fin (Module.finrank ℝ ↥(V m)),
              (⟪(IF_eff : ↥(L2ZeroMean P)),
                  (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Real.norm_eq_abs, sq_abs]
    exact ⟨Module.finrank ℝ ↥(V m), g_P, hg_orth, hg_in_T, h_norm_sq⟩
  choose n_m g_P_m h_orth_m h_in_m h_parseval_m using h_basis_data
  -- Step 3: clause (b) — per-`m` `perMConvDecomp` + Lévy m-pass.
  intro h_cone h_convex
  let sigma_sq_m : ℕ → ℝ≥0 := fun m =>
    ⟨∑ i : Fin (n_m m),
        (⟪(IF_eff : ↥(L2ZeroMean P)),
          (g_P_m m i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩
  have hBridge :=
    AsymptoticStatistics.LowerBounds.ParametricBridge.perMConvDecomp
      T_set hψ hEIF T_n L hWeak hRegular
  have h_perM_decomp : ∀ m, ∃ M : Measure ℝ, IsProbabilityMeasure M ∧
      L = MeasureTheory.Measure.conv
              (ProbabilityTheory.gaussianReal 0 (sigma_sq_m m)) M := by
    intro m
    exact hBridge h_cone h_convex (g_P_m m) (h_orth_m m) (h_in_m m)
  choose M_m hM_prob hM_decomp using h_perM_decomp
  have h_sigma_eq : ∀ m, ((sigma_sq_m m : ℝ≥0) : ℝ) = ‖p m‖ ^ 2 := by
    intro m
    change (⟨_, _⟩ : ℝ≥0).val = _
    exact (h_parseval_m m).symm
  have h_sigma_tendsto :
      Tendsto (fun m => ((sigma_sq_m m : ℝ≥0) : ℝ)) atTop
        (𝓝 (‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2)) := by
    have heq : (fun m => ((sigma_sq_m m : ℝ≥0) : ℝ)) =
        (fun m => ‖p m‖ ^ 2) := by
      funext m; exact h_sigma_eq m
    rw [heq]
    exact h_p_norm_sq_tendsto
  exact AsymptoticStatistics.LowerBounds.ParametricBridge.levyMpass
    (IF_eff := IF_eff) L M_m hM_prob sigma_sq_m hM_decomp
    h_sigma_tendsto

/-- *Theorem 25.20: scalar convolution theorem (combined `(a) ∧ (b)`
package, canonical user-facing endpoint).*

The canonical combined-form `(a) ∧ (b)` package. The body delegates to
the two per-clause forms `semiparametric_convolution_theorem_clause_a`
(clause (a) variance bound, carries `hL_memLp`) and
`semiparametric_convolution_theorem_clause_b` (clause (b) convolution
decomposition under convex cone, **no** `hL_memLp`).

Callers needing only one clause should target the corresponding
per-clause theorem directly:

- For only the variance bound `‖IF_eff‖² ≤ Var L`, use
  `semiparametric_convolution_theorem_clause_a` (same signature minus the
  convex-cone conjunct in the conclusion).
- For only the convolution decomposition `L = N(0, ‖IF_eff‖²) ⋆ M`
  under the convex-cone proviso, use
  `semiparametric_convolution_theorem_clause_b`, which drops `hL_memLp`:
  vdV (b) does not require finite 2nd moment of `L`.

The combined form's `hL_memLp` is genuinely required for the
(a)-component of the conjunction this package delivers.

Reference: vdV §25.3. -/
theorem semiparametric_convolution_theorem
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L)
    (hL_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2 L) :
    -- Clause (a) variance lower bound:
    ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 ≤ (∫ x, (x - ∫ y, y ∂L)^2 ∂L) ∧
    -- Clause (b) convolution decomposition under convex cone:
    ((∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t → t • x ∈ T_set.carrier) →
     (∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
        ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        a • x + b • y ∈ T_set.carrier) →
     let sigma_sq : ℝ≥0 :=
       ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩
     ∃ M : Measure ℝ, IsProbabilityMeasure M ∧
       L = MeasureTheory.Measure.conv
              (ProbabilityTheory.gaussianReal 0 sigma_sq) M) :=
  ⟨semiparametric_convolution_theorem_clause_a T_set hψ hEIF T_n hT_meas L hReg hL_memLp,
   fun h_cone h_convex =>
     semiparametric_convolution_theorem_clause_b T_set hψ hEIF T_n hT_meas L hReg h_cone h_convex⟩

/-- *Variance lower bound corollary of the canonical
`semiparametric_convolution_theorem`.*

Directly invokes `semiparametric_convolution_theorem_clause_a` (the
variance-bound-only form), skipping the `.1`-projection through the
combined-form package. `hL_memLp` is the second-moment regularity
required by the variance lower bound. -/
theorem efficient_bound_is_asympVar_lowerBound
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L)
    (hL_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2 L) :
    ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 ≤
        (∫ x, (x - ∫ y, y ∂L)^2 ∂L) :=
  semiparametric_convolution_theorem_clause_a T_set hψ hEIF T_n hT_meas L hReg hL_memLp

end AsymptoticStatistics.LowerBounds.Convolution
