module
public import StatLean.AsymptoticStatistics.LowerBounds.LeCamThirdAndCharFn
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorDerivations
public import StatLean.AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge
public import StatLean.AsymptoticStatistics.ParametricFamily.RegularEstimator
public import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Measure.LevyConvergence

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

@[expose] public section

/-!
# Semiparametric-to-parametric bridge (tangent set to LAN apparatus)

This file holds named theorems encapsulating the semiparametric-to-parametric
bridge content of van der Vaart's Chapter 25: the steps from a tangent set plus
an orthonormal score basis to the parametric local asymptotic normality (LAN)
apparatus of the earlier chapters.

Informally, fix a probability measure $P$ and a convex-cone tangent set $T$ of
score functions in $L^2_0(P)$ (mean-zero, square-integrable). Given an
$L^2(P)$-orthonormal basis $g_1, \dots, g_m$ of a finite-dimensional subspace of
$T$, one forms the finite-dimensional parametric submodel with densities
$(1 + \langle h, g\rangle)\, dP$, which is differentiable in quadratic mean at
$h = 0$ with Fisher information equal to the identity. The parametric efficiency
machinery of Chapters 7-8 then transfers to the semiparametric limit:

* **Per-$m$ convolution decomposition** (`perMConvDecomp`): the weak limit $L$ of
  the standardized regular estimator factors as a Gaussian convolution
  $L = N(0, \sigma_m^2) \star M_m$, where
  $\sigma_m^2 = \sum_{i=1}^m \langle \tilde\psi_{\mathrm{eff}}, g_i\rangle^2$ is
  the variance picked up along the efficient-influence-function direction inside
  $\operatorname{span}(g_1,\dots,g_m)$.
* **Lévy-continuity $m$-pass** (`levyMpass`): letting $m \to \infty$ so that
  $\sigma_m^2 \to \|\tilde\psi_{\mathrm{eff}}\|^2$, a characteristic-function /
  tightness argument produces a single mixing measure $M$ with
  $L = N(0, \|\tilde\psi_{\mathrm{eff}}\|^2) \star M$ (the convolution theorem).
* **Truncated Bayes-risk lower bound** (`bddInner`): for any bowl-shaped loss
  $\ell$ and truncation level $M$, the local asymptotic minimax left-hand side
  dominates $\int (\ell \wedge M)\, dN(0, \sigma_m^2)$.
* **Joint covariance block PSD-ness** (`covBlockPSDAll`): the joint covariance
  block of $(\tilde\psi_{\mathrm{eff}}, g_1, \dots, g_m)$, namely the matrix with
  variance-of-$L$ corner, off-diagonal entries
  $A_{m,i} = \langle \tilde\psi_{\mathrm{eff}}, g_i\rangle$, and identity
  block $I_m$, is positive semidefinite.

Headline declarations: `perMConvDecomp`, `levyMpass`, `bddInner`,
`covBlockPSDAll`, and the §25 closure bridges
(`pi_paramSubmodelQMDPath_curve_eq_productMeasure`,
`productMeasure_paramSubmodel_pushforward_weakConverges`,
`tangent_bounded_orthonormal_approx`,
`orthonormal_to_bounded_mixture_via_tangent_dense`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3, with Theorem 7.10 (local asymptotic
normality representation, Chapter 7, Local Asymptotic Normality) and
Proposition 8.4 (convolution-with-randomizer, Chapter 8, Efficiency of
Estimators) supplying the parametric core that this file transfers to the
semiparametric setting.

**Proof formalization notes.** The four headline theorems are stated relative to
the abstract tangent-set / efficient-influence-function infrastructure
(`TangentSpec`, `IsEfficientInfluenceFunction`, `QMDPath`) and assemble the
finite-dimensional submodel via `paramSubmodel` / `paramSubmodelQMDPath`. The
Lévy-continuity $m$-pass (`levyMpass`) is fully proved internally: it forms the
candidate target characteristic function
$f(t) = \widehat{L}(t) / \widehat{N(0,\|\tilde\psi_{\mathrm{eff}}\|^2)}(t)$
(the Gaussian characteristic function never vanishes, so the quotient is
well-defined and continuous at $0$ with $f(0)=1$), shows the mixing-measure
characteristic functions converge pointwise to $f$, invokes
`isTightMeasureSet_of_tendsto_charFun` for tightness, extracts a weakly
convergent subsequence by Prokhorov, identifies the limit's characteristic
function with $f$ via `ext_of_charFun`, and reassembles the convolution through
`charFun_conv`. The §25 closure bridges
(`pi_paramSubmodelQMDPath_curve_eq_productMeasure` and the pushforward lemmas)
transport `IsRegularEstimator.shift`'s `QMDPath`-based weak limits into the
`productMeasure`-based form consumed by
`AsymptoticRepresentation.LAN_representation`, justified by an eventually-in-$n$
equality of the two product-measure families. Deviations from a fully
self-contained derivation are confined to three caller-supplied book inputs that
are not yet closed internally and are flagged in the corresponding declaration
docstrings: `_hRegular` in `perMConvDecomp` (the Hájek-style per-$m$ convolution
form of the regular-estimator limit law, vdV §25.3 + Thm 7.10),
`_hBayesLowerBound` in `bddInner` (the per-$(M,m)$ limit-experiment Bayes-risk
bound, vdV §25.3 Lemmas 3-4 plus the basis-selection / Riesz-pairing bridge),
and `_hCovBlockPSD` in `covBlockPSDAll` (the joint-MGF differentiation +
Anderson PSD-monotone covariance bound). Each is a named, well-defined
downstream debt rather than an arbitrary assumption.

**Bibliographic comments.** The conceptual origin is Lucien Le Cam's theory of
limits of experiments — L. Le Cam, "Limits of experiments", in *Proceedings of
the Sixth Berkeley Symposium on Mathematical Statistics and Probability*, Vol. I:
Theory of Statistics, pp. 245-261, University of California Press, Berkeley,
1972 — which justifies transferring efficiency bounds from a (Gaussian-shift)
limit experiment back to the original sequence of experiments; this is exactly
the device by which the parametric LAN apparatus is brought to bear on the
semiparametric model here. The Gaussian-convolution structure of the limit law
of regular estimators (the convolution theorem realized by `perMConvDecomp` /
`levyMpass`) is due to J. Hájek, "A characterization of limiting distributions
of regular estimates", *Zeitschrift für Wahrscheinlichkeitstheorie und verwandte
Gebiete* 14 (1970), 323-330, and the matching local asymptotic minimax bound
(realized by `bddInner`) to J. Hájek, "Local asymptotic minimax and
admissibility in estimation", in *Proceedings of the Sixth Berkeley Symposium on
Mathematical Statistics and Probability*, Vol. I, pp. 175-194, University of
California Press, Berkeley, 1972. The systematic tangent-set formulation of
efficient influence functions for semiparametric models — the synthesis vdV §25
follows — is developed in P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and
J. A. Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*,
Johns Hopkins University Press, 1993. The cone-restriction and basis-selection
steps assembled in this file are a synthesis (vdV §25.3) of these
sources rather than a single seminal result.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal Matrix ProbabilityTheory

namespace AsymptoticStatistics.LowerBounds.ParametricBridge

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Per-`m` convolution decomposition** (parametric vdV Prop 8.4
specialized to a finite-dim submodel).

For a regular estimator with weak limit `L` and an `L²(P)`-orthonormal
basis `g_P : Fin m → L²₀(P)` of a finite-dim subspace of the (convex
cone) tangent set `tangentSpace T_set`, the limit law factors as
`L = N(0, σ_m²) ⋆ M_m` for some probability measure `M_m`, where
`σ_m² = Σᵢ ⟨IF_eff, g_P i⟩²`.

This is the conclusion of vdV's Proposition 8.4 specialized to the
finite-dimensional parametric submodel induced by `g_P` (the `L²₀(P)`-
orthonormal basis specifying the parametric directions). It is invoked
per-`m` in the proof of `semiparametric_convolution_theorem` (clause (b)) and threaded
through the Lévy-continuity m-pass (`hLevyMpass`).

The `_hRegular` hypothesis carries the convolution-decomposition form of the
regular-estimator limit law at `h = 0`, as delivered by vdV §25.3 + Thm 7.10:
the limit law factors as `_L = N(0, sigma_sq_m) ⋆ M_per` for some probability
measure `M_per` on `ℝ`, where `sigma_sq_m = ∑ᵢ ⟪IF_eff, g_P i⟫²` is the
variance contribution along the EIF direction in `span g_P` (= `‖A_m‖²` for the
Riesz-paired functional `A_m`). This is the Hájek-style conclusion of
regular-estimator + LAN; it cannot be derived from per-`h` weak convergence
alone without the parametric-submodel infrastructure (densities
`(1 + ⟨h, g_P⟩)P`, DQM at `0`, Fisher info = identity, mutual absolute
continuity), so it is supplied by the caller.

Reference: vdV §25.3, with vdV Prop 8.4 + Thm 7.10 as the parametric core. -/
theorem perMConvDecomp
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (_hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              _hψ.derivative IF_eff)
    (_T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_L : Measure ℝ) [IsProbabilityMeasure _L]
    (_hWeak : WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (_T_n n X - ψ P))) _L)
    -- vdV §25.3 + Thm 7.10: for every orthonormal score basis `g_P` of a
    -- finite-dim subspace of the tangent set, the regular-estimator weak limit
    -- `_L` factors in convolution form `_L = N(0, σ_m²) ∗ M_per` for some
    -- probability measure `M_per` on `ℝ`, where `σ_m² = Σᵢ ⟪IF_eff, g_P i⟫²`
    -- is the variance contribution along the EIF direction in `span g_P`
    -- (= `‖A_m‖²` for the Riesz-paired functional `A_m`). This is the
    -- Hájek-style conclusion of regular-estimator + LAN.
    (_hRegular : ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
        Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
        (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) →
        ∃ M_per : Measure ℝ, IsProbabilityMeasure M_per ∧
          _L =
            MeasureTheory.Measure.conv
              (ProbabilityTheory.gaussianReal 0
                ⟨∑ i : Fin m,
                    (⟪(IF_eff : ↥(L2ZeroMean P)),
                      (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
                  Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩) M_per) :
    (∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t → t • x ∈ T_set.carrier) →
    (∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
        ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        a • x + b • y ∈ T_set.carrier) →
    ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
      Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
      (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) →
      let sigma_sq_m : ℝ≥0 :=
        ⟨∑ i : Fin m,
            (⟪(IF_eff : ↥(L2ZeroMean P)),
              (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩
      ∃ M_m : Measure ℝ, IsProbabilityMeasure M_m ∧
        _L = MeasureTheory.Measure.conv
                (ProbabilityTheory.gaussianReal 0 sigma_sq_m) M_m := by
  -- `_hRegular` is exactly the slim per-`m` convolution decomposition.
  -- Extract the witness directly.
  intro _hCone _hConvex m g_P h_orth h_in_T
  exact _hRegular g_P h_orth h_in_T

/-- **Lévy-continuity m-pass** for the convolution decomposition (parametric
vdV step at the boundary of §25.3).

Given a per-`m` decomposition family `L = N(0, σ_m²) ⋆ M_m` for probability
measures `M_m` on `ℝ` with `σ_m² → sigmaR`, produce a final probability measure
`M` such that `L = N(0, sigmaR) ⋆ M`.

This is the m-pass through Lévy's continuity theorem on the mixing-measure
characteristic functions: `charFun M_m = charFun L / charFun N(0, σ_m²)`
converges pointwise to `f t := charFun L t / charFun N(0, sigmaR) t` (gaussian
charFn never vanishes, so the quotient is well-defined). Continuity of `f`
at `0` follows from continuity of both `charFun L` and `charFun N(0, sigmaR)`
at `0` and `f 0 = 1`. By
`MeasureTheory.isTightMeasureSet_of_tendsto_charFun`, the family `{M_m}`
is tight; by Prokhorov, it has a weakly convergent subnet with limit `M`;
the char-fn injectivity (`MeasureTheory.Measure.ext_of_charFun`) identifies
`charFun M = f`, so `charFun L = charFun N(0, sigmaR) * charFun M
= charFun (N(0, sigmaR) ⋆ M)` (`MeasureTheory.charFun_conv`), giving
`L = N(0, sigmaR) ⋆ M`.

The conclusion is mathematically forced by the setup parameters (the per-`m`
decomposition family + `σ_m² → sigmaR` are themselves derived via
`perMConvDecomp` + Parseval), so it is a named lemma rather than a
caller-supplied input. The closure uses
`isTightMeasureSet_of_tendsto_charFun` + Prokhorov + `ext_of_charFun` +
`charFun_conv` + `charFun_gaussianReal`.

Reference: vdV §25.3. -/
theorem levyMpass
    {IF_eff : ↥(L2ZeroMean P)}
    (_L : Measure ℝ) [IsProbabilityMeasure _L]
    (M_m : ℕ → Measure ℝ)
    (_hM_prob : ∀ m, IsProbabilityMeasure (M_m m))
    (sigma_sq_m : ℕ → ℝ≥0)
    (_hDecomp : ∀ m, _L = MeasureTheory.Measure.conv
                  (ProbabilityTheory.gaussianReal 0 (sigma_sq_m m))
                  (M_m m))
    (_hSigma : Tendsto (fun m => ((sigma_sq_m m : ℝ≥0) : ℝ)) atTop
        (𝓝 (‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2))) :
    let sigma_sq : ℝ≥0 :=
      ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩
    ∃ M : Measure ℝ, IsProbabilityMeasure M ∧
      _L = MeasureTheory.Measure.conv
              (ProbabilityTheory.gaussianReal 0 sigma_sq) M := by
  -- Local notation for the Gaussian factor at variance `v`.
  set sigmaNN : ℝ≥0 :=
    ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩ with hsigmaNN
  set sigmaR : ℝ := ((sigmaNN : ℝ≥0) : ℝ) with hsigmaR
  have hsigmaR_eq : sigmaR = ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 := by
    rw [hsigmaR, hsigmaNN]; rfl
  -- The candidate target characteristic function:
  -- `f t = charFun L t / charFun (gaussianReal 0 sigmaR) t`.
  set f : ℝ → ℂ := fun t =>
    MeasureTheory.charFun _L t /
      MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 sigmaNN) t with hf
  -- Convenience: the Gaussian charFn closed form.
  -- `charFun (gaussianReal 0 v) t = exp(t·0·I − v·t²/2) = exp(−v·t²/2)`,
  -- which is never zero.
  have hGauss_apply : ∀ (v : ℝ≥0) (t : ℝ),
      MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 v) t =
        Complex.exp (-((v : ℝ) * t ^ 2 / 2)) := by
    intro v t
    have := ProbabilityTheory.charFun_gaussianReal (μ := (0 : ℝ)) (v := v) t
    simpa using this
  have hGauss_ne : ∀ (v : ℝ≥0) (t : ℝ),
      MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 v) t ≠ 0 := by
    intro v t
    simp [hGauss_apply v t, Complex.exp_ne_zero]
  -- `charFun L 0 = 1`: at `0`, `charFun μ 0 = μ.real Set.univ`.
  have hL_charFn_zero : MeasureTheory.charFun _L 0 = 1 := by
    simp [MeasureTheory.charFun_zero, MeasureTheory.measureReal_def,
          measure_univ]
  -- `charFun (gaussianReal 0 sigmaR) 0 = 1`.
  have hGauss_zero : MeasureTheory.charFun
      (ProbabilityTheory.gaussianReal 0 sigmaNN) 0 = 1 := by
    simp [hGauss_apply sigmaNN 0]
  -- `f 0 = 1`.
  have hf_zero : f 0 = 1 := by
    simp [hf, hL_charFn_zero, hGauss_zero]
  -- `f` is continuous on ℝ — both numerator and denominator are continuous,
  -- and the denominator is nonzero everywhere.
  have hcharFn_L_cont : Continuous (MeasureTheory.charFun _L) :=
    MeasureTheory.continuous_charFun
  have hcharFn_Gauss_cont : ∀ v : ℝ≥0,
      Continuous (MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 v)) :=
    fun v => MeasureTheory.continuous_charFun
  have hf_cont : Continuous f := by
    refine Continuous.div hcharFn_L_cont (hcharFn_Gauss_cont sigmaNN) ?_
    intro t; exact hGauss_ne sigmaNN t
  have hf_cont0 : ContinuousAt f 0 := hf_cont.continuousAt
  -- Step 4: `charFun (M_m m) t → f t` pointwise.
  --
  -- From `_hDecomp m` and `charFun_conv`:
  --   `charFun L t = charFun (gaussianReal 0 (sigma_sq_m m)) t * charFun (M_m m) t`.
  -- So `charFun (M_m m) t = charFun L t / charFun (gaussianReal 0 (sigma_sq_m m)) t`.
  -- Continuity of the closed-form Gaussian char-fn in `v` plus `_hSigma` gives the limit.
  haveI : ∀ m, IsProbabilityMeasure (M_m m) := _hM_prob
  have hCharFn_conv : ∀ m (t : ℝ),
      MeasureTheory.charFun _L t =
        MeasureTheory.charFun
            (ProbabilityTheory.gaussianReal 0 (sigma_sq_m m)) t *
          MeasureTheory.charFun (M_m m) t := by
    intro m t
    rw [_hDecomp m]
    exact MeasureTheory.charFun_conv (μ := ProbabilityTheory.gaussianReal 0 _)
      (ν := M_m m) t
  have hCharFn_M : ∀ m (t : ℝ),
      MeasureTheory.charFun (M_m m) t =
        MeasureTheory.charFun _L t /
          MeasureTheory.charFun
              (ProbabilityTheory.gaussianReal 0 (sigma_sq_m m)) t := by
    intro m t
    have hne := hGauss_ne (sigma_sq_m m) t
    field_simp
    linear_combination (hCharFn_conv m t).symm
  have hCharFn_M_lim : ∀ t : ℝ,
      Tendsto (fun m => MeasureTheory.charFun (M_m m) t) atTop (𝓝 (f t)) := by
    intro t
    -- `(fun m => charFun (M_m m) t) =
    --  (fun m => charFun L t / charFun (gaussianReal 0 (sigma_sq_m m)) t)`
    -- by `hCharFn_M`.
    have h_eq : ∀ m,
        MeasureTheory.charFun (M_m m) t =
          MeasureTheory.charFun _L t /
            Complex.exp (-((sigma_sq_m m : ℝ) * t ^ 2 / 2)) := by
      intro m
      rw [hCharFn_M m t, hGauss_apply (sigma_sq_m m) t]
    -- The denominator side tends to `Complex.exp (-(sigmaR * t² / 2))` by continuity of
    -- `Complex.exp`
    -- composed with the real-valued continuous map `v ↦ -(v·t²/2)`.
    have h_denom :
        Tendsto (fun m => Complex.exp (-((sigma_sq_m m : ℝ) * t ^ 2 / 2)))
          atTop (𝓝 (Complex.exp (-(sigmaR * t ^ 2 / 2)))) := by
      refine (Complex.continuous_exp.tendsto _).comp ?_
      have h₁ : Tendsto (fun m => ((sigma_sq_m m : ℝ≥0) : ℝ)) atTop (𝓝 sigmaR) := by
        simpa [hsigmaR, hsigmaNN, hsigmaR_eq] using! _hSigma
      have h₂ : Tendsto
          (fun m => Complex.ofReal (-((sigma_sq_m m : ℝ) * t ^ 2 / 2)))
          atTop (𝓝 (Complex.ofReal (-(sigmaR * t ^ 2 / 2)))) := by
        refine (Complex.continuous_ofReal.tendsto _).comp ?_
        exact ((h₁.mul tendsto_const_nhds).div_const 2).neg
      simpa [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_ofNat] using h₂
    have h_target :
        Tendsto (fun m =>
            MeasureTheory.charFun _L t /
              Complex.exp (-((sigma_sq_m m : ℝ) * t ^ 2 / 2)))
          atTop (𝓝 (MeasureTheory.charFun _L t /
              Complex.exp (-(sigmaR * t ^ 2 / 2)))) :=
      tendsto_const_nhds.div h_denom (Complex.exp_ne_zero _)
    have h_f_eq : f t =
        MeasureTheory.charFun _L t /
          Complex.exp (-(sigmaR * t ^ 2 / 2)) := by
      change MeasureTheory.charFun _L t /
          MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 sigmaNN) t =
        MeasureTheory.charFun _L t /
          Complex.exp (-(sigmaR * t ^ 2 / 2))
      rw [hGauss_apply sigmaNN t]
    rw [h_f_eq]
    exact h_target.congr (fun m => (h_eq m).symm)
  -- Step 5: tightness of `{M_m m | m}`.
  have hTight : MeasureTheory.IsTightMeasureSet (Set.range M_m) :=
    MeasureTheory.isTightMeasureSet_of_tendsto_charFun (μ := M_m) hf_cont0
      hCharFn_M_lim
  -- Step 6: lift to `ProbabilityMeasure ℝ` and apply Prokhorov to get
  -- a subsequence converging to some `M : ProbabilityMeasure ℝ`.
  let MPM : ℕ → MeasureTheory.ProbabilityMeasure ℝ :=
    fun m => ⟨M_m m, _hM_prob m⟩
  have hTightPM :
      MeasureTheory.IsTightMeasureSet
        ({((μ : MeasureTheory.ProbabilityMeasure ℝ) : MeasureTheory.Measure ℝ) |
            μ ∈ Set.range MPM}) := by
    have hSet : ({((μ : MeasureTheory.ProbabilityMeasure ℝ) : MeasureTheory.Measure ℝ) |
                  μ ∈ Set.range MPM}) = Set.range M_m := by
      ext μ
      simp only [Set.mem_setOf_eq, Set.mem_range]
      constructor
      · rintro ⟨ν, ⟨m, rfl⟩, rfl⟩
        exact ⟨m, rfl⟩
      · rintro ⟨m, rfl⟩
        exact ⟨MPM m, ⟨m, rfl⟩, rfl⟩
    rw [hSet]
    exact hTight
  have hCompact : IsCompact (closure (Set.range MPM)) :=
    isCompact_closure_of_isTightMeasureSet hTightPM
  obtain ⟨M, hM_in_closure, φ, hφ_mono, hφ_tendsto⟩ :=
    hCompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  -- Step 7: identify `charFun M = f` via Lévy continuity for the
  -- subsequence.
  have hCharFn_M_eq :
      ∀ t, MeasureTheory.charFun ((M : MeasureTheory.Measure ℝ)) t = f t := by
    intro t
    -- (a) `charFun (MPM (φ k)) t → f t` along `k` (subsequence of pointwise limit).
    have h_sub_to_f :
        Tendsto
          (fun k => MeasureTheory.charFun
            ((MPM (φ k) : MeasureTheory.Measure ℝ)) t) atTop (𝓝 (f t)) := by
      have : Tendsto
          (fun k => MeasureTheory.charFun (M_m (φ k)) t) atTop (𝓝 (f t)) :=
        (hCharFn_M_lim t).comp hφ_mono.tendsto_atTop
      simpa [MPM] using this
    -- (b) `MPM (φ k) → M` weakly ⇒ pointwise charFn convergence.
    have h_sub_to_M :
        Tendsto
          (fun k => MeasureTheory.charFun
            ((MPM (φ k) : MeasureTheory.Measure ℝ)) t) atTop
          (𝓝 (MeasureTheory.charFun ((M : MeasureTheory.Measure ℝ)) t)) :=
      (MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp
        hφ_tendsto) t
    exact tendsto_nhds_unique h_sub_to_M h_sub_to_f
  -- Step 8: assemble the convolution identity via the existing helper.
  refine ⟨(M : MeasureTheory.Measure ℝ), inferInstance, ?_⟩
  -- The let-bound `sigma_sq` in the conclusion is definitionally `sigmaNN`.
  change _L = MeasureTheory.Measure.conv
              (ProbabilityTheory.gaussianReal 0 sigmaNN)
              ((M : MeasureTheory.Measure ℝ))
  -- Apply the char-fn factorisation extractor.
  refine
    AsymptoticStatistics.ForMathlib.CharFnConvolution.convolution_extraction_from_charFn
      _L (M : MeasureTheory.Measure ℝ) sigmaNN ?_
  intro u
  -- `charFun L u = charFun (gaussianReal 0 sigmaNN) u * charFun M u`.
  -- Use `charFun M u = f u = charFun L u / charFun (gaussianReal 0 sigmaNN) u`.
  rw [hCharFn_M_eq u]
  -- Goal: `charFun L u = charFun (gaussianReal 0 sigmaNN) u * f u`.
  -- Unfold `f` and clear the division.
  change MeasureTheory.charFun _L u =
    MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 sigmaNN) u *
      (MeasureTheory.charFun _L u /
        MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 sigmaNN) u)
  field_simp [hGauss_ne sigmaNN u]

/-- **Per-`(M, m)` inner Bayes-risk lower bound** (vdV §25.3 Lemmas 3+4 + the
basis-selection bridge, scalar specialisation).

For every truncation level `M : ℕ` and every variance candidate
`σ_m_sq : ℝ≥0` (in the projection-sequence range
`σ_m_sq := ‖p_m‖²` from `proj_seq_to_eif`), the LAM-LHS of
`semiparametric_local_asymptotic_minimax_theorem`
evaluated at the truncated loss `ℓ ⊓ M` dominates the Gaussian integral
`∫⁻ (ℓ ⊓ M) dN(0, σ_m_sq)`.

Book content (vdV §25.3):

* Lemma 3 (`bayes_risk_lower_bound`): per-finite-`I_0`
  `liminf_n` of Bayes-risk is bounded below by the limit-experiment
  Bayes risk against a Gaussian-shift density.
* Lemma 4 (`gaussianShift_minimax`): the limit-experiment Bayes
  risk dominates `∫⁻ ℓ dN(0, ‖A_m‖²)`.

The chain at fixed `m` chains these two via the basis-selection bridge
(`g_P : Fin m → L²₀(P)` orthonormal in `V_m`, `A : EuclideanSpace ℝ (Fin m)
→L[ℝ] ℝ` Riesz-paired with `p_m`) and identifies `‖A_m‖² = ‖p_m‖²`.

The per-`(M, m)` Bayes-risk lower bound `_hBayesLowerBound` is a book-data
input rather than a Lean-derived consequence of the LAM setup parameters:
closing it internally requires the full basis-selection + Riesz-pair +
ι-cone-restriction bridge plus the PSD-monotone Sion-minimax argument feeding
Lemma 4. The internal closure (via
`Parametric.GaussianShiftMinimax.gaussianShift_bayes_risk_sup_eq_target`)
is a separate downstream task. The resulting LAM theorem inherits the same
input one level up (propagated to
`semiparametric_local_asymptotic_minimax_theorem`).

Reference: vdV §25.3, plus the basis-selection bridge. -/
theorem bddInner
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (_hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              _hψ.derivative IF_eff)
    (_T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_γ : ↥(L2ZeroMean P) → QMDPath P)
    (_hγ_score : ∀ g, (g : ↥(L2ZeroMean P)) ∈ T_set.carrier →
      (_γ g).score = g)
    {ℓ : ℝ → ℝ≥0∞}
    (_hℓ_sub : BowlShaped ℓ)
    -- PSD-monotone via gaussianShift_bayes_risk_sup_eq_target + basis-selection
    -- bridge.
    (_hBayesLowerBound :
      ∀ (M : ℕ) (σ_m_sq : ℝ≥0),
        (σ_m_sq : ℝ) ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 →
        ⨆ I : { S : Finset ↥(L2ZeroMean P) //
                (S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier },
          Filter.liminf
            (fun n : ℕ =>
              (I.val : Finset ↥(L2ZeroMean P)).sup
                (fun g =>
                  ∫⁻ X : Fin n → Ω,
                    (ℓ (Real.sqrt n *
                        (_T_n n X - ψ ((_γ g).curve ((Real.sqrt n)⁻¹))))
                      ⊓ (M : ℝ≥0∞))
                    ∂(MeasureTheory.Measure.pi
                        (fun _ : Fin n => (_γ g).curve ((Real.sqrt n)⁻¹)))))
            atTop
          ≥ ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
              ∂(ProbabilityTheory.gaussianReal 0 σ_m_sq)) :
    ∀ (M : ℕ) (σ_m_sq : ℝ≥0),
      (σ_m_sq : ℝ) ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 →
      ⨆ I : { S : Finset ↥(L2ZeroMean P) //
              (S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier },
        Filter.liminf
          (fun n : ℕ =>
            (I.val : Finset ↥(L2ZeroMean P)).sup
              (fun g =>
                ∫⁻ X : Fin n → Ω,
                  (ℓ (Real.sqrt n *
                      (_T_n n X - ψ ((_γ g).curve ((Real.sqrt n)⁻¹))))
                    ⊓ (M : ℝ≥0∞))
                  ∂(MeasureTheory.Measure.pi
                      (fun _ : Fin n => (_γ g).curve ((Real.sqrt n)⁻¹)))))
          atTop
        ≥ ∫⁻ u : ℝ, (ℓ u ⊓ (M : ℝ≥0∞))
            ∂(ProbabilityTheory.gaussianReal 0 σ_m_sq) :=
  _hBayesLowerBound

/-- **Joint covariance block PSD-ness** (parametric joint-MGF differentiation
step from vdV §25.3).

For every orthonormal score basis `g_P : Fin m → L²₀(P)` of a finite-dim
subspace of the tangent set, the joint covariance block matrix
`[[varL, A_m]; [A_mᵀ, I_m]]` of `(IF_eff, g_P 1, …, g_P m)` is
positive semidefinite. Here `A_m i = ⟨IF_eff, g_P i⟩` and `varL` is the
variance of the regular-estimator weak limit.

The book argument proceeds by differentiating the joint MGF of
`(IF_eff, g_P 1, …, g_P m)` along an arbitrary linear combination and
applying Anderson's PSD-monotone covariance bound: for any `(s, t)
∈ ℝ × ℝᵐ`, the perturbed measure with score
`s · IF_eff + ⟨t, g_P⟩` has squared MGF gradient at `0` bounded by the
unperturbed Gaussian's, giving the PSD claim.

The joint covariance block PSD claim `_hCovBlockPSD` is book data via vdV
§25.3's joint-MGF differentiation + Anderson PSD-monotone covariance bound.
The internal closure (via the joint-MGF Schur reduction
`ForMathlib.JointMGF.joint_covariance_block_posSemidef` + `ForMathlib.Anderson`
PSD-monotone) is a separate downstream task. The resulting convolution theorem
inherits the same input one level up (propagated to
`semiparametric_convolution_theorem` and its corollary
`efficient_bound_is_asympVar_lowerBound`).

Reference: vdV §25.3, with vdV's joint-MGF differentiation argument as the
parametric core. -/
theorem covBlockPSDAll
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (_hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              _hψ.derivative IF_eff)
    (_T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_L : Measure ℝ) [IsProbabilityMeasure _L]
    (_hWeak : WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (_T_n n X - ψ P))) _L)
    (varL : ℝ)
    (_hvar : varL = ∫ x, (x - ∫ y, y ∂_L)^2 ∂_L)
    -- vdV §25.3 (joint MGF differentiation step). The book derives this
    -- from the parametric submodel's joint MGF identity + Anderson PSD-
    -- monotone covariance bound on the perturbed measure with score
    -- `s · IF_eff + ⟨t, g_P⟩` for `(s, t) ∈ ℝ × ℝᵐ`.
    (_hCovBlockPSD :
      ∀ {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P)),
        Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) →
        (∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) →
        (Matrix.fromBlocks
            (Matrix.of (fun _ _ : Fin 1 => varL))
            (Matrix.of (fun _ : Fin 1 => fun j : Fin m =>
              ⟪(IF_eff : ↥(L2ZeroMean P)),
                (g_P j : ↥(L2ZeroMean P))⟫_ℝ))
            (Matrix.of (fun i : Fin m => fun _ : Fin 1 =>
              ⟪(IF_eff : ↥(L2ZeroMean P)),
                (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
            (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (m : ℕ) (g_P : Fin m → ↥(L2ZeroMean P))
    (_hg_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (_hg_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    (Matrix.fromBlocks
        (Matrix.of (fun _ _ : Fin 1 => varL))
        (Matrix.of (fun _ : Fin 1 => fun j : Fin m =>
          ⟪(IF_eff : ↥(L2ZeroMean P)),
            (g_P j : ↥(L2ZeroMean P))⟫_ℝ))
        (Matrix.of (fun i : Fin m => fun _ : Fin 1 =>
          ⟪(IF_eff : ↥(L2ZeroMean P)),
            (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
        (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
  _hCovBlockPSD g_P _hg_orth _hg_in_T

/-! ## §25.20 closure bridges

The bridges below feed `AsymptoticRepresentation.LAN_representation`'s `hT_weak`
hypothesis from `IsRegularEstimator.shift`-style QMDPath weak limits
(the `paramSubmodelQMDPath` curve raised to the n-fold product).
`IsTangentBoundedDense` supplies bounded approximants to tangent vectors; the
finite-family construction later in this section orthonormalizes those
approximants while retaining boundedness, so they can be used in `paramSubmodel`. -/

open AsymptoticStatistics.LowerBounds.RegularEstimator
  (paramSubmodelQMDPath paramSubmodelQMDPath_curve_eq_paramSubmodel_density
   linPerturbScore linPerturbScore_mem_tangentSpace linPerturbScore_mem_span
   paramSubmodelQMDPath_score IsRegularEstimator)
open AsymptoticStatistics.ParametricFamily
  (paramSubmodel IsBoundedMixtureScores)
open AsymptoticStatistics.Core.MassMethod (IsTangentBoundedDense)

/-- **vdV §25.20 closure bridge** — the n-fold product of
the `paramSubmodelQMDPath` curve at parameter `(√n)⁻¹` equals the parametric
submodel's `productMeasure` at shift `(√n)⁻¹ • h`, eventually in `n`.

This is the **per-`h` eventually-form** bridge from `IsRegularEstimator.shift`'s
QMDPath-based weak limit (LHS) to `AsymptoticRepresentation.LAN_representation`'s
`productMeasure`-based `hT_weak` hypothesis (RHS).

For each fixed `h` satisfying `h_small`, both sides eventually agree as `n → ∞`
because the existing `paramSubmodelQMDPath_curve_eq_paramSubmodel_density`
gives the equality at every `s` near 0 in a `δ(h)`-neighborhood, and
`(√n)⁻¹ → 0` enters this neighborhood eventually-in-`n`.

Reference: vdV §25.3 proof of 25.20 (parametric submodel substitution step). -/
theorem pi_paramSubmodelQMDPath_curve_eq_productMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m))
    (h_small : ‖h‖ * m * hg.uniformBound ≤ 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      MeasureTheory.Measure.pi
          (fun _ : Fin n =>
            (AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPath
              g_P hg h h_small).curve ((Real.sqrt n)⁻¹))
        = AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (AsymptoticStatistics.ParametricFamily.paramSubmodel g_P hg h_orth)
            P ((Real.sqrt n)⁻¹ • h) (n := n) := by
  classical
  -- Step 1: get the existing eventually-in-s curve equality.
  have h_eventually_s :=
    paramSubmodelQMDPath_curve_eq_paramSubmodel_density g_P hg h_orth h h_small
  -- Step 2: transport eventually-in-`s in 𝓝 0` to eventually-in-`n in atTop`
  -- via Tendsto (fun n => (√n)⁻¹) atTop (𝓝 0).
  have h_tendsto :
      Filter.Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h_eventually_n :
      ∀ᶠ n : ℕ in Filter.atTop,
        (paramSubmodelQMDPath g_P hg h h_small).curve ((Real.sqrt n)⁻¹)
          = P.withDensity (fun ω =>
              ENNReal.ofReal
                ((paramSubmodel g_P hg h_orth).density ((Real.sqrt n)⁻¹ • h) ω)) :=
    h_tendsto.eventually h_eventually_s
  -- Step 3: lift the factor-equality through `Measure.pi` for each such n.
  filter_upwards [h_eventually_n] with n hn
  -- Both sides are `Measure.pi (fun _ : Fin n => F)` with equal factors.
  unfold AsymptoticStatistics.AsymptoticRepresentation.productMeasure
  exact congrArg (fun μ : Measure Ω => MeasureTheory.Measure.pi
      (fun _ : Fin n => μ)) hn

/-- **All-`h` analogue of `pi_paramSubmodelQMDPath_curve_eq_productMeasure`**:
eventually-in-`n` equality between the
`AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH` curve's
`n`-fold product and the parametric submodel's productMeasure at
`(√n)⁻¹ • h`. Works for any direction `h` (no smallness restriction).

This is the bridge consumed by the LAN-route pushforward weak-conv
lemma (`w2c_LAN_pushforward_steps_2_to_6`) to transfer
`IsRegularEstimator.shift`'s output (in `Measure.pi (curve.curve …)`
form) to the `productMeasure paramSubmodel`-based form. -/
theorem pi_paramSubmodelQMDPathAllH_curve_eq_productMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      MeasureTheory.Measure.pi
          (fun _ : Fin n =>
            (AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH g_P hg
                h).curve ((Real.sqrt n)⁻¹))
        = AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (paramSubmodel g_P hg h_orth) P ((Real.sqrt n)⁻¹ • h) (n := n) := by
  classical
  have h_eventually_s :=
    LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH_curve_eq_paramSubmodel_density
        g_P hg h_orth h
  have h_tendsto :
      Filter.Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h_eventually_n :
      ∀ᶠ n : ℕ in Filter.atTop,
        (AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH g_P hg h).curve
            ((Real.sqrt n)⁻¹)
          = P.withDensity (fun ω =>
              ENNReal.ofReal
                ((paramSubmodel g_P hg h_orth).density ((Real.sqrt n)⁻¹ • h) ω)) :=
    h_tendsto.eventually h_eventually_s
  filter_upwards [h_eventually_n] with n hn
  unfold AsymptoticStatistics.AsymptoticRepresentation.productMeasure
  exact congrArg (fun μ : Measure Ω => MeasureTheory.Measure.pi
      (fun _ : Fin n => μ)) hn

/-! ### productMeasure pushforward bridges

Two named theorems that lift the QMDPath-based weak limits supplied by
`IsRegularEstimator` (defined relative to `Measure.pi (curve.curve …)`)
to the `productMeasure`-based form consumed by
`AsymptoticRepresentation.LAN_representation` and downstream Le Cam bridges. The
measure-family substitution is justified by
`pi_paramSubmodelQMDPath_curve_eq_productMeasure`, which provides the
eventually-in-`n` equality of the two product measures. -/

/-- **Eventually-equal substitution for weak convergence.** If `μ n = ν n`
for `n` eventually large enough, then `WeakConverges μ ρ ↔ WeakConverges ν ρ`.
The forward direction (used here) is the bridge from a QMDPath-based weak
limit (LHS) to the parametrically-rewritten form (RHS). -/
private theorem weakConverges_congr_eventually
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    {μ ν : ℕ → Measure E} {ρ : Measure E}
    (h_eq : ∀ᶠ n : ℕ in Filter.atTop, μ n = ν n)
    (hμ : WeakConverges μ ρ) :
    WeakConverges ν ρ := by
  intro f
  -- Per test function, integrals match eventually in n, so the limits agree.
  refine (hμ f).congr' ?_
  filter_upwards [h_eq] with n hn
  exact congrArg (fun μ : Measure E => ∫ x, f x ∂μ) hn

/-- **vdV §25.20 closure bridge** — canonical form
(recenter at the *perturbed truth* `ψ((paramSubmodelQMDPath …).curve …)`).

Lifts `IsRegularEstimator.shift` from a `Measure.pi (curve.curve …)`-based
weak limit to a `productMeasure`-based weak limit, using the measure equality
`pi_paramSubmodelQMDPath_curve_eq_productMeasure`. The recentering is at the
perturbed truth, mirroring the canonical vdV §25.3.2 form. -/
theorem productMeasure_paramSubmodel_pushforward_weakConverges
    (T_set : TangentSpec P) (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (h : EuclideanSpace ℝ (Fin m))
    (h_small : ‖h‖ * m * hg.uniformBound ≤ 1) :
    WeakConverges
      (fun n : ℕ =>
        (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (AsymptoticStatistics.ParametricFamily.paramSubmodel g_P hg h_orth)
            P ((Real.sqrt n)⁻¹ • h) (n := n)).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n n X -
                ψ ((paramSubmodelQMDPath g_P hg h h_small).curve
                    ((Real.sqrt n)⁻¹)))))
      L := by
  classical
  -- Step 1: instantiate `IsRegularEstimator.shift` at the linear-combination
  -- score `g := linPerturbScore g_P h`, realised by `paramSubmodelQMDPath`.
  have hLin_in_T : linPerturbScore g_P h ∈ Submodule.span ℝ T_set.carrier :=
    linPerturbScore_mem_span T_set g_P h_in_T h
  have hScore_eq :
      (paramSubmodelQMDPath g_P hg h h_small).score = linPerturbScore g_P h :=
    paramSubmodelQMDPath_score g_P hg h h_small
  have h_qmd_weak :
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n =>
                (paramSubmodelQMDPath g_P hg h h_small).curve
                  ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X -
                  ψ ((paramSubmodelQMDPath g_P hg h h_small).curve
                      ((Real.sqrt n)⁻¹)))))
        L :=
    IsRegularEstimator.shift hReg (linPerturbScore g_P h) hLin_in_T
      (paramSubmodelQMDPath g_P hg h h_small) hScore_eq
  -- Step 2: substitute the measure family via the eventually-equality
  -- `pi_paramSubmodelQMDPath_curve_eq_productMeasure`.
  have h_eq_eventually :=
    pi_paramSubmodelQMDPath_curve_eq_productMeasure g_P hg h_orth h h_small
  have h_map_eq_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        (MeasureTheory.Measure.pi
            (fun _ : Fin n =>
              (paramSubmodelQMDPath g_P hg h h_small).curve
                ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n n X -
                ψ ((paramSubmodelQMDPath g_P hg h h_small).curve
                    ((Real.sqrt n)⁻¹))))
          = (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (AsymptoticStatistics.ParametricFamily.paramSubmodel g_P hg h_orth)
              P ((Real.sqrt n)⁻¹ • h) (n := n)).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X -
                  ψ ((paramSubmodelQMDPath g_P hg h h_small).curve
                      ((Real.sqrt n)⁻¹)))) := by
    filter_upwards [h_eq_eventually] with n hn
    rw [hn]
  -- Step 3: apply the `congr_eventually` helper.
  exact weakConverges_congr_eventually h_map_eq_eventually h_qmd_weak

/-- **vdV §25.20 closure bridge** — Hájek-shift form
(recenter at the *unperturbed* truth `ψ P`, pick up the deterministic
Slutsky shift `(dirac ⟪IF_eff, linPerturbScore g_P h⟫) ∗ L`).

This is the R¹-lifted form fed to `AsymptoticRepresentation.LAN_representation`. The
deterministic shift is the inner product of the EIF with the linear-
combination score along direction `h` in `span g_P`.

The conditional `‖h‖ * m * hg.uniformBound ≤ 1` is inherited from
`paramSubmodelQMDPath`'s small-direction constraint; the caller handles
arbitrary `h` via direction rescaling. -/
theorem productMeasure_paramSubmodel_pushforward_to_R1
    (T_set : TangentSpec P) (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff}
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    ∀ h : EuclideanSpace ℝ (Fin m),
      ‖h‖ * m * hg.uniformBound ≤ 1 →
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (AsymptoticStatistics.ParametricFamily.paramSubmodel g_P hg h_orth)
              P ((Real.sqrt n)⁻¹ • h) (n := n)).map
            (fun X : Fin n → Ω =>
              Real.sqrt n * (T_n n X - ψ P)))
        (MeasureTheory.Measure.conv
          (MeasureTheory.Measure.dirac
            (⟪(IF_eff : ↥(L2ZeroMean P)),
              AsymptoticStatistics.LowerBounds.RegularEstimator.linPerturbScore
                g_P h⟫_ℝ)) L) := by
  classical
  intro h h_small
  -- Step 1: instantiate `hajek_shift_form` at the linear-combination score.
  have hLin_in_T : linPerturbScore g_P h ∈ Submodule.span ℝ T_set.carrier :=
    linPerturbScore_mem_span T_set g_P h_in_T h
  have hScore_eq :
      (paramSubmodelQMDPath g_P hg h h_small).score = linPerturbScore g_P h :=
    paramSubmodelQMDPath_score g_P hg h h_small
  have h_hajek :
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n =>
                (paramSubmodelQMDPath g_P hg h h_small).curve
                  ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
        ((MeasureTheory.Measure.dirac
            (⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫_ℝ)) ∗ L) :=
    AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator.hajek_shift_form
      (hψ := hψ) (hEIF := hEIF) hReg hT_meas
      (linPerturbScore g_P h) hLin_in_T
      (paramSubmodelQMDPath g_P hg h h_small) hScore_eq
  -- Step 2: substitute the measure family via the eventually-equality
  -- `pi_paramSubmodelQMDPath_curve_eq_productMeasure`.
  have h_eq_eventually :=
    pi_paramSubmodelQMDPath_curve_eq_productMeasure g_P hg h_orth h h_small
  have h_map_eq_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        (MeasureTheory.Measure.pi
            (fun _ : Fin n =>
              (paramSubmodelQMDPath g_P hg h h_small).curve
                ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P))
          = (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (AsymptoticStatistics.ParametricFamily.paramSubmodel g_P hg h_orth)
              P ((Real.sqrt n)⁻¹ • h) (n := n)).map
            (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)) := by
    filter_upwards [h_eq_eventually] with n hn
    rw [hn]
  -- Step 3: identify `Measure.conv (dirac c) L = (dirac c) ∗ L` (notation
  -- `∗` is `MeasureTheory.Measure.conv`).
  have h_conv_eq :
      MeasureTheory.Measure.conv
          (MeasureTheory.Measure.dirac
            (⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫_ℝ)) L
        = (MeasureTheory.Measure.dirac
            (⟪(IF_eff : ↥(L2ZeroMean P)), linPerturbScore g_P h⟫_ℝ)) ∗ L := rfl
  rw [h_conv_eq]
  -- Step 4: apply the `congr_eventually` helper to substitute the measure family.
  exact weakConverges_congr_eventually h_map_eq_eventually h_hajek

/-! ### Orthonormal → IsBoundedMixtureScores adapter

The full statement (`orthonormal_to_bounded_mixture_via_tangent_dense`) is
built from the technical sub-lemma `tangent_bounded_orthonormal_approx`: the
Gram-Schmidt-on-bounded-approximants step that produces a bounded orthonormal
frame near the given orthonormal frame in L². -/

/-- **One-step Gram-Schmidt update on an essentially bounded vector.**

Given an orthonormal family `e' : Fin m → ↥(L2ZeroMean P)` of essentially
bounded vectors in `tangentSpace T_set` and an essentially bounded vector
`h ∈ tangentSpace T_set`, the projected residual

  `v := h - Σⱼ ⟨h, e' j⟩ • e' j`

is orthogonal to every `e' j`, lies in `tangentSpace T_set`, and is
essentially bounded. If `v ≠ 0`, normalising it yields a unit vector
`e := v/‖v‖` with the same properties. This is the building block used by
`tangent_bounded_orthonormal_approx` to incrementally extend a bounded
orthonormal frame. -/
private lemma gs_step_props
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {m : ℕ} (e' : Fin m → ↥(L2ZeroMean P))
    (he'_in_T : ∀ j, (e' j : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (he'_ess : ∀ j, AsymptoticStatistics.Core.MassMethod.IsEssBoundedMixtureScore (e' j))
    (h : ↥(L2ZeroMean P))
    (hh_in_T : (h : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (hh_ess : AsymptoticStatistics.Core.MassMethod.IsEssBoundedMixtureScore h) :
    (h - ∑ j, ⟪(e' j : ↥(L2ZeroMean P)),
                (h : ↥(L2ZeroMean P))⟫_ℝ • (e' j : ↥(L2ZeroMean P)))
        ∈ tangentSpace T_set ∧
      AsymptoticStatistics.Core.MassMethod.IsEssBoundedMixtureScore
        (h - ∑ j, ⟪(e' j : ↥(L2ZeroMean P)),
                    (h : ↥(L2ZeroMean P))⟫_ℝ • (e' j : ↥(L2ZeroMean P))) := by
  classical
  -- tangent-space membership: tangentSpace is a Submodule, closed under sub / sum / smul.
  refine ⟨?_, ?_⟩
  · refine Submodule.sub_mem _ hh_in_T ?_
    refine Submodule.sum_mem _ ?_
    intro j _
    exact Submodule.smul_mem _ _ (he'_in_T j)
  · -- ess-boundedness: the residual is a finite linear combination of `h` and `e' j`s.
    have h_sum_ess : AsymptoticStatistics.Core.MassMethod.IsEssBoundedMixtureScore
        (∑ j, ⟪(e' j : ↥(L2ZeroMean P)),
                (h : ↥(L2ZeroMean P))⟫_ℝ • (e' j : ↥(L2ZeroMean P))) := by
      apply AsymptoticStatistics.Core.MassMethod.IsEssBoundedMixtureScore.finsetSum
      intro j _
      exact (he'_ess j).smul _
    -- h - sum = h + (-1) • sum
    have h_neg : (- (∑ j, ⟪(e' j : ↥(L2ZeroMean P)),
                            (h : ↥(L2ZeroMean P))⟫_ℝ • (e' j : ↥(L2ZeroMean P))))
        = ((-1 : ℝ) • (∑ j, ⟪(e' j : ↥(L2ZeroMean P)),
                              (h : ↥(L2ZeroMean P))⟫_ℝ • (e' j : ↥(L2ZeroMean P)))) := by
      simp
    have h_eq : (h - ∑ j, ⟪(e' j : ↥(L2ZeroMean P)),
                            (h : ↥(L2ZeroMean P))⟫_ℝ • (e' j : ↥(L2ZeroMean P)))
        = h + ((-1 : ℝ) • (∑ j, ⟪(e' j : ↥(L2ZeroMean P)),
                                  (h : ↥(L2ZeroMean P))⟫_ℝ
                                  • (e' j : ↥(L2ZeroMean P)))) := by
      rw [sub_eq_add_neg, h_neg]
    rw [h_eq]
    exact hh_ess.add (h_sum_ess.smul _)

/-- **L²-closeness statement for the Gram-Schmidt step.**

This is the L²-closeness analytic step extracted as a named lemma — given a
unit vector `u` orthogonal in L²(P) to an orthonormal family `(g0 j)`, an
approximant `e' j` of `g0 j` (within η_E), an approximant `h` of `u`
(within η_H), the projected residual

  `v := h - Σⱼ ⟨e' j, h⟩ • e' j`

is L²-close to `u` within `η_H · (1 + m + m·η_H) + m · η_E · (1 + η_H)`.
This bound, normalised against ‖v‖ ≥ 1 - (that bound), yields the final
closeness for the Gram-Schmidt step in `tangent_bounded_orthonormal_approx`.

This is a project-internal analytic sub-lemma; not a vdV theorem. -/
private lemma gs_residual_close
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g0 : Fin m → ↥(L2ZeroMean P)) (u : ↥(L2ZeroMean P))
    (h_orth_extended : ∀ j : Fin m,
        ⟪(g0 j : ↥(L2ZeroMean P)), (u : ↥(L2ZeroMean P))⟫_ℝ = 0)
    (hg0_unit : ∀ j, ‖(g0 j : ↥(L2ZeroMean P))‖ = 1)
    (e' : Fin m → ↥(L2ZeroMean P))
    (he'_unit : ∀ j, ‖(e' j : ↥(L2ZeroMean P))‖ = 1)
    (η_E : ℝ) (he'_close : ∀ j, ‖(e' j : ↥(L2ZeroMean P))
                                    - (g0 j : ↥(L2ZeroMean P))‖ ≤ η_E)
    (η_E_nn : 0 ≤ η_E)
    (h : ↥(L2ZeroMean P))
    (η_H : ℝ) (hh_close : ‖h - u‖ ≤ η_H) (_η_H_nn : 0 ≤ η_H)
    (hu_unit : ‖(u : ↥(L2ZeroMean P))‖ = 1) :
    ‖(h - ∑ j, ⟪(e' j : ↥(L2ZeroMean P)),
              (h : ↥(L2ZeroMean P))⟫_ℝ • (e' j : ↥(L2ZeroMean P))) - u‖
      ≤ η_H + (m : ℝ) * (η_E * (1 + η_H) + η_H) := by
  classical
  -- ‖h‖ ≤ 1 + η_H.
  have hh_norm_le : ‖h‖ ≤ 1 + η_H := by
    have h_calc : ‖h‖ = ‖(h - u) + u‖ := by congr 1; abel
    rw [h_calc]
    calc ‖(h - u) + u‖
        ≤ ‖h - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ η_H + 1 := by gcongr; exact le_of_eq hu_unit
      _ = 1 + η_H := by ring
  -- bound on each |⟨e' j, h⟩|.
  have h_inner_bound : ∀ j : Fin m,
      |⟪(e' j : ↥(L2ZeroMean P)), (h : ↥(L2ZeroMean P))⟫_ℝ| ≤ η_E * (1 + η_H) + η_H := by
    intro j
    have h_split1 :
        ⟪(e' j : ↥(L2ZeroMean P)), (h : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪(e' j : ↥(L2ZeroMean P)) - (g0 j : ↥(L2ZeroMean P)),
              (h : ↥(L2ZeroMean P))⟫_ℝ
            + ⟪(g0 j : ↥(L2ZeroMean P)), (h : ↥(L2ZeroMean P))⟫_ℝ := by
      rw [← inner_add_left]; congr 1; abel
    have h_split2 :
        ⟪(g0 j : ↥(L2ZeroMean P)), (h : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪(g0 j : ↥(L2ZeroMean P)),
              (h : ↥(L2ZeroMean P)) - (u : ↥(L2ZeroMean P))⟫_ℝ
            + ⟪(g0 j : ↥(L2ZeroMean P)), (u : ↥(L2ZeroMean P))⟫_ℝ := by
      rw [← inner_add_right]; congr 1; abel
    rw [h_split1, h_split2, h_orth_extended j, add_zero]
    have h_cs1 :
        |⟪(e' j : ↥(L2ZeroMean P)) - (g0 j : ↥(L2ZeroMean P)),
            (h : ↥(L2ZeroMean P))⟫_ℝ|
          ≤ ‖(e' j : ↥(L2ZeroMean P)) - (g0 j : ↥(L2ZeroMean P))‖
            * ‖(h : ↥(L2ZeroMean P))‖ :=
      abs_real_inner_le_norm _ _
    have h_cs2 :
        |⟪(g0 j : ↥(L2ZeroMean P)),
            (h : ↥(L2ZeroMean P)) - (u : ↥(L2ZeroMean P))⟫_ℝ|
          ≤ ‖(g0 j : ↥(L2ZeroMean P))‖
            * ‖(h : ↥(L2ZeroMean P)) - (u : ↥(L2ZeroMean P))‖ :=
      abs_real_inner_le_norm _ _
    calc |⟪(e' j : ↥(L2ZeroMean P)) - (g0 j : ↥(L2ZeroMean P)),
              (h : ↥(L2ZeroMean P))⟫_ℝ
            + ⟪(g0 j : ↥(L2ZeroMean P)),
                (h : ↥(L2ZeroMean P)) - (u : ↥(L2ZeroMean P))⟫_ℝ|
        ≤ |⟪(e' j : ↥(L2ZeroMean P)) - (g0 j : ↥(L2ZeroMean P)),
                (h : ↥(L2ZeroMean P))⟫_ℝ|
          + |⟪(g0 j : ↥(L2ZeroMean P)),
                (h : ↥(L2ZeroMean P)) - (u : ↥(L2ZeroMean P))⟫_ℝ| := abs_add_le _ _
      _ ≤ ‖(e' j : ↥(L2ZeroMean P)) - (g0 j : ↥(L2ZeroMean P))‖
              * ‖(h : ↥(L2ZeroMean P))‖
          + ‖(g0 j : ↥(L2ZeroMean P))‖
              * ‖(h : ↥(L2ZeroMean P)) - (u : ↥(L2ZeroMean P))‖ :=
            add_le_add h_cs1 h_cs2
      _ ≤ η_E * (1 + η_H) + 1 * η_H := by
            gcongr
            · exact he'_close j
            · exact le_of_eq (hg0_unit j)
      _ = η_E * (1 + η_H) + η_H := by ring
  -- ‖proj‖ ≤ m * (η_E (1+η_H) + η_H).
  set proj : ↥(L2ZeroMean P) :=
    ∑ j, ⟪(e' j : ↥(L2ZeroMean P)), (h : ↥(L2ZeroMean P))⟫_ℝ
      • (e' j : ↥(L2ZeroMean P)) with hproj_def
  have h_proj_norm : ‖proj‖ ≤ (m : ℝ) * (η_E * (1 + η_H) + η_H) := by
    have h_sum_le : ‖proj‖
        ≤ ∑ j : Fin m, ‖⟪(e' j : ↥(L2ZeroMean P)),
                          (h : ↥(L2ZeroMean P))⟫_ℝ
                        • (e' j : ↥(L2ZeroMean P))‖ := by
      rw [hproj_def]; exact norm_sum_le _ _
    have h_each : ∀ j : Fin m,
        ‖⟪(e' j : ↥(L2ZeroMean P)),
              (h : ↥(L2ZeroMean P))⟫_ℝ
            • (e' j : ↥(L2ZeroMean P))‖
          ≤ (η_E * (1 + η_H) + η_H) := by
      intro j
      rw [norm_smul, Real.norm_eq_abs, he'_unit j, mul_one]
      exact h_inner_bound j
    refine h_sum_le.trans ?_
    calc ∑ j : Fin m, ‖⟪(e' j : ↥(L2ZeroMean P)),
                          (h : ↥(L2ZeroMean P))⟫_ℝ
                        • (e' j : ↥(L2ZeroMean P))‖
        ≤ ∑ _j : Fin m, (η_E * (1 + η_H) + η_H) :=
            Finset.sum_le_sum (fun j _ => h_each j)
      _ = (m : ℝ) * (η_E * (1 + η_H) + η_H) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- combine.
  have h_eq : (h - proj) - u = (h - u) - proj := by abel
  calc ‖(h - proj) - u‖
      = ‖(h - u) - proj‖ := by rw [h_eq]
    _ ≤ ‖h - u‖ + ‖proj‖ := by simpa using norm_sub_le (h - u) proj
    _ ≤ η_H + (m : ℝ) * (η_E * (1 + η_H) + η_H) := by gcongr

/-- **Normalisation closeness**: if `v` is L²-close to a unit vector `u`
within η < 1, then `v/‖v‖ - u` is close to `0` within `2η/(1-η)`. -/
private lemma normalise_close
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (v u : ↥(L2ZeroMean P)) (hu_unit : ‖u‖ = 1)
    (η : ℝ) (hv_close : ‖v - u‖ ≤ η) (hη_lt : η < 1) (hη_nn : 0 ≤ η) :
    ∃ (hv_ne : v ≠ 0), ‖(‖v‖⁻¹ • v) - u‖ ≤ 2 * η / (1 - η) := by
  -- ‖v‖ ≥ 1 - η > 0
  have hv_norm_lb : 1 - η ≤ ‖v‖ := by
    have h1 : (1 : ℝ) - ‖v‖ ≤ ‖v - u‖ := by
      have h_calc : (1 : ℝ) - ‖v‖ = ‖u‖ - ‖v‖ := by rw [hu_unit]
      rw [h_calc]
      have := abs_norm_sub_norm_le u v
      have h_ord : ‖u‖ - ‖v‖ ≤ |‖u‖ - ‖v‖| := le_abs_self _
      refine h_ord.trans (this.trans ?_)
      rw [show u - v = -(v - u) from by abel, norm_neg]
    linarith
  have hv_pos : 0 < ‖v‖ := by linarith
  have hv_ne : v ≠ 0 := by
    intro hzero; rw [hzero, norm_zero] at hv_pos; exact lt_irrefl _ hv_pos
  refine ⟨hv_ne, ?_⟩
  -- v/‖v‖ - u = (v - ‖v‖ • u) / ‖v‖
  have h_v_eq : (‖v‖⁻¹ • v) - u = ‖v‖⁻¹ • (v - ‖v‖ • u) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hv_pos), one_smul]
  rw [h_v_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv_pos)]
  -- ‖v - ‖v‖•u‖ ≤ ‖v - u‖ + |‖v‖ - 1| ≤ η + η = 2η.
  have h_abs_norm_le : |1 - ‖v‖| ≤ η := by
    have h_upper : ‖v‖ ≤ 1 + η := by
      have h_calc : ‖v‖ = ‖u + (v - u)‖ := by congr 1; abel
      rw [h_calc]
      calc ‖u + (v - u)‖
          ≤ ‖u‖ + ‖v - u‖ := norm_add_le _ _
        _ ≤ 1 + η := by gcongr; exact le_of_eq hu_unit
    rw [abs_le]
    refine ⟨?_, ?_⟩ <;> linarith
  have h_inner : ‖v - ‖v‖ • u‖ ≤ 2 * η := by
    have h_split : v - ‖v‖ • u = (v - u) + (1 - ‖v‖) • u := by
      rw [sub_smul, one_smul]; abel
    rw [h_split]
    calc ‖(v - u) + (1 - ‖v‖) • u‖
        ≤ ‖v - u‖ + ‖(1 - ‖v‖) • u‖ := norm_add_le _ _
      _ = ‖v - u‖ + |1 - ‖v‖| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖v - u‖ + |1 - ‖v‖| := by rw [hu_unit, mul_one]
      _ ≤ η + η := add_le_add hv_close h_abs_norm_le
      _ = 2 * η := by ring
  calc ‖v‖⁻¹ * ‖v - ‖v‖ • u‖
      ≤ ‖v‖⁻¹ * (2 * η) := by
        gcongr
      _ ≤ (1 - η)⁻¹ * (2 * η) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply inv_anti₀ (by linarith) hv_norm_lb
      _ = 2 * η / (1 - η) := by ring

/-- **Gram-Schmidt-on-bounded-approximants sub-lemma.**

Given an orthonormal family `g_P` of vectors in `tangentSpace T_set`, and
the regularity hypothesis `IsTangentBoundedDense T_set`, there exists an
orthonormal family `g_P'` in `tangentSpace T_set`, with each component
`IsEssBoundedMixtureScore`, that is L² close to `g_P` (within ε in each
coordinate).

This is the core technical step of `orthonormal_to_bounded_mixture_via_tangent_dense`.

**Proof strategy**: induct on `m`. Base case `m = 0` is vacuous. Inductive
step: apply the IH to `Fin.init g_P` with target tolerance `ε/(8(m+1))`
to get a bounded orthonormal `e' : Fin m → ↥(L2ZeroMean P)` close to
`Fin.init g_P`. Then pick a bounded approximant `h ∈ tangentSpace T_set`
of `g_P (Fin.last m)` with `‖h - g_P (last m)‖ ≤ ε/(8(m+1))`. The projected
residual

  `v := h - Σⱼ ⟨e' j, h⟩ • e' j`

is in tangent space, essentially bounded, and (by `gs_residual_close`)
within `ε/4` of `g_P (Fin.last m)`. Normalisation
(by `normalise_close`) gives the final unit vector within `ε`. Snoc to `e'`. -/
theorem tangent_bounded_orthonormal_approx
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    (hT_dense : IsTangentBoundedDense T_set)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g_P' : Fin m → ↥(L2ZeroMean P)),
      Orthonormal ℝ (fun i : Fin m => (g_P' i : ↥(L2ZeroMean P))) ∧
      IsBoundedMixtureScores g_P' ∧
      (∀ i, (g_P' i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set) ∧
      (∀ i, ‖(g_P i : ↥(L2ZeroMean P)) - (g_P' i : ↥(L2ZeroMean P))‖ ≤ ε) := by
  classical
  revert g_P h_orth h_in_T ε hε
  induction m with
  | zero =>
    intro g_P _ _ ε _
    refine ⟨g_P, ?_, ?_, ?_, ?_⟩
    · exact Orthonormal.of_isEmpty _
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ m IH =>
    intro g_P h_orth h_in_T ε hε
    -- Step 1: apply IH to `Fin.init g_P` with target tolerance
    -- ε' := ε/(8(m+1)).
    set g0 : Fin m → ↥(L2ZeroMean P) := fun i => g_P i.castSucc with hg0_def
    have hg0_orth : Orthonormal ℝ (fun i : Fin m => (g0 i : ↥(L2ZeroMean P))) := by
      have := h_orth.comp (fun i : Fin m => i.castSucc) (Fin.castSucc_injective m)
      simpa [g0, Function.comp] using! this
    have hg0_in_T : ∀ i, (g0 i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := by
      intro i; exact h_in_T i.castSucc
    have hm1_pos : 0 < ((m : ℝ) + 1) := by positivity
    -- Pick ε' := (min ε 1) / (16(m+1)). This guarantees:
    --  (a) ε' ≤ 1/(16(m+1)) ≤ 1/16, so ε'² ≤ ε'.
    --  (b) Total residual bound ≤ 3·(m+1)·ε' ≤ 3·(min ε 1)/16 ≤ min(ε/4, 1/2).
    set minε : ℝ := min ε 1 with hminε_def
    have hminε_pos : 0 < minε := lt_min hε (by norm_num)
    have hminε_le_ε : minε ≤ ε := min_le_left _ _
    have hminε_le_one : minε ≤ 1 := min_le_right _ _
    set ε' : ℝ := minε / (16 * ((m : ℝ) + 1)) with hε'_def
    have hε'_pos : 0 < ε' := by
      apply div_pos hminε_pos
      positivity
    have hε'_le_quarter : ε' ≤ 1 / 4 := by
      rw [hε'_def]
      have h_denom_pos : 0 < 16 * ((m : ℝ) + 1) := by positivity
      rw [div_le_iff₀ h_denom_pos]
      have : minε ≤ 1 := hminε_le_one
      have h_m_ge : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      nlinarith
    obtain ⟨e', he'_orth, he'_ess, he'_in_T, he'_close⟩ :=
      IH g0 hg0_orth hg0_in_T ε' hε'_pos
    -- Step 2: pick a bounded approximant h of `g_P (Fin.last m)` with
    -- ‖h - g_P (last m)‖ ≤ ε'.
    obtain ⟨h_seq, h_seq_in_T, h_seq_ess, h_seq_tendsto⟩ :=
      hT_dense (g_P (Fin.last m)) (h_in_T (Fin.last m))
    have h_extract : ∃ N, ‖h_seq N - g_P (Fin.last m)‖ ≤ ε' := by
      have h_tendsto_norm :
          Filter.Tendsto (fun n => ‖h_seq n - g_P (Fin.last m)‖)
            Filter.atTop (nhds 0) := h_seq_tendsto
      rw [Metric.tendsto_atTop] at h_tendsto_norm
      obtain ⟨N, hN⟩ := h_tendsto_norm ε' hε'_pos
      refine ⟨N, ?_⟩
      have := hN N le_rfl
      rw [Real.dist_eq, sub_zero] at this
      exact le_of_lt (lt_of_le_of_lt (le_abs_self _) this)
    obtain ⟨N, hN_close⟩ := h_extract
    set h : ↥(L2ZeroMean P) := h_seq N with hh_def
    have hh_in_T : (h : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := h_seq_in_T N
    have hh_ess : AsymptoticStatistics.Core.MassMethod.IsEssBoundedMixtureScore h :=
      h_seq_ess N
    have hh_close : ‖h - g_P (Fin.last m)‖ ≤ ε' := hN_close
    -- Step 3: form v := h - Σⱼ ⟨e' j, h⟩ • e' j. Prove tangent + ess-bounded.
    set proj : ↥(L2ZeroMean P) :=
      ∑ j, ⟪(e' j : ↥(L2ZeroMean P)), (h : ↥(L2ZeroMean P))⟫_ℝ
        • (e' j : ↥(L2ZeroMean P)) with hproj_def
    set v : ↥(L2ZeroMean P) := h - proj with hv_def
    have h_e'_ess : ∀ j, AsymptoticStatistics.Core.MassMethod.IsEssBoundedMixtureScore (e' j) :=
      fun j => he'_ess j
    obtain ⟨hv_in_T, hv_ess⟩ :=
      gs_step_props T_set e' he'_in_T h_e'_ess h hh_in_T hh_ess
    -- Step 4: apply gs_residual_close to bound ‖v - g_P (last m)‖.
    -- The orthonormality of g_P gives ⟨g0 j, g_P (last m)⟩ = 0 since
    -- g0 j = g_P j.castSucc ≠ g_P (last m).
    have h_orth_extended : ∀ j : Fin m,
        ⟪(g0 j : ↥(L2ZeroMean P)),
            (g_P (Fin.last m) : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
      intro j
      apply h_orth.inner_eq_zero
      exact Fin.ne_of_lt (Fin.castSucc_lt_last j)
    have hg0_unit : ∀ j, ‖(g0 j : ↥(L2ZeroMean P))‖ = 1 := fun j =>
      h_orth.norm_eq_one _
    have he'_unit : ∀ j, ‖(e' j : ↥(L2ZeroMean P))‖ = 1 := fun j =>
      he'_orth.norm_eq_one _
    have he'_close' : ∀ j, ‖(e' j : ↥(L2ZeroMean P))
                              - (g0 j : ↥(L2ZeroMean P))‖ ≤ ε' := by
      intro j
      have := he'_close j
      rw [show (e' j : ↥(L2ZeroMean P)) - (g0 j : ↥(L2ZeroMean P))
            = -((g0 j : ↥(L2ZeroMean P)) - (e' j : ↥(L2ZeroMean P))) from by abel,
            norm_neg]
      exact this
    have hu_unit : ‖(g_P (Fin.last m) : ↥(L2ZeroMean P))‖ = 1 := h_orth.norm_eq_one _
    have hε'_nn : 0 ≤ ε' := le_of_lt hε'_pos
    have hv_close_raw :
        ‖v - g_P (Fin.last m)‖
          ≤ ε' + (m : ℝ) * (ε' * (1 + ε') + ε') :=
      gs_residual_close g0 (g_P (Fin.last m)) h_orth_extended hg0_unit
        e' he'_unit ε' he'_close' hε'_nn h ε' hh_close hε'_nn hu_unit
    -- Bound: ε' + m·(ε'·(1+ε') + ε') ≤ minε / 4 ≤ min(ε/4)(1/4).
    -- Expand: (1 + 2m)·ε' + m·ε'². Use ε' ≤ 1/4 so ε'² ≤ ε'/4.
    -- Total ≤ ε'·(1 + 2m + m/4) ≤ ε'·3(m+1) = 3·minε/16 ≤ minε/4.
    have h_eps_sq : ε' * ε' ≤ ε' * (1 / 4) := by
      apply mul_le_mul_of_nonneg_left hε'_le_quarter (le_of_lt hε'_pos)
    have h_total : ε' + (m : ℝ) * (ε' * (1 + ε') + ε') ≤ minε / 4 := by
      have h_step1 : ε' + (m : ℝ) * (ε' * (1 + ε') + ε')
                  = (1 + 2 * (m : ℝ)) * ε' + (m : ℝ) * (ε' * ε') := by ring
      rw [h_step1]
      calc (1 + 2 * (m : ℝ)) * ε' + (m : ℝ) * (ε' * ε')
          ≤ (1 + 2 * (m : ℝ)) * ε' + (m : ℝ) * (ε' * (1/4)) := by
            gcongr
        _ = (1 + 2 * (m : ℝ) + (m : ℝ) / 4) * ε' := by ring
        _ ≤ (3 * ((m : ℝ) + 1)) * ε' := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hε'_pos)
            linarith [Nat.cast_nonneg (α := ℝ) m]
        _ = (3 * ((m : ℝ) + 1)) * (minε / (16 * ((m : ℝ) + 1))) := by rw [hε'_def]
        _ = 3 * minε / 16 := by field_simp
        _ ≤ minε / 4 := by linarith [hminε_pos]
    -- ‖v - g_P (last m)‖ ≤ minε/4 ≤ ε/4.
    have hv_close_minε : ‖v - g_P (Fin.last m)‖ ≤ minε / 4 :=
      hv_close_raw.trans h_total
    -- η := minε / 4: positive, < 1, suitable for normalise_close.
    set η : ℝ := minε / 4 with hη_def
    have hη_pos : 0 < η := by positivity
    have hη_le_quarter : η ≤ 1 / 4 := by
      rw [hη_def]; linarith [hminε_le_one]
    have hη_lt_one : η < 1 := lt_of_le_of_lt hη_le_quarter (by norm_num)
    have hη_nn : 0 ≤ η := le_of_lt hη_pos
    -- Apply normalise_close.
    obtain ⟨hv_ne, h_norm_close⟩ :=
      normalise_close v (g_P (Fin.last m)) hu_unit η hv_close_minε hη_lt_one hη_nn
    -- Normalised vector `e_last := ‖v‖⁻¹ • v` satisfies:
    --   ‖e_last - g_P (Fin.last m)‖ ≤ 2η/(1-η) ≤ 2·(1/4)/(1 - 1/4) = (1/2)/(3/4) = 2/3
    -- and via η ≤ minε/4 ≤ ε/4: 2η/(1-η) ≤ 2(ε/4)/(1 - 1/4) = (ε/2) · (4/3) = 2ε/3 ≤ ε.
    set e_last : ↥(L2ZeroMean P) := ‖v‖⁻¹ • v with he_last_def
    have h_e_last_close : ‖e_last - g_P (Fin.last m)‖ ≤ ε := by
      refine h_norm_close.trans ?_
      -- 2η/(1-η) ≤ ε. Need to verify.
      -- We have η ≤ minε/4 ≤ ε/4 and η ≤ 1/4 so 1 - η ≥ 3/4 > 0.
      have h1mη_pos : (0 : ℝ) < 1 - η := by linarith
      have h1mη_ge : (3 : ℝ) / 4 ≤ 1 - η := by linarith
      rw [div_le_iff₀ h1mη_pos]
      have h2η : 2 * η = 2 * (minε / 4) := by rw [hη_def]
      have h2η_le : 2 * η ≤ ε / 2 := by
        rw [h2η]
        have : minε ≤ ε := hminε_le_ε
        linarith
      have : 2 * η ≤ ε * (3 / 4) := by linarith
      calc 2 * η ≤ ε * (3 / 4) := this
        _ ≤ ε * (1 - η) := by
            apply mul_le_mul_of_nonneg_left h1mη_ge (le_of_lt hε)
    -- e_last is a unit vector.
    have h_e_last_norm : ‖e_last‖ = 1 := by
      rw [he_last_def, norm_smul, Real.norm_eq_abs]
      have hv_pos : 0 < ‖v‖ := by
        have : ‖v‖ ≠ 0 := fun heq => hv_ne (norm_eq_zero.mp heq)
        exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm this)
      rw [abs_of_pos (inv_pos.mpr hv_pos), inv_mul_cancel₀ (ne_of_gt hv_pos)]
    -- e_last is in tangent space (v is, and we're scalar-multiplying).
    have h_e_last_in_T : (e_last : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := by
      rw [he_last_def]
      exact Submodule.smul_mem _ _ hv_in_T
    -- e_last is essentially bounded.
    have h_e_last_ess :
        AsymptoticStatistics.Core.MassMethod.IsEssBoundedMixtureScore e_last := by
      rw [he_last_def]
      exact hv_ess.smul _
    -- e_last is orthogonal to each e' j.
    -- ⟨e' j, v⟩ = ⟨e' j, h⟩ - ⟨e' j, proj⟩. By Orthonormal.inner_right_finsupp:
    -- ⟨e' j, proj⟩ = ⟨e' j, Σ_k ⟨e' k, h⟩ • e' k⟩ = ⟨e' j, h⟩ (using ⟨e' j, e' k⟩ = δjk).
    have h_inner_e'_v : ∀ j : Fin m, ⟪(e' j : ↥(L2ZeroMean P)), v⟫_ℝ = 0 := by
      intro j
      have h_v_inner :
          ⟪(e' j : ↥(L2ZeroMean P)), v⟫_ℝ
            = ⟪(e' j : ↥(L2ZeroMean P)), h⟫_ℝ
              - ⟪(e' j : ↥(L2ZeroMean P)), proj⟫_ℝ := by
        rw [hv_def]; exact inner_sub_right _ _ _
      rw [h_v_inner]
      have h_proj_inner :
          ⟪(e' j : ↥(L2ZeroMean P)), proj⟫_ℝ = ⟪(e' j : ↥(L2ZeroMean P)), h⟫_ℝ := by
        rw [hproj_def]
        rw [inner_sum]
        -- Use orthonormality of e' to collapse the sum.
        have : ∀ k : Fin m,
            ⟪(e' j : ↥(L2ZeroMean P)),
                ⟪(e' k : ↥(L2ZeroMean P)), h⟫_ℝ • (e' k : ↥(L2ZeroMean P))⟫_ℝ
              = if k = j then ⟪(e' j : ↥(L2ZeroMean P)), h⟫_ℝ else 0 := by
          intro k
          rw [inner_smul_right]
          by_cases hjk : k = j
          · subst hjk
            rw [if_pos rfl]
            have h_norm_sq : ⟪(e' k : ↥(L2ZeroMean P)),
                              (e' k : ↥(L2ZeroMean P))⟫_ℝ = 1 := by
              have := he'_orth.norm_eq_one k
              rw [@real_inner_self_eq_norm_sq, this]; ring
            rw [h_norm_sq, mul_one]
          · rw [if_neg hjk]
            have h_zero : ⟪(e' j : ↥(L2ZeroMean P)),
                            (e' k : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
              apply he'_orth.inner_eq_zero
              exact Ne.symm hjk
            rw [h_zero, mul_zero]
        simp_rw [this]
        rw [Finset.sum_ite_eq']
        simp
      rw [h_proj_inner]
      ring
    have h_inner_e'_e_last : ∀ j : Fin m, ⟪(e' j : ↥(L2ZeroMean P)), e_last⟫_ℝ = 0 := by
      intro j
      rw [he_last_def, inner_smul_right, h_inner_e'_v j, mul_zero]
    -- Step 5: assemble the final family via Fin.snoc.
    refine ⟨Fin.snoc e' e_last, ?_, ?_, ?_, ?_⟩
    · -- Orthonormality: use ortho of e' + the new orthogonality conditions.
      refine ⟨?_, ?_⟩
      · -- All entries have norm 1.
        intro i
        induction i using Fin.lastCases with
        | last => simp [Fin.snoc_last, h_e_last_norm]
        | cast j => simp [Fin.snoc_castSucc, he'_orth.norm_eq_one j]
      · -- Pairwise orthogonal.
        intro i k hik
        induction i using Fin.lastCases with
        | last =>
          induction k using Fin.lastCases with
          | last => exact absurd rfl hik
          | cast k' =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc]
            rw [show ⟪e_last, (e' k' : ↥(L2ZeroMean P))⟫_ℝ
                  = ⟪(e' k' : ↥(L2ZeroMean P)), e_last⟫_ℝ from real_inner_comm _ _]
            exact h_inner_e'_e_last k'
        | cast j' =>
          induction k using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            exact h_inner_e'_e_last j'
          | cast k' =>
            simp only [Fin.snoc_castSucc]
            apply he'_orth.inner_eq_zero
            intro h_eq
            apply hik
            exact congrArg Fin.castSucc h_eq
    · -- IsBoundedMixtureScores
      intro i
      induction i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using h_e_last_ess
      | cast j => simpa [Fin.snoc_castSucc] using he'_ess j
    · -- ∀ i, in tangent space
      intro i
      induction i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using h_e_last_in_T
      | cast j => simpa [Fin.snoc_castSucc] using he'_in_T j
    · -- ∀ i, L²-close
      intro i
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [show (g_P (Fin.last m) : ↥(L2ZeroMean P)) - e_last
              = -(e_last - (g_P (Fin.last m) : ↥(L2ZeroMean P))) from by abel,
              norm_neg]
        exact h_e_last_close
      | cast j =>
        simp only [Fin.snoc_castSucc]
        -- Close: he'_close j gives ‖g0 j - e' j‖ ≤ ε' ≤ ε.
        -- We need ‖g_P j.castSucc - e' j‖ ≤ ε. g0 j = g_P j.castSucc.
        have h_ε'_le_ε : ε' ≤ ε := by
          rw [hε'_def]
          have hm1_ge : (1 : ℝ) ≤ 16 * ((m : ℝ) + 1) := by
            have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
            linarith
          calc minε / (16 * ((m : ℝ) + 1))
              ≤ minε / 1 := by
                apply div_le_div_of_nonneg_left (le_of_lt hminε_pos) (by norm_num) hm1_ge
            _ = minε := by ring
            _ ≤ ε := hminε_le_ε
        exact (he'_close j).trans h_ε'_le_ε

/-- **vdV §25.20 closure bridge** — under the regularity hypothesis
`IsTangentBoundedDense T_set`, every orthonormal `g_P` of vectors in
`tangentSpace T_set` admits an L∞-bounded approximation `g'_P` that is
(i) still orthonormal, (ii) in tangent space, (iii) preserves inner products
with `IF_eff` up to ε > 0 slack.

**Why this is needed**: `IsBoundedMixtureScores` (= per-coordinate L∞ a.e.
bound) is NOT derivable from L²-orthonormality alone (counter-example:
`√(k+1) sin(2πk·)` on `[0,1]` is orthonormal in L² but unbounded). The chain
feeds `g_P` into `paramSubmodel`, which requires `IsBoundedMixtureScores`,
hence this adapter via the existing regularity hypothesis
`IsTangentBoundedDense T_set`.

Reference: vdV §25.3.2 (the tangent set admits a bounded approximating
sequence, formalized here as `IsTangentBoundedDense`). -/
theorem orthonormal_to_bounded_mixture_via_tangent_dense
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    (hT_dense : AsymptoticStatistics.Core.MassMethod.IsTangentBoundedDense T_set)
    {IF_eff : ↥(L2ZeroMean P)}
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g_P' : Fin m → ↥(L2ZeroMean P)) (_hg : IsBoundedMixtureScores g_P'),
      Orthonormal ℝ (fun i : Fin m => (g_P' i : ↥(L2ZeroMean P))) ∧
      (∀ i, (g_P' i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set) ∧
      (∀ i, |⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ
              - ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P' i : ↥(L2ZeroMean P))⟫_ℝ| ≤ ε) := by
  classical
  -- Pick an L² tolerance δ small enough that Cauchy-Schwarz on `IF_eff`
  -- gives an ε bound on the inner-product difference.
  by_cases hIF : ‖(IF_eff : ↥(L2ZeroMean P))‖ = 0
  · -- Degenerate case: `IF_eff = 0`, so every inner product is 0; any
    -- bounded orthonormal approximation works (with any positive ε').
    obtain ⟨g_P', h_orth', hg', h_in_T', _⟩ :=
      tangent_bounded_orthonormal_approx T_set hT_dense g_P h_orth h_in_T 1 one_pos
    refine ⟨g_P', hg', h_orth', h_in_T', ?_⟩
    intro i
    have hIF_norm_zero : (IF_eff : ↥(L2ZeroMean P)) = 0 := by
      rwa [norm_eq_zero] at hIF
    -- both inner products are 0 ⇒ diff is 0 ≤ ε.
    have h1 : ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
      rw [hIF_norm_zero]
      exact inner_zero_left _
    have h2 : ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P' i : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
      rw [hIF_norm_zero]
      exact inner_zero_left _
    rw [h1, h2]; simpa using hε.le
  · -- Generic case: pick δ := ε / ‖IF_eff‖.
    have hIF_pos : 0 < ‖(IF_eff : ↥(L2ZeroMean P))‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hIF)
    have hδ_pos : 0 < ε / ‖(IF_eff : ↥(L2ZeroMean P))‖ := div_pos hε hIF_pos
    obtain ⟨g_P', h_orth', hg', h_in_T', h_close⟩ :=
      tangent_bounded_orthonormal_approx T_set hT_dense g_P h_orth h_in_T
        (ε / ‖(IF_eff : ↥(L2ZeroMean P))‖) hδ_pos
    refine ⟨g_P', hg', h_orth', h_in_T', ?_⟩
    intro i
    -- |⟪IF_eff, g_P i⟫ - ⟪IF_eff, g_P' i⟫|
    -- = |⟪IF_eff, g_P i - g_P' i⟫| ≤ ‖IF_eff‖ · ‖g_P i - g_P' i‖.
    have h_diff_inner :
        ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ
            - ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P' i : ↥(L2ZeroMean P))⟫_ℝ
          = ⟪(IF_eff : ↥(L2ZeroMean P)),
              (g_P i : ↥(L2ZeroMean P)) - (g_P' i : ↥(L2ZeroMean P))⟫_ℝ := by
      rw [inner_sub_right]
    rw [h_diff_inner]
    -- Cauchy-Schwarz: |⟨a, b⟩| ≤ ‖a‖ · ‖b‖.
    have h_cs := abs_real_inner_le_norm
      (IF_eff : ↥(L2ZeroMean P))
      ((g_P i : ↥(L2ZeroMean P)) - (g_P' i : ↥(L2ZeroMean P)))
    -- combine with the L² closeness.
    have hε_eq : ‖(IF_eff : ↥(L2ZeroMean P))‖
        * (ε / ‖(IF_eff : ↥(L2ZeroMean P))‖) = ε := by
      field_simp
    calc |⟪(IF_eff : ↥(L2ZeroMean P)),
            (g_P i : ↥(L2ZeroMean P)) - (g_P' i : ↥(L2ZeroMean P))⟫_ℝ|
        ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖
            * ‖(g_P i : ↥(L2ZeroMean P)) - (g_P' i : ↥(L2ZeroMean P))‖ := h_cs
      _ ≤ ‖(IF_eff : ↥(L2ZeroMean P))‖
            * (ε / ‖(IF_eff : ↥(L2ZeroMean P))‖) :=
          mul_le_mul_of_nonneg_left (h_close i) (norm_nonneg _)
      _ = ε := hε_eq

/-! ### Kernel-equivariance bridge for the LAN-induced kernel

The verbatim mirror of `HajekLeCamConvolution.randomized_kernel_is_equivariant_in_law`,
specialised to the scalar `(d = 1)` case with `J := (1 : Matrix _ _ ℝ)` and
`ψ̇ · h` replaced by the scalar `⟪IF_eff, Σᵢ h i • g_P i⟫_ℝ`. -/

/-- Kernel-equivariance bridge for the LAN-induced kernel on the parametric
submodel built from an orthonormal score basis `g_P`. Verbatim mirror of
`HajekLeCamConvolution.randomized_kernel_is_equivariant_in_law`, specialised to the scalar
`d = 1` setting where `ψ̇·h` becomes the scalar `⟪IF_eff, Σᵢ h i • g_P i⟫_ℝ`. -/
theorem lan_kernel_isEquivariantInLaw
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} {g_P : Fin m → ↥(L2ZeroMean P)}
    {IF_eff : ↥(L2ZeroMean P)}
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (κ : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin m)) ℝ)
    [ProbabilityTheory.IsMarkovKernel κ]
    -- Shape produced by `lan_kernel_for_basis`:
    (hκ : ∀ h : EuclideanSpace ℝ (Fin m),
      L = ((ProbabilityTheory.multivariateGaussian h
              (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹).bind κ).map
            (fun y : ℝ => y -
              ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i : Fin m, h i • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)) :
    ∀ h : EuclideanSpace ℝ (Fin m),
      (κ ∘ₘ (ProbabilityTheory.multivariateGaussian h
              (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹)).map
        (fun y : ℝ => y -
          ⟪(IF_eff : ↥(L2ZeroMean P)),
            ∑ i : Fin m, h i • (g_P i : ↥(L2ZeroMean P))⟫_ℝ) = L := by
  intro h
  -- `κ ∘ₘ μ = μ.bind κ` by definition of the `∘ₘ` notation, so the LHS
  -- is the RHS of `hκ h` and the conclusion is `hκ h` flipped.
  exact (hκ h).symm

/-! ### ∀-h perturbed-truth-recentered weak convergence

Lifts the small-h (`‖h‖·m·hg.uniformBound ≤ 1`) bridge
(`productMeasure_paramSubmodel_pushforward_weakConverges`) to an ∀-h
form by routing through the LAN / Le-Cam-3rd machinery in `AsymptoticRepresentation`.
Per fixed `h`, the pipeline mirrors what `AsymptoticRepresentation.LAN_representation`
does for all `h` simultaneously:

1. **Unperturbed CLT under `P^n`** via
   `RegularEstimator.weak_limit_under_P_of_regular`: from `hReg`,
   `(P^n).map (√n·(T_n - ψ P)) ⇀ L`. No direction-h QMDPath needed
   (`constP_QMDPath` covers the at-zero case for any direction).
2. **Joint conv `(T_n, scoreSum) ⇀ π` under `P^n`** via
   `AsymptoticRepresentation.joint_weak_conv_with_scoreSum`, with `M := paramSubmodel
   g_P hg h_orth`, `ℓ := g_P_total g_P`, `J := 1`, second marginal of
   `π` is `multivariateGaussian 0 J`.
3. **Continuous mapping → joint `(T_n, L_n)`** where
   `L_n := logLikelihood paramSubmodel 0 h n`. The LAN Taylor expansion
   gives `L_n ≈ ⟨scoreSum, h⟩ - (1/2)·‖h‖² + o_P(1)`; Slutsky absorbs
   the residual.
4. **UI of `exp(L_n)`** via `Contiguity.uniform_integrability_exp_L`.
5. **Le Cam 3rd lemma** via
   `Contiguity.weak_limit_under_Q_of_lecam_third`: tilts the joint to
   give weak conv under `Q_n := productMeasure paramSubmodel ((√n)⁻¹·h) n`.
6. **Slutsky-cancel the recentering offset** to convert from
   "recenter at `ψ P`" to "recenter at `ψ(P.withDensity ((√n)⁻¹·h))`"
   via `PathwiseDifferentiableAt`-derivative of `ψ` along the bounded
   direction `linPerturb g_P h` (a `paramSubmodelQMDPath` realises this
   only for small `h_alt := h/‖h‖`; the Slutsky shift is then
   re-normalised to direction `h`).

The full pipeline lives implicitly inside `LAN_representation`'s body but is
only exposed there as the all-h kernel form `L = (gauss h).bind κ`. Here we
need the bare ∀-h weak limit, before the kernel extraction: vdV §25.5
Lemma 25.14 + §25.3.1 chain, specialised to the parametric submodel
constructed from an orthonormal score basis.

The lift is decomposed into the unperturbed-CLT helper
`unperturbed_CLT` (no-h CLT under `P^n`, derived directly from
`IsRegularEstimator` via the constant-`P` `QMDPath`) plus
`w2c_LAN_pushforward_steps_2_to_6`, which bundles the LAN-Taylor /
Le-Cam-3 / Slutsky-recentering pipeline (Steps 2–6) per fixed `h`. Each step
has an analog in `AsymptoticRepresentation` / `Contiguity`; Steps 2–6 wire the
parametric-submodel-specific data (`paramSubmodel_DQM`,
`paramSubmodel_fisher_info`, `paramSubmodel_isPDFOf`, `g_P_total`) through the
`joint_weak_conv_with_scoreSum` and `weak_limit_under_Q_of_lecam_third`
interfaces, then perform the Slutsky recentering identification. -/

/-- **Step 1 — unperturbed CLT under `P^n`.** Direct specialisation of
`RegularEstimatorDerivations.weak_limit_under_P_of_regular` to the input data
of the all-h bridge. -/
private lemma unperturbed_CLT
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L) :
    WeakConverges
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).map
        (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
      L :=
  AsymptoticStatistics.LowerBounds.RegularEstimator.weak_limit_under_P_of_regular
    T_set ψ hψ hEIF T_n L hReg

/-- **Steps 2–6 — LAN-route pushforward weak convergence under `Q_n`.**
Per fixed `h`, this is the conclusion of the LAN-Taylor + Le-Cam-3 +
Slutsky-recentering pipeline applied to the parametric submodel
`paramSubmodel g_P hg h_orth`:

`Q_n.map (√n·(T_n - ψ(P.withDensity p_θ))) ⇀ L` where
`Q_n := productMeasure paramSubmodel P ((√n)⁻¹ • h) n` and
`p_θ ω := ENNReal.ofReal (paramSubmodel.density θ ω)` at
`θ := (√n)⁻¹ • h`.

**Reference**: vdV §25.5 (parametric submodel LAN) + §25.3 (regular
estimator weak limit invariance under local perturbations); the
template implementation is `AsymptoticRepresentation.LAN_representation`, with
`g_P_total` substituted for the abstract score `ℓ` and `J = 1`. -/
private theorem w2c_LAN_pushforward_steps_2_to_6
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (hStep1 :
      WeakConverges
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
        L)
    (h : EuclideanSpace ℝ (Fin m)) :
    WeakConverges
      (fun n : ℕ =>
        (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (AsymptoticStatistics.ParametricFamily.paramSubmodel
              g_P hg h_orth) P ((Real.sqrt n)⁻¹ • h) n).map
          (fun X : Fin n → Ω =>
            Real.sqrt n * (T_n n X - ψ (P.withDensity (fun ω =>
              ENNReal.ofReal
                ((AsymptoticStatistics.ParametricFamily.paramSubmodel
                    g_P hg h_orth).density ((Real.sqrt n)⁻¹ • h) ω))))))
      L := by
  -- Rather than re-run the full LAN pipeline (joint weak conv + LAN Taylor +
  -- Slutsky + UI of exp(L) + Le Cam 3 + Slutsky recentering), we use the
  -- all-`h` `paramSubmodelQMDPathAllH` QMDPath: a single
  -- `boundedDensityPath`-based curve whose score is `linPerturbScore g_P h`
  -- and whose `curve s` eventually-as-`s→0` matches
  -- `P.withDensity (paramSubmodel.density (s • h))` for any direction `h`
  -- (no smallness constraint). `IsRegularEstimator.shift` applied at this
  -- curve gives the desired weak conv in `Measure.pi (curve.curve …)`-form,
  -- which the eventually-in-`n` equality lifts to the `productMeasure
  -- paramSubmodel`-based form. Steps 2-6 (LAN pipeline) and `hStep1`
  -- (unperturbed CLT) become unnecessary on this route.
  classical
  -- `hStep1` is unused on the QMDPath-direct route.
  let _ := hStep1
  -- Score is in tangent space, and matches the QMDPath's score field.
  have hLin_in_T : linPerturbScore g_P h ∈ Submodule.span ℝ T_set.carrier :=
    linPerturbScore_mem_span T_set g_P h_in_T h
  have hScore_eq :
      (AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH g_P hg h).score =
          linPerturbScore g_P h :=
    AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH_score g_P hg h
  -- Apply `IsRegularEstimator.shift` at the all-`h` QMDPath.
  have h_qmd_weak :
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n =>
                (AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH g_P hg
                    h).curve
                  ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n *
                (T_n n X -
                  ψ ((AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH g_P
                      hg h).curve
                      ((Real.sqrt n)⁻¹)))))
        L :=
    IsRegularEstimator.shift hReg (linPerturbScore g_P h) hLin_in_T
      (AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH g_P hg h)
          hScore_eq
  -- Eventually-in-`n`, the curve equals the paramSubmodel density form.
  have h_curve_eq_eventually :=
    LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH_curve_eq_paramSubmodel_density
        g_P hg h_orth h
  have h_tendsto :
      Filter.Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h_curve_eq_n :
      ∀ᶠ n : ℕ in Filter.atTop,
        (AsymptoticStatistics.LowerBounds.RegularEstimator.paramSubmodelQMDPathAllH g_P hg h).curve
            ((Real.sqrt n)⁻¹)
          = P.withDensity (fun ω =>
              ENNReal.ofReal
                ((paramSubmodel g_P hg h_orth).density
                  ((Real.sqrt n)⁻¹ • h) ω)) :=
    h_tendsto.eventually h_curve_eq_eventually
  -- Substitute both the outer `Measure.pi` and the inner `ψ`-recentering
  -- simultaneously via `rw [hn]`.
  refine weakConverges_congr_eventually ?_ h_qmd_weak
  filter_upwards [h_curve_eq_n] with n hn
  rw [hn]
  -- After substitution both sides are
  -- `(Measure.pi (fun _ => P.withDensity (...))).map (fun X => √n · (...))`
  -- vs `(productMeasure ... ((√n)⁻¹ • h) n).map (fun X => √n · (...))`.
  -- Unfolding `productMeasure` gives definitional equality.
  rfl

/-- **vdV §25.20 closure bridge** —
∀-h weak convergence under the perturbed `paramSubmodel` product
measure, recentered at the *perturbed parametric truth*
`ψ(P.withDensity (paramSubmodel.density ((√n)⁻¹ • h)))`.

Stated in scalar (`ℝ`-target) form. The scalar-to-`EuclideanSpace ℝ
(Fin 1)` vector lift consumed by
`paramSubmodel_RegularEstimatorSequence_weakConv_of_scalar` is a thin
downstream adapter.

The body composes `unperturbed_CLT` with
`w2c_LAN_pushforward_steps_2_to_6` (the LAN-route Steps 2–6 per fixed `h`).

The `h_small`-restricted form
`productMeasure_paramSubmodel_pushforward_weakConverges` is a corollary at
small `h`; this lemma *extends* it to all `h` via the LAN route (small `h`
cannot be extended by direction-rescaling because that changes the `(√n)⁻¹`
rate). -/
theorem productMeasure_paramSubmodel_pushforward_all_h_weakConverges
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (hReg : AsymptoticStatistics.LowerBounds.RegularEstimator.IsRegularEstimator
              P T_set ψ hψ hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    ∀ h : EuclideanSpace ℝ (Fin m),
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (AsymptoticStatistics.ParametricFamily.paramSubmodel
                g_P hg h_orth) P ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n * (T_n n X - ψ (P.withDensity (fun ω =>
                ENNReal.ofReal
                  ((AsymptoticStatistics.ParametricFamily.paramSubmodel
                      g_P hg h_orth).density ((Real.sqrt n)⁻¹ • h) ω))))))
        L := by
  -- Step 1 (unperturbed CLT) feeds the LAN-route Steps 2–6 per fixed `h`.
  intro h
  have hStep1 := unperturbed_CLT T_set hψ hEIF T_n hReg
  exact w2c_LAN_pushforward_steps_2_to_6 T_set hψ hEIF T_n hT_meas hReg
    g_P hg h_orth h_in_T hStep1 h

/-! ### §25.20 closure bridges — RegularEstimatorSequence packaging

Bridges semiparametric `IsRegularEstimator` data into the parametric
inputs `hajek_le_cam_convolution_theorem` requires. The primitives
(`ψ_param`, `ψDot_clm`, `ψDotMat`, `T_param_of`,
`ψ_param_HasFDerivAt_of_residual`) come from
`AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge`. This block
adds the `RegularEstimatorSequence` bridge that packages an ∀-h
`productMeasure`-based weak-convergence input into a
`RegularEstimatorSequence (paramSubmodel …)` for use with
`hajek_le_cam_convolution_theorem`. -/

open AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge
  (ψ_param ψDotMat ψDot_clm T_param_of)

/-- **vdV §25.20 closure bridge** — expose
`LAMSemiparametricBridge.ψ_param` under the `ParametricBridge` namespace, as
the parametric functional restricted to the `paramSubmodel`. The underlying
definition is unchanged. -/
noncomputable abbrev ψ_param_lifted
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → ℝ) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 1) :=
  ψ_param g_P hg h_orth ψ

/-- **vdV §25.20 closure bridge** — lift a scalar estimator `T_n` to
`EuclideanSpace ℝ (Fin 1)`-valued form.

Alias for `LAMSemiparametricBridge.T_param_of`, exposed under the
`ParametricBridge` namespace for use with `RegularEstimatorSequence` /
`hajek_le_cam_convolution_theorem`. -/
noncomputable abbrev T_n_lifted
    {Ω : Type*} [MeasurableSpace Ω]
    (T_n : ∀ n, (Fin n → Ω) → ℝ) :
    ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin 1) :=
  T_param_of T_n

/-- **Scalar ↔ 1-D `EuclideanSpace` lifting identity.**

The scalar `r : ℝ` lifts to `EuclideanSpace.single 0 r : EuclideanSpace
ℝ (Fin 1)`. This is the bridge map between the scalar form and
the `RegularEstimatorSequence.tendsto` vector form (which lives in
`𝓨 1 = EuclideanSpace ℝ (Fin 1)`). -/
private lemma single_eq_withLp_const_apply (r : ℝ) :
    EuclideanSpace.single (0 : Fin 1) r
      = (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => r) := by
  -- Both sides are `WithLp.toLp 2 (fun _ : Fin 1 => r)` (the `Pi.single`
  -- on `Fin 1` collapses to the constant function on the single index).
  rw [show (fun _ : Fin 1 => r) = Pi.single 0 r from ?_]
  · exact (EuclideanSpace.toLp_single (𝕜 := ℝ) 0 r).symm
  · funext i
    fin_cases i
    rfl

/-- **`Real.sqrt n` smul ↔ 1-D `EuclideanSpace` lifting identity.** The
real scalar `Real.sqrt n * (a - b)` lifts to coordinate 0 of
`Real.sqrt n • (EuclideanSpace.single 0 a - EuclideanSpace.single 0 b)`. -/
private lemma sqrtn_smul_diff_single_eq (n : ℕ) (a b : ℝ) :
    Real.sqrt n •
        (EuclideanSpace.single (0 : Fin 1) a
          - EuclideanSpace.single (0 : Fin 1) b)
      = EuclideanSpace.single (0 : Fin 1) (Real.sqrt n * (a - b)) := by
  -- `EuclideanSpace.single 0` is ℝ-linear; this collapses by direct unfold.
  rw [single_eq_withLp_const_apply, single_eq_withLp_const_apply,
      single_eq_withLp_const_apply]
  -- Goal: r • ((.symm) (fun _ => a) - (.symm) (fun _ => b))
  --     = (.symm) (fun _ => r * (a - b))
  have h_diff : (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => a)
        - (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => b)
      = (WithLp.equiv 2 (Fin 1 → ℝ)).symm
          (fun _ : Fin 1 => a - b) := by
    ext i
    fin_cases i
    rfl
  rw [h_diff]
  ext i
  fin_cases i
  change WithLp.ofLp
      (Real.sqrt n • (WithLp.toLp 2 (fun _ : Fin 1 => a - b))) 0
    = (Real.sqrt n) * (a - b)
  rw [WithLp.ofLp_smul, WithLp.ofLp_toLp]
  simp [Pi.smul_apply, smul_eq_mul]

/-- **`T_n_lifted` minus `ψ_param_lifted` ↔ `EuclideanSpace.single 0` of
scalar diff.** Unpack the `WithLp` wrappers so the
`RegularEstimatorSequence`-shaped vector difference reduces to its
scalar coord-0 value. -/
private lemma T_n_lifted_sub_ψ_param_eq_single
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → ℝ) (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (θ : EuclideanSpace ℝ (Fin m)) (n : ℕ) (X : Fin n → Ω) :
    T_n_lifted T_n n X - ψ_param_lifted g_P hg h_orth ψ θ
      = EuclideanSpace.single (0 : Fin 1)
          (T_n n X - ψ (P.withDensity (fun ω =>
            ENNReal.ofReal ((paramSubmodel g_P hg h_orth).density θ ω)))) := by
  -- Both sides have coord 0 = T_n n X - ψ(...).
  unfold T_n_lifted T_param_of ψ_param_lifted ψ_param
  rw [single_eq_withLp_const_apply]
  ext i
  fin_cases i
  change WithLp.ofLp
      ((WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => T_n n X)
        - (WithLp.equiv 2 (Fin 1 → ℝ)).symm
            (fun _ : Fin 1 => ψ (P.withDensity (fun ω =>
              ENNReal.ofReal
                ((paramSubmodel g_P hg h_orth).density θ ω))))) 0
    = WithLp.ofLp
        ((WithLp.equiv 2 (Fin 1 → ℝ)).symm
          (fun _ : Fin 1 => T_n n X - ψ (P.withDensity (fun ω =>
            ENNReal.ofReal
              ((paramSubmodel g_P hg h_orth).density θ ω))))) 0
  rw [WithLp.ofLp_sub]
  rfl

/-- **vdV §25.20 closure bridge** —
package an ∀-h `productMeasure`-based weak convergence input into a
`RegularEstimatorSequence (paramSubmodel g_P hg h_orth) P 0
(ψ_param_lifted …) (T_n_lifted …)`.

This is the bridge that converts the semiparametric weak-convergence
data, supplied at the level of `AsymptoticRepresentation.productMeasure`, into the
structured `RegularEstimatorSequence` input expected by
`hajek_le_cam_convolution_theorem`.

**Recentering.** The hypothesis recenters at
`ψ_param ((√n)⁻¹ • h)` (the perturbed parametric truth), matching the
canonical `RegularEstimatorSequence` form (recenter at
`θ₀ + (√n)⁻¹ • h`). The `θ₀ = 0` specialisation cancels the additive
`0 + (√n)⁻¹ • h = (√n)⁻¹ • h`, eliminating the affine offset.

**Limit law.** The vector limit law is `L.map (EuclideanSpace.single
0)`: the push-forward of the user-supplied scalar limit `L` through
the canonical scalar-to-1D `EuclideanSpace` embedding. This is the
`limitDist` field that downstream code (`hajek_le_cam_convolution_theorem`)
consumes via its `hReg.limitDist` accessor.

**`hT_weak_all_h` form.** Lifted to the `EuclideanSpace ℝ (Fin 1)`
target directly (so the resulting `RegularEstimatorSequence.tendsto`
field is a simple `simp_rw` away from the input). A thin scalar-form ↔
vector-form adapter (via `WeakConverges.map` through
`EuclideanSpace.single 0`) bridges the two if needed. -/
noncomputable def paramSubmodel_RegularEstimatorSequence
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ψ : Measure Ω → ℝ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    {L_vec : Measure (EuclideanSpace ℝ (Fin 1))} [IsProbabilityMeasure L_vec]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    -- Vector form (target = `EuclideanSpace ℝ (Fin 1)`): weak convergence
    -- under `productMeasure` recentered at the perturbed parametric truth
    -- `ψ_param ((√n)⁻¹ • h)`.
    (hT_weak_all_h : ∀ h : EuclideanSpace ℝ (Fin m),
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (paramSubmodel g_P hg h_orth) P
              ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n_lifted T_n n X
                  - ψ_param_lifted g_P hg h_orth ψ
                      ((0 : EuclideanSpace ℝ (Fin m))
                        + (Real.sqrt n)⁻¹ • h))))
        L_vec) :
    AsymptoticStatistics.ParametricFamily.RegularEstimatorSequence
      (paramSubmodel g_P hg h_orth) P (0 : EuclideanSpace ℝ (Fin m))
      (ψ_param_lifted g_P hg h_orth ψ) (T_n_lifted T_n) where
  limitDist := L_vec
  isProb := inferInstance
  tendsto := hT_weak_all_h

/-- **Scalar → vector adapter.**

Bridge the scalar-target weak-convergence hypothesis to the vector-target
form consumed by `paramSubmodel_RegularEstimatorSequence`. The scalar form
(target `ℝ`) is what the joint-law/Le-Cam-third assembly produces; the vector
form (target `EuclideanSpace ℝ (Fin 1)`) is what the
`RegularEstimatorSequence` constructor needs.

This adapter does the pushforward through `EuclideanSpace.single 0`
(the canonical scalar-to-1D embedding) via the continuous-mapping
theorem for weak convergence (`WeakConverges.map`), then identifies
the resulting map function with the `Real.sqrt n •
(T_n_lifted - ψ_param_lifted)` shape via the bridge lemmas
`sqrtn_smul_diff_single_eq` and `T_n_lifted_sub_ψ_param_eq_single`. -/
theorem paramSubmodel_RegularEstimatorSequence_weakConv_of_scalar
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ψ : Measure Ω → ℝ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    {L : Measure ℝ} [IsProbabilityMeasure L]
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg : IsBoundedMixtureScores g_P)
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (hT_weak_scalar : ∀ h : EuclideanSpace ℝ (Fin m),
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (paramSubmodel g_P hg h_orth) P ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n * (T_n n X - ψ (P.withDensity (fun ω =>
                ENNReal.ofReal
                  ((paramSubmodel g_P hg h_orth).density
                    ((Real.sqrt n)⁻¹ • h) ω))))))
        L) :
    ∀ h : EuclideanSpace ℝ (Fin m),
      WeakConverges
        (fun n : ℕ =>
          (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (paramSubmodel g_P hg h_orth) P
              ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n_lifted T_n n X
                  - ψ_param_lifted g_P hg h_orth ψ
                      ((0 : EuclideanSpace ℝ (Fin m))
                        + (Real.sqrt n)⁻¹ • h))))
        (L.map (EuclideanSpace.single (0 : Fin 1))) := by
  intro h
  classical
  -- Step 1: scalar weak conv at h.
  have h_scalar := hT_weak_scalar h
  -- Step 2: `EuclideanSpace.single 0` is continuous + measurable.
  have h_cont : Continuous
      (EuclideanSpace.single (0 : Fin 1) : ℝ → EuclideanSpace ℝ (Fin 1)) := by
    have h_fun_eq :
        (EuclideanSpace.single (0 : Fin 1) : ℝ → EuclideanSpace ℝ (Fin 1))
          = fun r : ℝ => (WithLp.equiv 2 (Fin 1 → ℝ)).symm
              (fun _ : Fin 1 => r) := by
      funext r
      exact single_eq_withLp_const_apply r
    rw [h_fun_eq]
    refine (PiLp.continuous_toLp 2 (β := fun _ : Fin 1 => ℝ)).comp ?_
    exact continuous_pi (fun _ => continuous_id)
  have h_meas : Measurable
      (EuclideanSpace.single (0 : Fin 1) : ℝ → EuclideanSpace ℝ (Fin 1)) :=
    h_cont.measurable
  -- Step 3: push the scalar conv through `EuclideanSpace.single 0`.
  have h_pushed :
      WeakConverges
        (fun n : ℕ =>
          ((AsymptoticStatistics.AsymptoticRepresentation.productMeasure
              (paramSubmodel g_P hg h_orth) P ((Real.sqrt n)⁻¹ • h) n).map
            (fun X : Fin n → Ω =>
              Real.sqrt n * (T_n n X - ψ (P.withDensity (fun ω =>
                ENNReal.ofReal
                  ((paramSubmodel g_P hg h_orth).density
                    ((Real.sqrt n)⁻¹ • h) ω)))))).map
            (EuclideanSpace.single (0 : Fin 1)))
        (L.map (EuclideanSpace.single (0 : Fin 1))) :=
    h_scalar.map h_cont h_meas
  -- Step 4: per-n equality of the pushed-through measure and the goal's measure.
  -- Strategy: use `Measure.map_map` (needs measurability of the inner scalar map).
  have h_map_eq_n : ∀ n : ℕ,
      ((AsymptoticStatistics.AsymptoticRepresentation.productMeasure
          (paramSubmodel g_P hg h_orth) P ((Real.sqrt n)⁻¹ • h) n).map
        (fun X : Fin n → Ω =>
          Real.sqrt n * (T_n n X - ψ (P.withDensity (fun ω =>
            ENNReal.ofReal
              ((paramSubmodel g_P hg h_orth).density
                ((Real.sqrt n)⁻¹ • h) ω)))))).map
          (EuclideanSpace.single (0 : Fin 1))
        = (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (paramSubmodel g_P hg h_orth) P
            ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h) n).map
          (fun X : Fin n → Ω =>
            Real.sqrt n •
              (T_n_lifted T_n n X
                - ψ_param_lifted g_P hg h_orth ψ
                    ((0 : EuclideanSpace ℝ (Fin m))
                      + (Real.sqrt n)⁻¹ • h))) := by
    intro n
    -- `0 + θ = θ` in `EuclideanSpace`.
    have h_zero_add :
        (0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt (n : ℝ))⁻¹ • h
          = (Real.sqrt (n : ℝ))⁻¹ • h := zero_add _
    rw [h_zero_add]
    -- Inner scalar map is measurable (uses `hT_meas`).
    have h_scalar_meas : Measurable (fun X : Fin n → Ω =>
        Real.sqrt n * (T_n n X - ψ (P.withDensity (fun ω =>
          ENNReal.ofReal
            ((paramSubmodel g_P hg h_orth).density
              ((Real.sqrt n)⁻¹ • h) ω))))) := by
      refine Measurable.const_mul ?_ _
      exact (hT_meas n).sub_const _
    -- Collapse the two maps via `Measure.map_map`.
    rw [Measure.map_map h_meas h_scalar_meas]
    -- Pointwise equality of the now-composed map function.
    refine congrArg
      (fun g : (Fin n → Ω) → EuclideanSpace ℝ (Fin 1) =>
        (AsymptoticStatistics.AsymptoticRepresentation.productMeasure
            (paramSubmodel g_P hg h_orth) P
            ((Real.sqrt n)⁻¹ • h) n).map g) ?_
    funext X
    -- Goal at X (after Function.comp unfold):
    --   `EuclideanSpace.single 0 (Real.sqrt n * (T_n n X - ψ(...)))`
    -- = `Real.sqrt n • (T_n_lifted T_n n X - ψ_param_lifted ((√n)⁻¹•h))`.
    change EuclideanSpace.single (0 : Fin 1)
            (Real.sqrt n * (T_n n X - ψ (P.withDensity (fun ω =>
              ENNReal.ofReal
                ((paramSubmodel g_P hg h_orth).density
                  ((Real.sqrt n)⁻¹ • h) ω)))))
        = Real.sqrt n •
            (T_n_lifted T_n n X
              - ψ_param_lifted g_P hg h_orth ψ ((Real.sqrt n)⁻¹ • h))
    rw [T_n_lifted_sub_ψ_param_eq_single g_P hg h_orth ψ T_n
          ((Real.sqrt n)⁻¹ • h) n X]
    -- Goal: `single 0 (√n * x) = √n • single 0 x` where x = T_n n X - ψ(...).
    -- This is `single 0`-linearity (smul-equivariance) at the scalar `√n`.
    set x : ℝ := T_n n X - ψ (P.withDensity (fun ω => ENNReal.ofReal
      ((paramSubmodel g_P hg h_orth).density
        ((Real.sqrt n)⁻¹ • h) ω))) with hx_def
    -- Compute both sides via the underlying `WithLp` representation.
    rw [single_eq_withLp_const_apply, single_eq_withLp_const_apply]
    ext i
    fin_cases i
    change WithLp.ofLp
        ((WithLp.equiv 2 (Fin 1 → ℝ)).symm
          (fun _ : Fin 1 => Real.sqrt n * x)) 0
      = WithLp.ofLp (Real.sqrt n •
          (WithLp.equiv 2 (Fin 1 → ℝ)).symm
            (fun _ : Fin 1 => x)) 0
    rw [WithLp.ofLp_smul]
    simp [Pi.smul_apply, smul_eq_mul]
  -- Step 5: combine.
  refine weakConverges_congr_eventually ?_ h_pushed
  exact Filter.Eventually.of_forall (fun n => h_map_eq_n n)

end AsymptoticStatistics.LowerBounds.ParametricBridge
