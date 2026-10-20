module
public import StatLean.AsymptoticStatistics.LowerBounds.LAMSemiparametricUnbounded
public import StatLean.AsymptoticStatistics.LowerBounds.LAMLinearFromCone
public import StatLean.AsymptoticStatistics.LowerBounds.LAMUnboundedRecenter
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrow
public import StatLean.AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec
public import StatLean.AsymptoticStatistics.Core.PathwiseVec
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Semiparametric Local Asymptotic Minimax (LAM) Theorem (vector)

Let the functional $\psi : \mathcal{P} \to \mathbb{R}^k$ be differentiable at
$P$ relative to the tangent cone $\dot{\mathcal{P}}_P$ with **efficient
influence function** $\tilde\psi_P$. If $\dot{\mathcal{P}}_P$ is a convex cone,
then for any estimator sequence $\{T_n\}$ and any nonnegative, subconvex
(bowl-shaped) loss $\ell : \mathbb{R}^k \to [0, \infty]$,
$$
\sup_{I} \; \liminf_{n \to \infty} \; \sup_{g \in I} \;
  \mathbb{E}_{P_{1/\sqrt{n},\,g}}\,
    \ell\bigl(\sqrt{n}\,(T_n - \psi(P_{1/\sqrt{n},\,g}))\bigr)
\;\ge\; \int \ell \; dN\bigl(0,\; P\,\tilde\psi_P\,\tilde\psi_P^{\top}\bigr),
$$
where the outer supremum ranges over all finite subsets $I$ of the tangent
set. No estimator sequence can do asymptotically better than the Gaussian-shift
limit: the local minimax risk over the perturbed submodels is bounded below by
the integral of $\ell$ against the Gaussian with covariance
$P\,\tilde\psi_P\,\tilde\psi_P^{\top}$ (the optimal limit distribution).

This file states the headline vector theorem
`semiparametric_local_asymptotic_minimax_theorem`
($\psi : \mathrm{Measure}\,\Omega \to \mathbb{R}^d$, limit
$N(0, \mathrm{Matrix.gram}\;\mathbb{R}\;\mathrm{IF\_eff}) =
N(0, P\,\tilde\psi_P\,\tilde\psi_P^{\top})$)
and its scalar $d = 1$ corollary
`semiparametric_local_asymptotic_minimax_theorem_real`, where the book's
covariance matrix $P\,\tilde\psi_P\,\tilde\psi_P^{\top}$ collapses to the
scalar $\|\tilde\psi_P\|^2$ and the limit to the one-dimensional Gaussian
$N(0, \|\tilde\psi_P\|^2)$.

**Lean-vs-book deviations.** The loss takes values in the extended nonnegative
reals $[0,\infty]$ (so the risk integrals are unconditional `lintegral`s); the
book's "bowl-shaped" / subconvexity requirement is carried by `BowlShaped` plus
a per-truncation lower-semicontinuity hypothesis `hℓ_M_lsc` on $\ell \wedge M$
needed for the Portmanteau lower-bound step. Root-$n$ consistency of $T_n$ at
$P$ is supplied as a tightness hypothesis `hTight` (vdV Theorem 25.21 (§25.3), p. 367
standing assumption). The outer supremum is taken with `Finset.sup` (total on
$[0,\infty]$ with $\bot = 0$), so the empty finite subset contributes the
zero-information baseline $0$ and no nonemptiness side condition is needed.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series
in Statistical and Probabilistic Mathematics, Cambridge University Press, 1998.
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information),
Theorem 25.21 (local asymptotic minimax theorem).

**Proof formalization notes.** The proof forwards to
`lam_semiparametric_unbounded` (scalar) / `lam_semiparametric_unbounded_vec`
(vector): the convex-cone + negation-closure tangent hypotheses
(`hCone` / `hConvex` / `hNegClosed`) are equivalent to a **linear subspace**
(via `LAMLinearFromCone`), the perturbed submodel $P_{1/\sqrt{n},\,g}$ is the
internal `canonicalPath g`, and the written-out left-hand side is
definitionally the canonical-path functional `LHS_canonical` (scalar) /
`LHS_canonical_vec` (vector). Nonemptiness of the carrier
(`hCarrier_nonempty`) is constitutive of vdV's tangent cone, which contains
$0$ (the constant-path score); together with `hCone` it supplies
$0 \in \mathrm{carrier}$ for the linear-space reduction. The minimax reduction
itself rests on the convolution / minimax machinery (Theorem 8.11).

**Bibliographic comments.** The local asymptotic minimax theorem originates
with J. Hájek, "Local asymptotic minimax and admissibility in estimation,"
*Proceedings of the Sixth Berkeley Symposium on Mathematical Statistics and
Probability*, Vol. 1, University of California Press, 1972, pp. 175–194, which
established that the local minimax risk of any estimator sequence is bounded
below by the Gaussian-shift risk, the companion lower-bound result to Hájek's
convolution theorem (J. Hájek, "A characterization of limiting distributions of
regular estimates," *Z. Wahrscheinlichkeitstheorie verw. Gebiete* 14 (1970),
323–330). L. Le Cam's local asymptotic normality theory underlies the
parametric reduction. The semiparametric formulation stated here — efficient
influence function relative to a tangent cone, with the information-bound
covariance $P\,\tilde\psi_P\,\tilde\psi_P^{\top}$ — is the one developed in
P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A. Wellner, *Efficient and
Adaptive Estimation for Semiparametric Models*, Johns Hopkins University Press,
1993, and presented as vdV §25.3, Theorem 25.21.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics.LowerBounds.LAM

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics
open AsymptoticStatistics.LowerBounds
open AsymptoticStatistics.LowerBounds.RegularEstimator (canonicalPath)
open AsymptoticStatistics.LowerBounds.LAMSemiparametricUnbounded
  (lam_semiparametric_unbounded lam_semiparametric_unbounded_vec)
open AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec (T_param_of_vec)
open AsymptoticStatistics.Core.PathwiseVec (PathwiseDifferentiableAt_vec)
open AsymptoticStatistics.Core.EIFVec (IsEfficientInfluenceFunction_vec)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Theorem 25.21: vector local asymptotic minimax.*

Under the convex-cone tangent hypothesis and a nonnegative subconvex
(**bowl-shaped**) loss `ℓ : ℝᵈ → ℝ≥0∞`, the supremum of the `liminf` of the
per-`g` maximum risk along the LAN-perturbed submodels is bounded below by the
multivariate Gaussian integral of `ℓ` against `N(0, Matrix.gram ℝ IF_eff)`
(`= N(0, P ψ̃_P ψ̃_Pᵀ)`).

Reference: vdV §25.3.

The convex cone + negation-closure tangent hypotheses
(`hCone` / `hConvex` / `hNegClosed`) are equivalent to a **linear
subspace** (via `LAMLinearFromCone`), under which the canonical-path
functional `LHS_canonical_vec` (the left-hand side centered on the true
value `ψ((canonicalPath g).curve …)`) is bounded below by the multivariate
Gaussian integral through `lam_semiparametric_unbounded_vec` (the Theorem
8.11 minimax reduction on the unbounded parametric submodel). Nonemptiness
of the carrier (`hCarrier_nonempty`) is constitutive of vdV's tangent cone,
which contains `0` (the constant-path score); together with `hCone` it
supplies `0 ∈ carrier` for the linear-space reduction. -/
theorem semiparametric_local_asymptotic_minimax_theorem
    -- Tangent set as a convex cone (vdV §25.3).
    (T_set : TangentSpec P)
    (hCone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t →
      t • x ∈ T_set.carrier)
    (hConvex : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ T_set.carrier)
    -- The tangent cone (carrier) is closed under negation (vdV §25.3(b)).
    -- Together with `hCone` and `hConvex` this makes the carrier a linear
    -- subspace (via `LAMLinearFromCone`).
    (hNegClosed : ∀ x ∈ T_set.carrier, -x ∈ T_set.carrier)
    -- vdV's tangent cone is nonempty: it contains `0`, the constant-path score.
    (hCarrier_nonempty : T_set.carrier.Nonempty)
    -- Pathwise-differentiable vector functional and its efficient influence
    -- function tuple.
    {d : ℕ}
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {IF_eff : Fin d → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    -- Estimator sequence.
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    -- Estimator measurability (vdV §25 standing).
    (hT_n : ∀ n, Measurable (T_n n))
    -- Bowl-shaped (subconvex) loss (vdV §25), with per-truncation lower
    -- semicontinuity of `ℓ ⊓ M` for the Portmanteau lower-bound step.
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hℓ_sub : BowlShaped ℓ)
    (hℓ_M_lsc : ∀ M : ℕ,
      LowerSemicontinuous (fun u : EuclideanSpace ℝ (Fin d) => ℓ u ⊓ (M : ℝ≥0∞)))
    -- Root-n consistency: `√n(T_n − ψ(P))` is tight at `P` (vdV Theorem 25.21 (§25.3) p.367).
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
            (fun ω => (Real.sqrt n) •
              (T_param_of_vec T_n n ω - ψ P))))) :
    -- Conclusion: the supremum-over-finite-subsets of the liminf-sup of
    -- per-`g` `ℓ`-risk (along `canonicalPath g`) is bounded below by the
    -- multivariate Gaussian integral `∫ ℓ dN(0, Matrix.gram ℝ IF_eff)`. The
    -- written-out left-hand side is definitionally `LHS_canonical_vec T_set T_n ψ ℓ`.
    -- `Finset.sup` (not `sup'`) is total on `ℝ≥0∞` with `⊥ = 0`, so no
    -- nonemptiness side condition is needed: the book's `sup_{g ∈ I}` over a
    -- nonempty finite subset agrees with `Finset.sup`, and the empty subset
    -- contributes `0` to the outer `⨆`, the correct zero-information baseline
    -- (no admissible `g` gives no nontrivial bound from `I`).
    ⨆ I : { S : Finset ↥(L2ZeroMean P) //
            (S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier },
      Filter.liminf
        (fun n : ℕ =>
          ((I : { _S : Finset ↥(L2ZeroMean P) // _ }) :
              Finset ↥(L2ZeroMean P)).sup
            (fun g =>
              ∫⁻ X : Fin n → Ω,
                ℓ (Real.sqrt n •
                  (T_n n X - ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹))))
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin n => (canonicalPath g).curve ((Real.sqrt n)⁻¹)))))
        atTop
      ≥
    ∫⁻ y : EuclideanSpace ℝ (Fin d), ℓ y
        ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff)) := by
  -- The written-out left-hand side is definitionally `LHS_canonical_vec T_set T_n ψ ℓ`.
  change ∫⁻ y : EuclideanSpace ℝ (Fin d), ℓ y
        ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.gram ℝ IF_eff))
      ≤ LHS_canonical_vec T_set T_n ψ ℓ
  -- The carrier is nonempty (it contains the constant-path score `0`):
  -- cone + convexity + negation-closure give a linear space, then forward to
  -- `lam_semiparametric_unbounded_vec`.
  have hne : T_set.carrier.Nonempty := hCarrier_nonempty
  have hLin_smul : ∀ x ∈ T_set.carrier, ∀ t : ℝ, t • x ∈ T_set.carrier :=
    fun x hx t => LAMLinearFromCone.lin_smul_of_cone_neg T_set hCone hNegClosed hx t
  have hLin_add : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      x + y ∈ T_set.carrier :=
    fun x hx y hy => LAMLinearFromCone.lin_add_of_cone_convex T_set hCone hConvex hx hy
  have hLin_zero : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier :=
    LAMLinearFromCone.lin_zero_of_cone_nonempty T_set hCone hne
  exact lam_semiparametric_unbounded_vec T_set hLin_smul hLin_add hLin_zero
    hψ hEIF T_n hT_n ℓ hℓ_sub hℓ_M_lsc hTight

/-- *Theorem 25.21: scalar (real) local asymptotic minimax.*

Scalar `d = 1` specialization of
`semiparametric_local_asymptotic_minimax_theorem` for `ψ : Measure Ω → ℝ`,
proved directly by the scalar core `lam_semiparametric_unbounded`.

Under the convex-cone tangent hypothesis and a nonnegative subconvex
(**bowl-shaped**) loss `ℓ : ℝ → ℝ≥0∞`, the supremum of the `liminf` of the
per-`g` maximum risk along the LAN-perturbed submodels is bounded below by
the Gaussian integral of `ℓ` against `N(0, ‖IF_eff‖²)`.

Reference: vdV §25.3.

The convex cone + negation-closure tangent hypotheses
(`hCone` / `hConvex` / `hNegClosed`) are equivalent to a **linear
subspace** (via `LAMLinearFromCone`), under which the canonical-path
functional `LHS_canonical` (the left-hand side centered on the true value
`ψ((canonicalPath g).curve …)`) is bounded below by the Gaussian integral
through `lam_semiparametric_unbounded` (the Theorem 8.11 minimax reduction
on the unbounded parametric submodel). Nonemptiness of the carrier
(`hCarrier_nonempty`) is constitutive of vdV's tangent cone, which contains
`0` (the constant-path score); together with `hCone` it supplies
`0 ∈ carrier` for the linear-space reduction. -/
theorem semiparametric_local_asymptotic_minimax_theorem_real
    -- Tangent set as a convex cone (vdV §25.3).
    (T_set : TangentSpec P)
    (hCone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t →
      t • x ∈ T_set.carrier)
    (hConvex : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ T_set.carrier)
    -- The tangent cone (carrier) is closed under negation (vdV §25.3(b)).
    -- Together with `hCone` and `hConvex` this makes the carrier a linear
    -- subspace (via `LAMLinearFromCone`).
    (hNegClosed : ∀ x ∈ T_set.carrier, -x ∈ T_set.carrier)
    -- vdV's tangent cone is nonempty: it contains `0`, the constant-path score.
    (hCarrier_nonempty : T_set.carrier.Nonempty)
    -- Pathwise-differentiable scalar functional and its efficient influence
    -- function.
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    -- Estimator sequence.
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    -- Estimator measurability (vdV §25 standing).
    (hT_n : ∀ n, Measurable (T_n n))
    -- Bowl-shaped (subconvex) loss (vdV §25), with per-truncation lower
    -- semicontinuity of `ℓ ⊓ M` for the Portmanteau lower-bound step.
    (ℓ : ℝ → ℝ≥0∞)
    (hℓ_sub : BowlShaped ℓ)
    (hℓ_M_lsc : ∀ M : ℕ,
      LowerSemicontinuous (fun u : ℝ => ℓ u ⊓ (M : ℝ≥0∞)))
    -- Root-n consistency: `√n(T_n − ψ(P))` is tight at `P` (vdV Theorem 25.21 (§25.3) p.367).
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
            (fun ω => (Real.sqrt n) •
              (LAMSemiparametricBridge.T_param_of T_n n ω
                - EuclideanSpace.single (0 : Fin 1) (ψ P)))))) :
    -- Conclusion: the supremum-over-finite-subsets of the liminf-sup of
    -- per-`g` `ℓ`-risk (along `canonicalPath g`) is bounded below by the
    -- Gaussian integral `∫ ℓ dN(0, ‖IF_eff‖²)`. The written-out left-hand
    -- side is definitionally `LHS_canonical T_set T_n ψ ℓ`.
    let sigma_sq : ℝ≥0 :=
      ⟨‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩
    -- `Finset.sup` (not `sup'`) is total on `ℝ≥0∞` with `⊥ = 0`, so no
    -- nonemptiness side condition is needed: the book's `sup_{g ∈ I}` over a
    -- nonempty finite subset agrees with `Finset.sup`, and the empty subset
    -- contributes `0` to the outer `⨆`, the correct zero-information baseline
    -- (no admissible `g` gives no nontrivial bound from `I`).
    ⨆ I : { S : Finset ↥(L2ZeroMean P) //
            (S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier },
      Filter.liminf
        (fun n : ℕ =>
          ((I : { _S : Finset ↥(L2ZeroMean P) // _ }) :
              Finset ↥(L2ZeroMean P)).sup
            (fun g =>
              ∫⁻ X : Fin n → Ω,
                ℓ (Real.sqrt n *
                  (T_n n X - ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹))))
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin n => (canonicalPath g).curve ((Real.sqrt n)⁻¹)))))
        atTop
      ≥
    ∫⁻ u : ℝ, ℓ u ∂(ProbabilityTheory.gaussianReal 0 sigma_sq) := by
  intro sigma_sq
  -- The written-out left-hand side is definitionally `LHS_canonical T_set T_n ψ ℓ`.
  change ∫⁻ u : ℝ, ℓ u ∂(ProbabilityTheory.gaussianReal 0 sigma_sq)
      ≤ LHS_canonical T_set T_n ψ ℓ
  -- The carrier is nonempty (it contains the constant-path score `0`):
  -- cone + convexity + negation-closure give a linear space, then forward to
  -- `lam_semiparametric_unbounded`.
  have hne : T_set.carrier.Nonempty := hCarrier_nonempty
  have hLin_smul : ∀ x ∈ T_set.carrier, ∀ t : ℝ, t • x ∈ T_set.carrier :=
    fun x hx t => LAMLinearFromCone.lin_smul_of_cone_neg T_set hCone hNegClosed hx t
  have hLin_add : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      x + y ∈ T_set.carrier :=
    fun x hx y hy => LAMLinearFromCone.lin_add_of_cone_convex T_set hCone hConvex hx hy
  have hLin_zero : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier :=
    LAMLinearFromCone.lin_zero_of_cone_nonempty T_set hCone hne
  exact lam_semiparametric_unbounded T_set hLin_smul hLin_add hLin_zero
    hψ hEIF T_n hT_n ℓ hℓ_sub hℓ_M_lsc hTight

end AsymptoticStatistics.LowerBounds.LAM
