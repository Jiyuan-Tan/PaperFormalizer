module
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-!
# Le Cam's asymptotic representation theorem in kernel (randomized-statistic) form

Consider a parametric model that is differentiable in quadratic mean at a point
$\theta_0$ with nonsingular Fisher information matrix $J$, and let
$\kappa_n$ be a sequence of *randomized* statistics — Markov kernels mapping the
$n$-fold sample $(X_1,\dots,X_n)$ to a (possibly randomized) decision/estimate in
$\mathbb{R}^d$. Suppose that under each local alternative
$\theta_0 + h/\sqrt{n}$ the law of $\kappa_n$ applied to the sample converges
weakly to a limit law $L_h$, for every local parameter $h \in \mathbb{R}^k$.
Then there is a single Markov kernel (a randomized statistic) $\tilde\kappa$ on
the parameter space such that, for every $h$,
$$ L_h \;=\; N(h,\,J^{-1}) \;\circ\; \tilde\kappa, $$
i.e. $L_h$ is the law obtained by drawing $X \sim N(h, J^{-1})$ from the Gaussian
shift limit experiment and then applying the randomized rule $\tilde\kappa$ to $X$.
Equivalently, every weak limit of a sequence of (randomized) statistics in a
locally asymptotically normal model is *representable* as a randomized statistic
in the Gaussian shift experiment $\{N(h, J^{-1}) : h \in \mathbb{R}^k\}$.

This is the kernel-valued refinement of the deterministic-statistic representation
theorem. Relative to the book statement, the deterministic estimator $T_n$ is
replaced by a Markov kernel $\kappa_n$ (the limit randomized statistic
$\tilde\kappa$ is intrinsically randomized — a deterministic function does not
suffice for a Bayes-near-optimal sequence), the book's translation by
$\dot\psi_\theta h$ is specialized to the identity (estimating $h$ directly), and
the Le Cam transfer runs on the *contiguity* footing supplied by differentiability
in quadratic mean together with a density-regularity hypothesis, so that no
common-support assumption is required. The headline declarations are
`LAN_representation_kernel` and its subsequence-form variant
`LAN_representation_along_subseq`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 8 (Efficiency of Estimators), §8.3 (Lower Bound for Experiments),
Theorem 8.3 — the representation theorem for estimator sequences ("there exists a
randomized statistic $T$ in the experiment $\{N(h, I_\theta^{-1})\}$ such that
$T - \dot\psi_\theta h$ has distribution $L_{\theta,h}$"), which specializes the
general Asymptotic Representation Theorem of Chapter 7 (Local Asymptotic
Normality), Theorem 7.10. The result is the asymptotic backbone of the Local
Asymptotic Minimax / Bayes-risk lower bound, vdV Theorem 8.11. (The repository's
historical tag for this file is `vdV §8.5`; the verified book coordinates for the
representation statement formalized here are Theorem 8.3 / Theorem 7.10. §8.5 in
the book is the Convolution Theorem.)

**Proof formalization notes.** This file isolates the kernel-form variant of the
asymptotic representation theorem. It is the asymptotic backbone of Theorem 8.11's
Bayes-risk lower bound: the deterministic-`T` form
`AsymptoticRepresentation.LAN_representation` is structurally insufficient for a
Bayes-near-optimal sequence of statistics, which is naturally Markov-kernel valued
(the Bayes posterior decision rule is a *randomised* statistic, not a
deterministic function of the sample). The kernel-form replaces
`T : ∀n, (Fin n → 𝓧) → 𝓨 d` (deterministic) with
`κ : ∀n, Kernel (Fin n → 𝓧) (𝓨 d)` (Markov), and replaces the pushforward
`(productMeasure ...).map (T n)` with `(productMeasure ...).bind (κ n)`.

The proof mirrors the eight-step proof of the deterministic representation
theorem (`AsymptoticRepresentation.lean`, vdV Theorem 7.10 (§7.3)): score CLT + LAN expansion +
Le Cam's third lemma + Prohorov tightness + the Urysohn subsequence principle +
`condDistrib`-based representation-kernel construction, replacing each
`T n`-pushforward with a kernel `bind`. Step 7 (representation-kernel
construction) requires the kernel-form Girsanov / Cameron–Martin tilt applied to
the joint law of `(δ, κ_n(ω))` rather than `(δ, T_n(ω))`.

Headline declarations: `LAN_representation_kernel` and the subsequence-form
variant `LAN_representation_along_subseq`.

**Bibliographic comments.** The representation of limits of statistical
experiments by randomized procedures in the limit (Gaussian shift) experiment
originates with Lucien Le Cam's theory of weak convergence of experiments:
L. Le Cam, "Limits of experiments," in *Proceedings of the Sixth Berkeley
Symposium on Mathematical Statistics and Probability* (Vol. 1: Theory of
Statistics), University of California Press, 1972, pp. 245–261. The companion
convolution theorem for regular estimator sequences (vdV §8.5, Theorem 8.8) is due
to J. Hájek, "A characterization of limiting distributions of regular estimates,"
*Z. Wahrscheinlichkeitstheorie verw. Gebiete* 14 (1970), 323–330, and Le Cam.
van der Vaart's Theorem 8.3 / Theorem 7.10 specialize Le Cam's asymptotic
representation theorem to the locally asymptotically normal case.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace AsymptoticStatistics
namespace LocalAsymptoticMinimax

variable {k d : ℕ}
variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- Parameter space (matches `LocalAsymptoticMinimax.Θ`). -/
abbrev Θ' (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

/-- Target space of the kernel (matches `LocalAsymptoticMinimax.𝓨`). -/
abbrev 𝓨' (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-! ## Kernel-form sub-lemmas (kernel analogues of `AsymptoticRepresentation` Steps 2, 3, 5)

These mirror the deterministic-T helpers used by `AsymptoticRepresentation.LAN_representation`,
replacing every `(P^n).map (T n)` pushforward by `(P^n).bind (κ n)`. The
deterministic-T helpers (`joint_weak_subsequence`, `joint_weak_with_logLikelihood`,
`limit_law_under_h`) take `T : ∀ n, (Fin n → 𝓧) → 𝓨 d` directly; the kernel-form
analogues take `κ : ∀ n, Kernel (Fin n → 𝓧) (𝓨 d)` and construct the joint law on
`𝓨 d × Θ k` via the kernel product `(κ n) ×ₖ (Kernel.deterministic (scoreSum ℓ n))`.

Step-6 (`representationKernel`) and Step-7 (`gaussianShift_bind_eq_limit`) of the
deterministic body depend only on `π : Measure (𝓨 d × Θ k)`, not on `T`, so they
are reused. Steps 1, 4, 8 are similarly `T`-agnostic. -/

/-- **Joint-weak subsequence extraction, kernel form** (Step 2 analogue of
`AsymptoticRepresentation.joint_weak_subsequence`).

Given a Markov kernel sequence `κ_n : (Fin n → 𝓧) ⇝ 𝓨 d` weakly composed with
`productMeasure` and weakly converging to some `L_zero`, plus a tight score
sequence, extract a subsequence along which the joint law
`(P^n_{θ₀}).bind ((κ_n) ×ₖ Kernel.deterministic (scoreSum ℓ n))` converges weakly
to some probability measure `π` on `𝓨 d × Θ k`. -/
theorem joint_weak_subsequence_kernel
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : AsymptoticRepresentation.Θ k) (ℓ : 𝓧 → AsymptoticRepresentation.Θ k)
    (hΔ_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n))
    [∀ n, IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ₀ n)]
    (κ : ∀ n, Kernel (Fin n → 𝓧) (AsymptoticRepresentation.𝓨 d))
    [hκ_Markov : ∀ n, IsMarkovKernel (κ n)]
    (L_zero : Measure (AsymptoticRepresentation.𝓨 d)) [IsProbabilityMeasure L_zero]
    (hκ_tight_at_zero :
      WeakConverges (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).bind (κ n)) L_zero)
    (ν : Measure (AsymptoticRepresentation.Θ k)) [IsProbabilityMeasure ν]
    (hΔ_tight :
      WeakConverges (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
        (AsymptoticRepresentation.scoreSum ℓ n)) ν) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (π : Measure (AsymptoticRepresentation.𝓨 d ×
        AsymptoticRepresentation.Θ k)),
      IsProbabilityMeasure π ∧
      WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ (φ k_idx))
              (hΔ_meas (φ k_idx)))) π := by
  -- Joint kernel `κ_n ×ₖ Kernel.deterministic (scoreSum_n)` and its bind sequence.
  set jointK : ∀ n, Kernel (Fin n → 𝓧) (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k)
      :=
    fun n => (κ n) ×ₖ Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ n) (hΔ_meas n)
    with hjointK_def
  -- Markov-ness of the joint kernel (used for probability of marginals + bind).
  haveI hjointK_Markov : ∀ n, IsMarkovKernel (jointK n) := fun n => by
    simp only [hjointK_def]
    infer_instance
  -- Short names for the joint and marginal pushforward sequences.
  set joint : ℕ → Measure (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k) :=
    fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).bind (jointK n) with hjoint_def
  set Tseq : ℕ → Measure (AsymptoticRepresentation.𝓨 d) :=
    fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).bind (κ n) with hTseq_def
  set Δseq : ℕ → Measure (AsymptoticRepresentation.Θ k) :=
    fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
        (AsymptoticRepresentation.scoreSum ℓ n)
    with hΔseq_def
  -- The joint bind is a probability measure (`IsProbabilityMeasure` of `μ.bind κ` for Markov κ).
  haveI h_joint_prob : ∀ n, IsProbabilityMeasure (joint n) := fun n => inferInstance
  haveI h_T_prob : ∀ n, IsProbabilityMeasure (Tseq n) := fun n => inferInstance
  haveI h_Δ_prob : ∀ n, IsProbabilityMeasure (Δseq n) := fun n =>
    Measure.isProbabilityMeasure_map (hΔ_meas n).aemeasurable
  -- First marginal of the joint kernel-bind equals `Tseq` (kernel-bind of `κ`).
  -- Proof: `(P^n).bind (κ_n ×ₖ det) = (κ_n ×ₖ det) ∘ₘ P^n`. Then
  -- `((κ_n ×ₖ det) ∘ₘ P^n).map Prod.fst = (Kernel.map (κ_n ×ₖ det) Prod.fst) ∘ₘ P^n`
  -- by `Measure.map_comp`; the inner `Kernel.map _ Prod.fst = Kernel.fst _ = κ_n`
  -- by `Kernel.fst_eq` + `Kernel.fst_prod` (Markov on the right).
  have h_marg_fst : ∀ n, (joint n).map Prod.fst = Tseq n := by
    intro n
    simp only [hjoint_def, hTseq_def, hjointK_def]
    rw [Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq,
      Kernel.fst_prod (κ n)
        (Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ n) (hΔ_meas n))]
  -- Second marginal of the joint kernel-bind equals `Δseq` (deterministic pushforward).
  -- Proof: `((κ_n ×ₖ det) ∘ₘ P^n).map Prod.snd = (Kernel.snd (κ_n ×ₖ det)) ∘ₘ P^n`
  -- = `(Kernel.deterministic scoreSum_n) ∘ₘ P^n` = `P^n.map scoreSum_n`.
  have h_marg_snd : ∀ n, (joint n).map Prod.snd = Δseq n := by
    intro n
    simp only [hjoint_def, hΔseq_def, hjointK_def]
    rw [Measure.map_comp _ _ measurable_snd, ← Kernel.snd_eq,
      Kernel.snd_prod (κ n)
        (Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ n) (hΔ_meas n))]
    exact MeasureTheory.Measure.deterministic_comp_eq_map (hΔ_meas n)
  -- Each marginal sequence is tight (weak convergence ⇒ tight range).
  have hT_range_tight : IsTightMeasureSet (Set.range Tseq) :=
    Prohorov.weakConverges_range_tight _ _ hκ_tight_at_zero
  have hΔ_range_tight : IsTightMeasureSet (Set.range Δseq) :=
    Prohorov.weakConverges_range_tight _ _ hΔ_tight
  -- Images of the joint range under marginal projections equal the marginal ranges.
  have h_fst_image :
      (fun ρ : Measure (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k) => ρ.map
          Prod.fst) ''
          (Set.range joint) = Set.range Tseq := by
    ext ρ
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (h_marg_fst n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨joint n, ⟨n, rfl⟩, h_marg_fst n⟩
  have h_snd_image :
      (fun ρ : Measure (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k) => ρ.map
          Prod.snd) ''
          (Set.range joint) = Set.range Δseq := by
    ext ρ
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (h_marg_snd n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨joint n, ⟨n, rfl⟩, h_marg_snd n⟩
  -- Joint tightness.
  have h_joint_tight : IsTightMeasureSet (Set.range joint) :=
    Prohorov.tight_prod_of_tight_marginals _
      (h_fst_image ▸ hT_range_tight)
      (h_snd_image ▸ hΔ_range_tight)
  -- Extract weakly convergent subsequence via Prohorov.
  obtain ⟨φ, hφ_mono, π, hπ_prob, h_conv⟩ :=
    Prohorov.extract_weak_subseq joint h_joint_tight
  exact ⟨φ, hφ_mono, π, hπ_prob, h_conv⟩

/-- **Slutsky bridge to joint log-likelihood, kernel form** (Step 3 analogue of
`AsymptoticRepresentation.joint_weak_with_logLikelihood`).

Given a kernel-joint subsequence weakly converging to `π`, the Slutsky bridge
replaces the linearised second coordinate `⟨h, Δ_n⟩ - ½⟨h, J h⟩` by the
log-likelihood `L_{n,h}` and produces the joint weak convergence consumed by
the Le-Cam-3 step. The joint kernel construction uses
`κ_n ×ₖ Kernel.deterministic (fun ω => ⟪h, Δ_n ω⟫ - ½⟨h, J h⟩)` on the LHS and
`κ_n ×ₖ Kernel.deterministic (logLikelihood M θ₀ h n)` on the RHS.

**Wiring decomposition** (mirrors `AsymptoticRepresentation.joint_weak_with_logLikelihood`):
1. Apply continuous mapping with the affine `tilt_map (y, δ) := (y, ⟪h, δ⟩ - c)` to
   `h_subseq_joint` (where `c = ½⟪h, J h⟫_Mat`). Combined with
   `Kernel.deterministic_map` + `Kernel.map_prod_eq`, this yields the linearised
   joint kernel-bind law `(P^{φ k}).bind (κ_{φ k} ×ₖ Kernel.deterministic linearised)
   ⇝ π.map tilt_map`.
2. Apply the supplied `h_slutsky_bridge_kernel` to swap the linearised second
   coordinate for `logLikelihood`. -/
theorem joint_weak_with_logLikelihood_kernel
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : AsymptoticRepresentation.Θ k) (ℓ : 𝓧 → AsymptoticRepresentation.Θ k)
    (hΔ_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n))
    (_hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (_hJ : ∀ u v : AsymptoticRepresentation.Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    [∀ n, IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ₀ n)]
    (κ : ∀ n, Kernel (Fin n → 𝓧) (AsymptoticRepresentation.𝓨 d))
    [hκ_Markov : ∀ n, IsMarkovKernel (κ n)]
    (h : AsymptoticRepresentation.Θ k)
    (π : Measure (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k))
        [IsProbabilityMeasure π]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (h_subseq_joint :
      WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ (φ k_idx))
              (hΔ_meas (φ k_idx)))) π)
    -- Discharge of the LAN residual lives in the outer `LAN_representation_kernel`
    -- body, which has access to `hℓ, hPDF` and constructs the bridge via
    -- `lanResidual_tendsto_productMeasure` + Slutsky on the compProd-encoded
    -- base measure.
    (h_slutsky_bridge_kernel :
      WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic
              (fun ω : Fin (φ k_idx) → 𝓧 =>
                (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
                  ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫
                  : ℝ))
              (by
                have h_inner_meas : Measurable
                    (fun v : AsymptoticRepresentation.Θ k => ⟪h, v⟫) :=
                  (continuous_const.inner continuous_id).measurable
                exact (h_inner_meas.comp (hΔ_meas (φ k_idx))).sub_const _)))
        (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))) →
      WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h (φ k_idx))
              (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h (φ k_idx))))
        (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)))) :
    -- Conclusion: along the same φ, the joint kernel composed law with
    -- (κ_n, logLikelihood_n) on the product converges weakly to π's affine tilt.
    WeakConverges
      (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
        ((κ (φ k_idx)) ×ₖ
          Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h (φ k_idx))
            (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h (φ k_idx))))
      (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
        (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
          ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))) := by
  -- Constant abbreviation: the "½ ⟪h, J h⟫_Mat" term that appears throughout.
  set c : ℝ := (1 / 2 : ℝ) *
    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ with hc_def
  -- The continuous affine tilt that turns the second coordinate from `Θ k` to `ℝ`.
  let tilt_map : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k →
      AsymptoticRepresentation.𝓨 d × ℝ := fun p =>
    (p.1, ⟪h, p.2⟫ - c)
  have htilt_cont : Continuous tilt_map :=
    continuous_fst.prodMk
      ((continuous_const.inner continuous_snd).sub continuous_const)
  have htilt_meas : Measurable tilt_map := htilt_cont.measurable
  -- Piece (1): continuous mapping under `tilt_map` on the joint kernel-bind law.
  -- The pushforward of `(P^{φ k}).bind (κ_{φ k} ×ₖ Kernel.deterministic scoreSum)` by
  -- `tilt_map` equals `(P^{φ k}).bind ((κ_{φ k} ×ₖ Kernel.deterministic scoreSum).map
  -- tilt_map)` by `Measure.map_comp`; the inner kernel map further reduces via
  -- `map_prod_eq` (`tilt_map = Prod.map id (⟨h,·⟩-c)`) + `deterministic_map` to
  -- `(κ_{φ k}) ×ₖ Kernel.deterministic linearised`.
  -- The measurability witness for `⟨h, ·⟩ - c` composed with `scoreSum ℓ n`.
  have h_inner_meas : Measurable (fun v : AsymptoticRepresentation.Θ k => ⟪h, v⟫) :=
    (continuous_const.inner continuous_id).measurable
  have h_linearised_meas : ∀ n : ℕ,
      Measurable (fun ω : Fin n → 𝓧 =>
        (⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - c : ℝ)) := fun n =>
    (h_inner_meas.comp (hΔ_meas n)).sub_const _
  -- The kernel-form pushforward identity:
  -- `(κ ×ₖ Kernel.deterministic scoreSum).map tilt_map
  --    = κ ×ₖ Kernel.deterministic (⟨h, scoreSum ·⟩ - c)`.
  have h_kernel_pushforward : ∀ n,
      Kernel.map ((κ n) ×ₖ Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ n)
          (hΔ_meas n)) tilt_map
        = (κ n) ×ₖ Kernel.deterministic
          (fun ω : Fin n → 𝓧 => (⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - c : ℝ))
          (h_linearised_meas n) := by
    intro n
    -- `tilt_map = Prod.map id (fun δ => ⟪h, δ⟫ - c)`.
    have h_tilt_eq :
        tilt_map = Prod.map id (fun δ : AsymptoticRepresentation.Θ k => ⟪h, δ⟫ - c) := rfl
    rw [h_tilt_eq]
    have h_g_meas : Measurable (fun δ : AsymptoticRepresentation.Θ k => ⟪h, δ⟫ - c) :=
      h_inner_meas.sub_const _
    rw [show (Prod.map (id : AsymptoticRepresentation.𝓨 d → AsymptoticRepresentation.𝓨 d)
              (fun δ : AsymptoticRepresentation.Θ k => ⟪h, δ⟫ - c))
            = Prod.map (id : AsymptoticRepresentation.𝓨 d → AsymptoticRepresentation.𝓨 d)
              (fun δ : AsymptoticRepresentation.Θ k => ⟪h, δ⟫ - c) from rfl,
      ← Kernel.map_prod_map (κ n)
        (Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ n) (hΔ_meas n))
        measurable_id h_g_meas, Kernel.map_id,
      Kernel.deterministic_map (hΔ_meas n) h_g_meas]
    rfl
  -- Push the weak convergence through `tilt_map` and rewrite using
  -- `h_kernel_pushforward` to land in the linearised kernel-bind form.
  have h_cm := h_subseq_joint.map htilt_cont htilt_meas
  have h_linear_joint :
      WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic
              (fun ω : Fin (φ k_idx) → 𝓧 =>
                (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ k_idx) ω⟫ - c : ℝ))
              (h_linearised_meas (φ k_idx))))
        (π.map tilt_map) := by
    -- Rewrite `((P^n).bind (κ ×ₖ det)).map tilt_map = (P^n).bind ((κ ×ₖ det).map tilt_map)`
    -- via `Measure.map_comp`, then use `h_kernel_pushforward`.
    have h_fun_eq : ∀ k_idx,
        ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
            ((κ (φ k_idx)) ×ₖ
              Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ (φ k_idx))
                (hΔ_meas (φ k_idx)))).map tilt_map
          = (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
            ((κ (φ k_idx)) ×ₖ
              Kernel.deterministic
                (fun ω : Fin (φ k_idx) → 𝓧 =>
                  (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ k_idx) ω⟫ - c : ℝ))
                (h_linearised_meas (φ k_idx))) := by
      intro k_idx
      rw [Measure.map_comp _ _ htilt_meas, h_kernel_pushforward (φ k_idx)]
    intro f
    have := h_cm f
    -- Rewrite the LHS integrand using `h_fun_eq`.
    simp_rw [h_fun_eq] at this
    exact this
  -- Piece (2): apply the Slutsky bridge hypothesis.
  exact h_slutsky_bridge_kernel h_linear_joint

/-- **Auxiliary identity: kernel-bind = compProd pushforward** (kernel-form helper
for `slutsky_bridge_of_lanResidual_kernel`).

For any base measure `P : Measure α`, Markov kernel `κ : Kernel α β`, and
measurable function `f : α → γ`, the kernel-bind law
`P.bind (κ ×ₖ Kernel.deterministic f)` on `β × γ` equals the pushforward of
the compProd `P ⊗ₘ κ` on `α × β` by `(ω, y) ↦ (y, f ω)`. This is the key
identity that lets us apply the varying-base Slutsky lemma
(`WeakConverges.slutsky_of_tendstoInMeasure_dist`) to kernel-bind sequences. -/
private lemma bind_prodKernel_deterministic_eq_compProd_map
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass γ]
    (P : Measure α) [SFinite P] (κ : Kernel α β) [IsSFiniteKernel κ]
    {f : α → γ} (hf : Measurable f) :
    P.bind ((κ) ×ₖ Kernel.deterministic f hf)
      = (P ⊗ₘ κ).map (fun p : α × β => (p.2, f p.1)) := by
  -- Both sides are sigma-finite; verify equality on measurable sets.
  ext s hs
  -- The map of the measurable function `(ω, y) ↦ (y, f ω)`.
  have h_map_meas : Measurable (fun p : α × β => (p.2, f p.1)) :=
    measurable_snd.prodMk (hf.comp measurable_fst)
  -- Both sides equal `∫⁻ ω, (κ ω) {b | (b, f ω) ∈ s} ∂P`.
  rw [Measure.bind_apply hs (by fun_prop), Measure.map_apply h_map_meas hs,
    Measure.compProd_apply (h_map_meas hs)]
  -- Pointwise equality: `((κ ×ₖ det f) ω) s = (κ ω) {b | (b, f ω) ∈ s}`.
  apply lintegral_congr
  intro ω
  change ((κ ×ₖ Kernel.deterministic f hf) ω) s = _
  rw [Kernel.prod_apply' _ _ _ hs]
  -- LHS: `∫⁻ b, (Kernel.deterministic f hf ω) (Prod.mk b ⁻¹' s) ∂κ ω`.
  -- `Kernel.deterministic f hf ω = Measure.dirac (f ω)`, so the inner equals
  -- `indicator (Prod.mk b ⁻¹' s) 1 (f ω) = if (b, f ω) ∈ s then 1 else 0`.
  -- That integrates to `(κ ω) {b | (b, f ω) ∈ s}`.
  have h_eq_slice : (Prod.mk ω ⁻¹' ((fun p : α × β => (p.2, f p.1)) ⁻¹' s))
      = {b : β | (b, f ω) ∈ s} := by
    ext b; simp [Set.mem_preimage]
  have h_slice_meas : MeasurableSet {b : β | (b, f ω) ∈ s} := by
    have h_pre : MeasurableSet
        (Prod.mk ω ⁻¹' ((fun p : α × β => (p.2, f p.1)) ⁻¹' s)) :=
      measurable_prodMk_left (h_map_meas hs)
    rwa [h_eq_slice] at h_pre
  rw [h_eq_slice, ← lintegral_indicator_one (μ := κ ω) h_slice_meas]
  refine lintegral_congr (fun b => ?_)
  rw [Kernel.deterministic_apply,
    MeasureTheory.Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  rfl

/-- **Discharge of the kernel-form `h_slutsky_bridge_kernel` hypothesis** via the
`WeakConverges`-form Slutsky adapter. Kernel-form analogue of
`AsymptoticRepresentation.slutsky_bridge_of_lanResidual`.

Given that the LAN residual `logLikelihood - linearised` vanishes in probability
under `productMeasure`, the linearised joint kernel-bind weak convergence lifts to
the log-likelihood joint kernel-bind weak convergence — exactly the bridge consumed
by `joint_weak_with_logLikelihood_kernel`.

Proof outline: encode each kernel-bind law as a pushforward of the compProd
`(P^{φ k}) ⊗ₘ κ_{φ k}` via `bind_prodKernel_deterministic_eq_compProd_map`, then
invoke `WeakConverges.slutsky_of_tendstoInMeasure_dist` on the compProd base. The
distance condition lifts the `(P^{φ k})`-probability tendsto to a `(P ⊗ₘ κ)`-
probability tendsto because the distance function depends only on the first
coordinate (`P` factor) and `κ_{φ k}` is Markov. -/
theorem slutsky_bridge_of_lanResidual_kernel
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : AsymptoticRepresentation.Θ k, ∀ n,
        IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n)]
    (θ₀ : AsymptoticRepresentation.Θ k) (ℓ : 𝓧 → AsymptoticRepresentation.Θ k)
    (hΔ_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n))
    (J : Matrix (Fin k) (Fin k) ℝ)
    (κ : ∀ n, Kernel (Fin n → 𝓧) (AsymptoticRepresentation.𝓨 d))
    [hκ_Markov : ∀ n, IsMarkovKernel (κ n)]
    (h : AsymptoticRepresentation.Θ k)
    (π : Measure (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k))
        [IsProbabilityMeasure π]
    (φ : ℕ → ℕ)
    (h_lanResidual : ∀ ε > 0,
      Tendsto (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).real
        {ω : Fin (φ k_idx) → 𝓧 | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h (φ k_idx) ω
                 - (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|})
        atTop (𝓝 0)) :
    WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic
              (fun ω : Fin (φ k_idx) → 𝓧 =>
                (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
                  ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫
                  : ℝ))
              (by
                have h_inner_meas : Measurable
                    (fun v : AsymptoticRepresentation.Θ k => ⟪h, v⟫) :=
                  (continuous_const.inner continuous_id).measurable
                exact (h_inner_meas.comp (hΔ_meas (φ k_idx))).sub_const _)))
        (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))) →
    WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h (φ k_idx))
              (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h (φ k_idx))))
        (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))) := by
  intro h_linear_joint
  -- Abbreviate the tilted measure (limit).
  set ν : Measure (AsymptoticRepresentation.𝓨 d × ℝ) :=
    π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
      (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
        ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)) with hν_def
  haveI hν_prob : IsProbabilityMeasure ν := by
    refine Measure.isProbabilityMeasure_map ?_
    fun_prop
  -- Measurability of the inner-product map `δ ↦ ⟨h, δ⟩`.
  have h_inner_meas : Measurable (fun v : AsymptoticRepresentation.Θ k => ⟪h, v⟫) :=
    (continuous_const.inner continuous_id).measurable
  -- The linearised second coord function `ω ↦ ⟨h, scoreSum_n ω⟩ - c`.
  have h_linearised_meas : ∀ n : ℕ,
      Measurable (fun ω : Fin n → 𝓧 =>
        (⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (1 / 2 : ℝ) *
          ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ : ℝ)) := fun n =>
    (h_inner_meas.comp (hΔ_meas n)).sub_const _
  have h_logLik_meas : ∀ n, Measurable (AsymptoticRepresentation.logLikelihood M θ₀ h n) := fun n =>
    AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n
  -- Encode each kernel-bind law as a pushforward of the compProd `(P^{φ k}) ⊗ₘ κ_{φ k}`.
  -- Let X_n, Y_n : (Fin (φ n) → 𝓧) × 𝓨 d → 𝓨 d × ℝ be the corresponding maps.
  set X : ∀ n : ℕ, (Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d → AsymptoticRepresentation.𝓨 d × ℝ
      :=
    fun n p => (p.2, ⟪h, AsymptoticRepresentation.scoreSum ℓ (φ n) p.1⟫ - (1 / 2 : ℝ) *
      ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫) with hX_def
  set Y : ∀ n : ℕ, (Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d → AsymptoticRepresentation.𝓨 d × ℝ
      :=
    fun n p => (p.2, AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) p.1) with hY_def
  have hX_meas : ∀ n, Measurable (X n) := fun n =>
    measurable_snd.prodMk ((h_linearised_meas (φ n)).comp measurable_fst)
  have hY_meas : ∀ n, Measurable (Y n) := fun n =>
    measurable_snd.prodMk ((h_logLik_meas (φ n)).comp measurable_fst)
  -- The compProd base measures.
  let Ptilde : ∀ n : ℕ, Measure ((Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d) := fun n =>
    AsymptoticRepresentation.productMeasure M μ θ₀ (φ n) ⊗ₘ (κ (φ n))
  haveI hPtilde_prob : ∀ n, IsProbabilityMeasure (Ptilde n) := fun n => inferInstance
  -- The kernel-bind = compProd-pushforward identities.
  have h_X_pushforward : ∀ n,
      (AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)).bind
        ((κ (φ n)) ×ₖ Kernel.deterministic
          (fun ω : Fin (φ n) → 𝓧 =>
            (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ n) ω⟫ - (1 / 2 : ℝ) *
              ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ : ℝ))
          (h_linearised_meas (φ n)))
        = (Ptilde n).map (X n) :=
    fun n => bind_prodKernel_deterministic_eq_compProd_map
      (AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)) (κ (φ n)) (h_linearised_meas (φ n))
  have h_Y_pushforward : ∀ n,
      (AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)).bind
        ((κ (φ n)) ×ₖ Kernel.deterministic
          (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n)) (h_logLik_meas (φ n)))
        = (Ptilde n).map (Y n) :=
    fun n => bind_prodKernel_deterministic_eq_compProd_map
      (AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)) (κ (φ n)) (h_logLik_meas (φ n))
  -- Rewrite the input linear weak convergence in terms of `(Ptilde n).map (X n) ⇝ ν`.
  have hX_weak : WeakConverges (fun n => (Ptilde n).map (X n)) ν := by
    intro f
    have := h_linear_joint f
    simp_rw [h_X_pushforward] at this
    exact this
  -- Goal: `(Ptilde n).map (Y n) ⇝ ν`. Apply Slutsky-by-distance.
  suffices h_Y_weak : WeakConverges (fun n => (Ptilde n).map (Y n)) ν by
    intro f
    have := h_Y_weak f
    simp_rw [← h_Y_pushforward] at this
    exact this
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => (hX_meas n).aemeasurable) (fun n => (hY_meas n).aemeasurable)
    hX_weak ?_
  -- Distance condition: `dist(X_n(ω, y), Y_n(ω, y))` depends only on `ω` (first coord)
  -- because X_n and Y_n share their first output. So the dist-set on `Ptilde n` is a
  -- cylinder, and its mass equals the mass on `productMeasure (φ n)` (since κ is Markov).
  intro ε hε
  -- The dist set is `{(ω, y) : ε ≤ |logLik(ω) - linearised(ω)|}`, independent of `y`.
  have h_set_eq : ∀ n,
      {p : (Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d | ε ≤ dist (X n p) (Y n p)}
        = {ω | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω
                 - (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ n) ω⟫ - (1 / 2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|}
          ×ˢ Set.univ := by
    intro n
    ext ⟨ω, y⟩
    simp only [Set.mem_setOf_eq, hX_def, hY_def, Prod.dist_eq, dist_self, Real.dist_eq,
      Set.mem_prod, Set.mem_univ, and_true]
    rw [max_eq_right (abs_nonneg _), abs_sub_comm]
  -- The cylinder mass under compProd equals `(P^{φ n}) S × κ_{φ n}.univ = (P^{φ n}) S`.
  have h_mass_eq : ∀ n,
      (Ptilde n).real
          {p : (Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d | ε ≤ dist (X n p) (Y n p)}
        = (AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)).real
          {ω | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω
                 - (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ n) ω⟫ - (1 / 2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|} := by
    intro n
    rw [h_set_eq n]
    -- compProd of a rectangle: `(P ⊗ₘ κ)(S ×ˢ univ) = ∫_S κ(ω) univ ∂P = P(S) * 1`.
    have hS_meas : MeasurableSet
        {ω : Fin (φ n) → 𝓧 | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω
                 - (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ n) ω⟫ - (1 / 2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|} := by
      refine measurableSet_le measurable_const ?_
      exact ((h_logLik_meas (φ n)).sub (h_linearised_meas (φ n))).abs
    change ((Ptilde n) _).toReal = _
    rw [Measure.compProd_apply_prod hS_meas MeasurableSet.univ]
    -- `∫_S (κ ω univ) ∂P = ∫_S 1 ∂P = P S` since `κ_{φ n}` is Markov.
    have h_kappa_univ : ∀ a, (κ (φ n)) a Set.univ = 1 := fun a => by
      haveI : IsProbabilityMeasure ((κ (φ n)) a) :=
        (hκ_Markov (φ n)).isProbabilityMeasure a
      exact measure_univ
    simp_rw [h_kappa_univ]
    rw [MeasureTheory.lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, one_mul]
    rfl
  -- Conclude by transporting the tendsto.
  simp_rw [h_mass_eq]
  exact h_lanResidual ε hε

/-- **Second-marginal identification of the joint kernel limit** (kernel-form Step 2
helper).

Along the subsequence `φ` where the joint kernel-bind law converges to `π`, the
second marginal `π.map snd` equals the weak limit of the score-pushforward
sequence `(P^n_{θ₀}).map (scoreSum ℓ n)`. The proof: each joint kernel-bind law's
snd marginal equals the score pushforward by `Kernel.lintegral_prod_deterministic`,
and continuous-mapping under `snd` transports weak convergence.

This is a kernel-form analogue of the `h_π_snd` calculation in
`AsymptoticRepresentation.LAN_representation`. -/
theorem joint_kernel_snd_eq_scoreSum_pushforward
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : AsymptoticRepresentation.Θ k) (ℓ : 𝓧 → AsymptoticRepresentation.Θ k)
    (hΔ_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n))
    [∀ n, IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ₀ n)]
    (κ : ∀ n, Kernel (Fin n → 𝓧) (AsymptoticRepresentation.𝓨 d))
    [∀ n, IsMarkovKernel (κ n)]
    (φ : ℕ → ℕ) (π : Measure (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k))
    [IsProbabilityMeasure π]
    (_hφ_mono : StrictMono φ)
    (_h_joint :
      WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ (φ k_idx))
              (hΔ_meas (φ k_idx)))) π)
    (limit : Measure (AsymptoticRepresentation.Θ k)) [IsProbabilityMeasure limit]
    (_h_snd_seq :
      WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).map
          (AsymptoticRepresentation.scoreSum ℓ (φ k_idx))) limit) :
    π.map Prod.snd = limit := by
  -- Per-n marginal identity: snd-pushforward of `(P^n).bind (κ_n ×ₖ det g_n)` equals
  -- `(P^n).map g_n`, by the chain `Measure.map_comp` + `Kernel.snd_eq` + `Kernel.snd_prod`
  -- + `Measure.deterministic_comp_eq_map`.
  have h_marg : ∀ k_idx,
      ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ (φ k_idx))
              (hΔ_meas (φ k_idx)))).map Prod.snd
        = (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).map
            (AsymptoticRepresentation.scoreSum ℓ (φ k_idx)) := by
    intro k_idx
    -- Step 1: pull `Prod.snd` inside the bind via `Measure.map_comp`.
    rw [Measure.map_comp _ _ measurable_snd]
    -- Step 2: collapse `(κ ×ₖ Kernel.deterministic g).map Prod.snd = Kernel.deterministic g`
    -- via `Kernel.snd_eq` (snd = map snd) reversed + `Kernel.snd_prod`.
    rw [← Kernel.snd_eq, Kernel.snd_prod]
    -- Step 3: bind-with-deterministic-kernel = pushforward.
    exact Measure.deterministic_comp_eq_map (hΔ_meas (φ k_idx))
  -- Transport the snd-marginal weak convergence input to the joint-bind sequence's
  -- snd-marginals via `simp_rw [h_marg]`, then apply `WeakConverges.snd_eq`.
  have h_snd_seq' : WeakConverges
      (fun k_idx => ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
        ((κ (φ k_idx)) ×ₖ
          Kernel.deterministic (AsymptoticRepresentation.scoreSum ℓ (φ k_idx))
            (hΔ_meas (φ k_idx)))).map Prod.snd) limit := by
    simp_rw [h_marg]
    exact _h_snd_seq
  exact WeakConverges.snd_eq _h_joint h_snd_seq'

/-- **Limit law via Le Cam 3, kernel form** (Step 5 analogue of
`AsymptoticRepresentation.limit_law_under_h`).

The kernel analogue of vdV Theorem 7.10 (§7.3) Step 5: given joint weak convergence of
`(κ_n, logLikelihood_n)` and the auxiliary integrability/MGF conditions on the
tilted joint, the law of `(P^n_{θ₀+h/√n}).bind (κ n)` equals the first marginal
of the tilted joint `(π.withDensity (exp ∘ affineTilt)).map fst`. -/
theorem limit_law_under_h_kernel
    [HasOuterApproxClosed (AsymptoticRepresentation.𝓨 d)] [BorelSpace (AsymptoticRepresentation.𝓨
        d)]
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : AsymptoticRepresentation.Θ k, ∀ n,
        IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n)]
    (θ₀ : AsymptoticRepresentation.Θ k) (ℓ : 𝓧 → AsymptoticRepresentation.Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (_hJ_pd : Matrix.PosDef J)
    (κ : ∀ n, Kernel (Fin n → 𝓧) (AsymptoticRepresentation.𝓨 d))
    [hκ_Markov : ∀ n, IsMarkovKernel (κ n)]
    (h : AsymptoticRepresentation.Θ k)
    (π : Measure (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k))
        [IsProbabilityMeasure π]
    (L_h : Measure (AsymptoticRepresentation.𝓨 d)) [IsProbabilityMeasure L_h]
    (h_weak_under_h :
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ
          (θ₀ + (Real.sqrt n)⁻¹ • h) n).bind (κ n)) L_h)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (h_subseq_joint_log :
      WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).bind
          ((κ (φ k_idx)) ×ₖ
            Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h (φ k_idx))
              (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h (φ k_idx))))
        (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))))
    -- The contiguity-footing integral-comparison bound (derived internally from
    -- `hDQM` + `hPDF`) supplies the Le Cam transfer without requiring
    -- `Q_n = P_n.withDensity(exp Lₙ)` exactly.
    (hPDF : IsPDFOf M μ)
    (vLog : NNReal)
    (hLogLik_weak :
        WeakConverges
          (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (AsymptoticRepresentation.logLikelihood M θ₀ h n))
          (ProbabilityTheory.gaussianReal (-(vLog : ℝ) / 2) vLog))
    (h_exp_int_πtilt :
        Integrable (fun q : AsymptoticRepresentation.𝓨 d × ℝ => Real.exp q.2)
          (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
            (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
              ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))))
    (h_exp_int_πtilt_eq_one :
        ∫ q, Real.exp q.2 ∂
          (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
            (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
              ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)))
          = 1) :
    L_h = Measure.map Prod.fst
      (π.withDensity (fun p => ENNReal.ofReal
        (Real.exp (⟪h, p.2⟫ - (1 / 2 : ℝ) *
          ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)))) := by
  -- Affine tilt abbreviations (parallel to the deterministic-T template).
  let g : AsymptoticRepresentation.Θ k → ℝ := fun δ =>
    ⟪h, δ⟫ - (1 / 2 : ℝ) *
      ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫
  let tilt_map : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k →
      AsymptoticRepresentation.𝓨 d × ℝ :=
    fun p => (p.1, g p.2)
  have hg_meas : Measurable g :=
    (continuous_const.inner continuous_id).measurable.sub measurable_const
  have htilt_meas : Measurable tilt_map :=
    measurable_fst.prodMk (hg_meas.comp measurable_snd)
  haveI h_tilt_prob : IsProbabilityMeasure (π.map tilt_map) :=
    MeasureTheory.Measure.isProbabilityMeasure_map htilt_meas.aemeasurable
  -- Measurability of `logLikelihood`.
  have hL_meas : ∀ n, Measurable (AsymptoticRepresentation.logLikelihood M θ₀ h n) :=
    fun n => AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n
  -- Full-sequence UI of `exp(logLikelihood)` via the contiguity-footing variant.
  -- Derive the companions internally from `hDQM` + `hPDF` (replaces the exact
  -- change-of-measure identity that required common support).
  have h_exp_int_full :=
    AsymptoticRepresentation.productMeasure_exp_logLikelihood_integrable M μ θ₀ ℓ hℓ hDQM hPDF h
  have h_mass_full :=
    AsymptoticRepresentation.productMeasure_integral_exp_logLikelihood_tendsto_one M μ θ₀ ℓ hℓ hDQM
        hPDF h
  have h_UI_full := Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one
    (Ω := fun n => Fin n → 𝓧)
    (fun n => AsymptoticRepresentation.productMeasure M μ θ₀ n)
    (fun n => AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
    (fun n => AsymptoticRepresentation.logLikelihood M θ₀ h n) hL_meas
    h_exp_int_full h_mass_full vLog hLogLik_weak
  -- Subsequence UI via `StrictMono.id_le`.
  have h_UI_subseq : ∀ ε : ℝ, 0 < ε →
      ∃ Mbd : ℝ, 0 ≤ Mbd ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
            min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd
          ∂(AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)) ≤ ε := by
    intro ε hε
    obtain ⟨Mbd, hMbd, N₀, hN₀⟩ := h_UI_full ε hε
    refine ⟨Mbd, hMbd, N₀, fun n hn => hN₀ (φ n) (le_trans hn (hφ.id_le n))⟩
  -- Lift to the richer space `(Fin n → 𝓧) × 𝓨 d` via compProd:
  -- `P'_n := P_n ⊗ₘ κ_n`, with `X'_n := snd` and `L'_n := L_n ∘ fst`.
  -- Under this lift, Le Cam 3 applies pointwise.
  -- Use plain `let` (transparent) rather than `set` so downstream `rw`s see through.
  let Pn : ∀ n, Measure (Fin n → 𝓧) :=
    fun n => AsymptoticRepresentation.productMeasure M μ θ₀ n
  let Qn : ∀ n, Measure (Fin n → 𝓧) :=
    fun n => AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n
  let Ln : ∀ n, (Fin n → 𝓧) → ℝ :=
    fun n => AsymptoticRepresentation.logLikelihood M θ₀ h n
  -- Lifted probability spaces.
  have hP'_isProb : ∀ n, IsProbabilityMeasure ((Pn n).compProd (κ n)) := fun n => by
    infer_instance
  have hQ'_isProb : ∀ n, IsProbabilityMeasure ((Qn n).compProd (κ n)) := fun n => by
    infer_instance
  -- Lifted integral-comparison bound, replacing the exact lifted change-of-measure
  -- identity. For a BCF `f : 𝓨 d →ᵇ ℝ`, the Markov-kernel-integrated test function
  -- `gκ f n ω := ∫ y, f y ∂(κ n ω)` is bounded measurable (`|gκ| ≤ ‖f‖`); via `integral_compProd`
  -- the lifted comparison on `(Fin n → 𝓧) × 𝓨 d` reduces to the base-space comparison of `gκ f`,
  -- which `productMeasure_integral_comparison_boundedMeasurable` bounds by `‖f‖·ρ_n` (one `ρ` for
  -- all `f`, derived internally from `hDQM` + `hPDF`).
  obtain ⟨ρ, hρ_tendsto, hρ_bound⟩ :=
    AsymptoticRepresentation.productMeasure_integral_comparison_boundedMeasurable M μ θ₀ ℓ hℓ hDQM
        hPDF h
  -- `gκ f n` : the κ_n-integral of `f`, as a bounded measurable function of `ω`.
  have hgκ_meas : ∀ (f : BoundedContinuousFunction (AsymptoticRepresentation.𝓨 d) ℝ) n,
      Measurable (fun ω : Fin n → 𝓧 => ∫ y, f y ∂(κ n ω)) := fun f n =>
    (f.continuous.stronglyMeasurable.integral_kernel (κ := κ n)).measurable
  have hgκ_bound : ∀ (f : BoundedContinuousFunction (AsymptoticRepresentation.𝓨 d) ℝ) n
      (ω : Fin n → 𝓧), |∫ y, f y ∂(κ n ω)| ≤ ‖f‖ := by
    intro f n ω
    rw [← Real.norm_eq_abs]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    calc ∫ y, ‖f y‖ ∂(κ n ω) ≤ ∫ _y, ‖f‖ ∂(κ n ω) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _))
            (integrable_const ‖f‖) (Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm y))
      _ = ‖f‖ := by
          rw [integral_const]; simp
  -- Define the lifted maps `X' n := snd` and `L' n := L_n ∘ fst`.
  set X' : ∀ n, (Fin n → 𝓧) × AsymptoticRepresentation.𝓨 d → AsymptoticRepresentation.𝓨 d :=
    fun _ => Prod.snd with hX'_def
  set L' : ∀ n, (Fin n → 𝓧) × AsymptoticRepresentation.𝓨 d → ℝ :=
    fun n p => Ln n p.1 with hL'_def
  have hX'_meas : ∀ n, Measurable (X' n) := fun _ => measurable_snd
  have hL'_meas : ∀ n, Measurable (L' n) := fun n => (hL_meas n).comp measurable_fst
  -- The lifted integral-comparison hypothesis for the Le Cam call (along `φ`), stated in terms of
  -- the lifted maps `X'`/`L'` so it matches `_of_integral_comparison`'s hypothesis syntactically.
  have h_int_cmp_subseq :
      ∃ ρ' : ℕ → ℝ, Filter.Tendsto ρ' Filter.atTop (𝓝 0) ∧
        ∀ (f : BoundedContinuousFunction (AsymptoticRepresentation.𝓨 d) ℝ) (m : ℕ),
          |∫ p, f (X' (φ m) p)
              ∂((Qn (φ m)).compProd (κ (φ m)))
            - ∫ p, f (X' (φ m) p) * Real.exp (L' (φ m) p)
                ∂((Pn (φ m)).compProd (κ (φ m)))| ≤ ‖f‖ * ρ' m := by
    refine ⟨ρ ∘ φ, hρ_tendsto.comp hφ.tendsto_atTop, fun f m => ?_⟩
    -- `X' (φ m) p = p.2` and `L' (φ m) p = Ln (φ m) p.1` by definition.
    change |∫ p, f (Prod.snd p) ∂((Qn (φ m)).compProd (κ (φ m)))
        - ∫ p, f (Prod.snd p) * Real.exp (Ln (φ m) p.1)
            ∂((Pn (φ m)).compProd (κ (φ m)))| ≤ ‖f‖ * (ρ ∘ φ) m
    -- Reduce both compProd integrals to base-space integrals of `gκ f (φ m)`.
    have hint_Q : Integrable (fun p : (Fin (φ m) → 𝓧) × AsymptoticRepresentation.𝓨 d => f (Prod.snd
        p))
        ((Qn (φ m)).compProd (κ (φ m))) :=
      (integrable_const ‖f‖).mono'
        (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => by
          simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (Prod.snd p)))
    have hexpL_int : Integrable (fun ω => Real.exp (Ln (φ m) ω)) (Pn (φ m)) := h_exp_int_full (φ m)
    have h_fst_eq : ((Pn (φ m)).compProd (κ (φ m))).map Prod.fst = Pn (φ m) :=
      MeasureTheory.Measure.fst_compProd (Pn (φ m)) (κ (φ m))
    have hint_P : Integrable
        (fun p : (Fin (φ m) → 𝓧) × AsymptoticRepresentation.𝓨 d =>
          f (Prod.snd p) * Real.exp (Ln (φ m) p.1))
        ((Pn (φ m)).compProd (κ (φ m))) := by
      -- Dominate by `‖f‖ * exp(Ln ∘ fst)`, integrable via `fst_compProd` pushforward.
      have hdom_int : Integrable
          ((fun ω : Fin (φ m) → 𝓧 => ‖f‖ * Real.exp (Ln (φ m) ω)) ∘ Prod.fst)
          ((Pn (φ m)).compProd (κ (φ m))) := by
        refine Integrable.comp_measurable ?_ measurable_fst
        rw [h_fst_eq]
        exact hexpL_int.const_mul ‖f‖
      have hP_aesm : AEStronglyMeasurable
          (fun p : (Fin (φ m) → 𝓧) × AsymptoticRepresentation.𝓨 d =>
            f (Prod.snd p) * Real.exp (Ln (φ m) p.1))
          ((Pn (φ m)).compProd (κ (φ m))) :=
        ((f.continuous.measurable.comp measurable_snd).mul
          (Real.continuous_exp.measurable.comp
            ((hL_meas (φ m)).comp measurable_fst))).aestronglyMeasurable
      refine hdom_int.mono' hP_aesm (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Function.comp_apply, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      gcongr
      exact (Real.norm_eq_abs _).symm.trans_le (f.norm_coe_le_norm _)
    -- compProd reduction (Q-side): `∫ f(snd) d(Q⊗κ) = ∫ ω, gκ f ω ∂Q`.
    have hQ_red : ∫ p, f (Prod.snd p) ∂((Qn (φ m)).compProd (κ (φ m)))
        = ∫ ω, (∫ y, f y ∂(κ (φ m) ω)) ∂(Qn (φ m)) := by
      rw [MeasureTheory.Measure.integral_compProd hint_Q]
    -- compProd reduction (P-side): `∫ f(snd)·exp(Ln(fst)) d(P⊗κ) = ∫ ω, gκ f ω · exp(Ln ω) ∂P`.
    have hP_red : ∫ p, f (Prod.snd p) * Real.exp (Ln (φ m) p.1)
            ∂((Pn (φ m)).compProd (κ (φ m)))
        = ∫ ω, (∫ y, f y ∂(κ (φ m) ω)) * Real.exp (Ln (φ m) ω) ∂(Pn (φ m)) := by
      rw [MeasureTheory.Measure.integral_compProd hint_P]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      -- inner: `∫ y, f y · exp(Ln ω) ∂κ ω = (∫ y, f y ∂κ ω) · exp(Ln ω)`.
      simp only
      rw [integral_mul_const]
    rw [hQ_red, hP_red]
    -- Apply the base-space bounded-measurable comparison with `g := gκ f`, `C := ‖f‖`.
    exact hρ_bound (fun n ω => ∫ y, f y ∂(κ n ω)) ‖f‖ (hgκ_meas f) (norm_nonneg f)
      (hgκ_bound f) (φ m)
  -- Joint kernel-bind = compProd pushforward identity (for the sequence-side weak conv).
  have h_joint_seq_eq : ∀ n,
      (Pn n).bind ((κ n) ×ₖ
          Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h n)
            (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n))
        = ((Pn n).compProd (κ n)).map (fun p => (X' n p, L' n p)) := by
    intro n
    refine MeasureTheory.Measure.ext (fun s hs => ?_)
    rw [MeasureTheory.Measure.bind_apply hs (Kernel.aemeasurable _)]
    have h_map_meas : Measurable (fun p : (Fin n → 𝓧) × AsymptoticRepresentation.𝓨 d =>
        (X' n p, L' n p)) :=
      (hX'_meas n).prodMk (hL'_meas n)
    rw [MeasureTheory.Measure.map_apply h_map_meas hs]
    rw [MeasureTheory.Measure.compProd_apply (h_map_meas hs)]
    refine MeasureTheory.lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change ((κ n) ×ₖ Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h n)
        (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n)) ω s
      = (κ n) ω (Prod.mk ω ⁻¹' ((fun p : (Fin n → 𝓧) × AsymptoticRepresentation.𝓨 d =>
        (X' n p, L' n p)) ⁻¹' s))
    -- Both sides are `(κ n) ω {y | (y, L_n ω) ∈ s}`.
    -- LHS: `((κ n) ×ₖ det(L_n))(ω) s = κ(ω) {y | (y, L_n ω) ∈ s}` via `prod_apply'`
    --   + `lintegral_deterministic` (the deterministic kernel evaluation picks `L_n ω`).
    -- RHS: `κ(ω) (Prod.mk ω ⁻¹' ((fun p => (X' p, L' p)) ⁻¹' s))
    --       = κ(ω) {y | (y, L_n ω) ∈ s}`.
    have h_lhs_compute :
        ((κ n) ×ₖ Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h n)
          (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n)) ω s
          = (κ n) ω {y | (y, AsymptoticRepresentation.logLikelihood M θ₀ h n ω) ∈ s} := by
      rw [ProbabilityTheory.Kernel.prod_apply' (κ n) _ ω hs]
      -- Inner integrand: `(deterministic L_n) ω (Prod.mk a ⁻¹' s)
      --   = indicator (Prod.mk a ⁻¹' s) 1 (L_n ω)`.
      have h_inner : ∀ a : AsymptoticRepresentation.𝓨 d,
          (Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h n)
            (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n)) ω (Prod.mk a ⁻¹' s)
          = Set.indicator
              {y : AsymptoticRepresentation.𝓨 d | (y, AsymptoticRepresentation.logLikelihood M θ₀ h
                  n ω) ∈ s}
              (1 : AsymptoticRepresentation.𝓨 d → ℝ≥0∞) a := by
        intro a
        rw [ProbabilityTheory.Kernel.deterministic_apply' _ _ (measurable_prodMk_left hs)]
        by_cases ha : (a, AsymptoticRepresentation.logLikelihood M θ₀ h n ω) ∈ s
        · have h1 : AsymptoticRepresentation.logLikelihood M θ₀ h n ω ∈ Prod.mk a ⁻¹' s := ha
          have h2 : a ∈ {y : AsymptoticRepresentation.𝓨 d |
              (y, AsymptoticRepresentation.logLikelihood M θ₀ h n ω) ∈ s} := ha
          simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
        · have h1 : AsymptoticRepresentation.logLikelihood M θ₀ h n ω ∉ Prod.mk a ⁻¹' s := ha
          have h2 : a ∉ {y : AsymptoticRepresentation.𝓨 d |
              (y, AsymptoticRepresentation.logLikelihood M θ₀ h n ω) ∈ s} := ha
          simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      simp_rw [h_inner]
      have h_set_meas : MeasurableSet
          {y : AsymptoticRepresentation.𝓨 d | (y, AsymptoticRepresentation.logLikelihood M θ₀ h n ω)
              ∈ s} :=
        measurable_prodMk_right hs
      rw [MeasureTheory.lintegral_indicator h_set_meas]
      simp only [Pi.one_apply, MeasureTheory.setLIntegral_const, one_mul]
    rw [h_lhs_compute]
    -- RHS: `κ(ω) (Prod.mk ω ⁻¹' (...))` simplifies via `hX'_def, hL'_def`.
    congr 1
  -- Target tilted joint law identification: `(P_n ⊗ κ_n).map (X', L') ⇝ π.map tilt_map`.
  have h_subseq_joint_log' :
      WeakConverges
        (fun k_idx => ((Pn (φ k_idx)).compProd (κ (φ k_idx))).map
          (fun p => (X' (φ k_idx) p, L' (φ k_idx) p)))
        (π.map tilt_map) := by
    -- Match target form: `π.map (fun p => (p.1, ⟪h,p.2⟫ - ½⟪h, J h⟫)) = π.map tilt_map`.
    have h_target_rewrite :
        (π.map (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)))
            = π.map tilt_map := rfl
    -- LHS sequence equality: bind form = compProd.map form via `h_joint_seq_eq`.
    have h_seq_eq : (fun k_idx => (Pn (φ k_idx)).bind ((κ (φ k_idx)) ×ₖ
          Kernel.deterministic (AsymptoticRepresentation.logLikelihood M θ₀ h (φ k_idx))
            (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h (φ k_idx))))
        = (fun k_idx => ((Pn (φ k_idx)).compProd (κ (φ k_idx))).map
            (fun p => (X' (φ k_idx) p, L' (φ k_idx) p))) := by
      funext k_idx; exact h_joint_seq_eq (φ k_idx)
    rw [h_target_rewrite, h_seq_eq] at h_subseq_joint_log
    exact h_subseq_joint_log
  -- Sequence-side `(Q_n).bind κ_n = ((Q_n).compProd κ_n).map snd` identity.
  have h_Q_bind_eq : ∀ n : ℕ,
      (Qn n).bind (κ n) = ((Qn n).compProd (κ n)).map Prod.snd := by
    intro n
    refine MeasureTheory.Measure.ext (fun s hs => ?_)
    rw [MeasureTheory.Measure.bind_apply hs (Kernel.aemeasurable _)]
    rw [MeasureTheory.Measure.map_apply measurable_snd hs]
    rw [MeasureTheory.Measure.compProd_apply (measurable_snd hs)]
    refine MeasureTheory.lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change (κ n) ω s = (κ n) ω (Prod.mk ω ⁻¹' (Prod.snd ⁻¹' s))
    -- `Prod.mk ω ⁻¹' (Prod.snd ⁻¹' s) = s` as a set of `𝓨 d`.
    congr 1
  -- Apply Le Cam 3 on the lifted space.
  -- Note: the lifted UI must be re-expressed in terms of `P'_n = P_n ⊗ κ_n` and
  -- `L'_n = L_n ∘ fst`. But `∫⁻ p, exp(L'_n p) ∂P'_n = ∫⁻ ω, exp(L_n ω) ∂P_n` since
  -- `κ_n` is Markov (mass 1 on the second coordinate). Same for the `min ... M` part.
  have h_UI_lifted : ∀ ε : ℝ, 0 < ε →
      ∃ Mbd : ℝ, 0 ≤ Mbd ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ p, Real.exp (L' (φ n) p) - min (Real.exp (L' (φ n) p)) Mbd
          ∂(((Pn (φ n)).compProd (κ (φ n)))) ≤ ε := by
    intro ε hε
    obtain ⟨Mbd, hMbd, N₀, hN₀⟩ := h_UI_subseq ε hε
    refine ⟨Mbd, hMbd, N₀, fun n hn => ?_⟩
    -- Push the integral through `compProd.fst = Pn` (Markov-κ keeps mass).
    have h_fst_eq : ((Pn (φ n)).compProd (κ (φ n))).map Prod.fst = Pn (φ n) :=
      MeasureTheory.Measure.fst_compProd (Pn (φ n)) (κ (φ n))
    have h_integrand_factors : (fun p : (Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d =>
          Real.exp (L' (φ n) p) - min (Real.exp (L' (φ n) p)) Mbd)
        = (fun ω : Fin (φ n) → 𝓧 =>
            Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
              min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd) ∘ Prod.fst
                  := by
      funext p; rfl
    rw [h_integrand_factors]
    have h_int_meas : Measurable (fun ω : Fin (φ n) → 𝓧 =>
          Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
            min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd) :=
      ((Real.continuous_exp.measurable.comp (hL_meas (φ n))).sub
        ((Real.continuous_exp.measurable.comp (hL_meas (φ n))).min measurable_const))
    -- Use `integral_map` on the fst pushforward, then identify `compProd.map fst = Pn`.
    have h_compose_eq :
        ∫ p : (Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d, ((fun ω : Fin (φ n) → 𝓧 =>
            Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
              min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd) ∘
                  Prod.fst) p
          ∂((Pn (φ n)).compProd (κ (φ n)))
        = ∫ ω : Fin (φ n) → 𝓧,
            Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
              min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd
          ∂(Pn (φ n)) := by
      calc ∫ p : (Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d, ((fun ω : Fin (φ n) → 𝓧 =>
              Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
                min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd) ∘
                    Prod.fst) p
            ∂((Pn (φ n)).compProd (κ (φ n)))
          = ∫ ω, Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
              min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd
            ∂(((Pn (φ n)).compProd (κ (φ n))).map Prod.fst) :=
            (MeasureTheory.integral_map measurable_fst.aemeasurable
              h_int_meas.aestronglyMeasurable).symm
        _ = ∫ ω : Fin (φ n) → 𝓧,
              Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
                min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd
            ∂(Pn (φ n)) := by rw [h_fst_eq]
    rw [h_compose_eq]
    -- Now `Pn (φ n) = AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)`. The `let` should
    -- unfold defeq.
    exact hN₀ n hn
  -- Apply Le Cam 3 on the lifted system, via the contiguity-footing integral-comparison variant.
  have h_lecam := Contiguity.weak_limit_under_Q_of_lecam_third_of_integral_comparison
    (Ω := fun n => (Fin (φ n) → 𝓧) × AsymptoticRepresentation.𝓨 d) (E := AsymptoticRepresentation.𝓨
        d)
    (fun n => (Pn (φ n)).compProd (κ (φ n)))
    (fun n => (Qn (φ n)).compProd (κ (φ n)))
    (fun n => X' (φ n)) (fun n => L' (φ n))
    (fun n => hX'_meas (φ n)) (fun n => hL'_meas (φ n))
    h_int_cmp_subseq
    (π.map tilt_map) h_subseq_joint_log'
    h_UI_lifted h_exp_int_πtilt h_exp_int_πtilt_eq_one
  -- `h_lecam` reads: `((Q' (φ n)).map (X' (φ n))) ⇝ ((π.map tilt_map).withDensity exp).map fst`.
  -- Rewrite LHS: `(Q'_n).map (X'_n) = (Q_n.compProd κ_n).map snd = (Q_n).bind κ_n`.
  have h_lecam_rewritten :
      WeakConverges
        (fun n => (Qn (φ n)).bind (κ (φ n)))
        (((π.map tilt_map).withDensity
          (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst)
              := by
    intro f
    have := h_lecam f
    have h_rewrite : ∀ n, ((Qn (φ n)).compProd (κ (φ n))).map (X' (φ n))
        = (Qn (φ n)).bind (κ (φ n)) := fun n => (h_Q_bind_eq (φ n)).symm
    simp_rw [h_rewrite] at this
    exact this
  -- Subsequence version of `h_weak_under_h`: `((Q (φ n)).bind κ_{φ n}) ⇝ L_h`.
  have h_weak_subseq :
      WeakConverges
        (fun n => (Qn (φ n)).bind (κ (φ n))) L_h :=
    fun f => (h_weak_under_h f).comp hφ.tendsto_atTop
  -- Weak limits are unique on `𝓨 d`.
  have h_target_prob :
      IsProbabilityMeasure
        (((π.map tilt_map).withDensity
          (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst)
              := by
    have h_mass_one :
        ((π.map tilt_map).withDensity
          (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))) Set.univ = 1
              := by
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
          MeasureTheory.setLIntegral_univ]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_exp_int_πtilt
        (Filter.Eventually.of_forall (fun q => (Real.exp_pos _).le))]
      rw [h_exp_int_πtilt_eq_one, ENNReal.ofReal_one]
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.map_apply measurable_fst MeasurableSet.univ,
        Set.preimage_univ]
    exact h_mass_one
  have h_L_h_eq :
      L_h = ((π.map tilt_map).withDensity
        (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst :=
            by
    refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure ?_
    intro f
    exact tendsto_nhds_unique (h_weak_subseq f) (h_lecam_rewritten f)
  -- Final: re-express RHS as `(π.withDensity (exp ∘ g ∘ snd)).map fst`. Inlined here
  -- because `AsymptoticRepresentation.tilted_marginal_simplify` is `private`.
  rw [h_L_h_eq]
  have h_tilt_meas' : Measurable
      (fun p : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k => (p.1, g p.2)) :=
    measurable_fst.prodMk (hg_meas.comp measurable_snd)
  have h_exp_snd_meas :
      Measurable (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2)) :=
    (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
  rw [Measure.withDensity_map_eq_map_withDensity π _ h_tilt_meas'
    (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2)) h_exp_snd_meas]
  rw [MeasureTheory.Measure.map_map measurable_fst h_tilt_meas']
  rfl

/-! ## Main theorem: `LAN_representation_kernel` (kernel-form vdV Theorem 8.3 / Theorem 7.10)

Given DQM at `θ₀`, non-singular Fisher information `J`, and a Markov-kernel
family `κ_n : (Fin n → 𝓧) ⇝ 𝓨 d` whose `productMeasure`-bind under each
local alternative `P^n_{θ₀+h/√n}` weakly converges to `L h`, there exists a
Markov kernel `κ̃ : Θ ⇝ 𝓨 d` such that for every `h`,

    L_h = N(h, J⁻¹) >>= κ̃.

This is the kernel-form refinement of `AsymptoticRepresentation.LAN_representation`
required by Theorem 8.11's Bayes-risk lower bound. The proof strategy mirrors
the deterministic-T case (Steps 1–8 in `AsymptoticRepresentation.lean`): score CLT + LAN
expansion + Le Cam 3 + Prohorov tightness + Urysohn subsequence principle +
condDistrib-based representation kernel construction; every
`(productMeasure ...).map (T n)` is replaced by `(productMeasure ...).bind (κ n)`.
Step 7 (representation-kernel construction) requires the kernel-form Girsanov /
Cameron-Martin tilt applied to the joint law of `(δ, κ_n(ω))` rather than
`(δ, T_n(ω))`.

Hypotheses:
- `M, μ, θ₀, ℓ, hℓ, hDQM, hPDF` — vdV §7.5 regularity bundle (same as the
  deterministic-T form; the Le Cam transfer runs on the contiguity footing via
  the integral-comparison bound, so no common-support hypothesis is needed).
- `J, hJ_pd, hJ` — Fisher information matrix at `θ₀` + identification.
- `κ, hκ_Markov` — the kernel sequence (replaces deterministic `T n` +
  `hT_meas`); the Markov-kernel property is what makes the sequence randomised.
- `L, hκ_weak` — the per-`h` limit + weak convergence (replaces deterministic
  `hT_weak`).
- `gauss, hGauss` — Gaussian-shift family (same as deterministic-T form).
- The typeclass bundle on `𝓨 d` — `StandardBorelSpace + Nonempty +
  HasOuterApproxClosed + BorelSpace`; the topological data the `condDistrib`
  construction needs. -/
theorem LAN_representation_kernel
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : AsymptoticRepresentation.Θ k) (ℓ : 𝓧 → AsymptoticRepresentation.Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- form (vdV Theorem 8.11 requires it non-singular = PosDef).
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ : ∀ u v : AsymptoticRepresentation.Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- `AsymptoticRepresentation.LAN_representation`. The Bayes-near-optimal decision rule
    -- is naturally a randomised statistic.
    (κ : ∀ n, Kernel (Fin n → 𝓧) (AsymptoticRepresentation.𝓨 d))
    (hκ_Markov : ∀ n, IsMarkovKernel (κ n))
    -- Replaces deterministic-T form's `hT_weak`. Note: `Measure.bind` is the
    -- kernel-composition op `(productMeasure ...).bind (κ n)`; the
    -- deterministic-T form's `(productMeasure ...).map (T n)` is the
    -- special case `κ n = Kernel.deterministic (T n) hT_meas`.
    (L : AsymptoticRepresentation.Θ k → Measure (AsymptoticRepresentation.𝓨 d))
    [∀ h, IsProbabilityMeasure (L h)]
    (hκ_weak : ∀ h : AsymptoticRepresentation.Θ k,
      WeakConverges
        (fun n =>
          (AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).bind
            (κ n))
        (L h))
    -- limit experiment). Same as deterministic-T form.
    (gauss : AsymptoticRepresentation.Θ k → Measure (AsymptoticRepresentation.Θ k))
    (hGauss : GaussianShift.IsGaussianShift gauss J⁻¹)
    -- the `condDistrib`-based representation-kernel construction (same as
    -- deterministic-T form).
    [StandardBorelSpace (AsymptoticRepresentation.𝓨 d)] [Nonempty (AsymptoticRepresentation.𝓨 d)]
    [HasOuterApproxClosed (AsymptoticRepresentation.𝓨 d)] [BorelSpace (AsymptoticRepresentation.𝓨
        d)]
    -- only density-regularity input; no common-support hypothesis is needed (the
    -- kernel-form Le Cam transfer runs on the contiguity footing via the
    -- integral-comparison bound, derived internally from `hDQM` + `hPDF`).
    (hPDF : IsPDFOf M μ) :
    ∃ κ' : Kernel (AsymptoticRepresentation.Θ k) (AsymptoticRepresentation.𝓨 d), IsMarkovKernel κ' ∧
      ∀ h : AsymptoticRepresentation.Θ k, L h = (gauss h).bind κ' := by
  -- Derive `IsProbabilityMeasure (productMeasure M μ θ n)` internally from `hPDF`
  -- rather than requiring it as an external typeclass provider.
  haveI : ∀ θ : AsymptoticRepresentation.Θ k, ∀ n,
      IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n) :=
    fun θ n => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- Convenient: instance is also inferred at `θ₀` for the joint-subseq lemma.
  haveI hκM : ∀ n, IsMarkovKernel (κ n) := hκ_Markov
  -- At `h = 0`, `θ₀ + (√n)⁻¹ • 0 = θ₀`, so `hκ_weak 0` gives convergence under `P_θ₀^n`.
  have hκ_weak_0 : WeakConverges
      (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).bind (κ n)) (L 0) := by
    have h := hκ_weak 0
    simp only [smul_zero, add_zero] at h
    exact h
  -- Unpack `hPDF` into the per-parameter conditions that downstream helpers expect.
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ u : AsymptoticRepresentation.Θ k,
      ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
    fun t u => hPDF.density_integral_eq_one (θ₀ + t • u)
  have hint_perturb : ∀ t : ℝ, ∀ u : AsymptoticRepresentation.Θ k,
      Integrable (M.density (θ₀ + t • u)) μ :=
    fun t u => hPDF.density_integrable (θ₀ + t • u)
  -- Score CLT under `P^n_{θ₀}`.
  have hScoreCLT : WeakConverges
      (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : AsymptoticRepresentation.Θ k) J) :=
    AsymptoticRepresentation.scoreSum_weakly_converges M μ θ₀ ℓ hℓ h_one hint
      h_one_perturb hint_perturb hDQM J hJ_pd.posSemidef hJ
  -- The exact LAN log-ratio identity (which needed the common-support hypothesis)
  -- is not constructed here; `limit_law_under_h_kernel` runs the Le Cam transfer on
  -- the contiguity footing, deriving the integral-comparison bound internally from
  -- `hDQM` + `hPDF`.
  -- Step 1: `Δ_n` converges weakly to `multivariateGaussian 0 J` under `P^n_{θ₀}`.
  have h_Δ_tight := AsymptoticRepresentation.score_clt_local M μ θ₀ ℓ hℓ hDQM J hJ hScoreCLT
  -- Step 2 (kernel form): extract a joint subsequence `φ` with limit `π`.
  -- First, derive `h_Δ_meas` so that the joint-kernel signature uses a fixed witness.
  have h_Δ_meas_pre : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n) := by
    intro n
    unfold AsymptoticRepresentation.scoreSum
    have h_sum : Measurable (fun ω : Fin n → 𝓧 => ∑ i, ℓ (ω i)) :=
      Finset.univ.measurable_sum (fun i _ => hℓ.comp (measurable_pi_apply i))
    exact h_sum.const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  obtain ⟨φ, hφ_mono, π, hπ_prob, h_joint⟩ :=
    joint_weak_subsequence_kernel M μ θ₀ ℓ h_Δ_meas_pre κ (L 0) hκ_weak_0
      (ProbabilityTheory.multivariateGaussian (0 : AsymptoticRepresentation.Θ k) J) h_Δ_tight
  -- **π's second marginal is `multivariateGaussian 0 J`**: this follows from the
  -- continuous-mapping theorem applied to the snd projection of the joint kernel.
  -- The deterministic body's `h_π_snd` argument adapts directly because, for any
  -- Markov kernels `κ_n : (Fin n → 𝓧) ⇝ 𝓨 d` and the deterministic kernel for
  -- `scoreSum ℓ n`, `((P^n).bind (κ_n ×ₖ Kernel.deterministic (scoreSum_n))).map snd =
  -- (P^n).map (scoreSum ℓ n)`. We isolate this as a kernel-form lemma:
  -- Reuse `h_Δ_meas_pre` as the witness throughout.
  set h_Δ_meas := h_Δ_meas_pre with h_Δ_meas_def
  have h_π_snd : π.map Prod.snd =
      ProbabilityTheory.multivariateGaussian (0 : AsymptoticRepresentation.Θ k) J := by
    -- The joint kernel `κ_n ×ₖ Kernel.deterministic (scoreSum ℓ n)` has snd
    -- marginal equal to the (deterministic) pushforward of `scoreSum ℓ n` under
    -- `(P^n).bind κ_n = P^n` (since for Markov `κ_n` the bind is a probability).
    -- More directly: `((P^n).bind (κ_n ×ₖ det(scoreSum))).map snd =
    -- (P^n).map (scoreSum ℓ n)` via `Kernel.lintegral_prod_deterministic`.
    apply joint_kernel_snd_eq_scoreSum_pushforward M μ θ₀ ℓ h_Δ_meas κ φ π
      hφ_mono h_joint
    -- Weak convergence of the second marginal: snd of the joint converges to the
    -- weak limit of the snd marginal.
    have h_snd_seq : WeakConverges
        (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).map
          (AsymptoticRepresentation.scoreSum ℓ (φ k_idx)))
        (ProbabilityTheory.multivariateGaussian (0 : AsymptoticRepresentation.Θ k) J) :=
      hScoreCLT.comp hφ_mono
    exact h_snd_seq
  -- Refine the existence target. The representation kernel does not depend on T
  -- or κ — only on π. Re-use `AsymptoticRepresentation.representationKernel`.
  refine ⟨AsymptoticRepresentation.representationKernel J π, inferInstance, ?_⟩
  intro h
  -- Step 3 (kernel form): joint weak convergence with the log-likelihood ratio.
  -- Discharge `h_slutsky_bridge_kernel` via `slutsky_bridge_of_lanResidual_kernel`
  -- (the kernel-form analogue of `AsymptoticRepresentation.slutsky_bridge_of_lanResidual`).
  -- The LAN residual `o_P(1)` is supplied by `lanResidual_tendsto_productMeasure`
  -- (same as the deterministic body of `AsymptoticRepresentation.LAN_representation`).
  have h_lanResidual_full :=
    AsymptoticRepresentation.lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      h_one hint h_one_perturb hint_perturb hDQM J hJ h
  have h_lanResidual_subseq : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ k_idx)).real
        {ω : Fin (φ k_idx) → 𝓧 | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h (φ k_idx) ω
                 - (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ k_idx) ω⟫ - (1/2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|})
        atTop (𝓝 0) := fun ε hε =>
    (h_lanResidual_full ε hε).comp hφ_mono.tendsto_atTop
  have h_slutsky_kernel := slutsky_bridge_of_lanResidual_kernel
    M μ θ₀ ℓ h_Δ_meas J κ h π φ h_lanResidual_subseq
  have h_joint_log := joint_weak_with_logLikelihood_kernel
    M μ θ₀ ℓ h_Δ_meas hDQM J hJ κ h π φ hφ_mono h_joint h_slutsky_kernel
  -- Internally derive `vLog` + `hLogLik_weak` (same as deterministic body).
  let vLog : AsymptoticRepresentation.Θ k → NNReal := fun h' =>
    (h'.ofLp ⬝ᵥ J.mulVec h'.ofLp).toNNReal
  have h_vLog_coe : ∀ h' : AsymptoticRepresentation.Θ k,
      (vLog h' : ℝ) = h'.ofLp ⬝ᵥ J.mulVec h'.ofLp := by
    intro h'
    have h_nn : 0 ≤ h'.ofLp ⬝ᵥ J.mulVec h'.ofLp := by
      have := hJ_pd.posSemidef.re_dotProduct_nonneg (x := (h'.ofLp : Fin k → ℝ))
      simpa using this
    exact Real.coe_toNNReal _ h_nn
  have h_vLog_eq_fisher : ∀ h' : AsymptoticRepresentation.Θ k,
      (vLog h' : ℝ)
        = ⟪h', (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h'))⟫ := by
    intro h'
    rw [h_vLog_coe]
    change _ = inner ℝ h' ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h')
    rw [Matrix.inner_toEuclideanCLM]
  -- Marginal log-likelihood CLT (same chain as deterministic body).
  have hLogLik_weak : ∀ h' : AsymptoticRepresentation.Θ k,
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.logLikelihood M θ₀ h' n))
        (ProbabilityTheory.gaussianReal (-(vLog h' : ℝ) / 2) (vLog h')) := by
    intro h'
    have h_inner_cont : Continuous (fun v : AsymptoticRepresentation.Θ k => ⟪h', v⟫) :=
      continuous_const.inner continuous_id
    have h_inner_meas : Measurable (fun v : AsymptoticRepresentation.Θ k => ⟪h', v⟫) :=
      h_inner_cont.measurable
    have h_compA : (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫))
        = (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (AsymptoticRepresentation.scoreSum ℓ n)).map
            (fun v : AsymptoticRepresentation.Θ k => ⟪h', v⟫)) := by
      funext n
      exact (Measure.map_map h_inner_meas (h_Δ_meas n)).symm
    have h_scalarCLT : WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫))
        (ProbabilityTheory.gaussianReal 0 (vLog h')) := by
      rw [h_compA]
      have h_map := hScoreCLT.map h_inner_cont h_inner_meas
      rwa [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal h'
        hJ_pd.posSemidef] at h_map
    have h_sub_cont : Continuous (fun y : ℝ => y - (vLog h' : ℝ) / 2) := by fun_prop
    have h_sub_meas : Measurable (fun y : ℝ => y - (vLog h' : ℝ) / 2) :=
      h_sub_cont.measurable
    have h_compB : (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2))
        = (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫)).map
            (fun y : ℝ => y - (vLog h' : ℝ) / 2)) := by
      funext n
      exact (Measure.map_map h_sub_meas
        (h_inner_meas.comp (h_Δ_meas n))).symm
    have h_shiftedCLT : WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2))
        (ProbabilityTheory.gaussianReal (-(vLog h' : ℝ) / 2) (vLog h')) := by
      rw [h_compB]
      have h_map := h_scalarCLT.map h_sub_cont h_sub_meas
      rw [ProbabilityTheory.gaussianReal_map_sub_const ((vLog h' : ℝ) / 2),
        zero_sub, ← neg_div] at h_map
      exact h_map
    have h_resid := AsymptoticRepresentation.lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      h_one hint h_one_perturb hint_perturb hDQM J hJ h'
    have hc_as_fisher :
        (vLog h' : ℝ) / 2 = (1/2 : ℝ) *
          ⟪h', (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h'))⟫ := by
      rw [← h_vLog_eq_fisher]; ring
    have hX_ae : ∀ n, AEMeasurable
        (fun ω : Fin n → 𝓧 =>
          ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      ((h_inner_meas.comp (h_Δ_meas n)).sub_const _).aemeasurable
    have hY_ae : ∀ n, AEMeasurable (AsymptoticRepresentation.logLikelihood M θ₀ h' n)
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h' n).aemeasurable
    have h_dist_tendsto : ∀ ε > 0, Tendsto
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 | ε ≤
            dist (⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
              (AsymptoticRepresentation.logLikelihood M θ₀ h' n ω)})
        atTop (𝓝 0) := by
      intro ε hε
      have h_set_eq : ∀ n,
          {ω : Fin n → 𝓧 | ε ≤
              dist (⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
              (AsymptoticRepresentation.logLikelihood M θ₀ h' n ω)}
            = {ω | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h' n ω
                - (⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (1/2 : ℝ) *
                    ⟪h', (WithLp.equiv 2 _).symm
                      (J.mulVec ((WithLp.equiv 2 _) h'))⟫)|} := by
        intro n
        ext ω
        simp only [Set.mem_setOf_eq, Real.dist_eq, hc_as_fisher]
        rw [abs_sub_comm]
      simp_rw [h_set_eq]
      exact h_resid ε hε
    exact WeakConverges.slutsky_of_tendstoInMeasure_dist
      hX_ae hY_ae h_shiftedCLT h_dist_tendsto
  -- Step 5 (kernel form): `L_h = Measure.map fst (π.withDensity (exp ∘ tilt))`.
  have h_mgfTilt_integrable := ProbabilityTheory.integrable_exp_tilt
    π J hJ_pd.posSemidef h_π_snd h
  have h_mgfTilt_integral_one := ProbabilityTheory.integral_exp_tilt_eq_one
    π J hJ_pd.posSemidef h_π_snd h
  have h_L_h_formula := limit_law_under_h_kernel
    M μ θ₀ ℓ hℓ hDQM J hJ_pd κ h π (L h) (hκ_weak h)
    φ hφ_mono h_joint_log
    hPDF (vLog h) (hLogLik_weak h)
    h_mgfTilt_integrable h_mgfTilt_integral_one
  -- Step 7: Gaussian-shift tilt — reuse the deterministic body's
  -- `gaussianShift_bind_eq_limit` (independent of T / κ).
  have hTilt_π : GaussianShift.HasTiltedLinearPushforward gauss (π.map Prod.snd) J := by
    rw [h_π_snd]
    exact GaussianShift.hasTiltedLinearPushforward_of_isGaussianShift hJ_pd hGauss
  exact AsymptoticRepresentation.gaussianShift_bind_eq_limit J hJ_pd gauss hGauss π h (L h)
    hTilt_π h_L_h_formula

/-! ## Subseq-form variant: `LAN_representation_along_subseq`

This is the subsequence form of `AsymptoticRepresentation.LAN_representation`.
It accepts joint weak convergence along an arbitrary strictly monotone subsequence
`φ : ℕ → ℕ` and concludes the corresponding per-`h` weak convergence along the
same subsequence, with limit
`(multivariateGaussian h J⁻¹).bind (representationKernel J π)`.

The formulation is reusable when joint convergence is known only along a
subsequence. Its hypotheses otherwise match `AsymptoticRepresentation.LAN_representation`. -/
theorem LAN_representation_along_subseq
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : AsymptoticRepresentation.Θ k) (ℓ : 𝓧 → AsymptoticRepresentation.Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ : ∀ u v : AsymptoticRepresentation.Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (T : ∀ n, (Fin n → 𝓧) → AsymptoticRepresentation.𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (hPDF : IsPDFOf M μ)
    -- weak convergence holds.
    (φ : ℕ → ℕ) (hφ_mono : StrictMono φ)
    (π : Measure (AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k))
        [IsProbabilityMeasure π]
    (hπ_conv : WeakConverges
      (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)).map
        (fun ω => (T (φ n) ω, AsymptoticRepresentation.scoreSum ℓ (φ n) ω))) π)
    [StandardBorelSpace (AsymptoticRepresentation.𝓨 d)] [Nonempty (AsymptoticRepresentation.𝓨 d)]
    [HasOuterApproxClosed (AsymptoticRepresentation.𝓨 d)] [BorelSpace (AsymptoticRepresentation.𝓨
        d)] :
    ∀ h : AsymptoticRepresentation.Θ k,
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ
            (θ₀ + (Real.sqrt (φ n))⁻¹ • h) (φ n)).map (T (φ n)))
        ((ProbabilityTheory.multivariateGaussian h J⁻¹).bind
          (AsymptoticRepresentation.representationKernel J π)) := by
  classical
  -- Derive product-measure probability instances internally from `hPDF`.
  haveI hProd_prob : ∀ θ : AsymptoticRepresentation.Θ k, ∀ n,
      IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n) :=
    fun θ n => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- Unpack `hPDF` into the per-parameter conditions that downstream helpers expect.
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ u : AsymptoticRepresentation.Θ k,
      ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
    fun t u => hPDF.density_integral_eq_one (θ₀ + t • u)
  have hint_perturb : ∀ t : ℝ, ∀ u : AsymptoticRepresentation.Θ k,
      Integrable (M.density (θ₀ + t • u)) μ :=
    fun t u => hPDF.density_integrable (θ₀ + t • u)
  -- Score CLT under `P^n_{θ₀}`.
  have hScoreCLT : WeakConverges
      (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : AsymptoticRepresentation.Θ k) J) :=
    AsymptoticRepresentation.scoreSum_weakly_converges M μ θ₀ ℓ hℓ h_one hint
      h_one_perturb hint_perturb hDQM J hJ_pd.posSemidef hJ
  -- Measurability of `scoreSum ℓ n`.
  have hΔ_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n) := by
    intro n
    unfold AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  -- Identify `π.map snd = multivariateGaussian 0 J` via `WeakConverges.snd_eq`
  -- (score CLT pulled along φ).
  have h_pair_meas : ∀ n, Measurable
      (fun ω : Fin n → 𝓧 => (T n ω, AsymptoticRepresentation.scoreSum ℓ n ω)) :=
    fun n => (hT_meas n).prodMk (hΔ_meas n)
  have h_marg : ∀ n,
      ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)).map
          (fun ω => (T (φ n) ω, AsymptoticRepresentation.scoreSum ℓ (φ n) ω))).map Prod.snd
        = (AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)).map
            (AsymptoticRepresentation.scoreSum ℓ (φ n)) := by
    intro n
    rw [Measure.map_map measurable_snd (h_pair_meas (φ n))]
    rfl
  have hScoreCLT_subseq : WeakConverges
      (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)).map
          (fun ω => (T (φ n) ω, AsymptoticRepresentation.scoreSum ℓ (φ n) ω))).map Prod.snd)
      (ProbabilityTheory.multivariateGaussian (0 : AsymptoticRepresentation.Θ k) J) := by
    simp_rw [h_marg]
    exact hScoreCLT.comp hφ_mono
  have h_π_snd : π.map Prod.snd =
      ProbabilityTheory.multivariateGaussian (0 : AsymptoticRepresentation.Θ k) J :=
    WeakConverges.snd_eq hπ_conv hScoreCLT_subseq
  -- vLog + h_vLog_eq_fisher (parametric for downstream lemmas).
  let vLog : AsymptoticRepresentation.Θ k → NNReal := fun h' =>
    (h'.ofLp ⬝ᵥ J.mulVec h'.ofLp).toNNReal
  have h_vLog_coe : ∀ h' : AsymptoticRepresentation.Θ k,
      (vLog h' : ℝ) = h'.ofLp ⬝ᵥ J.mulVec h'.ofLp := by
    intro h'
    have h_nn : 0 ≤ h'.ofLp ⬝ᵥ J.mulVec h'.ofLp := by
      have := hJ_pd.posSemidef.re_dotProduct_nonneg (x := (h'.ofLp : Fin k → ℝ))
      simpa using this
    exact Real.coe_toNNReal _ h_nn
  have h_vLog_eq_fisher : ∀ h' : AsymptoticRepresentation.Θ k,
      (vLog h' : ℝ)
        = ⟪h', (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h'))⟫ := by
    intro h'
    rw [h_vLog_coe]
    change _ = inner ℝ h' ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h')
    rw [Matrix.inner_toEuclideanCLM]
  -- Marginal log-likelihood CLT (same chain as deterministic body).
  have hLogLik_weak : ∀ h' : AsymptoticRepresentation.Θ k,
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.logLikelihood M θ₀ h' n))
        (ProbabilityTheory.gaussianReal (-(vLog h' : ℝ) / 2) (vLog h')) := by
    intro h'
    have h_inner_cont : Continuous (fun v : AsymptoticRepresentation.Θ k => ⟪h', v⟫) :=
      continuous_const.inner continuous_id
    have h_inner_meas : Measurable (fun v : AsymptoticRepresentation.Θ k => ⟪h', v⟫) :=
      h_inner_cont.measurable
    have h_compA : (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫))
        = (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (AsymptoticRepresentation.scoreSum ℓ n)).map
            (fun v : AsymptoticRepresentation.Θ k => ⟪h', v⟫)) := by
      funext n
      exact (Measure.map_map h_inner_meas (hΔ_meas n)).symm
    have h_scalarCLT : WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫))
        (ProbabilityTheory.gaussianReal 0 (vLog h')) := by
      rw [h_compA]
      have h_map := hScoreCLT.map h_inner_cont h_inner_meas
      rwa [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal h'
        hJ_pd.posSemidef] at h_map
    have h_sub_cont : Continuous (fun y : ℝ => y - (vLog h' : ℝ) / 2) := by fun_prop
    have h_sub_meas : Measurable (fun y : ℝ => y - (vLog h' : ℝ) / 2) :=
      h_sub_cont.measurable
    have h_compB : (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2))
        = (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫)).map
            (fun y : ℝ => y - (vLog h' : ℝ) / 2)) := by
      funext n
      exact (Measure.map_map h_sub_meas
        (h_inner_meas.comp (hΔ_meas n))).symm
    have h_shiftedCLT : WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2))
        (ProbabilityTheory.gaussianReal (-(vLog h' : ℝ) / 2) (vLog h')) := by
      rw [h_compB]
      have h_map := h_scalarCLT.map h_sub_cont h_sub_meas
      rw [ProbabilityTheory.gaussianReal_map_sub_const ((vLog h' : ℝ) / 2),
        zero_sub, ← neg_div] at h_map
      exact h_map
    have h_resid := AsymptoticRepresentation.lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      h_one hint h_one_perturb hint_perturb hDQM J hJ h'
    have hc_as_fisher :
        (vLog h' : ℝ) / 2 = (1/2 : ℝ) *
          ⟪h', (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h'))⟫ := by
      rw [← h_vLog_eq_fisher]; ring
    have hX_ae : ∀ n, AEMeasurable
        (fun ω : Fin n → 𝓧 =>
          ⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      ((h_inner_meas.comp (hΔ_meas n)).sub_const _).aemeasurable
    have hY_ae : ∀ n, AEMeasurable (AsymptoticRepresentation.logLikelihood M θ₀ h' n)
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h' n).aemeasurable
    have h_dist_tendsto : ∀ ε > 0, Tendsto
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 | ε ≤
            dist (⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
              (AsymptoticRepresentation.logLikelihood M θ₀ h' n ω)})
        atTop (𝓝 0) := by
      intro ε hε
      have h_set_eq : ∀ n,
          {ω : Fin n → 𝓧 | ε ≤
              dist (⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
              (AsymptoticRepresentation.logLikelihood M θ₀ h' n ω)}
            = {ω | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h' n ω
                - (⟪h', AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (1/2 : ℝ) *
                    ⟪h', (WithLp.equiv 2 _).symm
                      (J.mulVec ((WithLp.equiv 2 _) h'))⟫)|} := by
        intro n
        ext ω
        simp only [Set.mem_setOf_eq, Real.dist_eq, hc_as_fisher]
        rw [abs_sub_comm]
      simp_rw [h_set_eq]
      exact h_resid ε hε
    exact WeakConverges.slutsky_of_tendstoInMeasure_dist
      hX_ae hY_ae h_shiftedCLT h_dist_tendsto
  -- Now produce the per-h conclusion.
  intro h
  -- Step 3: Slutsky bridge along φ.
  have h_lanResidual_full :=
    AsymptoticRepresentation.lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      h_one hint h_one_perturb hint_perturb hDQM J hJ h
  have h_lanResidual_subseq : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)).real
        {ω : Fin (φ n) → 𝓧 | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω
                 - (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ n) ω⟫ - (1/2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|})
        atTop (𝓝 0) := fun ε hε =>
    (h_lanResidual_full ε hε).comp hφ_mono.tendsto_atTop
  have hSlutsky_π := AsymptoticRepresentation.slutsky_bridge_of_lanResidual M μ θ₀ ℓ hℓ J T
    hT_meas h π φ
    (fun n => AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n)
    h_lanResidual_subseq
  -- Step 3': joint weak convergence with log-likelihood along φ.
  have h_joint_log := AsymptoticRepresentation.joint_weak_with_logLikelihood
    M μ θ₀ ℓ hℓ hDQM J hJ T hT_meas h π φ hφ_mono hπ_conv hSlutsky_π
  -- MGF integrability from `h_π_snd`.
  have h_mgfTilt_integrable := ProbabilityTheory.integrable_exp_tilt
    π J hJ_pd.posSemidef h_π_snd h
  have h_mgfTilt_integral_one := ProbabilityTheory.integral_exp_tilt_eq_one
    π J hJ_pd.posSemidef h_π_snd h
  -- Tilt-map abbreviation (`c = ½⟨h, Jh⟩`).
  set c : ℝ := (1 / 2 : ℝ) *
      ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ with hc_def
  let tilt_map : AsymptoticRepresentation.𝓨 d × AsymptoticRepresentation.Θ k →
      AsymptoticRepresentation.𝓨 d × ℝ :=
    fun p => (p.1, ⟪h, p.2⟫ - c)
  have htilt_meas : Measurable tilt_map :=
    measurable_fst.prodMk
      (((continuous_const.inner continuous_id).measurable.comp measurable_snd).sub_const _)
  haveI h_tilt_prob : IsProbabilityMeasure (π.map tilt_map) :=
    MeasureTheory.Measure.isProbabilityMeasure_map htilt_meas.aemeasurable
  -- UI of `exp(logLikelihood)` along φ (full sequence + StrictMono.id_le).
  -- Derive the contiguity-footing companions internally from `hDQM` + `hPDF`
  -- (replaces the exact change-of-measure identity that required common support).
  have hL_meas : ∀ n, Measurable (AsymptoticRepresentation.logLikelihood M θ₀ h n) :=
    fun n => AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n
  have h_exp_int_full :=
    AsymptoticRepresentation.productMeasure_exp_logLikelihood_integrable M μ θ₀ ℓ hℓ hDQM hPDF h
  have h_mass_full :=
    AsymptoticRepresentation.productMeasure_integral_exp_logLikelihood_tendsto_one M μ θ₀ ℓ hℓ hDQM
        hPDF h
  have h_UI_full := Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one
    (Ω := fun n => Fin n → 𝓧)
    (fun n => AsymptoticRepresentation.productMeasure M μ θ₀ n)
    (fun n => AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
    (fun n => AsymptoticRepresentation.logLikelihood M θ₀ h n) hL_meas
    h_exp_int_full h_mass_full (vLog h) (hLogLik_weak h)
  have h_UI_subseq : ∀ ε : ℝ, 0 < ε →
      ∃ Mbd : ℝ, 0 ≤ Mbd ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω) -
            min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)) Mbd
          ∂(AsymptoticRepresentation.productMeasure M μ θ₀ (φ n)) ≤ ε := by
    intro ε hε
    obtain ⟨Mbd, hMbd, N₀, hN₀⟩ := h_UI_full ε hε
    refine ⟨Mbd, hMbd, N₀, fun n hn => hN₀ (φ n)
      (le_trans hn (hφ_mono.id_le n))⟩
  -- Step 5: Le Cam 3 along φ via the contiguity-footing variant. Output:
  -- `(Q_{φ n}).map (T (φ n)) ⇝ ((π.map tilt_map).withDensity (exp ∘ snd)).map Prod.fst`.
  -- The exact change-of-measure identity is replaced by the integral-comparison bound
  -- (derived internally from `hDQM` + `hPDF`), specialised to the subsequence `φ`.
  obtain ⟨ρ, hρ_tendsto, hρ_bound⟩ :=
    AsymptoticRepresentation.productMeasure_integral_comparison M μ θ₀ ℓ hℓ hDQM hPDF T hT_meas h
  have h_int_cmp_subseq :
      ∃ ρ' : ℕ → ℝ, Filter.Tendsto ρ' Filter.atTop (𝓝 0) ∧
        ∀ (f : BoundedContinuousFunction (AsymptoticRepresentation.𝓨 d) ℝ) (n : ℕ),
          |∫ ω, f (T (φ n) ω)
              ∂(AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt (φ n))⁻¹ • h) (φ n))
            - ∫ ω, f (T (φ n) ω) * Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ n) ω)
                ∂(AsymptoticRepresentation.productMeasure M μ θ₀ (φ n))| ≤ ‖f‖ * ρ' n :=
    ⟨ρ ∘ φ, hρ_tendsto.comp hφ_mono.tendsto_atTop, fun f n => hρ_bound f (φ n)⟩
  have h_lecam := Contiguity.weak_limit_under_Q_of_lecam_third_of_integral_comparison
    (Ω := fun n => Fin (φ n) → 𝓧) (E := AsymptoticRepresentation.𝓨 d)
    (fun n => AsymptoticRepresentation.productMeasure M μ θ₀ (φ n))
    (fun n => AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt (φ n))⁻¹ • h) (φ n))
    (fun n => T (φ n))
    (fun n => AsymptoticRepresentation.logLikelihood M θ₀ h (φ n))
    (fun n => hT_meas (φ n))
    (fun n => hL_meas (φ n))
    h_int_cmp_subseq
    (π.map tilt_map) h_joint_log
    h_UI_subseq h_mgfTilt_integrable h_mgfTilt_integral_one
  -- Reconcile `((π.map tilt_map).withDensity (exp ∘ snd)).map fst` with the
  -- tilted-marginal form `Measure.map fst (π.withDensity (exp ∘ tilt))`.
  have h_target_eq :
      ((π.map tilt_map).withDensity
          (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst
        = Measure.map Prod.fst
          (π.withDensity (fun p => ENNReal.ofReal
            (Real.exp (⟪h, p.2⟫ - (1 / 2 : ℝ) *
              ⟪h, (WithLp.equiv 2 _).symm
                    (J.mulVec ((WithLp.equiv 2 _) h))⟫)))) := by
    have h_exp_snd_meas :
        Measurable (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    rw [Measure.withDensity_map_eq_map_withDensity π _ htilt_meas
      (fun q : AsymptoticRepresentation.𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2)) h_exp_snd_meas]
    rw [MeasureTheory.Measure.map_map measurable_fst htilt_meas]
    rfl
  -- Re-express `h_lecam`'s conclusion in the `withDensity-of-π` form.
  have h_lecam' : WeakConverges
      (fun n => (AsymptoticRepresentation.productMeasure M μ
          (θ₀ + (Real.sqrt (φ n))⁻¹ • h) (φ n)).map (T (φ n)))
      (Measure.map Prod.fst
        (π.withDensity (fun p => ENNReal.ofReal
          (Real.exp (⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm
                  (J.mulVec ((WithLp.equiv 2 _) h))⟫))))) := by
    have := h_lecam
    rwa [h_target_eq] at this
  -- Step 7 (Gaussian shift identification): apply `gaussianShift_bind_eq_limit`.
  set gauss : AsymptoticRepresentation.Θ k → Measure (AsymptoticRepresentation.Θ k) :=
    fun h' => ProbabilityTheory.multivariateGaussian h' J⁻¹ with hgauss
  have hGauss : GaussianShift.IsGaussianShift gauss J⁻¹ :=
    GaussianShift.isGaussianShift_multivariateGaussian J⁻¹ hJ_pd.inv
  have hTilt_π : GaussianShift.HasTiltedLinearPushforward gauss (π.map Prod.snd) J := by
    rw [h_π_snd]
    exact GaussianShift.hasTiltedLinearPushforward_of_isGaussianShift hJ_pd hGauss
  -- IsProbabilityMeasure for the tilted-marginal target (needed by gaussianShift_bind_eq_limit).
  have h_int_one : ∫ p, Real.exp (⟪h, p.2⟫ - c) ∂π = 1 := by
    have h_eq : ∫ p, Real.exp (⟪h, p.2⟫ - c) ∂π
        = ∫ q : AsymptoticRepresentation.𝓨 d × ℝ, Real.exp q.2 ∂(π.map tilt_map) := by
      rw [integral_map htilt_meas.aemeasurable (by fun_prop)]
    rw [h_eq]
    exact h_mgfTilt_integral_one
  have h_int_integrable : Integrable (fun p : AsymptoticRepresentation.𝓨 d ×
      AsymptoticRepresentation.Θ k =>
      Real.exp (⟪h, p.2⟫ - c)) π := by
    have h_src := h_mgfTilt_integrable
    have h_strong : AEStronglyMeasurable
        (fun q : AsymptoticRepresentation.𝓨 d × ℝ => Real.exp q.2) (π.map tilt_map) := by fun_prop
    exact (integrable_map_measure h_strong htilt_meas.aemeasurable).mp h_src
  have h_lint_one : ∫⁻ p, ENNReal.ofReal (Real.exp (⟪h, p.2⟫ - c)) ∂π = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal h_int_integrable
        (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
      h_int_one, ENNReal.ofReal_one]
  haveI hWD_prob : IsProbabilityMeasure (π.withDensity (fun p => ENNReal.ofReal
      (Real.exp (⟪h, p.2⟫ - c)))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact h_lint_one
  haveI hL_h_prob : IsProbabilityMeasure
      (Measure.map Prod.fst (π.withDensity (fun p => ENNReal.ofReal
        (Real.exp (⟪h, p.2⟫ - c))))) :=
    MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- The Gaussian-shift bind equals the tilted-marginal target.
  have h_gauss_eq :
      Measure.map Prod.fst
          (π.withDensity (fun p => ENNReal.ofReal
            (Real.exp (⟪h, p.2⟫ - (1 / 2 : ℝ) *
              ⟪h, (WithLp.equiv 2 _).symm
                    (J.mulVec ((WithLp.equiv 2 _) h))⟫))))
        = (gauss h).bind (AsymptoticRepresentation.representationKernel J π) :=
    AsymptoticRepresentation.gaussianShift_bind_eq_limit J hJ_pd gauss hGauss π h
      (Measure.map Prod.fst (π.withDensity (fun p => ENNReal.ofReal
        (Real.exp (⟪h, p.2⟫ - c))))) hTilt_π rfl
  -- Combine: `(P_{φ n}_h).map T ⇝ tilted marginal = (gauss h).bind κ`.
  rw [← h_gauss_eq]
  exact h_lecam'

end LocalAsymptoticMinimax
end AsymptoticStatistics
