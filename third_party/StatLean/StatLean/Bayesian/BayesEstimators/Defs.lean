module
public import StatLean.Bayesian.BernsteinVonMises.Defs

@[expose] public section

/-!
# Bayes point estimators: loss conditions and the posterior-risk process (data model)

Data model for vdV §10.3 (Bayes point estimators). A loss `ℓ : ℝ^k → [0,∞]` acts on the
**local** scale: the Bayes point estimator `Tₙ` minimizes
`t ↦ ∫ ℓ(√n(t − θ)) dΠ(θ | X₁..Xₙ)`, equivalently (after the local change of variables)
`τ ↦ ∫ ℓ(τ − h) d(local posterior)(h)` at `τ = √n(Tₙ − θ₀)`.

* `SeparatedLoss` — vdV's growth condition `sup_{‖h‖ ≤ M} ℓ ≤ inf_{‖h‖ ≥ 2M} ℓ` (every
  `M`), strict for at least one `M`, in pointwise (sup-free) form;
* `PolyGrowthLoss p` — the polynomial growth `ℓ(h) ≤ 1 + ‖h‖ᵖ`;
* `bpePosteriorRisk` — the local posterior-risk process
  `Zₙ(τ)(ω) = ∫ ℓ(τ − h) d(bvmLocalPosterior)(h)`;
* `bpeGaussCriterion` — the deterministic limit criterion
  `g(u) = ∫ ℓ(u − z) dN(0, J⁻¹)(z)` (the process of the Bayes-point-estimator theorem recentred by
  `X`:
  `∫ ℓ(t − h) dN(X, J⁻¹)(h) = g(t − X)`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.3 (Point Estimators), p. 147 (the loss conditions and the posterior-risk
minimization problem).

**Proof formalization notes.** Laptop-only data model. Losses are `ℝ≥0∞`-valued (matching
`BowlShaped` and `anderson_lemma_loss`); the risk process is a `lintegral`. The separation
condition is stated pointwise (`‖x‖ ≤ M → 2M ≤ ‖y‖ → ℓ x ≤ ℓ y`), equivalent to vdV's
sup–inf form but free of suprema over uncountable sets.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- **vdV's loss separation condition** (p. 147): `sup_{‖x‖ ≤ M} ℓ ≤ inf_{‖y‖ ≥ 2M} ℓ` for
every `M > 0`, with strict inequality for at least one pair; stated pointwise. -/
structure SeparatedLoss (ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞) : Prop where
  /-- Constitutive (vdV §10.3, p. 147): the two-scale monotonicity
  `sup_{‖h‖ ≤ M} ℓ ≤ inf_{‖h‖ ≥ 2M} ℓ`, in pointwise form
  `‖x‖ ≤ M → 2M ≤ ‖y‖ → ℓ x ≤ ℓ y`. -/
  mono : ∀ M : ℝ, 0 < M → ∀ x y, ‖x‖ ≤ M → 2 * M ≤ ‖y‖ → ℓ x ≤ ℓ y
  /-- Constitutive (vdV §10.3, p. 147): "with strict inequality for at least one `M`" — a
  genuine **gap** between the two levels, i.e. `sup_{‖x‖ ≤ M} ℓ ≤ c < inf_{‖y‖ ≥ 2M} ℓ` for
  some scale `M` and threshold `c`. Stated with an explicit separating `c` to avoid `sSup`/
  `sInf` while remaining equivalent to vdV's sup–inf form.

  The gap — not merely one pair with `ℓ x < ℓ y` — is what the tightness step of the
  Bayes-point-estimator theorem consumes (vdV p. 148 sets `η := ℓ̲(2δ) − ℓ̄(δ) > 0`). The
  weaker pointwise reading is genuinely insufficient: the `0–1` loss
  `ℓ(u) = 1 − 1_{u = 0}` satisfies `mono`
  and has `ℓ 0 < ℓ y`, yet its sup and inf coincide at every scale, its posterior risk is
  constant against an atomless posterior, every point is a minimizer, and tightness fails.
  Consistently, vdV's own sufficient condition ("`ℓ(h) = ℓ₀(‖h‖)` with `ℓ₀` nondecreasing and
  **not constant on `(0, ∞)`**") excludes that loss. -/
  strict : ∃ M : ℝ, 0 < M ∧ ∃ c : ℝ≥0∞,
    (∀ x, ‖x‖ ≤ M → ℓ x ≤ c) ∧ ∀ y, 2 * M ≤ ‖y‖ → c < ℓ y

/-- **Polynomial growth of the loss** (vdV p. 147): `ℓ(h) ≤ 1 + ‖h‖ᵖ`. -/
def PolyGrowthLoss (p : ℝ) (ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞) : Prop :=
  ∀ h, ℓ h ≤ ENNReal.ofReal (1 + ‖h‖ ^ p)

/-- The **local posterior-risk process**: `Zₙ(τ)(ω) = ∫ ℓ(τ − h) d(local posterior)(h)`
(vdV p. 148, the process `Zₙ` after the local change of variables). -/
noncomputable def bpePosteriorRisk (κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧)
    [IsMarkovKernel κ] (π : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure π]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞) (n : ℕ)
    (τ : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  ∫⁻ h, ℓ (τ - h) ∂(bvmLocalPosterior κ π θ₀ n ω)

/-- The **deterministic limit criterion** `g(u) = ∫ ℓ(u − z) dN(0, J⁻¹)(z)` (vdV §10.3:
the limit process is `t ↦ g(t − X)` for `X ∼ N(0, J⁻¹)`). -/
noncomputable def bpeGaussCriterion (J : Matrix (Fin k) (Fin k) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞) (u : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  ∫⁻ z, ℓ (u - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹)

end StatLean.Bayesian
