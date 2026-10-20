module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# Orlicz (Luxemburg) norms — definitions

For an *Orlicz generator* $\psi : \mathbb{R} \to \mathbb{R}$ (in applications:
nonnegative, convex, increasing on $[0,\infty)$ with $\psi(0)=0$), the
*Luxemburg / Orlicz norm* of a random variable $X$ is
$$ \|X\|_{\psi} \;=\; \inf\Bigl\{ K > 0 \;:\;
   \mathbb{E}\,\psi\bigl(|X|/K\bigr) \le 1 \Bigr\}, $$
with the convention $\inf \emptyset = \infty$. The two canonical generators are
$$ \psi_2(x) = e^{x^2} - 1, \qquad \psi_1(x) = e^{x} - 1, $$
giving the **sub-Gaussian norm** $\|X\|_{\psi_2}$ and the **sub-exponential
norm** $\|X\|_{\psi_1}$. Note $\mathbb{E}\,\psi_2(|X|/K) \le 1
\iff \mathbb{E}\exp(X^2/K^2) \le 2$, so the threshold-$1$ Luxemburg convention
reproduces the book's threshold-$2$ MGF conditions exactly.

**Reference.** Roman Vershynin, *High-Dimensional Probability: An Introduction
with Applications in Data Science*, 2nd ed., Cambridge University Press.
General Orlicz norm: Remark 2.8.9 and Exercises 2.42–2.43 (no numbered
definition in this edition). Sub-Gaussian norm: §2.6.1, Definition 2.6.4,
Eq. (2.18). Sub-exponential norm: §2.8.2, Definition 2.8.4, Eq. (2.25).

**Proof formalization notes.** The norm is `ℝ≥0∞`-valued (Mathlib `eLpNorm`
precedent): `orliczNorm` is the `⨅`-over-gauge-set of the coercion, so it is
`⊤` exactly when the gauge set is empty (e.g. a non-sub-Gaussian `X` under
`ψ₂`). The gauge condition uses the lower Lebesgue integral of
`ENNReal.ofReal ∘ ψ`, so no integrability side conditions enter the
*definition*; they surface only in the API lemmas. Edge behavior: for `K = 0`
the gauge condition is excluded by `0 < K`; a.e.-zero `X` has norm `0` (every
`K > 0` is in the gauge set once `ψ(0) = 0`); the infimum need not be attained
— attainment under continuity/monotonicity of `ψ` is `Orlicz/Attainment.lean`.
This file is definitions and `rfl`-level API only (laptop-only surface); all
analytic content lives in the sibling `Orlicz/` files. The identifiers `psi` /
`psiStar` are already taken by the log-MGF machinery in
`SubGaussian/Chernoff.lean`, hence `psiTwo` / `psiOne`.

**Bibliographic comments.** Orlicz spaces originate with W. Orlicz, "Über eine
gewisse Klasse von Räumen vom Typus B," *Bull. Int. Acad. Pol. Ser. A* 8/9
(1932), 207–220; the gauge-functional form used here is due to W. A. J.
Luxemburg, *Banach function spaces*, Thesis, Delft, 1955. The ψ₂/ψ₁ special
cases as the standard carriers of sub-Gaussian / sub-exponential behavior
follow Vershynin; see also Buldygin–Kozachenko, *Metric Characterization of
Random Variables and Random Processes*, AMS 2000.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The **Luxemburg gauge set** of `X` under the Orlicz generator `ψ`
(HDP Remark 2.8.9 / Exercise 2.43): the set of scales `K > 0` at which the
`ψ`-moment of `|X|/K` is at most `1`. Stated with the lower Lebesgue integral
of `ENNReal.ofReal ∘ ψ`, so it is meaningful with no integrability hypotheses.
Edge behavior: negative values of `ψ` are truncated to `0` by
`ENNReal.ofReal`; for the batch's generators `ψ ≥ 0` on the range of `|·|`,
so no truncation occurs. -/
def orliczSet (ψ : ℝ → ℝ) (X : Ω → ℝ) (μ : Measure Ω) : Set ℝ≥0 :=
  {K : ℝ≥0 | 0 < K ∧ ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (K : ℝ))) ∂μ ≤ 1}

/-- The **Orlicz (Luxemburg) norm** `‖X‖_ψ` (HDP Remark 2.8.9 / Exercises
2.42–2.43): the infimum of the gauge set, valued in `ℝ≥0∞`. Edge behavior:
`⊤` when no gauge exists (empty `⨅`), `0` iff arbitrarily small gauges work
(for a.e.-zero `X` with `ψ 0 = 0`, every `K > 0` is a gauge). -/
noncomputable def orliczNorm (ψ : ℝ → ℝ) (X : Ω → ℝ)
    (μ : Measure Ω := by volume_tac) : ℝ≥0∞ :=
  ⨅ K ∈ orliczSet ψ X μ, (K : ℝ≥0∞)

/-- The sub-Gaussian Orlicz generator `ψ₂(x) = exp(x²) − 1` (HDP §2.6).
Named `psiTwo` because `psi` is taken by the log-MGF of
`SubGaussian/Chernoff.lean`. -/
noncomputable def psiTwo : ℝ → ℝ := fun x => Real.exp (x ^ 2) - 1

/-- The sub-exponential Orlicz generator `ψ₁(x) = exp(x) − 1` (HDP §2.8). -/
noncomputable def psiOne : ℝ → ℝ := fun x => Real.exp x - 1

/-- **Sub-Gaussian norm** `‖X‖_{ψ₂}` (HDP Definition 2.6.4, Eq. (2.18)):
`inf {K > 0 : E exp(X²/K²) ≤ 2}`, realized as the Luxemburg norm for the
generator `ψ₂(x) = exp(x²) − 1` (the thresholds `2` and `1` agree exactly).
Edge behavior inherited from `orliczNorm`: `⊤` iff `X` is not sub-Gaussian. -/
noncomputable def subGaussianNorm (X : Ω → ℝ)
    (μ : Measure Ω := by volume_tac) : ℝ≥0∞ :=
  orliczNorm psiTwo X μ

/-- **Sub-exponential norm** `‖X‖_{ψ₁}` (HDP Definition 2.8.4, Eq. (2.25)):
`inf {K > 0 : E exp(|X|/K) ≤ 2}`, realized as the Luxemburg norm for
`ψ₁(x) = exp(x) − 1`. -/
noncomputable def subExponentialNorm (X : Ω → ℝ)
    (μ : Measure Ω := by volume_tac) : ℝ≥0∞ :=
  orliczNorm psiOne X μ

@[simp] lemma psiTwo_apply (x : ℝ) : psiTwo x = Real.exp (x ^ 2) - 1 := rfl

@[simp] lemma psiOne_apply (x : ℝ) : psiOne x = Real.exp x - 1 := rfl

lemma mem_orliczSet_iff {ψ : ℝ → ℝ} {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ≥0} :
    K ∈ orliczSet ψ X μ ↔
      0 < K ∧ ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (K : ℝ))) ∂μ ≤ 1 :=
  Iff.rfl

lemma subGaussianNorm_def (X : Ω → ℝ) (μ : Measure Ω) :
    subGaussianNorm X μ = orliczNorm psiTwo X μ := rfl

lemma subExponentialNorm_def (X : Ω → ℝ) (μ : Measure Ω) :
    subExponentialNorm X μ = orliczNorm psiOne X μ := rfl

/-- Any member of the gauge set bounds the Orlicz norm. -/
lemma orliczNorm_le_of_mem {ψ : ℝ → ℝ} {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ≥0}
    -- LEAN-ONLY: gauge-set membership is the caller-supplied witness; pure
    -- infimum manipulation, no book content.
    (hK : K ∈ orliczSet ψ X μ) :
    orliczNorm ψ X μ ≤ (K : ℝ≥0∞) :=
  iInf₂_le K hK

end StatLean.ConcentrationInequalities
