module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

/-!
# Randomized tests as Markov kernels — ForMathlib brick

A randomized test is carried in the testing theory as a **critical function** `φ : 𝓧 → ℝ`
with values in `[0,1]`: on observing `x` one rejects with probability `φ(x)`. The
decision-theoretic machinery instead quantifies over **Markov kernels** `𝓧 ⇝ Fin 2` (the
randomized `{accept, reject}` decision rules). This file builds the bridge:

* `randomizedTestKernel φ hφ` — the kernel sending `x` to the Bernoulli law
  `φ(x) δ₁ + (1 − φ(x)) δ₀` on `Fin 2`;
* its singleton masses, the Markov property under `0 ≤ φ ≤ 1`, and the integral formula
  `∫⁻ f d(randomizedTestKernel φ hφ x) = φ(x)·f(1) + (1 − φ(x))·f(0)`.

Theorem-agnostic and Mathlib-only: nothing here mentions models, levels or power.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.1 (Stating the Problem), supporting material for the formulation of a
randomized test as a critical function. (`TSH4 §3.1`.)

**Proof formalization notes.**
* The Bernoulli weights are `ENNReal.ofReal (φ x)` and `ENNReal.ofReal (1 − φ x)`, which makes
  the definition total: off the range `0 ≤ φ ≤ 1` the two weights simply fail to sum to `1`
  and the kernel is sub- or super-probabilistic. `isMarkovKernel_randomizedTestKernel` is the
  single place where the range condition is consumed, and it is stated with the two bare
  inequalities rather than the concept-layer critical-function predicate: this file sits in
  the bottom (Mathlib-only) layer and must not import the concept layer.
* Measurability of the kernel is checked through `Measure.measurable_of_measurable_coe` on the
  explicit two-atom formula. The minimax area builds an `ℝ≥0∞`-valued binary test the same
  way; the two are deliberately kept separate (that one is private and takes an `ℝ≥0∞`
  acceptance function, this one the `[0,1]`-real-valued critical function of testing theory).
* `Fin 2` has `MeasurableSingletonClass`, so `lintegral_randomizedTestKernel` needs no
  measurability hypothesis on the integrand.

**Bibliographic comments.** Randomized tests and their critical functions are due to
J. Neyman and E. S. Pearson ("On the problem of the most efficient tests of statistical
hypotheses," *Phil. Trans. R. Soc. A* **231** (1933), 289–337). Reading a randomized decision
rule as a Markov kernel from the sample space to the action space is due to A. Wald
(*Statistical Decision Functions*, Wiley, 1950).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **randomized-test kernel** of a critical function `φ`: on input `x` it answers `1`
(reject) with probability `φ(x)` and `0` (accept) with probability `1 − φ(x)`.

Total by construction: the weights are `ENNReal.ofReal`s, so values of `φ` outside `[0,1]` are
clamped at `0` and produce a non-Markov kernel rather than junk. -/
noncomputable def randomizedTestKernel (φ : 𝓧 → ℝ) (hφ : Measurable φ) : Kernel 𝓧 (Fin 2) :=
  Kernel.mk (fun x => ENNReal.ofReal (φ x) • Measure.dirac 1
      + ENNReal.ofReal (1 - φ x) • Measure.dirac 0)
    (by
      refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      exact (hφ.ennreal_ofReal.mul measurable_const).add
        ((measurable_const.sub hφ).ennreal_ofReal.mul measurable_const))

/-- Unfolding lemma: the kernel is the two-atom measure it is built from. -/
theorem randomizedTestKernel_apply
    -- LEAN-ONLY: measurability of the critical function; needed to form the kernel at all
    (φ : 𝓧 → ℝ) (hφ : Measurable φ) (x : 𝓧) :
    randomizedTestKernel φ hφ x
      = ENNReal.ofReal (φ x) • Measure.dirac 1 + ENNReal.ofReal (1 - φ x) • Measure.dirac 0 := by
  unfold randomizedTestKernel; rw [Kernel.coe_mk]

/-- The **rejection probability**: the kernel gives mass `φ(x)` to the reject action `1`. -/
theorem randomizedTestKernel_apply_one
    -- LEAN-ONLY: measurability of the critical function; needed to form the kernel at all
    (φ : 𝓧 → ℝ) (hφ : Measurable φ) (x : 𝓧) :
    randomizedTestKernel φ hφ x {1} = ENNReal.ofReal (φ x) := by
  rw [randomizedTestKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton (1 : Fin 2)),
    Measure.dirac_apply' _ (measurableSet_singleton (1 : Fin 2))]
  simp

/-- The **acceptance probability**: the kernel gives mass `1 − φ(x)` to the accept action
`0`. -/
theorem randomizedTestKernel_apply_zero
    -- LEAN-ONLY: measurability of the critical function; needed to form the kernel at all
    (φ : 𝓧 → ℝ) (hφ : Measurable φ) (x : 𝓧) :
    randomizedTestKernel φ hφ x {0} = ENNReal.ofReal (1 - φ x) := by
  rw [randomizedTestKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton (0 : Fin 2)),
    Measure.dirac_apply' _ (measurableSet_singleton (0 : Fin 2))]
  simp

/-- A `[0,1]`-valued critical function yields a **Markov kernel**. -/
theorem isMarkovKernel_randomizedTestKernel
    -- LEAN-ONLY: measurability of the critical function; needed to form the kernel at all
    (φ : 𝓧 → ℝ) (hφ : Measurable φ)
    -- USER-INPUT: the critical function is `[0,1]`-valued; Neyman–Pearson (1933)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1) :
    IsMarkovKernel (randomizedTestKernel φ hφ) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [randomizedTestKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, measure_univ, measure_univ, mul_one, mul_one,
    ← ENNReal.ofReal_add (h0 x) (by linarith [h1 x]),
    show φ x + (1 - φ x) = 1 by ring, ENNReal.ofReal_one]

/-- Integration against the randomized-test kernel is the two-point average
`φ(x)·f(1) + (1 − φ(x))·f(0)`. No measurability of `f` is needed (`Fin 2` is discrete). -/
theorem lintegral_randomizedTestKernel
    -- LEAN-ONLY: measurability of the critical function; needed to form the kernel at all
    (φ : 𝓧 → ℝ) (hφ : Measurable φ) (x : 𝓧) (f : Fin 2 → ℝ≥0∞) :
    ∫⁻ j, f j ∂(randomizedTestKernel φ hφ x)
      = ENNReal.ofReal (φ x) * f 1 + ENNReal.ofReal (1 - φ x) * f 0 := by
  rw [randomizedTestKernel_apply, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac, lintegral_dirac, smul_eq_mul, smul_eq_mul]

end StatLean.HypothesisTesting
