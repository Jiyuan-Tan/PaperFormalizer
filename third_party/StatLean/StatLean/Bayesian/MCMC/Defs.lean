module
public import StatLean.Bayesian.ForMathlib.KernelMixture
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.Probability.Kernel.Invariance

@[expose] public section

/-!
# MCMC — core data model (Metropolis–Hastings and Gibbs kernels)

Data model for Markov chain Monte Carlo correctness:

* **Metropolis–Hastings** on a countable state space `S`: given a target `π` and a proposal
  kernel `q`, the acceptance ratio
  $$\alpha(x, y) = \min\Big\{1, \frac{\pi\{y\}\,q(y, \{x\})}{\pi\{x\}\,q(x, \{y\})}\Big\}$$
  and the transition kernel "propose from `q`, accept with probability `α`, else stay";
* **Gibbs updates** on a product space `A × B`: refresh one coordinate from its exact conditional
  under the target `ρ` (via Mathlib's disintegration `Measure.condKernel`), keeping the other;
  the **random-scan** sweep is the `mixKernel` mixture of the two one-coordinate updates.

Stationarity vocabulary is the pinned Mathlib's: `ProbabilityTheory.Kernel.Invariant` and
`Kernel.IsReversible` (detailed balance), with `IsReversible.invariant` and `Invariant.comp`.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §11.1–11.2,
pp. 276–278.

**Proof formalization notes.** Laptop-only data model — definitions only. On a countable `S` with
measurable singletons the space is discrete, so the MH kernel's coe-measurability is automatic
(`Measurable.of_discrete`) and the definition carries no side conditions; the rejection mass
`1 − ∫ α(x, y) q(x, dy)` sits on the Dirac at the current state. `ℝ≥0∞` division junk: where
`π{x}·q(x,{y}) = 0` the ratio is `∞` and `α = 1` — harmless, as detailed balance is proven with
the symmetric `min` lemma. Gibbs kernels need `A`/`B` standard Borel for `condKernel`; no
countability is required there.

**Bibliographic comments.** The Metropolis algorithm is N. Metropolis, A. W. Rosenbluth,
M. N. Rosenbluth, A. H. Teller and E. Teller, "Equation of state calculations by fast computing
machines," *J. Chem. Phys.* 21 (1953), 1087–1092, generalized to asymmetric proposals by
W. K. Hastings, "Monte Carlo sampling methods using Markov chains and their applications,"
*Biometrika* 57 (1970), 97–109. Gibbs sampling is S. Geman and D. Geman, "Stochastic relaxation,
Gibbs distributions, and the Bayesian restoration of images," *IEEE Trans. PAMI* 6 (1984),
721–741, brought into mainstream statistics by A. E. Gelfand and A. F. M. Smith, "Sampling-based
approaches to calculating marginal densities," *J. Amer. Statist. Assoc.* 85 (1990), 398–409
(with data augmentation from M. A. Tanner and W. H. Wong, 1987).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-! ### Metropolis–Hastings on a countable state space -/

section MetropolisHastings

variable {S : Type*} [mS : MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The **Metropolis–Hastings acceptance probability**
`α(x, y) = min{1, π{y}·q(y,{x}) / (π{x}·q(x,{y}))}` (Gelman §11.1). `ℝ≥0∞` junk: `α = 1`
wherever the denominator vanishes. -/
noncomputable def mhAccept (π : Measure S) (q : Kernel S S) : S → S → ℝ≥0∞ :=
  fun x y => min 1 (π {y} * q y {x} / (π {x} * q x {y}))

/-- The **Metropolis–Hastings kernel**: propose from `q(x, ·)`, accept with probability
`mhAccept π q x ·`, otherwise stay at `x` (Gelman §11.1, boxed algorithm). -/
noncomputable def mhKernel (π : Measure S) (q : Kernel S S) : Kernel S S :=
  ⟨fun x =>
      (q x).withDensity (mhAccept π q x)
        + (1 - ∫⁻ y, mhAccept π q x y ∂(q x)) • Measure.dirac x,
    Measurable.of_discrete⟩

@[simp]
theorem mhKernel_apply (π : Measure S) (q : Kernel S S) (x : S) :
    mhKernel π q x
      = (q x).withDensity (mhAccept π q x)
          + (1 - ∫⁻ y, mhAccept π q x y ∂(q x)) • Measure.dirac x := rfl

end MetropolisHastings

/-! ### Gibbs updates on a product space -/

section Gibbs

variable {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]

/-- The **first-coordinate Gibbs update** for a target `ρ` on `A × B`: refresh `a` from the exact
conditional `ρ(da | b)`, keep `b` (Gelman §11.1). -/
noncomputable def gibbsFst (ρ : Measure (A × B)) [IsFiniteMeasure ρ]
    [StandardBorelSpace A] [Nonempty A] : Kernel (A × B) (A × B) :=
  ((((ρ.map Prod.swap).condKernel) ×ₖ Kernel.id)).comap Prod.snd measurable_snd

/-- The **second-coordinate Gibbs update** for a target `ρ` on `A × B`: keep `a`, refresh `b` from
the exact conditional `ρ(db | a)` (Gelman §11.1). -/
noncomputable def gibbsSnd (ρ : Measure (A × B)) [IsFiniteMeasure ρ]
    [StandardBorelSpace B] [Nonempty B] : Kernel (A × B) (A × B) :=
  (Kernel.id ×ₖ ρ.condKernel).comap Prod.fst measurable_fst

/-- The **random-scan Gibbs sweep**: update the first coordinate with probability `w`, else the
second (Gelman §11.1). -/
noncomputable def randomScanGibbs (ρ : Measure (A × B)) [IsFiniteMeasure ρ]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B]
    (w : ℝ≥0∞) : Kernel (A × B) (A × B) :=
  mixKernel w (gibbsFst ρ) (gibbsSnd ρ)

end Gibbs

end StatLean.Bayesian
