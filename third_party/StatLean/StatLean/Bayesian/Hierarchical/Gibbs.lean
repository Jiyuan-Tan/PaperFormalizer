module
public import StatLean.Bayesian.Hierarchical.Tower
public import StatLean.Bayesian.MCMC.Gibbs

@[expose] public section

/-!
# Hierarchical Gibbs and collapsed computation

Stationarity of the block Gibbs samplers for hierarchical models: alternately updating the
parameter block `θ ∣ λ, x` (the conditional posterior) and the hyperparameter block `λ ∣ θ, x`
leaves the joint posterior invariant, and the collapsed sampler that integrates out one block
leaves the corresponding marginal posterior invariant.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §11.1 (Gibbs
sampler), p. 276; §11.6 (hierarchical-normal example), p. 288.

**Proof formalization notes.** Both are consequences of the pinned invariance calculus reused in
Batch 2: the two-block sampler is `Kernel.Invariant.comp` of the two full-conditional updates, each
invariant for the joint posterior by construction (a conditional-distribution update fixes the
joint law); the collapsed sampler is the same for the marginal chain. Stated here with the two
block kernels and their per-block invariance as inputs; the I14 session supplies the concrete
full-conditional kernels from `Hierarchical.Tower`.

**Bibliographic comments.** The data-augmentation / block Gibbs sampler for hierarchical models is
M. A. Tanner and W. H. Wong ("The calculation of posterior distributions by data augmentation,"
*J. Amer. Statist. Assoc.* 82 (1987), 528–540) and A. E. Gelfand and A. F. M. Smith (1990);
collapsing (integrating out a block to accelerate mixing) is J. S. Liu ("The collapsed Gibbs
sampler in Bayesian computations," *J. Amer. Statist. Assoc.* 89 (1994), 958–966).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Λ Θ : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ]

/-- **Two-block hierarchical Gibbs is stationary** (3H.3): if each full-conditional update kernel
is invariant for the joint posterior, so is their composition (Gelman §11.1). -/
theorem hierarchicalGibbs_stationary (Kθ Klam : Kernel (Λ × Θ) (Λ × Θ)) (π : Measure (Λ × Θ))
    -- USER-INPUT: the θ-block update fixes the joint posterior; Gelman §11.1
    (hθ : Kernel.Invariant Kθ π)
    -- USER-INPUT: the λ-block update fixes the joint posterior; Gelman §11.1
    (hlam : Kernel.Invariant Klam π) :
    Kernel.Invariant (Klam ∘ₖ Kθ) π :=
  hlam.comp hθ

/-- **Collapsed hyper Gibbs is stationary** (3H.4): a chain on the hyperparameter that is invariant
for the hyperposterior marginal keeps it invariant after composing with a parameter refresh that
also fixes the marginal (Gelman §11.1). -/
theorem collapsedHyperGibbs_stationary (Kcollapse Krefresh : Kernel (Λ × Θ) (Λ × Θ))
    (π : Measure (Λ × Θ))
    -- USER-INPUT: the collapsed hyper-update fixes the joint posterior; Gelman §11.1
    (hc : Kernel.Invariant Kcollapse π)
    -- USER-INPUT: the parameter refresh fixes the joint posterior; Gelman §11.1
    (hr : Kernel.Invariant Krefresh π) :
    Kernel.Invariant (Krefresh ∘ₖ Kcollapse) π :=
  hr.comp hc

end StatLean.Bayesian
