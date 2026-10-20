module
public import StatLean.Bayesian.MCMC.Defs

@[expose] public section

/-!
# Gibbs sampler correctness: single-site, two-block, and random-scan stationarity

Correctness of Gibbs updates for a target `ρ` on a product space `A × B`:

* each **one-coordinate update preserves `ρ`** (2F.5): refreshing a coordinate from its exact
  conditional leaves the joint invariant;
* the **two-block sweep** `gibbsSnd ∘ₖ gibbsFst` preserves `ρ` (2F.6; Gelman §11.1) — by
  the pinned `Kernel.Invariant.comp`;
* the **random-scan sweep** preserves `ρ` (2F.7): a mixture of invariant kernels is invariant.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §11.1
(Gibbs sampler), p. 276.

**Proof formalization notes.** For `gibbsSnd`, the bound measure `ρ.bind (gibbsSnd ρ)` evaluates
through `Prod.fst`: the update factors as `(Kernel.id ×ₖ ρ.condKernel)` composed with the first
projection, and `ρ.fst ⊗ₘ ρ.condKernel = ρ` is exactly the pinned disintegration
(`Measure.compProd_fst_condKernel` / `Measure.disintegrate`), plus the
`compProd = comp of prod` bridge (`Measure.compProd_eq_comp_prod`). `gibbsFst` is the same
argument through `Prod.swap`. Two-block is `Invariant.comp`; random-scan is `bind_mixKernel` plus
`w • ρ + (1 − w) • ρ = ρ` for `w ≤ 1` (`tsub_add_cancel_of_le`-style smul algebra).

**Bibliographic comments.** The Gibbs sampler is Geman and Geman (1984), named for the Gibbs
distributions of statistical mechanics; its two-stage (data-augmentation) form is Tanner and Wong
(1987) and its statistical mainstreaming Gelfand and Smith (1990). The "exact conditional preserves
the joint" argument formalized here is the validity core; convergence rates and ergodicity are
beyond this batch.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]

/-- **The second-coordinate Gibbs update preserves the target** (2F.5; Gelman §11.1). -/
theorem invariant_gibbsSnd (ρ : Measure (A × B)) [IsFiniteMeasure ρ]
    [StandardBorelSpace B] [Nonempty B] :
    Kernel.Invariant (gibbsSnd ρ) ρ := by
  unfold Kernel.Invariant gibbsSnd
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  change (Kernel.id ×ₖ ρ.condKernel) ∘ₘ ρ.fst = ρ
  rw [← Measure.compProd_eq_comp_prod]
  exact ρ.disintegrate _

/-- **The first-coordinate Gibbs update preserves the target** (2F.5; Gelman §11.1). -/
theorem invariant_gibbsFst (ρ : Measure (A × B)) [IsFiniteMeasure ρ]
    [StandardBorelSpace A] [Nonempty A] :
    Kernel.Invariant (gibbsFst ρ) ρ := by
  unfold Kernel.Invariant gibbsFst
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  -- goal: ((ρ.map Prod.swap).condKernel ×ₖ Kernel.id) ∘ₘ (ρ.map Prod.snd) = ρ
  have e2 : (Kernel.id ×ₖ (ρ.map Prod.swap).condKernel) ∘ₘ (ρ.map Prod.snd)
      = ρ.map Prod.swap := by
    have hfst : (Measure.map Prod.snd ρ) = (ρ.map Prod.swap).fst := Measure.fst_map_swap.symm
    rw [hfst, ← Measure.compProd_eq_comp_prod]
    exact (ρ.map Prod.swap).disintegrate _
  rw [← Kernel.map_prod_swap, ← Kernel.swap_comp_eq_map, ← Measure.comp_assoc, e2,
    Measure.swap_comp, Measure.map_map measurable_swap measurable_swap]
  simp

/-- **Two-block Gibbs stationarity** (2F.6; Gelman §11.1): the systematic sweep
"update `a`, then update `b`" preserves the target. -/
theorem invariant_twoBlockGibbs (ρ : Measure (A × B)) [IsFiniteMeasure ρ]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B] :
    Kernel.Invariant (gibbsSnd ρ ∘ₖ gibbsFst ρ) ρ :=
  (invariant_gibbsSnd ρ).comp (invariant_gibbsFst ρ)

/-- **Random-scan Gibbs stationarity** (2F.7; Gelman §11.1): the `w`-mixture of the two
one-coordinate updates preserves the target, for any mixing probability `w ≤ 1`. -/
theorem invariant_randomScanGibbs (ρ : Measure (A × B)) [IsFiniteMeasure ρ]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B] {w : ℝ≥0∞}
    -- USER-INPUT: the scan probability is a probability; Gelman §11.1
    (hw : w ≤ 1) :
    Kernel.Invariant (randomScanGibbs ρ w) ρ := by
  unfold Kernel.Invariant randomScanGibbs
  rw [bind_mixKernel, (invariant_gibbsFst ρ).def, (invariant_gibbsSnd ρ).def,
    ← add_smul, add_tsub_cancel_of_le hw, one_smul]

end StatLean.Bayesian
