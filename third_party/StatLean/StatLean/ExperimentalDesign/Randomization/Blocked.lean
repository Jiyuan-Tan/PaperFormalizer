module
public import StatLean.ExperimentalDesign.Stratified.ProductDesign
public import StatLean.ExperimentalDesign.Core.Stratification
public import StatLean.ExperimentalDesign.Randomization.CompleteRandomization

@[expose] public section

/-!
# Blocked (randomised block) randomization

A **blocked randomization** runs an independent completely randomised design inside
each block of a stratification `bl : U → B`, with per-block replications
`r b : T → ℕ`.  The randomised complete block design of the textbooks is the special
case `r b t = 1` (each treatment once per block).  This file constructs the design as
a product design over the blocks, glues the per-block allocations into a single
allocation of the whole population, and proves:

* the **marginal assignment probability** of a unit is its within-block allocation
  frequency `r_{b(i)}(t) / N_{b(i)}`;
* assignments in **different blocks are uncorrelated** — the independence that kills
  all cross-block terms in randomisation-theory variance computations.

Deeper blocked moments (within-block pair probabilities, blocked arm means) are
inherited from `CompleteRandomization` through the product-design marginal lemmas
and are deferred to a later round.

## Main results

* `blockedRandomization` — the design.
* `glueAllocation` — the combined allocation of the whole population.
* `blocked_expect_armIndicator` — the marginal assignment probability.
* `blocked_cov_armIndicator_of_ne_block` — independence across blocks.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988: the randomised block
design and its restricted randomisation — each treatment allocated within each block,
independently across blocks — §2.5, §9.2 (design (ii)) and §9.4 (where
`δᵏᵢⱼ δᵏ'ᵢ'ⱼ'` are independent for different blocks `i ≠ i'`).  (`Mead §2.5`,
`Mead §9.2`, `Mead §9.4`.)

**Proof formalization notes.**
* The sample space is the dependent product `∀ b, Allocation (Stratum bl b) T`; the
  glued allocation evaluates the block component of `bl i` at `⟨i, rfl⟩`.
* Both theorems are compositions: rewrite the glued indicator as a statistic of the
  single component `ω (bl i)`, then apply `pmfExpect_productDesign_comp` /
  `pmfCov_productDesign_of_ne` and (for the marginal) `expect_armIndicator` for the
  within-block completely randomised design.
-/

namespace StatLean.ExperimentalDesign

variable {U T B : Type*} [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T]
variable [Fintype B] [DecidableEq B]

/-- **Blocked randomization**: independent completely randomised designs within the
blocks of `bl`, with per-block replications `r b` (`Mead §2.5`, `Mead §9.2`). -/
noncomputable def blockedRandomization (bl : U → B) (r : B → T → ℕ)
    -- USER-INPUT: within each block the replications exhaust the block; Mead §2.5
    (hr : ∀ b, ∑ t, r b t = Fintype.card (Stratum bl b)) :
    PMF (∀ b, Allocation (Stratum bl b) T) :=
  productDesign fun b => completeRandomization (r b) (hr b)

/-- The **glued allocation**: the per-block allocations assembled into one allocation
of the whole population. -/
def glueAllocation (bl : U → B) (ω : ∀ b, Allocation (Stratum bl b) T) :
    Allocation U T :=
  fun i => ω (bl i) ⟨i, rfl⟩

/-- **Marginal assignment probability under blocked randomization**: unit `i` receives
treatment `t` with its within-block frequency `r_{bl i}(t) / N_{bl i}`
(`Mead §9.4`, `P(δᵏᵢⱼ = 1) = 1/t` in the equireplicate case). -/
theorem blocked_expect_armIndicator (bl : U → B) (r : B → T → ℕ)
    (hr : ∀ b, ∑ t, r b t = Fintype.card (Stratum bl b)) (i : U) (t : T) :
    pmfExpect (blockedRandomization bl r hr)
        (fun ω => armIndicator t i (glueAllocation bl ω))
      = (r (bl i) t : ℝ) / (Fintype.card (Stratum bl (bl i)) : ℝ) := by
  classical
  refine Eq.trans ?_ (expect_armIndicator (r (bl i)) (hr (bl i)) (⟨i, rfl⟩ : Stratum bl (bl i)) t)
  exact pmfExpect_productDesign_comp (fun b => completeRandomization (r b) (hr b))
    (bl i) (armIndicator t (⟨i, rfl⟩ : Stratum bl (bl i)))

/-- **Independence across blocks**: assignment indicators of units in different
blocks are uncorrelated (`Mead §9.4`, independence of the randomisation in different
blocks). -/
theorem blocked_cov_armIndicator_of_ne_block (bl : U → B) (r : B → T → ℕ)
    (hr : ∀ b, ∑ t, r b t = Fintype.card (Stratum bl b)) {i j : U}
    -- LEAN-ONLY: the two units lie in distinct blocks; within-block covariances are
    -- those of the completely randomised design
    (hij : bl i ≠ bl j) (t s : T) :
    pmfCov (blockedRandomization bl r hr)
        (fun ω => armIndicator t i (glueAllocation bl ω))
        (fun ω => armIndicator s j (glueAllocation bl ω)) = 0 := by
  classical
  exact pmfCov_productDesign_of_ne (fun b => completeRandomization (r b) (hr b)) hij
    (armIndicator t (⟨i, rfl⟩ : Stratum bl (bl i)))
    (armIndicator s (⟨j, rfl⟩ : Stratum bl (bl j)))

end StatLean.ExperimentalDesign
