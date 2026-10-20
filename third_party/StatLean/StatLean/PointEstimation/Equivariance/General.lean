module
public import StatLean.PointEstimation.Equivariance.Defs
public import Mathlib.GroupTheory.GroupAction.Defs

@[expose] public section

/-!
# Equivariance — invariance of the risk function

The single structural fact that makes equivariant estimation work: in an invariant
estimation problem the risk function of an equivariant estimator is **constant along the
induced parameter action**. This file proves that fact and its two standard corollaries.

* `risk_smul` — `R(ḡθ, δ) = R(θ, δ)` for every `g` in the acting group;
* `risk_const_of_pretransitive` — when the induced action on `Θ` is transitive, the risk
  of an equivariant estimator does not depend on `θ` at all, so "uniformly minimize the
  risk over the equivariant class" collapses to "minimize one number";
* `risk_const_on_orbit` — without transitivity one still gets constancy on each orbit.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.2 (The
Principle of Equivariance), Theorem 2.7 (the risk of an equivariant estimator is invariant
under the induced group) with Corollaries 2.8 and 2.13 (constant risk under transitivity; risk
constant on orbits). (`TPE2 §3.2 Thm 2.7, Cor 2.8, Cor 2.13`.)

**Proof formalization notes.**
* The one-line computation is a change of variables: `P (g • θ) = (P θ).map (g • ·)` by
  model invariance, then `lintegral_map` moves `g` onto the integrand, equivariance turns
  `δ (g • x)` into `g • δ x`, and loss invariance cancels the `g` entirely.
* Because that change of variables goes through `lintegral_map`, measurability of `δ` and
  of each loss slice `L θ` are genuine Lean-side requirements even though the classical
  statement leaves them implicit.
* Instance choice: we require only `MeasurableConstSMul G 𝓧` (each `x ↦ g • x` is
  measurable) rather than the stronger `MeasurableSMul G 𝓧`, which would additionally
  force a `MeasurableSpace G`. Nothing in this development ever integrates over the group.
* Transitivity of the induced action is Mathlib's `MulAction.IsPretransitive G Θ`, and
  orbits are `MulAction.orbit G θ`; no bespoke notion of orbit is introduced.

**Bibliographic comments.** The group-theoretic ("invariance") reduction of a decision
problem originates with G. A. Hunt and C. Stein, *Most stringent tests of statistical
hypotheses* (unpublished manuscript, 1946), whose argument first reached print through
M. A. Girshick and L. J. Savage, "Bayes and minimax estimates for quadratic loss
functions," *Proc. Second Berkeley Symp. Math. Statist. Probab.*, Univ. California Press,
1951, 53–73. Equivariant estimation of location and scale parameters is due to
E. J. G. Pitman, "The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section General

variable {G Θ 𝓧 D : Type*} [Group G] [MeasurableSpace 𝓧] [MeasurableSpace D]
  [MulAction G 𝓧] [MulAction G Θ] [MulAction G D] [MeasurableConstSMul G 𝓧]

/-- **Risk invariance under the induced parameter action.** In an estimation problem
invariant under a group `G` — the model intertwines the data and parameter actions and
the loss is unchanged by the simultaneous action — the risk function of any equivariant
estimator satisfies `R(g • θ, δ) = R(θ, δ)`.

This is the structural reason the equivariance principle reduces a risk *function* to a
risk *number*: see `risk_const_of_pretransitive`. -/
theorem risk_smul {P : Θ → Measure 𝓧} {L : Θ → D → ℝ≥0∞} {δ : 𝓧 → D}
    -- USER-INPUT: the data action pushes `P θ` forward to `P (g • θ)` (invariant model)
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the loss is unchanged by the simultaneous parameter/decision action
    (hL : IsInvariantLoss (G := G) L)
    -- LEAN-ONLY: measurability of each loss slice; the classical statement leaves it
    -- implicit, and it is only needed to run `lintegral_map` (no scope change)
    (hLmeas : ∀ θ, Measurable (L θ))
    -- LEAN-ONLY: measurability of the estimator; same role, no scope change
    (hδ : Measurable δ)
    -- USER-INPUT: the estimator intertwines the data and decision actions (equivariance)
    (hδeq : IsEquivariant (G := G) δ)
    (g : G) (θ : Θ) :
    risk P L δ (g • θ) = risk P L δ θ := by
  unfold risk crossRisk
  have hgm : Measurable (fun x => L (g • θ) (δ x)) := (hLmeas (g • θ)).comp hδ
  rw [← hP g θ, lintegral_map hgm (measurable_const_smul g)]
  refine lintegral_congr fun x => ?_
  rw [hδeq g x, hL g θ (δ x)]

/-- **Constant risk under a transitive induced action.** If the induced action on the
parameter space is transitive, the risk function of an equivariant estimator is a
constant: it takes the same value at any two parameter points. Minimizing the risk
*uniformly* over the equivariant class therefore becomes minimizing a single number,
which is what makes a minimum risk equivariant estimator a reasonable thing to ask for. -/
theorem risk_const_of_pretransitive [MulAction.IsPretransitive G Θ]
    {P : Θ → Measure 𝓧} {L : Θ → D → ℝ≥0∞} {δ : 𝓧 → D}
    -- USER-INPUT: invariant model
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: invariant loss
    (hL : IsInvariantLoss (G := G) L)
    -- LEAN-ONLY: measurability of each loss slice (change of variables only)
    (hLmeas : ∀ θ, Measurable (L θ))
    -- LEAN-ONLY: measurability of the estimator (change of variables only)
    (hδ : Measurable δ)
    -- USER-INPUT: equivariant estimator
    (hδeq : IsEquivariant (G := G) δ)
    (θ θ' : Θ) :
    risk P L δ θ = risk P L δ θ' := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G θ θ'
  exact (risk_smul hP hL hLmeas hδ hδeq g θ).symm

/-- **Constant risk on orbits.** Without transitivity the risk of an equivariant
estimator is still constant on each orbit of the induced action on the parameter
space. -/
theorem risk_const_on_orbit {P : Θ → Measure 𝓧} {L : Θ → D → ℝ≥0∞} {δ : 𝓧 → D}
    -- USER-INPUT: invariant model
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: invariant loss
    (hL : IsInvariantLoss (G := G) L)
    -- LEAN-ONLY: measurability of each loss slice (change of variables only)
    (hLmeas : ∀ θ, Measurable (L θ))
    -- LEAN-ONLY: measurability of the estimator (change of variables only)
    (hδ : Measurable δ)
    -- USER-INPUT: equivariant estimator
    (hδeq : IsEquivariant (G := G) δ)
    {θ θ' : Θ}
    -- USER-INPUT: the two parameter points lie on a common orbit
    (hθ : θ' ∈ MulAction.orbit G θ) :
    risk P L δ θ' = risk P L δ θ := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hθ
  exact risk_smul hP hL hLmeas hδ hδeq g θ

end General

end StatLean.PointEstimation
