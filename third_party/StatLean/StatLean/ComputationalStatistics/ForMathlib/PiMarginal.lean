module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Marginals of i.i.d. product measures along coordinate deletion

Deleting one coordinate from an i.i.d. product sample leaves an i.i.d. product
sample of the smaller size:

* `pi_map_precomp_succAbove` — the pushforward of `P^{n+1}` under
  `x ↦ x ∘ Fin.succAbove i` is `P^n`;
* `pi_map_deleteSplit` — `x ↦ (x i, x ∘ Fin.succAbove i)` carries `P^{n+1}` to
  `P ⊗ P^n` (the deleted coordinate is independent of the rest).

These are the measure-theoretic content of the jackknife ("the deleted sample
is again a random sample", ECS §3.3) and of cross-validation fold splitting
("the test fold is independent of the training folds", ECS §3.2).

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §3.2–§3.3 (implicit in the jackknife and data
partitioning setups).  (`ECS §3.2–3.3`.)

**Proof formalization notes.**

* Constant factors only (`fun _ => P`); the general non-identical version is
  not needed by any consumer and is deferred.
* Expected route: Mathlib's `MeasurableEquiv.piFinSuccAbove` and the
  measure-preservation of the corresponding equivalence on `Measure.pi`,
  then project.  Candidate pinned-Mathlib bricks:
  `MeasureTheory.measurePreserving_piFinSuccAbove`, `Measure.pi_map_eval`.

**Bibliographic comments.** Folklore; recorded because Quenouille (1949) and
Tukey (1958) use it silently in every jackknife computation.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Measure 𝓧} [IsProbabilityMeasure P]
  {n : ℕ}

/-- The delete-and-split map is measurable. -/
private theorem measurable_deleteSplit (i : Fin (n + 1)) :
    Measurable fun x : Fin (n + 1) → 𝓧 => (x i, x ∘ i.succAbove) :=
  (measurable_pi_apply i).prodMk (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

/-- Delete-and-split is `MeasurableEquiv.piFinSuccAbove` at a constant family, so
Mathlib's measure preservation applies verbatim. -/
private theorem map_deleteSplit_aux (i : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => P).map (fun x => (x i, x ∘ i.succAbove))
      = P.prod (Measure.pi fun _ : Fin n => P) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i).map_eq

/-- **Coordinate deletion preserves the i.i.d. product law**: deleting the
`i`-th coordinate of a `P^{n+1}` sample yields a `P^n` sample. -/
theorem pi_map_precomp_succAbove (i : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => P).map (fun x => x ∘ i.succAbove)
      = Measure.pi fun _ : Fin n => P := by
  have hcomp : (fun x : Fin (n + 1) → 𝓧 => x ∘ i.succAbove)
      = Prod.snd ∘ fun x : Fin (n + 1) → 𝓧 => (x i, x ∘ i.succAbove) := rfl
  rw [hcomp, ← Measure.map_map measurable_snd (measurable_deleteSplit i),
    map_deleteSplit_aux i, Measure.map_snd_prod, measure_univ, one_smul]

/-- **Delete-and-split**: the deleted coordinate and the remaining sample are
independent, `(x_i, x_{(−i)}) ~ P ⊗ P^n` under `x ~ P^{n+1}`. -/
theorem pi_map_deleteSplit (i : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => P).map (fun x => (x i, x ∘ i.succAbove))
      = P.prod (Measure.pi fun _ : Fin n => P) :=
  map_deleteSplit_aux i

end StatLean.ComputationalStatistics

