# Concrete-model EIF template

This guide describes the standard layout for a concrete efficient influence
function (EIF) example under `StatLean/AsymptoticStatistics/Examples/`. The library
supports both verification of a supplied candidate and derivation by
efficient-score or nuisance-space projection.

## Directory layout

Create two modules:

```text
StatLean/AsymptoticStatistics/Examples/<ModelName>/Model.lean
StatLean/AsymptoticStatistics/Examples/<ModelName>/EIF.lean
```

Put the observation type, measurable-space instance, model helpers, and
parameter functional in `Model.lean`. Put the candidate formula, regularity
lemmas, and headline EIF theorem in `EIF.lean`. Use the project namespace:

```lean
namespace AsymptoticStatistics.Examples.<ModelName>
-- model and EIF declarations

end AsymptoticStatistics.Examples.<ModelName>
```

## Choosing an EIF route

For verification, the main entry points in
`AsymptoticStatistics.Core.MassMethod` are:

- `eif_via_Gateaux`, from `PathwiseDifferentiableAt` and an
  `IsMixtureGateauxRepresenter` proof;
- `eif_via_TV_frechet`, for an `L²` representer and a TV-Fréchet mixture
  expansion over perturbations with bounded Radon--Nikodym density;
- `eif_via_TV_QMD`, which constructs the pathwise derivative from an
  `IsTVFrechetExpansion` over the full tangent space;
- `eif_via_Point_mass`, from one-dimensional derivatives along
  bounded-density paths.

When the inner-product identity is already available, use
`AsymptoticStatistics.Core.EIF.candidate_isEIF_of_full_tangent` or
`candidate_isEIF_of_membership`. Nuisance-score problems often benefit from
the projection API in `Core/EIF.lean` and
`StrictModel/EfficientScore.lean`.

## Implementation checklist

Define the model, functional, and raw candidate; prove measurability, `MemLp`
membership, centering, derivative representation, and tangent membership; then
state the headline `IsEfficientInfluenceFunction` theorem.

See `Examples/EmpiricalDistribution/Model.lean` for a compact full-tangent
example, `Examples/SymmetricLocation/EIF.lean` and
`Examples/Regression/EIF.lean` for efficient-score projection, and
`Examples/MARMean/EIF.lean` for an AIPW formula.

## Imports and verification

A typical EIF module starts with:

```lean
import StatLean.AsymptoticStatistics.Examples.<ModelName>.Model
import StatLean.AsymptoticStatistics.Core.MassMethod
```

Build it by its library name:

```bash
lake build StatLean.AsymptoticStatistics.Examples.<ModelName>.EIF
```

If the module belongs in the aggregate public import, add it to
`StatLean/AsymptoticStatistics.lean`. Check the headline with a small Lean file:

```lean
import StatLean.AsymptoticStatistics.Examples.<ModelName>.EIF

#print axioms AsymptoticStatistics.Examples.<ModelName>.<headline>
```

The result must not contain `sorryAx`; only the project's standard
foundational axioms are expected.
