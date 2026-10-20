module
public import StatLean.CausalInference.Core.PopulationDefs

@[expose] public section

/-!
# Instrumental variables — potential treatments, compliance types, and the IV assumptions

Data model for noncompliance: a binary instrument `Z` (the *assigned* treatment), the pair
of potential treatments `D(1), D(0)` (what the unit would actually take under each
assignment), and the potential outcomes `Y(1), Y(0)` indexed by the assignment. Each unit
falls into one of four **compliance types** determined by `(D(1), D(0))`:

| `D(1)` | `D(0)` | type |
|---|---|---|
| 1 | 1 | always taker |
| 1 | 0 | complier |
| 0 | 1 | defier |
| 0 | 0 | never taker |

The three IV assumptions — random assignment, monotonicity (no defiers) and the exclusion
restriction — are separate predicates, as they are separately falsifiable and separately
used.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §21.2.1 (p. 282: the four compliance types);
Assumption 21.1 (p. 282: `Z ⫫ {D(1), D(0), Y(1), Y(0)}`); Assumption 21.2 (p. 283:
monotonicity `Dᵢ(1) ≥ Dᵢ(0)`, i.e. no defiers); Assumption 21.3 (p. 283: the exclusion
restriction `Yᵢ(1) = Yᵢ(0)` for always takers and never takers); Definition 21.1 (p. 284:
the complier average causal effect). (`Ding §21.2; Assumptions 21.1–21.3;
Definition 21.1`.) The noncompliance framework is developed at length in G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*,
Cambridge University Press, 2015, chs. 23–25. (`IR chs. 23–25`.)

**Proof formalization notes.**

* Potential outcomes are indexed by the **instrument**, `Y(z)`, not by the pair `(z, d)`.
  This is Ding's ch. 21 convention, and it is what makes the exclusion restriction
  statable as `Y(1) = Y(0)` on the non-compliers rather than as a functional-form
  restriction. The `Y(z, d)` formulation is not needed for any result in this release.
* The exclusion restriction is stated **pointwise** (`∀ ω, D(1) ω = D(0) ω → Y(1) ω =
  Y(0) ω`), which is the book's individual-level assumption; the weaker in-mean version
  would not support the mixture decompositions.
* `complianceType` is total: every unit has a type, so the four types partition the sample
  space by construction — the content of `complianceType_partition` is that these four
  events are disjoint and exhaust, which is then available for the mixture arguments.

**Bibliographic comments.** The compliance-type taxonomy and the LATE theorem are due to
G. W. Imbens and J. D. Angrist, "Identification and estimation of local average treatment
effects," *Econometrica* **62** (1994), 467–475, and J. D. Angrist, G. W. Imbens and
D. B. Rubin, "Identification of causal effects using instrumental variables," *J. Amer.
Statist. Assoc.* **91** (1996), 444–455.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **compliance type** of a unit, determined by its pair of potential treatments
(Ding §21.2.1). -/
inductive ComplianceType
  /-- Takes the treatment however assigned: `D(1) = D(0) = 1`. -/
  | alwaysTaker
  /-- Takes the treatment exactly when assigned to it: `D(1) = 1, D(0) = 0`. -/
  | complier
  /-- Does the opposite of the assignment: `D(1) = 0, D(0) = 1`. -/
  | defier
  /-- Never takes the treatment: `D(1) = D(0) = 0`. -/
  | neverTaker
  deriving DecidableEq, Repr

-- Port note (Lean v4.33 / Mathlib db584cd): Mathlib's enum-specialised `deriving Fintype` handler
-- fails here; the generic `derive_fintype%` elaborator (what `deriving Fintype` uses for non-enum
-- inductives) produces the same `Fintype` instance.
instance : Fintype ComplianceType := derive_fintype% _

namespace ComplianceType

/-- The compliance type of a unit from its potential treatments (Ding §21.2.1). -/
def of (d1 d0 : Ω → Bool) (ω : Ω) : ComplianceType :=
  match d1 ω, d0 ω with
  | true, true => .alwaysTaker
  | true, false => .complier
  | false, true => .defier
  | false, false => .neverTaker

end ComplianceType

/-- The event that a unit has a given compliance type. -/
def typeSet (d1 d0 : Ω → Bool) (t : ComplianceType) : Set Ω := {ω | ComplianceType.of d1 d0 ω = t}

/-- The **observed treatment received** `D = D(Z)` (Ding §21.2). -/
def obsTreat (Z d1 d0 : Ω → Bool) : Ω → Bool := fun ω => if Z ω then d1 ω else d0 ω

/-- **Random assignment of the instrument** (Ding Assumption 21.1): the instrument is
independent of all potential treatments and potential outcomes. -/
def IVRandomized (μ : Measure Ω) (Z d1 d0 : Ω → Bool) (y1 y0 : Ω → ℝ) : Prop :=
  IndepFun (fun ω => ((d1 ω, d0 ω), (y1 ω, y0 ω))) Z μ

/-- **Monotonicity / no defiers** (Ding Assumption 21.2): `Dᵢ(1) ≥ Dᵢ(0)` for every
unit. -/
def NoDefiers (d1 d0 : Ω → Bool) : Prop := ∀ ω, d0 ω = true → d1 ω = true

/-- **The exclusion restriction** (Ding Assumption 21.3): the instrument affects the
outcome only through the treatment received, so units whose treatment is unaffected by the
assignment have equal potential outcomes. -/
def ExclusionRestriction (d1 d0 : Ω → Bool) (y1 y0 : Ω → ℝ) : Prop :=
  ∀ ω, d1 ω = d0 ω → y1 ω = y0 ω

/-- **One-sided noncompliance** (Ding §21.2; `IR` ch. 23): nobody in the control arm can
access the treatment, `D(0) = 0` for every unit. -/
def OneSidedNoncompliance (d0 : Ω → Bool) : Prop := ∀ ω, d0 ω = false

/-- The **complier average causal effect** (CACE / LATE, Ding Definition 21.1):
`E[Y(1) - Y(0) | D(1) > D(0)]`. -/
noncomputable def cace (μ : Measure Ω) (d1 d0 : Ω → Bool) (y1 y0 : Ω → ℝ) : ℝ :=
  ∫ ω, (y1 ω - y0 ω) ∂(μ[|typeSet d1 d0 ComplianceType.complier])

/-- The **intention-to-treat contrast** of any observed variable across instrument arms:
`E[· | Z = 1] - E[· | Z = 0]`. With the observed outcome this is the reduced form; with
the observed treatment it is the first stage (Ding §21.2). -/
noncomputable def ittContrast (μ : Measure Ω) (Z : Ω → Bool) (W : Ω → ℝ) : ℝ :=
  primaFacie μ Z W

end StatLean.CausalInference
