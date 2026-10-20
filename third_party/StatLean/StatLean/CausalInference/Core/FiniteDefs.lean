module
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Notation.Indicator

@[expose] public section

/-!
# Potential outcomes on a finite population — science tables and assignment designs

The design-based (finite-population, randomization-based) half of causal inference. The
science of the `n` units is a *fixed* table of two potential-outcome vectors; the only
randomness is the treatment assignment, described by an **assignment design**.

* `ScienceTable n` — the pair of potential-outcome vectors `Y(1), Y(0) : Fin n → ℝ`.
* `ScienceTable.observed S z` — the observed outcome vector `Yᵢ = ZᵢYᵢ(1) + (1-Zᵢ)Yᵢ(0)`.
* `ScienceTable.unitEffect`, `ScienceTable.finiteATE` — `τᵢ = Yᵢ(1) - Yᵢ(0)` and `τ = n⁻¹∑τᵢ`.
* `ScienceTable.SharpNull` — Fisher's sharp null `Yᵢ(1) = Yᵢ(0)` for every unit.
* `Design n` — an assignment mechanism: a nonempty finite set of assignment vectors,
  drawn **uniformly**. `Design.expect`, `Design.prob`, `Design.var` are the induced
  expectation, probability and variance.
* `completeDesign n n₁` — complete randomization: all vectors with exactly `n₁` treated.
* `armMean`, `diffInMeans`, `armVar`, `neymanVarEst` — the treated/control sample means,
  the difference-in-means estimator `τ̂`, the arm sample variances and Neyman's variance
  estimator `V̂ = ŝ²(1)/n₁ + ŝ²(0)/n₀`.
* `popMean`, `popVar`, `popCov` — the finite-population mean, variance `S²` and covariance
  (both normalized by `n - 1`, as in the book).
* `fisherPValue` — the randomization p-value of a statistic under a design.

**Scope.** Designs here are *uniform* on their support. Every design in the covered
chapters (complete randomization, stratified randomization, matched pairs) is of this
form, and uniformity is what makes the randomization test exact. Bernoulli designs with
`p ≠ 1/2` are out of scope.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §2.2–2.3 (potential outcomes, the observed
outcome equation (2.2), the average causal effect), Definition 3.1 (complete
randomization), §3.2 (the sharp null and the randomization p-value (3.2)), §4.1–4.2
(the difference in means, the finite-population variances `S²`, and Neyman's variance
estimator). (`Ding §2.2; §3.1–3.2; §4.1–4.2`.) The assignment-mechanism viewpoint —
a probability distribution over assignment vectors — is that of G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*,
Cambridge University Press, 2015, Part II. (`IR Part II`.)

**Proof formalization notes.**

* A `Design` carries its support and a proof that the support is nonempty (constitutive:
  an assignment mechanism with no possible assignment is not a mechanism). Expectations
  are normalized `Finset` sums in `ℝ`; no measure theory is needed at this layer, and
  `Design.prob` uses `Set.indicator` so that no decidability instance is required.
* `popVar` and `popCov` divide by `n - 1`; for `n = 1` the divisor is `0` and Lean's
  junk value `0` results. The theorems that use them assume `2 ≤ n`.
* `armMean`/`armVar` divide by the realized arm size; on assignments where an arm is
  empty (or a singleton, for `armVar`) the junk value is `0`. The Neyman theorems
  restrict to `completeDesign` supports with `1 ≤ n₁ ≤ n - 1` (resp. `2 ≤ n₁ ≤ n - 2`),
  where the arms have the stated sizes.
* `completeDesign` needs `n₁ ≤ n` to have nonempty support; the witness is packaged as
  `completeSupport_nonempty`.

**Bibliographic comments.** The potential-outcome notation for randomized experiments is
J. Neyman's (1923, translated in *Statist. Sci.* **5** (1990), 465–472); its extension to
observational studies is D. B. Rubin, "Estimating causal effects of treatments in
randomized and nonrandomized studies," *J. Educ. Psychol.* **66** (1974), 688–701. The
randomization test is R. A. Fisher, *The Design of Experiments*, Oliver & Boyd, 1935.
-/

namespace StatLean.CausalInference

variable {n : ℕ}

/-! ### The science table -/

/-- A **treatment assignment vector** for `n` units: `z i = true` means unit `i` is
treated. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- The real-valued indicator of a `Bool`: `Zᵢ` as a number. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

/-- The **science table** of a finite population of `n` units: the two potential-outcome
vectors (Ding §2.2). Under SUTVA (Ding Assumptions 2.1–2.3) these are fixed numbers, so
the table is the complete "science" of the population; the assignment is the only source
of randomness. -/
structure ScienceTable (n : ℕ) where
  /-- Constitutive (Ding §2.2): the potential outcome of each unit under treatment. -/
  y1 : Fin n → ℝ
  /-- Constitutive (Ding §2.2): the potential outcome of each unit under control. -/
  y0 : Fin n → ℝ

namespace ScienceTable

/-- The **observed outcome vector** `Yᵢ = ZᵢYᵢ(1) + (1 - Zᵢ)Yᵢ(0)` (Ding eq. (2.2)). -/
def observed (S : ScienceTable n) (z : Assignment n) : Fin n → ℝ :=
  fun i => if z i then S.y1 i else S.y0 i

/-- The **individual causal effect** `τᵢ = Yᵢ(1) - Yᵢ(0)` (Ding §2.2). -/
def unitEffect (S : ScienceTable n) : Fin n → ℝ := fun i => S.y1 i - S.y0 i

/-- **Fisher's sharp null hypothesis** `H₀ : Yᵢ(1) = Yᵢ(0)` for every unit (Ding §3.2):
the treatment has no effect on any unit, so all missing potential outcomes are imputable
from the observed ones. -/
def SharpNull (S : ScienceTable n) : Prop := ∀ i, S.y1 i = S.y0 i

/-- The **constant (additive) treatment effect** model `τᵢ ≡ τ` (Ding §4.2): the case in
which Neyman's variance estimator is exactly unbiased. -/
def ConstantEffect (S : ScienceTable n) (τ : ℝ) : Prop := ∀ i, S.unitEffect i = τ

end ScienceTable

/-! ### Finite-population moments -/

/-- The **finite-population mean** `n⁻¹∑ᵢ vᵢ`. -/
noncomputable def popMean (v : Fin n → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i, v i

/-- The **finite-population variance** `S²(v) = (n-1)⁻¹∑ᵢ(vᵢ - v̄)²` (Ding §4.1; the
divisor is `n - 1`, as in the book). Junk value `0` when `n = 1`. -/
noncomputable def popVar (v : Fin n → ℝ) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ i, (v i - popMean v) ^ 2

/-- The **finite-population covariance** `S(u,v) = (n-1)⁻¹∑ᵢ(uᵢ - ū)(vᵢ - v̄)`
(Ding §4.1). Junk value `0` when `n = 1`. -/
noncomputable def popCov (u v : Fin n → ℝ) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ i, (u i - popMean u) * (v i - popMean v)

/-- The **finite-population average causal effect** `τ = n⁻¹∑ᵢ(Yᵢ(1) - Yᵢ(0))`
(Ding §2.2). -/
noncomputable def ScienceTable.finiteATE (S : ScienceTable n) : ℝ := popMean S.unitEffect

/-! ### Assignment designs -/

/-- An **assignment mechanism** (design): a nonempty finite set of assignment vectors,
from which the realized assignment is drawn uniformly at random.

Constitutive (Ding ch. 3; `IR` Part II): the support is the set of assignments the design
can produce, and it must be nonempty. Uniformity on the support is part of the definition
at this layer — see the scope note in the module docstring. -/
structure Design (n : ℕ) where
  /-- Constitutive: the set of assignment vectors the mechanism can produce. -/
  support : Finset (Assignment n)
  /-- Constitutive: some assignment is possible. -/
  support_nonempty : support.Nonempty

namespace Design

/-- The **expectation** of a function of the assignment under the design: the average of
`f` over the support. -/
noncomputable def expect (D : Design n) (f : Assignment n → ℝ) : ℝ :=
  (D.support.card : ℝ)⁻¹ * ∑ z ∈ D.support, f z

/-- The **probability** of a set of assignments under the design. -/
noncomputable def prob (D : Design n) (s : Set (Assignment n)) : ℝ :=
  D.expect (Set.indicator s fun _ => (1 : ℝ))

/-- The **variance** of a function of the assignment under the design. -/
noncomputable def var (D : Design n) (f : Assignment n → ℝ) : ℝ :=
  D.expect fun z => (f z - D.expect f) ^ 2

end Design

/-! ### Arms of an assignment -/

/-- The set of units in arm `a` under assignment `z` (`a = true`: treated). -/
def armIdx (z : Assignment n) (a : Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => z i = a

/-- The **number of treated units** under `z`. -/
def numTreated (z : Assignment n) : ℕ := (armIdx z true).card

/-! ### Complete randomization -/

/-- The support of complete randomization with `n₁` treated units: all assignment vectors
with exactly `n₁` ones (Ding Definition 3.1). -/
def completeSupport (n n₁ : ℕ) : Finset (Assignment n) :=
  Finset.univ.filter fun z => numTreated z = n₁

/-- Complete randomization has a possible assignment as soon as `n₁ ≤ n`. -/
theorem completeSupport_nonempty {n n₁ : ℕ}
    -- USER-INPUT: at most `n` units can be treated; Ding Definition 3.1
    (h : n₁ ≤ n) : (completeSupport n n₁).Nonempty := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := n₁) (by simpa using h)
  refine ⟨fun i => decide (i ∈ t), ?_⟩
  have harm : armIdx (fun i => decide (i ∈ t)) true = t := by
    ext i; simp [armIdx]
  rw [completeSupport, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [numTreated, harm, ht]⟩

/-- The **completely randomized experiment** (CRE) with `n₁` treated of `n` units: the
uniform distribution on the `C(n, n₁)` assignment vectors with `n₁` ones
(Ding Definition 3.1). -/
noncomputable def completeDesign (n n₁ : ℕ) (h : n₁ ≤ n) : Design n :=
  ⟨completeSupport n n₁, completeSupport_nonempty h⟩

/-! ### Estimators -/

/-- The **arm sample mean** of the observed outcomes in arm `a`. Junk value `0` when the
arm is empty. -/
noncomputable def armMean (S : ScienceTable n) (z : Assignment n) (a : Bool) : ℝ :=
  ((armIdx z a).card : ℝ)⁻¹ * ∑ i ∈ armIdx z a, S.observed z i

/-- The **difference-in-means estimator** `τ̂ = Ȳ₁ - Ȳ₀` (Ding §4.2). -/
noncomputable def diffInMeans (S : ScienceTable n) (z : Assignment n) : ℝ :=
  armMean S z true - armMean S z false

/-- The **arm sample variance** `ŝ²(a)`, with divisor `card - 1`. Junk value `0` when the
arm has at most one unit. -/
noncomputable def armVar (S : ScienceTable n) (z : Assignment n) (a : Bool) : ℝ :=
  (((armIdx z a).card : ℝ) - 1)⁻¹ * ∑ i ∈ armIdx z a, (S.observed z i - armMean S z a) ^ 2

/-- **Neyman's variance estimator** `V̂ = ŝ²(1)/n₁ + ŝ²(0)/n₀` (Ding §4.2). -/
noncomputable def neymanVarEst (S : ScienceTable n) (z : Assignment n) : ℝ :=
  armVar S z true / ((armIdx z true).card : ℝ) + armVar S z false / ((armIdx z false).card : ℝ)

/-! ### Randomization inference -/

/-- The **randomization p-value** of the statistic value function `g` at the realized
assignment `z` (Ding eq. (3.2)): the design probability that a re-randomized assignment
gives a statistic value at least as large as the realized one.

Here `g z' = T(z', Y^obs)` is the statistic recomputed at the hypothetical assignment `z'`
with the observed outcome vector held fixed — under the sharp null the outcome vector does
not depend on the assignment, which is exactly what makes `g` well defined. -/
noncomputable def fisherPValue (D : Design n) (g : Assignment n → ℝ) (z : Assignment n) : ℝ :=
  D.prob {z' | g z ≤ g z'}

end StatLean.CausalInference
