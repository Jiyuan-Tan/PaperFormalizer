module
public import StatLean.TimeSeries.Process.Defs
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Mixing coefficients (α, β, ρ, φ, ψ) — data model

The five classical measures of dependence between two sub-σ-algebras `m₁, m₂` of a
probability space, and their process-level specializations along the past/future
σ-algebras `σ{X_s : s ≤ 0}` and `σ{X_s : s ≥ n}` (FY §2.6.1, eq. (2.57), for strictly
stationary processes — the book's standing convention, which anchors the past at time
`0`). A process is α-, β-, ρ-, φ- or ψ-mixing when the corresponding coefficient sequence
tends to `0` (FY Definition 2.11). α-mixing = *strong mixing*; β-mixing = *absolute
regularity*.

All coefficients are real suprema (`sSup`) over description sets; on a probability space
each set is nonempty and bounded (`BddAbove` lemmas in `Mixing/Relations.lean`), and by
Lean's `Real.sSup` junk convention the definitions are total. The β-coefficient uses the
finite-partition formula `β = ½ sup Σᵢⱼ |P(Aᵢ ∩ Bⱼ) − P(Aᵢ)P(Bⱼ)|` (equivalent to the
book's conditional-probability form `E[sup_B |P(B) − P(B | 𝓕_{-∞}^0)|]`; the equivalence
on standard Borel spaces is recorded in `Mixing/Relations.lean` as a lemma against
`condDistrib`).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.1,
eq. (2.57) and Definition 2.11 (pp. 68–69). (`FY §2.6.1 eq. (2.57), Def 2.11`.)

**Proof formalization notes.**
* Division junk: in `phiMixCoeff`/`psiMixCoeff` the description sets restrict to events
  of positive probability, matching the book's side conditions; `rhoMixCoeff` divides by
  standard deviations and degenerate (zero-variance) variables contribute the junk value
  `0`, harmless under `sSup`.
* The process coefficients take the book's stationary-anchored form (past fixed at time
  `0`); for non-stationary processes a sup-over-anchor variant can be added when needed
  (FY restricts to strict stationarity "for notational simplicity").
* Coefficients are defined for arbitrary `m₁ m₂` (not required to be sub-σ-algebras of
  the ambient one); sub-σ-algebra hypotheses appear on lemmas that need them.

**Bibliographic comments.** α-mixing is due to M. Rosenblatt ("A central limit theorem
and a strong mixing condition", *Proc. Nat. Acad. Sci. USA* **42** (1956), 43–47);
β-mixing (absolute regularity) to V. A. Volkonskii and Yu. A. Rozanov (1959), building on
A. N. Kolmogorov; ρ-mixing to A. N. Kolmogorov and Yu. A. Rozanov (1960); φ-mixing to
I. A. Ibragimov (1962); ψ-mixing to J. R. Blum, D. L. Hanson and L. H. Koopmans (1963).
Standard references: R. C. Bradley, *Introduction to Strong Mixing Conditions*;
P. Doukhan, *Mixing: Properties and Examples*, Springer, 1994.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Coefficients between two σ-algebras (FY eq. (2.57)) -/

/-- **α (strong mixing) coefficient** between `m₁` and `m₂`:
`α = sup {|P(A ∩ B) − P(A)P(B)| : A ∈ m₁, B ∈ m₂}`. -/
noncomputable def alphaMixCoeff (μ : Measure Ω) (m₁ m₂ : MeasurableSpace Ω) : ℝ :=
  sSup {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
    r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|}

/-- **β (absolute regularity) coefficient** between `m₁` and `m₂`, via the
finite-partition formula:
`β = ½ sup Σᵢⱼ |P(Aᵢ ∩ Bⱼ) − P(Aᵢ)P(Bⱼ)|` over finite measurable partitions
`{Aᵢ} ⊆ m₁`, `{Bⱼ} ⊆ m₂` of `Ω`. -/
noncomputable def betaMixCoeff (μ : Measure Ω) (m₁ m₂ : MeasurableSpace Ω) : ℝ :=
  sSup {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
    (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
    (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
    (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
    (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
    r = (1 / 2) * ∑ i, ∑ j,
      |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|}

/-- **ρ (maximal correlation) coefficient** between `m₁` and `m₂`:
`ρ = sup |Corr(f, g)|` over `f ∈ L²(m₁)`, `g ∈ L²(m₂)`. Degenerate variables contribute
the junk value `0` (division convention). -/
noncomputable def rhoMixCoeff (μ : Measure Ω) (m₁ m₂ : MeasurableSpace Ω) : ℝ :=
  sSup {r : ℝ | ∃ f g : Ω → ℝ, Measurable[m₁] f ∧ Measurable[m₂] g ∧
    MemLp f 2 μ ∧ MemLp g 2 μ ∧
    r = |cov[f, g; μ]| / (Real.sqrt (variance f μ) * Real.sqrt (variance g μ))}

/-- **φ (uniform mixing) coefficient** between `m₁` and `m₂`:
`φ = sup {|P(B) − P(B | A)| : A ∈ m₁, P(A) > 0, B ∈ m₂}`. -/
noncomputable def phiMixCoeff (μ : Measure Ω) (m₁ m₂ : MeasurableSpace Ω) : ℝ :=
  sSup {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
    0 < (μ A).toReal ∧
    r = |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|}

/-- **ψ coefficient** between `m₁` and `m₂`:
`ψ = sup {|1 − P(B | A)/P(B)| : A ∈ m₁, B ∈ m₂, P(A)P(B) > 0}`. -/
noncomputable def psiMixCoeff (μ : Measure Ω) (m₁ m₂ : MeasurableSpace Ω) : ℝ :=
  sSup {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
    0 < (μ A).toReal ∧ 0 < (μ B).toReal ∧
    r = |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal|}

/-! ## Process-level coefficients (FY eq. (2.57), stationary anchoring) -/

/-- α-mixing coefficient of a process at lag `n`: `α(σ{X_s : s ≤ 0}, σ{X_s : s ≥ n})`. -/
noncomputable def alphaCoeff (X : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  alphaMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ))

/-- β-mixing coefficient of a process at lag `n`. -/
noncomputable def betaCoeff (X : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  betaMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ))

/-- ρ-mixing coefficient of a process at lag `n`. -/
noncomputable def rhoCoeff (X : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  rhoMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ))

/-- φ-mixing coefficient of a process at lag `n`. -/
noncomputable def phiCoeff (X : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  phiMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ))

/-- ψ-mixing coefficient of a process at lag `n`. -/
noncomputable def psiCoeff (X : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  psiMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ))

/-- **α-mixing** (strong mixing) process (FY Definition 2.11): `α(n) → 0`. -/
def IsAlphaMixing (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  Tendsto (fun n : ℕ => alphaCoeff X μ n) atTop (𝓝 0)

/-- **β-mixing** (absolutely regular) process (FY Definition 2.11): `β(n) → 0`. -/
def IsBetaMixing (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  Tendsto (fun n : ℕ => betaCoeff X μ n) atTop (𝓝 0)

/-- **ρ-mixing** process (FY Definition 2.11): `ρ(n) → 0`. -/
def IsRhoMixing (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  Tendsto (fun n : ℕ => rhoCoeff X μ n) atTop (𝓝 0)

/-- **φ-mixing** process (FY Definition 2.11): `φ(n) → 0`. -/
def IsPhiMixing (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  Tendsto (fun n : ℕ => phiCoeff X μ n) atTop (𝓝 0)

/-- **ψ-mixing** process (FY Definition 2.11): `ψ(n) → 0`. -/
def IsPsiMixing (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  Tendsto (fun n : ℕ => psiCoeff X μ n) atTop (𝓝 0)

end StatLean.TimeSeries
