module
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Exponential families — core data model

An **exponential family** in canonical form on a sample space `𝓧` with natural statistic
`T : 𝓧 → V` (`V` a real inner-product space) and reference measure `ν` is the family of
probability measures with density
$$ \frac{dP_\eta}{d\nu}(x) \;=\; \exp\bigl(\langle \eta, T(x)\rangle - A(\eta)\bigr), $$
where `A(η) = log ∫ exp⟨η, T x⟩ dν(x)` is the **log-partition function** and `η` ranges
over the **natural parameter set** `{η | ∫ exp⟨η, T⟩ dν < ∞}`. The classical
`exp(∑ ηᵢ Tᵢ(x) − A(η)) h(x) dμ` presentation is recovered by absorbing the carrier `h`
into the reference measure, `ν = h·μ`.

This file fixes the data model:

* `ExpFamily 𝓧 V` — the pair (reference measure `base`, natural statistic `stat`);
* `natSet` — the natural parameter set (a convex set, proved in `Basic`);
* `logPartition` — `A(η)`;
* `ExpFamily.P η` — the member measure, realized as `base.tilted ⟨η, stat ·⟩` (which is
  the zero measure off `natSet`: clean junk behavior);
* `ExpFamily.ofDensity` — the constructor absorbing a carrier `h` into the base;
* `IsCanonicalRepr` — a family `P' : Θ' → Measure 𝓧` is (a reparametrization of) the
  canonical family through `ηmap : Θ' → V`;
* `StatAffineIndep` — no nontrivial affine relation `⟨a, T⟩ = c` holds a.e.;
* `FullRank` — parameter set with nonempty interior + affinely independent statistic.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), equations (5.1)–(5.2) (general and canonical form, natural parameter
space) and Definition 5.2 (identifiability). (`TPE2 §1.5 (5.1)–(5.2), Def 5.2`.)

**Proof formalization notes.**
* Members are built with `Measure.tilted`, inheriting Mathlib's API
  (`isProbabilityMeasure_tilted`, `integral_tilted`, `tilted_tilted`, …) and its junk
  convention: `E.P η = 0` when `η ∉ E.natSet`.
* The statistic is `Measurable` into `[MeasurableSpace V]`; files composing with the
  inner product add `[OpensMeasurableSpace V]`/`[BorelSpace V]` as needed.
* `FullRank` deliberately separates two roles: completeness of `T` needs only the
  nonempty-interior condition, while minimality of `T` needs affine independence; the
  conjunction is packaged for the full-rank theorems that use both.

**Bibliographic comments.** Exponential families emerged from the work of R. A. Fisher
("Two new properties of mathematical likelihood," *Proc. R. Soc. Lond. A* **144**
(1934), 285–307), G. Darmois ("Sur les lois de probabilité à estimation exhaustive,"
*C. R. Acad. Sci. Paris* **200** (1935), 1265–1266), B. O. Koopman ("On distributions
admitting a sufficient statistic," *Trans. Amer. Math. Soc.* **39** (1936), 399–409) and
E. J. G. Pitman ("Sufficient statistics and intrinsic accuracy," *Proc. Camb. Phil.
Soc.* **32** (1936), 567–579). The systematic convex-analytic treatment (natural
parameter set, analyticity of the log-partition function) is due to O. Barndorff-Nielsen
(*Information and Exponential Families in Statistical Theory*, Wiley, 1978) and
L. D. Brown (*Fundamentals of Statistical Exponential Families*, IMS Lecture Notes 9,
1986).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

/-- An **exponential family** on `𝓧` with natural statistic in the real inner-product
space `V`: the data of a reference measure (with any carrier `h` already absorbed,
`base = h·μ`) and a measurable natural statistic. -/
structure ExpFamily (𝓧 : Type*) [MeasurableSpace 𝓧]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] where
  /-- Constitutive: the reference measure `ν` (carrier absorbed: `ν = h·μ`). -/
  base : Measure 𝓧
  /-- Constitutive: the natural (sufficient) statistic `T`. -/
  stat : 𝓧 → V
  /-- Constitutive: measurability of the natural statistic. -/
  stat_meas : Measurable stat

namespace ExpFamily

variable (E : ExpFamily 𝓧 V)

/-- The **natural parameter set** `{η | ∫ e^{⟨η,T⟩} dν < ∞}` — the largest set on which
the family is defined. Convexity is proved in `ExponentialFamily.Basic`. -/
def natSet : Set V :=
  {η : V | Integrable (fun x => Real.exp ⟪η, E.stat x⟫_ℝ) E.base}

/-- The **log-partition function** (cumulant function) `A(η) = log ∫ e^{⟨η,T⟩} dν`. -/
noncomputable def logPartition (η : V) : ℝ :=
  Real.log (∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)

/-- The member measure `P_η = e^{⟨η,T⟩ - A(η)}·ν`, realized as an exponential tilt of
the base measure. For `η ∉ natSet` this is the zero measure (junk convention inherited
from `Measure.tilted`). -/
noncomputable def P (η : V) : Measure 𝓧 :=
  E.base.tilted fun x => ⟪η, E.stat x⟫_ℝ

end ExpFamily

/-- Constructor for the classical presentation `exp(⟨η, T x⟩ - A(η))·h(x) dμ`: absorb
the carrier `h` into the reference measure. -/
noncomputable def ExpFamily.ofDensity (μ : Measure 𝓧) (h : 𝓧 → ℝ≥0∞) (T : 𝓧 → V)
    (hT : Measurable T) : ExpFamily 𝓧 V :=
  { base := μ.withDensity h
    stat := T
    stat_meas := hT }

/-- A family `P' : Θ' → Measure 𝓧` **is a canonical representation** through
`ηmap : Θ' → V` of the exponential family `E` if each member is the corresponding
canonical member. This is how the general-parametrization form
`exp(∑ ηᵢ(θ) Tᵢ(x) − B(θ)) h(x) dμ` enters: `B(θ) = A(ηmap θ)` becomes a lemma. -/
def IsCanonicalRepr {Θ' : Type*} (P' : Θ' → Measure 𝓧) (E : ExpFamily 𝓧 V)
    (ηmap : Θ' → V) : Prop :=
  ∀ θ, P' θ = E.P (ηmap θ)

/-- **Affine independence of the statistic**: no nontrivial affine relation
`⟨a, T x⟩ = c` holds `base`-a.e. (Together with a parameter set of nonempty interior
this is the classical *full rank* condition.) -/
def ExpFamily.StatAffineIndep (E : ExpFamily 𝓧 V) : Prop :=
  ∀ (a : V) (c : ℝ), (∀ᵐ x ∂E.base, ⟪a, E.stat x⟫_ℝ = c) → a = 0

/-- **Full rank** relative to a parameter set `Ξ'`: the set lies in the natural
parameter set, has nonempty interior, and the statistic is affinely independent. -/
def ExpFamily.FullRank (E : ExpFamily 𝓧 V) (Ξ' : Set V) : Prop :=
  Ξ' ⊆ E.natSet ∧ (interior Ξ').Nonempty ∧ E.StatAffineIndep

end StatLean.PointEstimation
