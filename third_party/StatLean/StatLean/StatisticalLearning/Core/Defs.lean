module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Statistical learning — the risk/ERM/PAC data model

The general learning setting of SSBD Ch. 2–4: an example domain `Z`, an
abstract hypothesis type `H`, a loss family `ℓ : H → Z → ℝ`, true risk
`L_D(h) = E_{z∼D} ℓ(h,z)` (SSBD Eq. (3.3)), empirical risk
`L_S(h) = n⁻¹ ∑ᵢ ℓ(h, zᵢ)` (SSBD Eq. (3.4)), the ERM/approximate-ERM
*predicates* (SSBD §2.3 — deliberately not an `argmin` construction),
`ε`-representative samples in sup-free `∀`-form (SSBD Definition 4.1), and the
sample-complexity-witnessed learnability predicates: uniform convergence (SSBD
Definition 4.3), agnostic PAC (SSBD Definition 3.4), and realizable PAC for
binary classification (SSBD Definitions 2.1 and 3.1).

**Reference.** Shalev-Shwartz & Ben-David, *Understanding Machine Learning*
(Cambridge, 2014), Ch. 2–4. Exact transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.**
* A sample is a *sequence* `Fin n → Z` (SSBD footnote 1, p. 14: order and
  repeats matter); its law is the `n`-fold product `Measure.pi` (`D^m`).
* Probability statements are phrased as
  `ENNReal.ofReal (1 − δ) ≤ sampleLaw D n {s | …}` on raw (outer-measure)
  events; measurability enters only in proofs, as LEAN-ONLY hypotheses
  (SSBD Remark 3.1 measurability caveat).
* Best-in-class risk is `sInf (risk D ℓ '' 𝓗)` (image form — avoids the
  real-`⨅` junk floor at `0`); junk value `0` when `𝓗 = ∅` or the image is
  unbounded below. Theorems carry nonemptiness/nonnegativity hypotheses.
* This file is a laptop-only Defs surface: definitions and instances only,
  0-sorry; all lemma content lives in the sibling files.

**Bibliographic comments.** The PAC model is due to L. G. Valiant, "A theory
of the learnable," *Comm. ACM* 27 (1984), 1134–1142; the agnostic extension to
D. Haussler, "Decision theoretic generalizations of the PAC model," *Inf.
Comput.* 100 (1992), 78–150. Uniform convergence as the route to learnability
goes back to Vapnik–Chervonenkis (1971).
-/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.StatisticalLearning

/-- A training sample of size `n` from example domain `Z` (SSBD §2.1): a
finite *sequence* of examples — the same example may appear twice and order is
visible (SSBD footnote 1, p. 14) — modeled as a function on `Fin n`. -/
abbrev Sample (Z : Type*) (n : ℕ) := Fin n → Z

variable {Z H : Type*}

/-- The law `D^n` of an i.i.d. sample of size `n` (SSBD §2.1, "the i.i.d.
assumption"): the `n`-fold product measure on `Fin n → Z`. -/
noncomputable def sampleLaw [MeasurableSpace Z] (D : Measure Z) (n : ℕ) :
    Measure (Sample Z n) :=
  Measure.pi fun _ => D

instance [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D] (n : ℕ) :
    IsProbabilityMeasure (sampleLaw D n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

/-- **True risk** (SSBD Eq. (3.3)): the expected loss `E_{z∼D} ℓ(h, z)` of
hypothesis `h` under distribution `D`. Edge behavior: Bochner junk value `0`
when `ℓ(h, ·)` is not integrable. -/
noncomputable def risk [MeasurableSpace Z] (D : Measure Z) (ℓ : H → Z → ℝ)
    (h : H) : ℝ :=
  ∫ z, ℓ h z ∂D

/-- **Empirical risk** (SSBD Eq. (3.4)): the average loss `n⁻¹ ∑ᵢ ℓ(h, zᵢ)` of
`h` on the sample `s`. Edge behavior: `n = 0` gives junk `0` (`(0:ℝ)⁻¹ = 0`). -/
noncomputable def empRisk {n : ℕ} (ℓ : H → Z → ℝ) (s : Sample Z n) (h : H) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ℓ h (s i)

/-- **Best-in-class risk** `inf_{g ∈ 𝓗} L_D(g)` (SSBD Definition 3.3 RHS), in
`sInf`-of-image form (junk `0` for `𝓗 = ∅` or an unbounded-below image). -/
noncomputable def bestRisk [MeasurableSpace Z] (D : Measure Z)
    (𝓗 : Set H) (ℓ : H → Z → ℝ) : ℝ :=
  sInf (risk D ℓ '' 𝓗)

/-- **Empirical risk minimizer, predicate form** (SSBD Eq. (2.4), §2.3): `h`
lies in the class and its empirical risk is minimal over the class. Existence,
selection, and measurability of a minimizer are deliberately *not* built in —
an ERM selector enters downstream theorems as data. -/
def IsERM {n : ℕ} (𝓗 : Set H) (ℓ : H → Z → ℝ) (s : Sample Z n) (h : H) :
    Prop :=
  h ∈ 𝓗 ∧ ∀ g ∈ 𝓗, empRisk ℓ s h ≤ empRisk ℓ s g

/-- **Approximate empirical risk minimizer**: in-class and within `η` of every
competitor's empirical risk. `IsApproxERM 𝓗 ℓ s 0 h ↔ IsERM 𝓗 ℓ s h`
definitionally up to `add_zero`. -/
def IsApproxERM {n : ℕ} (𝓗 : Set H) (ℓ : H → Z → ℝ) (s : Sample Z n) (η : ℝ)
    (h : H) : Prop :=
  h ∈ 𝓗 ∧ ∀ g ∈ 𝓗, empRisk ℓ s h ≤ empRisk ℓ s g + η

/-- **`ε`-representative sample** (SSBD Definition 4.1), sup-free `∀`-form:
every hypothesis in the class has empirical risk within `ε` of its true
risk. -/
def UniformDeviationLE [MeasurableSpace Z] (D : Measure Z) (𝓗 : Set H)
    (ℓ : H → Z → ℝ) {n : ℕ} (s : Sample Z n) (ε : ℝ) : Prop :=
  ∀ h ∈ 𝓗, |empRisk ℓ s h - risk D ℓ h| ≤ ε

/-- **Uniform convergence property with sample-complexity witness `mUC`**
(SSBD Definition 4.3): for every distribution and every `n ≥ mUC ε δ`, an
i.i.d. sample is `ε`-representative with probability at least `1 − δ`. The
event is a raw (outer-measure) set — measurability is a proof-side concern. -/
def HasUniformConvergenceWith [MeasurableSpace Z] (𝓗 : Set H)
    (ℓ : H → Z → ℝ) (mUC : ℝ → ℝ → ℕ) : Prop :=
  ∀ (D : Measure Z), IsProbabilityMeasure D →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
      ∀ n : ℕ, mUC ε δ ≤ n →
        ENNReal.ofReal (1 - δ) ≤
          sampleLaw D n {s | UniformDeviationLE D 𝓗 ℓ s ε}

/-- **Agnostic PAC learner with sample-complexity witness `mSC`** (SSBD
Definition 3.4, general loss): for every distribution over `Z` and every
`n ≥ mSC ε δ`, with probability at least `1 − δ` the returned hypothesis has
risk within `ε` of the best in the class. -/
def IsAgnosticPACLearnerWith [MeasurableSpace Z] (𝓗 : Set H)
    (ℓ : H → Z → ℝ) (A : ∀ n : ℕ, Sample Z n → H) (mSC : ℝ → ℝ → ℕ) : Prop :=
  ∀ (D : Measure Z), IsProbabilityMeasure D →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
      ∀ n : ℕ, mSC ε δ ≤ n →
        ENNReal.ofReal (1 - δ) ≤
          sampleLaw D n {s | risk D ℓ (A n s) ≤ bestRisk D 𝓗 ℓ + ε}

section BinaryClassification

variable {X : Type*}

/-- **0–1 loss** for binary classifiers (SSBD §3.2.1): `1` iff the prediction
differs from the label. -/
def zeroOneLoss (h : X → Bool) (p : X × Bool) : ℝ :=
  if h p.1 = p.2 then 0 else 1

/-- Label the instance sample `s` by the target `f` (SSBD §2.1's data-generation
model: instances from `D`, labels from `f`). -/
def labeledBy {n : ℕ} (f : X → Bool) (s : Sample X n) : Sample (X × Bool) n :=
  fun i => (s i, f (s i))

/-- **True error against `(D, f)`** (SSBD Eq. (2.1)): the `D`-mass of the
disagreement set `{x | h(x) ≠ f(x)}`, as a real number. -/
noncomputable def errProb [MeasurableSpace X] (D : Measure X) (f h : X → Bool) :
    ℝ :=
  D.real {x | h x ≠ f x}

/-- **Realizability** (SSBD Definition 2.1): some hypothesis in the class has
zero true error against `(D, f)` — stated as `D`-null disagreement set. -/
def Realizable [MeasurableSpace X] (D : Measure X) (f : X → Bool)
    (𝓗 : Set (X → Bool)) : Prop :=
  ∃ h ∈ 𝓗, D {x | h x ≠ f x} = 0

/-- **PAC learner (realizable binary classification) with sample-complexity
witness `mSC`** (SSBD Definition 3.1): for every marginal `D` and target `f`
realizable in `𝓗`, on `n ≥ mSC ε δ` labeled i.i.d. examples the learner's
output has true error at most `ε` with probability at least `1 − δ`. -/
def IsPACLearnerWith [MeasurableSpace X] (𝓗 : Set (X → Bool))
    (A : ∀ n : ℕ, Sample (X × Bool) n → (X → Bool)) (mSC : ℝ → ℝ → ℕ) :
    Prop :=
  ∀ (D : Measure X), IsProbabilityMeasure D → ∀ f : X → Bool,
    Realizable D f 𝓗 →
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ n : ℕ, mSC ε δ ≤ n →
          ENNReal.ofReal (1 - δ) ≤
            sampleLaw D n {s | errProb D f (A n (labeledBy f s)) ≤ ε}

end BinaryClassification

end StatLean.StatisticalLearning
