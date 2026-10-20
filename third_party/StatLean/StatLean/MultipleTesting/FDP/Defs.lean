module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# False discovery proportion / rate and family-wise error rate — definitions

Concept-layer definitions for the error criteria of multiple hypothesis testing.

Consider finitely many hypotheses indexed by a set $\iota$, a subset $H_0 \subseteq \iota$ of
the *true* null hypotheses, and a random subset $R(\omega) \subseteq \iota$ of *rejected*
hypotheses. Writing $V(\omega) = |R(\omega) \cap H_0|$ for the number of false rejections and
$R(\omega) = |R(\omega)|$ for the total number of rejections, we define:

* the number of rejections $|R(\omega)|$;
* the number of false rejections (rejected true nulls) $V(\omega) = |R(\omega) \cap H_0|$;
* the **false discovery proportion** $\mathrm{FDP}(\omega) = V(\omega) / \max(R(\omega), 1)$,
  i.e. the textbook ratio $V / (R \vee 1)$, which equals the discovery proportion $V/R$ whenever
  there is at least one rejection and is defined to be $0$ when $R(\omega) = \emptyset$;
* the **false discovery rate** $\mathrm{FDR} = \mathbb{E}[\mathrm{FDP}]$, the expectation of the
  false discovery proportion under the measure $\mu$;
* the **family-wise error rate** $\mathrm{FWER} = \mathbb{P}(V \ge 1) =
  \mathbb{P}(R \cap H_0 \neq \emptyset)$, the probability of at least one false rejection.

These are theorem-agnostic; the Benjamini–Hochberg / Holm / knockoff theorems live in sibling
assembly files and consume these definitions. This is a concept-layer foundation.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 19 (Multiple Hypotheses), §19.2 (family-wise error rate:
$\mathrm{FWER}$) and Chapter 20 (False Discovery Rate), §20.2 (false discovery proportion and
false discovery rate: $\mathrm{FDP}$, $\mathrm{FDR}$).

**Proof formalization notes.** This file contains only definitions, no proofs. The denominator
$\max(R(\omega), 1)$ encodes the book's convention $V/(R \vee 1)$: when there are no rejections
($R(\omega) = \emptyset$) the numerator $V$ is $0$, so $\mathrm{FDP} = 0$, matching the standard
convention that the false discovery proportion is $0$ on the no-discovery event. `FWER` is valued
in $[0,\infty]$ (`ℝ≥0∞`) as a raw measure of the false-rejection event, with no probability-measure
assumption baked into the definition.

**Bibliographic comments.** The false discovery rate originates with Y. Benjamini and
Y. Hochberg, "Controlling the false discovery rate: a practical and powerful approach to multiple
testing," *Journal of the Royal Statistical Society, Series B (Methodological)*, 57(1):289–300,
1995. There the random proportion $Q$ (their Eq. (1), denoted $Q = V/(V+S) = V/R$, set to $0$ when
$R = 0$) is exactly the $\mathrm{FDP}$ above, and the false discovery rate is its expectation
$\mathrm{FDR} = \mathbb{E}[Q]$ (their Eq. (2)). The family-wise error rate is older statistical
folklore with no single seminal paper; the notion of controlling the probability of any false
rejection across a family of comparisons is generally traced to J. W. Tukey's unpublished 1953
manuscript "The Problem of Multiple Comparisons," and was standard in the simultaneous-inference
literature well before the FDR was introduced.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*}

/-- Number of rejected hypotheses, `|R ω|` (Lu-BDA Ch20 (False Discovery Rate), §20.2, the `R`
of the BH proof). -/
def numRejections (R : Ω → Finset ι) (ω : Ω) : ℕ := (R ω).card

/-- Number of falsely rejected hypotheses — rejected true nulls, `|R ω ∩ H₀|`
(Lu-BDA Ch20 (False Discovery Rate), §20.2, "# False Positive"). -/
def numFalseRejections [DecidableEq ι] (H₀ : Finset ι) (R : Ω → Finset ι) (ω : Ω) : ℕ :=
  ((R ω) ∩ H₀).card

/-- False discovery proportion `FDP = (# false positives) / (# rejections ∨ 1)`
(Lu-BDA Ch20 (False Discovery Rate), §20.2).
The `max … 1` in the denominator encodes the book's `∨ 1`: with no rejections (`R ω = ∅`) the
numerator is `0` and `FDP = 0`. -/
noncomputable def FDP [DecidableEq ι] (H₀ : Finset ι) (R : Ω → Finset ι) (ω : Ω) : ℝ :=
  (numFalseRejections H₀ R ω : ℝ) / max (numRejections R ω : ℝ) 1

/-- False discovery rate `FDR = E[FDP]` (Lu-BDA Ch20 (False Discovery Rate), §20.2). -/
noncomputable def FDR [DecidableEq ι] (H₀ : Finset ι) (R : Ω → Finset ι) (μ : Measure Ω) : ℝ :=
  ∫ ω, FDP H₀ R ω ∂μ

/-- Family-wise error rate `FWER = P(R ∩ H₀ ≠ ∅)`: the probability of at least one false
rejection (Lu-BDA Ch19 (Multiple Hypotheses), §19.2). Valued in `ℝ≥0∞`. -/
noncomputable def FWER [DecidableEq ι] (H₀ : Finset ι) (R : Ω → Finset ι) (μ : Measure Ω) : ℝ≥0∞ :=
  μ {ω | ((R ω) ∩ H₀).Nonempty}

end StatLean.MultipleTesting
