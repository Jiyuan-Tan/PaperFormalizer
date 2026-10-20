module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Super-uniform p-values — definition

Concept-layer definition for multiple testing. A p-value $p : \Omega \to \mathbb{R}$ for a
*true* null hypothesis is **super-uniform** under the null distribution if its cumulative
distribution function is dominated by the identity, i.e.
$$ \mathbb{P}(p \le t) \le t \quad \text{for every } t \ge 0. $$
Equivalently, $p$ is stochastically larger than a $\mathrm{Uniform}[0,1]$ variable on the null;
this is exactly the *validity* condition required of a p-value. For an exactly-uniform null
p-value the bound holds with equality, $\mathbb{P}(p \le t) = t$.

This is the only distributional assumption the Benjamini–Hochberg / Holm FWER arguments place
on the null p-values; it is theorem-agnostic and consumed by the assembly files.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 19 (Multiple Hypotheses), §19.2 (Multiple Hypotheses). The
super-uniform / validity condition $\mathbb{P}(p \le t) \le t$ is the standing null assumption
under which the FDR/FWER guarantees are stated. The book's Benjamini–Hochberg proof is written
for the exact-uniform identity $\mathbb{P}(p \le t) = t$; the definition here is the honest
provable relaxation (the inequality form) used downstream — see `BenjaminiHochberg.lean`.

**Proof formalization notes.** Nothing to prove here — this file only fixes the definition
`SuperUniform p μ := ∀ t ≥ 0, μ {ω | p ω ≤ t} ≤ ENNReal.ofReal t`. The right-hand side uses
`ENNReal.ofReal t` so the comparison lives in `ℝ≥0∞` alongside the measure value; for `t < 0`
the hypothesis `0 ≤ t` makes the quantifier vacuous on the relevant range, and `ENNReal.ofReal`
clamps any spurious negative `t` to `0`. The relaxation from the book's equality to an
inequality is deliberate: it is what the BH / Holm assembly files can discharge for genuine
(not necessarily exactly-uniform) null statistics, and it is sufficient for every downstream
FDR/FWER bound.

**Bibliographic comments.** The super-uniform (a.k.a. *valid* or *conservative*) p-value
condition $\mathbb{P}(p \le t) \le t$ is folklore with no single seminal origin: it is
the standard formalization of what it means for a p-value to be valid under the null, appearing
implicitly throughout the classical hypothesis-testing literature (e.g. Lehmann & Romano,
*Testing Statistical Hypotheses*) and used explicitly as the null hypothesis in the
multiple-testing control results of Benjamini & Hochberg, "Controlling the false discovery
rate: a practical and powerful approach to multiple testing", *J. R. Stat. Soc. Ser. B* **57**
(1995), 289–300, and Holm, "A simple sequentially rejective multiple test procedure", *Scand.
J. Stat.* **6** (1979), 65–70. We therefore cite it as folklore rather than attribute it to a
single paper.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `SuperUniform p μ`: the p-value `p` is *super-uniform* under `μ`, i.e. `μ {p ≤ t} ≤ t` for
every `t ≥ 0` (Lu-BDA Ch19 (Multiple Hypotheses) §19.2). The defining null assumption; for an exactly-uniform `p` it holds
with equality. -/
def SuperUniform (p : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t → μ {ω | p ω ≤ t} ≤ ENNReal.ofReal t

end StatLean.MultipleTesting
