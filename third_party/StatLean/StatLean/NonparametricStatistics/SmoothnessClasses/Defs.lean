module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Smoothness classes for nonparametric estimation — definitions

The function classes over which nonparametric risk bounds are proved uniformly:

* `holderIndex β` — the integer $\ell(\beta)$, the greatest integer *strictly* smaller than
  $\beta$ (so $\ell = \beta - 1$ for integer $\beta$, and $\ell = \lfloor\beta\rfloor$ otherwise).
* `MemHolderOn β L f T` — the **Hölder class** $\Sigma(\beta, L)$ on an interval $T$:
  $f$ is $\ell$-times continuously differentiable on $T$ and its $\ell$-th derivative satisfies
  $|f^{(\ell)}(x) - f^{(\ell)}(y)| \le L\,|x-y|^{\beta-\ell}$ for all $x, y \in T$.
* `IsHolderDensity β L p` — the density class $\mathcal P(\beta, L)$: probability densities on
  $\mathbb R$ belonging to $\Sigma(\beta, L)$ globally.
* `MemNikolski β L f` — the **Nikol'skii class** $H(\beta, L)$: the $L^2$ analogue of the Hölder
  class, $\bigl(\int (f^{(\ell)}(x+t) - f^{(\ell)}(x))^2\,dx\bigr)^{1/2} \le L\,|t|^{\beta-\ell}$.
* `IsNikolskiDensity β L p` — densities in $H(\beta, L)$.
* `densityMeasure p` — the Borel measure `volume.withDensity (ofReal ∘ p)` on $\mathbb R$,
  the law of an observation with Lebesgue density `p`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.1, Definition 1.2 (the Hölder class
$\Sigma(\beta, L)$ and the density class $\mathcal{P}(\beta, L)$) and §1.2.3, Definition 1.4 (the
Nikol'skii class $\mathcal{H}(\beta, L)$ and $\mathcal{P}_H(\beta, L)$).

**Proof formalization notes.**

* *Differentiability field.* The classical definition asks for "$\ell$ times differentiable".
  For the Hölder class this file requires `ContDiffOn ℝ ℓ f T` (continuity of the $\ell$-th
  derivative included); the two definitions carve out the *same* class because the Hölder
  condition forces continuity of $f^{(\ell)}$, and derivatives of lower order are continuous
  wherever the next derivative exists. For the Nikol'skii class, `ContDiff ℝ ℓ f` is a genuine
  (mild) strengthening of the a.e.-flavoured classical class; the deviation is deliberate — it
  is what makes the order-$\ell$ Taylor identity with integral remainder available pointwise —
  and is recorded in the batch status ledger.
* *Lower Lebesgue integral in `MemNikolski`.* The translate condition is stated with `∫⁻` and
  `ENNReal.ofReal`: with the Bochner integral, a non-square-integrable difference would return
  the junk value `0` and satisfy the bound vacuously, silently emptying the hypothesis.
* *`holderIndex` on degenerate input.* For $\beta \le 0$ (never used), `⌈β⌉₊ = 0` and
  ℕ-subtraction yields `holderIndex β = 0`.

**Bibliographic comments.** Hölder conditions go back to O. Hölder, *Beiträge zur
Potentialtheorie* (Dissertation, Tübingen, 1882); their role as the standard smoothness scale
for pointwise nonparametric risk is classical, entering density estimation with M. Rosenblatt,
"Remarks on some nonparametric estimates of a density function," *Ann. Math. Statist.* **27**
(1956), 832–837, and E. Parzen, "On estimation of a probability density function and mode,"
*Ann. Math. Statist.* **33** (1962), 1065–1076. The $L^2$-modulus class is due to
S. M. Nikol'skii; see S. M. Nikol'skii, *Approximation of Functions of Several Variables and
Imbedding Theorems*, Springer, 1975.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- The smoothness index $\ell(\beta)$: the greatest integer **strictly** smaller than `β`.
For integer `β` this is `β - 1`; for non-integer `β > 0` it is the usual floor `⌊β⌋`.
Degenerate input `β ≤ 0` (never used) yields `0` by ℕ-truncation. -/
noncomputable def holderIndex (β : ℝ) : ℕ := ⌈β⌉₊ - 1

/-- **Hölder class** $\Sigma(\beta, L)$ on a set `T ⊆ ℝ` (classically an interval): the class of
`holderIndex β`-times continuously differentiable functions on `T` whose top derivative is
`(β - ℓ)`-Hölder with constant `L`. Membership is only meaningful for `0 < β`, `0 < L`, and `T`
an interval (on which `iteratedDerivWithin` is well behaved). -/
structure MemHolderOn (β L : ℝ) (f : ℝ → ℝ) (T : Set ℝ) : Prop where
  /-- Constitutive: the class consists of `ℓ = holderIndex β` times differentiable functions.
  Stated as `ContDiffOn`; equivalent to the classical phrasing because the Hölder field forces
  continuity of the top derivative. -/
  contDiffOn : ContDiffOn ℝ (holderIndex β) f T
  /-- Constitutive: the defining Hölder bound
  `|f⁽ℓ⁾(x) − f⁽ℓ⁾(y)| ≤ L·|x−y|^(β−ℓ)` on `T`. -/
  deriv_holder : ∀ x ∈ T, ∀ y ∈ T,
    |iteratedDerivWithin (holderIndex β) f T x - iteratedDerivWithin (holderIndex β) f T y|
      ≤ L * |x - y| ^ (β - (holderIndex β : ℝ))

/-- Global Hölder class: `MemHolderOn` with `T = univ`. -/
def MemHolder (β L : ℝ) (f : ℝ → ℝ) : Prop := MemHolderOn β L f Set.univ

/-- **Hölder density class** $\mathcal P(\beta, L)$: probability densities on `ℝ` that belong to
the Hölder class $\Sigma(\beta, L)$ globally. -/
structure IsHolderDensity (β L : ℝ) (p : ℝ → ℝ) : Prop where
  /-- Constitutive: a density is nonnegative. -/
  nonneg : ∀ x, 0 ≤ p x
  /-- Constitutive: a density integrates to one. (With the Bochner integral this also forces
  integrability of `p`: a non-integrable integrand would give the junk value `0 ≠ 1`.) -/
  integral_one : ∫ x, p x = 1
  /-- Constitutive: global Hölder smoothness of the density. -/
  holder : MemHolderOn β L p Set.univ

/-- **Nikol'skii class** $H(\beta, L)$: `ℓ = holderIndex β` times continuously differentiable
functions whose top derivative is `(β − ℓ)`-Hölder *in the `L²(ℝ)` sense*:
`‖f⁽ℓ⁾(· + t) − f⁽ℓ⁾‖₂ ≤ L·|t|^(β−ℓ)` for every shift `t`. -/
structure MemNikolski (β L : ℝ) (f : ℝ → ℝ) : Prop where
  /-- Constitutive: `ℓ = holderIndex β` times differentiable. Stated as `ContDiff`; the
  continuity refinement over the classical a.e. phrasing is a documented mild strengthening. -/
  contDiff : ContDiff ℝ (holderIndex β) f
  /-- Constitutive: the defining `L²`-translate bound, in squared form. Stated with the lower
  Lebesgue integral so that non-square-integrable differences register as `∞` rather than the
  Bochner junk value `0` (which would satisfy the bound vacuously). -/
  translate_sq_le : ∀ t : ℝ,
    ∫⁻ x, ENNReal.ofReal
        ((iteratedDeriv (holderIndex β) f (x + t) - iteratedDeriv (holderIndex β) f x) ^ 2)
      ≤ ENNReal.ofReal ((L * |t| ^ (β - (holderIndex β : ℝ))) ^ 2)

/-- **Nikol'skii density class** $\mathcal P_H(\beta, L)$: probability densities in the
Nikol'skii class $H(\beta, L)$. -/
structure IsNikolskiDensity (β L : ℝ) (p : ℝ → ℝ) : Prop where
  /-- Constitutive: a density is nonnegative. -/
  nonneg : ∀ x, 0 ≤ p x
  /-- Constitutive: a density integrates to one. -/
  integral_one : ∫ x, p x = 1
  /-- Constitutive: Nikol'skii smoothness of the density. -/
  nikolski : MemNikolski β L p

/-- The law on `ℝ` of an observation with Lebesgue density `p`:
`volume.withDensity (fun x => ENNReal.ofReal (p x))`. A probability measure whenever `p` is a
measurable density (nonnegative, integrating to one). -/
noncomputable def densityMeasure (p : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (p x)

end StatLean.NonparametricStatistics
