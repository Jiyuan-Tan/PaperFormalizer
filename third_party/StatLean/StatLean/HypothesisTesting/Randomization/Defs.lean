module
public import StatLean.MultipleTesting.ForMathlib.OrderStatistics
public import StatLean.HypothesisTesting.Tests.Defs

@[expose] public section

/-!
# Randomization tests — core data model

Under the **randomization hypothesis** — the law of the data is invariant under every
element of a finite group `G` of transformations — the conditional distribution of a
test statistic over the orbit of the observed data point is known exactly, and the
**randomization test** built from the orbit's order statistics has exact finite-sample
level. This file fixes:

* `RandomizationHypothesis G P` — `gX =_d X` for every `g : G`;
* `orbitValues G T x` — the multiset of statistic values over the orbit, as a
  `Fin (card G)`-indexed vector;
* `randDist G T x t` — the randomization distribution `M⁻¹ #{g : T(g·x) ≤ t}`;
* `orbitOrderStat G T x j` — the `j`-th smallest orbit value (1-indexed, junk `0` out
  of range);
* `randCritIndex G α = M − ⌊Mα⌋` and `randCritValue G T α x` — the critical order
  statistic `T^{(k)}`;
* `randPlusCount`, `randZeroCount`, `randGamma` — the counts `M⁺`, `M⁰` and the
  boundary-randomization weight `a(x) = (Mα − M⁺)/M⁰`;
* `randTest G T α` — the exact level-`α` randomization test;
* `randPValue G T x` — the randomization p-value `M⁻¹ #{g : T(g·x) ≥ T(x)}`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.2 (Permutation and Randomization Tests), Definition 17.2.1 (§17.2.1,
The Basic Construction): the randomization hypothesis `gX =_d X` under `H₀`. (`TSH4 §17.2 Def
17.2.1`.)

**Proof formalization notes.**
* Only invariance of the *null* law is assumed anywhere (the alternative need not be
  invariant) — that is the content of the randomization hypothesis.
* All constructions are total: out-of-range order statistics return `0`, and the
  boundary weight's denominator `M⁰` is at least `1` whenever `T(x)` equals the
  critical value (the identity element contributes), so the `0/0` corner is unreachable
  in the exactness proof.
* Enumeration of the group uses `Fintype.equivFin`; the order statistic reuses the
  multiple-testing area's `orderStat` (sorting via `Tuple.sort`).

**Bibliographic comments.** Randomization tests originate with R. A. Fisher (*The
Design of Experiments*, Oliver & Boyd, 1935) and E. J. G. Pitman ("Significance tests
which may be applied to samples from any populations," *J. R. Statist. Soc. Suppl.*
**4** (1937), 119–130); the group-theoretic formulation and exactness are classical
(cf. E. L. Lehmann and C. Stein, "On the theory of some non-parametric hypotheses,"
*Ann. Math. Statist.* **20** (1949), 28–45; M. Dwass, "Modified randomization tests for
nonparametric hypotheses," *Ann. Math. Statist.* **28** (1957), 181–187; W. Hoeffding,
"The large-sample power of tests based on permutations of observations," *Ann. Math.
Statist.* **23** (1952), 169–192).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.MultipleTesting (orderStat)

variable (G : Type*) [Group G] [Fintype G] {𝓧 : Type*} [MeasurableSpace 𝓧]
  [MulAction G 𝓧]

/-- **Randomization hypothesis**: the null law is invariant under every element of the
finite transformation group `G`. -/
def RandomizationHypothesis (P : Measure 𝓧) : Prop :=
  ∀ g : G, P.map (g • ·) = P

/-- The orbit's statistic values `(T(g·x))_g`, indexed through `Fintype.equivFin`. -/
noncomputable def orbitValues (T : 𝓧 → ℝ) (x : 𝓧) : Fin (Fintype.card G) → ℝ :=
  fun i => T ((Fintype.equivFin G).symm i • x)

/-- The **randomization distribution** `R̂(t ∣ x) = M⁻¹ ∑_g 1{T(g·x) ≤ t}`. -/
noncomputable def randDist (T : 𝓧 → ℝ) (x : 𝓧) (t : ℝ) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g : G, if T (g • x) ≤ t then (1 : ℝ) else 0

/-- The `j`-th smallest orbit value `T^{(j)}(x)` (1-indexed); junk `0` out of range. -/
noncomputable def orbitOrderStat (T : 𝓧 → ℝ) (x : 𝓧) (j : ℕ) : ℝ :=
  if h : j - 1 < Fintype.card G then orderStat (orbitValues G T x) ⟨j - 1, h⟩ else 0

/-- The critical index `k = M − ⌊Mα⌋`. -/
noncomputable def randCritIndex (α : ℝ) : ℕ :=
  Fintype.card G - ⌊(Fintype.card G : ℝ) * α⌋₊

/-- The critical value `T^{(k)}(x)` of the randomization test. -/
noncomputable def randCritValue (T : 𝓧 → ℝ) (α : ℝ) (x : 𝓧) : ℝ :=
  orbitOrderStat G T x (randCritIndex G α)

/-- `M⁺(x)`: the number of orbit values strictly above the critical value. -/
noncomputable def randPlusCount (T : 𝓧 → ℝ) (α : ℝ) (x : 𝓧) : ℕ :=
  (Finset.univ.filter fun g : G => randCritValue G T α x < T (g • x)).card

/-- `M⁰(x)`: the number of orbit values equal to the critical value. -/
noncomputable def randZeroCount (T : 𝓧 → ℝ) (α : ℝ) (x : 𝓧) : ℕ :=
  (Finset.univ.filter fun g : G => T (g • x) = randCritValue G T α x).card

/-- The boundary-randomization weight `a(x) = (Mα − M⁺(x)) / M⁰(x)`. -/
noncomputable def randGamma (T : 𝓧 → ℝ) (α : ℝ) (x : 𝓧) : ℝ :=
  ((Fintype.card G : ℝ) * α - randPlusCount G T α x) / randZeroCount G T α x

/-- The **randomization test**: reject above the orbit critical value, randomize on the
boundary with weight `a(x)`, accept below. -/
noncomputable def randTest (T : 𝓧 → ℝ) (α : ℝ) (x : 𝓧) : ℝ :=
  if randCritValue G T α x < T x then 1
  else if T x = randCritValue G T α x then randGamma G T α x
  else 0

/-- The **randomization p-value** `p̂(x) = M⁻¹ #{g : T(x) ≤ T(g·x)}`. -/
noncomputable def randPValue (T : 𝓧 → ℝ) (x : 𝓧) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g : G, if T x ≤ T (g • x) then (1 : ℝ) else 0

end StatLean.HypothesisTesting
