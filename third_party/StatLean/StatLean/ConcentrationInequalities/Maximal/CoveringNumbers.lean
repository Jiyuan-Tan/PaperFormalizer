module
public import Mathlib.Topology.MetricSpace.CoveringNumbers

@[expose] public section

/-!
# ε-Nets and covering numbers

Book-facing definitions for the ε-net and covering-number vocabulary used throughout
the maximal-inequality and metric-entropy chapters.

Let $(X, d)$ be a (pseudo-)metric space and $s \subseteq X$.  A subset $N \subseteq s$
is an **$\varepsilon$-net** of $s$ if every point of $s$ lies within distance
$\varepsilon$ of some point of $N$, i.e.
$$\forall\, x \in s,\ \exists\, y \in N,\ d(x, y) \le \varepsilon.$$
(The net is required to lie *inside* $s$ — an *internal* $\varepsilon$-cover.)

The **covering number** $N(s, d, \varepsilon)$ is the smallest possible cardinality of
such a net:
$$N(s, d, \varepsilon) \;=\; \min\bigl\{\, \lvert N\rvert : N \subseteq s \text{ is a finite } \varepsilon\text{-net of } s \,\bigr\},$$
taken to be $+\infty$ when no finite $\varepsilon$-net exists.  It is non-increasing in
$\varepsilon$: a smaller radius requires (weakly) more centres.

All non-trivial combinatorial content is delegated to
`Mathlib.Topology.MetricSpace.CoveringNumbers`.

## Main definitions

* `IsEpsilonNet N s ε` — `N ⊆ s` and every point of `s` lies within `dist ≤ ε`
  of some point of `N` (Lu-BDA §6.2, Definition 6.2 (ε-Net)).
* `coveringNumber s ε` — minimum cardinality (in `ℕ∞`) of a finite internal
  ε-net of `s`; thin alias of `Metric.coveringNumber` (Lu-BDA §6.2,
  Lemma 6.1 (Covering Number), `N(s, d, ε)`).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 6 (Bernstein and Maximal Inequalities),
§6.2 — Definition 6.2 ($\varepsilon$-Net) and Lemma 6.1 (Covering Number), the
covering number $N(s, d, \varepsilon)$.

**Proof formalization notes.**
These are *definitions*, not theorems; the only proof obligations are the sanity
lemmas at the end of the file (`isEpsilonNet_self`, `coveringNumber_anti`,
`IsEpsilonNet.isCover`).  Modelling choices:

* `coveringNumber s ε` is a thin alias of `Metric.coveringNumber (Real.toNNReal ε) s`.
  The `Real.toNNReal` coercion clamps `ε ≤ 0` to `0`; in particular `ε = 0` gives
  `s.encard` (every point is its own centre), and negative radii collapse to the
  `ε = 0` case rather than being undefined.
* `IsEpsilonNet` uses the closed condition `dist x y ≤ ε`, matching the book's
  $\le$ convention (rather than a strict `<`).  For `ε < 0` the condition is
  unsatisfiable, forcing `s = ∅`; for `ε = 0` in a genuine metric space it forces
  `N = s`.
* `IsEpsilonNet.isCover` is a `LEAN-ONLY` bridge from this `dist ≤ ε` form to
  Mathlib's `NNReal`/`edist`-based `Metric.IsCover`, carrying no book content.

**Bibliographic comments.**
The notions of $\varepsilon$-net, covering number, and the dual packing/capacity numbers
originate with A. N. Kolmogorov and V. M. Tikhomirov, "ε-entropy and ε-capacity of sets
in function spaces," *Uspekhi Matematicheskikh Nauk* **14** (1959), no. 2 (86), 3–86
(English translation: *American Mathematical Society Translations*, Series 2, Vol. 17
(1961), 277–364), where the logarithm $\log_2 N(s, d, \varepsilon)$ is introduced as the
*$\varepsilon$-entropy* (metric entropy) of $s$.  The covering-number vocabulary is by now
standard textbook material in empirical-process and high-dimensional statistics — see also
M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Cambridge
University Press, 2019), §5.1, for the modern statistical treatment that the Lu-BDA §6.2
(Bernstein and Maximal Inequalities) presentation follows.
-/

open Set
open scoped NNReal ENNReal

namespace StatLean.ConcentrationInequalities

variable {X : Type*} [PseudoMetricSpace X]

/-! ### ε-Net -/

/-- **ε-Net** (Lu-BDA §6.2, Definition 6.2 (ε-Net)).

A subset `N` of a pseudo-metric space `(X, d)` is an *ε-net* of `s ⊆ X` if:
- `N ⊆ s` (internal: the net lies inside the set), and
- `∀ x ∈ s, ∃ y ∈ N, dist x y ≤ ε` (every point of `s` is ε-close to some net point).

Also called an *internal ε-cover* in the literature (see `Metric.IsCover`).

Edge behaviour: for `ε < 0` the distance condition is impossible (distances are
non-negative), so `IsEpsilonNet N s ε` forces `s = ∅`.  For `ε = 0` in a metric
space, `dist x y ≤ 0 ↔ x = y`, so one needs `N = s`. -/
def IsEpsilonNet (N : Set X) (s : Set X) (ε : ℝ) : Prop :=
  N ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ N, dist x y ≤ ε

/-! ### Covering number -/

/-- **Covering number** `N(s, d, ε)` (Lu-BDA §6.2, Lemma 6.1 (Covering Number)).

The minimum cardinality (in `ℕ∞`) of a finite internal ε-net of `s ⊆ X`.
Returns `⊤` when no finite ε-net of `s` exists.

Thin alias of `Metric.coveringNumber (Real.toNNReal ε) s`.  The `toNNReal`
coercion clamps `ε ≤ 0` to `0`; for `ε = 0` this equals `s.encard`.

This is Lu-BDA §6.2's `N(s, d, ε)` (Lemma 6.1 (Covering Number)). -/
noncomputable def coveringNumber (s : Set X) (ε : ℝ) : ℕ∞ :=
  Metric.coveringNumber (Real.toNNReal ε) s

/-! ### Sanity lemmas -/

/-- `s` is an ε-net of itself for any non-negative `ε`
(take `y = x`; then `dist x x = 0 ≤ ε`). -/
lemma isEpsilonNet_self (s : Set X) {ε : ℝ} (hε : 0 ≤ ε) : IsEpsilonNet s s ε :=
  ⟨le_refl s, fun x hx => ⟨x, hx, (dist_self x).le.trans hε⟩⟩

/-- The covering number is anti-monotone in the radius:
a smaller `ε` requires weakly more net points (Lu-BDA §6.2, Lemma 6.1 (Covering Number)). -/
lemma coveringNumber_anti {s : Set X} {ε δ : ℝ} (h : ε ≤ δ) :
    coveringNumber s δ ≤ coveringNumber s ε :=
  Metric.coveringNumber_anti (Real.toNNReal_le_toNNReal h)

/-- If `N` is an ε-net of `s` (with `ε ≥ 0`), it is also a `Metric.IsCover`. -/
-- LEAN-ONLY: bridge to Mathlib's NNReal / edist API; no book content.
lemma IsEpsilonNet.isCover {N s : Set X} {ε : ℝ} (hε : 0 ≤ ε)
    (h : IsEpsilonNet N s ε) : Metric.IsCover (Real.toNNReal ε) s N := by
  intro x hx
  obtain ⟨y, hy, hd⟩ := h.2 x hx
  -- ↑(Real.toNNReal ε) : ENNReal = ENNReal.ofReal ε (definitionally), so edist_le_ofReal applies.
  exact ⟨y, hy, (edist_le_ofReal hε).mpr hd⟩

end StatLean.ConcentrationInequalities
