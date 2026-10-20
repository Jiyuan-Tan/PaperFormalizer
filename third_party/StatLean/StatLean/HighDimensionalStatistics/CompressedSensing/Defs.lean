module
public import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
public import StatLean.HighDimensionalStatistics.LinearModel.Defs

@[expose] public section

/-!
# Compressed sensing — primitives: sparsity, basis pursuit, restricted isometry property

Book setup: the noiseless sparse linear model $Y = X\beta^\*$ with design matrix
$X \in \mathbb{R}^{n\times d}$ in the high-dimensional regime $n \ll d$ and an unknown
$s$-sparse signal $\beta^\*$. The recovery method is **basis pursuit**, the
$\ell^1$-minimisation
$$\hat\beta = \arg\min_{\beta} \lVert\beta\rVert_1 \quad\text{subject to}\quad Y = X\beta,$$
and the standard sufficient condition for exact (and unique) recovery is the
**restricted isometry property** (RIP).

This concept-layer file fixes the four book-facing predicates that the recovery
theorems consume:

* **$s$-sparsity** `IsSparse s x` — $x$ has at most $s$ nonzero coordinates,
  i.e. $\lVert x\rVert_0 \le s$. Encoded in "support fits in a set" form: there
  is an index set $S$ with $|S| \le s$ and $x_i = 0$ for $i \notin S$.
* **Basis-pursuit estimator** `IsBasisPursuit X Y βhat` — $\hat\beta$ is feasible
  ($X\hat\beta = Y$) and $\ell^1$-minimal among all feasible points.
* **Unique basis-pursuit solution** `IsUniqueBasisPursuit X Y βhat` — $\hat\beta$ is
  a basis-pursuit minimiser, and any feasible point whose $\ell^1$ norm does not
  exceed $\lVert\hat\beta\rVert_1$ equals $\hat\beta$ (the "unique solution"
  conclusion of the cone theorem).
* **Restricted isometry property** `IsRIP X s δ` — $X$ satisfies $s$-RIP with
  constant $\delta$ when, for every $s$-sparse $\beta$,
  $$(1-\delta)\lVert\beta\rVert_2^2 \le \lVert X\beta\rVert_2^2 \le (1+\delta)\lVert\beta\rVert_2^2.$$
  The restricted isometry constant $\delta = \delta_s$ is a free parameter here;
  the threshold $\delta \in (0,1)$ is imposed by the consumer theorems, not by the
  definition.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapters 8–9 (Compressive Sensing, Restricted Isometry
Property): the sparse linear model and $s$-sparsity are introduced in Chapter 8
(Compressive Sensing), §8.1, Definition 8.1 (Sparse Linear Model); the basis-pursuit
program and its perfect-recovery theorem are in §8.2, Theorem 8.1; the RIP definition
is in Chapter 9 (Restricted Isometry Property), §9.1, Definition 9.1 (Restricted
Isometry Property).

**Proof formalization notes.** This file contains definitions only (no proofs).
Encoding choices: $s$-sparsity is stated in the decidability-free "support
fits in a set of cardinality $\le s$" form rather than via an $\ell^0$ counting
function, because that is the form the recovery proofs consume. The predicates
reuse `l1Norm` / `EuclideanSpace` from `ForMathlib/VecNorms.lean` and the design
map `designMap X : β ↦ X β` from `LinearModel/Defs.lean`. The cone $C(S)$ used by
the recovery theorems is the existing `reCone S 1` (`Lasso/Defs.lean`); the null
space of the design is `LinearMap.ker (designMap X)`.

**Bibliographic comments.** The restricted isometry property originates with
E. J. Candès and T. Tao, "Decoding by linear programming," *IEEE Transactions on
Information Theory* **51**(12):4203–4215, 2005 (Definition 1.1, the "restricted
isometry" condition $\delta_S$); the closely related $\ell^1$/$\ell^0$ equivalence
program was developed in E. J. Candès, J. Romberg and T. Tao, "Robust uncertainty
principles: exact signal reconstruction from highly incomplete frequency
information," *IEEE Transactions on Information Theory* **52**(2):489–509, 2006.
Basis pursuit — the $\ell^1$-minimisation program itself — is due to S. S. Chen,
D. L. Donoho and M. A. Saunders, "Atomic decomposition by basis pursuit," *SIAM
Journal on Scientific Computing* **20**(1):33–61, 1998. Lu, *Big Data Analysis*
presents these as standard compressed-sensing background rather than as original results.
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **`s`-sparsity** (Lu-BDA Ch8 §8.1, Definition 8.1 (Sparse Linear Model), `‖β‖₀ = ∑ⱼ 𝟙{βⱼ ≠ 0}`): `x` is `s`-sparse when its
support is contained in some index set of cardinality at most `s`. Stated in the
"support fits in a set" form (decidability-free, and the form the recovery proofs
consume) rather than via an `ℓ₀` counting function. -/
def IsSparse (s : ℕ) (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ S : Finset (Fin d), S.card ≤ s ∧ ∀ i ∉ S, x.ofLp i = 0

/-- **Basis-pursuit estimator predicate** (Lu-BDA Ch8 §8.2, Compressive Sensing): `βhat` is feasible
(`X βhat = Y`) and has minimal ℓ¹ norm among all feasible points. The
optimisation is `β̂ = argmin_β ‖β‖₁  s.t.  Y = X β`. -/
def IsBasisPursuit (X : Matrix (Fin n) (Fin d) ℝ) (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d)) : Prop :=
  designMap X βhat = Y ∧ ∀ β, designMap X β = Y → l1Norm βhat ≤ l1Norm β

/-- **Unique basis-pursuit solution** (Lu-BDA Ch8 §8.2, Theorem 8.1 (perfect recovery / unique basis-pursuit solution)): `βhat` is a basis-pursuit
minimiser, and every feasible point whose ℓ¹ norm does not exceed `‖βhat‖₁` equals
`βhat`. This is the "`β̂ = β*` is the unique solution" conclusion of the cone theorem. -/
def IsUniqueBasisPursuit (X : Matrix (Fin n) (Fin d) ℝ) (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d)) : Prop :=
  IsBasisPursuit X Y βhat ∧
    ∀ β, designMap X β = Y → l1Norm β ≤ l1Norm βhat → β = βhat

/-- **Restricted isometry property** (Lu-BDA Ch9 §9.1, Definition 9.1 (Restricted Isometry Property)): `X`
satisfies the `s`-RIP with constant `δ ∈ (0,1)` when, for every `s`-sparse `β`,
`(1 − δ)‖β‖₂² ≤ ‖X β‖₂² ≤ (1 + δ)‖β‖₂²`. The constant `δ` (the restricted isometry
constant `δ_s`) is left as a free parameter; the threshold `δ ∈ (0,1)` is imposed by
the consumers, not here. -/
def IsRIP (X : Matrix (Fin n) (Fin d) ℝ) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ β : EuclideanSpace ℝ (Fin d), IsSparse s β →
    (1 - δ) * ‖β‖ ^ 2 ≤ ‖designMap X β‖ ^ 2 ∧ ‖designMap X β‖ ^ 2 ≤ (1 + δ) * ‖β‖ ^ 2

end StatLean.HighDimensionalStatistics
