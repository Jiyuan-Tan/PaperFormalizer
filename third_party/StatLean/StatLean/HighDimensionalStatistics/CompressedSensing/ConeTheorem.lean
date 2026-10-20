module
public import StatLean.HighDimensionalStatistics.CompressedSensing.BasisPursuit

@[expose] public section

/-!
# The cone theorem (exact basis-pursuit recovery iff trivial cone–nullspace intersection)

Let $X \in \mathbb{R}^{n \times d}$ be a design matrix and $S \subseteq \{1,\dots,d\}$
a support set. *Basis pursuit* recovers a target $\beta^\star$ as the $\ell_1$-minimizer
among all coefficients consistent with the observations $X\beta^\star$. The theorem
characterizes exactly when basis pursuit recovers every $S$-supported target uniquely:

> Basis pursuit has $\beta^\star$ as its **unique** solution for every $\beta^\star$
> supported on $S$ **if and only if** the cone meets the null space only at the origin,
> $$ \mathcal{C}(S) \cap \mathrm{Null}(X) = \{0\}, $$
> where $\mathcal{C}(S) = \{\Delta : \lVert \Delta_{S^c} \rVert_1 \le \lVert \Delta_S \rVert_1\}$
> is the descent cone and $\mathrm{Null}(X)$ is the null space (kernel) of $X$.

In the formalization $\mathcal{C}(S)$ is `reCone S 1` and $\mathrm{Null}(X)$ is
`LinearMap.ker (designMap X)`. The bound $\lVert \Delta_{S^c} \rVert_1 \le \lVert \Delta_S \rVert_1$
appears as the factor-`1` form $\lVert \Delta_{S^c} \rVert_1 \le 1 \cdot \lVert \Delta_S \rVert_1$
of the general cone; no constants are changed relative to the book.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 8 (Compressive Sensing), §8.2, Theorem 8.1. The
descent cone $\mathcal{C}(S)$ is Definition 8.3 (Cone Condition).

**Proof formalization notes.**
The sufficiency (`⟸`) is `unique_basisPursuit_of_cone_trivial` (`BasisPursuit.lean`).
The necessity (`⟹`) is `cone_trivial_of_unique_basisPursuit` below (book contrapositive:
a nonzero `v ∈ C(S) ∩ Null(X)` yields a feasible competitor to `restrict S v`). The
biconditional `basisPursuit_unique_iff_cone_inter_ker` assembles the two directions.

**Bibliographic comments.**
The condition $\mathcal{C}(S) \cap \mathrm{Null}(X) = \{0\}$ is the support-restricted
form of the **null space property** (NSP) for $\ell_1$ recovery. Its equivalence with exact
$\ell_1$ recovery of all $S$-supported (more generally, $k$-sparse) vectors was established by
A. Cohen, W. Dahmen, and R. DeVore, "Compressed sensing and best $k$-term approximation,"
*Journal of the American Mathematical Society*, vol. 22, no. 1, pp. 211–231, 2009 (see their
null-space characterization of instance-optimal decoders). An earlier exact-recovery
criterion via an uncertainty principle for ideal atomic decomposition appears in
D. L. Donoho and X. Huo, "Uncertainty principles and ideal atomic decomposition,"
*IEEE Transactions on Information Theory*, vol. 47, no. 7, pp. 2845–2862, 2001. The
clean cone-versus-nullspace phrasing used here is standard textbook synthesis of these
sources; the support-restricted statement formalized below is not attributed to a single
seminal theorem.
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Necessity** of the cone condition (Lu-BDA §8.2, Theorem 8.1 ⟹). If basis pursuit
uniquely recovers every `β*` supported on `S`, then `C(S) ∩ Null(X) = {0}`.

Proof (book): suppose `0 ≠ v ∈ Null(X) ∩ C(S)`. Take `β* = restrict S v` (supported on
`S`) and the competitor `β = -restrict Sᶜ v`; then `X β = X β*` (since `X v = 0`) and
`‖β‖₁ = ‖v_{Sᶜ}‖₁ ≤ ‖v_S‖₁ = ‖β*‖₁` by `v ∈ C(S)`. Uniqueness forces `β = β*`,
i.e. `v = 0`, a contradiction. -/
theorem cone_trivial_of_unique_basisPursuit
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (h : ∀ βstar : EuclideanSpace ℝ (Fin d), (∀ i ∉ S, βstar.ofLp i = 0) →
        IsUniqueBasisPursuit X (designMap X βstar) βstar) :
    reCone S 1 ∩ (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) = {0} := by
  -- The restriction of `0` to any index set is `0` (used for `0 ∈ C(S)`).
  have hr0 : ∀ T : Finset (Fin d), restrict T (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
    intro T; apply WithLp.ofLp_injective 2; funext i
    rw [restrict_ofLp_apply]; simp
  apply subset_antisymm
  · -- `… ⊆ {0}`: a nonzero `v ∈ C(S) ∩ Null(X)` would give a feasible competitor.
    intro v hv
    obtain ⟨hcone, hker⟩ := hv
    have hc : l1Norm (restrict Sᶜ v) ≤ 1 * l1Norm (restrict S v) := hcone
    have hLv : designMap X v = 0 := by rwa [SetLike.mem_coe, LinearMap.mem_ker] at hker
    -- `β* = restrict S v` is supported on `S`.
    have hsupp : ∀ i ∉ S, (restrict S v).ofLp i = 0 := by
      intro i hi; rw [restrict_ofLp_apply, if_neg hi]
    -- Feasibility: `X (-v_{Sᶜ}) = X v_S`, since `X v = 0`.
    have hsum : designMap X (restrict S v) + designMap X (restrict Sᶜ v) = 0 := by
      rw [← map_add, restrict_add_restrict_compl]; exact hLv
    have key : designMap X (restrict S v) = - designMap X (restrict Sᶜ v) :=
      eq_neg_of_add_eq_zero_left hsum
    have hfeas : designMap X (-restrict Sᶜ v) = designMap X (restrict S v) := by
      rw [map_neg, ← key]
    -- ℓ¹-domination: `‖-v_{Sᶜ}‖₁ = ‖v_{Sᶜ}‖₁ ≤ ‖v_S‖₁`.
    have hle : l1Norm (-restrict Sᶜ v) ≤ l1Norm (restrict S v) := by
      rw [l1Norm_neg]; rw [one_mul] at hc; exact hc
    -- Uniqueness forces the competitor to equal `β*`.
    have heq : -restrict Sᶜ v = restrict S v :=
      (h (restrict S v) hsupp).2 (-restrict Sᶜ v) hfeas hle
    -- Hence `v = v_S + v_{Sᶜ} = -v_{Sᶜ} + v_{Sᶜ} = 0`.
    have hv0 : v = 0 := by
      have hvsum := restrict_add_restrict_compl S v
      rw [← heq, neg_add_cancel] at hvsum
      exact hvsum.symm
    rw [Set.mem_singleton_iff]; exact hv0
  · -- `{0} ⊆ …`: `0` is in the cone (both ℓ¹ sides vanish) and in the null space.
    intro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx
    refine ⟨?_, ?_⟩
    · change l1Norm (restrict Sᶜ (0 : EuclideanSpace ℝ (Fin d)))
        ≤ 1 * l1Norm (restrict S (0 : EuclideanSpace ℝ (Fin d)))
      rw [hr0, hr0]; simp
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_zero]

/-- **Cone theorem** (Lu, *Big Data Analysis* §8.2, Theorem 8.1; the cone is Definition 8.3).
Basis pursuit has `β*`
as its unique solution for every `β*` supported on `S` **iff** `C(S) ∩ Null(X) = {0}`. -/
theorem basisPursuit_unique_iff_cone_inter_ker
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (∀ βstar : EuclideanSpace ℝ (Fin d), (∀ i ∉ S, βstar.ofLp i = 0) →
        IsUniqueBasisPursuit X (designMap X βstar) βstar)
    ↔ reCone S 1 ∩ (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) = {0} :=
  ⟨fun h => cone_trivial_of_unique_basisPursuit X S h,
   fun htriv βstar hsupp => unique_basisPursuit_of_cone_trivial X S htriv βstar hsupp⟩

end StatLean.HighDimensionalStatistics
