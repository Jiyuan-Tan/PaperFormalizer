module
public import StatLean.HighDimensionalStatistics.CompressedSensing.Defs
public import StatLean.HighDimensionalStatistics.Lasso.Defs

@[expose] public section

/-!
# Basis pursuit — cone membership and uniqueness from a trivial cone–null intersection

Let $X$ be an $n \times d$ design matrix and let $\beta^\star$ be a vector supported on
an index set $S \subseteq \{1, \dots, d\}$ (so $\beta^\star_j = 0$ for $j \notin S$).
Basis pursuit recovers $\beta^\star$ from $Y = X\beta^\star$ by solving the $\ell^1$
minimization problem $\min_{\beta} \lVert \beta \rVert_1$ subject to $X\beta = Y$. Write
$C(S)$ for the cone of vectors $\Delta$ whose off-support mass is dominated by their
on-support mass, $\lVert \Delta_{S^c} \rVert_1 \le \lVert \Delta_S \rVert_1$, and write
$\mathrm{Null}(X) = \ker X$ for the null space. This file proves the two shared
structural facts:

* **Cone membership.** If $\hat\beta$ is any basis-pursuit solution for $Y = X\beta^\star$,
  then the error $\Delta = \hat\beta - \beta^\star$ lies in the cone $C(S)$, i.e.
  $\lVert (\hat\beta - \beta^\star)_{S^c} \rVert_1 \le \lVert (\hat\beta - \beta^\star)_S \rVert_1$.
* **Uniqueness.** If the cone meets the null space only at the origin,
  $C(S) \cap \mathrm{Null}(X) = \{0\}$, then for every $\beta^\star$ supported on $S$ the
  basis-pursuit problem for $Y = X\beta^\star$ has $\beta^\star$ as its *unique* minimizer.

These are the two lemmas that the cone theorem (`ConeTheorem.lean`, Lu-BDA §8.2,
Theorem 8.1) and the RIP recovery theorem (`RIPRecovery.lean`, Lu-BDA §9.1,
Theorem 9.1) both rely on:

* `deviation_mem_cone_of_basisPursuit` — optimality of basis pursuit forces the error
  `Δ = β̂ − β*` into the cone `C(S) = reCone S 1` (Eq (8.3)).
* `unique_basisPursuit_of_cone_trivial` — if `C(S) ∩ Null(X) = {0}` then `β*` is the
  unique basis-pursuit solution (the sufficiency core, shared by both theorems).

Concept-layer (theorem-agnostic); the cone `C(S)` is `reCone S 1` from `Lasso/Defs.lean`.
The condition $C(S) \cap \mathrm{Null}(X) = \{0\}$ is the support-restricted form of the
null-space property of compressed sensing.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 8 (Compressive Sensing), §8.2, Theorem 8.1 (perfect
recovery / unique basis-pursuit solution) and Eq (8.3); the uniqueness clause is the
sufficiency direction of the same theorem, and the recovery half is reused in Chapter 9
(Restricted Isometry Property), §9.1, Theorem 9.1 (Perfect Recovery Under RIP).

**Proof formalization notes.**

* *Cone membership* (`deviation_mem_cone_of_basisPursuit`, via the shared engine
  `mem_cone_of_feasible_of_le`). From basis-pursuit feasibility $\lVert\hat\beta\rVert_1
  \le \lVert\beta^\star\rVert_1$, split the $\ell^1$ norm over $S$ and $S^c$
  (`l1Norm_split`). Since $\beta^\star$ is supported on $S$, its $S^c$-restriction
  vanishes, so $\lVert\beta^\star\rVert_1 = \lVert\beta^\star_S\rVert_1$. Writing
  $\hat\beta = \beta^\star + \Delta$ and applying the reverse triangle inequality on the
  $S$-block (`l1Norm_sub_le`) yields
  $\lVert\Delta_{S^c}\rVert_1 \le \lVert\Delta_S\rVert_1$, i.e. $\Delta \in C(S)$.
* *Uniqueness* (`unique_basisPursuit_of_cone_trivial`). Any feasible competitor $\beta$
  with $\lVert\beta\rVert_1 \le \lVert\beta^\star\rVert_1$ has deviation $\Delta =
  \beta - \beta^\star$ both in $\mathrm{Null}(X)$ (same image, $X\beta = X\beta^\star$)
  and in $C(S)$ (cone membership above), hence $\Delta \in C(S) \cap \mathrm{Null}(X) =
  \{0\}$, so $\beta = \beta^\star$. The optimality clause of `IsUniqueBasisPursuit` is
  then immediate (uniqueness collapses the only smaller-or-equal-norm competitor onto
  $\beta^\star$).

**Bibliographic comments.** The characterization that $\ell^1$ minimization recovers
every $k$-sparse vector exactly iff a cone/null-space transversality condition holds is
the *null-space property* (NSP) of compressed sensing. The clean range-vs-null-space
formulation used here originates with A. Cohen, W. Dahmen and R. DeVore, "Compressed
sensing and best $k$-term approximation", *Journal of the American Mathematical Society*
22 (2009), no. 1, 211–231, which proves that the null-space property is equivalent to
instance-optimal recovery; earlier exact-recovery/uniqueness conditions of this flavor
appear in D. L. Donoho and X. Huo, "Uncertainty principles and ideal atomic
decomposition", *IEEE Trans. Inform. Theory* 47 (2001), no. 7, 2845–2862, and in
R. Gribonval and M. Nielsen, "Sparse representations in unions of bases", *IEEE Trans.
Inform. Theory* 49 (2003), no. 12, 3320–3325. The support-restricted version proven
here ($C(S) \cap \mathrm{Null}(X) = \{0\}$ for a fixed $S$) is a standard packaging of
that property; it is the deterministic core later combined
with the restricted-isometry property to give probabilistic recovery guarantees
(E. J. Candès and T. Tao, "Decoding by linear programming", *IEEE Trans. Inform. Theory*
51 (2005), no. 12, 4203–4215).
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Feasibility + ℓ¹-domination ⟹ cone membership** (Lu-BDA §8.2, Eq (8.3) core). For
`β*` supported on `S`, any `β` with the same image (`X β = X β*`) and no larger ℓ¹ norm
has its deviation `β − β*` in the cone `C(S) = reCone S 1`. The shared engine of both
`deviation_mem_cone_of_basisPursuit` and the uniqueness clause of
`unique_basisPursuit_of_cone_trivial`. -/
private theorem mem_cone_of_feasible_of_le
    (S : Finset (Fin d))
    (βstar β : EuclideanSpace ℝ (Fin d))
    (hsupp : ∀ i ∉ S, βstar.ofLp i = 0)
    (hle : l1Norm β ≤ l1Norm βstar) :
    (β - βstar) ∈ reCone S 1 := by
  set Δ := β - βstar with hΔ
  have hβ : β = βstar + Δ := by rw [hΔ]; abel
  change l1Norm (restrict Sᶜ Δ) ≤ 1 * l1Norm (restrict S Δ)
  rw [one_mul]
  -- β* supported on S ⟹ its complement-restriction vanishes
  have hcompl : restrict Sᶜ βstar = 0 := restrict_compl_eq_zero S βstar hsupp
  -- ‖β*‖₁ = ‖β*|_S‖₁
  have e2 : l1Norm βstar = l1Norm (restrict S βstar) := by
    rw [l1Norm_split S βstar, hcompl]; simp
  -- split ‖β‖₁ and rewrite the two blocks
  have e3 : restrict S β = restrict S βstar + restrict S Δ := by
    rw [hβ]; exact restrict_add S βstar Δ
  have e4 : restrict Sᶜ β = restrict Sᶜ Δ := by
    rw [hβ, restrict_add, hcompl, zero_add]
  have hβval : l1Norm β
      = l1Norm (restrict S βstar + restrict S Δ) + l1Norm (restrict Sᶜ Δ) := by
    rw [l1Norm_split S β, e3, e4]
  have hle2 : l1Norm β ≤ l1Norm (restrict S βstar) := e2 ▸ hle
  have rt := l1Norm_sub_le (restrict S βstar) (restrict S Δ)
  linarith [hβval, hle2, rt]

/-- **Optimality ⟹ cone membership** (Lu-BDA §8.2, Eq (8.3)). If `β*` is supported on
`S` and `β̂` is a basis-pursuit solution for `Y = X β*`, then the error `β̂ − β*`
lies in the cone `C(S) = reCone S 1`, i.e. `‖(β̂−β*)_{Sᶜ}‖₁ ≤ ‖(β̂−β*)_S‖₁`.

Proof (book): from feasibility `‖β̂‖₁ ≤ ‖β*‖₁`, split `‖·‖₁` over `S`/`Sᶜ`
(`l1Norm_split`), use `β*` supported on `S` and the reverse triangle inequality on the
`S`-block. -/
theorem deviation_mem_cone_of_basisPursuit
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (βstar βhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: β* is supported on S (β*ⱼ = 0 for j ∉ S); Lu-BDA §8.2, Theorem 8.1
    (hsupp : ∀ i ∉ S, βstar.ofLp i = 0)
    -- USER-INPUT: β̂ is a basis-pursuit solution for Y = X β*; Lu-BDA §8.2, Theorem 8.1
    (hbp : IsBasisPursuit X (designMap X βstar) βhat) :
    (βhat - βstar) ∈ reCone S 1 :=
  mem_cone_of_feasible_of_le S βstar βhat hsupp (hbp.2 βstar rfl)

/-- **Cone-condition ⟹ unique recovery** (Lu-BDA §8.2, sufficiency of Theorem 8.1). If the
cone `C(S) = reCone S 1` meets the null space `Null(X) = ker (designMap X)` only at
`0`, then for any `β*` supported on `S` the basis-pursuit problem for `Y = X β*` has
`β*` as its unique solution.

Proof (book): any feasible competitor `β` with `‖β‖₁ ≤ ‖β*‖₁` has `Δ = β − β* ∈
Null(X)` (same image) and `Δ ∈ C(S)` (by `deviation_mem_cone_of_basisPursuit`), hence
`Δ ∈ C(S) ∩ Null(X) = {0}`, so `β = β*`. -/
theorem unique_basisPursuit_of_cone_trivial
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    -- USER-INPUT: cone ∩ null space is trivial, C(S) ∩ Null(X) = {0}; Lu-BDA §8.2, Definition 8.3 (Cone Condition)
    (htriv : reCone S 1 ∩ (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) = {0})
    (βstar : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: β* is supported on S; Lu-BDA §8.2, Theorem 8.1
    (hsupp : ∀ i ∉ S, βstar.ofLp i = 0) :
    IsUniqueBasisPursuit X (designMap X βstar) βstar := by
  -- Uniqueness: any feasible competitor with no larger ℓ¹ norm equals β*.
  have uniq : ∀ β, designMap X β = designMap X βstar → l1Norm β ≤ l1Norm βstar →
      β = βstar := by
    intro β hfeas hle
    have hcone : (β - βstar) ∈ reCone S 1 :=
      mem_cone_of_feasible_of_le S βstar β hsupp hle
    have hker : (β - βstar) ∈
        (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) := by
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hfeas, sub_self]
    have hmem : (β - βstar) ∈ ({0} : Set (EuclideanSpace ℝ (Fin d))) := by
      rw [← htriv]; exact Set.mem_inter hcone hker
    exact sub_eq_zero.mp (Set.mem_singleton_iff.mp hmem)
  refine ⟨⟨rfl, ?_⟩, uniq⟩
  intro β hfeas
  by_cases hcase : l1Norm β ≤ l1Norm βstar
  · exact le_of_eq (congrArg l1Norm (uniq β hfeas hcase)).symm
  · exact (not_le.mp hcase).le

end StatLean.HighDimensionalStatistics
