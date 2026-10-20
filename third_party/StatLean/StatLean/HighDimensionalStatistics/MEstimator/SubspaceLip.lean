module
public import StatLean.HighDimensionalStatistics.MEstimator.Defs

@[expose] public section

/-!
# Subspace Lipschitz (compatibility) constant — defining inequality

For a regularizer (seminorm) $\Phi$ on a finite-dimensional inner-product space and a subspace
$S$, the **subspace Lipschitz constant** (Wainwright's *subspace compatibility constant*) is
$$\Psi(S) \;=\; \sup_{u \in S \setminus \{0\}} \frac{\Phi(u)}{\lVert u\rVert},$$
where $\lVert\cdot\rVert$ is the inner-product (Euclidean) norm. The constant measures how much the
regularizer can stretch a unit vector confined to $S$. Its **defining inequality** is the linear
bound it yields on $S$:
$$\Phi(u) \;\le\; \Psi(S)\,\lVert u\rVert \qquad \text{for all } u \in S.$$
This is exactly the property invoked by the estimation-error results (Theorem 9.19, Corollary 9.20,
Theorem 9.24), where it appears as step (iii) of equation (9.45).

The companion fact $\Psi(S) \ge 0$ is also recorded.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 9 (Decomposability and restricted strong convexity),
Definition 9.18 (subspace compatibility constant); the defining inequality is step (iii) of
Eq. (9.45) in the proof of the estimation-error bound.

**Proof formalization notes.** The non-trivial content is that the supremum defining $\Psi(S)$ is
over a set that is **bounded above**, so that `le_csSup` applies and gives the defining inequality.
Boundedness holds because *any* seminorm $\Phi$ on a finite-dimensional inner-product space is
dominated by a multiple of the norm: choosing an orthonormal basis $(b_i)$,
$$\Phi(x) \le \sum_i \lvert\langle b_i, x\rangle\rvert\,\Phi(b_i)
            \le \Big(\textstyle\sum_i \Phi(b_i)\Big)\,\lVert x\rVert$$
by subadditivity, homogeneity, and Cauchy–Schwarz ($\lvert\langle b_i, x\rangle\rvert \le
\lVert b_i\rVert\,\lVert x\rVert = \lVert x\rVert$). This is `seminorm_le_const_mul_norm`, which
supplies the upper bound `C` witnessing that the ratio set is bounded above. In `subspaceLip_le`
the case `u = 0` is handled separately (both sides vanish, `map_zero`); for `u ≠ 0` the ratio
$\Phi(u)/\lVert u\rVert$ is a member of the set whose `sSup` is $\Psi(S)$. In the degenerate case
`S = 0` the ratio set is empty and `sSup ∅ = 0`, consistent with `subspaceLip_nonneg`.

This is a concept-layer helper (theorem-agnostic); consumed by `Bound.lean` and `DualBound.lean`.

**Bibliographic comments.** The subspace compatibility / Lipschitz constant originates with
S. N. Negahban, P. Ravikumar, M. J. Wainwright and B. Yu, "A Unified Framework for
High-Dimensional Analysis of $M$-Estimators with Decomposable Regularizers," *Statistical Science*
27 (4), 538–557, 2012, where it is introduced as the **subspace compatibility constant**
$\Psi(\mathcal{M}) = \sup_{u \in \mathcal{M}\setminus\{0\}} \mathcal{R}(u)/\lVert u\rVert_2$
(their Definition 3) to convert a regularizer bound on the model subspace into an $\ell_2$-norm
bound inside the master oracle inequality (their Theorem 1). Wainwright's 2019 textbook
(Definition 9.18) is the streamlined exposition of that paper; the bound formalized here is the
elementary, regularizer-agnostic lemma underlying both.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Finite-dimensional seminorm bound.** Any seminorm `Φ` on a finite-dimensional inner-product
space is dominated by a multiple of the norm: `∃ C ≥ 0, ∀ x, Φ x ≤ C·‖x‖`. Proof via an
orthonormal basis: `Φ x ≤ ∑ᵢ |⟨bᵢ,x⟩|·Φ(bᵢ) ≤ √(∑Φ(bᵢ)²)·‖x‖` (triangle + Cauchy–Schwarz). -/
lemma seminorm_le_const_mul_norm (Φ : Seminorm ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, Φ x ≤ C * ‖x‖ := by
  let b := stdOrthonormalBasis ℝ E
  refine ⟨∑ i, Φ (b i), Finset.sum_nonneg (fun i _ => apply_nonneg Φ (b i)), fun x => ?_⟩
  calc Φ x = Φ (∑ i, b.repr x i • b i) := by rw [b.sum_repr x]
    _ ≤ ∑ i, Φ (b.repr x i • b i) :=
        Finset.le_sum_of_subadditive Φ (by simp) (fun a c => map_add_le_add Φ a c) _ _
    _ = ∑ i, |b.repr x i| * Φ (b i) := by simp_rw [map_smul_eq_mul, Real.norm_eq_abs]
    _ ≤ ∑ i, ‖x‖ * Φ (b i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg Φ (b i))
        rw [b.repr_apply_apply x i]
        calc |⟪b i, x⟫_ℝ| ≤ ‖b i‖ * ‖x‖ := abs_real_inner_le_norm (b i) x
          _ = ‖x‖ := by rw [b.orthonormal.1 i, one_mul]
    _ = (∑ i, Φ (b i)) * ‖x‖ := by rw [Finset.sum_mul]; simp_rw [mul_comm]

/-- The subspace Lipschitz constant is nonnegative (it is an `sSup` of nonnegative ratios, with the
empty/`S = 0` case giving `sSup ∅ = 0`). -/
lemma subspaceLip_nonneg (Φ : Seminorm ℝ E) (S : Submodule ℝ E) :
    0 ≤ subspaceLip Φ S := by
  unfold subspaceLip
  apply Real.sSup_nonneg
  rintro y ⟨u, -, rfl⟩
  exact div_nonneg (apply_nonneg Φ u) (norm_nonneg u)

/-- **Defining inequality of `Ψ(S)`** (Wainwright Def 9.18 / eq 9.45 step iii): for `u ∈ S`,
`Φ u ≤ Ψ(S)·‖u‖`. For `u = 0` both sides vanish; for `u ≠ 0`, `Φ(u)/‖u‖` is a member of the set
whose `sSup` is `Ψ(S)`, and that set is bounded above by `seminorm_le_const_mul_norm`. -/
lemma subspaceLip_le (Φ : Seminorm ℝ E) (S : Submodule ℝ E) {u : E} (hu : u ∈ S) :
    Φ u ≤ subspaceLip Φ S * ‖u‖ := by
  by_cases hu0 : u = 0
  · simp [hu0, map_zero]
  · have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    rw [← div_le_iff₀ hnorm]
    unfold subspaceLip
    apply le_csSup
    · obtain ⟨C, hC0, hC⟩ := seminorm_le_const_mul_norm Φ
      refine ⟨C, ?_⟩
      rintro y ⟨v, ⟨_, hv0⟩, rfl⟩
      have hvn : 0 < ‖v‖ := norm_pos_iff.mpr (by simpa using hv0)
      rw [div_le_iff₀ hvn]
      exact hC v
    · exact ⟨u, ⟨hu, hu0⟩, rfl⟩

end StatLean.HighDimensionalStatistics.MEstimator
