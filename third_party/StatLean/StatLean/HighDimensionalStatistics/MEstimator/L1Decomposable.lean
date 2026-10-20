module
public import StatLean.HighDimensionalStatistics.MEstimator.Defs
public import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms

@[expose] public section

/-!
# The ℓ₁/ℓ∞ decomposable regularizer instance

This file constructs the concrete decomposable regularizer underlying the Lasso and the GLM
corollaries: the regularizer is the ℓ₁ norm `Φ(\theta) = \|\theta\|_1`, its dual norm is the
ℓ∞ norm `Φ^*(v) = \|v\|_\infty`, and the model subspace is the support submodule
`M(S) = M̄(S) = \{\theta : \theta_j = 0 \text{ for all } j \notin S\}` of vectors supported on a
fixed index set `S`. The headline property is **decomposability**: for any `\alpha` supported on
`S` and any `\beta` supported on the complement `S^c`,
`\|\alpha + \beta\|_1 = \|\alpha\|_1 + \|\beta\|_1` (additivity of ℓ₁ across disjoint supports).
The construction also records the supporting facts: the orthogonal complement of the support
submodule is `M(S)^\perp = M(S^c)`; the ℓ₁/ℓ∞ Hölder pairing
`\langle u, v\rangle \le \|u\|_1\,\|v\|_\infty`; and its tightness via sign-vector achievability,
i.e. the variational characterization that `\|v\|_\infty \le c` whenever
`\langle u, v\rangle \le c` for all `u` with `\|u\|_1 \le 1`.

The package is delivered to the GLM corollaries as `l1DecomposableReg S`. With this instance the
subspace compatibility constant is `\Psi(M(S)) = \sqrt{s}` (where `s = |S|`), the resulting error
set is the cone `reCone S 3`, and the regularizer-side curvature term reduces to the ℓ∞ norm of
the empirical-loss gradient, `\Phi^*(\nabla L_n(\theta^*)) = \|\nabla L_n(\theta^*)\|_\infty`.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 9 (Decomposability and restricted strong convexity),
Examples 9.1 and 9.10, Table 9.1; support submodule `M(S)` is Eq (9.23).

**Proof formalization notes.** The ℓ₁ and ℓ∞ norms are bundled as `Seminorm`s
(`l1Seminorm`, `linfSeminorm`); the ℓ∞ triangle/scaling laws are reduced coordinatewise through
the private helper `linfNorm_le_of_forall`, which upgrades a uniform coordinate bound
`|v_j| \le c` (with `0 \le c` to cover the empty index set) to `\|v\|_\infty \le c`. The Hölder
pairing is `l1_linf_holder`, inherited from `abs_inner_le_l1Norm_mul_linfNorm`. Tightness
(`linf_tight`) is proved by the coordinate sign vectors `\pm e_j` (each of ℓ₁ norm one), which
achieve `\langle \pm e_j, v\rangle = |v_j|`, forcing `c \ge |v_j|` for every `j` and hence
`c \ge \|v\|_\infty`; nonnegativity of `c` is extracted by testing at `u = 0`. The complement
identity `suppSubmodule_orthogonal` (`M(S)^\perp = M(S^c)`) reduces orthogonality to the
single-coordinate inner product `inner_single_left_ofLp`. Decomposability (`l1_decomp`) is the
disjoint-support sum split of the ℓ₁ definition; here `M = M̄`, the ideal/oracle case in which
the model subspace and its decomposability subspace coincide. No book-versus-Lean constant
deviations: all constants (the ℓ₁/ℓ∞ pairing, `\Psi = \sqrt{s}`, the factor-3 cone) match the
reference exactly.

**Bibliographic comments.** Decomposable regularizers and the subspace-pair framework
`(M, M̄^\perp)` originate with S. N. Negahban, P. Ravikumar, M. J. Wainwright and B. Yu,
"A unified framework for high-dimensional analysis of M-estimators with decomposable
regularizers," *Statistical Science* 27(4):538–557, 2012. In that paper decomposability is the
defining condition (Definition 1, equation (5)): `\Phi(\alpha + \beta) = \Phi(\alpha) + \Phi(\beta)`
for `\alpha \in M` and `\beta \in M̄^\perp`, and the ℓ₁ norm with the support pair
`M(S) = M̄(S) = \{\theta : \theta_{S^c} = 0\}` is presented as their leading worked example (the
Lasso / sparse-vector case). The treatment formalized here (Wainwright 2019, Ch. 9)
is the streamlined exposition of that framework; the ℓ₁/ℓ∞ dual pairing itself is classical
(Hölder duality of `\ell_p`/`\ell_q` with `p = 1`, `q = \infty`).
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace

variable {d : ℕ}

/-- The **support submodule** `M(S) = {θ : θⱼ = 0 for all j ∉ S}` (Wainwright eq 9.23). -/
def suppSubmodule (S : Finset (Fin d)) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) where
  carrier := {θ | ∀ j ∉ S, θ.ofLp j = 0}
  zero_mem' := by intro j hj; simp
  add_mem' := by
    intro a b ha hb j hj
    simp only [WithLp.ofLp_add, Pi.add_apply, ha j hj, hb j hj, add_zero]
  smul_mem' := by
    intro c a ha j hj
    simp only [WithLp.ofLp_smul, Pi.smul_apply, ha j hj, smul_zero]

/-- ℓ₁ as a seminorm on `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def l1Seminorm (d : ℕ) : Seminorm ℝ (EuclideanSpace ℝ (Fin d)) where
  toFun := l1Norm
  map_zero' := by exact l1Norm_zero
  add_le' := by intro x y; exact l1Norm_add_le x y
  neg' := by intro x; exact l1Norm_neg x
  smul' := by
    intro c x
    unfold l1Norm
    rw [Real.norm_eq_abs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, abs_mul]

/-- A coordinatewise bound `|vⱼ| ≤ c` (with `0 ≤ c` to cover the empty index set) upgrades to the
ℓ∞ bound `‖v‖∞ ≤ c`. Private helper for `linfSeminorm.add_le'` and `linf_tight`. -/
private lemma linfNorm_le_of_forall {v : EuclideanSpace ℝ (Fin d)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |v.ofLp i| ≤ c) : linfNorm v ≤ c := by
  unfold linfNorm
  rcases isEmpty_or_nonempty (Fin d) with he | hne
  · haveI := he; rw [Real.iSup_of_isEmpty]; exact hc
  · haveI := hne; exact ciSup_le h

/-- ℓ∞ as a seminorm on `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def linfSeminorm (d : ℕ) : Seminorm ℝ (EuclideanSpace ℝ (Fin d)) where
  toFun := linfNorm
  map_zero' := by
    change linfNorm (0 : EuclideanSpace ℝ (Fin d)) = 0
    unfold linfNorm; simp
  add_le' := by
    intro x y
    refine linfNorm_le_of_forall (add_nonneg (linfNorm_nonneg x) (linfNorm_nonneg y)) fun i => ?_
    calc |(x + y).ofLp i| = |x.ofLp i + y.ofLp i| := by rw [WithLp.ofLp_add, Pi.add_apply]
      _ ≤ |x.ofLp i| + |y.ofLp i| := abs_add_le _ _
      _ ≤ linfNorm x + linfNorm y := add_le_add (abs_le_linfNorm x i) (abs_le_linfNorm y i)
  neg' := by
    intro x
    unfold linfNorm
    refine iSup_congr fun i => ?_
    rw [WithLp.ofLp_neg, Pi.neg_apply, abs_neg]
  smul' := by
    intro c x
    unfold linfNorm
    rw [Real.norm_eq_abs, Real.mul_iSup_of_nonneg (abs_nonneg c)]
    refine iSup_congr fun i => ?_
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, abs_mul]

/-- ℓ₁/ℓ∞ **Hölder pairing**: `⟪u, v⟫ ≤ ‖u‖₁·‖v‖∞` (from `abs_inner_le_l1Norm_mul_linfNorm`). -/
lemma l1_linf_holder (u v : EuclideanSpace ℝ (Fin d)) :
    ⟪u, v⟫_ℝ ≤ l1Norm u * linfNorm v := by
  exact le_trans (le_abs_self _) (abs_inner_le_l1Norm_mul_linfNorm u v)

/-- Inner product against a single coordinate basis vector: `⟪eⱼ·a, v⟫ = a · vⱼ`.
Private helper for `linf_tight` and `suppSubmodule_orthogonal`. -/
private lemma inner_single_left_ofLp (j : Fin d) (a : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    ⟪EuclideanSpace.single j a, v⟫_ℝ = a * v.ofLp j := by
  have hsum : (⟪EuclideanSpace.single j a, v⟫_ℝ : ℝ)
      = ∑ i, (EuclideanSpace.single j a).ofLp i * v.ofLp i := by
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change v.ofLp i * (EuclideanSpace.single j a).ofLp i
        = (EuclideanSpace.single j a).ofLp i * v.ofLp i
    ring
  rw [hsum, Finset.sum_eq_single j]
  · rw [PiLp.ofLp_single, Pi.single_eq_same]
  · intro i _ hij
    rw [PiLp.ofLp_single, Pi.single_eq_of_ne hij, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ j) h'

/-- **ℓ∞ tightness** (the dual-norm variational characterization): if `⟪u, v⟫ ≤ c` for every `u` with
`‖u‖₁ ≤ 1`, then `‖v‖∞ ≤ c`. Proof: the coordinate sign vector `±eⱼ` (which has `‖·‖₁ = 1`) achieves
`⟪±eⱼ, v⟫ = |vⱼ|`, so `c ≥ |vⱼ|` for every `j`, hence `c ≥ ‖v‖∞`. -/
lemma linf_tight (v : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (h : ∀ u : EuclideanSpace ℝ (Fin d), l1Norm u ≤ 1 → ⟪u, v⟫_ℝ ≤ c) :
    linfNorm v ≤ c := by
  have hc : 0 ≤ c := by
    have := h 0 (by rw [l1Norm_zero]; norm_num)
    simpa using this
  refine linfNorm_le_of_forall hc fun j => ?_
  -- ℓ₁ norm of a single coordinate sign vector
  have hl1 : ∀ a : ℝ, l1Norm (EuclideanSpace.single j a) = |a| := by
    intro a
    unfold l1Norm
    rw [Finset.sum_eq_single j]
    · rw [PiLp.ofLp_single, Pi.single_eq_same]
    · intro i _ hij
      rw [PiLp.ofLp_single, Pi.single_eq_of_ne hij, abs_zero]
    · intro h'; exact absurd (Finset.mem_univ j) h'
  rcases le_total 0 (v.ofLp j) with hpos | hneg
  · have h1 := h (EuclideanSpace.single j 1) (by rw [hl1]; norm_num)
    rw [inner_single_left_ofLp] at h1
    rw [abs_of_nonneg hpos]; linarith
  · have h1 := h (EuclideanSpace.single j (-1)) (by rw [hl1]; norm_num)
    rw [inner_single_left_ofLp] at h1
    rw [abs_of_nonpos hneg]; linarith

/-- `M(S)ᗮ = M(Sᶜ)`: the orthogonal complement of the `S`-supported subspace is the `Sᶜ`-supported one. -/
lemma suppSubmodule_orthogonal (S : Finset (Fin d)) :
    (suppSubmodule S)ᗮ = suppSubmodule Sᶜ := by
  ext u
  constructor
  · intro hu j hj
    rw [Finset.mem_compl, not_not] at hj
    have hw : EuclideanSpace.single j (1 : ℝ) ∈ suppSubmodule S := by
      intro j' hj'
      have hne : j' ≠ j := by rintro rfl; exact hj' hj
      rw [PiLp.ofLp_single, Pi.single_eq_of_ne hne]
    have hz := (Submodule.mem_orthogonal _ u).1 hu _ hw
    rw [inner_single_left_ofLp] at hz
    simpa using hz
  · intro hu
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hsum : (⟪w, u⟫_ℝ : ℝ) = ∑ i, w.ofLp i * u.ofLp i := by
      simp only [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      change u.ofLp i * w.ofLp i = w.ofLp i * u.ofLp i
      ring
    rw [hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases em (i ∈ S) with hi | hi
    · rw [hu i (by simpa using hi), mul_zero]
    · rw [hw i hi, zero_mul]

/-- **ℓ₁-decomposability** (Wainwright Example 9.10): for `α` supported on `S` and `β` supported on
`Sᶜ` (disjoint supports), `‖α + β‖₁ = ‖α‖₁ + ‖β‖₁`. -/
lemma l1_decomp (S : Finset (Fin d)) (α : EuclideanSpace ℝ (Fin d)) (hα : α ∈ suppSubmodule S)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ∈ (suppSubmodule S)ᗮ) :
    l1Norm (α + β) = l1Norm α + l1Norm β := by
  rw [suppSubmodule_orthogonal] at hβ
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WithLp.ofLp_add, Pi.add_apply]
  by_cases hi : i ∈ S
  · have hβi : β.ofLp i = 0 := hβ i (by simpa using hi)
    rw [hβi, add_zero, abs_zero, add_zero]
  · have hαi : α.ofLp i = 0 := hα i hi
    rw [hαi, zero_add, abs_zero, zero_add]

/-- The **ℓ₁/ℓ∞ decomposable regularizer** with model subspace `M(S)` (`M = M̄`, the ideal case). -/
noncomputable def l1DecomposableReg (S : Finset (Fin d)) :
    DecomposableReg (EuclideanSpace ℝ (Fin d)) where
  M := suppSubmodule S
  Mbar := suppSubmodule S
  subset_Mbar := le_refl _
  Φ := l1Seminorm d
  Φstar := linfSeminorm d
  holder := l1_linf_holder
  tight := linf_tight
  decomp := l1_decomp S

end StatLean.HighDimensionalStatistics.MEstimator
