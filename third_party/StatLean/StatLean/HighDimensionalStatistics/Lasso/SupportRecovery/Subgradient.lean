module
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Defs

@[expose] public section

/-!
# ℓ¹ subdifferential, KKT certificate, and the PDW uniqueness/support lemma

This file assembles the convex-analytic core of the primal–dual-witness (PDW) proof of the
Lasso variable-selection theorem. Write the (penalized least-squares) Lasso objective as
$$ F_\lambda(\theta) \;=\; \tfrac{1}{2n}\,\|Y - X\theta\|_2^2 \;+\; \lambda\,\|\theta\|_1, $$
and let $S$ denote the candidate active set. The results are:

* **Subdifferential characterization of the ℓ¹ norm.** A vector $z$ belongs to the
  subdifferential $\partial\|\theta\|_1$ if and only if it pairs to the norm and is dual-feasible:
  $\langle z,\theta\rangle = \|\theta\|_1$ and $\|z\|_\infty \le 1$.
* **KKT certificate (zero-subgradient condition).** Every Lasso minimizer $\hat\theta$ admits a
  subgradient $z \in \partial\|\hat\theta\|_1$ satisfying the stationarity equation
  $\tfrac{1}{n}X^\top(X\hat\theta - Y) + \lambda z = 0$, and conversely any point with such a
  certificate is a global minimizer (convex sufficiency). A Lasso minimizer exists for every
  $\lambda > 0$ by coercivity of the penalty.
* **Lemma 7.23 (b) — support of every minimizer.** If the PDW pair $(\hat\theta,\hat z)$ satisfies
  the KKT condition with $\hat\theta$ supported on $S$ and *strict* dual feasibility off $S$
  ($|\hat z_j| < 1$ for $j \notin S$), then *every* Lasso minimizer $\tilde\theta$ is supported
  on $S$.
* **Lemma 7.23 (a) — uniqueness.** Under the lower-eigenvalue condition (A3) (a positive
  lower bound $c_{\min} > 0$ on the restricted quadratic form $\|X_S v\|_2^2 / n$), a successful
  PDW construction implies the Lasso has a *unique* optimal solution.

Deviation from the book: the formalized Lemma 7.23 (a)/(b) carry an explicit hypothesis
$\lambda > 0$, which Wainwright assumes implicitly throughout §7.5. Without it the support and
uniqueness claims fail (e.g. $X = 0,\,Y = 0,\,\lambda = 0$ admits unsupported minimizers); see
the per-declaration docstrings.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 7 (Sparse linear models in high dimensions), §7.5.2
(Proof of Theorem 7.21), Lemma 7.23 (a) (uniqueness) and (b) (support), zero-subgradient /
KKT condition Eq (7.48); lower-eigenvalue condition (A3), §7.5.1, Eq (7.43a).

**Proof formalization notes.** The convex-analytic core of the primal–dual-witness proof of
Theorem 7.21 is split as:

* `l1_subgradient_iff` — `z ∈ ∂‖θ‖₁ ↔ (⟪z,θ⟫ = ‖θ‖₁ ∧ ‖z‖_∞ ≤ 1)` (dual pairing form).
* `loss_convex_gradient` — the gradient inequality of the quadratic loss `(1/2n)‖Y−Xθ‖²`.
* `lasso_minimizer_exists` — existence of a Lasso minimizer (coercive extreme-value theorem).
* `kkt_of_isLassoEstimator` — a Lasso minimizer admits a KKT subgradient certificate (7.48).
* `pdw_every_minimizer_supported` — **Lemma 7.23 (b)**: strict dual feasibility ⇒ *every*
  Lasso minimizer is supported on `S`.
* `pdw_unique` — **Lemma 7.23 (a)**: with (A3), the Lasso minimizer is unique.

Matrix-free except `pdw_unique`, whose strict-convexity step uses the (A3) `LowerEigenvalue`
quadratic-form bound on support-difference vectors. Reuses the Hölder bound
`abs_inner_le_l1Norm_mul_linfNorm` (`ForMathlib/VecNorms.lean`).

**Bibliographic comments.** The primal–dual-witness method formalized here originates with
M. J. Wainwright, "Sharp thresholds for high-dimensional and noisy sparsity recovery using
ℓ₁-constrained quadratic programming (Lasso)", *IEEE Transactions on Information Theory*,
vol. 55, no. 5, pp. 2183–2202, 2009, which introduced the PDW construction (and its supporting
lemmas, the analogues of Lemma 7.23) to establish sharp model-selection thresholds for the Lasso.
The subdifferential/KKT machinery is standard convex analysis (the optimality conditions for the
ℓ¹-penalized least-squares program); the book's Lemma 7.23 packages these classical facts in the
form needed for the PDW witness argument.
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-! ## Private convex-analysis helpers (this file only) -/

/-- Real inner product on `EuclideanSpace ℝ (Fin d)` as a coordinate sum. -/
private lemma inner_eq_sum (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, y⟫_ℝ = ∑ i, x.ofLp i * y.ofLp i := by
  simp only [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change y.ofLp i * x.ofLp i = x.ofLp i * y.ofLp i
  ring

/-- `j`-th coordinate as a pairing against the standard basis vector. -/
private lemma coord_eq_inner_single (v : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    ⟪v, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = v.ofLp j := by
  rw [inner_eq_sum, Finset.sum_eq_single j]
  · simp [EuclideanSpace.single, PiLp.single_apply]
  · intro i _ hij
    simp [EuclideanSpace.single, PiLp.single_apply, hij]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- If every coordinate is `≤ 1` in absolute value then `‖z‖_∞ ≤ 1`. -/
private lemma linfNorm_le_one_of_forall {z : EuclideanSpace ℝ (Fin d)}
    (h : ∀ i, |z.ofLp i| ≤ 1) : linfNorm z ≤ 1 := by
  rcases isEmpty_or_nonempty (Fin d) with he | hne
  · haveI := he
    simp only [linfNorm, Real.iSup_of_isEmpty]
    norm_num
  · exact ciSup_le h

/-- `‖x‖₂ ≤ ‖x‖₁`. -/
private lemma norm_le_l1Norm (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ≤ l1Norm x := by
  rw [EuclideanSpace.norm_eq]
  have hsq : ∑ i, ‖x.ofLp i‖ ^ 2 ≤ (∑ i, |x.ofLp i|) ^ 2 := by
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => |x.ofLp i|) (fun i _ => abs_nonneg _)
    simpa [Real.norm_eq_abs, sq_abs] using this
  calc Real.sqrt (∑ i, ‖x.ofLp i‖ ^ 2)
      ≤ Real.sqrt ((∑ i, |x.ofLp i|) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i, |x.ofLp i| := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ = l1Norm x := rfl

/-- ℓ¹ norm of a scalar multiple. -/
private lemma l1Norm_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    l1Norm (c • x) = |c| * l1Norm x := by
  unfold l1Norm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, abs_mul]

/-- Exact quadratic expansion along a perturbation `θ ↦ θ + t • w`. -/
private lemma quad_expand (X : Matrix (Fin n) (Fin d) ℝ) (Y : EuclideanSpace ℝ (Fin n))
    (θ w : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖Y - designMap X (θ + t • w)‖ ^ 2
      = ‖Y - designMap X θ‖ ^ 2 - 2 * t * ⟪Y - designMap X θ, designMap X w⟫_ℝ
        + t ^ 2 * ‖designMap X w‖ ^ 2 := by
  have hstep : Y - designMap X (θ + t • w) = (Y - designMap X θ) - t • designMap X w := by
    rw [map_add, map_smul]; abel
  rw [hstep, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

/-- ℓ¹ norm under a single-coordinate perturbation. -/
private lemma l1_single_perturb (θ : EuclideanSpace ℝ (Fin d)) (j : Fin d) (t : ℝ) :
    l1Norm (θ + t • EuclideanSpace.single j 1)
      = l1Norm θ + (|θ.ofLp j + t| - |θ.ofLp j|) := by
  have hcoord : ∀ i, (θ + t • EuclideanSpace.single j (1 : ℝ)).ofLp i
      = θ.ofLp i + t * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 2
    simp [EuclideanSpace.single, PiLp.single_apply]
  have hdiff : (∑ i, |(θ + t • EuclideanSpace.single j (1 : ℝ)).ofLp i|)
      - ∑ i, |θ.ofLp i| = |θ.ofLp j + t| - |θ.ofLp j| := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [hcoord j]; simp
    · intro i _ hij; rw [hcoord i]; simp [hij]
    · intro h; exact absurd (Finset.mem_univ j) h
  unfold l1Norm
  linarith [hdiff]

/-- One-sided second-order test: if `0 ≤ t·b + t²·K` for all small `t > 0`, then `0 ≤ b`. -/
private lemma small_pos_imp_nonneg (b K : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (H : ∀ t, 0 < t → t < δ → 0 ≤ t * b + t ^ 2 * K) : 0 ≤ b := by
  by_contra hb
  push_neg at hb
  have hden : 0 < |K| + 1 := by positivity
  have ht0 : 0 < min (δ / 2) ((-b) / (|K| + 1)) :=
    lt_min (by linarith) (div_pos (by linarith) hden)
  set t := min (δ / 2) ((-b) / (|K| + 1)) with htdef
  have htlt : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htb : t ≤ (-b) / (|K| + 1) := min_le_right _ _
  have hmul : t * (|K| + 1) ≤ -b := by rw [le_div_iff₀ hden] at htb; linarith
  have hkle : t * K ≤ t * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) ht0.le
  have hlt : b + t * K < 0 := by nlinarith [hmul, hkle, ht0]
  have hH := H t ht0 htlt
  nlinarith [mul_pos ht0 (neg_pos.mpr hlt), hH]

/-! ## Subgradient and convexity lemmas -/

/-- `⟪z,θ⟫ ≤ ‖θ‖₁` whenever `‖z‖_∞ ≤ 1` (Hölder ℓ¹–ℓ∞). -/
theorem inner_le_l1Norm_of_linfNorm_le_one (z θ : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: ‖z‖_∞ ≤ 1 (dual-feasible certificate); Wainwright §7.5.2
    (hz : linfNorm z ≤ 1) :
    ⟪z, θ⟫_ℝ ≤ l1Norm θ := by
  calc ⟪z, θ⟫_ℝ ≤ |⟪z, θ⟫_ℝ| := le_abs_self _
    _ = |⟪θ, z⟫_ℝ| := by rw [real_inner_comm]
    _ ≤ l1Norm θ * linfNorm z := abs_inner_le_l1Norm_mul_linfNorm θ z
    _ ≤ l1Norm θ * 1 := mul_le_mul_of_nonneg_left hz (l1Norm_nonneg θ)
    _ = l1Norm θ := mul_one _

/-- **Dual-pairing characterization of `∂‖·‖₁`** (Wainwright §7.5.2):
`z ∈ ∂‖θ‖₁ ↔ ⟪z,θ⟫ = ‖θ‖₁ ∧ ‖z‖_∞ ≤ 1`. -/
theorem l1_subgradient_iff (z θ : EuclideanSpace ℝ (Fin d)) :
    IsL1Subgradient z θ ↔ (⟪z, θ⟫_ℝ = l1Norm θ ∧ linfNorm z ≤ 1) := by
  constructor
  · intro hsub
    refine ⟨?_, linfNorm_le_one_of_forall (fun i => (hsub i).2.2)⟩
    rw [inner_eq_sum]
    unfold l1Norm
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases lt_trichotomy (θ.ofLp i) 0 with h | h | h
    · rw [(hsub i).2.1 h, abs_of_neg h]; ring
    · rw [h]; simp
    · rw [(hsub i).1 h, abs_of_pos h]; ring
  · rintro ⟨hpair, hlinf⟩
    have habs : ∀ i, |z.ofLp i| ≤ 1 := fun i => (abs_le_linfNorm z i).trans hlinf
    have hterm_nonneg : ∀ i ∈ Finset.univ,
        0 ≤ |θ.ofLp i| - z.ofLp i * θ.ofLp i := by
      intro i _
      have hle : z.ofLp i * θ.ofLp i ≤ |θ.ofLp i| := by
        calc z.ofLp i * θ.ofLp i ≤ |z.ofLp i * θ.ofLp i| := le_abs_self _
          _ = |z.ofLp i| * |θ.ofLp i| := abs_mul _ _
          _ ≤ 1 * |θ.ofLp i| := mul_le_mul_of_nonneg_right (habs i) (abs_nonneg _)
          _ = |θ.ofLp i| := one_mul _
      linarith
    have hsum0 : ∑ i, (|θ.ofLp i| - z.ofLp i * θ.ofLp i) = 0 := by
      rw [Finset.sum_sub_distrib]
      have he2 : ∑ i, z.ofLp i * θ.ofLp i = ⟪z, θ⟫_ℝ := (inner_eq_sum z θ).symm
      rw [he2, hpair]; simp [l1Norm]
    have key : ∀ i, z.ofLp i * θ.ofLp i = |θ.ofLp i| := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum0 i (Finset.mem_univ i)
      linarith
    intro i
    refine ⟨?_, ?_, habs i⟩
    · intro hpos
      have hk := key i
      rw [abs_of_pos hpos] at hk
      have heq : z.ofLp i * θ.ofLp i = 1 * θ.ofLp i := by rw [one_mul]; exact hk
      exact mul_right_cancel₀ (ne_of_gt hpos) heq
    · intro hneg
      have hk := key i
      rw [abs_of_neg hneg] at hk
      have heq : z.ofLp i * θ.ofLp i = (-1) * θ.ofLp i := by rw [neg_one_mul]; exact hk
      exact mul_right_cancel₀ (ne_of_lt hneg) heq

/-- **Gradient inequality of the quadratic loss** `F(θ) = (1/2n)‖Y − Xθ‖²` (convexity):
`F(θ') ≥ F(θ) + ⟪∇F(θ), θ' − θ⟫` with `∇F(θ) = (1/n) Xᵀ(Xθ − Y)`. -/
theorem loss_convex_gradient (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (θ θ' : EuclideanSpace ℝ (Fin d)) :
    (1 / (2 * (n : ℝ))) * ‖Y - designMap X θ‖ ^ 2
        + ⟪(1 / (n : ℝ)) • designMap Xᵀ (designMap X θ - Y), θ' - θ⟫_ℝ
      ≤ (1 / (2 * (n : ℝ))) * ‖Y - designMap X θ'‖ ^ 2 := by
  have hnorm : ‖Y - designMap X θ'‖ ^ 2
      = ‖Y - designMap X θ‖ ^ 2
        - 2 * 1 * ⟪Y - designMap X θ, designMap X (θ' - θ)⟫_ℝ
        + 1 ^ 2 * ‖designMap X (θ' - θ)‖ ^ 2 := by
    have := quad_expand X Y θ (θ' - θ) 1
    simp only [one_smul] at this
    rw [show θ + (θ' - θ) = θ' from by abel] at this
    rw [this]
  have hwh : ⟪designMap Xᵀ (designMap X θ - Y), θ' - θ⟫_ℝ
      = -⟪Y - designMap X θ, designMap X (θ' - θ)⟫_ℝ := by
    rw [real_inner_comm, ← inner_designMap_transpose X (θ' - θ) (designMap X θ - Y)]
    rw [show designMap X θ - Y = -(Y - designMap X θ) from by abel]
    rw [inner_neg_right, real_inner_comm]
  rw [real_inner_smul_left, hwh]
  have hsq : 0 ≤ ‖designMap X (θ' - θ)‖ ^ 2 := sq_nonneg _
  have hn0 : 0 ≤ 1 / (2 * (n : ℝ)) := by positivity
  rw [hnorm]
  have key : (1 / (2 * (n : ℝ))) * (2 * 1 * ⟪Y - designMap X θ, designMap X (θ' - θ)⟫_ℝ)
      = (1 / (n : ℝ)) * ⟪Y - designMap X θ, designMap X (θ' - θ)⟫_ℝ := by
    rcases eq_or_ne (n : ℝ) 0 with h | h
    · rw [h]; simp
    · field_simp
  nlinarith [mul_nonneg hn0 hsq, key]

/-- **Existence of a Lasso minimizer** (coercive extreme-value theorem,
`Continuous.exists_forall_le'`): for `λ > 0` the Lasso objective attains its minimum. -/
theorem lasso_minimizer_exists (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    -- USER-INPUT: λ > 0 (coercivity of the ℓ¹ penalty); Wainwright §7.5.2
    (hlam : 0 < lam) :
    ∃ βhat, IsLassoEstimator X Y lam βhat := by
  have hcontMap : Continuous (fun β : EuclideanSpace ℝ (Fin d) => designMap X β) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcontCoord : ∀ i, Continuous (fun β : EuclideanSpace ℝ (Fin d) => β.ofLp i) :=
    fun i => (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hcont : Continuous (lassoObjective X Y lam) := by
    unfold lassoObjective l1Norm
    refine Continuous.add (Continuous.mul continuous_const ?_)
      (Continuous.mul continuous_const ?_)
    · exact ((continuous_const.sub hcontMap).norm).pow 2
    · exact continuous_finset_sum _ fun i _ => (hcontCoord i).abs
  have hbdd : Bornology.IsBounded
      {β : EuclideanSpace ℝ (Fin d) | lassoObjective X Y lam β ≤ lassoObjective X Y lam 0} := by
    apply Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d)))
        (r := lassoObjective X Y lam 0 / lam))
    intro β hβ
    simp only [Set.mem_setOf_eq] at hβ
    rw [Metric.mem_closedBall, dist_zero_right]
    have hq : 0 ≤ (1 / (2 * (n : ℝ))) * ‖Y - designMap X β‖ ^ 2 := by positivity
    have h1 : lam * l1Norm β ≤ lassoObjective X Y lam 0 := by
      have hle : lam * l1Norm β ≤ lassoObjective X Y lam β := by
        unfold lassoObjective; linarith [hq]
      linarith [hle, hβ]
    have h2 : l1Norm β ≤ lassoObjective X Y lam 0 / lam := by
      rw [le_div_iff₀ hlam, mul_comm]; exact h1
    exact le_trans (norm_le_l1Norm β) h2
  obtain ⟨βhat, hβ⟩ := hcont.exists_forall_le_of_isBounded 0 hbdd
  exact ⟨βhat, hβ⟩

/-- **KKT certificate of a Lasso minimizer** (Wainwright 7.48): an optimal `θ̂` admits a
subgradient `z ∈ ∂‖θ̂‖₁` with `(1/n) Xᵀ(X θ̂ − Y) + λ z = 0`. -/
theorem kkt_of_isLassoEstimator (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (θhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < n; Wainwright §7.5.2
    (hn : 0 < n)
    -- USER-INPUT: θ̂ minimises the Lasso objective; Wainwright §7.5.2
    (hopt : IsLassoEstimator X Y lam θhat) :
    ∃ z, IsL1Subgradient z θhat ∧ IsKKT X Y lam θhat z := by
  set grad := (1 / (n : ℝ)) • designMap Xᵀ (designMap X θhat - Y) with hgrad_def
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Coordinate of the gradient as an inner product.
  have hgrad_coord : ∀ j, grad.ofLp j
      = -(1 / (n : ℝ)) * ⟪Y - designMap X θhat, designMap X (EuclideanSpace.single j 1)⟫_ℝ := by
    intro j
    rw [hgrad_def, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← coord_eq_inner_single,
      real_inner_comm, ← inner_designMap_transpose X (EuclideanSpace.single j 1)
        (designMap X θhat - Y),
      show designMap X θhat - Y = -(Y - designMap X θhat) from by abel, inner_neg_right,
      ← real_inner_comm (designMap X (EuclideanSpace.single j 1)) (Y - designMap X θhat)]
    ring
  -- Per-coordinate optimality ⇒ sign facts.
  have hP : ∀ j, (0 < θhat.ofLp j → grad.ofLp j = -lam)
      ∧ (θhat.ofLp j < 0 → grad.ofLp j = lam)
      ∧ (θhat.ofLp j = 0 → |grad.ofLp j| ≤ lam) := by
    intro j
    have rawopt : ∀ t : ℝ, 0 ≤ t * grad.ofLp j
        + t ^ 2 * (‖designMap X (EuclideanSpace.single j 1)‖ ^ 2 / (2 * (n : ℝ)))
        + lam * (|θhat.ofLp j + t| - |θhat.ofLp j|) := by
      intro t
      have hopt' := hopt (θhat + t • EuclideanSpace.single j 1)
      have hexp : lassoObjective X Y lam (θhat + t • EuclideanSpace.single j 1)
          = lassoObjective X Y lam θhat
            + (t * grad.ofLp j
                + t ^ 2 * (‖designMap X (EuclideanSpace.single j 1)‖ ^ 2 / (2 * (n : ℝ))))
            + lam * (|θhat.ofLp j + t| - |θhat.ofLp j|) := by
        unfold lassoObjective
        rw [l1_single_perturb, quad_expand, hgrad_coord j]
        field_simp
        ring
      rw [hexp] at hopt'
      linarith [hopt']
    set a := θhat.ofLp j with ha
    set K := ‖designMap X (EuclideanSpace.single j 1)‖ ^ 2 / (2 * (n : ℝ)) with hK
    have hKnn : 0 ≤ K := by rw [hK]; positivity
    refine ⟨?_, ?_, ?_⟩
    · intro hpos
      have h1 : 0 ≤ grad.ofLp j + lam := by
        refine small_pos_imp_nonneg (grad.ofLp j + lam) K hpos (fun t ht htδ => ?_)
        have hr := rawopt t
        have habst : |a + t| - |a| = t := by
          rw [abs_of_pos (by linarith : (0:ℝ) < a + t), abs_of_pos hpos]; ring
        rw [habst] at hr; nlinarith [hr]
      have h2 : 0 ≤ -(grad.ofLp j + lam) := by
        refine small_pos_imp_nonneg (-(grad.ofLp j + lam)) K hpos (fun t ht htδ => ?_)
        have hr := rawopt (-t)
        have habst : |a + (-t)| - |a| = -t := by
          rw [abs_of_pos (by linarith : (0:ℝ) < a + (-t)), abs_of_pos hpos]; ring
        rw [habst] at hr; nlinarith [hr]
      linarith
    · intro hneg
      have h1 : 0 ≤ grad.ofLp j - lam := by
        refine small_pos_imp_nonneg (grad.ofLp j - lam) K (neg_pos.mpr hneg)
          (fun t ht htδ => ?_)
        have hr := rawopt t
        have habst : |a + t| - |a| = -t := by
          rw [abs_of_neg (by linarith : a + t < 0), abs_of_neg hneg]; ring
        rw [habst] at hr; nlinarith [hr]
      have h2 : 0 ≤ -(grad.ofLp j - lam) := by
        refine small_pos_imp_nonneg (-(grad.ofLp j - lam)) K (neg_pos.mpr hneg)
          (fun t ht htδ => ?_)
        have hr := rawopt (-t)
        have habst : |a + (-t)| - |a| = t := by
          rw [abs_of_neg (by linarith : a + (-t) < 0), abs_of_neg hneg]; ring
        rw [habst] at hr; nlinarith [hr]
      linarith
    · intro hzero
      have h1 : 0 ≤ grad.ofLp j + lam := by
        refine small_pos_imp_nonneg (grad.ofLp j + lam) K one_pos (fun t ht htδ => ?_)
        have hr := rawopt t
        have habst : |a + t| - |a| = t := by
          rw [hzero]; simp [abs_of_pos ht]
        rw [habst] at hr; nlinarith [hr]
      have h2 : 0 ≤ lam - grad.ofLp j := by
        refine small_pos_imp_nonneg (lam - grad.ofLp j) K one_pos (fun t ht htδ => ?_)
        have hr := rawopt (-t)
        have habst : |a + (-t)| - |a| = t := by
          rw [hzero]; simp [abs_neg, abs_of_pos ht]
        rw [habst] at hr; nlinarith [hr]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- Build the certificate.
  refine ⟨WithLp.toLp 2 (fun j => if 0 < θhat.ofLp j then (1 : ℝ)
      else if θhat.ofLp j < 0 then -1 else -(grad.ofLp j) / lam), ?_, ?_⟩
  · intro i
    simp only [WithLp.ofLp_toLp]
    refine ⟨?_, ?_, ?_⟩
    · intro hpos; rw [if_pos hpos]
    · intro hneg; rw [if_neg (by linarith), if_pos hneg]
    split_ifs with h1 h2
    · norm_num
    · norm_num
    · have hzero : θhat.ofLp i = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      have hP0 := (hP i).2.2 hzero
      rcases eq_or_ne lam 0 with hl | hl
      · rw [hl]; simp
      · rw [abs_div, abs_neg, div_le_one (abs_pos.mpr hl)]
        have hlpos : 0 < lam := by
          rcases lt_trichotomy lam 0 with h | h | h
          · exact absurd (le_trans (abs_nonneg _) hP0) (not_le.mpr h)
          · exact absurd h hl
          · exact h
        rw [abs_of_pos hlpos]; exact hP0
  · show grad + lam • _ = 0
    apply WithLp.ofLp_injective 2
    funext j
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      WithLp.ofLp_zero, Pi.zero_apply, WithLp.ofLp_toLp]
    by_cases hpos : 0 < θhat.ofLp j
    · rw [if_pos hpos, (hP j).1 hpos]; ring
    · by_cases hneg : θhat.ofLp j < 0
      · rw [if_neg hpos, if_pos hneg, (hP j).2.1 hneg]; ring
      · rw [if_neg hpos, if_neg hneg]
        have hzero : θhat.ofLp j = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        have hP0 := (hP j).2.2 hzero
        rcases eq_or_ne lam 0 with hl | hl
        · have hgz : grad.ofLp j = 0 := abs_eq_zero.mp (le_antisymm (hl ▸ hP0) (abs_nonneg _))
          rw [hl, hgz]; ring
        · have hcancel : lam * (-(grad.ofLp j) / lam) = -(grad.ofLp j) := by
            field_simp
          rw [hcancel]; ring

/-- **KKT ⇒ global optimum** (convex sufficiency, converse of `kkt_of_isLassoEstimator`): a
point with a KKT subgradient certificate minimizes the Lasso objective. Used to identify the
primal–dual witness as the (unique) Lasso minimizer. -/
theorem lassoEstimator_of_kkt (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (θ z : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < n; Wainwright §7.5.2
    (hn : 0 < n)
    -- USER-INPUT: 0 < λ; Wainwright §7.5.2
    (hlam : 0 < lam)
    -- USER-INPUT: z ∈ ∂‖θ‖₁; Wainwright §7.5.2
    (hsub : IsL1Subgradient z θ)
    -- USER-INPUT: KKT (7.48) holds for (θ, z); Wainwright §7.5.2
    (hkkt : IsKKT X Y lam θ z) :
    IsLassoEstimator X Y lam θ := by
  intro β
  have hpair : ⟪z, θ⟫_ℝ = l1Norm θ := ((l1_subgradient_iff z θ).mp hsub).1
  have hlinf : linfNorm z ≤ 1 := ((l1_subgradient_iff z θ).mp hsub).2
  have hβ : ⟪z, β⟫_ℝ ≤ l1Norm β := inner_le_l1Norm_of_linfNorm_le_one z β hlinf
  have hg : (1 / (n : ℝ)) • designMap Xᵀ (designMap X θ - Y) = -(lam • z) :=
    eq_neg_of_add_eq_zero_left hkkt
  have hinner : ⟪(1 / (n : ℝ)) • designMap Xᵀ (designMap X θ - Y), β - θ⟫_ℝ
      = -lam * (⟪z, β⟫_ℝ - ⟪z, θ⟫_ℝ) := by
    rw [hg, inner_neg_left, real_inner_smul_left, inner_sub_right]; ring
  have hquad := loss_convex_gradient X Y θ β
  rw [hinner] at hquad
  unfold lassoObjective
  have h1 : lam * (⟪z, β⟫_ℝ - ⟪z, θ⟫_ℝ) + lam * l1Norm θ ≤ lam * l1Norm β := by
    rw [hpair]
    have hm : lam * ⟪z, β⟫_ℝ ≤ lam * l1Norm β := mul_le_mul_of_nonneg_left hβ hlam.le
    nlinarith [hm]
  linarith [hquad, h1]

/-- **Lemma 7.23 (b)** (Wainwright §7.5.2): if the primal–dual witness `(θ̂, ẑ)` satisfies
the KKT condition with `θ̂` supported on `S` and *strict* dual feasibility off `S`
(`|ẑ_j| < 1` for `j ∉ S`), then **every** Lasso minimizer `θ̃` is supported on `S`.

Note (deviation from stub): a `0 < lam` hypothesis is required and was added — without it the
statement is false (e.g. `X = 0, Y = 0, lam = 0, θ̂ = ẑ = 0` satisfies every other hypothesis
but admits unsupported minimizers). Wainwright's Lemma 7.23 assumes `λ > 0` throughout. -/
theorem pdw_every_minimizer_supported (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin d)) (lam : ℝ)
    (θhat zhat θtil : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < λ (required for Lemma 7.23 — see docstring); Wainwright §7.5.2
    (hlam : 0 < lam)
    -- USER-INPUT: 0 < n; Wainwright §7.5.2
    (hn : 0 < n)
    -- USER-INPUT: witness θ̂ supported on S; Wainwright §7.5.2 (PDW step 1)
    (hsupp : ∀ j ∉ S, θhat.ofLp j = 0)
    -- USER-INPUT: ẑ ∈ ∂‖θ̂‖₁; Wainwright §7.5.2
    (hsub : IsL1Subgradient zhat θhat)
    -- USER-INPUT: KKT (7.48) holds for (θ̂, ẑ); Wainwright §7.5.2
    (hkkt : IsKKT X Y lam θhat zhat)
    -- USER-INPUT: strict dual feasibility |ẑ_j| < 1 for j ∉ S; Wainwright §7.5.2 (PDW step 3)
    (hstrict : ∀ j ∉ S, |zhat.ofLp j| < 1)
    -- USER-INPUT: θ̃ is any Lasso minimizer; Wainwright §7.5.2 (Lemma 7.23)
    (hopt : IsLassoEstimator X Y lam θtil) :
    ∀ j ∉ S, θtil.ofLp j = 0 := by
  intro j hj
  have hpair : ⟪zhat, θhat⟫_ℝ = l1Norm θhat := ((l1_subgradient_iff zhat θhat).mp hsub).1
  have hlinf : linfNorm zhat ≤ 1 := ((l1_subgradient_iff zhat θhat).mp hsub).2
  have hg : (1 / (n : ℝ)) • designMap Xᵀ (designMap X θhat - Y) = -(lam • zhat) :=
    eq_neg_of_add_eq_zero_left hkkt
  have hinner : ⟪(1 / (n : ℝ)) • designMap Xᵀ (designMap X θhat - Y), θtil - θhat⟫_ℝ
      = -lam * (⟪zhat, θtil⟫_ℝ - ⟪zhat, θhat⟫_ℝ) := by
    rw [hg, inner_neg_left, real_inner_smul_left, inner_sub_right]; ring
  have hconv := loss_convex_gradient X Y θhat θtil
  rw [hinner, hpair] at hconv
  have hoptle := hopt θhat
  unfold lassoObjective at hoptle
  have hkey : lam * l1Norm θtil ≤ lam * ⟪zhat, θtil⟫_ℝ := by nlinarith [hconv, hoptle]
  have hle : l1Norm θtil ≤ ⟪zhat, θtil⟫_ℝ := le_of_mul_le_mul_left hkey hlam
  have hge : ⟪zhat, θtil⟫_ℝ ≤ l1Norm θtil := inner_le_l1Norm_of_linfNorm_le_one zhat θtil hlinf
  have heq : ⟪zhat, θtil⟫_ℝ = l1Norm θtil := le_antisymm hge hle
  -- per-coordinate: zhat_k · θtil_k = |θtil_k| for all k
  have habs : ∀ k, |zhat.ofLp k| ≤ 1 := fun k => (abs_le_linfNorm zhat k).trans hlinf
  have hterm_nonneg : ∀ k ∈ Finset.univ,
      0 ≤ |θtil.ofLp k| - zhat.ofLp k * θtil.ofLp k := by
    intro k _
    have hle' : zhat.ofLp k * θtil.ofLp k ≤ |θtil.ofLp k| := by
      calc zhat.ofLp k * θtil.ofLp k ≤ |zhat.ofLp k * θtil.ofLp k| := le_abs_self _
        _ = |zhat.ofLp k| * |θtil.ofLp k| := abs_mul _ _
        _ ≤ 1 * |θtil.ofLp k| := mul_le_mul_of_nonneg_right (habs k) (abs_nonneg _)
        _ = |θtil.ofLp k| := one_mul _
    linarith
  have hsum0 : ∑ k, (|θtil.ofLp k| - zhat.ofLp k * θtil.ofLp k) = 0 := by
    rw [Finset.sum_sub_distrib]
    have he2 : ∑ k, zhat.ofLp k * θtil.ofLp k = ⟪zhat, θtil⟫_ℝ := (inner_eq_sum zhat θtil).symm
    rw [he2, heq]; simp [l1Norm]
  have hkey2 : zhat.ofLp j * θtil.ofLp j = |θtil.ofLp j| := by
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum0 j (Finset.mem_univ j)
    linarith
  by_contra hne
  have hpos : 0 < |θtil.ofLp j| := abs_pos.mpr hne
  have hstrictj := hstrict j hj
  have hcontra : |zhat.ofLp j * θtil.ofLp j| < |θtil.ofLp j| := by
    rw [abs_mul]
    calc |zhat.ofLp j| * |θtil.ofLp j| < 1 * |θtil.ofLp j| :=
          mul_lt_mul_of_pos_right hstrictj hpos
      _ = |θtil.ofLp j| := one_mul _
  rw [hkey2, abs_of_nonneg (abs_nonneg _)] at hcontra
  exact lt_irrefl _ hcontra

/-- **Lemma 7.23 (a)** (Wainwright §7.5.2): under the lower-eigenvalue condition (A3), a
successful primal–dual witness implies the Lasso has a **unique** optimal solution.

Note (deviation from stub): a `0 < lam` hypothesis is required and was added — existence of a
minimizer needs coercivity (`lasso_minimizer_exists`) and the support step needs Lemma 7.23(b),
both of which require `λ > 0`. Wainwright's Lemma 7.23 assumes `λ > 0`. -/
theorem pdw_unique (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin d)) (lam cmin : ℝ)
    (θhat zhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < λ (required for Lemma 7.23 — see docstring); Wainwright §7.5.2
    (hlam : 0 < lam)
    -- USER-INPUT: 0 < n; Wainwright §7.5.2
    (hn : 0 < n)
    -- USER-INPUT: witness θ̂ supported on S; Wainwright §7.5.2
    (hsupp : ∀ j ∉ S, θhat.ofLp j = 0)
    -- USER-INPUT: ẑ ∈ ∂‖θ̂‖₁; Wainwright §7.5.2
    (hsub : IsL1Subgradient zhat θhat)
    -- USER-INPUT: KKT (7.48) holds; Wainwright §7.5.2
    (hkkt : IsKKT X Y lam θhat zhat)
    -- USER-INPUT: strict dual feasibility; Wainwright §7.5.2
    (hstrict : ∀ j ∉ S, |zhat.ofLp j| < 1)
    -- USER-INPUT: lower-eigenvalue condition (A3); Wainwright §7.5.1 (7.43a)
    (hA3 : LowerEigenvalue X S cmin)
    -- USER-INPUT: 0 < cmin; Wainwright §7.5.1 (7.43a)
    (hcmin : 0 < cmin) :
    ∃! βhat, IsLassoEstimator X Y lam βhat := by
  obtain ⟨β0, hβ0⟩ := lasso_minimizer_exists X Y lam hlam
  refine ⟨β0, hβ0, ?_⟩
  intro β1 hβ1
  have hsupp0 : ∀ k ∉ S, β0.ofLp k = 0 :=
    pdw_every_minimizer_supported X Y S lam θhat zhat β0 hlam hn hsupp hsub hkkt hstrict hβ0
  have hsupp1 : ∀ k ∉ S, β1.ofLp k = 0 :=
    pdw_every_minimizer_supported X Y S lam θhat zhat β1 hlam hn hsupp hsub hkkt hstrict hβ1
  have hobj : lassoObjective X Y lam β0 = lassoObjective X Y lam β1 :=
    le_antisymm (hβ0 β1) (hβ1 β0)
  set Δ := β0 - β1 with hΔ_def
  set m := (2⁻¹ : ℝ) • (β0 + β1) with hm_def
  -- exact midpoint quadratic identity (parallelogram law)
  have hXm : designMap X m = (2⁻¹ : ℝ) • (designMap X β0 + designMap X β1) := by
    rw [hm_def, map_smul, map_add]
  have hm_eq : Y - designMap X m
      = (2⁻¹ : ℝ) • ((Y - designMap X β0) + (Y - designMap X β1)) := by
    rw [hXm]; module
  have hXΔ : designMap X Δ = (Y - designMap X β1) - (Y - designMap X β0) := by
    rw [hΔ_def, map_sub]; abel
  have key : ‖Y - designMap X m‖ ^ 2
      = (1 / 2) * ‖Y - designMap X β0‖ ^ 2 + (1 / 2) * ‖Y - designMap X β1‖ ^ 2
        - (1 / 4) * ‖designMap X Δ‖ ^ 2 := by
    rw [hm_eq, norm_smul, mul_pow, hXΔ, norm_add_sq_real (Y - designMap X β0) (Y - designMap X β1),
      norm_sub_sq_real (Y - designMap X β1) (Y - designMap X β0),
      real_inner_comm (Y - designMap X β1) (Y - designMap X β0), Real.norm_eq_abs,
      sq_abs]
    ring
  have hquad_mid : (1 / (2 * (n : ℝ))) * ‖Y - designMap X m‖ ^ 2
      = (1 / 2) * ((1 / (2 * (n : ℝ))) * ‖Y - designMap X β0‖ ^ 2)
        + (1 / 2) * ((1 / (2 * (n : ℝ))) * ‖Y - designMap X β1‖ ^ 2)
        - (1 / (8 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2 := by
    rw [key]; ring
  -- midpoint objective inequality
  have hl1mid : l1Norm m ≤ (1 / 2) * l1Norm β0 + (1 / 2) * l1Norm β1 := by
    rw [hm_def, l1Norm_smul, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
    have := l1Norm_add_le β0 β1
    nlinarith [this]
  have hmid : lassoObjective X Y lam m
      ≤ (1 / 2) * lassoObjective X Y lam β0 + (1 / 2) * lassoObjective X Y lam β1
        - (1 / (8 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2 := by
    unfold lassoObjective
    rw [hquad_mid]
    have hl1 : lam * l1Norm m ≤ lam * ((1 / 2) * l1Norm β0 + (1 / 2) * l1Norm β1) :=
      mul_le_mul_of_nonneg_left hl1mid hlam.le
    nlinarith [hl1]
  -- minimum bound on the midpoint
  have hmin : lassoObjective X Y lam β0 ≤ lassoObjective X Y lam m := hβ0 m
  have h8 : (0 : ℝ) < 1 / (8 * (n : ℝ)) := by positivity
  have hbound : (1 / (8 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2 ≤ 0 := by nlinarith [hmid, hmin, hobj]
  have hsq0 : ‖designMap X Δ‖ ^ 2 ≤ 0 := by
    by_contra h; push_neg at h; nlinarith [mul_pos h8 h, hbound]
  have hsqz : ‖designMap X Δ‖ ^ 2 = 0 := le_antisymm hsq0 (sq_nonneg _)
  have hXΔ_zero : designMap X Δ = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hsqz)
  -- Δ supported on S, then (A3) forces Δ = 0
  have hΔsupp : ∀ k ∉ S, Δ.ofLp k = 0 := by
    intro k hk
    rw [hΔ_def]
    simp only [WithLp.ofLp_sub, Pi.sub_apply]
    rw [hsupp0 k hk, hsupp1 k hk]; ring
  set v := WithLp.toLp 2 (fun i : {x // x ∈ S} => Δ.ofLp i.val) with hv
  have hdS : designSub X S v = 0 := by
    rw [hv, ← designMap_restrict_eq_designSub, restrict_eq_self S Δ hΔsupp, hXΔ_zero]
  have hA3v := hA3 v
  rw [hdS, norm_zero] at hA3v
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hA3v
  have hvnorm : ‖v‖ ^ 2 = 0 := le_antisymm (by nlinarith [hA3v, hcmin, sq_nonneg ‖v‖]) (sq_nonneg _)
  have hvz : v = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hvnorm)
  have hvfun : ∀ i : {x // x ∈ S}, Δ.ofLp i.val = 0 := by
    intro i
    have h0 : v.ofLp i = 0 := by rw [hvz]; simp
    rwa [hv, WithLp.ofLp_toLp] at h0
  have hΔ0 : Δ = 0 := by
    apply WithLp.ofLp_injective 2
    funext k
    simp only [WithLp.ofLp_zero, Pi.zero_apply]
    by_cases hk : k ∈ S
    · exact hvfun ⟨k, hk⟩
    · exact hΔsupp k hk
  have hsub0 : β0 - β1 = 0 := by rw [← hΔ_def]; exact hΔ0
  exact (sub_eq_zero.mp hsub0).symm

end StatLean.HighDimensionalStatistics
