module
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Defs
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Subgradient

@[expose] public section

/-!
# Primal–dual witness construction, strict dual feasibility, and the ℓ∞ error bound

This file proves the deterministic core of Lasso variable-selection consistency: the
**primal–dual witness (PDW)** construction together with **strict dual feasibility** and the
**ℓ∞ error bound** on the support.

Consider the Lagrangian Lasso estimator
$$ \hat\theta \;\in\; \arg\min_{\theta\in\mathbb{R}^d}\;
   \Bigl\{ \tfrac{1}{2n}\,\lVert Y - X\theta\rVert_2^2 \;+\; \lambda\,\lVert\theta\rVert_1 \Bigr\}, $$
with response $Y = X\theta^\* + w$, where the true parameter $\theta^\*$ is supported on a
subset $S \subseteq \{1,\dots,d\}$ (i.e. $\theta^\*_j = 0$ for $j \notin S$). Assume:

* **(A3) Lower eigenvalue.** The sub-Gram matrix satisfies a restricted lower-eigenvalue
  bound with constant $c_{\min} > 0$ on $S$.
* **(A4) Mutual incoherence.** With parameter $\alpha \in [0,1)$,
  $\max_{j\notin S} \bigl\lVert (X_S^\top X_S)^{-1} X_S^\top X_j \bigr\rVert_1 \le \alpha$.
* **Regularization condition (7.44).**
  $\lambda \;\ge\; \dfrac{2}{1-\alpha}\,
   \bigl\lVert \tfrac{1}{n}\, X_{S^c}^\top\, \Pi_{S^\perp}(X)\, w \bigr\rVert_\infty$,
  where $\Pi_{S^\perp}(X)$ is the orthogonal projection onto the complement of the column
  space of $X_S$.

Then there exists a primal–dual witness pair $(\hat\theta, \hat z)$ such that:

1. $\hat\theta$ is **supported on $S$**: $\hat\theta_j = 0$ for all $j \notin S$;
2. $\hat z$ is a **subgradient of $\lVert\,\cdot\,\rVert_1$ at $\hat\theta$**, and the pair
   $(\hat\theta, \hat z)$ satisfies the Lasso zero-subgradient (KKT) optimality condition;
3. **strict dual feasibility**: $|\hat z_j| < 1$ for every $j \notin S$;
4. the **ℓ∞ error bound** on the support,
   $$ \bigl\lVert \hat\theta_S - \theta^\*_S \bigr\rVert_\infty
      \;\le\; B(\lambda; X)
      \;:=\; \bigl\lVert (\tfrac{1}{n}X_S^\top X_S)^{-1}\,\tfrac{1}{n}X_S^\top w
              \bigr\rVert_\infty
        \;+\; \lambda\,\bigl\lVert\!\lvert (\tfrac{1}{n}X_S^\top X_S)^{-1}
              \bigr\rvert\!\bigr\rVert_\infty , $$
   where $\lVert\!\lvert\,\cdot\,\rvert\!\rVert_\infty$ is the matrix $\ell_\infty$ operator
   norm.

Strict feasibility (item 3) follows from the block bound $\alpha + \tfrac{1}{2}(1-\alpha) < 1$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 7 (Sparse linear models in high dimensions),
§7.5.2 (Analysis under mutual incoherence), Theorem 7.21. Equations: PDW equations
(7.52)–(7.54), the ℓ∞ bound (7.45), and the regularization condition (7.44).

**Proof formalization notes.**
`pdw_witness_exists` bundles, under conditions (A3),(A4) and the regularization condition
(7.44), the witness consumed by `Subgradient.lean`'s Lemma 7.23:
* `θ̂` supported on `S` (PDW steps 1–2: zero off `S`, oracle solve on `S`);
* `ẑ ∈ ∂‖θ̂‖₁` with the KKT condition (7.48);
* **strict dual feasibility** `|ẑ_j| < 1` for `j ∉ S` (= `½(1+α) < 1`), from the block
  decomposition `ẑ_{Sᶜ} = μ + V_{Sᶜ}` (7.53), `‖μ‖_∞ ≤ α` (incoherence + Hölder) and
  `‖V_{Sᶜ}‖_∞ ≤ ½(1−α)` (choice of λ);
* the **ℓ∞ bound** `‖θ̂_S − θ*_S‖_∞ ≤ B(λ;X)` (7.54 / 7.45).

Internal proof roadmap (named `private` lemmas / `have`s, see cluster prompt):
`theta_diff_eq` (7.52), `zSc_eq` (7.53), `incoherence_bound`, `noise_bound`,
`strict_dual_feasibility`, `linf_error_bound`. Uses the Gram/inverse/projection bounds
from `GramMatrix.lean`.

*Deviation from the roadmap.*
The oracle `θ̂` (step 1) and its on-support subgradient `ẑ_S` (step 3) are obtained by
applying the *existing* `lasso_minimizer_exists` / `kkt_of_isLassoEstimator` to the design
`X'` obtained from `X` by **zeroing every column outside `S`** (`zeroOffCols`). Because `X'`
ignores off-support coordinates, every minimizer of its Lasso objective is automatically
supported on `S` (`minimizer_supported`), and on `S` the `X'`-gradient coincides with the
`X`-gradient (`zeroOff_designMap_eq`, `zeroOff_transpose_coord`). This reuses the heavy
convex-analysis machinery of `Subgradient.lean` verbatim and avoids re-indexing through
`Fin S.card`. Steps 4–9 are realized as named `have`s inside the main proof (rather than
top-level `private` lemmas) because they share the constructed witness `(θ̂, ẑ)` and a long
list of hypotheses; with `0` `sorry`s the gap structure is still fully explicit.

**Bibliographic comments.** The primal–dual witness construction and the strict-dual-
feasibility / mutual-incoherence analysis of the Lasso originate with M. J. Wainwright,
"Sharp Thresholds for High-Dimensional and Noisy Sparsity Recovery Using ℓ1-Constrained
Quadratic Programming (Lasso)," *IEEE Transactions on Information Theory*, vol. 55, no. 5,
pp. 2183–2202, 2009. There the witness is built in the proof of that paper's main support-
recovery theorem (Theorem 1), and the incoherence condition appears as the paper's mutual-
incoherence assumption; Theorem 7.21 is the streamlined deterministic restatement
formalized here. Closely related sufficient conditions for exact support
recovery were obtained independently by P. Zhao and B. Yu, "On Model Selection Consistency
of Lasso," *Journal of Machine Learning Research*, vol. 7, pp. 2541–2563, 2006 (the
"irrepresentable condition," which coincides with mutual incoherence).
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-! ## Matrix-algebra helpers (this file only) -/

/-- `.ofLp` of the design map is the matrix `mulVec` (definitional). -/
private lemma designMap_ofLp (X : Matrix (Fin n) (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    (designMap X θ).ofLp = X *ᵥ θ.ofLp := rfl

/-- Adjoint identity for `dotProduct`: `x ⬝ (M v) = (Mᵀ x) ⬝ v`. -/
private lemma dotProduct_mulVec_adj {p q : Type*} [Fintype p] [Fintype q]
    (M : Matrix p q ℝ) (x : p → ℝ) (y : q → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

/-- `(Xᵀ u)_j = ⟨X_j, u⟩` as a coordinate sum (the `j`-th column dotted with `u`). -/
private lemma transpose_mulVec_eq_col_dot (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d)
    (u : Fin n → ℝ) :
    (Xᵀ *ᵥ u) j = (col X j).ofLp ⬝ᵥ u := by
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, col, WithLp.ofLp_toLp]

/-- For `i ∈ S`, the `i.val`-coordinate of `Xᵀ V` equals the `i`-coordinate of `Xₛᵀ V`. -/
private lemma transpose_restrict (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (V : EuclideanSpace ℝ (Fin n)) (i : {x // x ∈ S}) :
    (designMap Xᵀ V).ofLp i.val = ((Xsub X S)ᵀ *ᵥ V.ofLp) i := by
  rw [designMap_ofLp, Xsub_transpose_mulVec_apply]
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]

/-- `0 ≤ ⨆ i, |f i|` over a finite index. -/
private lemma ciSup_abs_nonneg {ι : Type*} [Finite ι] (f : ι → ℝ) : 0 ≤ ⨆ i, |f i| := by
  rcases isEmpty_or_nonempty ι with he | hne
  · haveI := he; simp [Real.iSup_of_isEmpty]
  · haveI := Fintype.ofFinite ι
    exact le_ciSup_of_le (Finite.bddAbove_range _) (Classical.arbitrary ι) (abs_nonneg _)

/-- The matrix ℓ∞ operator norm is nonnegative. -/
private lemma matLinftyNorm_nonneg {p q : Type*} [Finite p] [Fintype q] (A : Matrix p q ℝ) :
    0 ≤ matLinftyNorm A := by
  unfold matLinftyNorm
  rcases isEmpty_or_nonempty p with he | hne
  · haveI := he; simp [Real.iSup_of_isEmpty]
  · haveI := Fintype.ofFinite p
    exact le_ciSup_of_le (Finite.bddAbove_range _) (Classical.arbitrary p)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- ℓ∞-norm bound from a uniform coordinate bound (nonempty- and empty-safe). -/
private lemma linfNorm_le_of_forall {x : EuclideanSpace ℝ (Fin d)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |x.ofLp i| ≤ c) : linfNorm x ≤ c := by
  rcases isEmpty_or_nonempty (Fin d) with he | hne
  · haveI := he; simp only [linfNorm, Real.iSup_of_isEmpty]; exact hc
  · exact ciSup_le h

/-! ## The "zero off `S`" design `X'` (PDW oracle device) -/

/-- The design `X` with **every column outside `S` zeroed out**. Its Lasso minimizers are
automatically supported on `S` (`minimizer_supported`), which realizes the PDW oracle solve
(Wainwright §7.5.2, step 1) using the existing `lasso_minimizer_exists`. -/
private def zeroOffCols (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of (fun i j => if j ∈ S then X i j else 0)

/-- On vectors supported on `S`, the zeroed design acts like `X`. -/
private lemma zeroOff_designMap_eq (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : ∀ j ∉ S, θ.ofLp j = 0) :
    designMap (zeroOffCols X S) θ = designMap X θ := by
  apply WithLp.ofLp_injective 2
  rw [designMap_ofLp, designMap_ofLp]
  funext k
  simp only [Matrix.mulVec, dotProduct, zeroOffCols, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S
  · rw [if_pos hj]
  · rw [if_neg hj, hθ j hj]; ring

/-- For `i ∈ S`, the zeroed transpose acts like `Xᵀ`. -/
private lemma zeroOff_transpose_coord (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (V : EuclideanSpace ℝ (Fin n)) (i : Fin d) (hi : i ∈ S) :
    (designMap (zeroOffCols X S)ᵀ V).ofLp i = (designMap Xᵀ V).ofLp i := by
  rw [designMap_ofLp, designMap_ofLp]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, zeroOffCols, Matrix.of_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [if_pos hi]

/-- **PDW oracle support** (Wainwright §7.5.2, step 1): every minimizer of the `X'`-Lasso
objective is supported on `S`. -/
private lemma minimizer_supported (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (θhat : EuclideanSpace ℝ (Fin d))
    (hlam : 0 < lam) (hopt : IsLassoEstimator (zeroOffCols X S) Y lam θhat) :
    ∀ j ∉ S, θhat.ofLp j = 0 := by
  have hdm : designMap (zeroOffCols X S) (restrict S θhat)
      = designMap (zeroOffCols X S) θhat := by
    apply WithLp.ofLp_injective 2
    rw [designMap_ofLp, designMap_ofLp]
    funext k
    simp only [Matrix.mulVec, dotProduct, zeroOffCols, Matrix.of_apply, restrict_ofLp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ S
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj]; ring
  have hle := hopt (restrict S θhat)
  unfold lassoObjective at hle
  rw [hdm] at hle
  have hpart : lam * l1Norm θhat ≤ lam * l1Norm (restrict S θhat) := by linarith [hle]
  have hge : l1Norm θhat ≤ l1Norm (restrict S θhat) := le_of_mul_le_mul_left hpart hlam
  have hsplit := l1Norm_split S θhat
  have hcompl0 : l1Norm (restrict Sᶜ θhat) = 0 :=
    le_antisymm (by linarith [hge, hsplit]) (l1Norm_nonneg _)
  rw [l1Norm_restrict_eq_sum] at hcompl0
  intro j hj
  have hjc : j ∈ Sᶜ := Finset.mem_compl.mpr hj
  exact abs_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)).mp hcompl0 j hjc)

/-! ## Normalized inverse Gram identity -/

/-- `(XₛᵀXₛ/n)⁻¹ u = n · (XₛᵀXₛ)⁻¹ u`, i.e. `gramInvNorm` is `n • gramInv` on vectors. -/
private lemma gramInvNorm_mulVec_eq (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2)
    (u : {x // x ∈ S} → ℝ) :
    (gramInvNorm X S) *ᵥ u = (n : ℝ) • (gramInv X S *ᵥ u) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hgu : IsUnit (gram X S).det := gram_isUnit_det X S hn hcmin hcoer
  have hunit : IsUnit ((1 / (n : ℝ)) • gram X S).det := by
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by positivity : (1 / (n : ℝ)) ≠ 0)).pow _).mul hgu
  have hG1 : gramInvNorm X S * ((1 / (n : ℝ)) • gram X S) = 1 := by
    rw [gramInvNorm]; exact Matrix.nonsing_inv_mul _ hunit
  have hgg : gram X S * gramInv X S = 1 := by
    rw [gramInv]; exact Matrix.mul_nonsing_inv _ hgu
  have hg2 : ((1 / (n : ℝ)) • gram X S) *ᵥ ((n : ℝ) • (gramInv X S *ᵥ u)) = u := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec,
      smul_smul, show (1 / (n : ℝ)) * (n : ℝ) = 1 from by field_simp, one_smul]
  calc (gramInvNorm X S) *ᵥ u
      = (gramInvNorm X S)
          *ᵥ (((1 / (n : ℝ)) • gram X S) *ᵥ ((n : ℝ) • (gramInv X S *ᵥ u))) := by rw [hg2]
    _ = (gramInvNorm X S * ((1 / (n : ℝ)) • gram X S)) *ᵥ ((n : ℝ) • (gramInv X S *ᵥ u)) := by
        rw [Matrix.mulVec_mulVec]
    _ = (n : ℝ) • (gramInv X S *ᵥ u) := by rw [hG1, Matrix.one_mulVec]

/-! ## The main theorem -/

/-- **Primal–dual witness existence + strict feasibility + ℓ∞ bound** (Wainwright §7.5.2).
Under the lower-eigenvalue condition (A3), mutual incoherence (A4) with `α ∈ [0,1)`, and the
regularization condition (7.44) `λ ≥ (2/(1−α))·‖Xₛᶜᵀ Π_{S⊥}(X) w/n‖_∞`, the Lagrangian Lasso
with response `Y = X θ* + w` admits a primal–dual witness `(θ̂, ẑ)` that is supported on `S`,
KKT-optimal, **strictly** dual feasible off `S`, and whose support error obeys the bound
`B(λ;X)`. -/
theorem pdw_witness_exists (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) (lam α cmin : ℝ)
    -- USER-INPUT: 0 < n; Wainwright §7.5
    (hn : 0 < n)
    -- USER-INPUT: θ* supported on S; Wainwright §7.5 (S-sparse model)
    (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    -- USER-INPUT: lower-eigenvalue condition (A3); Wainwright §7.5.1 (7.43a)
    (hA3 : LowerEigenvalue X S cmin)
    -- USER-INPUT: 0 < cmin; Wainwright §7.5.1 (7.43a)
    (hcmin : 0 < cmin)
    -- USER-INPUT: mutual incoherence (A4); Wainwright §7.5.1 (7.43b)
    (hA4 : MutualIncoherence X S α)
    -- USER-INPUT: 0 ≤ α; Wainwright §7.5.1 (incoherence parameter α ∈ [0,1))
    (hα0 : 0 ≤ α)
    -- USER-INPUT: α < 1; Wainwright §7.5.1 (incoherence parameter α ∈ [0,1))
    (hα1 : α < 1)
    -- USER-INPUT: 0 < λ; Wainwright §7.5
    (hlampos : 0 < lam)
    -- USER-INPUT: regularization condition λ ≥ (2/(1−α))·‖Xₛᶜᵀ Π_{S⊥} w/n‖_∞; Wainwright (7.44)
    (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w) :
    ∃ θhat zhat : EuclideanSpace ℝ (Fin d),
      (∀ j ∉ S, θhat.ofLp j = 0) ∧
      IsL1Subgradient zhat θhat ∧
      IsKKT X (designMap X θstar + w) lam θhat zhat ∧
      (∀ j ∉ S, |zhat.ofLp j| < 1) ∧
      linfNorm (restrict S (θhat - θstar)) ≤ supportRecoveryBound X S w lam := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hlam0 : lam ≠ 0 := hlampos.ne'
  have hαpos : 0 < 1 - α := by linarith
  have hane : (1 : ℝ) - α ≠ 0 := hαpos.ne'
  have habs_sub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])
  set Y : EuclideanSpace ℝ (Fin n) := designMap X θstar + w with hYdef
  -- Step 1: the oracle θ̂ (minimizer of the zeroed design ⇒ supported on S).
  obtain ⟨θhat, hopt'⟩ := lasso_minimizer_exists (zeroOffCols X S) Y lam hlampos
  have hsuppθ : ∀ j ∉ S, θhat.ofLp j = 0 :=
    minimizer_supported X S Y lam θhat hlampos hopt'
  obtain ⟨z', hz'sub, hz'kkt⟩ := kkt_of_isLassoEstimator (zeroOffCols X S) Y lam θhat hn hopt'
  -- Step 2: the dual witness ẑ (explicit gradient formula) and its KKT identity.
  set zhat : EuclideanSpace ℝ (Fin d) :=
    -(1 / (lam * (n : ℝ))) • designMap Xᵀ (designMap X θhat - Y) with hzhat
  have hKKT : IsKKT X Y lam θhat zhat := by
    unfold IsKKT
    rw [hzhat, smul_smul,
      show lam * -(1 / (lam * (n : ℝ))) = -(1 / (n : ℝ)) from by field_simp, neg_smul]
    abel
  -- Step 3 bridge: ẑ = z' on S, so ẑ_S is a subgradient of ‖θ̂_S‖₁.
  have hz'eq : z' = -(1 / (lam * (n : ℝ)))
      • designMap (zeroOffCols X S)ᵀ (designMap (zeroOffCols X S) θhat - Y) := by
    have hlz := eq_neg_of_add_eq_zero_right hz'kkt
    have hscale : z' = (1 / lam) • (lam • z') := by
      rw [smul_smul, one_div_mul_cancel hlam0, one_smul]
    rw [hscale, hlz, smul_neg, smul_smul,
      show (1 / lam) * (1 / (n : ℝ)) = 1 / (lam * (n : ℝ)) from by field_simp, ← neg_smul]
  have hzeq : ∀ i ∈ S, z'.ofLp i = zhat.ofLp i := by
    intro i hi
    have hV : designMap (zeroOffCols X S) θhat - Y = designMap X θhat - Y := by
      rw [zeroOff_designMap_eq X S θhat hsuppθ]
    rw [hz'eq, hzhat]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [hV, zeroOff_transpose_coord X S (designMap X θhat - Y) i hi]
  have hzS : ∀ i ∈ S, (0 < θhat.ofLp i → zhat.ofLp i = 1)
      ∧ (θhat.ofLp i < 0 → zhat.ofLp i = -1) ∧ |zhat.ofLp i| ≤ 1 := by
    intro i hi
    rw [← hzeq i hi]
    exact hz'sub i
  -- Residual identity: (X θ̂ − Y)|_coords = Xₛ Δ − w (Δ := θ̂_S − θ*_S).
  have hVeq : (designMap X θhat - Y).ofLp
      = (Xsub X S) *ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)
        - w.ofLp := by
    have e1 : X *ᵥ θhat.ofLp
        = Xsub X S *ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val) := by
      have hds := designMap_restrict_eq_designSub X S θhat
      rw [restrict_eq_self S θhat hsuppθ] at hds
      have h := congrArg WithLp.ofLp hds
      rwa [designMap_ofLp, designSub_apply, WithLp.ofLp_toLp] at h
    have e2 : X *ᵥ θstar.ofLp
        = Xsub X S *ᵥ (fun i : {x // x ∈ S} => θstar.ofLp i.val) := by
      have hds := designMap_restrict_eq_designSub X S θstar
      rw [restrict_eq_self S θstar hsupp] at hds
      have h := congrArg WithLp.ofLp hds
      rwa [designMap_ofLp, designSub_apply, WithLp.ofLp_toLp] at h
    funext k
    rw [hYdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply, designMap_ofLp]
    have key : (X *ᵥ θhat.ofLp) k - (X *ᵥ θstar.ofLp) k
        = (Xsub X S *ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)) k := by
      rw [e1, e2]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith [key]
  -- Step 4 (7.52): θ̂_S − θ*_S = (XₛᵀXₛ)⁻¹ Xₛᵀw − λn (XₛᵀXₛ)⁻¹ ẑ_S.
  have theta_diff_eq :
      (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)
        = gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)
          - (lam * (n : ℝ)) • (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) := by
    have hkkt_coord : ∀ j,
        (1 / (n : ℝ)) * (designMap Xᵀ (designMap X θhat - Y)).ofLp j + lam * zhat.ofLp j = 0 := by
      intro j
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v.ofLp j) hKKT
      simpa only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        WithLp.ofLp_zero, Pi.zero_apply] using h
    have hblock : ∀ i : {x // x ∈ S},
        (gram X S *ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)) i
          = ((Xsub X S)ᵀ *ᵥ w.ofLp) i - (lam * (n : ℝ)) * zhat.ofLp i.val := by
      intro i
      have hc := hkkt_coord i.val
      rw [transpose_restrict X S (designMap X θhat - Y) i, hVeq, Matrix.mulVec_sub,
        Pi.sub_apply, Matrix.mulVec_mulVec,
        show (Xsub X S)ᵀ * Xsub X S = gram X S from rfl] at hc
      have hmul := congrArg (fun t => (n : ℝ) * t) hc
      simp only [mul_add, mul_zero] at hmul
      rw [show (n : ℝ) * ((1 / (n : ℝ))
            * ((gram X S *ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)) i
              - ((Xsub X S)ᵀ *ᵥ w.ofLp) i))
          = (gram X S *ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)) i
            - ((Xsub X S)ᵀ *ᵥ w.ofLp) i from by field_simp,
        show (n : ℝ) * (lam * zhat.ofLp i.val) = (lam * (n : ℝ)) * zhat.ofLp i.val
          from by ring] at hmul
      linarith [hmul]
    have hgΔ : gram X S *ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)
        = (Xsub X S)ᵀ *ᵥ w.ofLp
          - (lam * (n : ℝ)) • (fun i : {x // x ∈ S} => zhat.ofLp i.val) := by
      funext i
      rw [hblock i]
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)
        = gramInv X S *ᵥ (gram X S
            *ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)) :=
          (gramInv_mulVec_gram X S hn hcmin hA3 _).symm
      _ = gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp
            - (lam * (n : ℝ)) • (fun i : {x // x ∈ S} => zhat.ofLp i.val)) := by rw [hgΔ]
      _ = gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)
            - (lam * (n : ℝ)) • (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  -- pointwise form of theta_diff_eq
  have hdiff : ∀ i : {x // x ∈ S}, θhat.ofLp i.val - θstar.ofLp i.val
      = (gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)) i
        - (lam * (n : ℝ)) * (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) i := by
    intro i
    have := congrFun theta_diff_eq i
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  -- Step 5 (7.54): the ℓ∞ error bound.
  have linf_error_bound :
      linfNorm (restrict S (θhat - θstar)) ≤ supportRecoveryBound X S w lam := by
    unfold supportRecoveryBound
    set A : ℝ := ⨆ i : {x // x ∈ S},
      |((gramInvNorm X S).mulVec ((1 / (n : ℝ)) • (Xsub X S)ᵀ.mulVec w.ofLp)) i| with hA
    set B : ℝ := matLinftyNorm (gramInvNorm X S) * lam with hB
    have hfirst : gramInvNorm X S *ᵥ ((1 / (n : ℝ)) • ((Xsub X S)ᵀ *ᵥ w.ofLp))
        = gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp) := by
      rw [gramInvNorm_mulVec_eq X S hn hcmin hA3, Matrix.mulVec_smul, smul_smul,
        show (n : ℝ) * (1 / (n : ℝ)) = 1 from by field_simp, one_smul]
    have hgconv : gramInvNorm X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)
        = (n : ℝ) • (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) :=
      gramInvNorm_mulVec_eq X S hn hcmin hA3 _
    have hAnn : 0 ≤ A := by rw [hA]; exact ciSup_abs_nonneg _
    have hBnn : 0 ≤ B := by rw [hB]; exact mul_nonneg (matLinftyNorm_nonneg _) hlampos.le
    apply linfNorm_le_of_forall (by linarith [hAnn, hBnn])
    intro k
    rw [restrict_ofLp_apply]
    by_cases hk : k ∈ S
    · rw [if_pos hk]
      have hkeq : (θhat - θstar).ofLp k = θhat.ofLp k - θstar.ofLp k := by
        simp
      rw [hkeq]
      have hkv : θhat.ofLp k - θstar.ofLp k
          = θhat.ofLp (⟨k, hk⟩ : {x // x ∈ S}).val
            - θstar.ofLp (⟨k, hk⟩ : {x // x ∈ S}).val := rfl
      rw [hkv, hdiff ⟨k, hk⟩]
      have hA1 : |(gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)) (⟨k, hk⟩ : {x // x ∈ S})| ≤ A := by
        rw [hA, ← hfirst]
        exact le_ciSup_of_le (Finite.bddAbove_range _) (⟨k, hk⟩ : {x // x ∈ S}) le_rfl
      haveI : Nonempty {x // x ∈ S} := ⟨⟨k, hk⟩⟩
      have hzSle1 : (⨆ i : {x // x ∈ S}, |zhat.ofLp i.val|) ≤ 1 :=
        ciSup_le (fun i => (hzS i.val i.2).2.2)
      have hsupB : (⨆ i : {x // x ∈ S},
          |(gramInvNorm X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) i|)
          ≤ matLinftyNorm (gramInvNorm X S) := by
        calc (⨆ i : {x // x ∈ S},
              |(gramInvNorm X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) i|)
            ≤ matLinftyNorm (gramInvNorm X S) * (⨆ i : {x // x ∈ S}, |zhat.ofLp i.val|) :=
              matLinftyNorm_mulVec_le (gramInvNorm X S)
                (fun i : {x // x ∈ S} => zhat.ofLp i.val)
          _ ≤ matLinftyNorm (gramInvNorm X S) * 1 :=
              mul_le_mul_of_nonneg_left hzSle1 (matLinftyNorm_nonneg _)
          _ = matLinftyNorm (gramInvNorm X S) := mul_one _
      have hB1 : (lam * (n : ℝ))
          * |(gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) (⟨k, hk⟩ : {x // x ∈ S})|
            ≤ B := by
        have hcoord : (n : ℝ) * (gramInv X S
              *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) (⟨k, hk⟩ : {x // x ∈ S})
            = (gramInvNorm X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))
                (⟨k, hk⟩ : {x // x ∈ S}) := by
          rw [hgconv]; simp [Pi.smul_apply, smul_eq_mul]
        have hle2 : |(gramInvNorm X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))
            (⟨k, hk⟩ : {x // x ∈ S})| ≤ matLinftyNorm (gramInvNorm X S) :=
          le_trans (le_ciSup_of_le (Finite.bddAbove_range _) (⟨k, hk⟩ : {x // x ∈ S}) le_rfl) hsupB
        have hrw : (lam * (n : ℝ))
            * |(gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))
                (⟨k, hk⟩ : {x // x ∈ S})|
            = lam * |(gramInvNorm X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))
                (⟨k, hk⟩ : {x // x ∈ S})| := by
          rw [← hcoord, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ))]; ring
        rw [hrw, hB, mul_comm (matLinftyNorm (gramInvNorm X S)) lam]
        exact mul_le_mul_of_nonneg_left hle2 hlampos.le
      calc |(gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)) (⟨k, hk⟩ : {x // x ∈ S})
              - (lam * (n : ℝ)) * (gramInv X S
                  *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) (⟨k, hk⟩ : {x // x ∈ S})|
          ≤ |(gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)) (⟨k, hk⟩ : {x // x ∈ S})|
            + |(lam * (n : ℝ)) * (gramInv X S
                *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)) (⟨k, hk⟩ : {x // x ∈ S})| :=
            habs_sub _ _
        _ ≤ A + B := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < lam * (n:ℝ))]
            exact add_le_add hA1 hB1
    · rw [if_neg hk, abs_zero]; linarith [hAnn, hBnn]
  -- Step 6 (7.53): the ẑ_{Sᶜ} block decomposition ẑ_j = μ_j + V_j.
  have zSc_eq : ∀ j ∉ S, zhat.ofLp j
      = ((Xsub X S)ᵀ *ᵥ (col X j).ofLp)
          ⬝ᵥ (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))
        + (1 / (lam * (n : ℝ))) * ((col X j).ofLp ⬝ᵥ ((projPerp X S) *ᵥ w.ofLp)) := by
    intro j hj
    have hcoord : (designMap Xᵀ (designMap X θhat - Y)).ofLp j
        = ((Xsub X S)ᵀ *ᵥ (col X j).ofLp)
            ⬝ᵥ (fun i : {x // x ∈ S} => θhat.ofLp i.val - θstar.ofLp i.val)
          - (col X j).ofLp ⬝ᵥ w.ofLp := by
      rw [designMap_ofLp, transpose_mulVec_eq_col_dot, hVeq, dotProduct_sub,
        dotProduct_mulVec_adj]
    have hexp : ((Xsub X S)ᵀ *ᵥ (col X j).ofLp)
        ⬝ᵥ (gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)
          - (lam * (n : ℝ)) • (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)))
        = ((Xsub X S)ᵀ *ᵥ (col X j).ofLp) ⬝ᵥ (gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp))
          - (lam * (n : ℝ)) * (((Xsub X S)ᵀ *ᵥ (col X j).ofLp)
              ⬝ᵥ (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))) := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hproj : (col X j).ofLp ⬝ᵥ ((projPerp X S) *ᵥ w.ofLp)
        = (col X j).ofLp ⬝ᵥ w.ofLp
          - ((Xsub X S)ᵀ *ᵥ (col X j).ofLp) ⬝ᵥ (gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)) := by
      unfold projPerp
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
      congr 1
      rw [show (Xsub X S * gramInv X S * (Xsub X S)ᵀ) *ᵥ w.ofLp
            = Xsub X S *ᵥ (gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ w.ofLp)) from by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
      rw [dotProduct_mulVec_adj]
    have hlhs : zhat.ofLp j
        = -(1 / (lam * (n : ℝ))) * (designMap Xᵀ (designMap X θhat - Y)).ofLp j := by
      rw [hzhat]; simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [hlhs, hcoord, theta_diff_eq, hexp, hproj]
    field_simp
    ring
  -- Step 7: incoherence bound |μ_j| ≤ α.
  have incoherence_bound : ∀ j ∉ S,
      |((Xsub X S)ᵀ *ᵥ (col X j).ofLp)
        ⬝ᵥ (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))| ≤ α := by
    intro j hj
    have hsymm : ((Xsub X S)ᵀ *ᵥ (col X j).ofLp)
        ⬝ᵥ (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))
        = (gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ (col X j).ofLp))
          ⬝ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val) := by
      rw [dotProduct_mulVec_adj,
        show (gramInv X S)ᵀ = gramInv X S from by
          rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
          exact gramInv_isHermitian X S hn hcmin hA3]
    rw [hsymm]
    calc |(gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ (col X j).ofLp))
            ⬝ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val)|
        ≤ ∑ i, |(gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ (col X j).ofLp)) i| * |zhat.ofLp i.val| := by
          rw [dotProduct]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i, |(gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ (col X j).ofLp)) i| * 1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (hzS i.val i.2).2.2 (abs_nonneg _)
      _ = ∑ i, |(gramInv X S *ᵥ ((Xsub X S)ᵀ *ᵥ (col X j).ofLp)) i| := by simp
      _ ≤ α := hA4 j hj
  -- Step 8: noise bound |V_j| ≤ (1−α)/2.
  have noise_bound : ∀ j ∉ S,
      |(1 / (lam * (n : ℝ))) * ((col X j).ofLp ⬝ᵥ ((projPerp X S) *ᵥ w.ofLp))| ≤ (1 - α) / 2 := by
    intro j hj
    have hjc : j ∈ Sᶜ := Finset.mem_compl.mpr hj
    haveI : Nonempty {x // x ∈ Sᶜ} := ⟨⟨j, hjc⟩⟩
    have hcoordeq : ((Xsub X Sᶜ)ᵀ *ᵥ ((1 / (n : ℝ)) • (projPerp X S) *ᵥ w.ofLp))
        (⟨j, hjc⟩ : {x // x ∈ Sᶜ})
        = (1 / (n : ℝ)) * ((col X j).ofLp ⬝ᵥ ((projPerp X S) *ᵥ w.ofLp)) := by
      rw [Xsub_transpose_mulVec_apply, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, col, WithLp.ofLp_toLp]
      ring
    have hLHSabs : |(1 / (lam * (n : ℝ))) * ((col X j).ofLp ⬝ᵥ ((projPerp X S) *ᵥ w.ofLp))|
        = (1 / lam) * |((Xsub X Sᶜ)ᵀ *ᵥ ((1 / (n : ℝ)) • (projPerp X S) *ᵥ w.ofLp))
            (⟨j, hjc⟩ : {x // x ∈ Sᶜ})| := by
      rw [hcoordeq, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (lam * (n : ℝ))),
        abs_of_pos (by positivity : (0:ℝ) < 1 / (n : ℝ))]
      field_simp
    have hcoord_le : |((Xsub X Sᶜ)ᵀ *ᵥ ((1 / (n : ℝ)) • (projPerp X S) *ᵥ w.ofLp))
          (⟨j, hjc⟩ : {x // x ∈ Sᶜ})| ≤ projNoiseLinf X S w := by
      unfold projNoiseLinf
      exact le_ciSup_of_le (Finite.bddAbove_range _) (⟨j, hjc⟩ : {x // x ∈ Sᶜ}) le_rfl
    have hP : projNoiseLinf X S w ≤ (1 - α) / 2 * lam := by
      have h2 := mul_le_mul_of_nonneg_left hlam (le_of_lt (by positivity : (0:ℝ) < (1 - α) / 2))
      have hc : (1 - α) / 2 * ((2 / (1 - α)) * projNoiseLinf X S w) = projNoiseLinf X S w := by
        field_simp
      rw [hc] at h2
      exact h2
    have hfin : (1 / lam) * projNoiseLinf X S w ≤ (1 - α) / 2 := by
      rw [show (1 / lam) * projNoiseLinf X S w = projNoiseLinf X S w / lam from by ring,
        div_le_iff₀ hlampos]
      exact hP
    calc |(1 / (lam * (n : ℝ))) * ((col X j).ofLp ⬝ᵥ ((projPerp X S) *ᵥ w.ofLp))|
        = (1 / lam) * |((Xsub X Sᶜ)ᵀ *ᵥ ((1 / (n : ℝ)) • (projPerp X S) *ᵥ w.ofLp))
            (⟨j, hjc⟩ : {x // x ∈ Sᶜ})| := hLHSabs
      _ ≤ (1 / lam) * projNoiseLinf X S w :=
          mul_le_mul_of_nonneg_left hcoord_le (by positivity)
      _ ≤ (1 - α) / 2 := hfin
  -- Step 9: strict dual feasibility.
  have hstrict : ∀ j ∉ S, |zhat.ofLp j| < 1 := by
    intro j hj
    rw [zSc_eq j hj]
    calc |((Xsub X S)ᵀ *ᵥ (col X j).ofLp)
            ⬝ᵥ (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))
          + (1 / (lam * (n : ℝ))) * ((col X j).ofLp ⬝ᵥ ((projPerp X S) *ᵥ w.ofLp))|
        ≤ |((Xsub X S)ᵀ *ᵥ (col X j).ofLp)
              ⬝ᵥ (gramInv X S *ᵥ (fun i : {x // x ∈ S} => zhat.ofLp i.val))|
          + |(1 / (lam * (n : ℝ))) * ((col X j).ofLp ⬝ᵥ ((projPerp X S) *ᵥ w.ofLp))| :=
          abs_add_le _ _
      _ ≤ α + (1 - α) / 2 := add_le_add (incoherence_bound j hj) (noise_bound j hj)
      _ < 1 := by linarith
  -- Step 10: assemble the ℓ¹ subgradient and the full witness.
  have hsub : IsL1Subgradient zhat θhat := by
    intro i
    by_cases hi : i ∈ S
    · exact hzS i hi
    · refine ⟨fun hpos => ?_, fun hneg => ?_, le_of_lt (hstrict i hi)⟩
      · rw [hsuppθ i hi] at hpos; exact absurd hpos (lt_irrefl 0)
      · rw [hsuppθ i hi] at hneg; exact absurd hneg (lt_irrefl 0)
  exact ⟨θhat, zhat, hsuppθ, hsub, hKKT, hstrict, linf_error_bound⟩

end StatLean.HighDimensionalStatistics
