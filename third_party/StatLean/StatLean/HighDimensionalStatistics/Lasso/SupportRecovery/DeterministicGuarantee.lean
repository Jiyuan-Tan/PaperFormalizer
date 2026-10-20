module
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Subgradient
public import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.DualCertificate

@[expose] public section

/-!
# Theorem 7.21 — Lasso variable-selection consistency

Consider the $S$-sparse linear model $Y = X\theta^\* + w$, where the true regression vector
$\theta^\*$ is supported on a subset $S \subseteq \{1,\dots,d\}$ (so $\theta^\*_j = 0$ for all
$j \notin S$). Assume the design matrix $X$ satisfies the **lower-eigenvalue condition (A3)** —
the restricted submatrix $\tfrac1n X_S^\top X_S$ has minimum eigenvalue at least $c_{\min} > 0$
— and the **mutual-incoherence condition (A4)** with parameter $\alpha \in [0,1)$. If the
regularization parameter satisfies the condition (7.44)
$$\lambda \ \ge\ \frac{2}{1-\alpha}\,\bigl\|\tfrac1n X_{S^c}^\top \Pi_{S^\perp}\, w\bigr\|_\infty ,$$
then the Lagrangian Lasso program enjoys the following variable-selection guarantees:

* **(a) Uniqueness.** The Lasso has a *unique* optimal solution $\widehat\beta$.
* **(b) No false inclusion.** Every Lasso minimizer is supported on $S$, i.e.
  $\operatorname{supp}(\widehat\beta) \subseteq S$ ($\widehat\beta_j = 0$ for all $j \notin S$).
* **(c) $\ell_\infty$ error bound (Eq. 7.45).** Every Lasso minimizer satisfies
  $\|\widehat\beta_S - \theta^\*_S\|_\infty \le B(\lambda; X)$, where $B(\lambda;X)$ is the
  support-recovery bound built from the regularization level and design.
* **(d) No false exclusion.** Every support coordinate whose magnitude exceeds the bound is
  recovered: if $i \in S$ and $|\theta^\*_i| > B(\lambda;X)$ then $\widehat\beta_i \neq 0$. In
  particular, when $\min_{i \in S}|\theta^\*_i| > B(\lambda;X)$ the Lasso achieves exact
  variable-selection consistency, $\operatorname{supp}(\widehat\beta) = S$.

This is the deterministic core of the boxed Theorem 7.21: parts (b)–(d) are stated in the
strong ∀-form (over *every* Lasso minimizer), which combined with (a) is exactly the book's
statement about "the" solution.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 7 (Sparse linear models in high dimensions), §7.5
(Variable or model selection consistency), Theorem 7.21 (a)–(d); conditions (A3),(A4) are
Eqs (7.43a),(7.43b), the regularization condition is Eq (7.44), and the $\ell_\infty$ bound is
Eq (7.45). The uniqueness part rests on Lemma 7.23 (strict dual feasibility ⇒ unique optimum).

**Proof formalization notes.** The result is assembled from the primal–dual-witness (PDW)
construction in `DualCertificate.lean` and the uniqueness Lemma 7.23 in `Subgradient.lean`:

* (a) `lasso_support_recovery_unique` — `pdw_witness_exists` produces a strictly dual-feasible
  witness $(\widehat\theta, \widehat z)$; `pdw_unique` upgrades strict feasibility to a unique
  optimum.
* (b) `lasso_support_recovery_no_false_inclusion` — `pdw_every_minimizer_supported` shows any
  minimizer agrees with the supported witness off $S$.
* (c) `lasso_support_recovery_linf` — the witness carries the $\ell_\infty$ bound `hbound`;
  uniqueness identifies an arbitrary minimizer with the witness, transporting the bound.
* (d) `lasso_support_recovery_no_false_exclusion` — derived from (c): $|\widehat\beta_i -
  \theta^\*_i| \le B$ together with $|\theta^\*_i| > B$ forces $\widehat\beta_i \neq 0$.

All four parts share the standing hypotheses: the $S$-sparse model `hsupp`, conditions (A3)
`hA3`/`hcmin` and (A4) `hA4`, $\alpha \in [0,1)$, $0 < \lambda$, and the regularization
condition (7.44) `hlam`. No book constants are altered.

**Bibliographic comments.** The primal–dual-witness technique and the sharp ℓ∞-bound /
mutual-incoherence analysis underlying this theorem originate with M. J. Wainwright, "Sharp
thresholds for high-dimensional and noisy sparsity recovery using ℓ₁-constrained quadratic
programming (Lasso)," *IEEE Transactions on Information Theory*, vol. 55, no. 5, pp. 2183–2202,
2009. The mutual-incoherence / "irrepresentable" condition (A4) was identified independently as
necessary and sufficient for sign-consistent support recovery by P. Zhao and B. Yu, "On model
selection consistency of Lasso," *Journal of Machine Learning Research*, vol. 7, pp. 2541–2563,
2006, and by N. Meinshausen and P. Bühlmann, "High-dimensional graphs and variable selection
with the Lasso," *Annals of Statistics*, vol. 34, no. 3, pp. 1436–1462, 2006 (in the
neighbourhood-selection setting). Theorem 7.21 is a synthesis of this line of work.
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Theorem 7.21 (a) — uniqueness** (Wainwright §7.5). Under (A3),(A4), `α ∈ [0,1)` and the
regularization condition (7.44), the Lagrangian Lasso for `Y = X θ* + w` has a unique optimum. -/
theorem lasso_support_recovery_unique (X : Matrix (Fin n) (Fin d) ℝ)
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
    -- USER-INPUT: 0 ≤ α; Wainwright §7.5.1
    (hα0 : 0 ≤ α)
    -- USER-INPUT: α < 1; Wainwright §7.5.1
    (hα1 : α < 1)
    -- USER-INPUT: 0 < λ; Wainwright §7.5
    (hlampos : 0 < lam)
    -- USER-INPUT: regularization condition (7.44); Wainwright §7.5
    (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w) :
    ∃! βhat, IsLassoEstimator X (designMap X θstar + w) lam βhat := by
  obtain ⟨thHat, zHat, hsp, hsub, hkkt, hstrict, _⟩ :=
    pdw_witness_exists X S θstar w lam α cmin hn hsupp hA3 hcmin hA4 hα0 hα1 hlampos hlam
  exact pdw_unique X (designMap X θstar + w) S lam cmin thHat zHat
    hlampos hn hsp hsub hkkt hstrict hA3 hcmin

/-- **Theorem 7.21 (b) — no false inclusion** (Wainwright §7.5): every Lasso minimizer has
its support contained in `S`. -/
theorem lasso_support_recovery_no_false_inclusion (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) (lam α cmin : ℝ)
    (hn : 0 < n) (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    (hA3 : LowerEigenvalue X S cmin) (hcmin : 0 < cmin)
    (hA4 : MutualIncoherence X S α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlampos : 0 < lam) (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w)
    (βhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: β̂ is a Lasso minimizer; Wainwright §7.5
    (hopt : IsLassoEstimator X (designMap X θstar + w) lam βhat) :
    ∀ j ∉ S, βhat.ofLp j = 0 := by
  obtain ⟨thHat, zHat, hsp, hsub, hkkt, hstrict, _⟩ :=
    pdw_witness_exists X S θstar w lam α cmin hn hsupp hA3 hcmin hA4 hα0 hα1 hlampos hlam
  exact pdw_every_minimizer_supported X (designMap X θstar + w) S lam thHat zHat βhat
    hlampos hn hsp hsub hkkt hstrict hopt

/-- **Theorem 7.21 (c) — ℓ∞ error bound** (Wainwright 7.45): every Lasso minimizer satisfies
`‖β̂_S − θ*_S‖_∞ ≤ B(λ;X)`. -/
theorem lasso_support_recovery_linf (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) (lam α cmin : ℝ)
    (hn : 0 < n) (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    (hA3 : LowerEigenvalue X S cmin) (hcmin : 0 < cmin)
    (hA4 : MutualIncoherence X S α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlampos : 0 < lam) (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w)
    (βhat : EuclideanSpace ℝ (Fin d))
    (hopt : IsLassoEstimator X (designMap X θstar + w) lam βhat) :
    linfNorm (restrict S (βhat - θstar)) ≤ supportRecoveryBound X S w lam := by
  obtain ⟨thHat, zHat, hsp, hsub, hkkt, hstrict, hbound⟩ :=
    pdw_witness_exists X S θstar w lam α cmin hn hsupp hA3 hcmin hA4 hα0 hα1 hlampos hlam
  have hthHatmin := lassoEstimator_of_kkt X (designMap X θstar + w) lam thHat zHat
    hn hlampos hsub hkkt
  have huniq := pdw_unique X (designMap X θstar + w) S lam cmin thHat zHat
    hlampos hn hsp hsub hkkt hstrict hA3 hcmin
  have hβeq : βhat = thHat := huniq.unique hopt hthHatmin
  rw [hβeq]; exact hbound

/-- **Theorem 7.21 (d) — no false exclusion** (Wainwright §7.5): the Lasso recovers every
support coordinate whose magnitude exceeds the bound; hence variable-selection consistency
when `min_{i∈S}|θ*_i| > B(λ;X)`. -/
theorem lasso_support_recovery_no_false_exclusion (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) (lam α cmin : ℝ)
    (hn : 0 < n) (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    (hA3 : LowerEigenvalue X S cmin) (hcmin : 0 < cmin)
    (hA4 : MutualIncoherence X S α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlampos : 0 < lam) (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w)
    (βhat : EuclideanSpace ℝ (Fin d))
    (hopt : IsLassoEstimator X (designMap X θstar + w) lam βhat)
    (i : Fin d) (hiS : i ∈ S)
    -- USER-INPUT: the coordinate exceeds the bound, |θ*_i| > B(λ;X); Wainwright §7.5 (d)
    (hbig : supportRecoveryBound X S w lam < |θstar.ofLp i|) :
    βhat.ofLp i ≠ 0 := by
  have hlinf := lasso_support_recovery_linf X S θstar w lam α cmin hn hsupp hA3 hcmin hA4 hα0 hα1
    hlampos hlam βhat hopt
  -- |β̂ᵢ − θ*ᵢ| ≤ ‖(β̂ − θ*)|_S‖_∞ ≤ B
  have hcoord : |(βhat - θstar).ofLp i| ≤ supportRecoveryBound X S w lam := by
    have h1 := abs_le_linfNorm (restrict S (βhat - θstar)) i
    rw [restrict_ofLp_apply, if_pos hiS] at h1
    exact h1.trans hlinf
  intro hzero
  -- with β̂ᵢ = 0, |β̂ᵢ − θ*ᵢ| = |θ*ᵢ| > B, contradiction
  have hsub : (βhat - θstar).ofLp i = βhat.ofLp i - θstar.ofLp i := by
    simp
  rw [hsub, hzero, zero_sub, abs_neg] at hcoord
  exact absurd (lt_of_le_of_lt hcoord hbig) (lt_irrefl _)

end StatLean.HighDimensionalStatistics
