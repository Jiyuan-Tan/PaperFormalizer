module
public import StatLean.Minimaxity.Fano.LocalPacking
public import StatLean.Minimaxity.ForMathlib.GaussianKLMulti
public import StatLean.Minimaxity.ForMathlib.Packing.SparsePacking
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Minimax risk for sparse linear regression

Consider the Gaussian linear model $y = X\theta^* + w$, with noise $w \sim \mathcal{N}(0, \sigma^2 I_n)$,
in which the regression vector $\theta^*$ is known a priori to be $s$-sparse. Take as the parameter set the
sparse Euclidean unit ball
$$
\mathbb{S}_d(s) \;=\; \mathbb{B}_0(s) \cap \mathbb{B}_2(1)
   \;=\; \{\theta : \|\theta\|_0 \le s,\ \|\theta\|_2 \le 1\},
$$
where $\|\theta\|_0$ counts the nonzero coordinates of $\theta$ (Eq. (15.40)). Then the minimax risk over
$\mathbb{S}_d(s)$ measured in squared Euclidean error is lower bounded by
$$
\mathfrak{M}\bigl(\mathbb{S}_d(s); \|\cdot\|_2^2\bigr)
   \;\gtrsim\; \min\!\left(\frac{\sigma^2}{\gamma_{2s}^2}\cdot
   \frac{s\,\log\!\bigl((d-s)/s\bigr)}{n},\ 1\right),
$$
where $\gamma_{2s} = \max_{|T| = 2s} \sigma_{\max}(X_T)/\sqrt{n}$ is the $2s$-restricted maximum singular
value of the design matrix $X$. Because $\mathbb{S}_d(s)$ is the bounded unit ball, the rate saturates at a
constant — hence the truncation $\min(\,\cdot\,, 1)$, exactly as in the PCA-over-the-sphere example.

**Deviations from the book.** The leading constant stated in Lean is loosened relative to the textbook
(permitted by CLAUDE.md §1): the formalized bound carries an explicit factor $1/4096$, forced by the
$(s/2)\log((d-s)/s) - s\log 2$ log-cardinality of the sparse-packing brick. The Lean statement also adds two
range hypotheses absent from the book's informal statement: $10 \le s$ (the local-packing / Fano cardinality
bound (15.35b) is vacuous for very small $s$; the book's stated range is $10 \le s \le d/2$) and $8s \le d$
(strengthening the book's $s \le d/2$ to absorb the $-s\log 2$ slack in the packing brick).

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3, Example 15.16, Eq. (15.40).

**Proof formalization notes.** The proof is the local-packing / Fano method (as in Example 15.14,
`LinearRegression.lean`) applied to a $1/2$-packing of $\mathbb{S}_d(s)$ (`exists_sparse_packing`,
Wainwright Exercise 5.8) rescaled into the ball (scale factor $\le 1$, so the points stay inside
$\mathbb{S}_d(s)$). The pairwise KL divergences are controlled by $\gamma_{2s}$ acting on the (at most
$2s$-sparse) packing differences, and the equal-covariance multivariate Gaussian KL
`klDiv_multivariateGaussian_smul_one` evaluates them, supplying the (15.35a) bound; the packing
cardinality supplies the (15.35b) bound.

**Bibliographic comments.** The sparse linear-regression minimax rate originates with G. Raskutti,
M. J. Wainwright, and B. Yu, "Minimax rates of estimation for high-dimensional linear regression over
$\ell_q$-balls," *IEEE Transactions on Information Theory*, vol. 57, no. 10, pp. 6976–6994, 2011
(arXiv:0910.2042). That paper establishes minimax rates over $\ell_q$-balls for $q \in [0, 1]$ in both
$\ell_2$-estimation and $\ell_2$-prediction loss; the hard-sparsity ($q = 0$, i.e. the $\mathbb{B}_0(s)$
ball) case formalized here is the $s\,\log(d/s)/n$ rate that Example 15.16 of Wainwright
distills from their analysis.
-/

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal

namespace StatLean.Minimaxity

/-- The `s`-sparse Euclidean unit ball `S_d(s) = B₀(s) ∩ B₂(1) = {θ : ‖θ‖₀ ≤ s, ‖θ‖₂ ≤ 1}`
(Wainwright Eq. 15.40), the parameter set over which the sparse-regression minimax risk is taken. A
vector is `s`-sparse when at most `s` coordinates are nonzero. -/
def SparseBall (d s : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {θ | (Finset.univ.filter fun i => θ i ≠ 0).card ≤ s ∧ ‖θ‖ ≤ 1}

/-- Support count is subadditive under subtraction: the support of `u - w` is contained in the union
of the supports of `u` and `w`, so its cardinality is at most the sum. Used to bound the packing
differences `θⱼ − θₖ` by `2s`-sparse vectors (Wainwright Ex 15.16). -/
private lemma card_filter_sub_le {d : ℕ} (u w : EuclideanSpace ℝ (Fin d)) :
    (Finset.univ.filter fun i => (u - w) i ≠ 0).card
      ≤ (Finset.univ.filter fun i => u i ≠ 0).card
        + (Finset.univ.filter fun i => w i ≠ 0).card := by
  classical
  have hsub : (Finset.univ.filter fun i => (u - w) i ≠ 0)
      ⊆ (Finset.univ.filter fun i => u i ≠ 0 ∨ w i ≠ 0) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    by_contra hc
    push_neg at hc
    apply hi.2
    rw [PiLp.sub_apply, hc.1, hc.2, sub_zero]
  calc (Finset.univ.filter fun i => (u - w) i ≠ 0).card
      ≤ (Finset.univ.filter fun i => u i ≠ 0 ∨ w i ≠ 0).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun i => u i ≠ 0).card
          + (Finset.univ.filter fun i => w i ≠ 0).card := by
        rw [Finset.filter_or]; exact Finset.card_union_le _ _

/-- **Crux: local packing data for sparse linear regression.** A `1/2`-packing of the `s`-sparse unit
ball (Wainwright Example 5.8, `exists_sparse_packing`) of log-cardinality `≥ (s/2)log((d−s)/s) − s·log2`,
rescaled into `S_d(s)` (scale `≤ 1`, so the points stay in the ball), gives a `δ`-separated family (in
`‖·‖₂`) whose pairwise KL divergences satisfy the (15.35a) bound — via the `2s`-restricted singular
value `γ` acting on the `≤ 2s`-sparse differences and the equal-covariance multivariate Gaussian KL
`klDiv_multivariateGaussian_smul_one` — and whose cardinality satisfies (15.35b).

The separation `δ² = 2048⁻¹·min(t, 1)` with `t = v·s·log((d−s)/s)/(γ²n)`; the `min(·,1)` is the bounded
unit-ball cap and the constant is loosened (CLAUDE.md §1) to fit the sparse-packing brick. -/
private lemma sparse_linreg_local_packing_data {n d s : ℕ} (hn : 1 ≤ n)
    -- LEAN-ONLY: 10 ≤ s — the local-packing/Fano cardinality (15.35b) is vacuous for small s; the book's range is 10 ≤ s ≤ d/2.
    (hs0 : 10 ≤ s)
    -- LEAN-ONLY: 8s ≤ d — stronger than the book's s ≤ d/2, to absorb the −s·log2 slack in the sparse-packing brick.
    (hds : 8 * s ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (γ : ℝ≥0) (hγ : γ ≠ 0)
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    -- USER-INPUT: `γ` is the `2s`-restricted singular value `γ₂ₛ = max_{|T|=2s} σ_max(X_T)/√n`; Wainwright Ex 15.16.
    (hγbd : ∀ θ : EuclideanSpace ℝ (Fin d),
        (Finset.univ.filter fun i => θ i ≠ 0).card ≤ 2 * s → ‖A θ‖ ≤ Real.sqrt (n : ℝ) * (γ : ℝ) * ‖θ‖)
    (P : Kernel (SparseBall d s) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel P]
    -- USER-INPUT: `y ∼ 𝒩(Aθ, v Iₙ)` (fixed-design Gaussian model); Wainwright §15.3.3, Ex 15.16.
    (hP : ∀ θ, P θ = multivariateGaussian (A (θ : EuclideanSpace ℝ (Fin d)))
            ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    ∃ (M : ℕ) (_ : NeZero M) (θfam : Fin M → SparseBall d s) (hθ : Measurable θfam) (c : ℝ),
      IsSeparatedFamily Subtype.val θfam (ENNReal.ofReal (Real.sqrt (2048⁻¹ *
          min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1))) ∧
      (∀ j k, j ≠ k → klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
        ≤ ENNReal.ofReal (c ^ 2 * (n : ℝ) * (ENNReal.ofReal (Real.sqrt (2048⁻¹ *
            min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1))).toReal ^ 2)) ∧
      2 * (c ^ 2 * (n : ℝ) * (ENNReal.ofReal (Real.sqrt (2048⁻¹ *
          min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1))).toReal ^ 2
          + Real.log 2)
        ≤ Real.log (M : ℝ) := by
  classical
  -- Basic positivity facts.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR : (n : ℝ) ≠ 0 := hnpos.ne'
  have hspos : 0 < s := by omega
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hsR10 : (10 : ℝ) ≤ s := by exact_mod_cast hs0
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hvR : (v : ℝ) ≠ 0 := hvpos.ne'
  have hγpos : (0 : ℝ) < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have hγR : (γ : ℝ) ≠ 0 := hγpos.ne'
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- The log factor `L = log((d−s)/s) ≥ log 7 > 0` (using `8s ≤ d`).
  set L : ℝ := Real.log (((d : ℝ) - s) / s) with hL_def
  have h7le : (7 : ℝ) ≤ ((d : ℝ) - s) / s := by
    rw [le_div_iff₀ hsR]
    have hd8 : (8 : ℝ) * s ≤ d := by exact_mod_cast hds
    linarith
  have hLlb : Real.log 7 ≤ L := by rw [hL_def]; exact Real.log_le_log (by norm_num) h7le
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg (by norm_num)) hLlb
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hLlb
  -- `14 log 2 ≤ 5 log 7 ≤ 5 L` (from `2¹⁴ ≤ 7⁵`).
  have h5L : 14 * Real.log 2 ≤ 5 * L := by
    have h : (2 : ℝ) ^ (14 : ℕ) ≤ (7 : ℝ) ^ (5 : ℕ) := by norm_num
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    linarith [h2, hLlb]
  have hp1 : 0 ≤ (s : ℝ) * (5 * L - 14 * Real.log 2) := mul_nonneg hsR.le (by linarith [h5L])
  have hp2 : 0 ≤ (5 * (s : ℝ) - 32) * Real.log 2 := mul_nonneg (by linarith [hsR10]) hlog2pos.le
  -- The separation radius `δ0 = √δsq`, `δsq = 2048⁻¹·min(t,1)`, and rescale factor `ρ = 4δ0 ≤ 1`.
  set t : ℝ := (v : ℝ) * (s : ℝ) * L / ((γ : ℝ) ^ 2 * n) with ht_def
  have htpos : 0 < t := by
    rw [ht_def]; exact div_pos (mul_pos (mul_pos hvpos hsR) hLpos) (by positivity)
  set δsq : ℝ := 2048⁻¹ * min t 1 with hδsq_def
  have hδsq_pos : 0 < δsq := by rw [hδsq_def]; exact mul_pos (by norm_num) (lt_min htpos (by norm_num))
  have hδsq0 : 0 ≤ δsq := hδsq_pos.le
  have hδsq_le : δsq ≤ 2048⁻¹ := by
    rw [hδsq_def]
    calc 2048⁻¹ * min t 1 ≤ 2048⁻¹ * 1 := by gcongr; exact min_le_right _ _
      _ = 2048⁻¹ := by norm_num
  set δ0 : ℝ := Real.sqrt δsq with hδ0_def
  have hδ0nonneg : 0 ≤ δ0 := Real.sqrt_nonneg _
  have hδ0pos : 0 < δ0 := Real.sqrt_pos.mpr hδsq_pos
  have hδ0sq : δ0 ^ 2 = δsq := Real.sq_sqrt hδsq0
  set ρ : ℝ := 4 * δ0 with hρ_def
  have hρnonneg : 0 ≤ ρ := by rw [hρ_def]; positivity
  have hρne : ρ ≠ 0 := by rw [hρ_def]; positivity
  have hρ2 : ρ ^ 2 = 16 * δsq := by
    rw [hρ_def, show (4 * δ0) ^ 2 = 16 * δ0 ^ 2 from by ring, hδ0sq]
  have hρ_le1 : ρ ≤ 1 := by nlinarith [hρ2, hδsq_le, hρnonneg]
  -- The leakage constant `c = √(32 γ² / v)`.
  set c : ℝ := Real.sqrt (32 * (γ : ℝ) ^ 2 / (v : ℝ)) with hc_def
  have hcsq : c ^ 2 = 32 * (γ : ℝ) ^ 2 / (v : ℝ) := by rw [hc_def]; exact Real.sq_sqrt (by positivity)
  -- The KL/cardinality budget bound `c²·n·δsq ≤ s·L/64`.
  have hcnδ : c ^ 2 * (n : ℝ) * δsq ≤ (s : ℝ) * L / 64 := by
    have hδsqle : δsq ≤ 2048⁻¹ * t := by rw [hδsq_def]; gcongr; exact min_le_left _ _
    calc c ^ 2 * (n : ℝ) * δsq
        ≤ c ^ 2 * (n : ℝ) * (2048⁻¹ * t) := by
          apply mul_le_mul_of_nonneg_left hδsqle (by positivity)
      _ = (s : ℝ) * L / 64 := by rw [hcsq, ht_def]; field_simp; ring
  -- The packing of the sparse unit ball.
  obtain ⟨T, hTcard, hTmem, hTsep⟩ := exists_sparse_packing d s hspos (by omega)
  rw [← hL_def] at hTcard
  set e := T.equivFin with he_def
  set pv : Fin T.card → EuclideanSpace ℝ (Fin d) := fun a => (e.symm a : EuclideanSpace ℝ (Fin d))
    with hpv_def
  have hpv_mem : ∀ a, pv a ∈ T := fun a => (e.symm a).2
  have hpv_unit : ∀ a, ‖pv a‖ = 1 := fun a => (hTmem _ (hpv_mem a)).1
  have hpv_supp : ∀ a, (Finset.univ.filter fun i => pv a i ≠ 0).card ≤ s :=
    fun a => (hTmem _ (hpv_mem a)).2
  have hpv_ne : ∀ a b, a ≠ b → pv a ≠ pv b := by
    intro a b hab hcon
    exact hab (e.symm.injective (Subtype.coe_injective hcon))
  have hpv_sep : ∀ a b, a ≠ b → (1 / 2 : ℝ) ≤ ‖pv a - pv b‖ :=
    fun a b hab => hTsep _ (hpv_mem a) _ (hpv_mem b) (hpv_ne a b hab)
  -- Cardinality is nonzero (the log-cardinality bound is strictly positive).
  have hMne0 : T.card ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, Real.log_zero] at hTcard
    have hslog2 : 0 < (s : ℝ) * Real.log 2 := mul_pos hsR hlog2pos
    nlinarith [hTcard, hp1, hslog2]
  -- The rescaled packing vectors `θvec a = ρ • pv a ∈ SparseBall d s`.
  set θvec : Fin T.card → EuclideanSpace ℝ (Fin d) := fun a => ρ • pv a with hθvec_def
  have hθvec_app : ∀ a, θvec a = ρ • pv a := fun a => rfl
  have hpredeq : ∀ a i, (θvec a i ≠ 0) ↔ (pv a i ≠ 0) := by
    intro a i
    rw [hθvec_app, PiLp.smul_apply, smul_eq_mul, mul_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨hρne, h⟩⟩
  have hfiltereq : ∀ a, (Finset.univ.filter fun i => θvec a i ≠ 0)
      = (Finset.univ.filter fun i => pv a i ≠ 0) := by
    intro a; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpredeq a i
  have hθvec_supp : ∀ a, (Finset.univ.filter fun i => θvec a i ≠ 0).card ≤ s := by
    intro a; rw [hfiltereq a]; exact hpv_supp a
  have hθvec_norm : ∀ a, ‖θvec a‖ = ρ := by
    intro a
    rw [hθvec_app, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρnonneg, hpv_unit a, mul_one]
  have hmem : ∀ a, θvec a ∈ SparseBall d s := by
    intro a
    refine ⟨hθvec_supp a, ?_⟩
    rw [hθvec_norm a]; exact hρ_le1
  set θfam : Fin T.card → SparseBall d s := fun a => ⟨θvec a, hmem a⟩ with hθfam_def
  have hθ : Measurable θfam := measurable_of_countable _
  have hvj : ∀ a, (θfam a).val = θvec a := fun a => rfl
  -- Norms of rescaled differences.
  have hsubsmul : ∀ j k, θvec j - θvec k = ρ • (pv j - pv k) := by
    intro j k; rw [hθvec_app j, hθvec_app k, ← smul_sub]
  have hsubnorm : ∀ j k, ‖θvec j - θvec k‖ = ρ * ‖pv j - pv k‖ := by
    intro j k
    rw [hsubsmul j k, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρnonneg]
  have hsupp2s : ∀ j k, (Finset.univ.filter fun i => (θvec j - θvec k) i ≠ 0).card ≤ 2 * s := by
    intro j k
    calc (Finset.univ.filter fun i => (θvec j - θvec k) i ≠ 0).card
        ≤ (Finset.univ.filter fun i => θvec j i ≠ 0).card
            + (Finset.univ.filter fun i => θvec k i ≠ 0).card := card_filter_sub_le _ _
      _ ≤ s + s := Nat.add_le_add (hθvec_supp j) (hθvec_supp k)
      _ = 2 * s := by ring
  have hpvsub_le : ∀ j k, ‖pv j - pv k‖ ≤ 2 := by
    intro j k
    calc ‖pv j - pv k‖ ≤ ‖pv j‖ + ‖pv k‖ := norm_sub_le _ _
      _ = 2 := by rw [hpv_unit j, hpv_unit k]; norm_num
  refine ⟨T.card, ⟨hMne0⟩, θfam, hθ, c, ?_, ?_, ?_⟩
  · -- (separation) `IsSeparatedFamily`.
    intro j k hjk
    rw [show (2 : ℝ≥0∞) * ENNReal.ofReal δ0 = ENNReal.ofReal (2 * δ0) from by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat],
        edist_dist, dist_eq_norm, hvj j, hvj k]
    apply ENNReal.ofReal_le_ofReal
    rw [hsubnorm j k, hρ_def]
    nlinarith [mul_nonneg hδ0nonneg
      (by linarith [hpv_sep j k hjk] : (0 : ℝ) ≤ 2 * ‖pv j - pv k‖ - 1)]
  · -- (15.35a) pairwise KL bound.
    intro j k hjk
    simp only [Kernel.comap_apply, hP]
    rw [hvj j, hvj k,
        show ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = (v • (1 : Matrix (Fin n) (Fin n) ℝ))
          from (NNReal.smul_def v _).symm,
        klDiv_multivariateGaussian_smul_one (A (θvec j)) (A (θvec k)) v hv]
    apply ENNReal.ofReal_le_ofReal
    rw [ENNReal.toReal_ofReal hδ0nonneg, ← map_sub]
    have hnormle : ‖A (θvec j - θvec k)‖ ≤ Real.sqrt n * (γ : ℝ) * (8 * δ0) := by
      calc ‖A (θvec j - θvec k)‖
          ≤ Real.sqrt n * (γ : ℝ) * ‖θvec j - θvec k‖ := hγbd _ (hsupp2s j k)
        _ = Real.sqrt n * (γ : ℝ) * (ρ * ‖pv j - pv k‖) := by rw [hsubnorm j k]
        _ ≤ Real.sqrt n * (γ : ℝ) * (ρ * 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left (hpvsub_le j k) hρnonneg
        _ = Real.sqrt n * (γ : ℝ) * (8 * δ0) := by rw [hρ_def]; ring
    have hAsq : ‖A (θvec j - θvec k)‖ ^ 2 ≤ (n : ℝ) * (γ : ℝ) ^ 2 * (64 * δ0 ^ 2) := by
      have hrhs0 : (0 : ℝ) ≤ Real.sqrt n * (γ : ℝ) * (8 * δ0) :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) γ.coe_nonneg)
          (mul_nonneg (by norm_num) hδ0nonneg)
      have hms := mul_le_mul hnormle hnormle (norm_nonneg _) hrhs0
      have hsqn : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hnpos.le
      rw [pow_two]
      calc ‖A (θvec j - θvec k)‖ * ‖A (θvec j - θvec k)‖
          ≤ (Real.sqrt n * (γ : ℝ) * (8 * δ0)) * (Real.sqrt n * (γ : ℝ) * (8 * δ0)) := hms
        _ = (n : ℝ) * (γ : ℝ) ^ 2 * (64 * δ0 ^ 2) := by
            rw [show (Real.sqrt n * (γ : ℝ) * (8 * δ0)) * (Real.sqrt n * (γ : ℝ) * (8 * δ0))
                = (Real.sqrt n * Real.sqrt n) * ((γ : ℝ) ^ 2 * (64 * δ0 ^ 2)) from by ring, hsqn]
            ring
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (v : ℝ))]
    have hrhseq : c ^ 2 * (n : ℝ) * δ0 ^ 2 * (2 * (v : ℝ))
        = (n : ℝ) * (γ : ℝ) ^ 2 * (64 * δ0 ^ 2) := by
      rw [hcsq]; field_simp; ring
    rw [hrhseq]; exact hAsq
  · -- (15.35b) cardinality.
    rw [ENNReal.toReal_ofReal hδ0nonneg, hδ0sq]
    nlinarith [hTcard, hcnδ, hp1, hp2, hlog2pos]

/-- **Minimax risk for sparse linear regression** (Wainwright Example 15.16): for the fixed-design
Gaussian model with design map `A : ℝᵈ → ℝⁿ`, noise variance `v`, and `2s`-restricted singular value
`γ`, the minimax risk over the `s`-sparse unit ball `S_d(s)` in squared Euclidean error is at least
`c·min(v·s·log((d−s)/s)/(γ²n), 1)`, witnessed by a `1/2`-packing of `S_d(s)` rescaled into the ball
(the `min(·,1)` is the bounded-ball cap).

The leading constant is loosened from the book's (CLAUDE.md §1), forced by the
`(s/2)log((d−s)/s) − s·log2` sparse-packing brick; the result holds for `10 ≤ s` and `8s ≤ d`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3, Example 15.16. -/
theorem sparse_linear_regression_minimax_rate {n d s : ℕ} (hn : 1 ≤ n)
    -- LEAN-ONLY: 10 ≤ s — the local-packing/Fano cardinality (15.35b) is vacuous for small s; the book's range is 10 ≤ s ≤ d/2.
    (hs0 : 10 ≤ s)
    -- LEAN-ONLY: 8s ≤ d — stronger than the book's s ≤ d/2, to absorb the −s·log2 slack in the sparse-packing brick.
    (hds : 8 * s ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (γ : ℝ≥0) (hγ : γ ≠ 0)
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    -- USER-INPUT: `γ` is the `2s`-restricted singular value `γ₂ₛ = max_{|T|=2s} σ_max(X_T)/√n`; Wainwright Ex 15.16.
    (hγbd : ∀ θ : EuclideanSpace ℝ (Fin d),
        (Finset.univ.filter fun i => θ i ≠ 0).card ≤ 2 * s → ‖A θ‖ ≤ Real.sqrt (n : ℝ) * (γ : ℝ) * ‖θ‖)
    (P : Kernel (SparseBall d s) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel P]
    -- USER-INPUT: `y ∼ 𝒩(Aθ, v Iₙ)` (fixed-design Gaussian model); Wainwright §15.3.3, Ex 15.16.
    (hP : ∀ θ, P θ = multivariateGaussian (A (θ : EuclideanSpace ℝ (Fin d)))
            ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    ENNReal.ofReal (4096⁻¹ *
        min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1)
      ≤ minimaxRiskDist (· ^ 2) Subtype.val P := by
  have hspos : 0 < s := by omega
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h7le : (7 : ℝ) ≤ ((d : ℝ) - s) / s := by
    rw [le_div_iff₀ hsR]
    have hd8 : (8 : ℝ) * s ≤ d := by exact_mod_cast hds
    linarith
  have hL0 : 0 ≤ Real.log (((d : ℝ) - s) / s) := Real.log_nonneg (by linarith)
  have ht0 : 0 ≤ (v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n) :=
    div_nonneg (mul_nonneg (mul_nonneg v.coe_nonneg hsR.le) hL0) (by positivity)
  have hms : (0 : ℝ) ≤ 2048⁻¹ *
      min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1 :=
    mul_nonneg (by norm_num) (le_min ht0 (by norm_num))
  obtain ⟨M, hMne, θfam, hθ, c, hsep, h35a, h35b⟩ :=
    sparse_linreg_local_packing_data hn hs0 hds v hv γ hγ A hγbd P hP
  haveI := hMne
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have key := minimax_local_packing (fun x : ℝ≥0∞ => x ^ 2) Subtype.val P θfam hθ
    (ENNReal.ofReal (Real.sqrt (2048⁻¹ *
      min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1)))
    c (n : ℝ) hΦ hsep (by positivity) h35a h35b
  have hΦδ : (fun x : ℝ≥0∞ => x ^ 2) (ENNReal.ofReal (Real.sqrt (2048⁻¹ *
        min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1)))
      = ENNReal.ofReal (2048⁻¹ *
        min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1) := by
    change (ENNReal.ofReal (Real.sqrt (2048⁻¹ *
      min ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / ((γ : ℝ) ^ 2 * n)) 1))) ^ 2 = _
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hms]
  beta_reduce at hΦδ
  rw [hΦδ] at key
  refine le_trans ?_ key
  have h2inv : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [h2inv, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  apply le_of_eq; congr 1; ring

end StatLean.Minimaxity
