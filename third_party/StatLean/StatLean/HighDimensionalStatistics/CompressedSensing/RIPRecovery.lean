module
public import StatLean.HighDimensionalStatistics.CompressedSensing.ConeTheorem
public import StatLean.HighDimensionalStatistics.ForMathlib.TopK

@[expose] public section

/-!
# Perfect recovery under the Restricted Isometry Property

Let $X \in \mathbb{R}^{n \times d}$ be a design (measurement) matrix and let $\beta^\star
\in \mathbb{R}^d$ be an $s$-sparse signal observed through $Y = X\beta^\star$. Suppose $X$
satisfies the $3s$-Restricted Isometry Property (RIP) with constant $\delta_{3s} < 1/3$,
i.e. for every $3s$-sparse vector $v$,
$$ (1-\delta_{3s})\,\|v\|_2^2 \;\le\; \|Xv\|_2^2 \;\le\; (1+\delta_{3s})\,\|v\|_2^2 . $$
Then the basis-pursuit program ($\ell_1$-minimization subject to $X\beta = Y$) recovers
$\beta^\star$ exactly: $\beta^\star$ is the **unique** minimizer, so $\hat\beta =
\beta^\star$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 9 (Restricted Isometry Property), §9.1, Theorem 9.1
(Perfect Recovery Under RIP). The textbook states
the threshold as $\delta_{3s} < 1/3$ on the $3s$-RIP constant; the Lean statement adds the
positivity normalization $0 < \delta$ (a harmless side condition, since the RIP constant
is nonnegative and the case $\delta = 0$ is degenerate).

**Proof formalization notes.** Write $\Delta = \hat\beta - \beta^\star \in \mathrm{Null}(X)$.
Optimality of $\hat\beta$ gives the cone membership $\Delta \in C(S)$, i.e.
$\|\Delta_{S^c}\|_1 \le \|\Delta_S\|_1$ (`deviation_mem_cone_of_basisPursuit`). Shell the
tail $\Delta_{S^c}$ into ordered $2s$-blocks $B_0, B_1, B_2, \dots$ by decreasing absolute
value (`orderedBlocks`, `TopK.lean`). Applying the $3s$-RIP to the head $S \cup B_0$
against the tail blocks gives, in $\ell_2$,
$\sqrt{1-\delta_{3s}}\,\|\Delta_{S\cup B_0}\|_2 \le \sqrt{1+\delta_{3s}}\sum_{j\ge 1}
\|B_j\|_2$. Bridging $\ell_2 \leftrightarrow \ell_1$ via the block monotonicity
$\|B_{j+1}\|_2 \le \tfrac{1}{\sqrt{2s}}\|B_j\|_1$ and $\|\Delta_S\|_1 \le \sqrt{s}\,
\|\Delta_S\|_2$ yields the contraction
$$ \|\Delta_S\|_1 \;\le\; \sqrt{\tfrac{1+\delta_{3s}}{2(1-\delta_{3s})}}\,\|\Delta_{S^c}\|_1 ,$$
whose ratio is $< 1$ exactly when $\delta_{3s} < 1/3$. Combined with the cone bound
$\|\Delta_{S^c}\|_1 \le \|\Delta_S\|_1$ this forces $\|\Delta_S\|_1 = 0$, hence $\Delta = 0$
and $\hat\beta = \beta^\star$.

**Bibliographic comments.** The Restricted Isometry Property and the idea of certifying
$\ell_1$ recovery through restricted isometry constants originate with E. J. Candès and
T. Tao, "Decoding by linear programming," *IEEE Transactions on Information Theory*,
51(12):4203–4215, 2005 (which proves exact $\ell_1$ recovery under a condition on the
restricted isometry constants, $\delta_{3S} + 3\delta_{4S} < 2$). The clean single-constant
sufficient condition was sharpened by E. J. Candès, "The restricted isometry property and
its implications for compressed sensing," *Comptes Rendus de l'Académie des Sciences,
Paris, Série I*, 346:589–592, 2008, which obtains exact recovery under $\delta_{2s} <
\sqrt 2 - 1$. The $3s$-RIP form with the threshold $\delta_{3s} < 1/3$ used here is a
standard variant of these results (the precise constant is presentation-dependent and not
a verbatim theorem of either original paper).
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-! ## File-local bricks -/

/-- A vector with vanishing ℓ¹ norm is zero (each `|xᵢ|` is a nonnegative summand of `0`). -/
private lemma eq_zero_of_l1Norm_eq_zero {x : EuclideanSpace ℝ (Fin d)} (h : l1Norm x = 0) :
    x = 0 := by
  have hsum : ∑ i, |x.ofLp i| = 0 := h
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin d)), |x.ofLp i| = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)).mp hsum
  apply WithLp.ofLp_injective 2
  funext i
  have hi : x.ofLp i = 0 := abs_eq_zero.mp (hz i (Finset.mem_univ i))
  simpa using hi

/-- The support restriction is idempotent: `(x|_S)|_S = x|_S`. -/
private lemma restrict_idem (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    restrict S (restrict S x) = restrict S x := by
  apply WithLp.ofLp_injective 2
  funext i
  simp only [restrict_ofLp_apply]
  split_ifs <;> rfl

/-- `x|_T` is `m`-sparse whenever `T` has at most `m` coordinates. -/
private lemma isSparse_restrict {T : Finset (Fin d)} {m : ℕ} (h : T.card ≤ m)
    (x : EuclideanSpace ℝ (Fin d)) : IsSparse m (restrict T x) :=
  ⟨T, h, fun i hi => by rw [restrict_ofLp_apply, if_neg hi]⟩

/-- The first `N` shelling blocks cover the complement `Sᶜ` (when `N·k ≥ |Sᶜ|`). -/
private lemma blocks_biUnion_compl (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    {k N : ℕ} (hk : 0 < k) (hN : Sᶜ.card ≤ N * k) :
    (Finset.range N).biUnion (fun j => orderedBlocks S x k j) = Sᶜ := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨j, _, hij⟩ := hi
    exact orderedBlocks_subset_compl S x k j hij
  · intro hi
    rw [Finset.mem_biUnion]
    have hiS : i ∉ S := Finset.mem_compl.mp hi
    obtain ⟨m, hm⟩ := mem_orderedBlocks_of_notMem S x hk hiS
    have hmlt : m < N := by
      by_contra hge
      push_neg at hge
      have hempty : orderedBlocks S x k m = ∅ :=
        orderedBlocks_eq_empty S x hk (le_trans hN (Nat.mul_le_mul_right k hge))
      rw [hempty] at hm
      exact absurd hm (Finset.notMem_empty i)
    exact ⟨m, Finset.mem_range.mpr hmlt, hm⟩

/-- The block ℓ¹ masses sum to the complement ℓ¹ mass (the blocks partition `Sᶜ`). -/
private lemma l1Norm_blocks_sum (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    {k N : ℕ} (hk : 0 < k) (hN : Sᶜ.card ≤ N * k) :
    ∑ j ∈ Finset.range N, l1Norm (restrict (orderedBlocks S x k j) x)
      = l1Norm (restrict Sᶜ x) := by
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (fun j => orderedBlocks S x k j) := by
    intro a _ b _ hab
    exact orderedBlocks_disjoint S x k hab
  simp_rw [l1Norm_restrict_eq_sum]
  rw [← Finset.sum_biUnion hdisj, blocks_biUnion_compl S x hk hN]

/-- **Head + tail decomposition.** With `T₀ = S ∪ B₀`, the head restriction plus the
tail blocks `B₁, B₂, …` (over `range N`, `N·k ≥ |Sᶜ|`) reconstruct `x`. -/
private lemma restrict_head_add_tail (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    {k N : ℕ} (hk : 0 < k) (hN : Sᶜ.card ≤ N * k) :
    restrict (S ∪ orderedBlocks S x k 0) x
      + ∑ j ∈ Finset.range N, restrict (orderedBlocks S x k (j + 1)) x = x := by
  apply WithLp.ofLp_injective 2
  funext i
  simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
    restrict_ofLp_apply]
  by_cases hiS : i ∈ S
  · rw [if_pos (Finset.mem_union_left _ hiS)]
    rw [Finset.sum_eq_zero (fun j _ => if_neg (fun hcon =>
      absurd hiS (Finset.mem_compl.mp (orderedBlocks_subset_compl S x k (j + 1) hcon))))]
    rw [add_zero]
  · by_cases hiB0 : i ∈ orderedBlocks S x k 0
    · rw [if_pos (Finset.mem_union_right _ hiB0)]
      rw [Finset.sum_eq_zero (fun j _ => if_neg (fun hcon =>
        Finset.disjoint_left.mp
          (orderedBlocks_disjoint S x k (by omega : (0 : ℕ) ≠ j + 1)) hiB0 hcon))]
      rw [add_zero]
    · rw [if_neg (by rw [Finset.mem_union]; push_neg; exact ⟨hiS, hiB0⟩)]
      obtain ⟨m, hm⟩ := mem_orderedBlocks_of_notMem S x hk hiS
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · exact absurd (h0 ▸ hm) hiB0
        · exact hpos
      have hmlt : m < N := by
        by_contra hge
        push_neg at hge
        have hempty : orderedBlocks S x k m = ∅ :=
          orderedBlocks_eq_empty S x hk (le_trans hN (Nat.mul_le_mul_right k hge))
        rw [hempty] at hm
        exact absurd hm (Finset.notMem_empty i)
      obtain ⟨j₀, rfl⟩ : ∃ j₀, m = j₀ + 1 := ⟨m - 1, by omega⟩
      rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_range.mpr (by omega))
        (fun j _ hjne => if_neg (fun hcon =>
          Finset.disjoint_left.mp
            (orderedBlocks_disjoint S x k (by omega : j + 1 ≠ j₀ + 1)) hcon hm))]
      rw [if_pos hm, zero_add]

/-! ## The null-space-property core -/

/-- **RIP ⟹ trivial cone–nullspace intersection** (Lu-BDA §9.1, Theorem 9.1 core). If
`S.card ≤ s` and `X` is `3s`-RIP with `0 < δ < 1/3`, then the cone `C(S) = reCone S 1`
meets `Null(X)` only at `0`. This is the null-space property feeding
`unique_basisPursuit_of_cone_trivial`. -/
private lemma rip_cone_trivial
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) (s : ℕ) (δ : ℝ)
    -- USER-INPUT: S contains the support, |S| ≤ s; Lu-BDA §9.1, Theorem 9.1
    (hScard : S.card ≤ s)
    -- USER-INPUT: X satisfies the 3s-RIP with constant δ; Lu-BDA §9.1, Theorem 9.1
    (hRIP : IsRIP X (3 * s) δ)
    -- USER-INPUT: 0 < δ; Lu-BDA §9.1, Theorem 9.1
    (hδ0 : 0 < δ)
    -- USER-INPUT: δ < 1/3 (the contraction threshold); Lu-BDA §9.1, Theorem 9.1
    (hδ : δ < 1 / 3) :
    reCone S 1 ∩ (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) = {0} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨?_, ?_⟩
  · -- `0` lies in the intersection.
    refine Set.mem_inter ?_ ?_
    · simp only [reCone, Set.mem_setOf_eq]
      simp [l1Norm_restrict_eq_sum]
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_zero]
  · intro Δ hΔ
    obtain ⟨hcone, hker'⟩ := hΔ
    have hcone' : l1Norm (restrict Sᶜ Δ) ≤ 1 * l1Norm (restrict S Δ) := hcone
    have hker : designMap X Δ = 0 := by
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hker'; exact hker'
    -- The crux: the ℓ¹ mass on `S` vanishes.
    have ha : l1Norm (restrict S Δ) = 0 := by
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · -- `s = 0` ⟹ `S = ∅`, so the `S`-restriction is already trivial.
        have hSempty : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hs0 ▸ hScard))
        rw [hSempty, l1Norm_restrict_eq_sum]; simp
      · -- `0 < s`: run the shelling contraction.
        set k := 2 * s with hk_def
        have hk : 0 < k := by rw [hk_def]; omega
        have hN : Sᶜ.card ≤ Sᶜ.card * k := Nat.le_mul_of_pos_right _ hk
        have hdecomp := restrict_head_add_tail S Δ hk hN
        have hblocksum := l1Norm_blocks_sum S Δ hk hN
        set T₀set := S ∪ orderedBlocks S Δ k 0 with hT0
        -- Sparsity witnesses for the head and the tail blocks.
        have hcardT0 : T₀set.card ≤ 3 * s := by
          rw [hT0]
          calc (S ∪ orderedBlocks S Δ k 0).card
              ≤ S.card + (orderedBlocks S Δ k 0).card := Finset.card_union_le _ _
            _ ≤ s + k := Nat.add_le_add hScard (orderedBlocks_card_le S Δ k 0)
            _ = 3 * s := by rw [hk_def]; ring
        have hsph : IsSparse (3 * s) (restrict T₀set Δ) := isSparse_restrict hcardT0 Δ
        have hsparse_tail : ∀ j, IsSparse (3 * s) (restrict (orderedBlocks S Δ k (j + 1)) Δ) :=
          fun j => isSparse_restrict
            (le_trans (orderedBlocks_card_le S Δ k (j + 1)) (by rw [hk_def]; omega)) Δ
        -- Square-root constants.
        set p := Real.sqrt (1 - δ) with hp_def
        set q := Real.sqrt (1 + δ) with hq_def
        set rs := Real.sqrt (s : ℝ) with hrs_def
        set rk := Real.sqrt (k : ℝ) with hrk_def
        have hp_nonneg : 0 ≤ p := by rw [hp_def]; exact Real.sqrt_nonneg _
        have hq_nonneg : 0 ≤ q := by rw [hq_def]; exact Real.sqrt_nonneg _
        have hrs_nonneg : 0 ≤ rs := by rw [hrs_def]; exact Real.sqrt_nonneg _
        have hrk_nonneg : 0 ≤ rk := by rw [hrk_def]; exact Real.sqrt_nonneg _
        have rs_pos : 0 < rs := by
          rw [hrs_def]; exact Real.sqrt_pos.mpr (by exact_mod_cast hs0)
        have hrk_rs : rk = Real.sqrt 2 * rs := by
          rw [hrk_def, hrs_def, show ((k : ℕ) : ℝ) = 2 * (s : ℝ) by rw [hk_def]; push_cast; ring,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        -- Block ℓ²→ℓ¹ shift: `rk·‖B_{j+1}‖₂ ≤ ‖B_j‖₁`.
        have hblock : ∀ j, rk * ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖
            ≤ l1Norm (restrict (orderedBlocks S Δ k j) Δ) := by
          intro j
          have hb1 : ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖
              ≤ Real.sqrt ((orderedBlocks S Δ k (j + 1)).card : ℝ)
                * linfNorm (restrict (orderedBlocks S Δ k (j + 1)) Δ) :=
            norm_le_sqrt_card_mul_linfNorm _ _
          have hcard : Real.sqrt ((orderedBlocks S Δ k (j + 1)).card : ℝ) ≤ rk := by
            rw [hrk_def]
            exact Real.sqrt_le_sqrt (by exact_mod_cast orderedBlocks_card_le S Δ k (j + 1))
          have hlinf_nn : 0 ≤ linfNorm (restrict (orderedBlocks S Δ k (j + 1)) Δ) :=
            linfNorm_nonneg _
          have hb1' : ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖
              ≤ rk * linfNorm (restrict (orderedBlocks S Δ k (j + 1)) Δ) :=
            le_trans hb1 (mul_le_mul_of_nonneg_right hcard hlinf_nn)
          have hb2 : linfNorm (restrict (orderedBlocks S Δ k (j + 1)) Δ)
              ≤ (1 / (k : ℝ)) * l1Norm (restrict (orderedBlocks S Δ k j) Δ) :=
            linfNorm_restrict_orderedBlocks_succ_le S Δ hk j
          have hrk2 : rk * rk = (k : ℝ) := by rw [hrk_def]; exact Real.mul_self_sqrt (by positivity)
          have hkR0 : (k : ℝ) ≠ 0 := by
            have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
            exact hkpos.ne'
          calc rk * ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖
              ≤ rk * (rk * linfNorm (restrict (orderedBlocks S Δ k (j + 1)) Δ)) :=
                mul_le_mul_of_nonneg_left hb1' hrk_nonneg
            _ = (k : ℝ) * linfNorm (restrict (orderedBlocks S Δ k (j + 1)) Δ) := by
                rw [← mul_assoc, hrk2]
            _ ≤ (k : ℝ) * ((1 / (k : ℝ)) * l1Norm (restrict (orderedBlocks S Δ k j) Δ)) :=
                mul_le_mul_of_nonneg_left hb2 (by positivity)
            _ = l1Norm (restrict (orderedBlocks S Δ k j) Δ) := by field_simp
        -- RIP head-vs-tail: `p·‖head‖₂ ≤ q·∑‖B_{j+1}‖₂`.
        have hA : p * ‖restrict T₀set Δ‖
            ≤ q * (∑ j ∈ Finset.range (Sᶜ.card),
                ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖) := by
          have hmap0 : designMap X (restrict T₀set Δ)
              + ∑ j ∈ Finset.range (Sᶜ.card),
                  designMap X (restrict (orderedBlocks S Δ k (j + 1)) Δ) = 0 := by
            have h := congrArg (designMap X) hdecomp
            rw [map_add, map_sum, hker] at h
            exact h
          have hmapeq : designMap X (restrict T₀set Δ)
              = - ∑ j ∈ Finset.range (Sᶜ.card),
                  designMap X (restrict (orderedBlocks S Δ k (j + 1)) Δ) :=
            eq_neg_of_add_eq_zero_left hmap0
          have hnorm_head : ‖designMap X (restrict T₀set Δ)‖
              ≤ ∑ j ∈ Finset.range (Sᶜ.card),
                  ‖designMap X (restrict (orderedBlocks S Δ k (j + 1)) Δ)‖ := by
            rw [hmapeq, norm_neg]; exact norm_sum_le _ _
          have hlow : p * ‖restrict T₀set Δ‖ ≤ ‖designMap X (restrict T₀set Δ)‖ := by
            have hr := (hRIP (restrict T₀set Δ) hsph).1
            have e : p * ‖restrict T₀set Δ‖
                = Real.sqrt ((1 - δ) * ‖restrict T₀set Δ‖ ^ 2) := by
              rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 - δ),
                Real.sqrt_sq (norm_nonneg _), hp_def]
            rw [e]
            calc Real.sqrt ((1 - δ) * ‖restrict T₀set Δ‖ ^ 2)
                ≤ Real.sqrt (‖designMap X (restrict T₀set Δ)‖ ^ 2) := Real.sqrt_le_sqrt hr
              _ = ‖designMap X (restrict T₀set Δ)‖ := Real.sqrt_sq (norm_nonneg _)
          have hup : ∀ j ∈ Finset.range (Sᶜ.card),
              ‖designMap X (restrict (orderedBlocks S Δ k (j + 1)) Δ)‖
                ≤ q * ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖ := by
            intro j _
            have hr := (hRIP (restrict (orderedBlocks S Δ k (j + 1)) Δ) (hsparse_tail j)).2
            have e : q * ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖
                = Real.sqrt ((1 + δ) * ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖ ^ 2) := by
              rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 + δ),
                Real.sqrt_sq (norm_nonneg _), hq_def]
            rw [e]
            calc ‖designMap X (restrict (orderedBlocks S Δ k (j + 1)) Δ)‖
                = Real.sqrt (‖designMap X (restrict (orderedBlocks S Δ k (j + 1)) Δ)‖ ^ 2) :=
                  (Real.sqrt_sq (norm_nonneg _)).symm
              _ ≤ Real.sqrt ((1 + δ) * ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖ ^ 2) :=
                  Real.sqrt_le_sqrt hr
          calc p * ‖restrict T₀set Δ‖
              ≤ ‖designMap X (restrict T₀set Δ)‖ := hlow
            _ ≤ ∑ j ∈ Finset.range (Sᶜ.card),
                  ‖designMap X (restrict (orderedBlocks S Δ k (j + 1)) Δ)‖ := hnorm_head
            _ ≤ ∑ j ∈ Finset.range (Sᶜ.card),
                  q * ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖ := Finset.sum_le_sum hup
            _ = q * (∑ j ∈ Finset.range (Sᶜ.card),
                  ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖) := by rw [Finset.mul_sum]
        -- Collapse the tail sum: `rk·∑‖B_{j+1}‖₂ ≤ ‖Δ_{Sᶜ}‖₁`.
        have hrkTnorm : rk * (∑ j ∈ Finset.range (Sᶜ.card),
            ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖) ≤ l1Norm (restrict Sᶜ Δ) := by
          rw [Finset.mul_sum]
          calc ∑ j ∈ Finset.range (Sᶜ.card),
                rk * ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖
              ≤ ∑ j ∈ Finset.range (Sᶜ.card),
                  l1Norm (restrict (orderedBlocks S Δ k j) Δ) :=
                Finset.sum_le_sum (fun j _ => hblock j)
            _ = l1Norm (restrict Sᶜ Δ) := hblocksum
        -- Lower bound the head: `‖Δ_S‖₁ ≤ rs·‖head‖₂`.
        have hC : l1Norm (restrict S Δ) ≤ rs * ‖restrict T₀set Δ‖ := by
          have hidem : restrict S (restrict S Δ) = restrict S Δ := restrict_idem S Δ
          have h1 : l1Norm (restrict S Δ) ≤ Real.sqrt (S.card : ℝ) * ‖restrict S Δ‖ := by
            have h := l1Norm_restrict_le_sqrt_card_mul_norm S (restrict S Δ)
            rwa [hidem] at h
          have h2 : Real.sqrt (S.card : ℝ) ≤ rs := by
            rw [hrs_def]; exact Real.sqrt_le_sqrt (by exact_mod_cast hScard)
          have h3 : ‖restrict S Δ‖ ≤ ‖restrict T₀set Δ‖ := by
            have hsub : S ⊆ T₀set := by rw [hT0]; exact Finset.subset_union_left
            exact norm_restrict_le_of_subset hsub Δ
          calc l1Norm (restrict S Δ)
              ≤ Real.sqrt (S.card : ℝ) * ‖restrict S Δ‖ := h1
            _ ≤ rs * ‖restrict S Δ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
            _ ≤ rs * ‖restrict T₀set Δ‖ := mul_le_mul_of_nonneg_left h3 hrs_nonneg
        -- Fold the head norm and the tail sum into opaque reals.
        set T := ‖restrict T₀set Δ‖ with hT_def
        set Tnorm := ∑ j ∈ Finset.range (Sᶜ.card),
          ‖restrict (orderedBlocks S Δ k (j + 1)) Δ‖ with hTnorm_def
        -- Chain the three estimates (clearing denominators).
        have hPT : rk * p * T ≤ q * l1Norm (restrict Sᶜ Δ) := by
          calc rk * p * T = rk * (p * T) := by ring
            _ ≤ rk * (q * Tnorm) := mul_le_mul_of_nonneg_left hA hrk_nonneg
            _ = q * (rk * Tnorm) := by ring
            _ ≤ q * l1Norm (restrict Sᶜ Δ) := mul_le_mul_of_nonneg_left hrkTnorm hq_nonneg
        have hPA : rk * p * l1Norm (restrict S Δ)
            ≤ rs * (q * l1Norm (restrict Sᶜ Δ)) := by
          calc rk * p * l1Norm (restrict S Δ) = (rk * p) * l1Norm (restrict S Δ) := by ring
            _ ≤ (rk * p) * (rs * T) :=
                mul_le_mul_of_nonneg_left hC (mul_nonneg hrk_nonneg hp_nonneg)
            _ = rs * (rk * p * T) := by ring
            _ ≤ rs * (q * l1Norm (restrict Sᶜ Δ)) := mul_le_mul_of_nonneg_left hPT hrs_nonneg
        have hfinal : Real.sqrt 2 * p * l1Norm (restrict S Δ)
            ≤ q * l1Norm (restrict Sᶜ Δ) := by
          have hcancel : rs * (Real.sqrt 2 * p * l1Norm (restrict S Δ))
              ≤ rs * (q * l1Norm (restrict Sᶜ Δ)) := by
            have hre : rs * (Real.sqrt 2 * p * l1Norm (restrict S Δ))
                = rk * p * l1Norm (restrict S Δ) := by rw [hrk_rs]; ring
            rw [hre]; exact hPA
          exact le_of_mul_le_mul_left hcancel rs_pos
        -- Endgame: `δ < 1/3` forces `‖Δ_S‖₁ = 0`.
        have hba : l1Norm (restrict Sᶜ Δ) ≤ l1Norm (restrict S Δ) := by
          rw [one_mul] at hcone'; exact hcone'
        have ha_nn : 0 ≤ l1Norm (restrict S Δ) := l1Norm_nonneg _
        have hqle : q * l1Norm (restrict Sᶜ Δ) ≤ q * l1Norm (restrict S Δ) :=
          mul_le_mul_of_nonneg_left hba hq_nonneg
        have hkey : Real.sqrt 2 * p * l1Norm (restrict S Δ)
            ≤ q * l1Norm (restrict S Δ) := le_trans hfinal hqle
        rcases eq_or_lt_of_le ha_nn with h0 | hpos
        · exact h0.symm
        · exfalso
          have hsq2p_le_q : Real.sqrt 2 * p ≤ q := le_of_mul_le_mul_right hkey hpos
          have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          have hp2 : p * p = 1 - δ := by rw [hp_def]; exact Real.mul_self_sqrt (by linarith)
          have hq2 : q * q = 1 + δ := by rw [hq_def]; exact Real.mul_self_sqrt (by linarith)
          have hnn : 0 ≤ Real.sqrt 2 * p := mul_nonneg (Real.sqrt_nonneg _) hp_nonneg
          have hmm := mul_le_mul hsq2p_le_q hsq2p_le_q hnn hq_nonneg
          have hlhs : (Real.sqrt 2 * p) * (Real.sqrt 2 * p) = 2 * (1 - δ) := by
            have hr : (Real.sqrt 2 * p) * (Real.sqrt 2 * p)
                = (Real.sqrt 2 * Real.sqrt 2) * (p * p) := by ring
            rw [hr, h2, hp2]
          rw [hlhs, hq2] at hmm
          linarith
    -- From `‖Δ_S‖₁ = 0` (and the cone) conclude `Δ = 0`.
    have hb : l1Norm (restrict Sᶜ Δ) = 0 := by
      have h := hcone'
      rw [ha, mul_zero] at h
      exact le_antisymm h (l1Norm_nonneg _)
    have hS0 : restrict S Δ = 0 := eq_zero_of_l1Norm_eq_zero ha
    have hSc0 : restrict Sᶜ Δ = 0 := eq_zero_of_l1Norm_eq_zero hb
    have hsum := restrict_add_restrict_compl S Δ
    rw [hS0, hSc0, add_zero] at hsum
    exact hsum.symm

/-! ## Main theorem -/

/-- **Perfect Recovery Under RIP** (Lu-BDA §9.1, Theorem 9.1). `3s`-RIP with `δ < 1/3` implies
basis pursuit uniquely recovers every `s`-sparse `β*`.

`δ < 1/3` is the constant on the `3s`-RIP constant `δ_{3s}`; it is exactly the
threshold making the contraction ratio `√((1+δ)/(2(1−δ))) < 1`. -/
theorem basisPursuit_recovers_of_rip
    (X : Matrix (Fin n) (Fin d) ℝ) (s : ℕ) (δ : ℝ)
    -- USER-INPUT: 0 < δ; Lu-BDA §9.1, Theorem 9.1
    (hδ0 : 0 < δ)
    -- USER-INPUT: δ < 1/3 (the 3s-RIP constant threshold); Lu-BDA §9.1, Theorem 9.1
    (hδ : δ < 1 / 3)
    -- USER-INPUT: X satisfies the 3s-RIP with constant δ; Lu-BDA §9.1, Theorem 9.1
    (hRIP : IsRIP X (3 * s) δ)
    (βstar : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: β* is s-sparse; Lu-BDA §9.1, Theorem 9.1
    (hsp : IsSparse s βstar) :
    IsUniqueBasisPursuit X (designMap X βstar) βstar := by
  obtain ⟨S, hScard, hsupp⟩ := hsp
  exact unique_basisPursuit_of_cone_trivial X S
    (rip_cone_trivial X S s δ hScard hRIP hδ0 hδ) βstar hsupp

end StatLean.HighDimensionalStatistics
