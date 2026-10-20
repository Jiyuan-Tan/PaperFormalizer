module
public import StatLean.HighDimensionalStatistics.CompressedSensing.GaussianChiSquared
public import StatLean.HighDimensionalStatistics.CompressedSensing.Defs
public import StatLean.ConcentrationInequalities.Maximal.CoveringBall

@[expose] public section

/-!
# Random Gaussian matrices satisfy the Restricted Isometry Property with high probability

Let $X \in \mathbb{R}^{n \times d}$ be a random matrix whose entries are independent and
identically distributed as $N(0, 1/n)$. If the sample size satisfies
$$ n \;\ge\; \frac{384}{\delta^2}\, s\, \log\!\Big(\frac{18 d}{\varepsilon}\Big), $$
then, with probability at least $1 - \varepsilon$, the matrix $X$ satisfies the restricted
isometry property of order $3s$ with constant $\delta$: for every $3s$-sparse vector $\beta$,
$$ (1 - \delta)\,\|\beta\|^2 \;\le\; \|X\beta\|^2 \;\le\; (1 + \delta)\,\|\beta\|^2 . $$
The result is formalized as `prob_rip_of_iid_gaussian` for $0 < \delta < 1$ and $0 < \varepsilon$,
with the random matrix realized as $X : \Omega \to \mathbb{R}^{n \times d}$ over a probability
space $(\Omega, \mu)$.

**Added hypothesis / changed constant.** The leading constant is $384$ rather than the book's
$96$ (a factor $4$). This is the only deviation from the textbook statement: the multiplier $18$
inside the logarithm and the order $O\big(s \log(d/\varepsilon)\big)$ are unchanged. The factor $4$
comes from the per-vector concentration bound we can actually prove (exponent $n\delta^2/32$
instead of the book's sharp $n\delta^2/8$); see the proof notes below. A larger sample-size
constant only strengthens the hypothesis, so the conclusion remains the book's.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 9 (Restricted Isometry Property), §9.1 (Restricted Isometry
Property), Theorem 9.2.

**Proof formalization notes.**
1. *Fixed `β`:* `‖Xβ‖²/‖β‖² ∼ (1/n)χ²_n` concentrates — `gaussian_quadratic_form_tail`
   (`GaussianChiSquared.lean`): `P(|‖Xβ‖²/‖β‖²−1| > δ) ≤ 2 exp(−nδ²/32)` (the provable `32`,
   off the book's `8` by the χ²₁ sub-exponential parameter `α = 4`).
2. *Net + discretisation* (`exists_quarter_net`, `quadform_le_two_sup_net`): a `1/4`-net of the
   unit ball of each `m`-dimensional coordinate subspace (`m = min(3s,d)`, transported by the
   linear isometry `coordEmb`) has `≤ 9^m` points, and `sup_{ball}|‖X·‖²−‖·‖²| ≤ 2 sup_{net}`.
3. *Union bound* over the `≤ d^m` support-embeddings `×` the `≤ 9^m` net points, each event at
   `δ/2`, gives `P(¬RIP) ≤ 2·(9d)^{3s}·exp(−nδ²/128)` (the per-vector exponent `/32` at `δ/2`).
4. *Sample size* (`sample_size_bound`): `log(18d/ε) = log(9d) + log(2/ε)` makes the union bound
   `≤ ε` once `n ≥ (384/δ²)·s·log(18d/ε)`, so `P(RIP) ≥ μ(¬RIP)ᶜ = 1 − μ(¬RIP) ≥ 1 − ε`.

   *Constant deviation.* The book (Lu §9.1, Theorem 9.2) states `96/δ²` with the sharp per-vector
   exponent `nδ²/8`. We prove only `nδ²/32` (factor `4`), so the provable sample size is
   `384/δ² = 4·96/δ²`. The multiplier `18` and the order `O(s·log(d/ε))` are unchanged; the only
   deviation is `96 → 384`.

**Bibliographic comments.** The restricted isometry property was introduced by E. J. Candès and
T. Tao, "Decoding by linear programming," *IEEE Transactions on Information Theory* 51(12):
4203–4215 (2005), where (together with E. J. Candès, J. Romberg, T. Tao, "Robust uncertainty
principles: exact signal reconstruction from highly incomplete frequency information," *IEEE
Trans. Inf. Theory* 52(2):489–509, 2006) it is shown that suitably normalized Gaussian random
matrices satisfy the RIP with high probability. The concentration-of-measure proof formalized
here — a per-vector chi-squared tail bound combined with a covering/net argument over sparse
coordinate subspaces and a union bound — follows R. Baraniuk, M. Davenport, R. DeVore and
M. Wakin, "A simple proof of the restricted isometry property for random matrices,"
*Constructive Approximation* 28(3):253–263 (2008), Lemma 5.1 and Theorem 5.2.
-/

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal NNReal InnerProductSpace
open StatLean.ConcentrationInequalities

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-! ## Discretisation: a `1/4`-net controls the quadratic form on the whole ball

The geometric core of the random-RIP theorem (Lu §9.1, Theorem 9.2): for a linear map `L` on a
finite-dimensional Euclidean
space, the quadratic form `g(u) = ‖L u‖² − ‖u‖²` over the **whole** closed unit ball is
controlled by its values on a `1/4`-net.  Concretely `sup_ball |g| ≤ 2 · sup_net |g|`.

The proof is the standard discretisation argument: pick a maximiser `u₀` of `|g|` over the
(compact) ball, a net point `v` within `1/4` of it, and telescope
`g(u₀) − g(v) = B(u₀−v, u₀) + B(v, u₀−v)` where `B(x,y) = ⟪Lx,Ly⟫ − ⟪x,y⟫` is the symmetric
bilinear form with `B(w,w) = g(w)`.  The sharp bound `|B(x,y)| ≤ M‖x‖‖y‖` (with
`M = sup_ball |g|`) comes from polarisation + the parallelogram law + degree-2 homogeneity of
`g`, and yields `M ≤ sup_net |g| + M/2`. -/
private lemma quadform_le_two_sup_net
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] F)
    (N : Set (EuclideanSpace ℝ (Fin m)))
    (hNball : N ⊆ Metric.closedBall 0 1)
    (hcover : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1,
      ∃ y ∈ N, dist x y ≤ 1 / 4)
    {c : ℝ}
    (hnet : ∀ v ∈ N, |‖L v‖ ^ 2 - ‖v‖ ^ 2| ≤ c)
    (u : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ ≤ 1) :
    |‖L u‖ ^ 2 - ‖u‖ ^ 2| ≤ 2 * c := by
  set g : EuclideanSpace ℝ (Fin m) → ℝ := fun w => ‖L w‖ ^ 2 - ‖w‖ ^ 2 with hgdef
  set B : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ :=
    fun x y => ⟪L x, L y⟫_ℝ - ⟪x, y⟫_ℝ with hBdef
  -- B(w,w) = g(w)
  have hgB : ∀ w, g w = B w w := by
    intro w
    simp only [hgdef, hBdef, real_inner_self_eq_norm_sq]
  -- bilinearity facts
  have hBsubL : ∀ x y z, B (x - y) z = B x z - B y z := by
    intro x y z
    simp only [hBdef, map_sub, inner_sub_left]; ring
  have hBsubR : ∀ x y z, B x (y - z) = B x y - B x z := by
    intro x y z
    simp only [hBdef, map_sub, inner_sub_right]; ring
  have hBsmul : ∀ (a b : ℝ) x y, B (a • x) (b • y) = a * b * B x y := by
    intro a b x y
    simp only [hBdef, map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  -- polarisation: g(x+y) − g(x−y) = 4·B(x,y)
  have hpolar : ∀ x y, g (x + y) - g (x - y) = 4 * B x y := by
    intro x y
    simp only [hgdef, hBdef, map_add, map_sub, norm_add_sq_real, norm_sub_sq_real]
    ring
  -- compactness: a maximiser u₀ of |g| over the closed unit ball
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hcont : Continuous fun w => |g w| := by
    simp only [hgdef]
    exact (((hLc.norm).pow 2).sub (continuous_norm.pow 2)).abs
  have hcompact : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    isCompact_closedBall 0 1
  have hne : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨u₀, hu₀mem, hu₀max⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  set M := |g u₀| with hMdef
  have hMnonneg : 0 ≤ M := abs_nonneg _
  have hu₀norm : ‖u₀‖ ≤ 1 := by simpa [dist_zero_right] using Metric.mem_closedBall.mp hu₀mem
  have hMmax : ∀ w, ‖w‖ ≤ 1 → |g w| ≤ M := by
    intro w hw
    have hwmem : w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
      simpa [dist_zero_right] using hw
    exact isMaxOn_iff.mp hu₀max w hwmem
  -- degree-2 homogeneity of g
  have hghom : ∀ (t : ℝ) w, g (t • w) = t ^ 2 * g w := by
    intro t w
    simp only [hgdef, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  -- homogeneity bound: |g w| ≤ M · ‖w‖²
  have hghbound : ∀ w, |g w| ≤ M * ‖w‖ ^ 2 := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw0
    · simp [hgdef]
    · have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
      set wh := ‖w‖⁻¹ • w with hwh
      have hwhnorm : ‖wh‖ = 1 := by rw [hwh]; exact norm_smul_inv_norm hw0
      have hwwh : w = ‖w‖ • wh := by
        rw [hwh, smul_smul, mul_inv_cancel₀ hwn, one_smul]
      have hgw : g w = ‖w‖ ^ 2 * g wh := by
        conv_lhs => rw [hwwh]
        rw [hghom]
      rw [hgw, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖w‖ ^ 2)]
      have := hMmax wh (le_of_eq hwhnorm)
      nlinarith [abs_nonneg (g wh), sq_nonneg ‖w‖, this]
  -- sharp bilinear bound: |B x y| ≤ M · ‖x‖ · ‖y‖
  have hsharp : ∀ x y, |B x y| ≤ M * ‖x‖ * ‖y‖ := by
    intro x y
    rcases eq_or_ne x 0 with rfl | hx0
    · have h0 : B 0 y = 0 := by simp [hBdef]
      rw [h0]; simp
    rcases eq_or_ne y 0 with rfl | hy0
    · have h0 : B x 0 = 0 := by simp [hBdef]
      rw [h0]; simp
    have hxn : (0 : ℝ) < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hx0))
    have hyn : (0 : ℝ) < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hy0))
    set xh := ‖x‖⁻¹ • x with hxhdef
    set yh := ‖y‖⁻¹ • y with hyhdef
    have hxhnorm : ‖xh‖ = 1 := by rw [hxhdef]; exact norm_smul_inv_norm hx0
    have hyhnorm : ‖yh‖ = 1 := by rw [hyhdef]; exact norm_smul_inv_norm hy0
    -- unit bound: |B xh yh| ≤ M
    have hunit : |B xh yh| ≤ M := by
      have hpol : B xh yh = (g (xh + yh) - g (xh - yh)) / 4 := by
        rw [hpolar]; ring
      rw [hpol, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      have h1 : |g (xh + yh)| ≤ M * ‖xh + yh‖ ^ 2 := hghbound _
      have h2 : |g (xh - yh)| ≤ M * ‖xh - yh‖ ^ 2 := hghbound _
      have hpar : ‖xh + yh‖ ^ 2 + ‖xh - yh‖ ^ 2 = 2 * (‖xh‖ ^ 2 + ‖yh‖ ^ 2) :=
        parallelogram_law_with_norm ℝ xh yh
      rw [hxhnorm, hyhnorm] at hpar
      have htri : |g (xh + yh) - g (xh - yh)| ≤ |g (xh + yh)| + |g (xh - yh)| := by
        have h := abs_add_le (g (xh + yh)) (-(g (xh - yh)))
        simpa [sub_eq_add_neg, abs_neg] using h
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
      nlinarith [htri, h1, h2, hpar]
    -- scale back
    have hscale : B x y = ‖x‖ * ‖y‖ * B xh yh := by
      have hxy : B x y = B (‖x‖ • xh) (‖y‖ • yh) := by
        congr 1
        · rw [hxhdef, smul_smul, mul_inv_cancel₀ hxn.ne', one_smul]
        · rw [hyhdef, smul_smul, mul_inv_cancel₀ hyn.ne', one_smul]
      rw [hxy, hBsmul]
    rw [hscale, abs_mul, abs_mul, abs_of_pos hxn, abs_of_pos hyn]
    calc ‖x‖ * ‖y‖ * |B xh yh| ≤ ‖x‖ * ‖y‖ * M :=
          mul_le_mul_of_nonneg_left hunit (by positivity)
      _ = M * ‖x‖ * ‖y‖ := by ring
  -- telescoping at the maximiser
  obtain ⟨v, hvN, hdist⟩ := hcover u₀ hu₀mem
  have hvnorm : ‖v‖ ≤ 1 := by simpa [dist_zero_right] using Metric.mem_closedBall.mp (hNball hvN)
  have hd : ‖u₀ - v‖ ≤ 1 / 4 := by rwa [dist_eq_norm] at hdist
  have htel : g u₀ - g v = B (u₀ - v) u₀ + B v (u₀ - v) := by
    rw [hgB u₀, hgB v, hBsubL, hBsubR]; ring
  have hcross : |g u₀ - g v| ≤ M / 2 := by
    have hb1 : |B (u₀ - v) u₀| ≤ M * ‖u₀ - v‖ * ‖u₀‖ := hsharp _ _
    have hb2 : |B v (u₀ - v)| ≤ M * ‖v‖ * ‖u₀ - v‖ := hsharp _ _
    have htri : |g u₀ - g v| ≤ |B (u₀ - v) u₀| + |B v (u₀ - v)| := by
      rw [htel]; exact abs_add_le _ _
    have e1 : M * ‖u₀ - v‖ * ‖u₀‖ ≤ M * (1 / 4) * 1 := by
      apply mul_le_mul _ hu₀norm (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hd hMnonneg
    have e2 : M * ‖v‖ * ‖u₀ - v‖ ≤ M * 1 * (1 / 4) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hvnorm hMnonneg) hd (norm_nonneg _)
        (by positivity)
    linarith [htri, hb1, hb2, e1, e2]
  -- M ≤ 2c
  have hgv : |g v| ≤ c := hnet v hvN
  have hM2c : M ≤ 2 * c := by
    have hsplit : M ≤ |g v| + |g u₀ - g v| := by
      calc M = |g u₀| := hMdef
        _ = |g v + (g u₀ - g v)| := by rw [show g v + (g u₀ - g v) = g u₀ from by ring]
        _ ≤ |g v| + |g u₀ - g v| := abs_add_le _ _
    linarith [hsplit, hgv, hcross]
  exact le_trans (hMmax u hu) hM2c

/-! ## Coordinate embedding of a low-dimensional Euclidean space

For an embedding of index sets `e : Fin m ↪ Fin d`, the coordinate inclusion sending the
`k`-th basis vector of `ℝ^m` to the `e k`-th basis vector of `ℝ^d` is a linear isometry onto
the coordinate subspace `span {eₖ : k ∈ range e}`.  We use it to transport the `1/4`-net of the
`m`-dimensional ball into the `3s`-sparse unit sphere supported on `range e`. -/

/-- The coordinate inclusion `ℝ^m ↪ ℝ^d` along `e : Fin m ↪ Fin d`, as a linear isometry. -/
private noncomputable def coordEmb {m d : ℕ} (e : Fin m ↪ Fin d) :
    EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.isometryOfOrthonormal
    ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.constr ℝ
      (fun k => EuclideanSpace.single (e k) (1 : ℝ)))
    (v := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis)
    (by rw [OrthonormalBasis.coe_toBasis]; exact (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal)
    (by
      have h : (⇑((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.constr ℝ
            (fun k => EuclideanSpace.single (e k) (1 : ℝ))) ∘
            ⇑(EuclideanSpace.basisFun (Fin m) ℝ).toBasis)
          = fun k => EuclideanSpace.single (e k) (1 : ℝ) := by
        funext k
        simp only [Function.comp_apply, Module.Basis.constr_basis]
      rw [h]
      have he : (fun k => EuclideanSpace.single (e k) (1 : ℝ))
          = (⇑(EuclideanSpace.basisFun (Fin d) ℝ)) ∘ e := by
        funext k; rw [Function.comp_apply, EuclideanSpace.basisFun_apply]
      rw [he]
      exact ((EuclideanSpace.basisFun (Fin d) ℝ).orthonormal).comp e e.injective)

/-- `coordEmb` sends the `k`-th standard basis vector to the `e k`-th one. -/
private lemma coordEmb_single {m d : ℕ} (e : Fin m ↪ Fin d) (k : Fin m) :
    coordEmb e (EuclideanSpace.single k (1 : ℝ)) = EuclideanSpace.single (e k) (1 : ℝ) := by
  have hbk : EuclideanSpace.single k (1 : ℝ)
      = (EuclideanSpace.basisFun (Fin m) ℝ).toBasis k := by
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have h1 : coordEmb e (EuclideanSpace.single k (1 : ℝ))
      = ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.constr ℝ
          (fun j => EuclideanSpace.single (e j) (1 : ℝ)))
        (EuclideanSpace.single k (1 : ℝ)) := rfl
  rw [h1, hbk, Module.Basis.constr_basis]

/-- The norm is preserved. -/
private lemma coordEmb_norm {m d : ℕ} (e : Fin m ↪ Fin d) (u : EuclideanSpace ℝ (Fin m)) :
    ‖coordEmb e u‖ = ‖u‖ := (coordEmb e).norm_map u

/-- **Coverage**: any vector supported on `range e` is in the image of `coordEmb e`. -/
private lemma exists_coordEmb_eq {m d : ℕ} (e : Fin m ↪ Fin d)
    (β : EuclideanSpace ℝ (Fin d)) (hsupp : ∀ i, i ∉ Set.range e → β i = 0) :
    ∃ u, coordEmb e u = β := by
  classical
  refine ⟨∑ k, β (e k) • EuclideanSpace.single k (1 : ℝ), ?_⟩
  rw [map_sum]
  simp only [map_smul, coordEmb_single]
  -- standard-basis expansion of β
  have hexp : ∑ i, β i • EuclideanSpace.single i (1 : ℝ) = β := by
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr β
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using h
  -- reindex the `k`-sum as a sum over `range e`, then fill out to all of `Fin d`
  have key : ∑ k, β (e k) • EuclideanSpace.single (e k) (1 : ℝ)
      = ∑ i, β i • EuclideanSpace.single i (1 : ℝ) := by
    rw [← Finset.sum_map Finset.univ e (fun i => β i • EuclideanSpace.single i (1 : ℝ))]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hni : i ∉ Set.range e := by
      rintro ⟨k, rfl⟩
      exact hi (Finset.mem_map.mpr ⟨k, Finset.mem_univ k, rfl⟩)
    rw [hsupp i hni, zero_smul]
  rw [key, hexp]

/-! ## A finite `1/4`-net of the unit ball with `9^m` points -/

/-- **Existence of a `1/4`-net** of the closed unit ball of `ℝ^m` with at most `9^m` points
(Lu §6.2, Lemma 6.1 (Covering Number), packing bound at `ε = 1/4`, via
`coveringNumber_closedBall_le`). -/
private lemma exists_quarter_net (m : ℕ) [NeZero m] :
    ∃ N : Finset (EuclideanSpace ℝ (Fin m)),
      (∀ v ∈ N, v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1, ∃ y ∈ N, dist x y ≤ 1 / 4) ∧
      N.card ≤ 9 ^ m := by
  classical
  have hε0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hε1 : (1 : ℝ) / 4 < 1 := by norm_num
  have hcn := coveringNumber_closedBall_le (d := m) hε0 hε1
  rw [show (1 + 2 / (1 / 4 : ℝ)) = 9 from by norm_num,
    show (⌊(9 : ℝ) ^ m⌋₊) = 9 ^ m from by
      rw [show (9 : ℝ) ^ m = ((9 ^ m : ℕ) : ℝ) from by push_cast; ring]
      exact Nat.floor_natCast _] at hcn
  -- `hcn : coveringNumber (closedBall 0 1) (1/4) ≤ ↑(9 ^ m)`
  have hcn' : Metric.coveringNumber (Real.toNNReal (1 / 4))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) ≤ (9 ^ m : ℕ) := hcn
  have hne : Metric.coveringNumber (Real.toNNReal (1 / 4))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hcn'
  set C := Metric.minimalCover (Real.toNNReal (1 / 4))
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) with hCdef
  have hCfin : C.Finite := Metric.finite_minimalCover
  have hencard : C.encard ≤ (9 ^ m : ℕ) := by
    rw [hCdef, Metric.encard_minimalCover hne]; exact hcn'
  obtain ⟨_, hncard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hencard
  refine ⟨hCfin.toFinset, ?_, ?_, ?_⟩
  · intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    exact Metric.minimalCover_subset hv
  · intro x hx
    obtain ⟨y, hyC, hxy⟩ := Metric.isCover_minimalCover hne hx
    refine ⟨y, Set.Finite.mem_toFinset hCfin |>.mpr hyC, ?_⟩
    rw [← edist_le_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    exact hxy
  · rw [← Set.ncard_eq_toFinset_card C hCfin]
    exact hncard

/-! ## Sample-size arithmetic

The union bound gives `μ(¬RIP) ≤ 2·(9d)^{3s}·exp(−nδ²/128)` (the `/128` is `(δ/2)²/32`, the
provable per-vector exponent at `δ/2`).  With `n ≥ (384/δ²)·s·log(18d/ε)` this is `≤ ε`.

**Constant deviation (Lu §9.1, Theorem 9.2).** The book states `96/δ²`, which corresponds to the
sharp per-vector exponent `nδ²/8`.  Our `GaussianChiSquared.lean` proves the exponent `nδ²/32`
(sub-exponential parameter `α = 4`, off the book's `α = 2` by a factor `2` in the standard
deviation), so the per-net-point tail at `δ/2` is `2·exp(−nδ²/128)` instead of `2·exp(−nδ²/32)`,
a factor `4` in the exponent.  Re-running the union bound, `n ≥ (384/δ²)·s·log(18d/ε)` (`= 4·96`)
suffices: the key identity `log(18d/ε) = log(9d) + log(2/ε)` makes `3s·log(18d/ε)` dominate
`log 2 + 3s·log(9d) + log(1/ε)` whenever `s ≥ 1` and `0 < ε < 1`.  We keep the order
`O(s·log(d/ε))` and the multiplier `18`; only the leading constant changes `96 → 384`. -/
private lemma sample_size_bound {s d n : ℕ} {δ ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 1 ≤ d) (hs : 1 ≤ s) (hδpos : 0 < δ ^ 2)
    (hn : (n : ℝ) ≥ (384 / δ ^ 2) * (s : ℝ) * Real.log (18 * (d : ℝ) / ε)) :
    2 * ((9 * (d : ℝ)) ^ (3 * s)) * Real.exp (-(n : ℝ) * δ ^ 2 / 128) ≤ ε := by
  have hdge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hδ2 : δ ^ 2 ≠ 0 := hδpos.ne'
  have hδne : δ ≠ 0 := by intro h; apply hδ2; rw [h]; ring
  have h9d : (1 : ℝ) < 9 * (d : ℝ) := by nlinarith
  have h9dpos : (0 : ℝ) < 9 * (d : ℝ) := by linarith
  have h2eps : (1 : ℝ) < 2 / ε := by rw [lt_div_iff₀ hε0]; linarith
  have hLsplit : Real.log (18 * (d : ℝ) / ε)
      = Real.log (9 * (d : ℝ)) + (Real.log 2 - Real.log ε) := by
    rw [show 18 * (d : ℝ) / ε = (9 * (d : ℝ)) * (2 / ε) from by ring,
      Real.log_mul h9dpos.ne' (by positivity), Real.log_div (by norm_num) hε0.ne']
  -- `nδ²/128 ≥ 3s·log(18d/ε)`
  have h128 : (0 : ℝ) ≤ δ ^ 2 / 128 := by positivity
  have hnlb : (3 : ℝ) * (s : ℝ) * Real.log (18 * (d : ℝ) / ε) ≤ (n : ℝ) * δ ^ 2 / 128 := by
    have hmul := mul_le_mul_of_nonneg_right hn h128
    have hcancel : (384 / δ ^ 2) * (s : ℝ) * Real.log (18 * (d : ℝ) / ε) * (δ ^ 2 / 128)
        = 3 * (s : ℝ) * Real.log (18 * (d : ℝ) / ε) := by
      field_simp [hδne]; ring
    rw [hcancel] at hmul
    calc (3 : ℝ) * (s : ℝ) * Real.log (18 * (d : ℝ) / ε)
        ≤ (n : ℝ) * (δ ^ 2 / 128) := hmul
      _ = (n : ℝ) * δ ^ 2 / 128 := by ring
  -- the gap `(3s−1)·log(2/ε) ≥ 0`
  have hlog2eps : 0 < Real.log 2 - Real.log ε := by
    rw [← Real.log_div (by norm_num) hε0.ne']; exact Real.log_pos h2eps
  have hgap : 0 ≤ (3 * (s : ℝ) - 1) * (Real.log 2 - Real.log ε) := by
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    apply mul_nonneg _ hlog2eps.le; linarith
  -- log of the LHS ≤ log ε
  have hLHSpos : (0 : ℝ) < 2 * ((9 * (d : ℝ)) ^ (3 * s)) * Real.exp (-(n : ℝ) * δ ^ 2 / 128) := by
    positivity
  rw [← Real.log_le_log_iff hLHSpos hε0,
    Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp]
  push_cast
  rw [hLsplit] at hnlb
  nlinarith [hnlb, hgap]

/-- **Random matrix is `3s`-RIP w.h.p.** (Lu, *Big Data Analysis* Ch. 9 §9.1, Theorem 9.2).
For an i.i.d. `N(0,1/n)` matrix `X` and `n ≥ (96/δ²)·s·log(18d/ε)`,
`P(X is 3s-RIP with constant δ) ≥ 1 − ε`. -/
theorem prob_rip_of_iid_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℕ) (δ ε : ℝ)
    -- USER-INPUT: 0 < δ < 1 (target RIP constant); Lu-BDA §9.1, Theorem 9.2
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: 0 < ε (target failure probability); Lu-BDA §9.1, Theorem 9.2
    (hε0 : 0 < ε)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    -- USER-INPUT: the entries Xᵢⱼ are jointly independent; Lu-BDA §9.1, Theorem 9.2
    (hindep : iIndepFun (fun (p : Fin n × Fin d) ω => X ω p.1 p.2) μ)
    -- USER-INPUT: each entry Xᵢⱼ ∼ N(0,1/n); Lu-BDA §9.1, Theorem 9.2
    (hlaw : ∀ i j, Measure.map (fun ω => X ω i j) μ
              = gaussianReal 0 (⟨1 / (n : ℝ), div_nonneg zero_le_one (Nat.cast_nonneg n)⟩ : ℝ≥0))
    -- USER-INPUT: sample-size lower bound n ≥ (384/δ²)·s·log(18d/ε); Lu-BDA §9.1, Theorem 9.2.
    -- Constant `384 = 4·96`: the book's `96` assumes the sharp per-vector exponent `nδ²/8`;
    -- `GaussianChiSquared.lean` proves only `nδ²/32` (α = 4), a factor 4, hence `96 → 384`.
    -- See `sample_size_bound`. A larger constant only strengthens this USER-INPUT hypothesis.
    (hn : (n : ℝ) ≥ (384 / δ ^ 2) * (s : ℝ) * Real.log (18 * (d : ℝ) / ε)) :
    μ {ω | IsRIP (X ω) (3 * s) δ} ≥ 1 - ENNReal.ofReal ε := by
  classical
  -- vacuous case `ε ≥ 1`: the bound `1 - ε ≤ 0`.
  by_cases hεbig : 1 ≤ ε
  · have h0 : (1 : ℝ≥0∞) - ENNReal.ofReal ε = 0 := by
      rw [tsub_eq_zero_iff_le]
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hεbig
    rw [ge_iff_le, h0]; exact zero_le
  have hεlt : ε < 1 := not_le.mp hεbig
  -- a measurable representative `X'` of `X`, a.e. equal entrywise.
  set vn : ℝ≥0 := ⟨1 / (n : ℝ), div_nonneg zero_le_one (Nat.cast_nonneg n)⟩ with hvn
  have hXae : ∀ i j, AEMeasurable (fun ω => X ω i j) μ := by
    intro i j; apply AEMeasurable.of_map_ne_zero; rw [hlaw i j]
    exact IsProbabilityMeasure.ne_zero _
  set X' : Ω → Matrix (Fin n) (Fin d) ℝ :=
    fun ω => Matrix.of (fun i j => (hXae i j).mk (fun ω' => X ω' i j) ω) with hX'def
  have hX'meas : ∀ i j, Measurable (fun ω => X' ω i j) :=
    fun i j => (hXae i j).measurable_mk
  have hXeq : ∀ i j, (fun ω => X' ω i j) =ᵐ[μ] (fun ω => X ω i j) :=
    fun i j => (hXae i j).ae_eq_mk.symm
  have hX'law : ∀ i j, Measure.map (fun ω => X' ω i j) μ = gaussianReal 0 vn := by
    intro i j; rw [Measure.map_congr (hXeq i j)]; exact hlaw i j
  have hX'indep : iIndepFun (fun (p : Fin n × Fin d) ω => X' ω p.1 p.2) μ :=
    (iIndepFun_congr (fun p : Fin n × Fin d => hXeq p.1 p.2)).mpr hindep
  have hae_mat : ∀ᵐ ω ∂μ, X' ω = X ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ i j, X' ω i j = X ω i j := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact hXeq i j
    filter_upwards [hall] with ω hω; ext i j; exact hω i j
  have hRIPeq : μ {ω | IsRIP (X ω) (3 * s) δ} = μ {ω | IsRIP (X' ω) (3 * s) δ} := by
    apply measure_congr
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae_mat] with ω hω
    show IsRIP (X ω) (3 * s) δ ↔ IsRIP (X' ω) (3 * s) δ
    rw [hω]
  -- measurability of `ω ↦ ‖designMap (X' ω) γ‖²`.
  have hmeas_normsq : ∀ γ : EuclideanSpace ℝ (Fin d),
      Measurable (fun ω => ‖designMap (X' ω) γ‖ ^ 2) := by
    intro γ
    have hrw : (fun ω => ‖designMap (X' ω) γ‖ ^ 2)
        = fun ω => ∑ i, (∑ j, X' ω i j * γ.ofLp j) ^ 2 := by
      funext ω
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcoord : (designMap (X' ω) γ).ofLp i = ∑ j, X' ω i j * γ.ofLp j := by
        rw [show (designMap (X' ω) γ).ofLp = X' ω *ᵥ γ.ofLp from rfl]
        simp [Matrix.mulVec, dotProduct]
      rw [hcoord]
    rw [hrw]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine (Finset.measurable_sum _ (fun j _ => (hX'meas i j).mul measurable_const)).pow_const 2
  -- trivial-sparsity helper: when `d = 0` or `s = 0`, every `3s`-sparse vector is `0`.
  have hRIP_all : (∀ β : EuclideanSpace ℝ (Fin d), IsSparse (3 * s) β → β = 0) →
      μ {ω | IsRIP (X ω) (3 * s) δ} ≥ 1 - ENNReal.ofReal ε := by
    intro hzero
    have huniv : {ω | IsRIP (X ω) (3 * s) δ} = Set.univ := by
      apply Set.eq_univ_of_forall; intro ω β hβ
      rw [hzero β hβ]
      simp
    rw [huniv, measure_univ]; exact tsub_le_self
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    exact hRIP_all (fun β _ => Subsingleton.elim β 0)
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0
    refine hRIP_all (fun β hβ => ?_)
    obtain ⟨S, hScard, hSsupp⟩ := hβ
    have hSempty : S = ∅ := by
      rw [← Finset.card_eq_zero]; omega
    apply PiLp.ext; intro i
    have := hSsupp i (by rw [hSempty]; exact Finset.notMem_empty i)
    simpa using this
  -- main case: `d ≥ 1`, `s ≥ 1`, `ε < 1`.
  set m := min (3 * s) d with hm
  have hmpos : 0 < m := lt_min (by omega) hdpos
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have hm3s : m ≤ 3 * s := min_le_left _ _
  have hmd : m ≤ d := min_le_right _ _
  obtain ⟨N₀, hN₀ball, hN₀cover, hN₀card⟩ := exists_quarter_net m
  -- the bad-event family, indexed by support-embeddings `e` and net points `v`.
  set badE : (Fin m ↪ Fin d) → EuclideanSpace ℝ (Fin m) → Set Ω :=
    fun e v => {ω | v ≠ 0 ∧
      δ / 2 < |‖designMap (X' ω) (coordEmb e v)‖ ^ 2 / ‖coordEmb e v‖ ^ 2 - 1|} with hbadEdef
  set F : Finset ((Fin m ↪ Fin d) × EuclideanSpace ℝ (Fin m)) := Finset.univ ×ˢ N₀ with hF
  set G : Set Ω := ⋃ p ∈ F, badE p.1 p.2 with hGdef
  -- measurability of each bad event, hence of `G`.
  have hbadE_meas : ∀ e v, MeasurableSet (badE e v) := by
    intro e v
    by_cases hv : v = 0
    · rw [show badE e v = ∅ from by ext ω; simp [hbadEdef, hv]]; exact MeasurableSet.empty
    · rw [show badE e v
          = {ω | δ / 2 < |‖designMap (X' ω) (coordEmb e v)‖ ^ 2 / ‖coordEmb e v‖ ^ 2 - 1|}
          from by ext ω; simp [hbadEdef, hv]]
      exact measurableSet_lt measurable_const
        (((hmeas_normsq _).div_const _).sub_const _).abs
  have hGmeas : MeasurableSet G := by
    rw [hGdef]
    exact MeasurableSet.biUnion F.countable_toSet (fun p _ => hbadE_meas p.1 p.2)
  -- per-event tail bound.
  have hbadE_le : ∀ e v, μ (badE e v)
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 128)) := by
    intro e v
    by_cases hv : v = 0
    · rw [show badE e v = ∅ from by ext ω; simp [hbadEdef, hv]]; simp
    · have hγ : coordEmb e v ≠ 0 := by
        rw [← norm_ne_zero_iff, coordEmb_norm]; exact norm_ne_zero_iff.mpr hv
      have hsub : badE e v
          ⊆ {ω | δ / 2 < |‖designMap (X' ω) (coordEmb e v)‖ ^ 2 / ‖coordEmb e v‖ ^ 2 - 1|} :=
        fun ω hω => hω.2
      refine le_trans (measure_mono hsub) ?_
      have htail := gaussian_quadratic_form_tail μ X' hX'indep hX'law (coordEmb e v) hγ
        (δ := δ / 2) (by positivity) (by linarith)
      rw [show (-(n : ℝ) * (δ / 2) ^ 2 / 32) = -(n : ℝ) * δ ^ 2 / 128 from by ring] at htail
      exact htail
  -- the discretisation gives: off `G`, RIP holds for `X'`.
  have hcompl : Gᶜ ⊆ {ω | IsRIP (X' ω) (3 * s) δ} := by
    intro ω hωc β hβsparse
    rcases eq_or_ne β 0 with rfl | hβ0
    · exact ⟨by simp, by simp⟩
    -- find a support-embedding `e` whose range contains `β`'s support
    obtain ⟨S, hScard, hSsupp⟩ := hβsparse
    have hScardm : S.card ≤ m := by
      rw [hm]
      exact le_min hScard ((Finset.card_le_univ S).trans (le_of_eq (Fintype.card_fin d)))
    obtain ⟨T, hST, hTcard⟩ := Finset.exists_superset_card_eq hScardm
      (by rw [Fintype.card_fin]; exact hmd)
    set e : Fin m ↪ Fin d := (T.orderEmbOfFin hTcard).toEmbedding with he
    have hrange : Set.range e = (T : Set (Fin d)) := by
      rw [he]
      exact Finset.range_orderEmbOfFin T hTcard
    have hβsupp_e : ∀ i, i ∉ Set.range e → β i = 0 := by
      intro i hi
      exact hSsupp i (fun hiS => hi (by rw [hrange]; exact Finset.mem_coe.mpr (hST hiS)))
    obtain ⟨u, hu⟩ := exists_coordEmb_eq e β hβsupp_e
    set Lω := (designMap (X' ω)).comp (coordEmb e).toLinearMap with hLωdef
    have hLωapp : ∀ w, Lω w = designMap (X' ω) (coordEmb e w) := fun w => rfl
    -- off `G`, the net values are controlled
    have hnetgood : ∀ w ∈ (↑N₀ : Set (EuclideanSpace ℝ (Fin m))),
        |‖Lω w‖ ^ 2 - ‖w‖ ^ 2| ≤ δ / 2 := by
      intro w hwN
      have hwball : w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 :=
        hN₀ball w (Finset.mem_coe.mp hwN)
      have hwle : ‖w‖ ≤ 1 := by simpa [dist_zero_right] using Metric.mem_closedBall.mp hwball
      rcases eq_or_ne w 0 with rfl | hw0
      · simp only [hLωapp, map_zero, norm_zero]; simpa using by positivity
      · have hwF : (e, w) ∈ F := by
          rw [hF, Finset.mem_product]
          exact ⟨Finset.mem_univ _, Finset.mem_coe.mp hwN⟩
        have hnotbad : ω ∉ badE e w := fun hb => hωc (Set.mem_biUnion hwF hb)
        have hbound : |‖designMap (X' ω) (coordEmb e w)‖ ^ 2 / ‖coordEmb e w‖ ^ 2 - 1| ≤ δ / 2 := by
          by_contra hlt
          exact hnotbad ⟨hw0, not_le.mp hlt⟩
        have hcw : ‖coordEmb e w‖ = ‖w‖ := coordEmb_norm e w
        have hwsq : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
        have hkey : ‖w‖ ^ 2 * |‖designMap (X' ω) (coordEmb e w)‖ ^ 2 / ‖coordEmb e w‖ ^ 2 - 1|
            = |‖designMap (X' ω) (coordEmb e w)‖ ^ 2 - ‖w‖ ^ 2| := by
          rw [hcw,
            show ‖designMap (X' ω) (coordEmb e w)‖ ^ 2 / ‖w‖ ^ 2 - 1
              = (‖designMap (X' ω) (coordEmb e w)‖ ^ 2 - ‖w‖ ^ 2) / ‖w‖ ^ 2 from by
                field_simp,
            abs_div, abs_of_pos hwsq]
          field_simp
        rw [hLωapp, ← hkey]
        calc ‖w‖ ^ 2 * |‖designMap (X' ω) (coordEmb e w)‖ ^ 2 / ‖coordEmb e w‖ ^ 2 - 1|
            ≤ ‖w‖ ^ 2 * (δ / 2) := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
          _ ≤ 1 * (δ / 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith [hwle, norm_nonneg w]
          _ = δ / 2 := one_mul _
    -- discretisation: `|‖Lω u'‖² − ‖u'‖²| ≤ δ` for the unit vector `u'`
    have hβnorm : (0 : ℝ) < ‖β‖ := norm_pos_iff.mpr hβ0
    have hunorm : ‖u‖ = ‖β‖ := by rw [← hu, coordEmb_norm]
    have hu0 : u ≠ 0 := by rw [← norm_ne_zero_iff, hunorm]; exact hβnorm.ne'
    set u' := ‖u‖⁻¹ • u with hu'def
    have hu'norm : ‖u'‖ = 1 := by rw [hu'def]; exact norm_smul_inv_norm hu0
    have hdisc := quadform_le_two_sup_net Lω (↑N₀)
      (fun w hw => hN₀ball w (Finset.mem_coe.mp hw))
      (fun x hx => by
        obtain ⟨y, hyN, hd⟩ := hN₀cover x hx
        exact ⟨y, Finset.mem_coe.mpr hyN, hd⟩)
      hnetgood u' (le_of_eq hu'norm)
    -- rewrite `‖Lω u'‖²` and `‖u'‖²`
    have hcoordu' : coordEmb e u' = ‖β‖⁻¹ • β := by
      rw [hu'def, map_smul, hu, hunorm]
    have hLu' : Lω u' = ‖β‖⁻¹ • designMap (X' ω) β := by
      rw [hLωapp, hcoordu', map_smul]
    have hnormLu' : ‖Lω u'‖ ^ 2 = ‖designMap (X' ω) β‖ ^ 2 / ‖β‖ ^ 2 := by
      rw [hLu', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβnorm), mul_pow, inv_pow]
      field_simp
    have hnormu' : ‖u'‖ ^ 2 = 1 := by rw [hu'norm]; norm_num
    rw [hnormLu', hnormu', show 2 * (δ / 2) = δ from by ring, abs_le] at hdisc
    obtain ⟨hlo, hhi⟩ := hdisc
    have hβ2 : (0 : ℝ) < ‖β‖ ^ 2 := by positivity
    refine ⟨(le_div_iff₀ hβ2).mp (by linarith), (div_le_iff₀ hβ2).mp (by linarith)⟩
  -- union bound and sample size collapse `μ G ≤ ε`.
  have hFcard : F.card ≤ (9 * d) ^ (3 * s) := by
    have hembcard : Fintype.card (Fin m ↪ Fin d) ≤ d ^ m := by
      calc Fintype.card (Fin m ↪ Fin d) ≤ Fintype.card (Fin m → Fin d) :=
            Fintype.card_le_of_injective _ DFunLike.coe_injective
        _ = d ^ m := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    calc F.card = Fintype.card (Fin m ↪ Fin d) * N₀.card := by
          rw [hF, Finset.card_product, Finset.card_univ]
      _ ≤ d ^ m * 9 ^ m := Nat.mul_le_mul hembcard hN₀card
      _ = (9 * d) ^ m := by rw [mul_pow]; ring
      _ ≤ (9 * d) ^ (3 * s) := Nat.pow_le_pow_right (by omega) hm3s
  have hμGle : μ G ≤ ENNReal.ofReal ε := by
    have h1 : μ G ≤ ∑ p ∈ F, μ (badE p.1 p.2) := by
      rw [hGdef]; exact measure_biUnion_finset_le F _
    have h2 : ∑ p ∈ F, μ (badE p.1 p.2)
        ≤ ∑ _p ∈ F, ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 128)) :=
      Finset.sum_le_sum (fun p _ => hbadE_le p.1 p.2)
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    refine le_trans h1 (le_trans h2 ?_)
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hcardR : (F.card : ℝ) ≤ (9 * (d : ℝ)) ^ (3 * s) := by
      calc (F.card : ℝ) ≤ (((9 * d) ^ (3 * s) : ℕ) : ℝ) := by exact_mod_cast hFcard
        _ = (9 * (d : ℝ)) ^ (3 * s) := by push_cast; ring
    have hPpos : 0 ≤ 2 * Real.exp (-(n : ℝ) * δ ^ 2 / 128) := by positivity
    calc (F.card : ℝ) * (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 128))
        ≤ (9 * (d : ℝ)) ^ (3 * s) * (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 128)) :=
          mul_le_mul_of_nonneg_right hcardR hPpos
      _ = 2 * ((9 * (d : ℝ)) ^ (3 * s)) * Real.exp (-(n : ℝ) * δ ^ 2 / 128) := by ring
      _ ≤ ε := sample_size_bound hε0 hεlt hdpos hspos (by positivity) hn
  -- assemble via the complement.
  rw [hRIPeq, ge_iff_le]
  calc (1 : ℝ≥0∞) - ENNReal.ofReal ε ≤ 1 - μ G := tsub_le_tsub_left hμGle 1
    _ = μ Gᶜ := (prob_compl_eq_one_sub hGmeas).symm
    _ ≤ μ {ω | IsRIP (X' ω) (3 * s) δ} := measure_mono hcompl

end StatLean.HighDimensionalStatistics
