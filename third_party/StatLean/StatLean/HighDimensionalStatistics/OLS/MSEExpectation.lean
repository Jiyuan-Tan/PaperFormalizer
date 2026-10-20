module
public import StatLean.HighDimensionalStatistics.LinearModel.Defs
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Expected prediction MSE of the ordinary least squares estimator

Consider the linear model $Y = X\beta^* + \varepsilon$ with a fixed design matrix
$X \in \mathbb{R}^{n \times d}$, an unknown coefficient vector $\beta^*$, and noise
$\varepsilon$ whose coordinates are independent, mean-zero, and each sub-Gaussian with
variance proxy $\sigma^2$. For any ordinary least squares (OLS) estimator $\hat\beta$
— that is, any minimizer of $\lVert Y - X\beta\rVert^2$ — the expected in-sample
prediction error satisfies
$$
\mathbb{E}\bigl[\mathrm{MSE}(X\hat\beta, X\beta^*)\bigr]
  \;=\; \frac{1}{n}\,\mathbb{E}\bigl[\lVert X\hat\beta - X\beta^*\rVert^2\bigr]
  \;\le\; \frac{\sigma^2 \, \mathrm{rank}(X)}{n}.
$$
The main result is `mse_ols_expectation_le`.

**Deviations from the book.** The book states the bound up to an absolute constant
($\lesssim$); here the constant is made explicit and equals exactly
$\sigma^2 \,\mathrm{rank}(X)/n$. The hypotheses used are the genuine model inputs
(independence, mean-zero, sub-Gaussian proxy per coordinate, and that $\hat\beta$ is an
OLS minimizer); the only added hypothesis is $n > 0$, needed so the $1/n$ factor and the
right-hand side are well-defined.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 7 (Ordinary Least Squares), §7.2, Theorem 7.1
(Mean Squared Error of Least Squares), expectation half.

**Proof formalization notes.**
1. The OLS minimizer satisfies $X\hat\beta = P_C(Y)$, the orthogonal projection of $Y$
   onto the column space $C = \mathcal{C}(X)$.
2. Prediction error $X\hat\beta - X\beta^* = P_C(\varepsilon)$ (linearity of the
   projection together with $X\beta^* \in C$).
3. Parseval: $\lVert P_C(\varepsilon)\rVert^2 = \sum_{k<r} \langle e_k, \varepsilon\rangle^2$
   for an orthonormal basis $\{e_k\}$ of $C$, where $r = \mathrm{rank}(X)$.
4. Each $\langle e_k, \varepsilon\rangle = \sum_i (e_k)_i\,\varepsilon_i$ is sub-Gaussian
   with proxy $\sigma^2$ (independent linear combination with a unit-norm coefficient
   vector).
5. Variance bound: $\mathbb{E}[Z^2] \le \sigma^2$ for a mean-zero sub-Gaussian variable
   $Z$ (proved in-file via the $\cosh$ expansion of the moment generating function and a
   derivative limit).
6. Summation: $\mathbb{E}[\mathrm{MSE}] \le (1/n)\cdot r \cdot \sigma^2
   = \sigma^2 r / n$.

**Bibliographic comments.** This is the classical risk bound for the in-sample prediction
error of least squares; it is folklore with no single seminal origin. The exact-variance
version $\mathbb{E}[\lVert X\hat\beta - X\beta^*\rVert^2] = \sigma^2\,\mathrm{rank}(X)$
holds when $\varepsilon$ has covariance $\sigma^2 I$ (Gaussian–Markov / projection
trace identity); the sub-Gaussian inequality version stated here replaces the exact
variance identity by the second-moment bound $\mathbb{E}[Z^2] \le \sigma^2$ and is
standard in the high-dimensional statistics literature (see, e.g., M. J. Wainwright,
*High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press,
2019, Chapter 7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace StatLean.HighDimensionalStatistics
open StatLean.ConcentrationInequalities

variable {n d : ℕ}

/-! ### Variance bound for mean-0 sub-Gaussian variables -/

/-- `cosh` is bounded below by its first two power-series terms: `1 + u²/2 ≤ cosh u`.
Both terms are entries of the all-nonneg series `cosh u = ∑ u^{2k}/(2k)!`. -/
private lemma one_add_half_sq_le_cosh (u : ℝ) : 1 + u ^ 2 / 2 ≤ Real.cosh u := by
  have hsum := Real.hasSum_cosh u
  have hle := sum_le_hasSum (Finset.range 2) (fun i _ => by simp only [pow_mul]; positivity) hsum
  rw [Finset.sum_range_succ, Finset.sum_range_one] at hle
  norm_num [Nat.factorial] at hle
  linarith

/-- **Variance ≤ proxy for a sub-Gaussian variable.**

For `HasSubgaussianMGF X σ2 μ`, the second moment satisfies `E[X²] ≤ σ2`. (Mathlib's
`HasSubgaussianMGF` already forces `E[X] = 0`, so this is the variance bound; no separate
mean-zero hypothesis is needed.)

**Proof:** Summing the MGF bound at `t` and `-t` gives
`E[exp(tX) + exp(-tX)] ≤ 2·exp(σ2 t²/2)`. The pointwise bound `2 + u² ≤ exp u + exp(-u)`
(from `1 + u²/2 ≤ cosh u`) integrates to `2 + t²·E[X²] ≤ 2·exp(σ2 t²/2)`, hence for all
`t ≠ 0`, `E[X²] ≤ (2·exp(σ2 t²/2) − 2)/t²`. The right side tends to `σ2` as `t → 0`
(a derivative limit of `exp`), so `E[X²] ≤ σ2`. -/
private lemma hasSubgaussianMGF_integral_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ2 : ℝ≥0}
    (h : HasSubgaussianMGF X σ2 μ) :
    ∫ ω, X ω ^ 2 ∂μ ≤ σ2 := by
  have hXsq_int : Integrable (fun ω => X ω ^ 2) μ := (h.memLp 2).integrable_sq
  rcases eq_or_ne σ2 0 with hσ | hσ
  · -- σ2 = 0 ⟹ X = 0 a.e. ⟹ ∫ X² = 0.
    subst hσ
    have hX0 : X =ᵐ[μ] 0 := h.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hsq0 : (fun ω => X ω ^ 2) =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [hX0] with ω hω; simp [hω]
    rw [integral_congr_ae hsq0, integral_zero]; simp
  · -- σ2 > 0.
    have hσpos : (0 : ℝ≥0) < σ2 := lt_of_le_of_ne (zero_le (a := σ2)) (Ne.symm hσ)
    have hσR : (0 : ℝ) < (σ2 : ℝ) := NNReal.coe_pos.mpr hσpos
    -- Key per-`t` bound from the cosh expansion of the MGF.
    have hkey : ∀ t : ℝ, t ≠ 0 →
        ∫ ω, X ω ^ 2 ∂μ ≤ (2 * Real.exp ((σ2 : ℝ) * t ^ 2 / 2) - 2) / t ^ 2 := by
      intro t ht
      have hsq_eq : (fun ω => (t * X ω) ^ 2) = fun ω => t ^ 2 * X ω ^ 2 := by
        funext ω; ring
      have hsq_int' : Integrable (fun ω => (t * X ω) ^ 2) μ := by
        rw [hsq_eq]; exact hXsq_int.const_mul (t ^ 2)
      have hexp1 : Integrable (fun ω => Real.exp (t * X ω)) μ := h.integrable_exp_mul t
      have hexp2 : Integrable (fun ω => Real.exp (-(t * X ω))) μ := by
        simpa [neg_mul] using h.integrable_exp_mul (-t)
      -- pointwise: 2 + (t X)² ≤ exp(t X) + exp(-(t X))
      have hptwise : ∀ ω,
          2 + (t * X ω) ^ 2 ≤ Real.exp (t * X ω) + Real.exp (-(t * X ω)) := by
        intro ω
        have hc := one_add_half_sq_le_cosh (t * X ω)
        rw [Real.cosh_eq] at hc
        linarith
      have hf_int : Integrable (fun ω => 2 + (t * X ω) ^ 2) μ :=
        (integrable_const (2 : ℝ)).add hsq_int'
      have hg_int : Integrable (fun ω => Real.exp (t * X ω) + Real.exp (-(t * X ω))) μ :=
        hexp1.add hexp2
      have hmono := integral_mono hf_int hg_int hptwise
      -- LHS integral
      have hc2 : ∫ _ω : Ω, (2 : ℝ) ∂μ = 2 := by simp
      have hLHS : ∫ ω, (2 + (t * X ω) ^ 2) ∂μ = 2 + t ^ 2 * ∫ ω, X ω ^ 2 ∂μ := by
        rw [integral_add (integrable_const (2 : ℝ)) hsq_int', hsq_eq, integral_const_mul, hc2]
      -- RHS integral ≤ 2 exp(σ2 t²/2)
      have hRHS : ∫ ω, (Real.exp (t * X ω) + Real.exp (-(t * X ω))) ∂μ
          ≤ 2 * Real.exp ((σ2 : ℝ) * t ^ 2 / 2) := by
        rw [integral_add hexp1 hexp2]
        have e1 : ∫ ω, Real.exp (t * X ω) ∂μ = mgf X μ t := rfl
        have e2 : ∫ ω, Real.exp (-(t * X ω)) ∂μ = mgf X μ (-t) := by
          simp only [mgf, neg_mul]
        rw [e1, e2]
        have hm1 := h.mgf_le t
        have hm2 := h.mgf_le (-t)
        rw [neg_sq] at hm2
        linarith
      have hcomb : 2 + t ^ 2 * ∫ ω, X ω ^ 2 ∂μ ≤ 2 * Real.exp ((σ2 : ℝ) * t ^ 2 / 2) := by
        rw [← hLHS]; exact le_trans hmono hRHS
      have ht2 : (0 : ℝ) < t ^ 2 := by positivity
      rw [le_div_iff₀ ht2]
      nlinarith [hcomb]
    -- The right side tends to σ2 as t → 0.
    have hD : Tendsto (fun u : ℝ => (Real.exp u - 1) / u) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      have hd : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
      have hs := hasDerivAt_iff_tendsto_slope.mp hd
      refine Tendsto.congr (fun u => ?_) hs
      rw [slope_def_field, Real.exp_zero, sub_zero]
    have hq : Tendsto (fun t : ℝ => (σ2 : ℝ) * t ^ 2 / 2) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hcont : Continuous (fun t : ℝ => (σ2 : ℝ) * t ^ 2 / 2) := by fun_prop
        exact (hcont.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
        exact div_ne_zero (mul_ne_zero (ne_of_gt hσR) (pow_ne_zero 2 ht)) two_ne_zero
    have hcomp := hD.comp hq
    have hg : Tendsto (fun t : ℝ => (2 * Real.exp ((σ2 : ℝ) * t ^ 2 / 2) - 2) / t ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (σ2 : ℝ)) := by
      have hmul := hcomp.const_mul (σ2 : ℝ)
      rw [mul_one] at hmul
      refine Tendsto.congr' ?_ hmul
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
      have hqne : (σ2 : ℝ) * t ^ 2 / 2 ≠ 0 :=
        div_ne_zero (mul_ne_zero (ne_of_gt hσR) ht2) two_ne_zero
      simp only [Function.comp_apply]
      field_simp
    have he : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        ∫ ω, X ω ^ 2 ∂μ ≤ (2 * Real.exp ((σ2 : ℝ) * t ^ 2 / 2) - 2) / t ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      exact hkey t ht
    exact ge_of_tendsto hg he

/-! ### Helper: orthogonality of residual from the OLS first-order condition -/

/-- The OLS residual `Y − Xβ̂` is orthogonal to every element of `columnSpace X`.
This is the standard first-order (gradient) condition for a least-squares minimiser. -/
private lemma ols_residual_orthogonal
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: βhat minimises ‖Y − Xβ‖² (OLS); Lu-BDA §7.2 Theorem 7.1
    (hols : IsOLSEstimator X Y βhat)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ columnSpace X) :
    ⟪Y - designMap X βhat, w⟫_ℝ = 0 := by
  obtain ⟨γ, rfl⟩ := hw
  -- Quadratic expansion of the perturbed objective along direction γ.
  have expand : ∀ t : ℝ,
      ‖(Y - designMap X βhat) - t • designMap X γ‖ ^ 2
        = ‖Y - designMap X βhat‖ ^ 2
          - 2 * t * ⟪Y - designMap X βhat, designMap X γ⟫_ℝ
          + t ^ 2 * ‖designMap X γ‖ ^ 2 := by
    intro t
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  -- First-order condition: 0 ≤ t²‖Xγ‖² − 2t⟪res, Xγ⟫ for all t.
  have key : ∀ t : ℝ,
      0 ≤ t ^ 2 * ‖designMap X γ‖ ^ 2 - 2 * t * ⟪Y - designMap X βhat, designMap X γ⟫_ℝ := by
    intro t
    have hcomp := hols (βhat + t • γ)
    rw [map_add, map_smul] at hcomp
    have he : Y - (designMap X βhat + t • designMap X γ)
        = (Y - designMap X βhat) - t • designMap X γ := by abel
    rw [he, expand t] at hcomp
    linarith
  -- Specialise at t = c/(2+s) to force c = 0.
  set c := ⟪Y - designMap X βhat, designMap X γ⟫_ℝ with hc
  set s := ‖designMap X γ‖ ^ 2 with hs
  have hs_nn : 0 ≤ s := by rw [hs]; positivity
  have h2pos : (0 : ℝ) < 2 + s := by linarith
  have h2s : (2 : ℝ) + s ≠ 0 := h2pos.ne'
  have hden : (0 : ℝ) < (2 + s) ^ 2 := pow_pos h2pos 2
  have hspec := key (c / (2 + s))
  have hid : (c / (2 + s)) ^ 2 * s - 2 * (c / (2 + s)) * c
      = -(c ^ 2 * (4 + s)) / (2 + s) ^ 2 := by
    field_simp
    ring
  rw [hid, le_div_iff₀ hden, zero_mul] at hspec
  have hc2 : c ^ 2 ≤ 0 := by
    nlinarith [hspec, hs_nn, sq_nonneg c, mul_nonneg (sq_nonneg c) hs_nn]
  have hc2' : c ^ 2 = 0 := le_antisymm hc2 (sq_nonneg c)
  exact pow_eq_zero_iff (by norm_num) |>.mp hc2'

/-! ### OLS prediction = orthogonal projection -/

/-- The OLS prediction `Xβ̂` equals the orthogonal projection of `Y` onto `columnSpace X`.
Follows from uniqueness of the orthogonal projection, characterised by orthogonality. -/
private lemma ols_pred_eq_proj
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d))
    (hols : IsOLSEstimator X Y βhat)
    [(columnSpace X).HasOrthogonalProjection] :
    (columnSpace X).starProjection Y = designMap X βhat :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (LinearMap.mem_range_self _ _)
    (fun _ hw => ols_residual_orthogonal X Y βhat hols hw)

/-! ### designRank = finrank of columnSpace -/

private lemma designRank_eq_finrank_columnSpace (X : Matrix (Fin n) (Fin d) ℝ) :
    designRank X = Module.finrank ℝ ↥(columnSpace X) := by
  simp only [designRank, columnSpace, designMap, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.rank_eq_finrank_range_toLin X
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

/-! ### Main theorem -/

/-- **Expected MSE of OLS — Lu-BDA §7.2 Theorem 7.1 (Mean Squared Error of Least Squares), expectation half.**

For `Y ω = X β* + ε ω` with noise `ε` having independent mean-0 coordinates each
sub-Gaussian proxy `σ²`, every OLS estimator `βhat` satisfies
  `E[MSE(Xβ̂, Xβ*)] ≤ σ² · rank(X) / n`.

**Hypotheses:**
- `hε_indep` (USER-INPUT; Lu-BDA §7.2 Theorem 7.1): joint independence of noise coordinates.
- `hε_meanz` (USER-INPUT; Lu-BDA §7.2 Theorem 7.1): mean-0 noise coordinates.
- `hε_subG` (USER-INPUT; Lu-BDA §7.2 Theorem 7.1): sub-Gaussian proxy σ² per coordinate.
- `hβ_ols` (USER-INPUT; Lu-BDA §7.2 Theorem 7.1): βhat ω is OLS for Y ω = Xβ* + ε ω.
- `hn` (LEAN-ONLY): `n > 0` so the `(1/n)` factor and the final bound are well-typed. -/
theorem mse_ols_expectation_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ)
    -- LEAN-ONLY: needed so (1/n : ℝ) is well-defined and the final bound is finite; no scope change
    (hn : 0 < n)
    {σ2 : ℝ≥0}
    {ε : Ω → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: noise coordinates are jointly independent; Lu-BDA §7.2 Theorem 7.1
    (hε_indep : iIndepFun (fun (i : Fin n) (ω : Ω) => (ε ω) i) μ)
    -- USER-INPUT: each noise coordinate has mean 0; Lu-BDA §7.2 Theorem 7.1
    (hε_meanz : ∀ i : Fin n, ∫ ω, (ε ω) i ∂μ = 0)
    -- USER-INPUT: each noise coordinate is sub-Gaussian proxy σ²; Lu-BDA §7.2 Theorem 7.1
    (hε_subG : ∀ i : Fin n, IsSubGaussian (fun ω => (ε ω) i) σ2 μ)
    -- USER-INPUT: true coefficient vector; Lu-BDA §7.2 Theorem 7.1
    (βstar : EuclideanSpace ℝ (Fin d))
    {βhat : Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: βhat ω minimises ‖Y ω − Xβ‖² over β; Lu-BDA §7.2 Theorem 7.1
    (hβ_ols : ∀ ω, IsOLSEstimator X (designMap X βstar + ε ω) (βhat ω)) :
    ∫ ω, mse X (βhat ω) βstar ∂μ ≤ ↑σ2 * ↑(designRank X) / ↑n := by
  -- Setup: column space C = range(X), finite-dimensional ⟹ complete ⟹ has orthogonal projection.
  let C := columnSpace X
  haveI hC_fd : FiniteDimensional ℝ ↥C := LinearMap.finiteDimensional_range _
  haveI hC_complete : CompleteSpace ↥C := inferInstance
  haveI hC_proj : C.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace C
  let r := Module.finrank ℝ ↥C
  -- Standard ONB for C, indexed by Fin r.
  let b : OrthonormalBasis (Fin r) ℝ ↥C := stdOrthonormalBasis ℝ ↥C
  have hr_eq : designRank X = r := designRank_eq_finrank_columnSpace X
  -- Step 1: OLS prediction = orthogonal projection of Y ω onto C.
  have hpred : ∀ ω, C.starProjection (designMap X βstar + ε ω) = designMap X (βhat ω) :=
    fun ω => ols_pred_eq_proj X (designMap X βstar + ε ω) (βhat ω) (hβ_ols ω)
  -- Step 2: Prediction error = projection of noise (since Xβ* ∈ C is a fixed point).
  have hXβstar_mem : designMap X βstar ∈ C := LinearMap.mem_range_self _ _
  have hpred_err : ∀ ω,
      designMap X (βhat ω) - designMap X βstar = C.starProjection (ε ω) := by
    intro ω
    have hfix : C.starProjection (designMap X βstar) = designMap X βstar :=
      Submodule.starProjection_mem_subspace_eq_self ⟨designMap X βstar, hXβstar_mem⟩
    rw [← hpred ω, map_add, hfix]
    abel
  -- Step 3: MSE at ω = (1/n) · ‖P_C(ε ω)‖².
  have hmse_eq : ∀ ω,
      mse X (βhat ω) βstar = (1 / ↑n : ℝ) * ‖C.starProjection (ε ω)‖ ^ 2 := by
    intro ω; simp only [mse, hpred_err ω]
  -- Step 4: Parseval — ‖P_C(x)‖² = ∑_{k<r} ⟪(b k : E), x⟫².
  have hParseval : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖C.starProjection x‖ ^ 2
        = ∑ k : Fin r, ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), x⟫_ℝ ^ 2 := by
    intro x
    rw [Submodule.starProjection_apply, Submodule.norm_coe,
        ← b.sum_sq_inner_right (C.orthogonalProjection x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact Submodule.inner_orthogonalProjection_eq_of_mem_left (b k) x
  -- Step 5: Each inner product ⟪(b k : E), ε⟫ is sub-Gaussian with proxy σ².
  have hinner_subG : ∀ k : Fin r,
      HasSubgaussianMGF (fun ω => ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ) σ2 μ := by
    intro k
    set e := ((b k : ↥C) : EuclideanSpace ℝ (Fin n)) with he_def
    have hinner_sum : ∀ ω, ⟪e, ε ω⟫_ℝ = ∑ i : Fin n, e i * (ε ω) i := by
      intro ω
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      change (ε ω) i * e i = e i * (ε ω) i
      ring
    have h_raw : ∀ i : Fin n, HasSubgaussianMGF (fun ω => (ε ω) i) σ2 μ := by
      intro i
      have h2 : HasSubgaussianMGF (fun ω => (ε ω) i - ∫ x, (ε x) i ∂μ) σ2 μ := hε_subG i
      rw [hε_meanz i] at h2; simpa using h2
    have h_indep_i : iIndepFun (fun (i : Fin n) (ω : Ω) => e i * (ε ω) i) μ := by
      have := hε_indep.comp (fun (i : Fin n) (x : ℝ) => e i * x)
        (fun i => measurable_const.mul measurable_id)
      exact this
    -- Sum of scaled independent coordinates is sub-Gaussian; collapse proxy via ‖e‖ = 1.
    have hsum_subG := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) h_indep_i
      (fun i _ => (h_raw i).const_mul (e i))
    have he_norm : ‖e‖ = 1 := by
      have hbk := b.orthonormal.1 k
      rw [he_def, Submodule.norm_coe]; exact hbk
    refine HasSubgaussianMGF.congr ?_ (ae_of_all _ fun ω => (hinner_sum ω).symm)
    convert hsum_subG using 2
    -- proxy equality:  σ2 = ∑ i, ⟨(e i)², _⟩ * σ2
    apply NNReal.coe_injective
    rw [NNReal.coe_sum]
    change (σ2 : ℝ) = ∑ x, e x ^ 2 * (σ2 : ℝ)
    rw [← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq e, he_norm]
    simp
  -- Step 6: Variance bound ⟹ E[⟪e_k, ε⟫²] ≤ σ2 (mean-0 is implied by `HasSubgaussianMGF`).
  have hE_sq : ∀ k : Fin r,
      ∫ ω, ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2 ∂μ ≤ σ2 :=
    fun k => hasSubgaussianMGF_integral_sq_le (hinner_subG k)
  -- Step 8: Assemble.
  have h_pointwise : ∀ ω, mse X (βhat ω) βstar =
      (1 / ↑n : ℝ) * ∑ k : Fin r,
        ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2 :=
    fun ω => (hmse_eq ω).trans (by rw [hParseval (ε ω)])
  have hint_inner_sq : ∀ k : Fin r,
      Integrable (fun ω => ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2) μ :=
    fun k => ((hinner_subG k).memLp 2).integrable_sq
  have hE_mse : ∫ ω, mse X (βhat ω) βstar ∂μ ≤ (1 / ↑n : ℝ) * (↑r * ↑σ2) := by
    rw [show (fun ω => mse X (βhat ω) βstar) =
          fun ω => (1 / ↑n : ℝ) * ∑ k : Fin r,
            ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2
          from funext h_pointwise,
        integral_const_mul,
        integral_finset_sum Finset.univ (fun k _ => hint_inner_sq k)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ k : Fin r, ∫ ω, ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2 ∂μ
        ≤ ∑ _k : Fin r, (σ2 : ℝ) := Finset.sum_le_sum (fun k _ => hE_sq k)
      _ = ↑r * ↑σ2 := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  -- Step 9: Convert to σ2 · designRank / n.
  calc ∫ ω, mse X (βhat ω) βstar ∂μ
      ≤ (1 / ↑n : ℝ) * (↑r * ↑σ2) := hE_mse
    _ = ↑σ2 * ↑(designRank X) / ↑n := by rw [hr_eq]; ring

end StatLean.HighDimensionalStatistics
