module
public import StatLean.HighDimensionalStatistics.LinearModel.Defs
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import StatLean.ConcentrationInequalities.Maximal.L2Maximal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# High-probability mean-squared error of ordinary least squares

Consider the linear model $Y = X\beta^\star + \varepsilon$ on $n$ observations,
where the noise vector $\varepsilon = (\varepsilon_1,\dots,\varepsilon_n)$ has
independent coordinates, each with mean zero and sub-Gaussian with
variance-proxy $\sigma^2$, and where $X$ has rank $r$. Let $\hat\beta$ be any
ordinary least-squares minimiser of $\lVert Y - X\beta\rVert^2$, and write
$\mathrm{MSE}(X\hat\beta) = \tfrac1n\lVert X(\hat\beta-\beta^\star)\rVert^2$ for
the prediction mean-squared error. Then for any confidence level
$\delta \in (0,1)$, with probability at least $1-\delta$,
$$\mathrm{MSE}(X\hat\beta) \;\le\; \frac{32\,\sigma^2 r}{n}
  \;+\; \frac{16\,\sigma^2}{n}\,\log\!\Big(\frac1\delta\Big).$$

This file provides two equivalent statements:

* `mse_ols_highProb_tail` — the **tail** form: the bad event where the prediction
  error exceeds the bound has probability at most $\delta$;
* `mse_ols_highProb_le` — the **confidence** form: the good event where the bound
  holds has probability at least $1-\delta$.

**Deviation from the book.** The textbook states the bound with the
order-of-magnitude symbol $\lesssim$ (a universal constant $C$). We pin the
explicit, *provable* constants $C = 32$ for the $\sigma^2 r/n$ term and $C' = 16$
for the $(\sigma^2/n)\log(1/\delta)$ term, which arise from squaring the
$\ell_2$-maximal tail bound $4\sigma\sqrt r + 2\sigma\sqrt{2\log(1/\delta)}$ via
$(a+b)^2 \le 2a^2 + 2b^2$. (The $\ell_2$-maximal bound itself carries a `log 5 ≤ 2`
deviation from the book; see `l2_max_tail`.) An extra hypothesis `0 < n` is
required so that $1/n$ is well-defined and the bound is finite — implicit in the
book's $n \to \infty$ framing.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 7 (Ordinary Least Squares), §7.2, Theorem 7.1
(Mean Squared Error of Least Squares), high-probability half; Eqs (7.1)–(7.2). The
proof invokes the maximal inequality for the $\ell_2$-norm, Chapter 6 (Bernstein
and Maximal Inequalities), §6.2, Theorem 6.3 (Maximal Inequality for ℓ²-Norm)
(`l2_max_tail`). (Project tags abbreviate these as `Lu-BDA §7.2 Theorem 7.1` and
`Lu-BDA §6.2 Theorem 6.3`.)

**Proof formalization notes.**
1. As in the expectation half, the OLS minimiser gives `Xβ̂ = P_C Y` and prediction
   error `Xβ̂ − Xβ* = P_C ε`, so `MSE = (1/n)‖P_C ε‖²`.
2. Encode the projected noise in an ONB `{e_k}_{k<r}` of `C = C(X)` as the
   random vector `Z ω = b.repr (P_C (ε ω)) ∈ E^r`. Then `‖Z ω‖ = ‖P_C ε‖`, each
   `⟨u, Z⟩ = ⟨w_u, ε⟩` is sub-Gaussian with proxy `σ²‖u‖²` (linear combination of
   independent sub-Gaussian coordinates), and `Z` is centered & integrable.
3. The ℓ²-maximal tail bound `l2_max_tail` (Lu §6.2 Theorem 6.3) gives, w.p. `≥ 1−δ`,
   `‖Z ω‖ ≤ 4σ√r + 2σ√(2 log(1/δ))`.
4. Squaring and dividing by `n`, with `(a+b)² ≤ 2a² + 2b²`:
   `MSE = ‖Z‖²/n ≤ 32 σ² r/n + 16 σ² log(1/δ)/n`.

The `r = 0` (trivial column space) case is handled separately: there `MSE = 0` and
the bound is `≥ 0`, so the bad event is empty.

**Bibliographic comments.** This is a folklore result with no single seminal
origin: it is the sub-Gaussian / $\ell_2$-maximal-concentration analysis of the
ordinary-least-squares prediction risk, assembled from standard ingredients —
the zero-order (least-squares) optimality condition, orthogonal projection onto
the column space, and a maximal/concentration tail bound for the norm of a
sub-Gaussian random vector. The same in-expectation and high-probability rates
$\sigma^2 r/n$ appear throughout the modern non-asymptotic literature, e.g.
M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*
(Cambridge University Press, 2019), Chapter 7, and R. Vershynin, *High-Dimensional
Probability* (Cambridge University Press, 2018), Chapter 6 (random vectors and
suprema of sub-Gaussian processes). We follow the formulation and constants of
Lu, *Big Data Analysis*, Theorem 7.1.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace StatLean.HighDimensionalStatistics
open StatLean.ConcentrationInequalities

variable {n d : ℕ}

/-! ### Sub-Gaussianity / integrability of `⟨w, ε⟩` for a sub-Gaussian noise vector -/

/-- Pointwise expansion of the Euclidean inner product as a coordinate sum. -/
private lemma inner_eq_sum (w x : EuclideanSpace ℝ (Fin n)) :
    ⟪w, x⟫_ℝ = ∑ i, w i * x i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change x i * w i = w i * x i
  ring

section EpsLemmas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {σ2 : ℝ≥0} {ε : Ω → EuclideanSpace ℝ (Fin n)}

/-- Each noise coordinate is (un-centered) `HasSubgaussianMGF σ²`, using mean-0. -/
private lemma eps_coord_hasSubG
    (hε_meanz : ∀ i : Fin n, ∫ ω, (ε ω) i ∂μ = 0)
    (hε_subG : ∀ i : Fin n, IsSubGaussian (fun ω => (ε ω) i) σ2 μ)
    (i : Fin n) : HasSubgaussianMGF (fun ω => (ε ω) i) σ2 μ := by
  have h2 : HasSubgaussianMGF (fun ω => (ε ω) i - ∫ x, (ε x) i ∂μ) σ2 μ := hε_subG i
  rw [hε_meanz i] at h2
  simpa using h2

/-- `⟨w, ε⟩` is integrable: a finite sum of scaled integrable coordinates. -/
private lemma eps_inner_integrable
    (hε_meanz : ∀ i : Fin n, ∫ ω, (ε ω) i ∂μ = 0)
    (hε_subG : ∀ i : Fin n, IsSubGaussian (fun ω => (ε ω) i) σ2 μ)
    (w : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ω => ⟪w, ε ω⟫_ℝ) μ := by
  have hsum : (fun ω => ⟪w, ε ω⟫_ℝ) = (fun ω => ∑ i, w i * (ε ω) i) :=
    funext fun ω => inner_eq_sum w (ε ω)
  rw [hsum]
  apply integrable_finset_sum
  intro i _
  exact ((eps_coord_hasSubG hε_meanz hε_subG i).integrable).const_mul (w i)

/-- `⟨w, ε⟩` has mean 0 (each coordinate does). -/
private lemma eps_inner_mean0
    (hε_meanz : ∀ i : Fin n, ∫ ω, (ε ω) i ∂μ = 0)
    (hε_subG : ∀ i : Fin n, IsSubGaussian (fun ω => (ε ω) i) σ2 μ)
    (w : EuclideanSpace ℝ (Fin n)) :
    ∫ ω, ⟪w, ε ω⟫_ℝ ∂μ = 0 := by
  have hcoord_int : ∀ i, Integrable (fun ω => (ε ω) i) μ :=
    fun i => (eps_coord_hasSubG hε_meanz hε_subG i).integrable
  calc ∫ ω, ⟪w, ε ω⟫_ℝ ∂μ
      = ∫ ω, ∑ i, w i * (ε ω) i ∂μ := by simp_rw [inner_eq_sum]
    _ = ∑ i, ∫ ω, w i * (ε ω) i ∂μ :=
          integral_finset_sum _ (fun i _ => (hcoord_int i).const_mul _)
    _ = ∑ i, w i * ∫ ω, (ε ω) i ∂μ := by simp_rw [integral_const_mul]
    _ = 0 := by simp [hε_meanz]

/-- **Linear combination of independent sub-Gaussian coordinates.**
For a noise vector `ε` with jointly independent mean-0 coordinates each sub-Gaussian
with proxy `σ²`, the linear functional `⟨w, ε⟩ = ∑ᵢ wᵢ εᵢ` is sub-Gaussian with
proxy `σ²‖w‖²`.  This is the `subGaussian_coords` argument (Lu-BDA §4.2 Theorem 4.7
(Hoeffding Inequality) / linear-combination rule), generalised from a unit ONB
vector to an arbitrary `w`. -/
private lemma eps_inner_subGaussian
    (hε_indep : iIndepFun (fun (i : Fin n) (ω : Ω) => (ε ω) i) μ)
    (hε_meanz : ∀ i : Fin n, ∫ ω, (ε ω) i ∂μ = 0)
    (hε_subG : ∀ i : Fin n, IsSubGaussian (fun ω => (ε ω) i) σ2 μ)
    (w : EuclideanSpace ℝ (Fin n)) :
    IsSubGaussian (fun ω => ⟪w, ε ω⟫_ℝ) (σ2 * ‖w‖₊ ^ 2) μ := by
  have hinner_sum : ∀ ω, ⟪w, ε ω⟫_ℝ = ∑ i, w i * (ε ω) i :=
    fun ω => inner_eq_sum w (ε ω)
  have h_raw : ∀ i, HasSubgaussianMGF (fun ω => (ε ω) i) σ2 μ :=
    fun i => eps_coord_hasSubG hε_meanz hε_subG i
  have h_indep : iIndepFun (fun (i : Fin n) (ω : Ω) => w i * (ε ω) i) μ := by
    have := hε_indep.comp (fun (i : Fin n) (x : ℝ) => w i * x)
      (fun i => measurable_const.mul measurable_id)
    exact this
  -- Sum of scaled independent sub-Gaussian coordinates.
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) h_indep
    (fun i _ => (h_raw i).const_mul (w i))
  -- Assemble: rewrite the function (mean-0) and collapse the proxy to `σ²‖w‖²`.
  have hfinal := HasSubgaussianMGF.congr hsum (ae_of_all _ fun ω => (hinner_sum ω).symm)
  rw [isSubGaussian_iff]
  simp only [eps_inner_mean0 hε_meanz hε_subG w, sub_zero]
  convert hfinal using 2
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_mk, coe_nnnorm]
  calc (σ2 : ℝ) * ‖w‖ ^ 2 = ∑ i, w i ^ 2 * (σ2 : ℝ) := by
        rw [← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq w]; ring
    _ = _ := Finset.sum_congr rfl fun i _ => rfl

end EpsLemmas

/-! ### Helper: a Euclidean Bochner integral with all coordinate-means 0 is 0 -/

/-- If a Euclidean-space-valued integrable function has every coordinate mean equal
to 0, its Bochner integral is 0. -/
private lemma euclidean_integral_eq_zero_of_coords
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m : ℕ}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (hf : Integrable f μ) (hcoord : ∀ i, ∫ ω, (f ω) i ∂μ = 0) :
    ∫ ω, f ω ∂μ = 0 := by
  refine PiLp.ext (fun i => ?_)
  rw [show ((0 : EuclideanSpace ℝ (Fin m)).ofLp i) = 0 from rfl]
  have hcomm := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) i) hf
  simp only [EuclideanSpace.coe_proj] at hcomm
  rw [← hcomm]
  exact hcoord i

/-! ### OLS prediction = orthogonal projection (re-derived, cf. `MSEExpectation`) -/

/-- The OLS residual `Y − Xβ̂` is orthogonal to every element of `columnSpace X`
(the first-order least-squares condition). -/
private lemma ols_residual_orthogonal
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: βhat minimises ‖Y − Xβ‖² (OLS); Lu-BDA §7.2 Theorem 7.1
    (hols : IsOLSEstimator X Y βhat)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ columnSpace X) :
    ⟪Y - designMap X βhat, w⟫_ℝ = 0 := by
  obtain ⟨γ, rfl⟩ := hw
  have expand : ∀ t : ℝ,
      ‖(Y - designMap X βhat) - t • designMap X γ‖ ^ 2
        = ‖Y - designMap X βhat‖ ^ 2
          - 2 * t * ⟪Y - designMap X βhat, designMap X γ⟫_ℝ
          + t ^ 2 * ‖designMap X γ‖ ^ 2 := by
    intro t
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have key : ∀ t : ℝ,
      0 ≤ t ^ 2 * ‖designMap X γ‖ ^ 2 - 2 * t * ⟪Y - designMap X βhat, designMap X γ⟫_ℝ := by
    intro t
    have hcomp := hols (βhat + t • γ)
    rw [map_add, map_smul] at hcomp
    have he : Y - (designMap X βhat + t • designMap X γ)
        = (Y - designMap X βhat) - t • designMap X γ := by abel
    rw [he, expand t] at hcomp
    linarith
  set c := ⟪Y - designMap X βhat, designMap X γ⟫_ℝ with hc
  set s := ‖designMap X γ‖ ^ 2 with hs
  have hs_nn : 0 ≤ s := by rw [hs]; positivity
  have h2pos : (0 : ℝ) < 2 + s := by linarith
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

/-- The OLS prediction `Xβ̂` equals the orthogonal projection of `Y` onto
`columnSpace X`. -/
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

/-- `designRank X = finrank (columnSpace X)`. -/
private lemma designRank_eq_finrank_columnSpace (X : Matrix (Fin n) (Fin d) ℝ) :
    designRank X = Module.finrank ℝ ↥(columnSpace X) := by
  simp only [designRank, columnSpace, designMap, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.rank_eq_finrank_range_toLin X
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

/-! ### Main theorems -/

/-- **High-probability MSE of OLS — tail form (Lu-BDA §7.2 Theorem 7.1).**

For `Y ω = X β* + ε ω` with independent mean-0 sub-Gaussian (proxy `σ²`) noise
coordinates and `δ ∈ (0,1)`, the bad event has measure `≤ δ`:
`μ {ω | 32 σ² r/n + 16 (σ²/n) log(1/δ) < MSE(Xβ̂, Xβ*)} ≤ δ`, with `r = rank X`. -/
theorem mse_ols_highProb_tail
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ)
    -- LEAN-ONLY: needed so `(1/n : ℝ)` is well-defined and the bound is finite; no scope change
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
    -- USER-INPUT: βhat ω minimises ‖Y ω − Xβ‖² for Y ω = Xβ* + ε ω; Lu-BDA §7.2 Theorem 7.1
    (hβ_ols : ∀ ω, IsOLSEstimator X (designMap X βstar + ε ω) (βhat ω))
    -- USER-INPUT: confidence level δ ∈ (0,1); Lu-BDA §7.2 Theorem 7.1
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ {ω | 32 * (σ2 : ℝ) * (designRank X : ℝ) / (n : ℝ)
            + 16 * ((σ2 : ℝ) / (n : ℝ)) * Real.log (1 / δ) < mse X (βhat ω) βstar}
      ≤ ENNReal.ofReal δ := by
  -- Setup: column space, completeness, orthogonal projection.
  let C := columnSpace X
  haveI hC_fd : FiniteDimensional ℝ ↥C := LinearMap.finiteDimensional_range _
  haveI hC_proj : C.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace C
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Step 1–3: MSE = (1/n)‖P_C ε‖².
  have hmse_eq : ∀ ω, mse X (βhat ω) βstar = (1 / (n : ℝ)) * ‖C.starProjection (ε ω)‖ ^ 2 := by
    have hpred : ∀ ω, C.starProjection (designMap X βstar + ε ω) = designMap X (βhat ω) :=
      fun ω => ols_pred_eq_proj X (designMap X βstar + ε ω) (βhat ω) (hβ_ols ω)
    have hXβstar_mem : designMap X βstar ∈ C := LinearMap.mem_range_self _ _
    have hpred_err : ∀ ω,
        designMap X (βhat ω) - designMap X βstar = C.starProjection (ε ω) := by
      intro ω
      have hfix : C.starProjection (designMap X βstar) = designMap X βstar :=
        Submodule.starProjection_mem_subspace_eq_self ⟨designMap X βstar, hXβstar_mem⟩
      rw [← hpred ω, map_add, hfix]; abel
    intro ω; simp only [mse, hpred_err ω]
  let R := Module.finrank ℝ ↥C
  have hrank : designRank X = R := designRank_eq_finrank_columnSpace X
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · -- r = 0: column space trivial ⟹ MSE = 0 ⟹ bound ≥ 0 ⟹ bad event empty.
    have hCbot : C = ⊥ := Submodule.finrank_eq_zero.mp hR0
    have hmse0 : ∀ ω, mse X (βhat ω) βstar = 0 := by
      intro ω
      rw [hmse_eq ω]
      have hz : C.starProjection (ε ω) = 0 := by
        rw [Submodule.starProjection_apply_eq_zero_iff, hCbot]
        simp
      rw [hz, norm_zero]; simp
    have hlog : 0 ≤ Real.log (1 / δ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    have hbnd_nonneg : 0 ≤ 32 * (σ2 : ℝ) * (designRank X : ℝ) / (n : ℝ)
        + 16 * ((σ2 : ℝ) / (n : ℝ)) * Real.log (1 / δ) := by
      have h1 : (0 : ℝ) ≤ 32 * (σ2 : ℝ) * (designRank X : ℝ) / (n : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ 16 * ((σ2 : ℝ) / (n : ℝ)) * Real.log (1 / δ) := by
        apply mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hlog
      linarith
    have hempty : {ω | 32 * (σ2 : ℝ) * (designRank X : ℝ) / (n : ℝ)
        + 16 * ((σ2 : ℝ) / (n : ℝ)) * Real.log (1 / δ) < mse X (βhat ω) βstar} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hmse0 ω]; exact hbnd_nonneg
    rw [hempty]; simp
  · -- r > 0: encode projected noise as an r-dimensional sub-Gaussian vector.
    haveI : NeZero R := ⟨hRpos.ne'⟩
    let b : OrthonormalBasis (Fin R) ℝ ↥C := stdOrthonormalBasis ℝ ↥C
    let Z : Ω → EuclideanSpace ℝ (Fin R) := fun ω => b.repr (C.orthogonalProjection (ε ω))
    have hZdef : ∀ ω, Z ω = b.repr (C.orthogonalProjection (ε ω)) := fun ω => rfl
    -- coordinate formula
    have hZcoord : ∀ ω, ∀ k, (Z ω).ofLp k = ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ := by
      intro ω k
      rw [hZdef ω, OrthonormalBasis.repr_apply_apply]
      exact Submodule.inner_orthogonalProjection_eq_of_mem_left (b k) (ε ω)
    -- norm: ‖Z ω‖ = ‖P_C ε‖
    have hZnorm : ∀ ω, ‖Z ω‖ = ‖C.starProjection (ε ω)‖ := by
      intro ω
      rw [hZdef ω, b.repr.norm_map, ← Submodule.norm_coe, ← Submodule.starProjection_apply]
    -- integrability
    have hZ_int : Integrable Z μ := by
      rw [integrable_piLp_iff]
      intro k
      rw [show (fun ω => (Z ω).ofLp k)
            = (fun ω => ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ)
          from funext fun ω => hZcoord ω k]
      exact eps_inner_integrable hε_meanz hε_subG _
    -- centering
    have hZ_center : ∫ ω, Z ω ∂μ = 0 := by
      apply euclidean_integral_eq_zero_of_coords hZ_int
      intro k
      calc ∫ ω, (Z ω) k ∂μ
          = ∫ ω, ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ∂μ := by
            apply integral_congr_ae; filter_upwards with ω; exact hZcoord ω k
        _ = 0 := eps_inner_mean0 hε_meanz hε_subG _
    -- direction-wise sub-Gaussianity
    have hZ_subG : ∀ u : EuclideanSpace ℝ (Fin R),
        IsSubGaussian (fun ω => inner ℝ u (Z ω)) (σ2 * ‖u‖₊ ^ 2) μ := by
      intro u
      set wu : EuclideanSpace ℝ (Fin n) :=
        ((b.repr.symm u : ↥C) : EuclideanSpace ℝ (Fin n)) with hwu_def
      have hwu_norm : ‖wu‖ = ‖u‖ := by
        rw [hwu_def, Submodule.norm_coe]; exact b.repr.symm.norm_map u
      have hinner_eq : ∀ ω, inner ℝ u (Z ω) = ⟪wu, ε ω⟫_ℝ := by
        intro ω
        rw [hZdef ω]
        conv_lhs => rw [show u = b.repr (b.repr.symm u) from (b.repr.apply_symm_apply u).symm]
        rw [b.repr.inner_map_map, Submodule.inner_orthogonalProjection_eq_of_mem_left]
      have hnn : ‖u‖₊ = ‖wu‖₊ := by
        rw [← NNReal.coe_inj, coe_nnnorm, coe_nnnorm]; exact hwu_norm.symm
      rw [show (fun ω => inner ℝ u (Z ω)) = (fun ω => ⟪wu, ε ω⟫_ℝ) from funext hinner_eq, hnn]
      exact eps_inner_subGaussian hε_indep hε_meanz hε_subG wu
    -- Step 3: ℓ²-maximal tail bound for the r-dimensional sub-Gaussian vector Z.
    have htail := l2_max_tail hZ_center hZ_subG hZ_int hδ0
    set t := 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (R : ℝ)
              + 2 * Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (1 / δ)) with ht_def
    have ht_nonneg : 0 ≤ t := by rw [ht_def]; positivity
    -- Step 4: t² ≤ 32 σ² r + 16 σ² log(1/δ)  (via (a+b)² ≤ 2a² + 2b²).
    have htsq : t ^ 2 ≤ 32 * (σ2 : ℝ) * (R : ℝ) + 16 * (σ2 : ℝ) * Real.log (1 / δ) := by
      have hlog : 0 ≤ Real.log (1 / δ) :=
        Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
      rw [ht_def]
      set s := Real.sqrt (σ2 : ℝ) with hs_def
      set p := Real.sqrt (R : ℝ) with hp_def
      set q := Real.sqrt (2 * Real.log (1 / δ)) with hq_def
      have hs2 : s ^ 2 = (σ2 : ℝ) := Real.sq_sqrt σ2.coe_nonneg
      have hp2 : p ^ 2 = (R : ℝ) := Real.sq_sqrt (Nat.cast_nonneg R)
      have hq2 : q ^ 2 = 2 * Real.log (1 / δ) := Real.sq_sqrt (by linarith)
      nlinarith [mul_nonneg σ2.coe_nonneg (sq_nonneg (2 * p - q)), hp2, hq2, hs2]
    -- Bad-event bound.
    set bnd := 32 * (σ2 : ℝ) * (designRank X : ℝ) / (n : ℝ)
                + 16 * ((σ2 : ℝ) / (n : ℝ)) * Real.log (1 / δ) with hbnd_def
    have hpoint : ∀ ω, ‖Z ω‖ ≤ t → mse X (βhat ω) βstar ≤ bnd := by
      intro ω hle
      have hmse : mse X (βhat ω) βstar = (1 / (n : ℝ)) * ‖Z ω‖ ^ 2 := by
        rw [hmse_eq ω, hZnorm ω]
      rw [hmse, hbnd_def]
      have hZsq : ‖Z ω‖ ^ 2 ≤ t ^ 2 := by
        nlinarith [hle, norm_nonneg (Z ω), ht_nonneg]
      have hninv : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      calc (1 / (n : ℝ)) * ‖Z ω‖ ^ 2
          ≤ (1 / (n : ℝ)) * t ^ 2 := mul_le_mul_of_nonneg_left hZsq hninv
        _ ≤ (1 / (n : ℝ)) * (32 * (σ2 : ℝ) * (R : ℝ) + 16 * (σ2 : ℝ) * Real.log (1 / δ)) :=
              mul_le_mul_of_nonneg_left htsq hninv
        _ = 32 * (σ2 : ℝ) * (designRank X : ℝ) / (n : ℝ)
              + 16 * ((σ2 : ℝ) / (n : ℝ)) * Real.log (1 / δ) := by rw [hrank]; ring
    have hsub : {ω | bnd < mse X (βhat ω) βstar} ⊆ {ω | t < ‖Z ω‖} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      by_contra hcon
      rw [not_lt] at hcon
      exact absurd (hpoint ω hcon) (not_le.mpr hω)
    calc μ {ω | bnd < mse X (βhat ω) βstar}
        ≤ μ {ω | t < ‖Z ω‖} := measure_mono hsub
      _ ≤ ENNReal.ofReal δ := htail

/-- **High-probability MSE of OLS — confidence form (Lu-BDA §7.2 Theorem 7.1).**

For `Y ω = X β* + ε ω` with independent mean-0 sub-Gaussian (proxy `σ²`) noise
coordinates and `δ ∈ (0,1)`, with probability at least `1 − δ`:
`MSE(Xβ̂, Xβ*) ≤ 32 σ² r/n + 16 (σ²/n) log(1/δ)`, with `r = rank X`.

Stated as `1 − δ ≤ μ {ω | MSE ≤ …}`; obtained from `mse_ols_highProb_tail` by the
complement (subadditivity) bridge `1 = μ univ ≤ μ{good} + μ{bad}`. -/
theorem mse_ols_highProb_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ)
    -- LEAN-ONLY: needed so `(1/n : ℝ)` is well-defined and the bound is finite; no scope change
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
    -- USER-INPUT: βhat ω minimises ‖Y ω − Xβ‖² for Y ω = Xβ* + ε ω; Lu-BDA §7.2 Theorem 7.1
    (hβ_ols : ∀ ω, IsOLSEstimator X (designMap X βstar + ε ω) (βhat ω))
    -- USER-INPUT: confidence level δ ∈ (0,1); Lu-BDA §7.2 Theorem 7.1
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ)
      ≤ μ {ω | mse X (βhat ω) βstar ≤ 32 * (σ2 : ℝ) * (designRank X : ℝ) / (n : ℝ)
                + 16 * ((σ2 : ℝ) / (n : ℝ)) * Real.log (1 / δ)} := by
  have htail := mse_ols_highProb_tail X hn hε_indep hε_meanz hε_subG βstar hβ_ols hδ0 hδ1
  set bnd := 32 * (σ2 : ℝ) * (designRank X : ℝ) / (n : ℝ)
              + 16 * ((σ2 : ℝ) / (n : ℝ)) * Real.log (1 / δ) with hbnd_def
  have hcompl : {ω | mse X (βhat ω) βstar ≤ bnd}ᶜ = {ω | bnd < mse X (βhat ω) βstar} := by
    ext ω; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have huniv : (1 : ℝ≥0∞)
      ≤ μ {ω | mse X (βhat ω) βstar ≤ bnd} + μ {ω | bnd < mse X (βhat ω) βstar} := by
    rw [← hcompl]
    calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
      _ = μ ({ω | mse X (βhat ω) βstar ≤ bnd} ∪ {ω | mse X (βhat ω) βstar ≤ bnd}ᶜ) := by
            rw [Set.union_compl_self]
      _ ≤ μ {ω | mse X (βhat ω) βstar ≤ bnd} + μ {ω | mse X (βhat ω) βstar ≤ bnd}ᶜ :=
            measure_union_le _ _
  have hkey : (1 : ℝ≥0∞) ≤ μ {ω | mse X (βhat ω) βstar ≤ bnd} + ENNReal.ofReal δ :=
    le_trans huniv (add_le_add le_rfl htail)
  rw [ENNReal.ofReal_sub _ (le_of_lt hδ0), ENNReal.ofReal_one, tsub_le_iff_right]
  exact hkey

end StatLean.HighDimensionalStatistics
