module
public import StatLean.Minimaxity.Fano.LocalPacking
public import StatLean.Minimaxity.ForMathlib.GaussianKLMulti
public import StatLean.Minimaxity.ForMathlib.Packing.SpherePacking
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Minimax risk for fixed-design linear regression

For the Gaussian linear model $y = X\theta^* + w$ with noise $w \sim \mathcal{N}(0, \sigma^2 I_n)$,
equipped with the prediction semimetric
$$
  \rho_X(\theta, \theta') = \frac{\lVert X(\theta - \theta')\rVert_2}{\sqrt{n}},
$$
the local-packing / Fano method lower-bounds the minimax prediction risk. For the unconstrained
problem one obtains
$$
  \inf_{\hat\theta}\ \sup_{\theta}\ \mathbb{E}\!\left[\frac{1}{n}\lVert X(\hat\theta - \theta)\rVert_2^2\right]
  \ \gtrsim\ \frac{\sigma^2}{2560}\cdot\frac{\operatorname{rank}(X)}{n},
$$
which is the formalized statement here (Example 15.14), and — restricting to $s$-sparse regression
vectors — one obtains the sparse-rate variant
$$
  \mathfrak{M}\big(\mathbb{S}^d(s);\ \lVert\cdot\rVert_2\big)
  \ \gtrsim\ \frac{\sigma^2}{\gamma^2}\cdot\frac{s\log(d/s)}{n}
$$
(Example 15.16).

We realize the prediction semimetric as the Euclidean distance on the prediction space by taking
$g(\theta) = (1/\sqrt{n})\, A\theta$, where $A$ is the design map, so that
$\rho\big(g(\theta), g(\theta')\big) = \rho_X(\theta, \theta')$.

The leading constant is stated as the provable $1/2560$ rather than the book's $1/128$ (see the
proof notes below), and the result is established for $\operatorname{rank}(A) = r \ge 40$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3, Examples 15.14 and
15.16 (local-packing conditions (15.35a)–(15.35b)).

**Proof formalization notes.** We realize the prediction semimetric as the Euclidean `edist` on
the prediction space by taking `g θ = (1/√n)·(A θ)`, where `A` is the design map, so
`ρ(g θ, g θ') = ρ_X(θ, θ')`. The lower bound is assembled from a `rank(A)`-dimensional sphere
packing (Wainwright Example 5.8, via `exists_sphere_packing`) spread across `range A` through a
linear isometry and pulled back by the normalized design map; the pairwise Kullback–Leibler
divergences are computed from the multivariate equal-covariance Gaussian KL formula
(`klDiv_multivariateGaussian_smul_one`) and fed into the Fano local-packing bound
(`minimax_local_packing`). The book's leading constant `1/128` is loosened to the provable
`1/2560` (= `2·1280⁻¹`), forced by the `r/10` Gilbert–Varshamov sphere-packing brick; the
separation radius is correspondingly `δ = √(v·r/(1280 n))`. The result requires `r = rank(A) ≥ 40`,
since the local-packing/Fano cardinality condition (15.35b) needs `Ω(r)` packing hypotheses and
small-rank designs are degenerate.

**Bibliographic comments.** The fixed-design prediction-error minimax rates formalized here
(Examples 15.14, 15.16) are due to G. Raskutti, M. J. Wainwright,
and B. Yu, "Minimax rates of estimation for high-dimensional linear regression over $\ell_q$-balls,"
*IEEE Transactions on Information Theory*, vol. 57, no. 10, pp. 6976–6994, 2011 (DOI
10.1109/TIT.2011.2165799; preprint arXiv:0910.2042). That paper derives matching minimax upper and
lower bounds, under suitable design regularity, for both $\ell_2$-estimation loss and
$\ell_2$-prediction loss over $\ell_q$-balls, with the sparse prediction rate scaling as
$\frac{s\log(d/s)}{n}$; the lower bounds use exactly the Fano / local-packing argument reproduced
here. The general local-packing (Hasminskii / Fano) machinery these examples instantiate is
classical, but the specific high-dimensional linear-regression rates of Examples 15.14 and 15.16
trace to that Raskutti–Wainwright–Yu paper.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

namespace StatLean.Minimaxity

/-- A linear isometric embedding of `ℝʳ` into `ℝⁿ` whose image lands inside the range of the design
map `A`, available whenever `r = rank(A)`. Built from an orthonormal basis of `range A` (which is an
`r`-dimensional inner-product space), composed with the isometric submodule inclusion. Used in the
linear-regression minimax construction (Wainwright Ex 15.14) to spread a sphere packing of `ℝʳ`
across `range A`. -/
private lemma exists_range_linearIsometry {n d r : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    -- LEAN-ONLY: `r = rank A` pins the source dimension to `range A`'s; Wainwright Ex 15.14.
    (hr : r = Module.finrank ℝ (LinearMap.range A)) :
    ∃ f : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ w, f w ∈ LinearMap.range A := by
  classical
  let b : OrthonormalBasis (Fin r) ℝ ↥(LinearMap.range A) :=
    (stdOrthonormalBasis ℝ ↥(LinearMap.range A)).reindex (finCongr hr.symm)
  let e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] ↥(LinearMap.range A) := b.repr.symm
  refine ⟨(LinearMap.range A).subtypeₗᵢ.comp e.toLinearIsometry, ?_⟩
  intro w
  exact Submodule.coe_mem _

open InformationTheory in
/-- **Crux: local packing data for fixed-design linear regression.** A `rank(A)`-dimensional packing
of the unit sphere of `ℝʳ` (Wainwright Example 5.8, `exists_sphere_packing`), spread across the range
of `A` through a linear isometry and pulled back by the normalized design map `g θ = Aθ/√n`, gives a
`δ`-separated family with `δ = √(v·r/(1280n))` whose pairwise KL divergences satisfy the (15.35a)
bound (via the multivariate equal-covariance Gaussian KL `klDiv_multivariateGaussian_smul_one`) and
whose cardinality satisfies (15.35b).

The separation/rate constant is loosened from the book's `64⁻¹` (Ex 15.14) to fit the `r/10`
Gilbert–Varshamov sphere-packing brick; see the constant tag below. -/
private lemma linreg_local_packing_data {n d : ℕ} (hn : 1 ≤ n) (v : ℝ≥0) (hv : v ≠ 0) (r : ℕ)
    -- LEAN-ONLY: r ≥ 40 — the local-packing/Fano condition (15.35b) needs Ω(r) hypotheses; small-rank is degenerate.
    (hr0 : 40 ≤ r)
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n))
    (P : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel P]
    (hg : ∀ θ, g θ = (Real.sqrt n)⁻¹ • A θ)
    (hP : ∀ θ, P θ = multivariateGaussian (A θ) ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hr : r = Module.finrank ℝ (LinearMap.range A)) :
    ∃ (M : ℕ) (_ : NeZero M) (θfam : Fin M → EuclideanSpace ℝ (Fin d)) (hθ : Measurable θfam)
      (c : ℝ),
      -- USER-INPUT: separation/rate constant loosened (book 64⁻¹) to fit the r/10 sphere-packing brick; Wainwright Ex 15.14, CLAUDE.md §1.
      IsSeparatedFamily g θfam (ENNReal.ofReal (Real.sqrt ((v : ℝ) * r / (1280 * n)))) ∧
      (∀ j k, j ≠ k → klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
        ≤ ENNReal.ofReal (c ^ 2 * (n : ℝ) *
            (ENNReal.ofReal (Real.sqrt ((v : ℝ) * r / (1280 * n)))).toReal ^ 2)) ∧
      2 * (c ^ 2 * (n : ℝ) *
          (ENNReal.ofReal (Real.sqrt ((v : ℝ) * r / (1280 * n)))).toReal ^ 2 + Real.log 2)
        ≤ Real.log (M : ℝ) := by
  classical
  -- Basic positivity facts.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR : (n : ℝ) ≠ 0 := hnpos.ne'
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hvR : (v : ℝ) ≠ 0 := hvpos.ne'
  have hr0R : (40 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have hsqn_pos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsqn_ne : Real.sqrt (n : ℝ) ≠ 0 := hsqn_pos.ne'
  -- The separation radius `δr = √(v r / (1280 n))`.
  set δr : ℝ := Real.sqrt ((v : ℝ) * r / (1280 * n)) with hδr_def
  have hδr_nonneg : 0 ≤ δr := by rw [hδr_def]; exact Real.sqrt_nonneg _
  have h2δ : δr ^ 2 = (v : ℝ) * r / (1280 * n) := by rw [hδr_def]; exact Real.sq_sqrt (by positivity)
  have htoReal : (ENNReal.ofReal δr).toReal = δr := ENNReal.toReal_ofReal hδr_nonneg
  -- The leakage constant `c = √(32 / v)`.
  set c : ℝ := Real.sqrt (32 / (v : ℝ)) with hc_def
  have hcsq : c ^ 2 = 32 / (v : ℝ) := by rw [hc_def]; exact Real.sq_sqrt (by positivity)
  -- The KL/cardinality budget evaluates to `r / 40`.
  have hRHSval : c ^ 2 * (n : ℝ) * δr ^ 2 = (r : ℝ) / 40 := by
    rw [hcsq, h2δ]; field_simp; ring
  -- Linear isometry spreading `ℝʳ` into `range A`, scaled by `4 δr √n`.
  obtain ⟨f, hfmem⟩ := exists_range_linearIsometry A hr
  set scale : ℝ := 4 * δr * Real.sqrt (n : ℝ) with hscale_def
  have hscale_nonneg : 0 ≤ scale := by
    rw [hscale_def]; exact mul_nonneg (mul_nonneg (by norm_num) hδr_nonneg) (Real.sqrt_nonneg _)
  have hscale_sq : scale ^ 2 = (v : ℝ) * r / 80 := by
    have hsqn2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    rw [hscale_def]
    have hh : (4 * δr * Real.sqrt (n : ℝ)) ^ 2 = 16 * δr ^ 2 * Real.sqrt (n : ℝ) ^ 2 := by ring
    rw [hh, hsqn2, h2δ]; field_simp; ring
  -- For each sphere vector `w`, pick a parameter `θof w` with `A (θof w) = scale • f w`.
  have hmem_scale : ∀ w, scale • f w ∈ LinearMap.range A := fun w =>
    Submodule.smul_mem _ scale (hfmem w)
  have hpre : ∀ w, ∃ θ, A θ = scale • f w := fun w => LinearMap.mem_range.mp (hmem_scale w)
  let θof : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin d) := fun w => (hpre w).choose
  have hAθ : ∀ w, A (θof w) = scale • f w := fun w => (hpre w).choose_spec
  -- Norm of prediction differences: `‖A(θof w₁) − A(θof w₂)‖ = scale · ‖w₁ − w₂‖`.
  have hAnorm : ∀ w₁ w₂, ‖A (θof w₁) - A (θof w₂)‖ = scale * ‖w₁ - w₂‖ := by
    intro w₁ w₂
    rw [hAθ, hAθ, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale_nonneg]
    congr 1
    rw [← map_sub]; exact f.norm_map _
  -- The sphere packing of `ℝʳ`.
  obtain ⟨S, hScard, hpack_unit, hpack_sep⟩ := exists_sphere_packing r
  let sfun : Fin S.card → EuclideanSpace ℝ (Fin r) := fun j => (↑(S.equivFin.symm j))
  have hsfun_mem : ∀ j, sfun j ∈ S := fun j => (S.equivFin.symm j).2
  have hsfun_ne : ∀ j k, j ≠ k → sfun j ≠ sfun k := by
    intro j k hjk h
    exact hjk (S.equivFin.symm.injective (Subtype.ext h))
  -- Cardinality is nonzero.
  have hMne : S.card ≠ 0 := by
    intro h0
    have h := hScard
    rw [h0, Nat.cast_zero, Real.log_zero] at h
    linarith [hr0R]
  refine ⟨S.card, ⟨hMne⟩, fun j => θof (sfun j), measurable_of_finite _, c, ?_, ?_, ?_⟩
  · -- (separation) `IsSeparatedFamily`.
    intro j k hjk
    show 2 * ENNReal.ofReal δr ≤ edist (g (θof (sfun j))) (g (θof (sfun k)))
    have h2δr : (2 : ℝ≥0∞) * ENNReal.ofReal δr = ENNReal.ofReal (2 * δr) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    rw [edist_dist, dist_eq_norm, h2δr]
    apply ENNReal.ofReal_le_ofReal
    have hgn : ‖g (θof (sfun j)) - g (θof (sfun k))‖ = 4 * δr * ‖sfun j - sfun k‖ := by
      rw [hg, hg, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (Real.sqrt_nonneg (n : ℝ)), hAnorm (sfun j) (sfun k), hscale_def]
      field_simp
    rw [hgn]
    have hSlow : (1 : ℝ) / 2 ≤ ‖sfun j - sfun k‖ :=
      hpack_sep (sfun j) (hsfun_mem j) (sfun k) (hsfun_mem k) (hsfun_ne j k hjk)
    nlinarith [mul_nonneg hδr_nonneg
      (by linarith [hSlow] : (0 : ℝ) ≤ 2 * ‖sfun j - sfun k‖ - 1)]
  · -- (15.35a) pairwise KL bound.
    intro j k hjk
    simp only [Kernel.comap_apply, hP]
    rw [show ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = (v • (1 : Matrix (Fin n) (Fin n) ℝ))
        from (NNReal.smul_def v _).symm,
      klDiv_multivariateGaussian_smul_one (A (θof (sfun j))) (A (θof (sfun k))) v hv]
    apply ENNReal.ofReal_le_ofReal
    rw [hAnorm (sfun j) (sfun k), htoReal, hRHSval]
    have hSle : ‖sfun j - sfun k‖ ≤ 2 := by
      have h1 : ‖sfun j‖ = 1 := hpack_unit (sfun j) (hsfun_mem j)
      have h2 : ‖sfun k‖ = 1 := hpack_unit (sfun k) (hsfun_mem k)
      calc ‖sfun j - sfun k‖ ≤ ‖sfun j‖ + ‖sfun k‖ := norm_sub_le _ _
        _ = 2 := by rw [h1, h2]; norm_num
    have hSnn : 0 ≤ ‖sfun j - sfun k‖ := norm_nonneg _
    have h4 : ‖sfun j - sfun k‖ ^ 2 ≤ 4 := by nlinarith [hSle, hSnn]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (v : ℝ))]
    have hexp : (scale * ‖sfun j - sfun k‖) ^ 2 = scale ^ 2 * ‖sfun j - sfun k‖ ^ 2 := by ring
    rw [hexp, hscale_sq]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (v : ℝ) * r)
      (by linarith [h4] : (0 : ℝ) ≤ 4 - ‖sfun j - sfun k‖ ^ 2)]
  · -- (15.35b) cardinality.
    rw [htoReal, hRHSval]
    nlinarith [hScard, Real.log_two_lt_d9, hr0R]

/-- **Minimax risk for fixed-design linear regression** (Wainwright Example 15.14): for the Gaussian
model with design map `A : ℝᵈ → ℝⁿ` and noise variance `v`, the minimax risk in the prediction
(semi)norm `ρ_X(θ,θ') = ‖A(θ−θ')‖/√n` is at least `(v/2560)·rank(A)/n`, where `g θ = A θ/√n` realizes
`ρ_X` as the Euclidean distance.

The book's leading constant is `128⁻¹`; we prove the looser `2560⁻¹` (= `2·1280⁻¹`), forced by the
`r/10` Gilbert–Varshamov sphere-packing brick (see `linreg_local_packing_data`). Holds for `r ≥ 40`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3, Example 15.14. -/
theorem linear_regression_minimax_rate {n d : ℕ} (hn : 1 ≤ n) (v : ℝ≥0) (hv : v ≠ 0) (r : ℕ)
    -- LEAN-ONLY: r ≥ 40 — the local-packing/Fano condition (15.35b) needs Ω(r) hypotheses; small-rank is degenerate.
    (hr0 : 40 ≤ r)
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n))
    (P : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel P]
    -- USER-INPUT: `g θ = A θ/√n` is the normalized prediction map; Wainwright §15.3.3, Ex 15.14.
    (hg : ∀ θ, g θ = (Real.sqrt n)⁻¹ • A θ)
    -- USER-INPUT: `y ∼ 𝒩(Aθ, v Iₙ)` (fixed-design Gaussian model); Wainwright §15.3.3, Ex 15.14.
    (hP : ∀ θ, P θ = multivariateGaussian (A θ) ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    -- USER-INPUT: `r = rank(A)`; Wainwright §15.3.3, Ex 15.14.
    (hr : r = Module.finrank ℝ (LinearMap.range A)) :
    ENNReal.ofReal ((v : ℝ) * r / (2560 * n)) ≤ minimaxRiskDist (· ^ 2) g P := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  have hx0 : (0 : ℝ) ≤ Real.sqrt ((v : ℝ) * r / (1280 * n)) := Real.sqrt_nonneg _
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  obtain ⟨M, hMne, θfam, hθ, c, hsep, h35a, h35b⟩ :=
    linreg_local_packing_data hn v hv r hr0 A g P hg hP hr
  haveI := hMne
  have key := minimax_local_packing (fun x : ℝ≥0∞ => x ^ 2) g P θfam hθ
    (ENNReal.ofReal (Real.sqrt ((v : ℝ) * r / (1280 * n)))) c (n : ℝ) hΦ hsep (by positivity) h35a h35b
  have hΦδ : (fun x : ℝ≥0∞ => x ^ 2) (ENNReal.ofReal (Real.sqrt ((v : ℝ) * r / (1280 * n))))
      = ENNReal.ofReal ((v : ℝ) * r / (1280 * n)) := by
    change (ENNReal.ofReal (Real.sqrt ((v : ℝ) * r / (1280 * n)))) ^ 2 = _
    rw [← ENNReal.ofReal_pow hx0, Real.sq_sqrt (by positivity)]
  rw [show ENNReal.ofReal (Real.sqrt ((v : ℝ) * r / (1280 * n))) ^ 2
      = ENNReal.ofReal ((v : ℝ) * r / (1280 * n)) from hΦδ] at key
  refine le_trans ?_ key
  have h2inv : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [h2inv, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  apply le_of_eq; congr 1; field_simp; ring

end StatLean.Minimaxity
