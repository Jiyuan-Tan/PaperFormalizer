module
public import StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
public import StatLean.ConcentrationInequalities.Maximal.CoveringBall
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# ℓ²-Norm Maximal Inequality

Let $X$ be a random vector in $\mathbb{R}^d$ that is *sub-Gaussian as a vector*: for
every direction $u \in \mathbb{R}^d$, the projection $\langle u, X\rangle$ is a
sub-Gaussian random variable with variance proxy $\sigma^2\|u\|^2$. Then the Euclidean
norm of $X$ obeys, in expectation,
$$\mathbb{E}\,\|X\| \le 4\,\sigma\,\sqrt{d},$$
and, as a high-probability tail bound, for every $\delta > 0$ with probability at
least $1-\delta$,
$$\|X\| \le 4\,\sigma\,\sqrt{d} + 2\,\sigma\,\sqrt{2\log(1/\delta)}.$$

Formalized as `l2_max_expectation` (expectation bound) and `l2_max_tail` (tail bound),
where the tail statement is phrased equivalently as a bound on the measure of the event
$\{\,4\sigma\sqrt{d} + 2\sigma\sqrt{2\log(1/\delta)} < \|X\|\,\}$.

*Added hypotheses (relative to the book statement).* The book states the result for a
random vector $X$ without an explicit centering or integrability condition; the Lean
formalization additionally assumes $\mathbb{E}[X] = 0$ (`hcenter`) and Bochner
integrability of $X$ (`hX_int`). Centering is the assumption under which the underlying
finite-maximum bounds (`expectation_max_le` / `tail_max_le`) hold; integrability is a
Lean-side regularity input that is in fact implied by sub-Gaussianity in finite
dimension. The conclusion's constants ($4\sigma\sqrt{d}$ and the additive
$2\sigma\sqrt{2\log(1/\delta)}$) match the book exactly.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 6 (Bernstein and Maximal Inequalities), §6.2,
Theorem 6.3 (Maximal Inequality for ℓ²-Norm).

**Proof formalization notes.** Discretization trick (Lu §6.2). Take a $1/2$-net $N$ of
the unit ball $\mathcal{B}_2^d = $ `closedBall 0 1`, with cardinality $|N| \le 5^d$
(covering-number bound). For a unit vector $u = x/\|x\|$ pick $v \in N$ with
$\|u - v\| \le 1/2$; the variational identity $\|x\| = \langle x/\|x\|, x\rangle$
together with Cauchy–Schwarz on $\langle u - v, X\rangle$ gives the key reduction
$\|x\| \le 2\max_{v \in N} \langle v, x\rangle$, turning a supremum over the infinite
ball into a maximum over the finite net. Each projection $\langle v, X\rangle$ with
$\|v\| \le 1$ is sub-Gaussian with proxy $\sigma^2$, so `expectation_max_le` and
`tail_max_le` control the finite maximum. Using $\log 5 \le 2$ relaxes
$\sqrt{2d\log 5} \le 2\sqrt{d}$, yielding the clean constants.

Deviation from book: the constant uses $\log 5 \le 2$ (equivalently $5 \le e^2$) to
relax $\sqrt{2d\log 5} \le 2\sqrt{d}$. The tail proof's numerical core
(`l2_tail_numerical`) establishes $k\cdot\exp(-(t/2)^2/(2\sigma^2)) \le \delta$ for
$t = 4\sigma\sqrt{d} + 2\sigma\sqrt{2\log(1/\delta)}$ and $k \le 5^d$, via
$5^d \le \exp(2d)$ and the expansion $(A+B)^2/2 \ge 2d + \log(1/\delta)$ with
$A = 2\sqrt{d}$, $B = \sqrt{2\log(1/\delta)}$ and nonnegative cross term; the
$\sigma^2 = 0$ corner case (degenerate $X = 0$ a.e.) is handled separately in
`l2_max_tail`.

**Bibliographic comments.** This is a folklore result with no single seminal
research-paper origin: it is the standard $\epsilon$-net (discretization) argument for
the norm of a sub-Gaussian random vector, where the supremum $\|X\| = \max_{u\in
\mathcal{B}_2}\langle u, X\rangle$ over the unit sphere is reduced to a maximum over a
finite net and then controlled by a finite sub-Gaussian maximal inequality. The
covering/net method goes back to classical metric-entropy arguments in geometric
functional analysis (Kolmogorov–Tikhomirov $\epsilon$-entropy; Sudakov–Dudley
chaining).
-/

open MeasureTheory ProbabilityTheory Real Metric Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Private helpers -/

/-- Monotonicity of `HasSubgaussianMGF` in the variance proxy. -/
private lemma hasSubgaussianMGF_mono {X : Ω → ℝ} {c d : ℝ≥0} {μ : Measure Ω}
    (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr (by
    have hcd' : (c : ℝ) ≤ d := NNReal.coe_le_coe.mpr hcd
    nlinarith [sq_nonneg t]))

/-- Monotonicity of `IsSubGaussian` in the variance proxy. -/
private lemma isSubGaussian_mono {X : Ω → ℝ} {c d : ℝ≥0} {μ : Measure Ω}
    (h : IsSubGaussian X c μ) (hcd : c ≤ d) : IsSubGaussian X d μ :=
  hasSubgaussianMGF_mono h hcd

/-- If `X` is a sub-Gaussian vector (each direction `u` has `⟨u, X⟩` sub-Gaussian with
proxy `σ²‖u‖₊²`) and `‖v‖ ≤ 1`, then `⟨v, X⟩` is sub-Gaussian with proxy `σ²`. -/
private lemma isSubGaussian_inner_of_norm_le
    {d : ℕ} [NeZero d] {μ : Measure Ω} {σ2 : ℝ≥0}
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ u : EuclideanSpace ℝ (Fin d),
        IsSubGaussian (fun ω => inner ℝ u (X ω)) (σ2 * ‖u‖₊ ^ 2) μ)
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ ≤ 1) :
    IsSubGaussian (fun ω => inner ℝ v (X ω)) σ2 μ := by
  apply isSubGaussian_mono (hX v)
  nth_rewrite 2 [← mul_one σ2]
  apply mul_le_mul_of_nonneg_left _ (zero_le)
  have h_nnnorm_le : (‖v‖₊ : ℝ) ≤ 1 := by exact_mod_cast hv
  have h_sq_le : (‖v‖₊ : ℝ) ^ 2 ≤ 1 := by
    nlinarith [NNReal.coe_nonneg ‖v‖₊, sq_nonneg (1 - (‖v‖₊ : ℝ))]
  exact_mod_cast h_sq_le

/-- `log 5 ≤ 2`, i.e., `5 ≤ e²`.  Used to relax `√(2d log 5) ≤ 2√d`. -/
private lemma log_five_le_two : Real.log 5 ≤ 2 := by
  rw [show (2 : ℝ) = Real.log (Real.exp 2) from (Real.log_exp 2).symm]
  apply Real.log_le_log (by norm_num)
  have h := Real.sum_le_exp_of_nonneg (x := 2) (by norm_num) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h; linarith

/-- Integrability of `fun ω => ⨆ j : Fin d, f j ω` when each `f j` is integrable.
Dominated by `∑ ‖f j ω‖`. -/
private lemma integrable_iSup_fin
    {d : ℕ} [NeZero d] {μ : Measure Ω}
    {f : Fin d → Ω → ℝ} (hf : ∀ j, Integrable (f j) μ) :
    Integrable (fun ω => ⨆ j, f j ω) μ := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero d)
  apply Integrable.mono' (g := fun ω => ∑ j : Fin d, ‖f j ω‖)
  · exact integrable_finset_sum _ (fun j _ => (hf j).norm)
  · exact (AEMeasurable.iSup (fun j =>
        (hf j).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  · filter_upwards with ω
    simp only [Real.norm_eq_abs]
    have hbdd : BddAbove (Set.range (fun j => f j ω)) := Finite.bddAbove_range _
    have h1 : ⨆ j, f j ω ≤ ∑ j : Fin d, |f j ω| :=
      ciSup_le fun j =>
        (le_abs_self _).trans
          (Finset.single_le_sum (f := fun k => |f k ω|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j))
    have h2 : -(⨆ j, f j ω) ≤ ∑ j : Fin d, |f j ω| :=
      calc -(⨆ j, f j ω)
          ≤ -(f 0 ω) := neg_le_neg (le_ciSup hbdd 0)
        _ ≤ |f 0 ω| := by rw [← abs_neg]; exact le_abs_self _
        _ ≤ ∑ j : Fin d, |f j ω| :=
            Finset.single_le_sum (f := fun k => |f k ω|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ 0)
    exact abs_le.mpr ⟨by linarith, h1⟩

/-! ### Common net infrastructure (used by both main theorems) -/

/-- Build a 1/2-net `F : Finset` of the unit ball in `EuclideanSpace ℝ (Fin d)`.
Returns `⟨F, he, hcov⟩` where `F` is a Finset, `he` enumerates it, `hcov` is the
covering property, and the cardinality satisfies `F.card ≤ 5^d`. -/
private structure L2NetData (d : ℕ) [NeZero d] where
  F : Finset (EuclideanSpace ℝ (Fin d))
  hF_nonempty : F.Nonempty
  hF_norm : ∀ v ∈ F, ‖v‖ ≤ 1
  hF_cover : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
               ∃ v ∈ F, dist x v ≤ 1 / 2
  hF_card_le : F.card ≤ 5 ^ d

/-- Construct the 1/2-net data via `Metric.minimalCover`. -/
private noncomputable def buildL2Net (d : ℕ) [NeZero d]
    [DecidableEq (EuclideanSpace ℝ (Fin d))] : L2NetData d := by
  let ε' : ℝ≥0 := Real.toNNReal (1 / 2)
  have hcov_ne_top : Metric.coveringNumber ε' (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _)
      (coveringNumber_closedBall_le (d := d) (ε := 1 / 2) (by norm_num) (by norm_num))
  let N := Metric.minimalCover ε' (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hN_cov : Metric.IsCover ε' (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) N :=
    Metric.isCover_minimalCover hcov_ne_top
  have hN_fin : N.Finite := Metric.finite_minimalCover
  have hN_sub : N ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    Metric.minimalCover_subset
  let F := hN_fin.toFinset
  have hN_nonempty : N.Nonempty := by
    obtain ⟨v, hv_N, _⟩ := hN_cov (Metric.mem_closedBall_self zero_le_one)
    exact ⟨v, hv_N⟩
  have hF_nonempty : F.Nonempty := hN_fin.toFinset_nonempty.mpr hN_nonempty
  have hF_norm : ∀ v ∈ F, ‖v‖ ≤ 1 := fun v hv => by
    have := hN_sub (hN_fin.mem_toFinset.mp hv)
    simp only [mem_closedBall, dist_zero_right] at this; exact this
  have hF_cover : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∃ v ∈ F, dist x v ≤ 1 / 2 := fun x hx => by
    obtain ⟨v, hv_N, hv_edist⟩ := hN_cov hx
    refine ⟨v, hN_fin.mem_toFinset.mpr hv_N, ?_⟩
    rw [← edist_le_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc edist x v ≤ (ε' : ℝ≥0∞) := hv_edist
      _ = ENNReal.ofReal (1 / 2) := by simp [ε', ENNReal.ofReal, Real.toNNReal]
  have hF_card_le : F.card ≤ 5 ^ d := by
    apply ENat.coe_le_coe.mp
    calc (F.card : ℕ∞)
        = N.encard := hN_fin.encard_eq_coe_toFinset_card.symm
      _ = Metric.coveringNumber ε' (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
            Metric.encard_minimalCover hcov_ne_top
      _ = coveringNumber (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (1 / 2 : ℝ) := rfl
      _ ≤ (⌊(1 + 2 / (1 / 2 : ℝ)) ^ d⌋₊ : ℕ∞) :=
            coveringNumber_closedBall_le (by norm_num) (by norm_num)
      _ = ((5 : ℕ) ^ d : ℕ∞) := by
            norm_cast
            rw [show ⌊(1 + 2 / (1 / 2 : ℝ)) ^ d⌋₊ = 5 ^ d from by
              have : (1 + 2 / (1 / 2 : ℝ)) ^ d = ((5 ^ d : ℕ) : ℝ) := by push_cast; norm_num
              rw [this, Nat.floor_natCast]]
  exact ⟨F, hF_nonempty, hF_norm, hF_cover, hF_card_le⟩

/-! ### Main theorems -/

/-- **ℓ²-Norm Maximal Inequality — expectation bound** (Lu-BDA §6.2, Theorem 6.3).

For a centered sub-Gaussian random vector `X : Ω → EuclideanSpace ℝ (Fin d)` with
variance proxy `σ²‖u‖₊²` for every direction `u`, under a probability measure `μ`:
```
E[‖X‖] ≤ 4σ√d
```

Proof (Lu §6.2): take a 1/2-net `N` of `closedBall 0 1` with `|N| ≤ 5^d`.  The
variational identity `‖x‖ = ⟨x/‖x‖, x⟩` and the net give `‖x‖ ≤ 2 max_{v∈N} ⟨v,x⟩`.
Each `⟨v, X⟩` is sub-Gaussian with proxy `σ²`, so `expectation_max_le` gives
`E[max ⟨v,X⟩] ≤ σ√(2 log|N|) ≤ σ√(2d log 5) ≤ 2σ√d`.  Combined: `E‖X‖ ≤ 4σ√d`.

Deviation from book: constant uses `log 5 ≤ 2`. -/
theorem l2_max_expectation
    {d : ℕ} [NeZero d]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {σ2 : ℝ≥0}
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: E[X] = 0; Lu-BDA §6.2 Theorem 6.3
    (hcenter : ∫ ω, X ω ∂μ = 0)
    -- USER-INPUT: ⟨u, X⟩ sub-Gaussian with proxy σ²‖u‖₊²; Lu-BDA §6.2 Theorem 6.3
    (hX : ∀ u : EuclideanSpace ℝ (Fin d),
        IsSubGaussian (fun ω => inner ℝ u (X ω)) (σ2 * ‖u‖₊ ^ 2) μ)
    -- LEAN-ONLY: Bochner integrability; implied by sub-Gaussianity in finite dimension
    (hX_int : Integrable X μ) :
    ∫ ω, ‖X ω‖ ∂μ ≤ 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) := by
  haveI : DecidableEq (EuclideanSpace ℝ (Fin d)) := Classical.decEq _
  -- *** Step 1: Construct 1/2-net ***
  let net := buildL2Net d
  let F := net.F
  let k := F.card
  have hk_pos : 0 < k := Finset.card_pos.mpr net.hF_nonempty
  haveI hk_ne : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk_pos⟩
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk_pos
  -- *** Step 2: Enumerate net as Fin k → E ***
  let e : Fin k → EuclideanSpace ℝ (Fin d) := fun j => (F.equivFin.symm j : F).val
  have he_norm : ∀ j, ‖e j‖ ≤ 1 := fun j =>
    net.hF_norm (e j) (F.equivFin.symm j).prop
  -- *** Step 3: Y j ω = ⟨e j, X ω⟩ is centered sub-Gaussian ***
  let Y : Fin k → Ω → ℝ := fun j ω => inner ℝ (e j) (X ω)
  have hY_int : ∀ j, Integrable (Y j) μ := fun j =>
    (innerSL ℝ (e j) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integrable_comp hX_int
  have hcenter_Y : ∀ j, ∫ ω, Y j ω ∂μ = 0 := fun j => by
    simp only [Y, ← innerSL_apply_apply]
    rw [(innerSL ℝ (e j)).integral_comp_comm hX_int, hcenter, map_zero]
  have hY_sg : ∀ j, IsSubGaussian (Y j) σ2 μ := fun j =>
    isSubGaussian_inner_of_norm_le hX (he_norm j)
  -- *** Step 4: Discretization — ‖X ω‖ ≤ 2 * ⨆ j, Y j ω ***
  have hdiscr : ∀ ω, ‖X ω‖ ≤ 2 * ⨆ j, Y j ω := fun ω => by
    by_cases hx0 : X ω = 0
    · simp only [hx0, norm_zero, Y, inner_zero_right, ciSup_const, mul_zero, le_refl]
    · have hx_pos : 0 < ‖X ω‖ := norm_pos_iff.mpr hx0
      -- u* = ‖X ω‖⁻¹ • X ω is a unit vector in closedBall 0 1
      let u_star := ‖X ω‖⁻¹ • X ω
      have hu_star_norm : ‖u_star‖ = 1 := norm_smul_inv_norm hx0
      have hu_star_ball : u_star ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        simp only [mem_closedBall, dist_zero_right, hu_star_norm, le_refl]
      -- Get net point v with dist u_star v ≤ 1/2
      obtain ⟨v, hv_F, hv_dist⟩ := net.hF_cover u_star hu_star_ball
      -- Find index j₀ with e j₀ = v
      have hv_in_F : v ∈ F := hv_F
      let j₀ : Fin k := F.equivFin ⟨v, hv_in_F⟩
      have he_j₀ : e j₀ = v := by
        change (F.equivFin.symm (F.equivFin ⟨v, hv_in_F⟩) : F).val = v
        rw [Equiv.symm_apply_apply]
      -- inner ℝ u_star (X ω) = ‖X ω‖
      have h_inner_ustar : inner ℝ u_star (X ω) = ‖X ω‖ := by
        simp only [u_star, real_inner_smul_left, real_inner_self_eq_norm_sq, sq]
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx_pos), one_mul]
      -- Cauchy-Schwarz: ⟨v - u_star, X ω⟩ ≥ -(1/2)‖X ω‖
      have hvu : ‖v - u_star‖ ≤ 1 / 2 := by
        rw [← dist_eq_norm, dist_comm]; exact hv_dist
      have h_diff_inner : -(1 / 2) * ‖X ω‖ ≤ inner ℝ (v - u_star) (X ω) := by
        linarith [neg_abs_le (inner ℝ (v - u_star) (X ω)),
                  (abs_real_inner_le_norm (v - u_star) (X ω)).trans
                    (mul_le_mul_of_nonneg_right hvu (norm_nonneg _))]
      -- ⟨v, X ω⟩ ≥ ‖X ω‖ / 2
      have h_inner_v : ‖X ω‖ / 2 ≤ inner ℝ v (X ω) := by
        have h_split : inner ℝ v (X ω) =
            inner ℝ u_star (X ω) + inner ℝ (v - u_star) (X ω) := by
          rw [inner_sub_left]; ring
        rw [h_split, h_inner_ustar]; linarith
      -- Conclude via iSup ≥ Y j₀ ω ≥ ‖X ω‖ / 2
      have hbdd : BddAbove (Set.range (fun j => Y j ω)) := Finite.bddAbove_range _
      have hY_j₀ : Y j₀ ω = inner ℝ v (X ω) := by simp [Y, he_j₀]
      linarith [le_ciSup hbdd j₀, hY_j₀ ▸ h_inner_v]
  -- *** Step 5: Integrability of ⨆ j, Y j ***
  have hint_supr : Integrable (fun ω => ⨆ j, Y j ω) μ :=
    integrable_iSup_fin hY_int
  -- *** Step 6: Expectation bound via expectation_max_le ***
  have hE_max : ∫ ω, ⨆ j, Y j ω ∂μ ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log k) :=
    expectation_max_le hcenter_Y hY_sg
  have hE_norm_le : ∫ ω, ‖X ω‖ ∂μ ≤ 2 * ∫ ω, ⨆ j, Y j ω ∂μ := by
    have h := integral_mono hX_int.norm (hint_supr.const_mul 2) (fun ω => hdiscr ω)
    rwa [integral_const_mul] at h
  -- *** Step 7: k ≤ 5^d and log k ≤ 2d ***
  have hk_le : k ≤ 5 ^ d := net.hF_card_le
  have hlog_k : Real.log k ≤ 2 * (d : ℝ) := by
    calc Real.log (k : ℝ)
        ≤ Real.log ((5 : ℕ) ^ d : ℝ) := by
              apply Real.log_le_log (by exact_mod_cast hk_pos)
              exact_mod_cast hk_le
      _ = (d : ℝ) * Real.log 5 := by push_cast; rw [Real.log_pow]
      _ ≤ (d : ℝ) * 2 := mul_le_mul_of_nonneg_left log_five_le_two (Nat.cast_nonneg d)
      _ = 2 * d := by ring
  -- *** Step 8: √(2 log k) ≤ 2√d ***
  have hsqrt_bound : Real.sqrt (2 * Real.log k) ≤ 2 * Real.sqrt (d : ℝ) := by
    have h4d : 2 * Real.log k ≤ 4 * (d : ℝ) := by linarith
    rw [show (2 : ℝ) * Real.sqrt (d : ℝ) = Real.sqrt (4 * (d : ℝ)) from by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          show Real.sqrt 4 = 2 from by
            rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]; exact Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h4d
  -- *** Step 9: Conclude ***
  calc ∫ ω, ‖X ω‖ ∂μ
      ≤ 2 * ∫ ω, ⨆ j, Y j ω ∂μ := hE_norm_le
    _ ≤ 2 * (Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log k)) :=
          mul_le_mul_of_nonneg_left hE_max (by norm_num)
    _ ≤ 2 * (Real.sqrt (σ2 : ℝ) * (2 * Real.sqrt (d : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hsqrt_bound (Real.sqrt_nonneg _)
    _ = 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) := by ring

/-!
### Tail bound — numerical algebra lemma

The tail bound requires showing `k · exp(-(t/2)²/(2σ²)) ≤ δ` for
`t = 4σ√d + 2σ√(2 log(1/δ))` and `k ≤ 5^d`.  The proof proceeds by:
- `5^d ≤ exp(2d)` (from `log 5 ≤ 2`)
- `(t/2)² / (2σ²) = (A+B)²/2 ≥ 2d + log(1/δ)` where A=2√d, B=√(2log(1/δ)), cross≥0
- So `5^d · exp(-(t/2)²/(2σ²)) ≤ exp(2d) · exp(-2d) · δ = δ`
The `σ² = 0` corner case is handled in `l2_max_tail` directly.
-/

/-- Numerical core of `l2_max_tail` for `σ² > 0`: the exponential product is ≤ δ. -/
private lemma l2_tail_numerical
    {d : ℕ} [NeZero d] {σ2 : ℝ≥0} {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    -- LEAN-ONLY: σ² > 0 required for (t/2)²/(2σ²) algebra; σ²=0 handled in l2_max_tail
    (hσ : 0 < (σ2 : ℝ))
    (hk_pos : 0 < k) (hk_le : k ≤ 5 ^ d)
    (t : ℝ) (ht : t = 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) +
                       2 * Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (1 / δ))) :
    (k : ℝ) * Real.exp (-(t / 2) ^ 2 / (2 * (σ2 : ℝ))) ≤ δ := by
  -- Let s = √σ², A = 2√d, B = √(2·log(1/δ)), so t/2 = s·(A+B)
  set s := Real.sqrt (σ2 : ℝ) with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hσ
  have hs_sq : s ^ 2 = (σ2 : ℝ) := Real.sq_sqrt hσ.le
  set A := 2 * Real.sqrt (d : ℝ) with hA_def
  set B := Real.sqrt (2 * Real.log (1 / δ)) with hB_def
  have hA_nn : 0 ≤ A := by positivity
  have hB_nn : 0 ≤ B := Real.sqrt_nonneg _
  -- Step 1: -(t/2)²/(2σ²) = -((A+B)²/2)
  have ht2 : t / 2 = s * (A + B) := by rw [ht, hA_def, hB_def, hs_def]; ring
  have h_arg : (t / 2) ^ 2 / (2 * (σ2 : ℝ)) = (A + B) ^ 2 / 2 := by
    rw [ht2, mul_pow, hs_sq]
    field_simp [hσ.ne']
  -- The goal has -(t/2)²/(2σ²); use neg_div to expose (t/2)²/(2σ²) for h_arg
  rw [show -(t / 2) ^ 2 / (2 * (σ2 : ℝ)) = -((A + B) ^ 2 / 2) from by rw [neg_div, h_arg]]
  -- Step 2: B²/2 ≥ log(1/δ)  (holds trivially when log(1/δ) < 0 since B = 0)
  have hB2 : B ^ 2 / 2 ≥ Real.log (1 / δ) := by
    simp only [hB_def]
    by_cases hlog : 0 ≤ Real.log (1 / δ)
    · have hBsq : Real.sqrt (2 * Real.log (1 / δ)) ^ 2 = 2 * Real.log (1 / δ) :=
        Real.sq_sqrt (by linarith)
      linarith
    · push Not at hlog
      have hB0 : Real.sqrt (2 * Real.log (1 / δ)) = 0 :=
        Real.sqrt_eq_zero'.mpr (by linarith)
      have hzero : Real.sqrt (2 * Real.log (1 / δ)) ^ 2 / 2 = 0 := by
        rw [hB0]; norm_num
      linarith
  -- Step 3: (A+B)²/2 ≥ 2d + log(1/δ)  (A²/2 = 2d, cross term A·B ≥ 0)
  have h_sum_ge : (A + B) ^ 2 / 2 ≥ 2 * (d : ℝ) + Real.log (1 / δ) := by
    have hAB_expand : (A + B) ^ 2 / 2 = A ^ 2 / 2 + A * B + B ^ 2 / 2 := by ring
    rw [hAB_expand]
    have hA2 : A ^ 2 / 2 = 2 * (d : ℝ) := by
      have : A ^ 2 = 4 * (d : ℝ) := by
        simp only [hA_def, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
        norm_num
      linarith
    linarith [mul_nonneg hA_nn hB_nn, hB2]
  -- Step 4: exp(-((A+B)²/2)) ≤ exp(-2d) · δ
  have h_exp_le : Real.exp (-((A + B) ^ 2 / 2)) ≤ Real.exp (-(2 * (d : ℝ))) * δ := by
    rw [show Real.exp (-(2 * (d : ℝ))) * δ = Real.exp (-(2 * (d : ℝ)) + Real.log δ) from by
      rw [Real.exp_add, Real.exp_log hδ]]
    apply Real.exp_le_exp.mpr
    have h_log1d : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    linarith [h_sum_ge]
  -- Step 5: k ≤ 5^d ≤ exp(2d)  (since log 5 ≤ 2 → 5 ≤ exp 2 → 5^d ≤ exp(2d))
  have h_k_exp : (k : ℝ) ≤ Real.exp (2 * (d : ℝ)) := by
    have h5 : (5 : ℝ) ≤ Real.exp 2 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 5)]
      exact Real.exp_le_exp.mpr log_five_le_two
    have h5d : (5 : ℝ) ^ d ≤ Real.exp (2 * (d : ℝ)) :=
      calc (5 : ℝ) ^ d
          ≤ (Real.exp 2) ^ d := by gcongr
        _ = Real.exp (2 * (d : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.exp_mul]
    calc (k : ℝ) ≤ ((5 ^ d : ℕ) : ℝ) := by exact_mod_cast hk_le
      _ = (5 : ℝ) ^ d := by push_cast; norm_num
      _ ≤ Real.exp (2 * (d : ℝ)) := h5d
  -- Step 6: Combine: k · exp(-((A+B)²/2)) ≤ exp(2d) · exp(-2d) · δ = δ
  calc (k : ℝ) * Real.exp (-((A + B) ^ 2 / 2))
      ≤ Real.exp (2 * (d : ℝ)) * (Real.exp (-(2 * (d : ℝ))) * δ) :=
          mul_le_mul h_k_exp h_exp_le (Real.exp_pos _).le (Real.exp_pos _).le
    _ = δ := by
          calc Real.exp (2 * (d : ℝ)) * (Real.exp (-(2 * (d : ℝ))) * δ)
              = Real.exp (2 * (d : ℝ)) * Real.exp (-(2 * (d : ℝ))) * δ := by ring
            _ = Real.exp (2 * (d : ℝ) + -(2 * (d : ℝ))) * δ := by rw [← Real.exp_add]
            _ = δ := by simp

/-- **ℓ²-Norm Maximal Inequality — high-probability tail bound** (Lu-BDA §6.2, Theorem 6.3).

For a centered sub-Gaussian random vector `X : Ω → EuclideanSpace ℝ (Fin d)` with
variance proxy `σ²‖u‖₊²` for every direction `u`, and any `δ > 0`:
```
μ {ω | 4σ√d + 2σ√(2 log(1/δ)) < ‖X ω‖} ≤ ENNReal.ofReal δ
```

Proof: `{‖X‖ > t} ⊆ {max_j ⟨e_j, X⟩ > t/2}` by discretization; apply `tail_max_le`
with net size `k ≤ 5^d` and the numerical estimate `l2_tail_numerical`.

Deviation from book: constant uses `log 5 ≤ 2`. -/
theorem l2_max_tail
    {d : ℕ} [NeZero d]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {σ2 : ℝ≥0}
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: E[X] = 0; Lu-BDA §6.2 Theorem 6.3
    (hcenter : ∫ ω, X ω ∂μ = 0)
    -- USER-INPUT: ⟨u, X⟩ sub-Gaussian with proxy σ²‖u‖₊²; Lu-BDA §6.2 Theorem 6.3
    (hX : ∀ u : EuclideanSpace ℝ (Fin d),
        IsSubGaussian (fun ω => inner ℝ u (X ω)) (σ2 * ‖u‖₊ ^ 2) μ)
    -- LEAN-ONLY: Bochner integrability; implied by sub-Gaussianity in finite dimension
    (hX_int : Integrable X μ)
    -- USER-INPUT: δ > 0; Lu-BDA §6.2 Theorem 6.3
    {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) +
           2 * Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (1 / δ)) < ‖X ω‖}
      ≤ ENNReal.ofReal δ := by
  haveI : DecidableEq (EuclideanSpace ℝ (Fin d)) := Classical.decEq _
  -- *** Step 1: Build net ***
  let net := buildL2Net d
  let F := net.F
  let k := F.card
  have hk_pos : 0 < k := Finset.card_pos.mpr net.hF_nonempty
  haveI hk_ne : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk_pos⟩
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk_pos
  let e : Fin k → EuclideanSpace ℝ (Fin d) := fun j => (F.equivFin.symm j : F).val
  have he_norm : ∀ j, ‖e j‖ ≤ 1 := fun j =>
    net.hF_norm (e j) (F.equivFin.symm j).prop
  -- *** Step 2: Y j ω = ⟨e j, X ω⟩ ***
  let Y : Fin k → Ω → ℝ := fun j ω => inner ℝ (e j) (X ω)
  have hcenter_Y : ∀ j, ∫ ω, Y j ω ∂μ = 0 := fun j => by
    simp only [Y, ← innerSL_apply_apply]
    rw [(innerSL ℝ (e j)).integral_comp_comm hX_int, hcenter, map_zero]
  have hY_sg : ∀ j, IsSubGaussian (Y j) σ2 μ := fun j =>
    isSubGaussian_inner_of_norm_le hX (he_norm j)
  -- *** Step 3: Discretization ‖X ω‖ ≤ 2 * ⨆ j, Y j ω ***
  have hdiscr : ∀ ω, ‖X ω‖ ≤ 2 * ⨆ j, Y j ω := fun ω => by
    by_cases hx0 : X ω = 0
    · simp only [hx0, norm_zero, Y, inner_zero_right, ciSup_const, mul_zero, le_refl]
    · have hx_pos : 0 < ‖X ω‖ := norm_pos_iff.mpr hx0
      let u_star := ‖X ω‖⁻¹ • X ω
      have hu_star_norm : ‖u_star‖ = 1 := norm_smul_inv_norm hx0
      obtain ⟨v, hv_F, hv_dist⟩ := net.hF_cover u_star
        (by simp only [mem_closedBall, dist_zero_right, hu_star_norm, le_refl])
      let j₀ : Fin k := F.equivFin ⟨v, hv_F⟩
      have he_j₀ : e j₀ = v := by
        change (F.equivFin.symm (F.equivFin ⟨v, hv_F⟩) : F).val = v
        rw [Equiv.symm_apply_apply]
      have h_inner_ustar : inner ℝ u_star (X ω) = ‖X ω‖ := by
        simp only [u_star, real_inner_smul_left, real_inner_self_eq_norm_sq, sq]
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx_pos), one_mul]
      have hvu : ‖v - u_star‖ ≤ 1 / 2 := by rw [← dist_eq_norm, dist_comm]; exact hv_dist
      have h_diff_inner : -(1 / 2) * ‖X ω‖ ≤ inner ℝ (v - u_star) (X ω) := by
        linarith [neg_abs_le (inner ℝ (v - u_star) (X ω)),
                  (abs_real_inner_le_norm (v - u_star) (X ω)).trans
                    (mul_le_mul_of_nonneg_right hvu (norm_nonneg _))]
      have h_inner_v : ‖X ω‖ / 2 ≤ inner ℝ v (X ω) := by
        have h_split : inner ℝ v (X ω) =
            inner ℝ u_star (X ω) + inner ℝ (v - u_star) (X ω) := by
          rw [inner_sub_left]; ring
        rw [h_split, h_inner_ustar]; linarith
      have hbdd : BddAbove (Set.range (fun j => Y j ω)) := Finite.bddAbove_range _
      linarith [le_ciSup hbdd j₀, show Y j₀ ω = inner ℝ v (X ω) from by simp [Y, he_j₀],
                h_inner_v]
  -- *** Step 4: Split on σ² = 0 vs σ² > 0 ***
  by_cases hσ0 : σ2 = 0
  · -- σ² = 0: threshold t = 0, Y j = 0 a.e., so X = 0 a.e. and event has measure 0
    have hσ_zero : (σ2 : ℝ) = 0 := NNReal.coe_eq_zero.mpr hσ0
    -- Simplify the threshold to 0
    have ht0 : 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) +
               2 * Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (1 / δ)) = 0 := by
      rw [hσ_zero, Real.sqrt_zero]; ring
    -- Get HasSubgaussianMGF (Y j) 0 μ from IsSubGaussian (Y j) 0 μ + centeredness
    have hsg_zero : ∀ j : Fin k, HasSubgaussianMGF (Y j) 0 μ := fun j => by
      have h := isSubGaussian_iff.mp (hσ0 ▸ hY_sg j)
      simp only [hcenter_Y j, sub_zero] at h
      exact h
    -- Y j = 0 a.e. for each j
    have hY0 : ∀ j : Fin k, Y j =ᵐ[μ] 0 := fun j =>
      HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zero (hsg_zero j)
    -- ⨆ j, Y j ω = 0 a.e.
    have hsupr0 : ∀ᵐ ω ∂μ, ⨆ j : Fin k, Y j ω = 0 := by
      have hall : ∀ᵐ ω ∂μ, ∀ j : Fin k, Y j ω = 0 := ae_all_iff.mpr hY0
      filter_upwards [hall] with ω hω
      simp_rw [hω]; exact ciSup_const
    -- μ {threshold < ‖X‖} ≤ μ {0 < ‖X‖} = 0 ≤ ENNReal.ofReal δ
    -- (threshold = 0 when σ² = 0, so the two sets are equal)
    have hme : μ {ω | (0 : ℝ) < ‖X ω‖} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hsupr0)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro heq
      have h := hdiscr ω
      rw [heq, mul_zero] at h
      linarith
    calc μ {ω | 4 * Real.sqrt (↑σ2) * Real.sqrt (↑d) +
               2 * Real.sqrt (↑σ2) * Real.sqrt (2 * Real.log (1 / δ)) < ‖X ω‖}
        ≤ μ {ω | (0 : ℝ) < ‖X ω‖} := by
            apply measure_mono
            intro ω hω
            simp only [Set.mem_setOf_eq] at hω ⊢
            simp only [ht0] at hω
            exact hω
      _ = 0 := hme
      _ ≤ ENNReal.ofReal δ := zero_le
  · -- σ² > 0: use tail_max_le + l2_tail_numerical
    have hσ_pos : 0 < (σ2 : ℝ) :=
      NNReal.coe_pos.mpr (lt_of_le_of_ne (zero_le (a := σ2)) (Ne.symm hσ0))
    set t := 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) +
             2 * Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (1 / δ))
    have h_subset : {ω | t < ‖X ω‖} ⊆ {ω | t / 2 < ⨆ j, Y j ω} := by
      intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; linarith [hdiscr ω]
    calc μ {ω | t < ‖X ω‖}
        ≤ μ {ω | t / 2 < ⨆ j, Y j ω} := measure_mono h_subset
      _ ≤ ENNReal.ofReal ((k : ℝ) * Real.exp (-(t / 2) ^ 2 / (2 * ↑σ2))) :=
            tail_max_le hcenter_Y hY_sg (by positivity)
      _ ≤ ENNReal.ofReal δ :=
            ENNReal.ofReal_le_ofReal
              (l2_tail_numerical hδ hσ_pos hk_pos net.hF_card_le t rfl)

end StatLean.ConcentrationInequalities
