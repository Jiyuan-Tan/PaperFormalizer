module
public import StatLean.Minimaxity.ForMathlib.Packing.SpherePacking
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Metric entropy / packing lower bound for the Sobolev ellipsoid

A Chapter-5 metric-entropy prerequisite for the Sobolev minimax example. Fix a smoothness index
$\alpha > 1/2$ and consider the **Sobolev ellipsoid**
$$\mathcal{E}_\alpha = \Bigl\{\, \theta \in \ell^2(\mathbb{N}) : \sum_{j} j^{2\alpha}\,\theta_j^2 \le 1 \,\Bigr\}.$$
Its metric entropy — the logarithm of the smallest number of $\delta$-balls (in the $\ell^2$ norm)
needed to cover it — obeys the Kolmogorov–Tikhomirov rate
$$\log N(\delta;\, \mathcal{E}_\alpha,\, \lVert\cdot\rVert_2) \;\asymp\; \left(\tfrac{1}{\delta}\right)^{1/\alpha}.$$
The minimax lower bounds use only the **packing (lower) direction**: for every
$0 < \delta \le 1/2$ there is a constant $c > 0$ and a finite $\delta$-separated subset
$T \subset \mathcal{E}_\alpha$ (every pair of distinct points at $\ell^2$-distance $\ge \delta$,
every point in the ellipsoid) with
$$c\,\left(\tfrac{1}{\delta}\right)^{1/\alpha} \;\le\; \log |T|.$$

Two deviations from the book statement are made explicit in the Lean formalization:

* The membership constraint is written with the shifted weights $(j+1)^{2\alpha}$ over indices
  $j \in \mathbb{N}$ starting at $0$, rather than $j^{2\alpha}$ starting at $1$; this is the same
  ellipsoid under a re-indexing of coordinates.
* The restriction $0 < \delta \le 1/2$ (`hδ2`) is added. It is forced rather than cosmetic: the
  ellipsoid has $\ell^2$-diameter $\le 2$, so no $\delta$-separated pair can exist for large
  $\delta$, and the metric-entropy rate is intrinsically a $\delta \to 0$ statement.

The constant `c` is the *provable* one produced by the construction below, namely
$c = (k/10)\big/(1/\delta)^{1/\alpha}$ with $k = \lfloor (1/(2\delta))^{1/\alpha}\rfloor$, not a
named book constant.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.12
(invoked in Chapter 15, §15.3.5, Example 15.23).

**Proof formalization notes.**
The lower bound is a volume-ratio packing routed through the **Euclidean sphere packing**
(`exists_sphere_packing`, in `SpherePacking.lean`). Set `k := ⌊(1/(2δ))^{1/α}⌋` and take a
`1/2`-separated set `S` of unit vectors on `𝕊^{k-1}` with `log |S| ≥ k/10`. Scale by
`ρ := k^{-α}` and embed each `v ∈ ℝ^k` into the first `k` coords of `ℓ²(ℕ)`:
```
emb v := (j ↦ if j < k then ρ · vⱼ else 0).
```
This embedding is linear, scales norms by `ρ` (`‖emb v‖ = ρ‖v‖`), lands inside the ellipsoid
(`Σⱼ (j+1)^{2α} (emb v)ⱼ² ≤ ρ² k^{2α} ‖v‖² = 1`, using `(j+1)^{2α} ≤ k^{2α}` and
`ρ² k^{2α} = 1`), and keeps the points `δ`-separated (`‖emb u − emb v‖ = ρ‖u−v‖ ≥ ρ/2 ≥ δ`,
because `k^α ≤ 1/(2δ)`). The image `T = emb(S)` then has `log |T| = log |S| ≥ k/10 ≍ (1/δ)^{1/α}`.

**Bibliographic comments.**
The $\varepsilon$-entropy of smoothness (Sobolev/Lipschitz) classes, and in particular the
$\varepsilon^{-1/\alpha}$ rate specialized here to the ellipsoid $\mathcal{E}_\alpha$, originates
with A. N. Kolmogorov and V. M. Tikhomirov, "ε-entropy and ε-capacity of sets in function spaces"
(in Russian), *Uspekhi Matematicheskikh Nauk* **14** (1959), no. 2(86), 3–86; English translation
in *American Mathematical Society Translations*, Series 2, Vol. 17 (1961), 277–364. That paper
introduced the now-standard definitions of metric entropy ($\varepsilon$-entropy) and capacity and
computed them for the principal function classes. Wainwright's Example 5.12 is the textbook
specialization to the Sobolev ellipsoid; the precise constants here are those provable by the
sphere-packing construction above and are not asserted to match any constant in the original paper.
-/

open scoped ENNReal
open Finset

namespace StatLean.Minimaxity

/-- The `j`-th coordinate of the scaled embedding of `w ∈ ℝ^k` into `ℓ²(ℕ)`: `ρ · wⱼ` for the first
`k` coordinates (`j < k`), and `0` beyond. The degenerate fallback `0` for `j ≥ k` makes the
sequence finitely supported, hence a genuine `ℓ²` element. -/
private def sobolevCoeff (k : ℕ) (ρ : ℝ) (w : EuclideanSpace ℝ (Fin k)) (j : ℕ) : ℝ :=
  if h : j < k then ρ * w ⟨j, h⟩ else 0

/-- The scaled finite-support embedding `ℝ^k ↪ ℓ²(ℕ)` of Wainwright Example 5.12, realised as a
finite sum of `lp.single`'s so its `ℓ²`-norm is computable via `lp.norm_sum_single`. -/
private noncomputable def sobolevEmb (k : ℕ) (ρ : ℝ) (w : EuclideanSpace ℝ (Fin k)) :
    lp (fun _ : ℕ => ℝ) 2 :=
  ∑ j ∈ Finset.range k, lp.single 2 j (sobolevCoeff k ρ w j)

/-- For an in-range index `i : Fin k`, the embedding coefficient is just `ρ · wᵢ`. -/
private lemma sobolevCoeff_val (k : ℕ) (ρ : ℝ) (w : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    sobolevCoeff k ρ w i.val = ρ * w i := by
  simp only [sobolevCoeff]
  rw [dif_pos i.isLt]

/-- The coercion of `sobolevEmb` to a sequence is exactly `sobolevCoeff`. -/
private lemma coeFn_sobolevEmb (k : ℕ) (ρ : ℝ) (w : EuclideanSpace ℝ (Fin k)) :
    ⇑(sobolevEmb k ρ w) = sobolevCoeff k ρ w := by
  funext j
  simp only [sobolevEmb, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  split_ifs with hj
  · rfl
  · have hjk : ¬ (j < k) := by rwa [Finset.mem_range] at hj
    simp only [sobolevCoeff, dif_neg hjk]

/-- The embedding is linear in `w` (here: respects subtraction). -/
private lemma sobolevEmb_sub (k : ℕ) (ρ : ℝ) (u v : EuclideanSpace ℝ (Fin k)) :
    sobolevEmb k ρ u - sobolevEmb k ρ v = sobolevEmb k ρ (u - v) := by
  apply lp.ext
  rw [lp.coeFn_sub, coeFn_sobolevEmb, coeFn_sobolevEmb, coeFn_sobolevEmb]
  funext j
  simp only [Pi.sub_apply, sobolevCoeff]
  split_ifs with h
  · rw [PiLp.sub_apply]; ring
  · ring

/-- Squared Euclidean norm as a sum of squared coordinates. -/
private lemma sq_norm_eucl (k : ℕ) (w : EuclideanSpace ℝ (Fin k)) :
    ‖w‖ ^ 2 = ∑ i : Fin k, (w i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.norm_eq_abs, sq_abs]

/-- The sum of squared embedding coefficients over the first `k` coordinates is `ρ² ‖w‖²`. -/
private lemma sum_sq_sobolevCoeff (k : ℕ) (ρ : ℝ) (w : EuclideanSpace ℝ (Fin k)) :
    ∑ j ∈ Finset.range k, (sobolevCoeff k ρ w j) ^ 2 = ρ ^ 2 * ‖w‖ ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => (sobolevCoeff k ρ w j) ^ 2) k]
  have hcoe : ∀ i : Fin k, (sobolevCoeff k ρ w i.val) ^ 2 = ρ ^ 2 * (w i) ^ 2 := by
    intro i
    rw [sobolevCoeff_val, mul_pow]
  rw [Finset.sum_congr rfl (fun i _ => hcoe i), ← Finset.mul_sum, sq_norm_eucl]

/-- **Norm scaling.** `‖emb w‖ = ρ‖w‖` (for `ρ ≥ 0`). -/
private lemma norm_sobolevEmb (k : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (w : EuclideanSpace ℝ (Fin k)) :
    ‖sobolevEmb k ρ w‖ = ρ * ‖w‖ := by
  have hP : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hnorm := lp.norm_sum_single hP (sobolevCoeff k ρ w) (Finset.range k)
  simp only [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hnorm
  rw [show (∑ j ∈ Finset.range k, lp.single 2 j (sobolevCoeff k ρ w j)) = sobolevEmb k ρ w from rfl]
    at hnorm
  have hsum : ∑ j ∈ Finset.range k, ‖sobolevCoeff k ρ w j‖ ^ 2 = ρ ^ 2 * ‖w‖ ^ 2 := by
    rw [← sum_sq_sobolevCoeff k ρ w]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [hsum] at hnorm
  have h1 : ‖sobolevEmb k ρ w‖ = Real.sqrt (ρ ^ 2 * ‖w‖ ^ 2) := by
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, ← mul_pow, Real.sqrt_sq (mul_nonneg hρ (norm_nonneg _))]

/-- **Ellipsoid membership.** A unit vector `w` lands inside the Sobolev ellipsoid under `emb`
(when `ρ = k^{-α}`, `k ≥ 1`, `α ≥ 0`). -/
private lemma sobolevEmb_mem (k : ℕ) (hk : 0 < k) (ρ α : ℝ) (hα0 : 0 ≤ α)
    (hρ : ρ = (k : ℝ) ^ (-α)) (w : EuclideanSpace ℝ (Fin k)) (hw : ‖w‖ = 1) :
    ∑' j : ℕ, ((j : ℝ) + 1) ^ (2 * α) * ((sobolevEmb k ρ w) j) ^ 2 ≤ 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h2α : (0 : ℝ) ≤ 2 * α := by linarith
  simp only [coeFn_sobolevEmb]
  have hzero : ∀ j ∉ Finset.range k,
      ((j : ℝ) + 1) ^ (2 * α) * (sobolevCoeff k ρ w j) ^ 2 = 0 := by
    intro j hj
    rw [Finset.mem_range, not_lt] at hj
    have : sobolevCoeff k ρ w j = 0 := by
      simp only [sobolevCoeff]; rw [dif_neg (Nat.not_lt.mpr hj)]
    rw [this]; ring
  rw [tsum_eq_sum hzero]
  have hbound : ∑ j ∈ Finset.range k, ((j : ℝ) + 1) ^ (2 * α) * (sobolevCoeff k ρ w j) ^ 2
      ≤ ∑ j ∈ Finset.range k, (k : ℝ) ^ (2 * α) * (sobolevCoeff k ρ w j) ^ 2 := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjk : (j : ℝ) + 1 ≤ (k : ℝ) := by
      rw [Finset.mem_range] at hj
      have : j + 1 ≤ k := hj
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) hjk h2α) (sq_nonneg _)
  refine hbound.trans ?_
  rw [← Finset.mul_sum, sum_sq_sobolevCoeff, hw, one_pow, mul_one, hρ]
  have : (k : ℝ) ^ (2 * α) * ((k : ℝ) ^ (-α)) ^ 2 = 1 := by
    rw [sq, ← mul_assoc, ← Real.rpow_add hkpos, ← Real.rpow_add hkpos,
      show 2 * α + -α + -α = 0 by ring, Real.rpow_zero]
  rw [this]

-- LEAN-ONLY: δ ≤ 1/2 (small-scale regime; the ellipsoid has ℓ²-diameter ≤ 2 so no δ-separated pair
-- exists for large δ); the metric-entropy rate is a δ→0 statement (Wainwright Ex 5.12).
/-- **Residual Kolmogorov–Tikhomirov construction** for the Sobolev packing bound, via the Euclidean
sphere packing. Restricting the ellipsoid to its first `k ≍ (1/δ)^{1/α}` coordinates and scaling a
`1/2`-separated unit-sphere packing by `ρ = k^{-α}` produces an `exp(k/10)`-cardinality
`δ`-separated subset of the ellipsoid. -/
private lemma sobolev_packing_lower_bound_aux (α : ℝ) (hα : 1 / 2 < α) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ∃ (c : ℝ) (_ : 0 < c) (T : Finset (lp (fun _ : ℕ => ℝ) 2)),
      c * (1 / δ) ^ (1 / α) ≤ Real.log T.card ∧
      (∀ x ∈ T, ∑' j : ℕ, ((j : ℝ) + 1) ^ (2 * α) * (x j) ^ 2 ≤ 1) ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ ‖x - y‖ := by
  classical
  have hαpos : (0 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) ≤ α := hαpos.le
  have h2δpos : (0 : ℝ) < 2 * δ := by linarith
  -- The dimension `k = ⌊(1/(2δ))^{1/α}⌋`.
  set k : ℕ := ⌊(1 / (2 * δ)) ^ (1 / α)⌋₊ with hk_def
  have h1le : (1 : ℝ) ≤ 1 / (2 * δ) := by
    rw [le_div_iff₀ h2δpos, one_mul]; linarith
  have hk : 0 < k := by
    rw [hk_def, Nat.floor_pos]
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / α) := (Real.one_rpow _).symm
      _ ≤ (1 / (2 * δ)) ^ (1 / α) := Real.rpow_le_rpow zero_le_one h1le (by positivity)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkle : (k : ℝ) ≤ (1 / (2 * δ)) ^ (1 / α) := by
    rw [hk_def]; exact Nat.floor_le (by positivity)
  -- The scale `ρ = k^{-α}` and the key bound `k^α ≤ 1/(2δ)`.
  set ρ : ℝ := (k : ℝ) ^ (-α) with hρ_def
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hkpos _
  have hApos : 0 < (k : ℝ) ^ α := Real.rpow_pos_of_pos hkpos α
  have hkα : (k : ℝ) ^ α ≤ 1 / (2 * δ) := by
    calc (k : ℝ) ^ α ≤ ((1 / (2 * δ)) ^ (1 / α)) ^ α :=
          Real.rpow_le_rpow hkpos.le hkle hα0
      _ = (1 / (2 * δ)) ^ ((1 / α) * α) := (Real.rpow_mul (by positivity) _ _).symm
      _ = (1 / (2 * δ)) ^ (1 : ℝ) := by rw [one_div_mul_cancel (ne_of_gt hαpos)]
      _ = 1 / (2 * δ) := Real.rpow_one _
  have hρ2δ : 2 * δ ≤ ρ := by
    rw [hρ_def, Real.rpow_neg hkpos.le, ← one_div, le_div_iff₀ hApos]
    rw [le_div_iff₀ h2δpos] at hkα
    rw [mul_comm]; exact hkα
  -- The Euclidean sphere packing of dimension `k`.
  obtain ⟨S, hSlog, _hSnorm, hSsep⟩ := exists_sphere_packing k
  -- The image packing in `ℓ²(ℕ)`.
  have hemb_inj : Function.Injective (sobolevEmb k ρ) := by
    intro u v huv
    have h0 : ρ * ‖u - v‖ = 0 := by
      rw [← norm_sobolevEmb k ρ hρ0.le (u - v), ← sobolevEmb_sub, huv, sub_self, norm_zero]
    have : ‖u - v‖ = 0 := (mul_eq_zero.mp h0).resolve_left (ne_of_gt hρ0)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  set T : Finset (lp (fun _ : ℕ => ℝ) 2) := S.image (sobolevEmb k ρ) with hT_def
  -- The cardinality constant.
  have hden : (0 : ℝ) < (1 / δ) ^ (1 / α) := Real.rpow_pos_of_pos (one_div_pos.mpr hδ) _
  set c : ℝ := ((k : ℝ) / 10) / ((1 / δ) ^ (1 / α)) with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; exact div_pos (by linarith) hden
  refine ⟨c, hc_pos, T, ?_, ?_, ?_⟩
  · -- Cardinality bound.
    have hcard : Real.log (T.card) = Real.log (S.card) := by
      rw [hT_def, Finset.card_image_of_injective S hemb_inj]
    have hc_eq : c * (1 / δ) ^ (1 / α) = (k : ℝ) / 10 := by
      rw [hc_def, div_mul_cancel₀ _ (ne_of_gt hden)]
    rw [hc_eq, hcard]
    exact hSlog
  · -- Every image vector lies in the ellipsoid.
    intro x hx
    obtain ⟨v, _hvS, rfl⟩ := Finset.mem_image.mp hx
    exact sobolevEmb_mem k hk ρ α hα0 hρ_def v (_hSnorm v _hvS)
  · -- The images are `δ`-separated.
    intro x hx y hy hxy
    obtain ⟨u, huS, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hvS, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun h => hxy (by rw [h])
    rw [sobolevEmb_sub, norm_sobolevEmb k ρ hρ0.le]
    have hsep : (1 / 2 : ℝ) ≤ ‖u - v‖ := hSsep u huS v hvS huv
    calc δ ≤ ρ * (1 / 2) := by rw [mul_one_div]; linarith
      _ ≤ ρ * ‖u - v‖ := mul_le_mul_of_nonneg_left hsep hρ0.le

/-- **Packing lower bound for the Sobolev ellipsoid** (Wainwright Example 5.12): for `α > 1/2` and
`0 < δ ≤ 1/2`, the ellipsoid `ℰ_α ⊂ ℓ²(ℕ)` contains a `δ`-separated set `T` with
`log |T| ≳ (1/δ)^{1/α}`.

The small-scale restriction `δ ≤ 1/2` is forced: the ellipsoid has `ℓ²`-diameter `≤ 2`, so no
`δ`-separated pair exists for large `δ`; the metric-entropy rate is a `δ → 0` statement.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.12. -/
theorem sobolev_packing_lower_bound (α : ℝ) (hα : 1 / 2 < α) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ∃ (c : ℝ) (_ : 0 < c) (T : Finset (lp (fun _ : ℕ => ℝ) 2)),
      c * (1 / δ) ^ (1 / α) ≤ Real.log T.card ∧
      (∀ x ∈ T, ∑' j : ℕ, ((j : ℝ) + 1) ^ (2 * α) * (x j) ^ 2 ≤ 1) ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ ‖x - y‖ :=
  sobolev_packing_lower_bound_aux α hα δ hδ hδ2

end StatLean.Minimaxity
