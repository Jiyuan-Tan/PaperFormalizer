module
public import StatLean.NonparametricStatistics.Projection.CoefficientRisk
public import StatLean.NonparametricStatistics.Projection.TrigOrthogonality
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

/-!
# Exact MISE decomposition of the projection estimator

At the regular design with independent centered noise of common second moment `σ_ξ²`, for the
target `f = seriesFun θ` and any order `1 ≤ N ≤ n − 1`:
$$ \mathbb E\,\|\hat f_{nN} - f\|_{L^2[0,1]}^2
   \;=\; \frac{\sigma_\xi^2 N}{n} \;+\; \sum_{j=1}^N \alpha_j^2 \;+\; \rho_N,
   \qquad \rho_N = \sum_{j>N}\theta_j^2 $$
— an exact identity: stochastic error `σ_ξ²N/n`, Riemann-sum (aliasing) error `∑αⱼ²`, and
approximation (tail) error `ρ_N`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7.2, Proposition 1.17 (exact MISE
decomposition of the projection estimator).

**Proof formalization notes.** Expand `f̂ − f = ∑_{j≤N}(θ̂ⱼ − θⱼ)φⱼ − ∑_{j>N}θⱼφⱼ`. The `L²`
cross terms vanish and the squares decouple by orthonormality (`trigBasis_orthonormal`); the
tail's squared norm is `ρ_N` by dominated convergence (uniform convergence of the tail series
under `∑|θ| < ∞`, envelope `(√2·∑|θ|)²` on the finite interval) plus orthonormality — no
completeness of the trigonometric system is invoked, since `f` is *defined* by its series.
Then take expectations termwise (`coeffEstimator_sq_error` for `j ≤ N`; independence kills
the `j ≠ k` covariance terms via the mean formula). Everything is stated in `∫⁻` form.

**Bibliographic comments.** The exact decomposition is the standard starting point of
orthogonal-series risk analysis: N. N. Čencov, *Soviet Math. Dokl.* **3** (1962), 1559–1562;
J. Rice, *Ann. Statist.* **12** (1984), 1215–1230.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- The trigonometric basis functions are continuous. -/
private lemma continuous_trigBasis (j : ℕ) : Continuous (trigBasis j) := by
  unfold trigBasis
  split_ifs <;> fun_prop

/-- Absolute summability of the coefficients makes `j ↦ θ j · φⱼ(x)` summable. -/
private lemma summable_trigTerm {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) (x : ℝ) :
    Summable fun j => θ j * trigBasis j x := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (hθ1.mul_left (Real.sqrt 2))
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (trigBasis_abs_le j x) (abs_nonneg _)

/-- `seriesFun` is continuous under absolute summability. -/
private lemma continuous_seriesFun {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) :
    Continuous (seriesFun θ) := by
  unfold seriesFun
  refine continuous_tsum (fun j => continuous_const.mul (continuous_trigBasis j))
    (hθ1.mul_left (Real.sqrt 2)) (fun n x => ?_)
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (trigBasis_abs_le n x) (abs_nonneg _)

/-- The tail function `g(x) = ∑_{m} θ_{N+1+m}·φ_{N+1+m}(x)`, indexed to match the `range`-tail. -/
private noncomputable def gTail (θ : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑' m : ℕ, θ (m + (N + 1)) * trigBasis (m + (N + 1)) x

private lemma continuous_gTail {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) (N : ℕ) :
    Continuous (gTail θ N) := by
  unfold gTail
  refine continuous_tsum (fun m => continuous_const.mul (continuous_trigBasis _))
    (((summable_nat_add_iff (f := fun j => |θ j|) (N + 1)).mpr hθ1).mul_left (Real.sqrt 2))
    (fun m x => ?_)
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (trigBasis_abs_le _ x) (abs_nonneg _)

private lemma gTail_abs_le {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) (N : ℕ) (x : ℝ) :
    |gTail θ N x| ≤ Real.sqrt 2 * ∑' m, |θ (m + (N + 1))| := by
  unfold gTail
  have hs : Summable fun m => |θ (m + (N + 1))| :=
    (summable_nat_add_iff (f := fun j => |θ j|) (N + 1)).mpr hθ1
  have hb : ∀ m, |θ (m + (N + 1)) * trigBasis (m + (N + 1)) x|
      ≤ Real.sqrt 2 * |θ (m + (N + 1))| := fun m => by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (trigBasis_abs_le _ x) (abs_nonneg _)
  have hsp : Summable fun m => |θ (m + (N + 1)) * trigBasis (m + (N + 1)) x| :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hb (hs.mul_left _)
  calc |∑' m, θ (m + (N + 1)) * trigBasis (m + (N + 1)) x|
      ≤ ∑' m, |θ (m + (N + 1)) * trigBasis (m + (N + 1)) x| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun m => θ (m + (N + 1)) * trigBasis (m + (N + 1)) x)
          (by simpa [Real.norm_eq_abs] using hsp)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' m, Real.sqrt 2 * |θ (m + (N + 1))| := Summable.tsum_le_tsum hb hsp (hs.mul_left _)
    _ = Real.sqrt 2 * ∑' m, |θ (m + (N + 1))| := tsum_mul_left

/-- The continuous orthonormality relation, as a set integral over `[0,1]`. -/
private lemma trigBasis_orthonormal_Icc {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∫ x in Set.Icc (0:ℝ) 1, trigBasis j x * trigBasis k x = if j = k then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (zero_le_one)]
  exact trigBasis_orthonormal hj hk

/-- Split `seriesFun` into its first-`N` partial sum and the tail function `g`. -/
private lemma seriesFun_split {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) (N : ℕ) (x : ℝ) :
    seriesFun θ x = (∑ j ∈ Finset.Icc 1 N, θ j * trigBasis j x) + gTail θ N x := by
  have hsum := summable_trigTerm hθ1 x
  have hsplit := Summable.sum_add_tsum_nat_add (N + 1) hsum
  unfold seriesFun gTail
  rw [← hsplit]
  congr 1
  · have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert (by simp)]
    simp [trigBasis]

/-- Interchange integral and tail-sum against a bounded continuous test function `h`. -/
private lemma integral_gTail_mul {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) (N : ℕ)
    (h : ℝ → ℝ) (hcont : Continuous h) (C : ℝ) (hC : ∀ x, |h x| ≤ C) :
    ∫ x in Set.Icc (0:ℝ) 1, gTail θ N x * h x
      = ∑' m : ℕ, θ (m + (N + 1))
          * ∫ x in Set.Icc (0:ℝ) 1, trigBasis (m + (N + 1)) x * h x := by
  have hs : Summable fun m => |θ (m + (N + 1))| :=
    (summable_nat_add_iff (f := fun j => |θ j|) (N + 1)).mpr hθ1
  have hpt : ∀ x, gTail θ N x * h x
      = ∑' m, θ (m + (N + 1)) * (trigBasis (m + (N + 1)) x * h x) := by
    intro x; unfold gTail
    rw [← tsum_mul_right]
    exact tsum_congr fun m => by ring
  have hmeas : ∀ m, AEStronglyMeasurable
      (fun x => θ (m + (N + 1)) * (trigBasis (m + (N + 1)) x * h x))
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    fun m => (continuous_const.mul ((continuous_trigBasis _).mul hcont)).aestronglyMeasurable
  have hfin : (∑' m, ∫⁻ x in Set.Icc (0:ℝ) 1,
      ‖θ (m + (N + 1)) * (trigBasis (m + (N + 1)) x * h x)‖ₑ) ≠ ∞ := by
    have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
    have hb : ∀ m, ∫⁻ x in Set.Icc (0:ℝ) 1,
        ‖θ (m + (N + 1)) * (trigBasis (m + (N + 1)) x * h x)‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt 2 * C * |θ (m + (N + 1))|) := by
      intro m
      calc ∫⁻ x in Set.Icc (0:ℝ) 1,
            ‖θ (m + (N + 1)) * (trigBasis (m + (N + 1)) x * h x)‖ₑ
          ≤ ∫⁻ _ in Set.Icc (0:ℝ) 1,
              ENNReal.ofReal (Real.sqrt 2 * C * |θ (m + (N + 1))|) := by
            apply lintegral_mono
            intro x
            simp only [Real.enorm_eq_ofReal_abs]
            apply ENNReal.ofReal_le_ofReal
            rw [abs_mul, abs_mul]
            have h1 : |trigBasis (m + (N + 1)) x| * |h x| ≤ Real.sqrt 2 * C :=
              mul_le_mul (trigBasis_abs_le _ x) (hC x) (abs_nonneg _)
                (Real.sqrt_nonneg _)
            calc |θ (m + (N + 1))| * (|trigBasis (m + (N + 1)) x| * |h x|)
                ≤ |θ (m + (N + 1))| * (Real.sqrt 2 * C) :=
                  mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
              _ = Real.sqrt 2 * C * |θ (m + (N + 1))| := by ring
        _ = ENNReal.ofReal (Real.sqrt 2 * C * |θ (m + (N + 1))|)
              * volume (Set.Icc (0:ℝ) 1) := setLIntegral_const _ _
        _ = ENNReal.ofReal (Real.sqrt 2 * C * |θ (m + (N + 1))|) := by
            rw [Real.volume_Icc]; simp
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hb) ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) ((hs.mul_left _))]
    exact ENNReal.ofReal_lt_top
  rw [integral_congr_ae (ae_of_all _ hpt), integral_tsum hmeas hfin]
  exact tsum_congr fun m => integral_const_mul _ _

/-- Orthogonality of `φ_p` to the tail: `∫ φ_p·g = θ_p` if `p > N`, else `0`. -/
private lemma integral_trigBasis_mul_gTail {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|)
    (N p : ℕ) (hp : 1 ≤ p) :
    ∫ x in Set.Icc (0:ℝ) 1, trigBasis p x * gTail θ N x = if N + 1 ≤ p then θ p else 0 := by
  rw [integral_congr_ae (ae_of_all _ fun x => mul_comm (trigBasis p x) (gTail θ N x)),
    integral_gTail_mul hθ1 N (trigBasis p) (continuous_trigBasis p) (Real.sqrt 2)
      (fun x => trigBasis_abs_le p x)]
  have hom : ∀ m, θ (m + (N + 1)) * ∫ x in Set.Icc (0:ℝ) 1,
      trigBasis (m + (N + 1)) x * trigBasis p x
      = θ (m + (N + 1)) * (if m + (N + 1) = p then 1 else 0) := fun m => by
    rw [trigBasis_orthonormal_Icc (by omega) hp]
  rw [tsum_congr hom]
  split_ifs with hle
  · obtain ⟨m₀, hm₀⟩ := Nat.exists_eq_add_of_le hle
    rw [tsum_eq_single m₀ (fun m hm => by rw [if_neg (by omega), mul_zero])]
    rw [if_pos (by omega), mul_one]; congr 1; omega
  · rw [tsum_congr (fun m => by rw [if_neg (by omega), mul_zero]), tsum_zero]

/-- The tail's squared `L²`-norm equals the tail energy `ρ_N`. -/
private lemma integral_gTail_sq {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) (N : ℕ) :
    ∫ x in Set.Icc (0:ℝ) 1, gTail θ N x ^ 2 = tailEnergy θ N := by
  have h1 : ∫ x in Set.Icc (0:ℝ) 1, gTail θ N x ^ 2
      = ∫ x in Set.Icc (0:ℝ) 1, gTail θ N x * gTail θ N x :=
    integral_congr_ae (ae_of_all _ fun x => pow_two (gTail θ N x))
  rw [h1, integral_gTail_mul hθ1 N (gTail θ N) (continuous_gTail hθ1 N)
    (Real.sqrt 2 * ∑' m, |θ (m + (N + 1))|) (gTail_abs_le hθ1 N)]
  have h2 : (∑' m, θ (m + (N + 1)) * ∫ x in Set.Icc (0:ℝ) 1,
      trigBasis (m + (N + 1)) x * gTail θ N x) = ∑' m, θ (m + (N + 1)) * θ (m + (N + 1)) := by
    refine tsum_congr fun m => ?_
    rw [integral_trigBasis_mul_gTail hθ1 N (m + (N + 1)) (by omega), if_pos (by omega)]
  rw [h2]
  unfold tailEnergy
  exact tsum_congr fun m => by rw [← sq, add_comm m (N + 1)]

/-- The exact `L²[0,1]` expansion of the squared projection error for fixed coefficients `c`. -/
private lemma proj_L2_sq_integral {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) {N : ℕ}
    (_hN : 1 ≤ N) (c : ℕ → ℝ) :
    ∫ x in Set.Icc (0:ℝ) 1,
        ((∑ j ∈ Finset.Icc 1 N, c j * trigBasis j x) - seriesFun θ x) ^ 2
      = (∑ j ∈ Finset.Icc 1 N, (c j - θ j) ^ 2) + tailEnergy θ N := by
  have hcS : Continuous (fun x => ∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_trigBasis j))
  have hcg : Continuous (gTail θ N) := continuous_gTail hθ1 N
  have hDrw : ∀ x, (∑ j ∈ Finset.Icc 1 N, c j * trigBasis j x) - seriesFun θ x
      = (∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) - gTail θ N x := by
    intro x
    rw [seriesFun_split hθ1 N x,
      Finset.sum_congr rfl (fun j _ => (by ring :
        (c j - θ j) * trigBasis j x = c j * trigBasis j x - θ j * trigBasis j x)),
      Finset.sum_sub_distrib]
    ring
  rw [integral_congr_ae (ae_of_all _ fun x => by rw [hDrw x])]
  have hsq : ∀ x, ((∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) - gTail θ N x) ^ 2
      = (∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) ^ 2
        - 2 * ((∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) * gTail θ N x)
        + gTail θ N x ^ 2 := fun x => by ring
  rw [integral_congr_ae (ae_of_all _ hsq)]
  have iS2 : Integrable (fun x => (∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) := (hcS.pow 2).integrableOn_Icc
  have iSg : Integrable (fun x => 2 * ((∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x)
      * gTail θ N x)) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    (continuous_const.mul (hcS.mul hcg)).integrableOn_Icc
  have ig2 : Integrable (fun x => gTail θ N x ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) := (hcg.pow 2).integrableOn_Icc
  have hStwo : ∫ x in Set.Icc (0:ℝ) 1, (∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) ^ 2
      = ∑ j ∈ Finset.Icc 1 N, (c j - θ j) ^ 2 := by
    have he : ∀ x, (∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) ^ 2
        = ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          ((c j - θ j) * (c k - θ k)) * (trigBasis j x * trigBasis k x) := by
      intro x
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have hInt1 : ∀ j k, Integrable (fun x => ((c j - θ j) * (c k - θ k))
        * (trigBasis j x * trigBasis k x)) (volume.restrict (Set.Icc (0:ℝ) 1)) := fun j k =>
      (continuous_const.mul
        ((continuous_trigBasis j).mul (continuous_trigBasis k))).integrableOn_Icc
    have hInt2 : ∀ j, Integrable (fun x => ∑ k ∈ Finset.Icc 1 N,
        ((c j - θ j) * (c k - θ k)) * (trigBasis j x * trigBasis k x))
        (volume.restrict (Set.Icc (0:ℝ) 1)) :=
      fun j => integrable_finset_sum _ (fun k _ => hInt1 j k)
    rw [integral_congr_ae (ae_of_all _ he),
      integral_finset_sum (Finset.Icc 1 N) (fun j _ => hInt2 j)]
    apply Finset.sum_congr rfl; intro j hj
    rw [integral_finset_sum (Finset.Icc 1 N) (fun k _ => hInt1 j k)]
    rw [Finset.sum_congr rfl (fun k hk => by rw [integral_const_mul,
      trigBasis_orthonormal_Icc (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1])]
    rw [Finset.sum_eq_single j (fun k _ hkj => by rw [if_neg (Ne.symm hkj), mul_zero])
      (fun hjj => absurd hj hjj), if_pos rfl]
    ring
  have hSg : ∫ x in Set.Icc (0:ℝ) 1,
      (∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) * gTail θ N x = 0 := by
    have he : ∀ x, (∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) * gTail θ N x
        = ∑ j ∈ Finset.Icc 1 N, (c j - θ j) * (trigBasis j x * gTail θ N x) := by
      intro x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hIntg : ∀ j, Integrable (fun x => (c j - θ j) * (trigBasis j x * gTail θ N x))
        (volume.restrict (Set.Icc (0:ℝ) 1)) := fun j =>
      (continuous_const.mul ((continuous_trigBasis j).mul hcg)).integrableOn_Icc
    rw [integral_congr_ae (ae_of_all _ he),
      integral_finset_sum (Finset.Icc 1 N) (fun j _ => hIntg j)]
    apply Finset.sum_eq_zero; intro j hj
    rw [integral_const_mul, integral_trigBasis_mul_gTail hθ1 N j (Finset.mem_Icc.mp hj).1,
      if_neg (by have := (Finset.mem_Icc.mp hj).2; omega), mul_zero]
  have iAB : Integrable (fun x => (∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) ^ 2
      - 2 * ((∑ j ∈ Finset.Icc 1 N, (c j - θ j) * trigBasis j x) * gTail θ N x))
      (volume.restrict (Set.Icc (0:ℝ) 1)) := iS2.sub iSg
  rw [integral_add iAB ig2, integral_sub iS2 iSg, integral_const_mul,
    hStwo, hSg, integral_gTail_sq hθ1 N]
  ring

set_option maxHeartbeats 1000000 in
-- Large elaboration: nested `∫⁻`/`ofReal` bookkeeping over a finite sum of coefficient risks.
/-- **Exact MISE decomposition of the projection estimator**: for `1 ≤ N ≤ n − 1`,
`E‖f̂_{nN} − f‖₂² = σ_ξ²·N/n + ∑_{j≤N} αⱼ² + ρ_N` with `f = seriesFun θ`. -/
theorem proj_mise_decomposition {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n N : ℕ} {ξ : Fin n → Ω → ℝ} {θ : ℕ → ℝ} {σξ2 : ℝ}
    -- LEAN-ONLY: order range in which discrete orthonormality applies
    (hN : 1 ≤ N) (hN' : N ≤ n - 1)
    -- USER-INPUT: nonnegative noise level; model parameter
    (hσ : 0 ≤ σξ2)
    -- USER-INPUT: absolutely summable coefficients; the classical summability assumption
    (hθ1 : Summable fun j => |θ j|)
    -- LEAN-ONLY: measurability of the noise; standard regularity
    (hξm : ∀ i, Measurable (ξ i))
    -- USER-INPUT: mutually independent noise; the fixed-design regression model
    (hξi : iIndepFun ξ P)
    -- USER-INPUT: centered noise; the fixed-design regression model
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    -- USER-INPUT: common noise second moment `σ_ξ²` (lower-Lebesgue form); the model
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P = ENNReal.ofReal σξ2) :
    ∫⁻ ω, (∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal
        ((projEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) N x
          - seriesFun θ x) ^ 2)) ∂P
      = ENNReal.ofReal (σξ2 * N / n
          + (∑ j ∈ Finset.Icc 1 N, (riemannResidual θ n j) ^ 2) + tailEnergy θ N) := by
  have htailnn : 0 ≤ tailEnergy θ N := tsum_nonneg fun m => sq_nonneg _
  -- per-ω: the inner lower-Lebesgue integral is `ofReal` of the real `L²` expansion
  have key : ∀ ω, (∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal
        ((projEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) N x
          - seriesFun θ x) ^ 2))
      = ENNReal.ofReal (∑ j ∈ Finset.Icc 1 N,
          (coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j) ^ 2
          + tailEnergy θ N) := by
    intro ω
    have hcD : Continuous (fun x =>
        projEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) N x - seriesFun θ x) := by
      refine Continuous.sub ?_ (continuous_seriesFun hθ1)
      unfold projEstimator
      exact continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_trigBasis j))
    rw [← ofReal_integral_eq_lintegral_ofReal ((hcD.fun_pow 2).integrableOn_Icc)
      (ae_of_all _ fun x => sq_nonneg _)]
    congr 1
    unfold projEstimator
    exact proj_L2_sq_integral hθ1 hN
      (fun j => coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j)
  rw [lintegral_congr key]
  -- split `ofReal (∑ + tail)` into a finite sum plus a constant
  have hstep : ∀ ω, ENNReal.ofReal (∑ j ∈ Finset.Icc 1 N,
        (coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j) ^ 2
        + tailEnergy θ N)
      = (∑ j ∈ Finset.Icc 1 N, ENNReal.ofReal
          ((coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j) ^ 2))
        + ENNReal.ofReal (tailEnergy θ N) := by
    intro ω
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => sq_nonneg _) htailnn,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
  rw [lintegral_congr hstep]
  -- measurability of each summand in `ω`
  have hmeasa : ∀ j, Measurable (fun ω =>
      (coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j) ^ 2) := by
    intro j
    refine Measurable.pow_const (Measurable.sub ?_ measurable_const) 2
    unfold coeffEstimator
    refine Measurable.const_mul (Finset.measurable_sum _ (fun i _ => ?_)) _
    exact (measurable_const.add (hξm i)).mul measurable_const
  rw [lintegral_add_right _ measurable_const,
    lintegral_finset_sum _ (fun j _ => (hmeasa j).ennreal_ofReal), lintegral_const,
    measure_univ, mul_one]
  -- apply the exact coefficient risk termwise
  have hcoeff : ∀ j ∈ Finset.Icc 1 N, ∫⁻ ω, ENNReal.ofReal
      ((coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j) ^ 2) ∂P
      = ENNReal.ofReal (σξ2 / n + (riemannResidual θ n j) ^ 2) := by
    intro j hj
    exact coeffEstimator_sq_error (Finset.mem_Icc.mp hj).1
      (le_trans (Finset.mem_Icc.mp hj).2 hN') hσ hθ1 hξm hξi hξ0 hξ2
  rw [Finset.sum_congr rfl hcoeff]
  -- assemble the constants
  have hterm : ∀ j ∈ Finset.Icc 1 N, (0:ℝ) ≤ σξ2 / n + (riemannResidual θ n j) ^ 2 :=
    fun j _ => add_nonneg (div_nonneg hσ (Nat.cast_nonneg n)) (sq_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg hterm,
    ← ENNReal.ofReal_add (Finset.sum_nonneg hterm) htailnn]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
  have hcard : (N + 1 - 1 : ℕ) = N := by omega
  rw [hcard, nsmul_eq_mul]
  ring

end StatLean.NonparametricStatistics
