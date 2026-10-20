module
public import StatLean.NonparametricStatistics.Projection.DiscreteOrthogonality
public import StatLean.NonparametricStatistics.Projection.TrigOrthogonality
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Mean and quadratic risk of trigonometric coefficient estimates

At the regular design with independent centered noise of common second moment `σ_ξ²`, the
coefficient estimates `θ̂ⱼ = n⁻¹∑ᵢYᵢφⱼ(xᵢ)` for the target `f = seriesFun θ` satisfy, for
`1 ≤ j ≤ n − 1`:
$$ \mathbb E[\hat\theta_j] = \theta_j + \alpha_j, \qquad
   \mathbb E[(\hat\theta_j - \theta_j)^2] = \frac{\sigma_\xi^2}{n} + \alpha_j^2, $$
where `αⱼ` is the Riemann-sum residual — the entire stochastic error is `σ_ξ²/n` *exactly*,
by discrete orthonormality.

Also here: elementary facts about `seriesFun` under absolute summability of the coefficients
(uniform bound, square-summability), used across the projection risk files.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7.2, Proposition 1.16 (mean and squared error
of the coefficient estimators: $\mathbf{E}\hat\theta_j = \theta_j + \alpha_j$,
$\mathbf{E}(\hat\theta_j - \theta_j)^2 = \sigma^2/n + \alpha_j^2$).

**Proof formalization notes.** The mean is linearity plus `E ξᵢ = 0` (noise integrability is
*derived* from the second-moment equality: a finite `∫⁻ ξ²` forces `MemLp 2`, hence `L¹` on a
probability space). The variance uses independence to reduce to
`n⁻²∑ᵢ E ξᵢ²·φⱼ(xᵢ)² = (σ_ξ²/n)·(n⁻¹∑ᵢφⱼ(xᵢ)²)`, which is `σ_ξ²/n` by the diagonal case of
`trigBasis_discrete_orthonormal`. The `MSE` combines both with the cross term vanishing.

**Bibliographic comments.** J. Rice, *Ann. Statist.* **12** (1984), 1215–1230; the density
analogue of unbiased coefficient estimation is N. N. Čencov, *Soviet Math. Dokl.* **3**
(1962), 1559–1562.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- Under absolute summability of the coefficients, the series function is uniformly bounded:
`|seriesFun θ x| ≤ √2·∑'|θⱼ|`. -/
theorem seriesFun_abs_le {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) (x : ℝ) :
    |seriesFun θ x| ≤ Real.sqrt 2 * ∑' j, |θ j| := by
  unfold seriesFun
  have hb : ∀ j, |θ j * trigBasis j x| ≤ Real.sqrt 2 * |θ j| := by
    intro j
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (trigBasis_abs_le j x) (abs_nonneg _)
  have hsummable_bound : Summable fun j => Real.sqrt 2 * |θ j| := hθ1.mul_left _
  have hsummable_prod : Summable fun j => |θ j * trigBasis j x| :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hb hsummable_bound
  calc |∑' j, θ j * trigBasis j x|
      ≤ ∑' j, |θ j * trigBasis j x| := by
        have h := norm_tsum_le_tsum_norm (f := fun j => θ j * trigBasis j x)
          (by simpa [Real.norm_eq_abs] using hsummable_prod)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' j, Real.sqrt 2 * |θ j| := Summable.tsum_le_tsum hb hsummable_prod hsummable_bound
    _ = Real.sqrt 2 * ∑' j, |θ j| := tsum_mul_left

/-- Absolute summability of the coefficients implies square summability. -/
theorem summable_sq_of_summable_abs {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) :
    Summable fun j => (θ j) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
    (hθ1.mul_left (∑' i, |θ i|))
  have hb : |θ j| ≤ ∑' i, |θ i| := hθ1.le_tsum j (fun i _ => abs_nonneg _)
  calc (θ j) ^ 2 = |θ j| * |θ j| := by rw [← sq_abs (θ j)]; ring
    _ ≤ (∑' i, |θ i|) * |θ j| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/-- Square-integrability of the noise, derived from a finite lower-Lebesgue second moment. -/
private lemma memLp_two_of_lintegral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Ω → ℝ} {σξ2 : ℝ} (hξm : Measurable ξ)
    (hξ2 : ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 2) ∂P = ENNReal.ofReal σξ2) : MemLp ξ 2 P := by
  rw [memLp_two_iff_integrable_sq hξm.aestronglyMeasurable]
  refine ⟨(hξm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _), hξ2]
  exact ENNReal.ofReal_lt_top

/-- The Bochner second moment equals `σξ2`, recovered from the lower-Lebesgue form. -/
private lemma integral_sq_of_lintegral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Ω → ℝ} {σξ2 : ℝ} (hσ : 0 ≤ σξ2) (hInt : Integrable (fun ω => (ξ ω) ^ 2) P)
    (hξ2 : ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 2) ∂P = ENNReal.ofReal σξ2) :
    ∫ ω, (ξ ω) ^ 2 ∂P = σξ2 := by
  have h := ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun ω => sq_nonneg _)
  rw [hξ2] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun ω => sq_nonneg _) hσ).mp h

/-- **Mean of the coefficient estimate**: `E[θ̂ⱼ] = θⱼ + αⱼ` for the target
`f = seriesFun θ` (any `j`; no index restriction is needed for the mean). -/
theorem coeffEstimator_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ξ : Fin n → Ω → ℝ} {θ : ℕ → ℝ} {σξ2 : ℝ} (j : ℕ)
    -- USER-INPUT: absolutely summable coefficients (so the target series converges); the
    -- classical summability assumption
    (hθ1 : Summable fun j => |θ j|)
    -- LEAN-ONLY: measurability of the noise; standard regularity
    (hξm : ∀ i, Measurable (ξ i))
    -- USER-INPUT: centered noise; the fixed-design regression model
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    -- USER-INPUT: common noise second moment `σ_ξ²` (lower-Lebesgue form); the model
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P = ENNReal.ofReal σξ2) :
    ∫ ω, coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j ∂P
      = θ j + riemannResidual θ n j := by
  have hInt : ∀ i, Integrable (ξ i) P := fun i =>
    (memLp_two_of_lintegral_sq (hξm i) (hξ2 i)).integrable one_le_two
  have hsplit : ∀ i : Fin n,
      (fun ω => (seriesFun θ (regularDesign n i) + ξ i ω) * trigBasis j (regularDesign n i))
        = fun ω => seriesFun θ (regularDesign n i) * trigBasis j (regularDesign n i)
          + ξ i ω * trigBasis j (regularDesign n i) := fun i => by funext ω; ring
  have hsum_int : ∀ i : Fin n, Integrable
      (fun ω => (seriesFun θ (regularDesign n i) + ξ i ω)
        * trigBasis j (regularDesign n i)) P := by
    intro i; rw [hsplit i]; exact (integrable_const _).add ((hInt i).mul_const _)
  unfold coeffEstimator
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun i _ => hsum_int i)]
  have hone : ∀ i : Fin n, ∫ ω, (seriesFun θ (regularDesign n i) + ξ i ω)
        * trigBasis j (regularDesign n i) ∂P
      = seriesFun θ (regularDesign n i) * trigBasis j (regularDesign n i) := by
    intro i
    rw [hsplit i, integral_add (integrable_const _) ((hInt i).mul_const _), integral_const,
      integral_mul_const, hξ0 i, zero_mul, add_zero, probReal_univ, one_smul]
  rw [Finset.sum_congr rfl (fun i _ => hone i)]
  unfold riemannResidual
  ring

set_option maxHeartbeats 1000000 in
-- Large elaboration: variance identity expands a double sum over the design with independence.
/-- **Quadratic risk of the coefficient estimate**: for `1 ≤ j ≤ n − 1`,
`E[(θ̂ⱼ − θⱼ)²] = σ_ξ²/n + αⱼ²` — exactly. -/
theorem coeffEstimator_sq_error {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ξ : Fin n → Ω → ℝ} {θ : ℕ → ℝ} {σξ2 : ℝ} {j : ℕ}
    -- LEAN-ONLY: the index range in which discrete orthonormality holds
    (hj : 1 ≤ j) (hj' : j ≤ n - 1)
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
    ∫⁻ ω, ENNReal.ofReal
        ((coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j) ^ 2) ∂P
      = ENNReal.ofReal (σξ2 / n + (riemannResidual θ n j) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have memξ : ∀ i, MemLp (ξ i) 2 P := fun i => memLp_two_of_lintegral_sq (hξm i) (hξ2 i)
  have hInt : ∀ i, Integrable (ξ i) P := fun i => (memξ i).integrable one_le_two
  set Z : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i : Fin n, ξ i ω
    * trigBasis j (regularDesign n i) with hZ
  -- `Z` is square-integrable
  have hZmemLp : MemLp Z 2 P := by
    have hsum : MemLp (fun ω => ∑ i : Fin n, ξ i ω * trigBasis j (regularDesign n i)) 2 P := by
      have h := memLp_finset_sum' (Finset.univ : Finset (Fin n))
        (f := fun i ω => ξ i ω * trigBasis j (regularDesign n i))
        (fun i _ => (memξ i).mul_const _)
      have heq : (∑ i : Fin n, fun ω => ξ i ω * trigBasis j (regularDesign n i))
          = fun ω => ∑ i : Fin n, ξ i ω * trigBasis j (regularDesign n i) := by
        funext ω; rw [Finset.sum_apply]
      rw [heq] at h; exact h
    simp only [hZ]; exact hsum.const_mul _
  have hintZ : Integrable Z P := hZmemLp.integrable one_le_two
  have hintZ2 : Integrable (fun ω => Z ω ^ 2) P := hZmemLp.integrable_sq
  have hcZ : MemLp (fun ω => riemannResidual θ n j + Z ω) 2 P :=
    (memLp_const (riemannResidual θ n j)).add hZmemLp
  have hint_all : Integrable (fun ω => (riemannResidual θ n j + Z ω) ^ 2) P :=
    hcZ.integrable_sq
  -- pointwise: `θ̂ⱼ − θⱼ = αⱼ + Z`
  have hpt : ∀ ω, coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j
      = riemannResidual θ n j + Z ω := by
    intro ω
    simp only [hZ]
    unfold coeffEstimator riemannResidual
    have hs : ∀ i : Fin n,
        (seriesFun θ (regularDesign n i) + ξ i ω) * trigBasis j (regularDesign n i)
          = seriesFun θ (regularDesign n i) * trigBasis j (regularDesign n i)
            + ξ i ω * trigBasis j (regularDesign n i) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, mul_add]
    ring
  -- mean of `Z` is zero
  have hZ0 : ∫ ω, Z ω ∂P = 0 := by
    simp only [hZ]
    rw [integral_const_mul, integral_finset_sum Finset.univ
      (fun i _ => ((memξ i).mul_const _).integrable one_le_two)]
    have hz : ∀ i : Fin n, ∫ ω, ξ i ω * trigBasis j (regularDesign n i) ∂P = 0 := by
      intro i; rw [integral_mul_const, hξ0 i, zero_mul]
    rw [Finset.sum_congr rfl (fun i _ => hz i)]; simp
  -- second moment of `Z` is `σξ2 / n`
  have hmulint : ∀ i k : Fin n, Integrable (fun ω => ξ i ω * ξ k ω) P := fun i k =>
    (memξ i).integrable_mul (memξ k)
  have hMoff : ∀ i k : Fin n, i ≠ k → ∫ ω, ξ i ω * ξ k ω ∂P = 0 := by
    intro i k hik
    rw [(hξi.indepFun hik).integral_fun_mul_eq_mul_integral (hξm i).aestronglyMeasurable
      (hξm k).aestronglyMeasurable, hξ0 i, zero_mul]
  have hMdiag : ∀ i : Fin n, ∫ ω, ξ i ω * ξ i ω ∂P = σξ2 := by
    intro i
    have he : (fun ω => ξ i ω * ξ i ω) = fun ω => (ξ i ω) ^ 2 := by funext ω; rw [sq]
    rw [he]; exact integral_sq_of_lintegral_sq hσ (memξ i).integrable_sq (hξ2 i)
  have hphi : ∑ i : Fin n,
      trigBasis j (regularDesign n i) * trigBasis j (regularDesign n i) = (n : ℝ) := by
    have hd := trigBasis_discrete_orthonormal hj hj' hj hj'
    rw [if_pos rfl, inv_mul_eq_div, div_eq_one_iff_eq hn0] at hd
    exact hd
  have hZ2val : ∫ ω, Z ω ^ 2 ∂P = σξ2 / n := by
    have hexpand : ∀ ω, Z ω ^ 2 = (n : ℝ)⁻¹ ^ 2 * ∑ i : Fin n, ∑ k : Fin n,
        (ξ i ω * ξ k ω) * (trigBasis j (regularDesign n i) * trigBasis j (regularDesign n k)) := by
      intro ω
      simp only [hZ, mul_pow]
      congr 1
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [integral_congr_ae (ae_of_all _ hexpand), integral_const_mul,
      integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ
        (fun k _ => (hmulint i k).mul_const _))]
    have hrow : ∀ i : Fin n, ∫ ω, (∑ k : Fin n,
        (ξ i ω * ξ k ω) * (trigBasis j (regularDesign n i)
          * trigBasis j (regularDesign n k))) ∂P
        = σξ2 * (trigBasis j (regularDesign n i) * trigBasis j (regularDesign n i)) := by
      intro i
      rw [integral_finset_sum Finset.univ (fun k _ => (hmulint i k).mul_const _),
        Finset.sum_eq_single i]
      · rw [integral_mul_const, hMdiag i]
      · intro k _ hki
        rw [integral_mul_const, hMoff i k (Ne.symm hki), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [Finset.sum_congr rfl (fun i _ => hrow i), ← Finset.mul_sum, hphi]
    field_simp
  -- assemble
  have hfinal : ∫ ω, (riemannResidual θ n j + Z ω) ^ 2 ∂P
      = σξ2 / n + (riemannResidual θ n j) ^ 2 := by
    have hexp : ∀ ω, (riemannResidual θ n j + Z ω) ^ 2
        = (riemannResidual θ n j) ^ 2 + (2 * riemannResidual θ n j) * Z ω + Z ω ^ 2 :=
      fun ω => by ring
    have i1 : Integrable (fun ω => (riemannResidual θ n j) ^ 2
        + (2 * riemannResidual θ n j) * Z ω) P :=
      (integrable_const ((riemannResidual θ n j) ^ 2)).add
        (hintZ.const_mul (2 * riemannResidual θ n j))
    rw [integral_congr_ae (ae_of_all _ hexp),
      integral_add i1 hintZ2,
      integral_add (integrable_const ((riemannResidual θ n j) ^ 2))
        (hintZ.const_mul (2 * riemannResidual θ n j)),
      integral_const, integral_const_mul, hZ0, hZ2val]
    simp only [probReal_univ, one_smul, mul_zero, add_zero]
    ring
  calc ∫⁻ ω, ENNReal.ofReal
        ((coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j) ^ 2) ∂P
      = ∫⁻ ω, ENNReal.ofReal ((riemannResidual θ n j + Z ω) ^ 2) ∂P := by
        exact lintegral_congr fun ω => by rw [hpt ω]
    _ = ENNReal.ofReal (∫ ω, (riemannResidual θ n j + Z ω) ^ 2 ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint_all (ae_of_all _ fun ω => sq_nonneg _)).symm
    _ = ENNReal.ofReal (σξ2 / n + (riemannResidual θ n j) ^ 2) := by rw [hfinal]

end StatLean.NonparametricStatistics
