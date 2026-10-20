module
public import StatLean.NonparametricStatistics.LocalPolynomial.PointwiseRisk
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# L² risk of the local polynomial estimator

The integrated version of the pointwise rate: with `h = α·n^{−1/(2β+1)}`, uniformly over
`f ∈ Σ(β, L)` on `[0,1]`,
$$ \mathbb E\,\|\hat f_n - f\|_2^2 \;\le\; C\,n^{-\frac{2\beta}{2\beta+1}},
   \qquad \|g\|_2^2 = \int_0^1 g^2(t)\,dt, $$
with the same explicit constant as the pointwise bound.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6.1, Corollary 1.2 ($L^2$ rate of the local
polynomial estimator).

**Proof formalization notes.** Tonelli swaps the sample-space and `t` integrals; the pointwise
MSE bound (`lp_pointwise_rate`) is uniform over `t ∈ [0,1]`, and `volume (Icc 0 1) = 1`, so
integrating costs nothing. Everything stays in `∫⁻`, so no measurability of the risk in `t`
is needed beyond joint measurability of the integrand (finite sums of measurable functions).

**Bibliographic comments.** C. J. Stone, "Optimal global rates of convergence for
nonparametric regression," *Ann. Statist.* **10** (1982), 1040–1053.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- Determinant of a `t`-parametrized matrix with measurable entries is measurable in `t`. -/
private lemma measurable_det_of_entries {ι : ℕ} {M : ℝ → Matrix (Fin ι) (Fin ι) ℝ}
    (hM : ∀ a b, Measurable (fun t => M t a b)) : Measurable (fun t => (M t).det) := by
  classical
  simp_rw [Matrix.det_apply]
  refine Finset.measurable_sum _ (fun σ _ => ?_)
  exact (Finset.measurable_prod _ (fun i _ => hM (σ i) i)).const_smul _

/-- The LP weight `t ↦ W*ᵢ(t)` is measurable (needed for the Tonelli swap of the two risk
integrals): each design-matrix entry, its determinant and adjugate, hence each entry of the
inverse, is measurable in `t`. -/
private lemma lpWeight_measurable_in_t {n : ℕ} (xdat : Fin n → ℝ) {K : ℝ → ℝ}
    (hK : Measurable K) {h : ℝ} (ℓ : ℕ) (i : Fin n) :
    Measurable (fun t => lpWeight xdat K h ℓ t i) := by
  classical
  have hbasis : ∀ (j : Fin (ℓ + 1)) (i' : Fin n),
      Measurable (fun t => lpBasis ℓ ((xdat i' - t) / h) j) := by
    intro j i'
    simp only [lpBasis]
    exact (((measurable_const.sub measurable_id).div_const h).pow_const _).div_const _
  have hKz : ∀ i' : Fin n, Measurable (fun t => K ((xdat i' - t) / h)) :=
    fun i' => hK.comp ((measurable_const.sub measurable_id).div_const h)
  have hM : ∀ a b, Measurable (fun t => (lpMatrix xdat K h ℓ t) a b) := by
    intro a b
    simp only [lpMatrix, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    refine Measurable.const_mul (Finset.measurable_sum _ (fun i' _ => ?_)) _
    exact (hKz i').mul ((hbasis a i').mul (hbasis b i'))
  have hdet : Measurable (fun t => (lpMatrix xdat K h ℓ t).det) := measurable_det_of_entries hM
  have hadj : ∀ a b, Measurable (fun t => (lpMatrix xdat K h ℓ t).adjugate a b) := by
    intro a b
    simp_rw [Matrix.adjugate_apply]
    refine measurable_det_of_entries (fun x y => ?_)
    simp only [Matrix.updateRow_apply]
    by_cases hx : x = b
    · simp only [hx, if_true]; exact measurable_const
    · simp only [hx, if_false]; exact hM x y
  have hMinv : ∀ b, Measurable (fun t => (lpMatrix xdat K h ℓ t)⁻¹ 0 b) := by
    intro b
    simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact hdet.inv.mul (hadj 0 b)
  have hmulvec : Measurable (fun t =>
      (lpMatrix xdat K h ℓ t)⁻¹.mulVec (lpBasis ℓ ((xdat i - t) / h)) 0) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ (fun b _ => (hMinv b).mul (hbasis b i))
  simp only [lpWeight]
  exact (measurable_const.mul hmulvec).mul (hKz i)

/-- **L² rate of LP(`ℓ`) over `Σ(β, L)`**: with `h = α·n^{−1/(2β+1)}`,
`E ∫₀¹ (f̂(t) − f(t))² dt ≤ lpRateConst·n^{−2β/(2β+1)}`. -/
theorem lp_l2_rate {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h lam0 a₀ Kmax : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {β L α : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hL : 0 ≤ L) (hα : 0 < α) (hσ : 0 ≤ σmax2)
    (hn : 0 < n)
    -- LEAN-ONLY: rate-optimal bandwidth, packaged as an equation
    (hform : h = α * (n : ℝ) ^ (-(1 / (2 * β + 1))))
    -- LEAN-ONLY: side condition `h ≥ 1/(2n)`, satisfied for all large `n`
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- LEAN-ONLY: measurability of the kernel, needed for the Tonelli swap of the two risk
    -- integrals; standard regularity (all classical kernels qualify)
    (hKmeas : Measurable K)
    -- USER-INPUT: design in `[0,1]`, eigenvalue floor, boxed kernel, design density bound;
    -- the standing fixed-design assumptions
    (hx : ∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1)
    (heig : DesignEigenvalueLB xdat K h (holderIndex β) lam0)
    (hbox : KernelBoxed K Kmax)
    (hdens : DesignDensityBound xdat a₀)
    -- USER-INPUT: the regression function lies in `Σ(β, L)` on `[0,1]`
    (hf : MemHolderOn β L f (Set.Icc 0 1))
    -- LEAN-ONLY: measurability of the noise; standard regularity
    (hξm : ∀ i, Measurable (ξ i))
    -- USER-INPUT: independent centered noise with second moments ≤ `σ²_max`; the
    -- fixed-design regression model
    (hξi : iIndepFun ξ P)
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2) :
    ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t
          - f t) ^ 2)) ∂P
      ≤ ENNReal.ofReal (lpRateConst β L α σmax2 Kmax lam0 a₀
          * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
  -- joint measurability of the integrand on `Ω × [0,1]`
  have hSf : Measurable (fun p : Ω × ℝ =>
      lpEstimator xdat (fun i => f (xdat i) + ξ i p.1) K h (holderIndex β) p.2) := by
    simp only [lpEstimator]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (measurable_const.add ((hξm i).comp measurable_fst)).mul
      ((lpWeight_measurable_in_t xdat hKmeas (holderIndex β) i).comp measurable_snd)
  have hf_snd : AEMeasurable (fun p : Ω × ℝ => f p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (hf.contDiffOn.continuousOn.aemeasurable measurableSet_Icc).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have hmeas : AEMeasurable (Function.uncurry (fun ω t => ENNReal.ofReal
      ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t - f t) ^ 2)))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (((hSf.aemeasurable.sub hf_snd).pow_const 2)).ennreal_ofReal
  -- Tonelli swap, then the pointwise rate at each `t ∈ [0,1]`
  rw [lintegral_lintegral_swap hmeas]
  calc ∫⁻ t in Set.Icc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t - f t) ^ 2) ∂P
      ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (lpRateConst β L α σmax2 Kmax lam0 a₀
          * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
          (ae_of_all _ fun t ht => ?_))
        exact lp_pointwise_rate hβ hL hα hσ hn hform hhl hlam ha₀ hx heig hbox hdens hf hξm
          hξi hξ0 hξ2 ht
    _ = ENNReal.ofReal (lpRateConst β L α σmax2 Kmax lam0 a₀
          * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
        rw [setLIntegral_const, Real.volume_Icc]
        simp

end StatLean.NonparametricStatistics
