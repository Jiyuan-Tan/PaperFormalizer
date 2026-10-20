module
public import StatLean.NonparametricStatistics.KernelDensity.Variance
public import StatLean.NonparametricStatistics.KernelDensity.Bias
public import StatLean.NonparametricStatistics.KernelDensity.UniformDensityBound

@[expose] public section

/-!
# Pointwise minimax rate of the kernel density estimator over Hölder classes

With bandwidth `h = α·n^{−1/(2β+1)}`, the kernel estimator attains, **uniformly over the
point `x₀` and the density class `P(β, L)`**, the pointwise rate
$$ \sup_{x_0}\ \sup_{p \in \mathcal P(\beta,L)}
   \mathbb E_p\bigl[(\hat p_n(x_0) - p(x_0))^2\bigr] \;\le\; C\,n^{-\frac{2\beta}{2\beta+1}}
   \qquad (n \ge 1), $$
with `C = C(β, L, α, K)`. (The rate `n^{−β/(2β+1)}` is optimal over the class; lower bounds
are minimax-theory material outside this area.)

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.1, Theorem 1.1 (pointwise rate
$n^{-2\beta/(2\beta+1)}$ of the kernel density estimator over $\mathcal{P}(\beta, L)$).

**Proof formalization notes.** MSE = bias² + variance (`kdeMseAt_eq_bias_sq_add_variance`);
the bias term is `(C₂·h^β)²` (`kde_bias_abs_le`), the variance term `C₁/(nh)`
(`kde_variance_le`) with `pmax` supplied *internally* by `holder_density_uniform_bound` — the
uniform boundedness of the class is derived, not assumed. Substituting the bandwidth gives
`C = C₂²α^{2β} + C₁/α`; since `pmax` (inside `C₁`) is existential, the headline constant is
existential too, with the stated dependence. Uniformity in `x₀`, `p`, and the underlying
probability space is by quantifier position: `C` is chosen before them.

**Bibliographic comments.** The pointwise rate `n^{−2β/(2β+1)}` for kernel estimators over
smoothness classes is classical, going back to M. Rosenblatt, *Ann. Math. Statist.* **27**
(1956), 832–837, and E. Parzen, *Ann. Math. Statist.* **33** (1962), 1065–1076, with the
higher-order-kernel form standard since the 1960s–70s (cf. C. J. Stone, *Ann. Statist.* **8**
(1980), 1348–1360, for optimality).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Pointwise rate over the Hölder density class**: with `h = α·n^{−1/(2β+1)}` there is a
constant `C = C(β, L, α, K)` such that for every `n ≥ 1`, every point, every density of
`P(β, L)`, and every i.i.d. sample of size `n`,
`E[(p̂ₙ(x₀) − p(x₀))²] ≤ C·n^{−2β/(2β+1)}`. -/
theorem kde_pointwise_rate {β L α : ℝ}
    -- USER-INPUT: positive smoothness, Hölder constant, and bandwidth scale; class and
    -- tuning parameters
    (hβ : 0 < β) (hL : 0 < L) (hα : 0 < α)
    {K : ℝ → ℝ}
    -- USER-INPUT: `K` is a kernel of order `ℓ = holderIndex β`; classical bias-reduction
    -- condition (cf. Parzen 1962)
    (hK : IsKernelOfOrder K (holderIndex β))
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: square-integrable kernel; classical variance-bound input
    (hK2 : Integrable fun u => (K u) ^ 2)
    -- USER-INPUT: finite `β`-moment of the kernel; classical bias-bound input
    (hKβ : Integrable fun u => |u| ^ β * |K u|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ) (p : ℝ → ℝ) (x₀ : ℝ),
        1 ≤ n →
        IsIIDSample P X (densityMeasure p) →
        (∀ i, Measurable (X i)) →
        IsHolderDensity β L p →
        kdeMseAt P X K (α * (n : ℝ) ^ (-(1 / (2 * β + 1)))) p x₀
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
  obtain ⟨pmax, hpm, hbdd⟩ := holder_density_uniform_bound β L hβ hL
  have hCnn : 0 ≤ kdeBiasConst β L K := by
    rw [kdeBiasConst]
    exact mul_nonneg (div_nonneg hL.le (by positivity)) (integral_nonneg fun u => by positivity)
  have hCb : 0 ≤ (kdeBiasConst β L K) ^ 2 * α ^ (2 * β) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hα.le _)
  have hCv : 0 ≤ kdeVarianceConst K pmax / α := by
    rw [kdeVarianceConst]
    exact div_nonneg (mul_nonneg hpm.le (integral_nonneg fun u => sq_nonneg _)) hα.le
  refine ⟨(kdeBiasConst β L K) ^ 2 * α ^ (2 * β) + kdeVarianceConst K pmax / α + 1,
    by linarith, ?_⟩
  intro Ω hMS P hP n X p x₀ hn hs hX hpd
  have hnpos : 0 < n := hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hne : (2 * β + 1) ≠ 0 := by positivity
  set h := α * (n : ℝ) ^ (-(1 / (2 * β + 1))) with hh_def
  have hh : 0 < h := mul_pos hα (Real.rpow_pos_of_pos hnR _)
  have hp_meas : Measurable p :=
    (contDiffOn_univ.mp (MemHolderOn.contDiffOn hpd.holder)).continuous.measurable
  have h0 : ∀ y, 0 ≤ p y := hpd.nonneg
  have hbdd' : ∀ y, p y ≤ pmax := hbdd p hpd
  have hL2 : MemLp (fun ω => kde X K h ω x₀) 2 P :=
    kde_memLp_two hh hs hX hp_meas h0 hbdd' hKmeas hK2
  have hbias : |kdeBiasAt P X K h p x₀| ≤ kdeBiasConst β L K * h ^ β :=
    kde_bias_abs_le hβ hL.le hnpos hh hs hpd hK hKmeas hKβ
  have hb2 : (kdeBiasAt P X K h p x₀) ^ 2 ≤ (kdeBiasConst β L K * h ^ β) ^ 2 :=
    sq_le_sq' (abs_le.mp hbias).1 (abs_le.mp hbias).2
  have hT1 : (kdeBiasConst β L K * h ^ β) ^ 2
      = (kdeBiasConst β L K) ^ 2 * α ^ (2 * β) * (n : ℝ) ^ (-(2 * β / (2 * β + 1))) := by
    rw [mul_pow]
    have hhβ2 : (h ^ β) ^ 2 = h ^ (2 * β) := by
      rw [← Real.rpow_natCast (h ^ β) 2, ← Real.rpow_mul hh.le]; congr 1; push_cast; ring
    rw [hhβ2, hh_def, Real.mul_rpow hα.le (Real.rpow_nonneg hnR.le _), ← Real.rpow_mul hnR.le]
    have hexp : -(1 / (2 * β + 1)) * (2 * β) = -(2 * β / (2 * β + 1)) := by
      rw [neg_mul, one_div_mul_eq_div]
    rw [hexp]; ring
  have hT2 : kdeVarianceConst K pmax / ((n : ℝ) * h)
      = kdeVarianceConst K pmax / α * (n : ℝ) ^ (-(2 * β / (2 * β + 1))) := by
    have hnh : (n : ℝ) * h = α * (n : ℝ) ^ (2 * β / (2 * β + 1)) := by
      rw [hh_def]
      have hstep : (n : ℝ) * (α * (n : ℝ) ^ (-(1 / (2 * β + 1))))
          = α * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / (2 * β + 1)))) := by
        rw [Real.rpow_one]; ring
      rw [hstep, ← Real.rpow_add hnR]
      have hexp2 : (1 : ℝ) + -(1 / (2 * β + 1)) = 2 * β / (2 * β + 1) := by
        field_simp; ring
      rw [hexp2]
    rw [hnh, Real.rpow_neg hnR.le, ← div_eq_mul_inv, div_div]
  rw [kdeMseAt_eq_bias_sq_add_variance hL2]
  have hC1nn : 0 ≤ kdeVarianceConst K pmax / ((n : ℝ) * h) := by
    rw [kdeVarianceConst]
    exact div_nonneg (mul_nonneg hpm.le (integral_nonneg fun u => sq_nonneg _)) (mul_pos hnR hh).le
  refine (add_le_add (ENNReal.ofReal_le_ofReal hb2)
    (kde_variance_le hh hs hX hp_meas h0 hbdd' hKmeas hK2)).trans ?_
  rw [← ENNReal.ofReal_add (sq_nonneg _) hC1nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hT1, hT2]
  have hfac : ((kdeBiasConst β L K) ^ 2 * α ^ (2 * β) + kdeVarianceConst K pmax / α + 1)
        * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))
      = (kdeBiasConst β L K) ^ 2 * α ^ (2 * β) * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))
        + kdeVarianceConst K pmax / α * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))
        + (n : ℝ) ^ (-(2 * β / (2 * β + 1))) := by ring
  rw [hfac]
  linarith [Real.rpow_nonneg hnR.le (-(2 * β / (2 * β + 1)))]

end StatLean.NonparametricStatistics
