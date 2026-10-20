module
public import StatLean.NonparametricStatistics.KernelDensity.Bias
public import StatLean.NonparametricStatistics.KernelDensity.AuxiliaryKernel

@[expose] public section

/-!
# Uniform boundedness of Hölder densities

Densities in a Hölder class are uniformly bounded:
$$ \sup_{x} \sup_{p \in \mathcal P(\beta, L)} p(x) \;\le\; p_{\max}(\beta, L) < \infty. $$

This is the hidden ingredient of the pointwise minimax rate: the variance bound needs
`p ≤ pmax`, and over the class this bound must be *derived*, not assumed — keeping it as a
hypothesis of the rate theorem would silently shrink the class.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.1, Eq. (1.9) (uniform bound on the densities
of the class $\mathcal{P}(\beta, L)$ — the hidden dependency of Theorem 1.1).

**Proof formalization notes.** Apply the deterministic bias core
(`abs_integral_kernel_taylor_le`) with bandwidth `h = 1` and an auxiliary **bounded** kernel
`K*` of order `ℓ` supported in `[−1,1]` (`exists_bounded_kernel_of_order`):
`p(x) ≤ |∫K*(u)p(x+u)du| + C₂* ≤ sup|K*|·∫p + C₂* = sup|K*| + C₂*`, using `∫ p = 1` and
`p ≥ 0`. The compact support makes the `β`-moment of `K*` finite. The bound `pmax` is
existential (it depends on the auxiliary kernel construction), which suffices for its sole
consumer, the rate theorem.

**Bibliographic comments.** A classical remark in the pointwise risk analysis of kernel
estimators; folklore, implicit in E. Parzen, *Ann. Math. Statist.* **33** (1962), 1065–1076.
-/

open MeasureTheory

namespace StatLean.NonparametricStatistics

/-- **Uniform bound on a Hölder density class**: there is `pmax = pmax(β, L)` bounding every
density of `P(β, L)` everywhere. -/
theorem holder_density_uniform_bound (β L : ℝ)
    -- USER-INPUT: positive smoothness and Hölder constant; class parameters
    (hβ : 0 < β) (hL : 0 < L) :
    ∃ pmax : ℝ, 0 < pmax ∧
      ∀ p : ℝ → ℝ, IsHolderDensity β L p → ∀ x, p x ≤ pmax := by
  obtain ⟨K, Kmax, hKmax, hord, hbd, hsupp⟩ := exists_bounded_kernel_of_order (holderIndex β)
  -- finite `β`-moment of the compactly supported kernel `K`
  have hcont : Continuous fun u => |u| ^ β := continuous_abs.rpow_const (fun _ => Or.inr hβ.le)
  have hKaesm : AEStronglyMeasurable K volume := by
    have h := (hord.integrable_pow 0 (Nat.zero_le _)).aestronglyMeasurable
    simpa only [pow_zero, one_mul] using h
  have hKabs : AEStronglyMeasurable (fun u => |K u|) volume := by
    have h := hKaesm.norm; simpa only [Real.norm_eq_abs] using h
  have haesm : AEStronglyMeasurable (fun u => |u| ^ β * |K u|) volume :=
    hcont.aestronglyMeasurable.mul hKabs
  have hM_int : Integrable (Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => Kmax)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hbound : ∀ u, |u| ^ β * |K u|
      ≤ Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => Kmax) u := by
    intro u
    by_cases hu : u ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hu]
      have h1 : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
      calc |u| ^ β * |K u| ≤ 1 * Kmax :=
            mul_le_mul (Real.rpow_le_one (abs_nonneg _) h1 hβ.le) (hbd u) (abs_nonneg _)
              zero_le_one
        _ = Kmax := one_mul _
    · rw [Set.indicator_of_notMem hu, hsupp u hu, abs_zero, mul_zero]
  have hKβ : Integrable fun u => |u| ^ β * |K u| :=
    hM_int.mono' haesm (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hbound u)
  have hCnn : 0 ≤ kdeBiasConst β L K := by
    rw [kdeBiasConst]
    exact mul_nonneg (div_nonneg hL.le (by positivity)) (integral_nonneg fun u => by positivity)
  refine ⟨kdeBiasConst β L K + Kmax, by linarith, fun p hpd x => ?_⟩
  have h0 : ∀ y, 0 ≤ p y := hpd.nonneg
  have hp_int : Integrable p := by
    by_contra hni
    have := hpd.integral_one; rw [integral_undef hni] at this; exact one_ne_zero this.symm
  have hshift : Integrable (fun u => p (x + u * 1)) := by
    simp only [mul_one]
    exact ((measurePreserving_add_left (volume : Measure ℝ) x).integrable_comp
      hp_int.aestronglyMeasurable).mpr hp_int
  have hintp : Integrable fun u => K u * p (x + u * 1) :=
    integrable_kernel_mul_holder hβ hL.le hpd.holder hord hKβ one_pos x
  have hAle : (∫ u, K u * p (x + u * 1)) ≤ Kmax := by
    refine (integral_mono hintp (hshift.const_mul Kmax) (fun u => ?_)).trans (le_of_eq ?_)
    · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hbd u)) (h0 _)
    · rw [integral_const_mul]; simp only [mul_one]
      rw [integral_add_left_eq_self p x, hpd.integral_one, mul_one]
  have hbias := abs_integral_kernel_taylor_le hβ hL.le hpd.holder hord hKβ one_pos x
  rw [Real.one_rpow, mul_one] at hbias
  have := (abs_le.mp hbias).1
  linarith

end StatLean.NonparametricStatistics
