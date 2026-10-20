module
public import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
public import StatLean.NonparametricStatistics.SmoothnessClasses.HolderTaylor

@[expose] public section

/-!
# Pointwise bias of the kernel density estimator

For a density in the Hölder class `P(β, L)` and a kernel of order `ℓ = holderIndex β` with
finite `β`-moment:
$$ |b(x_0)| \;\le\; C_2\,h^{\beta}, \qquad C_2 = \frac{L}{\ell!}\int |u|^{\beta}|K(u)|\,du, $$
for all `x₀`, `h > 0`, `n ≥ 1` — non-asymptotic, dimension-free in `n`.

Contents:
* `integrable_kernel_mul_holder` — the *derived* integrability of `u ↦ K(u)·f(x₀ + uh)` for
  global Hölder `f` (never a hypothesis of the headline results);
* `abs_integral_kernel_taylor_le` — the deterministic core:
  `|∫ K(u)·f(x₀+uh) du − f(x₀)| ≤ C₂·h^β`;
* `kde_bias_abs_le` — the probabilistic statement for the estimator's bias.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.1, Proposition 1.2 (pointwise bias bound on
$\mathcal{P}(\beta, L)$, constant $C_2 = \frac{L}{\ell!}\int |u|^{\beta}|K(u)|\,du$).

**Proof formalization notes.** Write `∫K(u)f(x₀+uh)du − f(x₀) = ∫K(u)·(f(x₀+uh) − f(x₀))du`
using `∫K = 1`; insert the order-`ℓ` Taylor polynomial: the vanishing moments kill every term
`f⁽ʲ⁾(x₀)·hʲ·∫uʲK`, `1 ≤ j ≤ ℓ` (and the `j = 0` term cancels with `f(x₀)`), leaving the
Hölder–Taylor remainder, bounded pointwise by `(L/ℓ!)·|uh|^β`
(`MemHolder.taylor_remainder_abs_le`); integrating gives `C₂·h^β`. Integrability of every
intermediate integrand comes from the kernel's moment integrability and the polynomial-growth
envelope `MemHolder.abs_le_growth`. The probabilistic form composes with
`kdeMeanAt_eq_integral_kernel`.

**Bibliographic comments.** The bias computation with higher-order kernels is classical:
E. Parzen, *Ann. Math. Statist.* **33** (1962), 1065–1076; M. S. Bartlett, *Sankhyā Ser. A*
**25** (1963), 245–254.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Derived integrability**: for a global Hölder function `f` and a kernel of order
`ℓ = holderIndex β` with finite `β`-moment, `u ↦ K(u)·f(x₀ + u·h)` is integrable.
This discharges the integrability hypotheses of the law-transfer lemmas — it is never itself
a hypothesis of a headline theorem. -/
theorem integrable_kernel_mul_holder {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    {f K : ℝ → ℝ} (hf : MemHolder β L f)
    (hK : IsKernelOfOrder K (holderIndex β))
    (hKβ : Integrable fun u => |u| ^ β * |K u|)
    {h : ℝ} (hh : 0 < h) (x₀ : ℝ) :
    Integrable fun u => K u * f (x₀ + u * h) := by
  have hfcont : Continuous f := (contDiffOn_univ.mp (MemHolderOn.contDiffOn hf)).continuous
  have hKaesm : AEStronglyMeasurable K volume := by
    have h := (hK.integrable_pow 0 (Nat.zero_le _)).aestronglyMeasurable
    simpa only [pow_zero, one_mul] using h
  have haesm : AEStronglyMeasurable (fun u => K u * f (x₀ + u * h)) volume :=
    hKaesm.mul (hfcont.comp (by fun_prop)).aestronglyMeasurable
  have hint_dom : Integrable (fun u =>
      (∑ j ∈ Finset.range (holderIndex β + 1),
        |iteratedDeriv j f x₀| / (Nat.factorial j : ℝ) * h ^ j * (|u| ^ j * |K u|))
      + (L / (Nat.factorial (holderIndex β) : ℝ) * h ^ β) * (|u| ^ β * |K u|)) := by
    apply Integrable.add
    · apply integrable_finset_sum
      intro j hj
      have hjℓ : j ≤ holderIndex β := Finset.mem_range_succ_iff.mp hj
      have hjint : Integrable (fun u => |u| ^ j * |K u|) := by
        have h := (hK.integrable_pow j hjℓ).abs
        simpa only [abs_mul, abs_pow] using h
      exact hjint.const_mul _
    · exact hKβ.const_mul _
  refine hint_dom.mono' haesm (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hg := hf.abs_le_growth hβ hL x₀ (u * h)
  have huh : |u * h| = |u| * h := by rw [abs_mul, abs_of_pos hh]
  calc |K u| * |f (x₀ + u * h)|
      ≤ |K u| * ((∑ j ∈ Finset.range (holderIndex β + 1),
            |iteratedDeriv j f x₀| * |u * h| ^ j / (Nat.factorial j : ℝ))
          + L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β) :=
        mul_le_mul_of_nonneg_left hg (abs_nonneg _)
    _ = (∑ j ∈ Finset.range (holderIndex β + 1),
          |iteratedDeriv j f x₀| / (Nat.factorial j : ℝ) * h ^ j * (|u| ^ j * |K u|))
        + (L / (Nat.factorial (holderIndex β) : ℝ) * h ^ β) * (|u| ^ β * |K u|) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [huh, mul_pow]; ring
        · rw [huh, Real.mul_rpow (abs_nonneg u) hh.le]; ring

/-- **Deterministic bias core**: for global Hölder `f` and a kernel of order
`ℓ = holderIndex β` with finite `β`-moment,
`|∫ K(u)·f(x₀ + uh) du − f(x₀)| ≤ C₂·h^β` with `C₂ = kdeBiasConst β L K`. -/
theorem abs_integral_kernel_taylor_le {β L : ℝ}
    -- USER-INPUT: positive smoothness, nonnegative Hölder constant; class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f K : ℝ → ℝ}
    -- USER-INPUT: `f` lies in the global Hölder class `Σ(β, L)`
    (hf : MemHolder β L f)
    -- USER-INPUT: `K` is a kernel of order `ℓ = holderIndex β`; classical bias-reduction
    -- condition (cf. Parzen 1962)
    (hK : IsKernelOfOrder K (holderIndex β))
    -- USER-INPUT: finite `β`-moment of the kernel; classical bias-bound input
    (hKβ : Integrable fun u => |u| ^ β * |K u|)
    {h : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h) (x₀ : ℝ) :
    |(∫ u, K u * f (x₀ + u * h)) - f x₀| ≤ kdeBiasConst β L K * h ^ β := by
  have hcomp : Integrable (fun u => K u * f (x₀ + u * h)) :=
    integrable_kernel_mul_holder hβ hL hf hK hKβ hh x₀
  have hpolyint : ∀ j ∈ Finset.range (holderIndex β + 1),
      Integrable (fun u => K u * (iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ))) := by
    intro j hj
    have hjℓ : j ≤ holderIndex β := Finset.mem_range_succ_iff.mp hj
    have h := (hK.integrable_pow j hjℓ).const_mul
      (iteratedDeriv j f x₀ * h ^ j / (Nat.factorial j : ℝ))
    refine h.congr (ae_of_all _ fun u => ?_)
    simp only [mul_pow]; ring
  have hInt_poly : Integrable (fun u => K u * ∑ j ∈ Finset.range (holderIndex β + 1),
      iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ)) := by
    have hfun : (fun u => K u * ∑ j ∈ Finset.range (holderIndex β + 1),
          iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ))
        = fun u => ∑ j ∈ Finset.range (holderIndex β + 1),
          K u * (iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ)) := by
      funext u; rw [Finset.mul_sum]
    rw [hfun]; exact integrable_finset_sum _ hpolyint
  have hKT : (∫ u, K u * ∑ j ∈ Finset.range (holderIndex β + 1),
      iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ)) = f x₀ := by
    have hfun : (fun u => K u * ∑ j ∈ Finset.range (holderIndex β + 1),
          iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ))
        = fun u => ∑ j ∈ Finset.range (holderIndex β + 1),
          K u * (iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ)) := by
      funext u; rw [Finset.mul_sum]
    rw [hfun, integral_finset_sum _ hpolyint]
    have hterm : ∀ j ∈ Finset.range (holderIndex β + 1),
        (∫ u, K u * (iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ)))
          = iteratedDeriv j f x₀ * h ^ j / (Nat.factorial j : ℝ) * (∫ u, u ^ j * K u) := by
      intro j _
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp only [mul_pow]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single (0 : ℕ)
      (fun j hj hj0 => by
        have hjℓ : j ≤ holderIndex β := Finset.mem_range_succ_iff.mp hj
        rw [hK.moment_eq_zero j (Nat.one_le_iff_ne_zero.mpr hj0) hjℓ, mul_zero])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h)]
    have hK1 : (∫ u, u ^ (0 : ℕ) * K u) = 1 := by
      simp only [pow_zero, one_mul]; exact hK.integral_eq_one
    rw [hK1]; simp [iteratedDeriv_zero]
  have key : (∫ u, K u * f (x₀ + u * h)) - f x₀
      = ∫ u, K u * (f (x₀ + u * h) - ∑ j ∈ Finset.range (holderIndex β + 1),
          iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ)) := by
    rw [← hKT, ← integral_sub hcomp hInt_poly]
    exact integral_congr_ae (ae_of_all _ fun u => (mul_sub _ _ _).symm)
  have habs_int : Integrable (fun u => K u * (f (x₀ + u * h)
      - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ))) := by
    refine (hcomp.sub hInt_poly).congr (ae_of_all _ fun u => ?_)
    exact (mul_sub _ _ _).symm
  have hmaj_eq : (fun u => |K u| * (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β))
      = fun u => (L / (Nat.factorial (holderIndex β) : ℝ) * h ^ β) * (|u| ^ β * |K u|) := by
    funext u
    rw [show |u * h| = |u| * h by rw [abs_mul, abs_of_pos hh],
        Real.mul_rpow (abs_nonneg u) hh.le]; ring
  have hmaj_int : Integrable
      (fun u => |K u| * (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β)) := by
    rw [hmaj_eq]; exact hKβ.const_mul _
  calc |(∫ u, K u * f (x₀ + u * h)) - f x₀|
      = ‖∫ u, K u * (f (x₀ + u * h) - ∑ j ∈ Finset.range (holderIndex β + 1),
          iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ))‖ := by
        rw [key, Real.norm_eq_abs]
    _ ≤ ∫ u, ‖K u * (f (x₀ + u * h) - ∑ j ∈ Finset.range (holderIndex β + 1),
          iteratedDeriv j f x₀ * (u * h) ^ j / (Nat.factorial j : ℝ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u, |K u| * (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β) := by
        refine integral_mono habs_int.norm hmaj_int (fun u => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hf.taylor_remainder_abs_le hβ hL x₀ (u * h)) (abs_nonneg _)
    _ = kdeBiasConst β L K * h ^ β := by
        rw [hmaj_eq, integral_const_mul, kdeBiasConst]; ring

/-- **Pointwise bias bound for the kernel density estimator**: for `p ∈ P(β, L)`, kernel of
order `ℓ = holderIndex β` with finite `β`-moment, `n ≥ 1` and `h > 0`:
`|b(x₀)| ≤ C₂·h^β` with `C₂ = kdeBiasConst β L K`. -/
theorem kde_bias_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ} {x₀ : ℝ}
    {β L : ℝ}
    -- USER-INPUT: positive smoothness, nonnegative Hölder constant; class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    -- LEAN-ONLY: nonempty sample; with `n = 0` the estimator degenerates to `0`
    (hn : 0 < n)
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- USER-INPUT: the density lies in the Hölder class `P(β, L)`
    (hp : IsHolderDensity β L p)
    -- USER-INPUT: `K` is a kernel of order `ℓ = holderIndex β`; classical bias-reduction
    -- condition (cf. Parzen 1962)
    (hK : IsKernelOfOrder K (holderIndex β))
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: finite `β`-moment of the kernel; classical bias-bound input
    (hKβ : Integrable fun u => |u| ^ β * |K u|) :
    |kdeBiasAt P X K h p x₀| ≤ kdeBiasConst β L K * h ^ β := by
  have h0 : ∀ x, 0 ≤ p x := hp.nonneg
  have hp_meas : Measurable p :=
    (contDiffOn_univ.mp (MemHolderOn.contDiffOn hp.holder)).continuous.measurable
  have hint : Integrable fun u => K u * p (x₀ + u * h) :=
    integrable_kernel_mul_holder hβ hL hp.holder hK hKβ hh x₀
  unfold kdeBiasAt
  rw [kdeMeanAt_eq_integral_kernel hn hh hs hp_meas h0 hKmeas hint]
  exact abs_integral_kernel_taylor_le hβ hL hp.holder hK hKβ hh x₀

end StatLean.NonparametricStatistics
