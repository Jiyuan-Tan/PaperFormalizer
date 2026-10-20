module
public import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
public import StatLean.NonparametricStatistics.SmoothnessClasses.NikolskiTaylor
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Order.Group.Lattice

@[expose] public section

/-!
# Integrated squared bias of the kernel density estimator

For a density in the Nikol'skii class `P_H(β, L)` and a kernel of order `ℓ = holderIndex β`
with finite `β`-moment:
$$ \int b^2(x)\,dx \;\le\; C_2^2\,h^{2\beta}, \qquad
   C_2 = \frac{L}{\ell!}\int|u|^{\beta}|K(u)|\,du $$
— the same constant as the pointwise bias bound, now in integrated form.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.3, Proposition 1.5 (integrated squared bias
bound $C_2^2 h^{2\beta}$ over $\mathcal{P}_H(\beta, L)$).

**Proof formalization notes.** For a.e. `x` (Tonelli gives `∫∫|K(u)|·p(x+uh)·du·dx =
∫|K| < ∞`, hence a.e.-`x` integrability), the bias equals
`∫K(u)·(p(x+uh) − ∑_{j≤ℓ} p⁽ʲ⁾(x)(uh)ʲ/j!)du` after moment cancellation. The `L²(dx)`-norm is
pulled inside the `u`-integral by the generalized Minkowski inequality
(`lintegral_lintegral_sq_rpow_le`), and each slice is bounded by the Nikol'skii–Taylor
remainder bound (`MemNikolski.lintegral_sq_remainder_le`), giving
`‖b‖₂ ≤ ∫|K(u)|·(L/ℓ!)|uh|^β du = C₂·h^β`. On the junk set of `x` where the Bochner mean is
`0`, the lower Lebesgue integral is unaffected (null set). Everything stays in `∫⁻`.

**Bibliographic comments.** The Nikol'skii-class integrated bias computation is the classical
route to MISE rates; cf. S. M. Nikol'skii, *Approximation of Functions of Several Variables
and Imbedding Theorems* (Springer, 1975) for the class, and G. S. Watson and
M. R. Leadbetter, *Ann. Math. Statist.* **34** (1963), 480–491, for the `L²` analysis.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- Helper: `(ENNReal.ofReal (u^2))^(1/2) = ENNReal.ofReal u` for `0 ≤ u`. -/
private lemma ofReal_sq_rpow_half_ib {u : ℝ} (hu : 0 ≤ u) :
    (ENNReal.ofReal (u ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal u := by
  rw [ENNReal.ofReal_pow hu, ← ENNReal.rpow_natCast (ENNReal.ofReal u) 2, ← ENNReal.rpow_mul]
  norm_num

/-- The Taylor polynomial of `p` at `x` (order `ℓ`, evaluated for shift `u·h`) integrates
against a kernel of order `ℓ` to the value `p x` (moment cancellation). -/
private lemma integral_kernel_taylor_self {K p : ℝ → ℝ} {ℓ : ℕ} {h : ℝ}
    (hK : IsKernelOfOrder K ℓ) (x : ℝ) :
    ∫ u, K u * ∑ j ∈ Finset.range (ℓ + 1),
        iteratedDeriv j p x * (u * h) ^ j / (Nat.factorial j : ℝ) = p x := by
  have hterm_eq : (fun u => K u * ∑ j ∈ Finset.range (ℓ + 1),
        iteratedDeriv j p x * (u * h) ^ j / (Nat.factorial j : ℝ))
      = fun u => ∑ j ∈ Finset.range (ℓ + 1),
        iteratedDeriv j p x * h ^ j / (Nat.factorial j : ℝ) * (u ^ j * K u) := by
    funext u
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  rw [hterm_eq, integral_finset_sum _ (fun j hj =>
    (hK.integrable_pow j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).const_mul _)]
  rw [Finset.sum_eq_single 0]
  · rw [integral_const_mul, iteratedDeriv_zero, pow_zero, mul_one, Nat.factorial_zero,
      Nat.cast_one, div_one]
    simp only [pow_zero, one_mul]
    rw [hK.integral_eq_one, mul_one]
  · intro j hj hjne
    rw [integral_const_mul, hK.moment_eq_zero j (Nat.one_le_iff_ne_zero.mpr hjne)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), mul_zero]
  · intro hnotmem
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos ℓ)) hnotmem

/-- The kernel-weighted Taylor polynomial `u ↦ K u · T_x(u)` is integrable. -/
private lemma integrable_kernel_taylor_poly {K p : ℝ → ℝ} {ℓ : ℕ} {h : ℝ}
    (hK : IsKernelOfOrder K ℓ) (x : ℝ) :
    Integrable (fun u => K u * ∑ j ∈ Finset.range (ℓ + 1),
        iteratedDeriv j p x * (u * h) ^ j / (Nat.factorial j : ℝ)) := by
  have hterm_eq : (fun u => K u * ∑ j ∈ Finset.range (ℓ + 1),
        iteratedDeriv j p x * (u * h) ^ j / (Nat.factorial j : ℝ))
      = fun u => ∑ j ∈ Finset.range (ℓ + 1),
        iteratedDeriv j p x * h ^ j / (Nat.factorial j : ℝ) * (u ^ j * K u) := by
    funext u
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  rw [hterm_eq]
  exact integrable_finset_sum _ (fun j hj =>
    (hK.integrable_pow j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).const_mul _)

/-- **Integrated squared bias bound**: for `p ∈ P_H(β, L)`, kernel of order
`ℓ = holderIndex β` with finite `β`-moment, `n ≥ 1`, `h > 0`:
`∫ b²(x) dx ≤ C₂²·h^{2β}` with `C₂ = kdeBiasConst β L K`. -/
theorem kde_integrated_sq_bias_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ} {β L : ℝ}
    -- USER-INPUT: positive smoothness, nonnegative constant; class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    -- LEAN-ONLY: nonempty sample; with `n = 0` the estimator degenerates
    (hn : 0 < n)
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: the density lies in the Nikol'skii class `P_H(β, L)`
    (hp : IsNikolskiDensity β L p)
    -- USER-INPUT: `K` is a kernel of order `ℓ = holderIndex β`; classical bias-reduction
    -- condition
    (hK : IsKernelOfOrder K (holderIndex β))
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: finite `β`-moment of the kernel; classical bias-bound input
    (hKβ : Integrable fun u => |u| ^ β * |K u|) :
    (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
      ≤ ENNReal.ofReal ((kdeBiasConst β L K) ^ 2 * h ^ (2 * β)) := by
  classical
  -- Regularity of the density.
  have hp_cont : Continuous p := hp.nikolski.contDiff.continuous
  have hp_meas : Measurable p := hp_cont.measurable
  have hhb : (0 : ℝ) ≤ h ^ β := Real.rpow_nonneg hh.le β
  -- `p` is integrable and its `∫⁻` mass is one.
  have hp_int : Integrable p := by
    by_contra hni
    have h1 := hp.integral_one
    rw [integral_undef hni] at h1
    exact one_ne_zero h1.symm
  have hmass : (∫⁻ z, ENNReal.ofReal (p z)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hp_int (ae_of_all _ hp.nonneg), hp.integral_one,
      ENNReal.ofReal_one]
  -- `K` is integrable (order-0 moment).
  have hK_int : Integrable K := by
    have := hK.integrable_pow 0 (Nat.zero_le _)
    simpa using this
  have hKabs_int : Integrable (fun u => |K u|) := hK_int.abs
  -- Abbreviations for the Taylor polynomial `T` and remainder `R`.
  set T : ℝ → ℝ → ℝ := fun x u => ∑ j ∈ Finset.range (holderIndex β + 1),
    iteratedDeriv j p x * (u * h) ^ j / (Nat.factorial j : ℝ) with hTdef
  set R : ℝ → ℝ → ℝ := fun x u => p (x + u * h) - T x u with hRdef
  set g : ℝ → ℝ → ℝ≥0∞ := fun u x => ENNReal.ofReal (|K u| * |R x u|) with hgdef
  -- Joint continuity/measurability of the remainder.
  have hRcont : Continuous (fun q : ℝ × ℝ => R q.2 q.1) := by
    simp only [hRdef, hTdef]
    refine (hp_cont.comp (by fun_prop)).sub (continuous_finset_sum _ (fun j hj => ?_))
    have hcj : Continuous (iteratedDeriv j p) :=
      hp.nikolski.contDiff.continuous_iteratedDeriv j
        (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    exact ((hcj.comp continuous_snd).mul (by fun_prop)).div_const _
  have hg : Measurable (Function.uncurry g) := by
    have huc : Function.uncurry g
        = fun q : ℝ × ℝ => ENNReal.ofReal (|K q.1| * |R q.2 q.1|) := rfl
    rw [huc]
    exact ((Measurable.abs (hKmeas.comp measurable_fst)).mul
      hRcont.measurable.abs).ennreal_ofReal
  -- Joint measurability for the a.e.-`x` integrability Tonelli argument.
  have hfmeas : Measurable (Function.uncurry
      (fun x u => ENNReal.ofReal (|K u| * p (x + u * h)))) := by
    have huc : Function.uncurry (fun x u => ENNReal.ofReal (|K u| * p (x + u * h)))
        = fun q : ℝ × ℝ => ENNReal.ofReal (|K q.2| * p (q.1 + q.2 * h)) := rfl
    rw [huc]
    exact ((Measurable.abs (hKmeas.comp measurable_snd)).mul
      (hp_meas.comp (by fun_prop))).ennreal_ofReal
  -- Total double integral controlling a.e.-`x` integrability of `u ↦ K u · p(x+uh)`.
  have hDbias : (∫⁻ x, ∫⁻ u, ENNReal.ofReal (|K u| * p (x + u * h)))
      = ENNReal.ofReal (∫ u, |K u|) := by
    rw [lintegral_lintegral_swap (f := fun x u => ENNReal.ofReal (|K u| * p (x + u * h)))
      hfmeas.aemeasurable]
    have hinner : ∀ u, (∫⁻ x, ENNReal.ofReal (|K u| * p (x + u * h)))
        = ENNReal.ofReal (|K u|) := by
      intro u
      rw [lintegral_congr (fun x => ENNReal.ofReal_mul (abs_nonneg _)),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        show (∫⁻ x, ENNReal.ofReal (p (x + u * h))) = ∫⁻ x, ENNReal.ofReal (p x) from
          lintegral_add_right_eq_self (fun x => ENNReal.ofReal (p x)) (u * h),
        hmass, mul_one]
    rw [lintegral_congr hinner]
    exact (ofReal_integral_eq_lintegral_ofReal hKabs_int (ae_of_all _ fun u => abs_nonneg _)).symm
  have haex : ∀ᵐ x, (∫⁻ u, ENNReal.ofReal (|K u| * p (x + u * h))) < ⊤ := by
    refine ae_lt_top hfmeas.lintegral_prod_right' ?_
    rw [hDbias]; exact ENNReal.ofReal_ne_top
  -- The a.e.-`x` bias identity: bias equals the kernel-weighted Taylor remainder.
  have hbias_ae : ∀ᵐ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2)
      = ENNReal.ofReal ((∫ u, K u * R x u) ^ 2) := by
    filter_upwards [haex] with x hx
    have hKp : Integrable (fun u => K u * p (x + u * h)) := by
      refine ⟨(hKmeas.mul (hp_meas.comp (by fun_prop))).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      rw [lintegral_congr fun u => by
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hp.nonneg _)]]
      exact hx
    have hmean : kdeMeanAt P X K h x = ∫ u, K u * p (x + u * h) :=
      kdeMeanAt_eq_integral_kernel hn hh hs hp_meas hp.nonneg hKmeas hKp
    have hcancel : (∫ u, K u * T x u) = p x := integral_kernel_taylor_self hK x
    have hKT : Integrable (fun u => K u * T x u) := integrable_kernel_taylor_poly hK x
    have hbias : kdeBiasAt P X K h p x = ∫ u, K u * R x u := by
      have hb : kdeBiasAt P X K h p x = kdeMeanAt P X K h x - p x := rfl
      rw [hb, hmean, ← hcancel, ← integral_sub hKp hKT]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp only [hRdef]; ring
    rw [hbias]
  rw [lintegral_congr_ae hbias_ae]
  -- Pointwise: `ofReal((∫ K·R)²) ≤ (∫⁻ u, g u x)²`.
  have hpt : ∀ x, ENNReal.ofReal ((∫ u, K u * R x u) ^ 2) ≤ (∫⁻ u, g u x) ^ 2 := by
    intro x
    have h1 : |∫ u, K u * R x u| ≤ ∫ u, |K u| * |R x u| := by
      have hn := norm_integral_le_integral_norm (μ := volume) (fun u => K u * R x u)
      simp only [Real.norm_eq_abs, abs_mul] at hn
      exact hn
    have hnn : (0 : ℝ) ≤ ∫ u, |K u| * |R x u| := integral_nonneg fun u => by positivity
    calc ENNReal.ofReal ((∫ u, K u * R x u) ^ 2)
        = ENNReal.ofReal (|∫ u, K u * R x u| ^ 2) := by rw [sq_abs]
      _ ≤ ENNReal.ofReal ((∫ u, |K u| * |R x u|) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [abs_nonneg (∫ u, K u * R x u), h1]
      _ = (ENNReal.ofReal (∫ u, |K u| * |R x u|)) ^ 2 := ENNReal.ofReal_pow hnn _
      _ ≤ (∫⁻ u, g u x) ^ 2 := by
          have hle : ENNReal.ofReal (∫ u, |K u| * |R x u|) ≤ ∫⁻ u, g u x := by
            by_cases hint : Integrable (fun u => |K u| * |R x u|)
            · rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun u => by positivity)]
            · rw [integral_undef hint, ENNReal.ofReal_zero]; exact zero_le
          rw [sq, sq]; exact mul_le_mul' hle hle
  -- Generalized Minkowski (squared form).
  have hmink : (∫⁻ x, (∫⁻ u, g u x) ^ 2)
      ≤ (∫⁻ u, (∫⁻ x, (g u x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
    have hle := lintegral_lintegral_sq_rpow_le volume volume (g := g) hg
    have hAeq : (∫⁻ x, (∫⁻ u, g u x) ^ 2)
        = ((∫⁻ x, (∫⁻ u, g u x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]; norm_num
    rw [hAeq, sq, sq]; exact mul_le_mul' hle hle
  -- Per-`u` slice bound from the Nikol'skii–Taylor remainder.
  have hslice : ∀ u, (∫⁻ x, (g u x) ^ 2) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (|K u|
        * (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β)) := by
    intro u
    have hR : (∫⁻ x, ENNReal.ofReal ((R x u) ^ 2))
        ≤ ENNReal.ofReal ((L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β) ^ 2) :=
      MemNikolski.lintegral_sq_remainder_le hβ hL hp.nikolski (u * h)
    have hconst : (∫⁻ x, (g u x) ^ 2)
        = ENNReal.ofReal (|K u| ^ 2) * ∫⁻ x, ENNReal.ofReal ((R x u) ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      simp only [hgdef]
      rw [← ENNReal.ofReal_pow (by positivity), mul_pow, ENNReal.ofReal_mul (by positivity),
        sq_abs (R x u)]
    rw [hconst]
    have hLnn : (0 : ℝ) ≤ L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β :=
      mul_nonneg (div_nonneg hL (by positivity)) (Real.rpow_nonneg (abs_nonneg _) _)
    calc (ENNReal.ofReal (|K u| ^ 2) * ∫⁻ x, ENNReal.ofReal ((R x u) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (|K u| ^ 2)
            * ENNReal.ofReal ((L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β) ^ 2))
              ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (mul_le_mul_right hR _) (by norm_num)
      _ = ENNReal.ofReal (|K u|)
            * ENNReal.ofReal (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ofReal_sq_rpow_half_ib (abs_nonneg _),
            ofReal_sq_rpow_half_ib hLnn]
      _ = ENNReal.ofReal (|K u|
            * (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β)) :=
          (ENNReal.ofReal_mul (abs_nonneg _)).symm
  -- The outer `u`-integral equals `ofReal(C₂ · h^β)`.
  have hintegral_eq : (∫⁻ u, ENNReal.ofReal (|K u|
        * (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β)))
      = ENNReal.ofReal (kdeBiasConst β L K * h ^ β) := by
    have hpre : ∀ u, |K u| * (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β)
        = L / (Nat.factorial (holderIndex β) : ℝ) * h ^ β * (|u| ^ β * |K u|) := by
      intro u
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_of_pos hh]; ring
    rw [lintegral_congr fun u => by
      rw [hpre u, ENNReal.ofReal_mul (mul_nonneg (div_nonneg hL (by positivity)) hhb)],
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hKβ (ae_of_all _ fun u => by positivity),
      ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hL (by positivity)) hhb)]
    congr 1
    rw [kdeBiasConst]; ring
  -- Nonnegativity of the constant and the power identity.
  have hCh0 : (0 : ℝ) ≤ kdeBiasConst β L K * h ^ β := by
    refine mul_nonneg ?_ hhb
    rw [kdeBiasConst]
    exact mul_nonneg (div_nonneg hL (by positivity)) (integral_nonneg fun u => by positivity)
  have hpow : (h ^ β) ^ 2 = h ^ (2 * β) := by
    rw [← Real.rpow_natCast (h ^ β) 2, ← Real.rpow_mul hh.le]
    congr 1; push_cast; ring
  -- Assemble.
  calc ∫⁻ x, ENNReal.ofReal ((∫ u, K u * R x u) ^ 2)
      ≤ ∫⁻ x, (∫⁻ u, g u x) ^ 2 := lintegral_mono hpt
    _ ≤ (∫⁻ u, (∫⁻ x, (g u x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := hmink
    _ ≤ (∫⁻ u, ENNReal.ofReal (|K u|
          * (L / (Nat.factorial (holderIndex β) : ℝ) * |u * h| ^ β))) ^ 2 := by
        rw [sq, sq]; exact mul_le_mul' (lintegral_mono hslice) (lintegral_mono hslice)
    _ = ENNReal.ofReal (kdeBiasConst β L K * h ^ β) ^ 2 := by rw [hintegral_eq]
    _ = ENNReal.ofReal ((kdeBiasConst β L K) ^ 2 * h ^ (2 * β)) := by
        rw [← ENNReal.ofReal_pow hCh0, mul_pow, hpow]

end StatLean.NonparametricStatistics
