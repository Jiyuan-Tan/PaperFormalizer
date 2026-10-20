module
public import StatLean.NonparametricStatistics.KernelDensity.IntegratedVariance
public import StatLean.NonparametricStatistics.ForMathlib.MinkowskiIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Data.Real.Sqrt

@[expose] public section

/-!
# Exact asymptotics of the integrated variance

The two-sided refinement of the integrated variance bound: for a square-integrable density,
$$ \frac{1}{nh}\int K^2 - \frac{1}{n}\Bigl(\int |K|\Bigr)^2\!\!\int p^2
   \;\le\; \int \sigma^2(x)\,dx \;\le\; \frac{1}{nh}\int K^2 . $$
The correction term is `O(1/n)`, hence negligible against the main term `(nh)⁻¹∫K²` as
`h → 0` — this is the variance half of the exact asymptotic MISE.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.3, Proposition 1.6 (variance half of the
exact asymptotic MISE; proof in the Appendix, Proposition A.1).

**Proof formalization notes.** The exact identity is
`∫σ² = (nh²)⁻¹(h∫K² − ∫(E K((X−x)/h))² dx)`; the subtracted term is the squared `L²` norm of
the convolution-type mean, bounded by Young/Minkowski
(`‖|K|_h ⋆ p‖₂ ≤ ‖|K|_h‖₁·‖p‖₂ = ∫|K|·‖p‖₂`, via `lintegral_lintegral_sq_rpow_le`), giving
the correction `n⁻¹·(∫|K|)²·∫p²`. Requires `p ∈ L²` — supplied as a hypothesis
(`MemLp p 2`); see the batch ledger for its status (derivable in principle for the densities
of the exact-MISE theorem, kept as a documented input here).

**Bibliographic comments.** G. S. Watson and M. R. Leadbetter, "On the estimation of the
probability density, I," *Ann. Math. Statist.* **34** (1963), 480–491.
-/

set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- Helper: `(ENNReal.ofReal (u^2))^(1/2) = ENNReal.ofReal u` for `0 ≤ u`. -/
private lemma ofReal_sq_rpow_half_mv {u : ℝ} (hu : 0 ≤ u) :
    (ENNReal.ofReal (u ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal u := by
  rw [ENNReal.ofReal_pow hu, ← ENNReal.rpow_natCast (ENNReal.ofReal u) 2, ← ENNReal.rpow_mul]
  norm_num

/-- Integrability transfer along the law (replica of the `IntegratedVariance.lean` helper). -/
private lemma integrable_comp_law_mv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p g : ℝ → ℝ}
    (hX : HasLaw X (densityMeasure p) P) (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (hg : Measurable g) (hint : Integrable fun z => g z * p z) :
    Integrable (fun ω => g (X ω)) P := by
  have h2 : Integrable g (densityMeasure p) := by
    rw [densityMeasure, integrable_withDensity_iff hp.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    exact hint.congr (ae_of_all _ fun z => by simp only [ENNReal.toReal_ofReal (h0 z)])
  have h3 := integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable
  rw [hX.map_eq] at h3
  exact h3.mp h2

/-- Affine (reflect–scale) change of variables in the lower Lebesgue integral: for `h > 0`,
`∫⁻ x, F ((z − x)/h) dx = h · ∫⁻ y, F y dy`. -/
private lemma lintegral_kernel_shift_mv {F : ℝ → ℝ≥0∞} (hF : Measurable F) {h : ℝ} (hh : 0 < h)
    (z : ℝ) : ∫⁻ x, F ((z - x) / h) = ENNReal.ofReal h * ∫⁻ y, F y := by
  have hSmeas : Measurable (fun x : ℝ => (z - x) / h) :=
    (measurable_const.sub measurable_id).div_const h
  have hmap : Measure.map (fun x : ℝ => (z - x) / h) volume = ENNReal.ofReal h • volume := by
    have hcomp : (fun x : ℝ => (z - x) / h)
        = (fun y : ℝ => y + z / h) ∘ (fun x : ℝ => x * (-h⁻¹)) := by
      funext x; simp only [Function.comp_apply]; field_simp; ring
    rw [hcomp, ← Measure.map_map (show Measurable (fun y : ℝ => y + z / h) by fun_prop)
      (show Measurable (fun x : ℝ => x * (-h⁻¹)) by fun_prop),
      Real.map_volume_mul_right (neg_ne_zero.2 (inv_ne_zero hh.ne')),
      Measure.map_smul, map_add_right_eq_self]
    congr 1
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos hh]
  calc ∫⁻ x, F ((z - x) / h)
      = ∫⁻ y, F y ∂(Measure.map (fun x : ℝ => (z - x) / h) volume) :=
        (lintegral_map hF hSmeas).symm
    _ = ENNReal.ofReal h * ∫⁻ y, F y := by rw [hmap, lintegral_smul_measure, smul_eq_mul]

/-- Affine change of variables `z = x + u·h` on the whole line (`h > 0`). -/
private lemma integral_scale_shift_mv (F : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (∫ z, F z) = h * ∫ u, F (x + u * h) := by
  have hstep : (∫ u, F (x + u * h)) = |h⁻¹| • ∫ y, F (x + y) :=
    Measure.integral_comp_mul_right (fun y => F (x + y)) h
  rw [hstep, integral_add_left_eq_self F x, smul_eq_mul, abs_of_pos (inv_pos.2 hh),
    ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

/-- **Convolution `L²` (Young/Minkowski) bound**: for a square-integrable density and integrable
kernel, `∫ (∫ K(u)·p(x+uh) du)² dx ≤ (∫|K|)²·∫p²`. -/
private lemma conv_sq_lintegral_le_mv {p K : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (hp2 : MemLp p 2 volume)
    (hK : Measurable K) (hK1 : Integrable K) :
    (∫⁻ x, ENNReal.ofReal ((∫ u, K u * p (x + u * h)) ^ 2))
      ≤ ENNReal.ofReal ((∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2) := by
  set S2 : ℝ := ∫ x, (p x) ^ 2 with hS2def
  have hp2int : Integrable (fun x => (p x) ^ 2) := hp2.integrable_sq
  have hS2nn : (0 : ℝ) ≤ S2 := integral_nonneg fun x => sq_nonneg _
  set s : ℝ := Real.sqrt S2 with hsdef
  have hsnn : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hssq : s ^ 2 = S2 := Real.sq_sqrt hS2nn
  set g : ℝ → ℝ → ℝ≥0∞ := fun u x => ENNReal.ofReal (|K u| * p (x + u * h)) with hgdef
  have hg : Measurable (Function.uncurry g) := by
    have huc : Function.uncurry g
        = fun q : ℝ × ℝ => ENNReal.ofReal (|K q.1| * p (q.2 + q.1 * h)) := rfl
    rw [huc]
    exact ((Measurable.abs (hK.comp measurable_fst)).mul
      (hp.comp ((measurable_snd.add ((measurable_fst).mul_const h))))).ennreal_ofReal
  -- Pointwise: `ofReal((∫ K·p)²) ≤ (∫⁻ u, g u x)²`.
  have hpt : ∀ x, ENNReal.ofReal ((∫ u, K u * p (x + u * h)) ^ 2) ≤ (∫⁻ u, g u x) ^ 2 := by
    intro x
    have h1 : |∫ u, K u * p (x + u * h)| ≤ ∫ u, |K u| * p (x + u * h) := by
      calc |∫ u, K u * p (x + u * h)|
          ≤ ∫ u, |K u * p (x + u * h)| := abs_integral_le_integral_abs
        _ = ∫ u, |K u| * p (x + u * h) := by
            refine integral_congr_ae (ae_of_all _ fun u => ?_)
            simp only [abs_mul, abs_of_nonneg (h0 (x + u * h))]
    have hnn : (0 : ℝ) ≤ ∫ u, |K u| * p (x + u * h) :=
      integral_nonneg fun u => mul_nonneg (abs_nonneg _) (h0 _)
    have hle : ENNReal.ofReal (∫ u, |K u| * p (x + u * h)) ≤ ∫⁻ u, g u x := by
      by_cases hint : Integrable (fun u => |K u| * p (x + u * h))
      · rw [ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun u => mul_nonneg (abs_nonneg _) (h0 _))]
      · rw [integral_undef hint, ENNReal.ofReal_zero]; exact zero_le
    calc ENNReal.ofReal ((∫ u, K u * p (x + u * h)) ^ 2)
        = ENNReal.ofReal (|∫ u, K u * p (x + u * h)| ^ 2) := by rw [sq_abs]
      _ ≤ ENNReal.ofReal ((∫ u, |K u| * p (x + u * h)) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [abs_nonneg (∫ u, K u * p (x + u * h)), h1]
      _ = (ENNReal.ofReal (∫ u, |K u| * p (x + u * h))) ^ 2 := ENNReal.ofReal_pow hnn _
      _ ≤ (∫⁻ u, g u x) ^ 2 := by rw [sq, sq]; exact mul_le_mul' hle hle
  -- Per-`u` slice bound.
  have hslice : ∀ u, (∫⁻ x, (g u x) ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (|K u| * s) := by
    intro u
    have htrans : (∫⁻ x, ENNReal.ofReal ((p (x + u * h)) ^ 2))
        = ENNReal.ofReal S2 := by
      rw [show (∫⁻ x, ENNReal.ofReal ((p (x + u * h)) ^ 2))
            = ∫⁻ x, ENNReal.ofReal ((p x) ^ 2) from
          lintegral_add_right_eq_self (fun x => ENNReal.ofReal ((p x) ^ 2)) (u * h),
        hS2def, ofReal_integral_eq_lintegral_ofReal hp2int (ae_of_all _ fun x => sq_nonneg _)]
    have hconst : (∫⁻ x, (g u x) ^ 2) = ENNReal.ofReal (|K u| ^ 2) * ENNReal.ofReal S2 := by
      rw [← htrans, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      rw [hgdef, ← ENNReal.ofReal_pow (mul_nonneg (abs_nonneg _) (h0 _)), mul_pow,
        ENNReal.ofReal_mul (by positivity)]
    rw [hconst, ← ENNReal.ofReal_mul (by positivity),
      show |K u| ^ 2 * S2 = (|K u| * s) ^ 2 by rw [mul_pow, hssq],
      ofReal_sq_rpow_half_mv (by positivity)]
  -- Assemble.
  have hend : (∫⁻ u, (∫⁻ x, (g u x) ^ 2) ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal (s * ∫ u, |K u|) := by
    calc (∫⁻ u, (∫⁻ x, (g u x) ^ 2) ^ (1 / 2 : ℝ))
        ≤ ∫⁻ u, ENNReal.ofReal (|K u| * s) := lintegral_mono hslice
      _ = ∫⁻ u, ENNReal.ofReal s * ENNReal.ofReal (|K u|) := by
          refine lintegral_congr fun u => ?_
          rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
      _ = ENNReal.ofReal s * ∫⁻ u, ENNReal.ofReal (|K u|) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal s * ENNReal.ofReal (∫ u, |K u|) := by
          rw [ofReal_integral_eq_lintegral_ofReal hK1.abs (ae_of_all _ fun u => abs_nonneg _)]
      _ = ENNReal.ofReal (s * ∫ u, |K u|) := (ENNReal.ofReal_mul hsnn).symm
  have hmink := lintegral_lintegral_sq_rpow_le volume volume (g := g) hg
  have hAsq : (∫⁻ x, (∫⁻ u, g u x) ^ 2)
      = ((∫⁻ x, (∫⁻ u, g u x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ x, ENNReal.ofReal ((∫ u, K u * p (x + u * h)) ^ 2))
      ≤ ∫⁻ x, (∫⁻ u, g u x) ^ 2 := lintegral_mono hpt
    _ = ((∫⁻ x, (∫⁻ u, g u x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := hAsq
    _ ≤ (ENNReal.ofReal (s * ∫ u, |K u|)) ^ 2 := by
        rw [sq, sq]; exact mul_le_mul' (hmink.trans hend) (hmink.trans hend)
    _ = ENNReal.ofReal ((∫ u, |K u|) ^ 2 * S2) := by
        rw [← ENNReal.ofReal_pow (by positivity), mul_pow, hssq]; ring_nf

/-- **Integrated variance, exact lower bound**: for a square-integrable density,
`(nh)⁻¹∫K² − n⁻¹(∫|K|)²·∫p² ≤ ∫ σ²(x) dx`. Together with
`kde_integrated_variance_le` this pins the integrated variance to `(nh)⁻¹∫K²` up to `O(1/n)`. -/
theorem kde_integrated_variance_ge {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ}
    -- LEAN-ONLY: nonempty sample and positive bandwidth; standard side conditions
    (hn : 0 < n) (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    -- USER-INPUT: square-integrable density; input of the exact variance asymptotics
    -- (documented: derivable for the exact-MISE densities, kept as an input here)
    (hp2 : MemLp p 2 volume)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hK : Measurable K)
    -- USER-INPUT: integrable and square-integrable kernel; classical inputs
    (hK1 : Integrable K) (hK2 : Integrable fun u => (K u) ^ 2) :
    ENNReal.ofReal (((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2)
        - (n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2)
      ≤ ∫⁻ x, kdeVarianceAt P X K h x := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hh' : h ≠ 0 := hh.ne'
  set c : ℝ := ((n : ℝ) * h ^ 2)⁻¹ with hcdef
  have hcnn : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
  -- The density is a probability density.
  have hprob : IsProbabilityMeasure (densityMeasure p) := by
    rw [← (hs.law ⟨0, hn⟩).map_eq]
    exact Measure.isProbabilityMeasure_map (hs.law ⟨0, hn⟩).aemeasurable
  have hmass : (∫⁻ z, ENNReal.ofReal (p z)) = 1 := by
    have h := hprob.measure_univ
    rwa [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  have hp_int : Integrable p := by
    rw [← memLp_one_iff_integrable]
    refine ⟨hp.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm]
    rw [lintegral_congr fun z => by rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (h0 z)]]
    rw [hmass]; exact ENNReal.one_lt_top
  -- Real functions of `x`.
  set Amv : ℝ → ℝ := fun x => ∫ z, (K ((z - x) / h)) ^ 2 * p z with hAmvdef
  set meanℓ : ℝ → ℝ := fun x => ∫ z, K ((z - x) / h) * p z with hmeandef
  set GG : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal c
    * ∫⁻ z, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) with hGGdef
  -- Joint measurability for the `A`-term kernel.
  have hΦmeas : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal ((K ((q.2 - q.1) / h)) ^ 2) * ENNReal.ofReal (p q.2)) :=
    (((hK.comp ((measurable_snd.sub measurable_fst).div_const h)).pow_const 2).ennreal_ofReal).mul
      ((hp.comp measurable_snd).ennreal_ofReal)
  have hGℓmeas : Measurable fun x => ∫⁻ z,
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) :=
    hΦmeas.lintegral_prod_right'
  have hGGmeas : Measurable GG := by rw [hGGdef]; exact measurable_const.mul hGℓmeas
  -- The total `A`-double integral: `∫∫ = h·∫K²`.
  have hD : (∫⁻ x, ∫⁻ z, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z))
      = ENNReal.ofReal h * ENNReal.ofReal (∫ u, (K u) ^ 2) := by
    rw [lintegral_lintegral_swap (f := fun x z =>
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z)) hΦmeas.aemeasurable]
    have hinner : ∀ z, (∫⁻ x, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z))
        = ENNReal.ofReal h * ENNReal.ofReal (∫ u, (K u) ^ 2) * ENNReal.ofReal (p z) := by
      intro z
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      congr 1
      rw [lintegral_kernel_shift_mv ((hK.pow_const 2).ennreal_ofReal) hh z]
      congr 1
      exact (ofReal_integral_eq_lintegral_ofReal hK2 (ae_of_all _ fun u => sq_nonneg _)).symm
    rw [lintegral_congr hinner,
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      hmass, mul_one]
  have hGℓfin : ∀ᵐ x, (∫⁻ z,
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z)) < ⊤ := by
    refine ae_lt_top hGℓmeas ?_
    rw [hD]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- `∫⁻ GG = ofReal((nh)⁻¹∫K²)`.
  have hGGval : (∫⁻ x, GG x) = ENNReal.ofReal (((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2) := by
    have harg : c * h * ∫ u, (K u) ^ 2 = ((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2 := by
      rw [hcdef]; field_simp
    simp only [hGGdef]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hD, ← mul_assoc,
      ← ENNReal.ofReal_mul hcnn, ← ENNReal.ofReal_mul (mul_nonneg hcnn hh.le), harg]
  -- Measurability of `x ↦ kdeVarianceAt`.
  have hjkde : Measurable (fun q : ℝ × Ω => kde X K h q.2 q.1) := by
    simp only [kde, kdeData]
    refine measurable_const.mul (Finset.measurable_sum _ (fun i _ => ?_))
    exact hK.comp (((hX i).comp measurable_snd).sub measurable_fst |>.div_const h)
  have hmeanAtmeas : Measurable (fun x => kdeMeanAt P X K h x) := by
    have := (hjkde.stronglyMeasurable).integral_prod_right' (ν := P)
    exact this.measurable
  have hVarMeas : Measurable (fun x => kdeVarianceAt P X K h x) := by
    have hφ : Measurable (fun q : ℝ × Ω =>
        ENNReal.ofReal ((kde X K h q.2 q.1 - kdeMeanAt P X K h q.1) ^ 2)) :=
      (((hjkde.sub (hmeanAtmeas.comp measurable_fst)).pow_const 2)).ennreal_ofReal
    exact hφ.lintegral_prod_right'
  -- Measurability of the `B`-term.
  have hmeanℓmeas : Measurable meanℓ := by
    have hker : Measurable (fun q : ℝ × ℝ => K ((q.2 - q.1) / h) * p q.2) :=
      (hK.comp ((measurable_snd.sub measurable_fst).div_const h)).mul (hp.comp measurable_snd)
    have := (hker.stronglyMeasurable).integral_prod_right' (ν := volume)
    exact this.measurable
  have hBMeas : Measurable (fun x => ENNReal.ofReal (c * (meanℓ x) ^ 2)) :=
    (measurable_const.mul (hmeanℓmeas.pow_const 2)).ennreal_ofReal
  -- The a.e.-`x` additive identity: `kdeVar x + ofReal(c·(meanℓ x)²) = GG x`.
  have hae_add : ∀ᵐ x, kdeVarianceAt P X K h x + ENNReal.ofReal (c * (meanℓ x) ^ 2) = GG x := by
    filter_upwards [hGℓfin] with x hx
    have hGmeas : Measurable (fun z => (K ((z - x) / h)) ^ 2) :=
      (hK.comp ((measurable_id.sub_const x).div_const h)).pow_const 2
    have hkmeas : Measurable (fun z => K ((z - x) / h)) :=
      hK.comp ((measurable_id.sub_const x).div_const h)
    have hnn : 0 ≤ᵐ[volume] fun z => (K ((z - x) / h)) ^ 2 * p z :=
      ae_of_all _ fun z => mul_nonneg (sq_nonneg _) (h0 z)
    -- Integrability of `K²·p` from finiteness of the second-moment kernel.
    have hIntGp : Integrable (fun z => (K ((z - x) / h)) ^ 2 * p z) volume := by
      refine ⟨(hGmeas.mul hp).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnn]
      have hcongr : (fun z => ENNReal.ofReal ((K ((z - x) / h)) ^ 2 * p z))
          = fun z => ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) := by
        funext z; rw [ENNReal.ofReal_mul (sq_nonneg _)]
      rw [hcongr]; exact hx
    -- Integrability of `K·p` by domination `|K|·p ≤ (K²·p + p)/2`.
    have hIntKp : Integrable (fun z => K ((z - x) / h) * p z) volume := by
      have hdom : Integrable (fun z => ((K ((z - x) / h)) ^ 2 * p z + p z) / 2) volume :=
        (hIntGp.add hp_int).div_const 2
      refine Integrable.mono' hdom (hkmeas.mul hp).aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 z)]
      have hle : |K ((z - x) / h)| ≤ ((K ((z - x) / h)) ^ 2 + 1) / 2 := by
        nlinarith [sq_nonneg (|K ((z - x) / h)| - 1), sq_abs (K ((z - x) / h))]
      nlinarith [h0 z, hle, abs_nonneg (K ((z - x) / h))]
    -- Each summand is `L²`.
    have hmemP : ∀ i, MemLp (fun ω => K ((X i ω - x) / h)) 2 P := by
      intro i
      have haesm : AEStronglyMeasurable (fun ω => K ((X i ω - x) / h)) P :=
        (hK.comp (((hX i).sub_const x).div_const h)).aestronglyMeasurable
      rw [memLp_two_iff_integrable_sq haesm]
      exact integrable_comp_law_mv (g := fun z => (K ((z - x) / h)) ^ 2)
        (hs.law i) hp h0 hGmeas hIntGp
    have hEsq : ∀ i, ∫ ω, (K ((X i ω - x) / h)) ^ 2 ∂P = Amv x :=
      fun i => integral_comp_law_densityMeasure (g := fun z => (K ((z - x) / h)) ^ 2)
        (hs.law i) hp h0 hGmeas hIntGp
    have hEmean : ∀ i, ∫ ω, K ((X i ω - x) / h) ∂P = meanℓ x :=
      fun i => integral_comp_law_densityMeasure (g := fun z => K ((z - x) / h))
        (hs.law i) hp h0 hkmeas hIntKp
    -- Variance of the estimator: `c·(Amv x − (meanℓ x)²)`.
    have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)))
        (fun i j => (fun ω => K ((X i ω - x) / h)) ⟂ᵢ[P] (fun ω => K ((X j ω - x) / h))) := by
      intro i _ j _ hij
      exact (hs.indep.indepFun hij).comp (hK.comp ((measurable_id.sub_const x).div_const h))
        (hK.comp ((measurable_id.sub_const x).div_const h))
    have hvarsum : variance (fun ω => ∑ i, K ((X i ω - x) / h)) P
        = ∑ i, variance (fun ω => K ((X i ω - x) / h)) P := by
      rw [show (fun ω => ∑ i, K ((X i ω - x) / h))
          = ∑ i : Fin n, (fun ω => K ((X i ω - x) / h)) from by
            funext ω; simp only [Finset.sum_apply]]
      exact IndepFun.variance_sum (fun i _ => hmemP i) hpair
    have hvarterm : ∀ i, variance (fun ω => K ((X i ω - x) / h)) P = Amv x - (meanℓ x) ^ 2 := by
      intro i
      rw [variance_eq_sub (hmemP i)]
      congr 1
      · rw [← hEsq i]; rfl
      · rw [hEmean i]
    have hvarsum2 : variance (fun ω => ∑ i, K ((X i ω - x) / h)) P
        = (n : ℝ) * (Amv x - (meanℓ x) ^ 2) := by
      rw [hvarsum, Finset.sum_congr rfl (fun i _ => hvarterm i), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hL2 : MemLp (fun ω => kde X K h ω x) 2 P := by
      have hfun : (∑ i : Fin n, fun ω => K ((X i ω - x) / h))
          = fun ω => ∑ i, K ((X i ω - x) / h) := by funext ω; simp only [Finset.sum_apply]
      have hsum : MemLp (fun ω => ∑ i, K ((X i ω - x) / h)) 2 P := by
        rw [← hfun]; exact memLp_finset_sum' _ (fun i _ => hmemP i)
      exact hsum.const_mul ((n : ℝ) * h)⁻¹
    have hvar : variance (fun ω => kde X K h ω x) P = c * (Amv x - (meanℓ x) ^ 2) := by
      have hrfl : (fun ω => kde X K h ω x)
          = fun ω => ((n : ℝ) * h)⁻¹ * ∑ i, K ((X i ω - x) / h) := rfl
      have halg : (((n : ℝ) * h)⁻¹) ^ 2 * ((n : ℝ) * (Amv x - (meanℓ x) ^ 2))
          = c * (Amv x - (meanℓ x) ^ 2) := by rw [hcdef]; field_simp
      rw [hrfl, variance_const_mul, hvarsum2, halg]
    -- Nonnegativity of `Amv x − (meanℓ x)²` (variance ≥ 0).
    have hABnn : (0 : ℝ) ≤ c * (Amv x - (meanℓ x) ^ 2) := hvar ▸ variance_nonneg _ _
    -- `kdeVar x = ofReal(variance)`, `GG x = ofReal(c·Amv x)`.
    have hVarEq : kdeVarianceAt P X K h x = ENNReal.ofReal (c * (Amv x - (meanℓ x) ^ 2)) := by
      rw [kdeVarianceAt_eq_ofReal_variance hL2, hvar]
    have hGGx : GG x = ENNReal.ofReal (c * Amv x) := by
      have hAeq : (∫⁻ z, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z))
          = ENNReal.ofReal (Amv x) := by
        simp only [hAmvdef]
        rw [ofReal_integral_eq_lintegral_ofReal hIntGp hnn]
        exact lintegral_congr fun z => by rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      simp only [hGGdef]
      rw [hAeq, ← ENNReal.ofReal_mul hcnn]
    rw [hVarEq, hGGx, ← ENNReal.ofReal_add hABnn (by positivity)]
    congr 1; ring
  -- The `B`-integral bound.
  have hBbound : (∫⁻ x, ENNReal.ofReal (c * (meanℓ x) ^ 2))
      ≤ ENNReal.ofReal ((n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2) := by
    have hmeanℓ_eq : ∀ x, meanℓ x = h * ∫ u, K u * p (x + u * h) := by
      intro x
      simp only [hmeandef]
      rw [integral_scale_shift_mv (fun z => K ((z - x) / h) * p z) hh x]
      refine congrArg (h * ·) (integral_congr_ae (ae_of_all _ fun u => ?_))
      simp only [add_sub_cancel_left, mul_div_cancel_right₀ _ hh']
    have hBrw : (∫⁻ x, ENNReal.ofReal (c * (meanℓ x) ^ 2))
        = ENNReal.ofReal (c * h ^ 2)
          * ∫⁻ x, ENNReal.ofReal ((∫ u, K u * p (x + u * h)) ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      rw [hmeanℓ_eq x, mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [hBrw]
    calc ENNReal.ofReal (c * h ^ 2)
          * ∫⁻ x, ENNReal.ofReal ((∫ u, K u * p (x + u * h)) ^ 2)
        ≤ ENNReal.ofReal (c * h ^ 2)
            * ENNReal.ofReal ((∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2) :=
          mul_le_mul_right (conv_sq_lintegral_le_mv hh hp h0 hp2 hK hK1) _
      _ = ENNReal.ofReal ((n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          have halg2 : c * h ^ 2 * ((∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2)
              = (n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2 := by
            rw [hcdef]; field_simp
          rw [halg2]
  -- Assemble: `∫⁻ kdeVar = ∫⁻ GG − ∫⁻ ofReal(c·(meanℓ)²) ≥ RHS`.
  have hsplit : (∫⁻ x, kdeVarianceAt P X K h x) + (∫⁻ x, ENNReal.ofReal (c * (meanℓ x) ^ 2))
      = ∫⁻ x, GG x := by
    rw [← lintegral_add_left hVarMeas]
    exact lintegral_congr_ae hae_add
  have hVarEq : (∫⁻ x, kdeVarianceAt P X K h x)
      = (∫⁻ x, GG x) - (∫⁻ x, ENNReal.ofReal (c * (meanℓ x) ^ 2)) :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBbound) hsplit
  rw [hVarEq, hGGval,
    show ENNReal.ofReal (((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2)
        - (n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2)
      = ENNReal.ofReal (((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2)
        - ENNReal.ofReal ((n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2) from by
      rw [ENNReal.ofReal_sub _ (by positivity)]]
  exact tsub_le_tsub_left hBbound _

end StatLean.NonparametricStatistics
