module
public import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
public import StatLean.NonparametricStatistics.ForMathlib.MinkowskiIntegral
public import StatLean.NonparametricStatistics.ForMathlib.TranslationL2
public import StatLean.NonparametricStatistics.SmoothnessClasses.NikolskiTaylor
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Group.LIntegral

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Exact asymptotics of the integrated squared bias

For a differentiable density whose derivative is absolutely continuous with square-integrable
a.e. second derivative `w`, and a kernel of order `1` with finite second moment:
$$ \Bigl|\ \int b^2(x)\,dx \;-\; \frac{h^4}{4}\,S_K^2 \int w^2 \ \Bigr| \;\le\; \varepsilon\,h^4
   \qquad (0 < h < h_0(\varepsilon)),\qquad S_K = \int u^2 K(u)\,du. $$
This is the bias half of the exact asymptotic MISE: as `h → 0`, `∫b² ~ (h⁴/4)·S_K²·∫w²`.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.3, Proposition 1.6 (bias half of the exact
asymptotic MISE; proof in the Appendix, Proposition A.1).

**Proof formalization notes.** From the order-`2` integral remainder (with `ℓ = 2` playing the
role of `holderIndex` at `β = 2`),
`b(x) = h²∫u²K(u)∫₀¹(1−τ)·w(x+τuh) dτ du` (a.e. `x`); compare with the constant-`w` surrogate
`h²·(S_K/2)·w(x)` whose squared `L²` norm is exactly `(h⁴/4)S_K²∫w²`. The difference is
controlled by two generalized Minkowski applications and the `L²`-continuity of translation
(`tendsto_lintegral_sq_sub_translate`) applied to `w`, with a split of the `u`-integral at
`|u| ≤ h^{-1/2}` and the envelope `u²|K(u)|` for the far range. This is the analytically
hardest step of the exact MISE; the split thresholds and the `ε`-bookkeeping follow the
classical appendix computation.

The absolute continuity of `p'` is encoded by the explicit a.e.-derivative witness
`w` with `deriv p b − deriv p a = ∫_a^b w` — the honest rendering of "`p'` absolutely
continuous with `p'' = w ∈ L²`".

**Bibliographic comments.** The exact MISE expansion is due to G. S. Watson and
M. R. Leadbetter, *Ann. Math. Statist.* **34** (1963), 480–491; the second-order form with
the `(h⁴/4)S_K²∫(p'')²` bias constant is the classical optimal-bandwidth computation of
M. S. Bartlett, *Sankhyā Ser. A* **25** (1963), 245–254, and V. A. Epanechnikov, *Theory
Probab. Appl.* **14** (1969), 153–158.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- Local integrability of `w` on every bounded interval, from `MemLp w 2` via the domination
`|w| ≤ (w² + 1)/2`. -/
private lemma intervalIntegrable_of_memLp_two {w : ℝ → ℝ} (hw_meas : Measurable w)
    (hw2 : MemLp w 2 volume) (a b : ℝ) : IntervalIntegrable w volume a b := by
  have hsq : IntegrableOn (fun x => w x ^ 2) (Set.uIoc a b) volume :=
    hw2.integrable_sq.integrableOn
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.uIoc a b) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hdom : IntegrableOn (fun x => (w x ^ 2 + 1) / 2) (Set.uIoc a b) volume :=
    ((hsq.add hc).div_const 2)
  rw [intervalIntegrable_iff]
  refine hdom.mono' hw_meas.aestronglyMeasurable.restrict (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|w x| - 1), sq_abs (w x), abs_nonneg (w x)]

/-- Triangle Fubini for `0 ≤ t`: `∫₀ᵗ ∫₀ˢ f = ∫₀ᵗ (t−r) f(r)`. -/
private lemma triangle_double_integral_nonneg {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, f r) = ∫ r in (0 : ℝ)..t, (t - r) * f r := by
  have hfon : IntegrableOn f (Set.Ioc 0 t) volume := by
    have := hf 0 t; rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at this
  haveI : Fact (volume (Set.Ioc (0 : ℝ) t) < ⊤) := ⟨measure_Ioc_lt_top⟩
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμdef
  set F : ℝ → ℝ → ℝ := fun s r => {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => f p.2) (s, r)
    with hFdef
  have hFmeas : Measurable (Function.uncurry F) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
      measurableSet_le measurable_snd measurable_fst
    exact (hfm.comp measurable_snd).indicator hset
  -- Inner integral over the fixed interval with the indicator.
  have hinner : ∀ s ∈ Set.Ioc (0 : ℝ) t, (∫ r in (0 : ℝ)..s, f r) = ∫ r in Set.Ioc (0:ℝ) t, F s r
      := by
    intro s hs
    rw [intervalIntegral.integral_of_le hs.1.le,
      ← MeasureTheory.integral_indicator measurableSet_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [hFdef, Set.indicator_apply, Set.mem_Ioc, Set.mem_setOf_eq]
    by_cases h1 : 0 < r ∧ r ≤ s
    · have h2 : 0 < r ∧ r ≤ t := ⟨h1.1, h1.2.trans hs.2⟩
      rw [if_pos h1, if_pos h2, if_pos h1.2]
    · by_cases h2 : 0 < r ∧ r ≤ t
      · have hrs : ¬ r ≤ s := by
          rcases not_and_or.1 h1 with h | h; exacts [absurd h2.1 h, h]
        rw [if_neg h1, if_pos h2, if_neg hrs]
      · rw [if_neg h1, if_neg h2]
  -- Outer-`s` integral of `F s r` for fixed `r ∈ Ioc 0 t`.
  have houter : ∀ r ∈ Set.Ioc (0 : ℝ) t, (∫ s in Set.Ioc (0:ℝ) t, F s r) = (t - r) * f r := by
    intro r hr
    have hFr : (fun s => F s r) = (Set.Ici r).indicator (fun _ => f r) := by
      funext s
      simp only [hFdef, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ici]
    have hint_eq : Set.Ioc (0:ℝ) t ∩ Set.Ici r = Set.Icc r t := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hr.1 h1, h2⟩, h1⟩
    rw [hFr, ← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [show (fun s => (Set.Ioc (0:ℝ) t).indicator ((Set.Ici r).indicator (fun _ => f r)) s)
        = (Set.Ioc (0:ℝ) t ∩ Set.Ici r).indicator (fun _ => f r) by
      rw [Set.indicator_indicator]]
    rw [MeasureTheory.integral_indicator (measurableSet_Ioc.inter measurableSet_Ici),
      MeasureTheory.setIntegral_const, hint_eq, MeasureTheory.measureReal_def,
      Real.volume_Icc, smul_eq_mul, ENNReal.toReal_ofReal (by linarith [hr.2]), mul_comm]
  -- Integrability of `F` on the square.
  have hFint : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hg : Integrable (fun p : ℝ × ℝ => |f p.2|) (μ.prod μ) := hfon.abs.comp_snd μ
    refine hg.mono' hFmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, hFdef, Set.indicator_apply, Real.norm_eq_abs]
    split_ifs with h
    · exact le_refl _
    · simp [abs_nonneg]
  -- Assemble.
  rw [intervalIntegral.integral_of_le ht,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hinner,
    MeasureTheory.integral_integral_swap hFint,
    intervalIntegral.integral_of_le ht,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc houter]

/-- Triangle Fubini: `∫₀ᵗ ∫₀ˢ f = ∫₀ᵗ (t−s) f(s)` for any real `t`. -/
private lemma triangle_double_integral {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, f r) = ∫ s in (0 : ℝ)..t, (t - s) * f s := by
  rcases le_total 0 t with ht | ht
  · exact triangle_double_integral_nonneg hfm hf ht
  · -- Reflect: apply the nonneg case to `g r = f (-r)` at `-t ≥ 0`.
    set g : ℝ → ℝ := fun r => f (-r) with hgdef
    have hgm : Measurable g := hfm.comp measurable_neg
    have hgii : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
      intro a b
      have h := (IntervalIntegrable.iff_comp_neg (f := f)).mp (hf (-a) (-b))
      simpa only [neg_neg, hgdef] using h
    have hnt : (0 : ℝ) ≤ -t := by linarith
    have hkey := triangle_double_integral_nonneg hgm hgii hnt
    -- inner reflection: `∫ r in 0..s, g r = -(∫ r in 0..(-s), f r)`.
    have hinnref : ∀ s : ℝ, (∫ r in (0:ℝ)..s, g r) = -(∫ r in (0:ℝ)..(-s), f r) := by
      intro s
      have := intervalIntegral.integral_comp_neg (a := 0) (b := s) f
      simp only [neg_zero, hgdef] at this ⊢
      rw [this, intervalIntegral.integral_symm]
    -- Generic reflection of an `∫ 0..(-t)` integral into an `∫ 0..t` one.
    have hrefl : ∀ φ : ℝ → ℝ, (∫ s in (0:ℝ)..(-t), φ s) = -(∫ x in (0:ℝ)..t, φ (-x)) := by
      intro φ
      have := intervalIntegral.integral_comp_neg (a := 0) (b := t) φ
      simp only [neg_zero] at this
      rw [this, intervalIntegral.integral_symm]
    have hL : (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, f r)
        = ∫ s in (0 : ℝ)..(-t), ∫ r in (0 : ℝ)..s, g r := by
      rw [hrefl (fun s => ∫ r in (0:ℝ)..s, g r)]
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      show (∫ r in (0:ℝ)..x, f r) = -(∫ r in (0:ℝ)..(-x), g r)
      rw [hinnref (-x), neg_neg, neg_neg]
    have hR : (∫ s in (0 : ℝ)..t, (t - s) * f s)
        = ∫ s in (0 : ℝ)..(-t), (-t - s) * g s := by
      rw [hrefl (fun s => (-t - s) * g s)]
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hgdef, neg_neg]; ring
    rw [hL, hR, hkey]

/-- Continuity of `deriv p` from the a.e.-second-derivative witness. -/
private lemma continuous_deriv_of_hpw {p w : ℝ → ℝ} (hw_meas : Measurable w)
    (hw2 : MemLp w 2 volume) (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s) :
    Continuous (deriv p) := by
  have hii : ∀ a b : ℝ, IntervalIntegrable w volume a b :=
    fun a b => intervalIntegrable_of_memLp_two hw_meas hw2 a b
  have hcont : Continuous (fun b => ∫ s in (0 : ℝ)..b, w s) :=
    intervalIntegral.continuous_primitive hii 0
  have heq : deriv p = fun b => deriv p 0 + ∫ s in (0 : ℝ)..b, w s := by
    funext b; have := hpw 0 b; linarith
  rw [heq]; exact continuous_const.add hcont

/-- **Step A**: the second-order integral remainder for `p` (whose derivative is absolutely
continuous with a.e. second derivative `w`):
`p(x+t) − p x − t·deriv p x = t²·∫₀¹ (1−τ)·w(x+τ·t) dτ`. -/
private lemma second_order_remainder {p w : ℝ → ℝ} (hp1 : Differentiable ℝ p)
    (hw_meas : Measurable w) (hw2 : MemLp w 2 volume)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s) (x t : ℝ) :
    p (x + t) - p x - t * deriv p x
      = t ^ 2 * ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * t) := by
  have hdc : Continuous (deriv p) := continuous_deriv_of_hpw hw_meas hw2 hpw
  have hii : ∀ a b : ℝ, IntervalIntegrable w volume a b :=
    fun a b => intervalIntegrable_of_memLp_two hw_meas hw2 a b
  -- FTC: `p(x+t) − p x = ∫ 0..t deriv p (x+s) ds`.
  have hFTC : p (x + t) - p x = ∫ s in (0 : ℝ)..t, deriv p (x + s) := by
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun s => p (x + s)) (deriv p (x + s)) s := by
      intro s _
      have hin : HasDerivAt (fun s : ℝ => x + s) 1 s := by simpa using (hasDerivAt_id s).const_add x
      have hout : HasDerivAt p (deriv p (x + s)) (x + s) := (hp1 (x + s)).hasDerivAt
      simpa using! hout.comp s hin
    have hcont : Continuous (fun s : ℝ => deriv p (x + s)) := hdc.comp (by fun_prop)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 t)
    simp only [add_zero] at this
    rw [this]
  -- `deriv p (x+s) = deriv p x + ∫ 0..s w (x+r) dr`.
  have hdsub : ∀ s : ℝ, deriv p (x + s) = deriv p x + ∫ r in (0 : ℝ)..s, w (x + r) := by
    intro s
    have h1 := hpw x (x + s)
    have h2 : (∫ r in x..(x + s), w r) = ∫ r in (0 : ℝ)..s, w (x + r) := by
      have := intervalIntegral.integral_comp_add_left w x (a := 0) (b := s)
      simp only [add_zero] at this; rw [this]
    rw [h2] at h1; linarith
  rw [hFTC]
  rw [intervalIntegral.integral_congr (g := fun s => deriv p x + ∫ r in (0 : ℝ)..s, w (x + r))
    (fun s _ => hdsub s)]
  -- The double integral over the triangle equals `∫₀ᵗ (t−s) w(x+s) ds` (Fubini).
  set f : ℝ → ℝ := fun r => w (x + r) with hfdef
  have hfm : Measurable f := hw_meas.comp (by fun_prop)
  have hfii : ∀ a b : ℝ, IntervalIntegrable f volume a b := by
    intro a b
    have h := (hii (x + a) (x + b)).comp_add_left x
    simpa only [hfdef, add_sub_cancel_left] using h
  have hWcont : Continuous (fun s : ℝ => ∫ r in (0 : ℝ)..s, f r) :=
    intervalIntegral.continuous_primitive hfii 0
  rw [intervalIntegral.integral_add (intervalIntegrable_const)
    (hWcont.intervalIntegrable 0 t), intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have htri : (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, f r)
      = ∫ s in (0 : ℝ)..t, (t - s) * f s := triangle_double_integral hfm hfii t
  rw [htri]
  -- Change of variables `s = τ·t`.
  have hcov : (∫ s in (0 : ℝ)..t, (t - s) * f s)
      = t ^ 2 * ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * t) := by
    rcases eq_or_ne t 0 with ht0 | ht0
    · simp [ht0]
    · have hc := intervalIntegral.integral_comp_mul_left (fun s => (t - s) * f s) ht0
        (a := 0) (b := 1)
      rw [mul_zero, mul_one] at hc
      have hval : (∫ s in (0:ℝ)..t, (t - s) * f s)
          = t • ∫ τ in (0:ℝ)..1, (t - t * τ) * f (t * τ) := by
        rw [hc, smul_smul, mul_inv_cancel₀ ht0, one_smul]
      have hrw : (∫ τ in (0:ℝ)..1, (t - t * τ) * f (t * τ))
          = t * ∫ τ in (0:ℝ)..1, (1 - τ) * w (x + τ * t) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun τ _ => ?_
        simp only [hfdef]; ring_nf
      rw [hval, hrw, smul_eq_mul]; ring
  rw [hcov]; ring

/-- The deterministic kernel-mean bias functional `D h x = (∫ u, K u · p(x+uh)) − p x`. -/
private noncomputable def kmBias (p K : ℝ → ℝ) (h x : ℝ) : ℝ := (∫ u, K u * p (x + u * h)) - p x

/-- The surrogate `b*(x) = h²·(S_K/2)·w x`, whose squared `L²` norm is exactly `M h`. -/
private noncomputable def kmSurr (w K : ℝ → ℝ) (h x : ℝ) : ℝ :=
  h ^ 2 * ((∫ u, u ^ 2 * K u) / 2) * w x

/-- The `L²`-translation modulus of `w` at shift `s`, as a real number. -/
private noncomputable def transMod (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  ((∫⁻ x, ENNReal.ofReal ((w (x + s) - w x) ^ 2)) ^ (1 / 2 : ℝ)).toReal

/-- The raw `L²`-translation-modulus lower integral `Λ s = ∫⁻ (w(·+s) − w)²`. -/
private noncomputable def transModSq (w : ℝ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((w (x + s) - w x) ^ 2)

private lemma transMod_nonneg {w : ℝ → ℝ} (s : ℝ) : 0 ≤ transMod w s := ENNReal.toReal_nonneg

/-- `Λ s = ∫⁻ (w(·+s)−w)²` is bounded by `4·∫w²`, hence finite. -/
private lemma transModSq_le {w : ℝ → ℝ} (hw_meas : Measurable w) (hw2 : MemLp w 2 volume)
    (s : ℝ) : transModSq w s ≤ ENNReal.ofReal (4 * ∫ x, (w x) ^ 2) := by
  set I : ℝ := ∫ x, (w x) ^ 2 with hIdef
  have hInn : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hΛ0 : (∫⁻ x, ENNReal.ofReal ((w x) ^ 2)) = ENNReal.ofReal I :=
    (ofReal_integral_eq_lintegral_ofReal hw2.integrable_sq (ae_of_all _ fun x => sq_nonneg _)).symm
  have hstep : ∀ x, ENNReal.ofReal ((w (x + s) - w x) ^ 2)
      ≤ ENNReal.ofReal (2 * (w (x + s)) ^ 2) + ENNReal.ofReal (2 * (w x) ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (w (x + s) - w x), sq_nonneg (w (x + s) + w x)])
  calc transModSq w s
      ≤ ∫⁻ x, (ENNReal.ofReal (2 * (w (x + s)) ^ 2) + ENNReal.ofReal (2 * (w x) ^ 2)) :=
        lintegral_mono hstep
    _ = (∫⁻ x, ENNReal.ofReal (2 * (w (x + s)) ^ 2)) + ∫⁻ x, ENNReal.ofReal (2 * (w x) ^ 2) :=
        lintegral_add_right _ (by measurability)
    _ = ENNReal.ofReal (2 * I) + ENNReal.ofReal (2 * I) := by
        congr 1
        · rw [lintegral_congr fun x => ENNReal.ofReal_mul (by norm_num),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [show (∫⁻ x, ENNReal.ofReal ((w (x + s)) ^ 2))
              = ∫⁻ x, ENNReal.ofReal ((w x) ^ 2) from
            lintegral_add_right_eq_self (fun x => ENNReal.ofReal ((w x) ^ 2)) s, hΛ0,
            ← ENNReal.ofReal_mul (by norm_num), show (2:ℝ) * I = 2 * I from rfl]
        · rw [lintegral_congr fun x => ENNReal.ofReal_mul (by norm_num),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hΛ0,
            ← ENNReal.ofReal_mul (by norm_num)]
    _ = ENNReal.ofReal (4 * I) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

private lemma transModSq_ne_top {w : ℝ → ℝ} (hw_meas : Measurable w) (hw2 : MemLp w 2 volume)
    (s : ℝ) : transModSq w s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (transModSq_le hw_meas hw2 s)

/-- `ofReal (ω s) = Λ s ^ (1/2)`: the modulus is the honest square root of the finite `Λ s`. -/
private lemma ofReal_transMod {w : ℝ → ℝ} (hw_meas : Measurable w) (hw2 : MemLp w 2 volume)
    (s : ℝ) : ENNReal.ofReal (transMod w s) = (transModSq w s) ^ (1 / 2 : ℝ) := by
  rw [transMod, transModSq]
  exact ENNReal.ofReal_toReal
    ((ENNReal.rpow_lt_top_of_nonneg (by norm_num) (transModSq_ne_top hw_meas hw2 s)).ne)

private lemma transMod_le {w : ℝ → ℝ} (hw_meas : Measurable w) (hw2 : MemLp w 2 volume)
    (s : ℝ) : transMod w s ≤ Real.sqrt (4 * ∫ x, (w x) ^ 2) := by
  have hInn : 0 ≤ 4 * ∫ x, (w x) ^ 2 := by positivity
  have h1 : (transModSq w s) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt (4 * ∫ x, (w x) ^ 2)) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hInn (by norm_num)]
    exact ENNReal.rpow_le_rpow (transModSq_le hw_meas hw2 s) (by norm_num)
  have h2 : ENNReal.ofReal (transMod w s) ≤ ENNReal.ofReal (Real.sqrt (4 * ∫ x, (w x) ^ 2)) := by
    rw [ofReal_transMod hw_meas hw2 s]; exact h1
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).1 h2

private lemma tendsto_transMod {w : ℝ → ℝ} (hw_meas : Measurable w) (hw2 : MemLp w 2 volume) :
    Filter.Tendsto (transMod w) (nhds 0) (nhds 0) := by
  have hΛ : Filter.Tendsto (transModSq w) (nhds 0) (nhds 0) :=
    tendsto_lintegral_sq_sub_translate hw_meas hw2
  have hrpow : Filter.Tendsto (fun s => (transModSq w s) ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h.comp hΛ
  have htoReal : Filter.Tendsto (fun s => ((transModSq w s) ^ (1 / 2 : ℝ)).toReal)
      (nhds 0) (nhds (0 : ℝ)) := by
    have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hrpow
    simpa using! this
  exact htoReal

private lemma measurable_transMod {w : ℝ → ℝ} (hw_meas : Measurable w) :
    Measurable (transMod w) := by
  have hF : Measurable (Function.uncurry fun s x => ENNReal.ofReal ((w (x + s) - w x) ^ 2)) := by
    have huc : (Function.uncurry fun s x => ENNReal.ofReal ((w (x + s) - w x) ^ 2))
        = fun q : ℝ × ℝ => ENNReal.ofReal ((w (q.2 + q.1) - w q.2) ^ 2) := rfl
    rw [huc]
    exact (((hw_meas.comp (by fun_prop)).sub (hw_meas.comp measurable_snd)).pow_const 2).ennreal_ofReal
  have hΛmeas : Measurable (transModSq w) := hF.lintegral_prod_right'
  exact (ENNReal.continuous_rpow_const.measurable.comp hΛmeas).ennreal_toReal

/-- **Step C, τ-level Minkowski**: the `L²(dx)` norm of the second-order remainder integral over
`τ` is at most the integral over `τ` of the `L²`-moduli, i.e.
`‖∫₀¹ (1−τ)(w(·+τuh)−w) dτ‖_{L²} ≤ ∫₀¹ (1−τ)·ω(τuh) dτ`. -/
private lemma stepC_tau_bound {w : ℝ → ℝ} (hw_meas : Measurable w) (hw2 : MemLp w 2 volume)
    (h u : ℝ) :
    (∫⁻ x, ENNReal.ofReal
        ((∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x)) ^ 2)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (∫ τ in (0 : ℝ)..1, (1 - τ) * transMod w (τ * (u * h))) := by
  classical
  have hωmeas : Measurable (transMod w) := measurable_transMod hw_meas
  set μ2 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ2def
  -- Pointwise `ofReal(D²) ≤ (∫⁻_τ ‖·‖ₑ)²`.
  have hptD : ∀ x,
      ENNReal.ofReal ((∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x)) ^ 2)
        ≤ (∫⁻ τ, ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ ∂μ2) ^ 2 := by
    intro x
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hle := enorm_integral_le_lintegral_enorm
      (μ := μ2) (fun τ => (1 - τ) * (w (x + τ * (u * h)) - w x))
    have heq : ENNReal.ofReal ((∫ τ in Set.Ioc (0 : ℝ) 1, (1 - τ) * (w (x + τ * (u * h)) - w x)) ^ 2)
        = ‖∫ τ in Set.Ioc (0 : ℝ) 1, (1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [heq]
    exact pow_le_pow_left' hle 2
  -- Joint measurability of the `(τ, x)` integrand.
  have hg2meas : Measurable
      (Function.uncurry fun τ x => ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ) := by
    have : (Function.uncurry fun τ x => ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ)
        = fun q : ℝ × ℝ => ‖(1 - q.1) * (w (q.2 + q.1 * (u * h)) - w q.2)‖ₑ := rfl
    rw [this]
    exact (((continuous_const.sub continuous_fst).measurable).mul
      ((hw_meas.comp (by fun_prop)).sub (hw_meas.comp measurable_snd))).enorm
  -- The two-variable Minkowski inequality (over `τ` and `x`).
  have hmink := lintegral_lintegral_sq_rpow_le μ2 volume
    (g := fun τ x => ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ) hg2meas
  -- `R2 = ofReal(∫₀¹ (1−τ)ω)`.
  have hinner : ∀ᵐ τ ∂μ2,
      (∫⁻ x, ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal ((1 - τ) * transMod w (τ * (u * h))) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => ?_
    have hx : ∀ x, ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ ^ 2
        = ENNReal.ofReal ((1 - τ) ^ 2) * ENNReal.ofReal ((w (x + τ * (u * h)) - w x) ^ 2) := by
      intro x
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, mul_pow,
        ENNReal.ofReal_mul (by positivity)]
    rw [lintegral_congr hx, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      show (∫⁻ x, ENNReal.ofReal ((w (x + τ * (u * h)) - w x) ^ 2)) = transModSq w (τ * (u * h))
        from rfl,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ofReal_transMod hw_meas hw2 (τ * (u * h)),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by linarith [hτ.2] : (0 : ℝ) ≤ 1 - τ),
      ← ENNReal.ofReal_mul (by linarith [hτ.2] : (0 : ℝ) ≤ 1 - τ)]
  have hginteg : Integrable (fun τ => (1 - τ) * transMod w (τ * (u * h))) μ2 := by
    rw [hμ2def]
    refine Integrable.mono' (g := fun _ => Real.sqrt (4 * ∫ x, (w x) ^ 2))
      (integrableOn_const (C := Real.sqrt (4 * ∫ x, (w x) ^ 2)) measure_Ioc_lt_top.ne)
      (((continuous_const.sub continuous_id).measurable).mul
        (hωmeas.comp (by fun_prop))).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => ?_
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by linarith [hτ.2]) (transMod_nonneg _))]
    calc (1 - τ) * transMod w (τ * (u * h))
        ≤ 1 * Real.sqrt (4 * ∫ x, (w x) ^ 2) :=
          mul_le_mul (by linarith [hτ.1]) (transMod_le hw_meas hw2 _)
            (transMod_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hgnn : ∀ᵐ τ ∂μ2, 0 ≤ (1 - τ) * transMod w (τ * (u * h)) :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ =>
      mul_nonneg (by linarith [hτ.2]) (transMod_nonneg _)
  have hR2eq : (∫⁻ τ, (∫⁻ x, ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ ^ 2) ^ (1 / 2 : ℝ) ∂μ2)
      = ENNReal.ofReal (∫ τ in (0 : ℝ)..1, (1 - τ) * transMod w (τ * (u * h))) := by
    rw [lintegral_congr_ae hinner, ← ofReal_integral_eq_lintegral_ofReal hginteg hgnn,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- Assemble.
  calc (∫⁻ x, ENNReal.ofReal
          ((∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x)) ^ 2)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ x, (∫⁻ τ, ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ ∂μ2) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono hptD) (by norm_num)
    _ ≤ ∫⁻ τ, (∫⁻ x, ‖(1 - τ) * (w (x + τ * (u * h)) - w x)‖ₑ ^ 2) ^ (1 / 2 : ℝ) ∂μ2 := hmink
    _ = ENNReal.ofReal (∫ τ in (0 : ℝ)..1, (1 - τ) * transMod w (τ * (u * h))) := hR2eq

/-- **Step B**: the a.e.-`x` bias identity. Using `∫K = 1` and `∫uK = 0`,
`kmBias p K h x = h²·∫ u, K u · u² · (∫₀¹ (1−τ)·w(x+τuh) dτ) du`. -/
private lemma kmBias_eq {p K w : ℝ → ℝ}
    (hp_meas : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1)
    (hp1 : Differentiable ℝ p) (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s)
    (hw2 : MemLp w 2 volume) (hK : IsKernelOfOrder K 1) (hKmeas : Measurable K)
    (hKu2 : Integrable fun u => u ^ 2 * |K u|) {h : ℝ} (hh : 0 < h) (x : ℝ)
    (hKp : Integrable (fun u => K u * p (x + u * h))) :
    kmBias p K h x
      = h ^ 2 * ∫ u, K u * u ^ 2 * ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * (u * h)) := by
  set R : ℝ → ℝ := fun u => ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * (u * h)) with hRdef
  -- Step A pointwise, with `t = u·h`.
  have hA : ∀ u, K u * p (x + u * h)
      = (K u * p x + K u * (u * h) * deriv p x) + K u * (u ^ 2 * h ^ 2) * R u := by
    intro u
    have hsa := second_order_remainder hp1 hw_meas hw2 hpw x (u * h)
    have hRu : (∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * (u * h))) = R u := rfl
    have : p (x + u * h) = p x + (u * h) * deriv p x + (u * h) ^ 2 * R u := by
      rw [hRdef] at hRu ⊢; nlinarith [hsa]
    rw [this]; ring
  -- The two low-order pieces integrate to `p x` and `0`.
  have hK_int : Integrable K := by simpa using hK.integrable_pow 0 (Nat.zero_le _)
  have hpoly1 : Integrable (fun u => K u * p x) := hK_int.mul_const _
  have hpoly2 : Integrable (fun u => K u * (u * h) * deriv p x) := by
    have h1 : Integrable (fun u => u ^ 1 * K u) := hK.integrable_pow 1 (le_refl 1)
    have : (fun u => K u * (u * h) * deriv p x)
        = fun u => (h * deriv p x) * (u ^ 1 * K u) := by funext u; simp only [pow_one]; ring
    rw [this]; exact h1.const_mul _
  have hpoly : Integrable (fun u => K u * p x + K u * (u * h) * deriv p x) := hpoly1.add hpoly2
  have hthird : Integrable (fun u => K u * (u ^ 2 * h ^ 2) * R u) := by
    have heq : (fun u => K u * (u ^ 2 * h ^ 2) * R u)
        = fun u => K u * p (x + u * h) - (K u * p x + K u * (u * h) * deriv p x) := by
      funext u; rw [hA u]; ring
    rw [heq]; exact hKp.sub hpoly
  -- Assemble.
  have hsplit : (∫ u, K u * p (x + u * h))
      = (∫ u, K u * p x + K u * (u * h) * deriv p x) + ∫ u, K u * (u ^ 2 * h ^ 2) * R u := by
    rw [← integral_add hpoly hthird]
    exact integral_congr_ae (ae_of_all _ fun u => hA u)
  have hlow : (∫ u, K u * p x + K u * (u * h) * deriv p x) = p x := by
    rw [integral_add hpoly1 hpoly2, integral_mul_const, hK.integral_eq_one, one_mul]
    have h0m : (∫ u, K u * (u * h) * deriv p x) = 0 := by
      have : (fun u => K u * (u * h) * deriv p x)
          = fun u => (h * deriv p x) * (u ^ 1 * K u) := by funext u; simp only [pow_one]; ring
      rw [this, integral_const_mul, hK.moment_eq_zero 1 (le_refl 1) (le_refl 1), mul_zero]
    rw [h0m, add_zero]
  have hthirdval : (∫ u, K u * (u ^ 2 * h ^ 2) * R u) = h ^ 2 * ∫ u, K u * u ^ 2 * R u := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun u => ?_); ring
  rw [kmBias, hsplit, hlow, hthirdval, add_sub_cancel_left]

/-- `∫⁻ x ofReal(f x²) = (eLpNorm f 2)²`, the `ofReal`↔`eLpNorm` bridge for real `f`. -/
private lemma lintegral_ofReal_sq_eq_eLpNorm_sq {f : ℝ → ℝ} :
    (∫⁻ x, ENNReal.ofReal ((f x) ^ 2)) = (eLpNorm f 2 volume) ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    Real.rpow_two, sq_abs]

/-- Interval-integrability of `τ ↦ (1−τ)·w(x+τc)` on `[0,1]` from `MemLp w 2` (affine change of
variables plus continuity of `1−τ`). -/
private lemma intervalIntegrable_taylor_kernel {w : ℝ → ℝ} (hw_meas : Measurable w)
    (hw2 : MemLp w 2 volume) (x c : ℝ) :
    IntervalIntegrable (fun τ => (1 - τ) * w (x + τ * c)) volume 0 1 := by
  have hii : ∀ a b : ℝ, IntervalIntegrable w volume a b :=
    fun a b => intervalIntegrable_of_memLp_two hw_meas hw2 a b
  have haff : IntervalIntegrable (fun τ => w (x + τ * c)) volume 0 1 := by
    rcases eq_or_ne c 0 with hc | hc
    · simp only [hc, mul_zero, add_zero]; exact intervalIntegrable_const
    · have h1 : IntervalIntegrable (fun y => w (x + y)) volume 0 c := by
        simpa using (hii x (x + c)).comp_add_left x
      simpa only [zero_div, div_self hc, mul_comm c] using h1.comp_mul_left (c := c)
  exact haff.continuousOn_mul (Continuous.continuousOn (by fun_prop))

/-- Integrability in `u` of `K u · u² · ∫₀¹ (1−τ)·w(x+τuh) dτ`, from the second-order remainder
and the low-order kernel-moment integrabilities. -/
private lemma integrable_kernel_sq_taylor {p K w : ℝ → ℝ}
    (hp1 : Differentiable ℝ p) (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s) (hw2 : MemLp w 2 volume)
    (hK : IsKernelOfOrder K 1) {h x : ℝ} (hh : 0 < h)
    (hKp : Integrable (fun u => K u * p (x + u * h))) :
    Integrable (fun u => K u * u ^ 2 * ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * (u * h))) := by
  set R : ℝ → ℝ := fun u => ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * (u * h)) with hRdef
  have hK_int : Integrable K := by simpa using hK.integrable_pow 0 (Nat.zero_le _)
  have hpoly1 : Integrable (fun u => K u * p x) := hK_int.mul_const _
  have hpoly2 : Integrable (fun u => K u * (u * h) * deriv p x) := by
    have hh1 : Integrable (fun u => u ^ 1 * K u) := hK.integrable_pow 1 (le_refl 1)
    have he : (fun u => K u * (u * h) * deriv p x) = fun u => (h * deriv p x) * (u ^ 1 * K u) := by
      funext u; simp only [pow_one]; ring
    rw [he]; exact hh1.const_mul _
  have hpoly : Integrable (fun u => K u * p x + K u * (u * h) * deriv p x) := hpoly1.add hpoly2
  have hA : ∀ u, K u * p (x + u * h)
      = (K u * p x + K u * (u * h) * deriv p x) + K u * (u ^ 2 * h ^ 2) * R u := by
    intro u
    have hsa := second_order_remainder hp1 hw_meas hw2 hpw x (u * h)
    have hRu : (∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * (u * h))) = R u := rfl
    rw [hRu] at hsa
    have hp : p (x + u * h) = p x + (u * h) * deriv p x + (u * h) ^ 2 * R u := by linarith [hsa]
    rw [hp]; ring
  have hthird : Integrable (fun u => K u * (u ^ 2 * h ^ 2) * R u) := by
    have heq : (fun u => K u * (u ^ 2 * h ^ 2) * R u)
        = fun u => K u * p (x + u * h) - (K u * p x + K u * (u * h) * deriv p x) := by
      funext u; rw [hA u]; ring
    rw [heq]; exact hKp.sub hpoly
  have hh0 : (h : ℝ) ^ 2 ≠ 0 := by positivity
  have hfac : (fun u => K u * u ^ 2 * R u)
      = fun u => (h ^ 2)⁻¹ * (K u * (u ^ 2 * h ^ 2) * R u) := by
    funext u; field_simp
  show Integrable (fun u => K u * u ^ 2 * R u)
  rw [hfac]; exact hthird.const_mul _

/-- **Step C**: the `L²(dx)` distance between the bias and its surrogate is `o(h²)`. There is a
function `κ : ℝ → ℝ` tending to `0` at `0`, with `κ ≥ 0`, such that for all `0 < h`,
`eLpNorm (fun x => kmBias p K h x − kmSurr w K h x) 2 ≤ ofReal (h² · κ h)`. -/
private lemma stepC_bound {p K w : ℝ → ℝ}
    (hp_meas : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1)
    (hp1 : Differentiable ℝ p) (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s)
    (hw2 : MemLp w 2 volume) (hK : IsKernelOfOrder K 1) (hKmeas : Measurable K)
    (hKu2 : Integrable fun u => u ^ 2 * |K u|) :
    ∃ κ : ℝ → ℝ, (∀ s, 0 ≤ κ s) ∧ Filter.Tendsto κ (nhds 0) (nhds 0) ∧
      ∀ h : ℝ, 0 < h →
        eLpNorm (fun x => kmBias p K h x - kmSurr w K h x) 2 volume
          ≤ ENNReal.ofReal (h ^ 2 * κ h) := by
  classical
  set I : ℝ := ∫ x, (w x) ^ 2 with hIdef
  set M : ℝ := Real.sqrt (4 * I) with hMdef
  have hMnn : 0 ≤ M := Real.sqrt_nonneg _
  have hωnn : ∀ s, 0 ≤ transMod w s := fun s => transMod_nonneg s
  have hωle : ∀ s, transMod w s ≤ M := fun s => transMod_le hw_meas hw2 s
  have hωmeas : Measurable (transMod w) := measurable_transMod hw_meas
  have hω0 : Filter.Tendsto (transMod w) (nhds 0) (nhds 0) := tendsto_transMod hw_meas hw2
  -- Inner integrand `τ ↦ (1−τ)·ω(τ·u·h)` is interval-integrable on `[0,1]`.
  have hII : ∀ u h' : ℝ,
      IntervalIntegrable (fun τ => (1 - τ) * transMod w (τ * (u * h'))) volume 0 1 := by
    intro u h'
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hmeas : AEStronglyMeasurable (fun τ => (1 - τ) * transMod w (τ * (u * h')))
        (volume.restrict (Set.Ioc 0 1)) :=
      (((continuous_const.sub continuous_id).measurable).mul
        (hωmeas.comp (by fun_prop))).aestronglyMeasurable
    refine Integrable.mono' (g := fun _ => M) (integrableOn_const measure_Ioc_lt_top.ne) hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hτ.2]) (hωnn _))]
    calc (1 - τ) * transMod w (τ * (u * h'))
        ≤ 1 * M := mul_le_mul (by linarith [hτ.1]) (hωle _) (hωnn _) (by norm_num)
      _ = M := one_mul M
  -- The inner integral `gg u h = ∫₀¹ (1−τ)·ω(τuh) dτ`.
  set gg : ℝ → ℝ → ℝ := fun u h' => ∫ τ in (0 : ℝ)..1, (1 - τ) * transMod w (τ * (u * h'))
    with hggdef
  have hg_nonneg : ∀ u h', 0 ≤ gg u h' := fun u h' =>
    intervalIntegral.integral_nonneg (by norm_num)
      (fun τ hτ => mul_nonneg (by linarith [hτ.2]) (hωnn _))
  have hg_le : ∀ u h', gg u h' ≤ M := by
    intro u h'
    have h1 : gg u h' ≤ ∫ _τ in (0 : ℝ)..1, M := by
      refine intervalIntegral.integral_mono_on (by norm_num) (hII u h') intervalIntegrable_const
        (fun τ hτ => ?_)
      calc (1 - τ) * transMod w (τ * (u * h'))
          ≤ 1 * M := mul_le_mul (by linarith [hτ.1]) (hωle _) (hωnn _) (by norm_num)
        _ = M := one_mul M
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul] at h1
  have hgmeas : ∀ h', Measurable (fun u => gg u h') := by
    intro h'
    have hrw : (fun u => gg u h')
        = fun u => ∫ τ in Set.Ioc (0 : ℝ) 1, (1 - τ) * transMod w (τ * (u * h')) := by
      funext u; simp only [hggdef]; rw [intervalIntegral.integral_of_le (by norm_num)]
    rw [hrw]
    have hsm : StronglyMeasurable
        (Function.uncurry fun u τ => (1 - τ) * transMod w (τ * (u * h'))) := by
      refine Measurable.stronglyMeasurable ?_
      have : (Function.uncurry fun u τ => (1 - τ) * transMod w (τ * (u * h')))
          = fun q : ℝ × ℝ => (1 - q.2) * transMod w (q.2 * (q.1 * h')) := rfl
      rw [this]
      exact ((continuous_const.sub continuous_snd).measurable).mul (hωmeas.comp (by fun_prop))
    exact (hsm.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 1))).measurable
  -- The dominating integrable envelope `|K u|·u²·M`.
  have hdom : Integrable (fun u => |K u| * u ^ 2 * M) :=
    (hKu2.const_mul M).congr (ae_of_all _ fun u => by ring)
  -- The modulus function.
  set κ : ℝ → ℝ := fun h' => ∫ u, |K u| * u ^ 2 * gg u h' with hκdef
  refine ⟨κ, ?_, ?_, ?_⟩
  · -- `κ ≥ 0`.
    intro h'
    exact integral_nonneg fun u =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (hg_nonneg u h')
  · -- `κ → 0` at `0`, by nested dominated convergence.
    -- Inner limit: for each `u`, `gg u h' → 0` as `h' → 0`.
    have hgtend : ∀ u, Filter.Tendsto (fun h' => gg u h') (nhds 0) (nhds 0) := by
      intro u
      have hmeas2 : ∀ h', AEStronglyMeasurable (fun τ => (1 - τ) * transMod w (τ * (u * h')))
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun h' =>
        (((continuous_const.sub continuous_id).measurable).mul
          (hωmeas.comp (by fun_prop))).aestronglyMeasurable
      have hbd2 : ∀ h', ∀ᵐ τ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
          ‖(1 - τ) * transMod w (τ * (u * h'))‖ ≤ M := by
        intro h'
        refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hτ.2]) (hωnn _))]
        calc (1 - τ) * transMod w (τ * (u * h'))
            ≤ 1 * M := mul_le_mul (by linarith [hτ.1]) (hωle _) (hωnn _) (by norm_num)
          _ = M := one_mul M
      have hbdint2 : Integrable (fun _ : ℝ => M) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        integrableOn_const measure_Ioc_lt_top.ne
      have hlim2 : ∀ᵐ τ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
          Filter.Tendsto (fun h' => (1 - τ) * transMod w (τ * (u * h'))) (nhds 0) (nhds 0) := by
        refine ae_of_all _ fun τ => ?_
        have htend0 : Filter.Tendsto (fun h' : ℝ => τ * (u * h')) (nhds 0) (nhds 0) :=
          (by fun_prop : Continuous (fun h' : ℝ => τ * (u * h'))).tendsto' 0 0 (by simp)
        have := (hω0.comp htend0).const_mul (1 - τ)
        simpa using this
      have hconv : (fun h' => gg u h')
          = fun h' => ∫ τ in Set.Ioc (0 : ℝ) 1, (1 - τ) * transMod w (τ * (u * h')) := by
        funext h'; simp only [hggdef]; rw [intervalIntegral.integral_of_le (by norm_num)]
      rw [hconv]
      have key := tendsto_integral_filter_of_dominated_convergence
        (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (l := nhds (0 : ℝ)) (f := fun _ => (0 : ℝ))
        (fun _ => M) (Filter.Eventually.of_forall hmeas2) (Filter.Eventually.of_forall hbd2)
        hbdint2 hlim2
      simpa using key
    -- Outer dominated convergence.
    have hmeasO : ∀ h', AEStronglyMeasurable (fun u => |K u| * u ^ 2 * gg u h') volume := fun h' =>
      (((hKmeas.abs).mul (by fun_prop)).mul (hgmeas h')).aestronglyMeasurable
    have hbdO : ∀ h', ∀ᵐ u, ‖|K u| * u ^ 2 * gg u h'‖ ≤ |K u| * u ^ 2 * M := by
      intro h'
      refine ae_of_all _ fun u => ?_
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (hg_nonneg u h'))]
      exact mul_le_mul_of_nonneg_left (hg_le u h') (mul_nonneg (abs_nonneg _) (sq_nonneg _))
    have hlimO : ∀ᵐ u, Filter.Tendsto (fun h' => |K u| * u ^ 2 * gg u h') (nhds 0) (nhds 0) := by
      refine ae_of_all _ fun u => ?_
      have := (hgtend u).const_mul (|K u| * u ^ 2)
      simpa using this
    have keyO := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := nhds (0 : ℝ))
      (f := fun _ => (0 : ℝ)) (fun u => |K u| * u ^ 2 * M) (Filter.Eventually.of_forall hmeasO)
      (Filter.Eventually.of_forall hbdO) hdom hlimO
    simpa using keyO
  · -- The `L²` bound via two generalized Minkowski inequalities.
    intro h hh
    have hp_int : Integrable p := by
      by_contra hni; rw [integral_undef hni] at h1; exact one_ne_zero h1.symm
    have hmass : (∫⁻ z, ENNReal.ofReal (p z)) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hp_int (ae_of_all _ h0), h1, ENNReal.ofReal_one]
    have hK_int : Integrable K := by simpa using hK.integrable_pow 0 (Nat.zero_le _)
    have hKabs_int : Integrable (fun u => |K u|) := hK_int.abs
    set G : ℝ → ℝ → ℝ := fun u x => K u * u ^ 2
        * ∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x) with hGdef
    -- Tonelli: a.e.-`x` integrability of `u ↦ K u · p(x+uh)`.
    have hfmeas : Measurable (Function.uncurry
        (fun x u => ENNReal.ofReal (|K u| * p (x + u * h)))) := by
      have huc : Function.uncurry (fun x u => ENNReal.ofReal (|K u| * p (x + u * h)))
          = fun q : ℝ × ℝ => ENNReal.ofReal (|K q.2| * p (q.1 + q.2 * h)) := rfl
      rw [huc]
      exact ((Measurable.abs (hKmeas.comp measurable_snd)).mul
        (hp_meas.comp (by fun_prop))).ennreal_ofReal
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
    -- `κ h ≥ 0`.
    have hκnn : 0 ≤ κ h := integral_nonneg fun u =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (hg_nonneg u h)
    -- The a.e.-`x` identity `Δ x = h²·∫ u, G u x`.
    have hΔ : ∀ᵐ x, kmBias p K h x - kmSurr w K h x = h ^ 2 * ∫ u, G u x := by
      filter_upwards [haex] with x hx
      have hKp : Integrable (fun u => K u * p (x + u * h)) := by
        refine ⟨(hKmeas.mul (hp_meas.comp (by fun_prop))).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        rw [lintegral_congr fun u => by
          rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (h0 _)]]
        exact hx
      have hbeq := kmBias_eq hp_meas h0 h1 hp1 hw_meas hpw hw2 hK hKmeas hKu2 hh x hKp
      have hRint := integrable_kernel_sq_taylor hp1 hw_meas hpw hw2 hK hh hKp
      have hu2K : Integrable (fun u => u ^ 2 * K u) := by
        refine hKu2.mono' ((by fun_prop : Measurable (fun u : ℝ => u ^ 2)).mul
          hKmeas).aestronglyMeasurable (ae_of_all _ fun u => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hconstint : Integrable (fun u => K u * u ^ 2 * (w x / 2)) := by
        have he : (fun u => K u * u ^ 2 * (w x / 2)) = fun u => (w x / 2) * (u ^ 2 * K u) := by
          funext u; ring
        rw [he]; exact hu2K.const_mul _
      have h12 : (∫ τ in (0 : ℝ)..1, (1 - τ)) = 1 / 2 := by
        have hd : ∀ τ ∈ Set.uIcc (0 : ℝ) 1,
            HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - τ) τ := by
          intro τ _
          have hderiv : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - 2 * τ ^ 1 / 2) τ :=
            (hasDerivAt_id τ).sub ((hasDerivAt_pow 2 τ).div_const 2)
          convert hderiv using 1; ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          ((by fun_prop : Continuous (fun τ : ℝ => 1 - τ)).intervalIntegrable 0 1)]
        norm_num
      have hDsplit : ∀ u, (∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x))
          = (∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * (u * h))) - w x / 2 := by
        intro u
        have e1 : (fun τ => (1 - τ) * (w (x + τ * (u * h)) - w x))
            = fun τ => (1 - τ) * w (x + τ * (u * h)) - w x * (1 - τ) := by funext τ; ring
        rw [e1, intervalIntegral.integral_sub
          (intervalIntegrable_taylor_kernel hw_meas hw2 x (u * h))
          ((by fun_prop : Continuous (fun τ => w x * (1 - τ))).intervalIntegrable 0 1),
          intervalIntegral.integral_const_mul, h12]
        ring
      have hGval : (∫ u, G u x)
          = (∫ u, K u * u ^ 2 * ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * (u * h)))
              - ∫ u, K u * u ^ 2 * (w x / 2) := by
        rw [← integral_sub hRint hconstint]
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only [hGdef]
        rw [hDsplit u]; ring
      have hconstval : (∫ u, K u * u ^ 2 * (w x / 2)) = (∫ u, u ^ 2 * K u) / 2 * w x := by
        rw [show (fun u => K u * u ^ 2 * (w x / 2)) = fun u => (w x / 2) * (u ^ 2 * K u) from by
          funext u; ring, integral_const_mul]
        ring
      rw [hGval, mul_sub, ← hbeq, hconstval]
      simp only [kmSurr]; ring
    -- Joint measurability of `G`.
    have hD2meas : Measurable (Function.uncurry
        (fun u x => ∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x))) := by
      have hrw : (Function.uncurry
          (fun u x => ∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x)))
          = fun q : ℝ × ℝ => ∫ τ in Set.Ioc (0 : ℝ) 1,
              (1 - τ) * (w (q.2 + τ * (q.1 * h)) - w q.2) := by
        funext q; simp only [Function.uncurry]
        rw [intervalIntegral.integral_of_le (by norm_num)]
      rw [hrw]
      have hsm : StronglyMeasurable (Function.uncurry
          fun q : ℝ × ℝ => fun τ => (1 - τ) * (w (q.2 + τ * (q.1 * h)) - w q.2)) := by
        refine Measurable.stronglyMeasurable ?_
        have : (Function.uncurry fun q : ℝ × ℝ =>
              fun τ => (1 - τ) * (w (q.2 + τ * (q.1 * h)) - w q.2))
            = fun r : (ℝ × ℝ) × ℝ => (1 - r.2) * (w (r.1.2 + r.2 * (r.1.1 * h)) - w r.1.2) := rfl
        rw [this]
        exact ((continuous_const.sub continuous_snd).measurable).mul
          ((hw_meas.comp (by fun_prop)).sub (hw_meas.comp (by fun_prop)))
      exact (hsm.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))).measurable
    have hGmeas : Measurable (Function.uncurry G) := by
      have hrw : Function.uncurry G = fun q : ℝ × ℝ => K q.1 * q.1 ^ 2
          * Function.uncurry
              (fun u x => ∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x)) q := rfl
      rw [hrw]
      exact ((hKmeas.comp measurable_fst).mul (by fun_prop)).mul hD2meas
    -- Per-`u` factor bound from the `τ`-level Minkowski.
    have hRu_bound : ∀ u, (∫⁻ x, ‖G u x‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (|K u| * u ^ 2 * gg u h) := by
      intro u
      have hGx : ∀ x, ‖G u x‖ₑ ^ 2
          = ENNReal.ofReal ((K u * u ^ 2) ^ 2) * ENNReal.ofReal
              ((∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x)) ^ 2) := by
        intro x
        simp only [hGdef]
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, mul_pow,
          ENNReal.ofReal_mul (by positivity)]
      rw [lintegral_congr hGx, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg u)]
      calc ENNReal.ofReal (|K u| * u ^ 2)
            * (∫⁻ x, ENNReal.ofReal
                ((∫ τ in (0 : ℝ)..1, (1 - τ) * (w (x + τ * (u * h)) - w x)) ^ 2)) ^ (1 / 2 : ℝ)
          ≤ ENNReal.ofReal (|K u| * u ^ 2) * ENNReal.ofReal (gg u h) :=
            mul_le_mul_right (stepC_tau_bound hw_meas hw2 h u) _
        _ = ENNReal.ofReal (|K u| * u ^ 2 * gg u h) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
    -- Two-variable Minkowski over `(u, x)`.
    have hmink := lintegral_lintegral_sq_rpow_le volume volume
      (g := fun u x => ‖G u x‖ₑ) hGmeas.enorm
    have hκintegrand : Integrable (fun u => |K u| * u ^ 2 * gg u h) := by
      refine Integrable.mono' hdom
        (((hKmeas.abs).mul (by fun_prop)).mul (hgmeas h)).aestronglyMeasurable
        (ae_of_all _ fun u => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (hg_nonneg u h))]
      exact mul_le_mul_of_nonneg_left (hg_le u h) (mul_nonneg (abs_nonneg _) (sq_nonneg _))
    have hRle : (∫⁻ u, (∫⁻ x, ‖G u x‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal (κ h) := by
      calc (∫⁻ u, (∫⁻ x, ‖G u x‖ₑ ^ 2) ^ (1 / 2 : ℝ))
          ≤ ∫⁻ u, ENNReal.ofReal (|K u| * u ^ 2 * gg u h) := lintegral_mono hRu_bound
        _ = ENNReal.ofReal (∫ u, |K u| * u ^ 2 * gg u h) :=
            (ofReal_integral_eq_lintegral_ofReal hκintegrand
              (ae_of_all _ fun u => mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))
                (hg_nonneg u h))).symm
    have hchain : (∫⁻ x, (∫⁻ u, ‖G u x‖ₑ) ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (κ h) :=
      le_trans hmink hRle
    have hRint2 : (∫⁻ x, (∫⁻ u, ‖G u x‖ₑ) ^ 2) ≤ (ENNReal.ofReal (κ h)) ^ 2 := by
      have h2 := ENNReal.rpow_le_rpow hchain (by norm_num : (0 : ℝ) ≤ 2)
      rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.rpow_two] at h2
    -- Pointwise bound feeding the outer lintegral.
    have hpt : ∀ x, ENNReal.ofReal ((h ^ 2 * ∫ u, G u x) ^ 2)
        ≤ (ENNReal.ofReal (h ^ 2)) ^ 2 * (∫⁻ u, ‖G u x‖ₑ) ^ 2 := by
      intro x
      have he : ENNReal.ofReal ((h ^ 2 * ∫ u, G u x) ^ 2) = ‖h ^ 2 * ∫ u, G u x‖ₑ ^ 2 := by
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      rw [he]
      have hb : ‖h ^ 2 * ∫ u, G u x‖ₑ ≤ ENNReal.ofReal (h ^ 2) * ∫⁻ u, ‖G u x‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 2),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ h ^ 2)]
        refine mul_le_mul_right ?_ _
        rw [← Real.enorm_eq_ofReal_abs]
        exact enorm_integral_le_lintegral_enorm _
      calc ‖h ^ 2 * ∫ u, G u x‖ₑ ^ 2
          ≤ (ENNReal.ofReal (h ^ 2) * ∫⁻ u, ‖G u x‖ₑ) ^ 2 := pow_le_pow_left' hb 2
        _ = (ENNReal.ofReal (h ^ 2)) ^ 2 * (∫⁻ u, ‖G u x‖ₑ) ^ 2 := by rw [mul_pow]
    have hcore : (∫⁻ x, ENNReal.ofReal ((h ^ 2 * ∫ u, G u x) ^ 2))
        ≤ ENNReal.ofReal ((h ^ 2 * κ h) ^ 2) := by
      calc (∫⁻ x, ENNReal.ofReal ((h ^ 2 * ∫ u, G u x) ^ 2))
          ≤ (ENNReal.ofReal (h ^ 2)) ^ 2 * ∫⁻ x, (∫⁻ u, ‖G u x‖ₑ) ^ 2 := by
            calc (∫⁻ x, ENNReal.ofReal ((h ^ 2 * ∫ u, G u x) ^ 2))
                ≤ ∫⁻ x, (ENNReal.ofReal (h ^ 2)) ^ 2 * (∫⁻ u, ‖G u x‖ₑ) ^ 2 := lintegral_mono hpt
              _ = (ENNReal.ofReal (h ^ 2)) ^ 2 * ∫⁻ x, (∫⁻ u, ‖G u x‖ₑ) ^ 2 :=
                  lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        _ ≤ (ENNReal.ofReal (h ^ 2)) ^ 2 * (ENNReal.ofReal (κ h)) ^ 2 :=
            mul_le_mul_right hRint2 _
        _ = ENNReal.ofReal ((h ^ 2 * κ h) ^ 2) := by
            rw [← mul_pow, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_pow (mul_nonneg (by positivity) hκnn)]
    -- Conclude.
    rw [eLpNorm_congr_ae hΔ]
    have heLp : eLpNorm (fun x => h ^ 2 * ∫ u, G u x) 2 volume
        = (∫⁻ x, ENNReal.ofReal ((h ^ 2 * ∫ u, G u x) ^ 2)) ^ (1 / 2 : ℝ) := by
      rw [lintegral_ofReal_sq_eq_eLpNorm_sq, ← ENNReal.rpow_mul,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
    rw [heLp]
    calc (∫⁻ x, ENNReal.ofReal ((h ^ 2 * ∫ u, G u x) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal ((h ^ 2 * κ h) ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hcore (by norm_num)
      _ = ENNReal.ofReal (h ^ 2 * κ h) := by
          rw [show ((h ^ 2 * κ h) ^ 2) = (h ^ 2 * κ h) ^ (2 : ℝ) from (Real.rpow_natCast _ 2).symm,
            ← ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity) hκnn) (by norm_num),
            ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

/-- The surrogate is in `L²` with `eLpNorm (kmSurr) 2 = ofReal(h²·|S_K|/2·√(∫w²))`. -/
private lemma eLpNorm_kmSurr {w K : ℝ → ℝ} (hw_meas : Measurable w) (hw2 : MemLp w 2 volume)
    {h : ℝ} :
    eLpNorm (fun x => kmSurr w K h x) 2 volume
      = ENNReal.ofReal (h ^ 2 * (|∫ u, u ^ 2 * K u| / 2) * (∫ x, (w x) ^ 2).sqrt) := by
  set c : ℝ := h ^ 2 * ((∫ u, u ^ 2 * K u) / 2) with hcdef
  set S : ℝ := ∫ u, u ^ 2 * K u with hSdef
  set I : ℝ := ∫ x, (w x) ^ 2 with hIdef
  have hInn : 0 ≤ I := by rw [hIdef]; exact integral_nonneg fun x => sq_nonneg _
  -- `eLpNorm w 2 = ofReal (√ I)`.
  have hwnorm : eLpNorm w 2 volume = ENNReal.ofReal I.sqrt := by
    have h1 : (∫⁻ x, ENNReal.ofReal ((w x) ^ 2)) = (eLpNorm w 2 volume) ^ (2 : ℝ) :=
      lintegral_ofReal_sq_eq_eLpNorm_sq
    have h2 : (∫⁻ x, ENNReal.ofReal ((w x) ^ 2)) = ENNReal.ofReal I :=
      (ofReal_integral_eq_lintegral_ofReal hw2.integrable_sq (ae_of_all _ fun x => sq_nonneg _)).symm
    have h3 : (eLpNorm w 2 volume) ^ (2 : ℝ) = ENNReal.ofReal I := by rw [← h1, h2]
    have h4 : eLpNorm w 2 volume = (ENNReal.ofReal I) ^ (1 / 2 : ℝ) := by
      rw [← h3, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
    rw [h4, ENNReal.ofReal_rpow_of_nonneg hInn (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.sqrt_eq_rpow]
  -- The surrogate is `c • w`.
  have hsmul : (fun x => kmSurr w K h x) = c • w := by
    funext x; simp only [kmSurr, Pi.smul_apply, smul_eq_mul, hcdef, hSdef]
  rw [hsmul, eLpNorm_const_smul, hwnorm, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_mul (abs_nonneg c)]
  congr 1
  have hcabs : |c| = h ^ 2 * (|S| / 2) := by
    rw [hcdef, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 2), abs_div,
      show |(2 : ℝ)| = 2 by norm_num]
  rw [hcabs]

/-- **Deterministic core**: the exact asymptotics of `∫⁻ x ofReal(D h x ²)`, independent of the
sample and of `n`. -/
private lemma kmBias_asymptotic {p K w : ℝ → ℝ}
    (hp_meas : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1)
    (hp1 : Differentiable ℝ p) (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s)
    (hw2 : MemLp w 2 volume) (hK : IsKernelOfOrder K 1) (hKmeas : Measurable K)
    (hKu2 : Integrable fun u => u ^ 2 * |K u|) (ε : ℝ) (hε : 0 < ε) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ENNReal.ofReal (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) - ε * h ^ 4)
          ≤ (∫⁻ x, ENNReal.ofReal ((kmBias p K h x) ^ 2)) ∧
        (∫⁻ x, ENNReal.ofReal ((kmBias p K h x) ^ 2))
          ≤ ENNReal.ofReal
              (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) + ε * h ^ 4) := by
  classical
  set S : ℝ := ∫ u, u ^ 2 * K u with hSdef
  set W2 : ℝ := ∫ x, (w x) ^ 2 with hW2def
  have hW2nn : 0 ≤ W2 := by rw [hW2def]; exact integral_nonneg fun x => sq_nonneg _
  set aC : ℝ := |S| / 2 * W2.sqrt with haCdef
  have haCnn : 0 ≤ aC := by rw [haCdef]; positivity
  obtain ⟨κ, hκnn, hκ0, hκb⟩ := stepC_bound hp_meas h0 h1 hp1 hw_meas hpw hw2 hK hKmeas hKu2
  -- Choose `h₀` so that `κ h · (aC·2 + κ h) ≤ ε` for `0 < h < h₀`.
  have hev : ∀ᶠ h in nhds (0:ℝ), κ h * (2 * aC + κ h) ≤ ε := by
    have hcont : Filter.Tendsto (fun h => κ h * (2 * aC + κ h)) (nhds 0) (nhds (0 * (2 * aC + 0))) :=
      hκ0.mul (Filter.Tendsto.const_add _ hκ0)
    simp only [zero_mul] at hcont
    exact hcont.eventually_le_const hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨h₀, hh₀0, hh₀⟩ := hev
  refine ⟨h₀, hh₀0, fun h hh hhlt => ?_⟩
  -- Real quantities.
  set A : ℝ≥0∞ := eLpNorm (fun x => kmSurr w K h x) 2 volume with hAdef
  set B : ℝ≥0∞ := eLpNorm (fun x => kmBias p K h x - kmSurr w K h x) 2 volume with hBdef
  set C : ℝ≥0∞ := eLpNorm (fun x => kmBias p K h x) 2 volume with hCdef
  have hAval : A = ENNReal.ofReal (h ^ 2 * aC) := by
    rw [hAdef, eLpNorm_kmSurr hw_meas hw2, haCdef, hSdef, hW2def]; ring_nf
  have hAfin : A ≠ ⊤ := by rw [hAval]; exact ENNReal.ofReal_ne_top
  have hBb : B ≤ ENNReal.ofReal (h ^ 2 * κ h) := hκb h hh
  have hBfin : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBb
  -- Measurability.
  have hSurrmeas : AEStronglyMeasurable (fun x => kmSurr w K h x) volume :=
    ((measurable_const.mul hw_meas)).aestronglyMeasurable
  have hBiasmeas : AEStronglyMeasurable (fun x => kmBias p K h x) volume := by
    have hF : Measurable (Function.uncurry fun x u => K u * p (x + u * h)) := by
      have : Function.uncurry (fun x u => K u * p (x + u * h))
          = fun q : ℝ × ℝ => K q.2 * p (q.1 + q.2 * h) := rfl
      rw [this]; exact (hKmeas.comp measurable_snd).mul (hp_meas.comp (by fun_prop))
    have hm : Measurable (fun x => ∫ u, K u * p (x + u * h)) :=
      (hF.stronglyMeasurable).integral_prod_right'.measurable
    exact (hm.sub hp_meas).aestronglyMeasurable
  have hΔmeas : AEStronglyMeasurable (fun x => kmBias p K h x - kmSurr w K h x) volume :=
    hBiasmeas.sub hSurrmeas
  -- Triangle inequalities: `C ≤ A + B` and `A ≤ C + B`.
  have hCAB : C ≤ A + B := by
    have hsum : (fun x => kmBias p K h x)
        = (fun x => kmSurr w K h x) + (fun x => kmBias p K h x - kmSurr w K h x) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [hCdef, hsum]
    exact eLpNorm_add_le hSurrmeas hΔmeas one_le_two
  have hACB : A ≤ C + B := by
    have hsum : (fun x => kmSurr w K h x)
        = (fun x => kmBias p K h x) + (fun x => -(kmBias p K h x - kmSurr w K h x)) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [hAdef, hsum]
    have := eLpNorm_add_le hBiasmeas hΔmeas.neg (μ := volume) (p := 2) one_le_two
    rwa [eLpNorm_neg] at this
  -- Pass to reals.
  set a : ℝ := A.toReal with hadef
  set b : ℝ := B.toReal with hbdef
  set c : ℝ := C.toReal with hcdef
  have haval : a = h ^ 2 * aC := by rw [hadef, hAval, ENNReal.toReal_ofReal (by positivity)]
  have hhκnn : 0 ≤ h ^ 2 * κ h := mul_nonneg (by positivity) (hκnn h)
  have hbb : b ≤ h ^ 2 * κ h := by
    rw [hbdef]; exact (ENNReal.toReal_le_toReal hBfin ENNReal.ofReal_ne_top).2 hBb |>.trans_eq
      (ENNReal.toReal_ofReal hhκnn)
  have hCfin : C ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hAfin, hBfin⟩) hCAB
  have hca : c ≤ a + b := by
    rw [hcdef, hadef, hbdef, ← ENNReal.toReal_add hAfin hBfin]
    exact (ENNReal.toReal_le_toReal hCfin (ENNReal.add_ne_top.2 ⟨hAfin, hBfin⟩)).2 hCAB
  have hac : a ≤ c + b := by
    rw [hadef, hcdef, hbdef, ← ENNReal.toReal_add hCfin hBfin]
    exact (ENNReal.toReal_le_toReal hAfin (ENNReal.add_ne_top.2 ⟨hCfin, hBfin⟩)).2 hACB
  have hbnn : 0 ≤ b := ENNReal.toReal_nonneg
  have hcnn : 0 ≤ c := ENNReal.toReal_nonneg
  have hann : 0 ≤ a := ENNReal.toReal_nonneg
  -- `|c² − a²| ≤ b·(2a+b) ≤ h⁴·ε`.
  have hMh : h ^ 4 / 4 * S ^ 2 * W2 = a ^ 2 := by
    have hs : W2.sqrt ^ 2 = W2 := Real.sq_sqrt hW2nn
    have hab : |S| ^ 2 = S ^ 2 := sq_abs S
    rw [haval, haCdef, mul_pow, mul_pow, hs, div_pow, hab]; ring
  have hκev : κ h * (2 * aC + κ h) ≤ ε := by
    apply hh₀; rw [Real.dist_eq, sub_zero, abs_of_pos hh]; exact hhlt
  have hbound : |c ^ 2 - a ^ 2| ≤ ε * h ^ 4 := by
    have h1 : c ^ 2 - a ^ 2 ≤ b * (2 * a + b) := by nlinarith [hca, hann, hbnn, hcnn]
    have h2 : a ^ 2 - c ^ 2 ≤ b * (2 * a + b) := by nlinarith [hac, hann, hbnn, hcnn]
    have h3 : b * (2 * a + b) ≤ (h ^ 2 * κ h) * (2 * (h ^ 2 * aC) + h ^ 2 * κ h) := by
      apply mul_le_mul hbb _ (by positivity) hhκnn
      have : 2 * a + b ≤ 2 * (h ^ 2 * aC) + h ^ 2 * κ h := by rw [haval]; linarith [hbb]
      exact this
    have h4 : (h ^ 2 * κ h) * (2 * (h ^ 2 * aC) + h ^ 2 * κ h)
        = h ^ 4 * (κ h * (2 * aC + κ h)) := by ring
    rw [abs_sub_le_iff]
    have hκpos : (0:ℝ) ≤ 2 * aC + κ h := by have := hκnn h; positivity
    have hh4 : 0 ≤ h ^ 4 := by positivity
    constructor <;> nlinarith [h1, h2, h3, h4, hκev, hh4, mul_nonneg (hκnn h) hκpos]
  -- Conclude.
  have hCsq : (∫⁻ x, ENNReal.ofReal ((kmBias p K h x) ^ 2)) = ENNReal.ofReal (c ^ 2) := by
    rw [lintegral_ofReal_sq_eq_eLpNorm_sq, ← hCdef, ← ENNReal.ofReal_toReal hCfin, ← hcdef,
      ENNReal.ofReal_rpow_of_nonneg hcnn (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hCsq, hMh]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    have := abs_le.1 hbound; linarith [this.1]
  · apply ENNReal.ofReal_le_ofReal
    have := abs_le.1 hbound; linarith [this.2]

/-- **Integrated squared bias, exact asymptotics**: under the second-order smoothness
hypotheses, for every `ε > 0` there is `h₀ > 0` such that for all `0 < h < h₀`, `n ≥ 1`:
`ofReal ((h⁴/4)·S_K²·∫w² − ε·h⁴) ≤ ∫ b² ≤ ofReal ((h⁴/4)·S_K²·∫w² + ε·h⁴)`. -/
theorem kde_integrated_sq_bias_asymptotic {p K w : ℝ → ℝ}
    -- USER-INPUT: `p` is a probability density; the sampling model
    (hp_meas : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1)
    -- USER-INPUT: `p` is differentiable; second-order smoothness input
    (hp1 : Differentiable ℝ p)
    -- USER-INPUT: `p'` is absolutely continuous with a.e. derivative `w`; second-order
    -- smoothness input (the classical `p'' = w`)
    (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s)
    -- USER-INPUT: square-integrable second derivative; second-order smoothness input
    (hw2 : MemLp w 2 volume)
    -- USER-INPUT: kernel of order 1; classical input of the second-order expansion
    (hK : IsKernelOfOrder K 1)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: finite second moment of the kernel; classical input
    (hKu2 : Integrable fun u => u ^ 2 * |K u|) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ), 1 ≤ n →
        IsIIDSample P X (densityMeasure p) → (∀ i, Measurable (X i)) →
        ∀ h : ℝ, 0 < h → h < h₀ →
          ENNReal.ofReal (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) - ε * h ^ 4)
              ≤ (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2)) ∧
            (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
              ≤ ENNReal.ofReal
                  (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) + ε * h ^ 4) := by
  intro ε hε
  obtain ⟨h₀, hh₀, hcore⟩ := kmBias_asymptotic hp_meas h0 h1 hp1 hw_meas hpw hw2 hK hKmeas hKu2 ε hε
  refine ⟨h₀, hh₀, ?_⟩
  intro Ω _ P _ n X hn hs hX h hh hhlt
  -- `p` is integrable with unit `∫⁻` mass; `K` is integrable.
  have hp_int : Integrable p := by
    by_contra hni; rw [integral_undef hni] at h1; exact one_ne_zero h1.symm
  have hmass : (∫⁻ z, ENNReal.ofReal (p z)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hp_int (ae_of_all _ h0), h1, ENNReal.ofReal_one]
  have hK_int : Integrable K := by simpa using hK.integrable_pow 0 (Nat.zero_le _)
  have hKabs_int : Integrable (fun u => |K u|) := hK_int.abs
  have hn' : 0 < n := hn
  -- Tonelli: a.e.-`x` integrability of `u ↦ K u · p(x+uh)`.
  have hfmeas : Measurable (Function.uncurry
      (fun x u => ENNReal.ofReal (|K u| * p (x + u * h)))) := by
    have huc : Function.uncurry (fun x u => ENNReal.ofReal (|K u| * p (x + u * h)))
        = fun q : ℝ × ℝ => ENNReal.ofReal (|K q.2| * p (q.1 + q.2 * h)) := rfl
    rw [huc]
    exact ((Measurable.abs (hKmeas.comp measurable_snd)).mul
      (hp_meas.comp (by fun_prop))).ennreal_ofReal
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
  -- a.e.-`x`, `kdeBiasAt = kmBias`.
  have hbias_ae : ∀ᵐ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2)
      = ENNReal.ofReal ((kmBias p K h x) ^ 2) := by
    filter_upwards [haex] with x hx
    have hKp : Integrable (fun u => K u * p (x + u * h)) := by
      refine ⟨(hKmeas.mul (hp_meas.comp (by fun_prop))).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      rw [lintegral_congr fun u => by
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (h0 _)]]
      exact hx
    have hmean : kdeMeanAt P X K h x = ∫ u, K u * p (x + u * h) :=
      kdeMeanAt_eq_integral_kernel hn' hh hs hp_meas h0 hKmeas hKp
    rw [show kdeBiasAt P X K h p x = kmBias p K h x from by
      rw [kdeBiasAt, hmean, kmBias]]
  rw [lintegral_congr_ae hbias_ae]
  exact hcore h hh hhlt

end StatLean.NonparametricStatistics
