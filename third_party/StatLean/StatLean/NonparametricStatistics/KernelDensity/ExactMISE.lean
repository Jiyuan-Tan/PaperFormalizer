module
public import StatLean.NonparametricStatistics.KernelDensity.MISEVariance
public import StatLean.NonparametricStatistics.KernelDensity.MISEBias

@[expose] public section

/-!
# Exact asymptotic MISE of the kernel density estimator

For a twice (weakly) differentiable density and a kernel of order `1` with `S_K = ∫u²K ≠ 0`:
$$ \mathrm{MISE} \;=\; \Bigl(\frac{1}{nh}\int K^2
     + \frac{h^4}{4}\,S_K^2\int (p'')^2\Bigr)\bigl(1 + o(1)\bigr), $$
with `o(1)` independent of `n` and vanishing as `h → 0`. Minimizing the main term in `h` (and
then over nonnegative kernels) is the classical route to the optimal-bandwidth formula and to
the parabolic (Epanechnikov) kernel; the theorem is stated here in the ε-form
$$ \bigl|\mathrm{MISE} - A(n,h)\bigr| \;\le\; \varepsilon\,\Bigl(\frac{1}{nh} + h^4\Bigr),
   \qquad 0 < h < h_0(\varepsilon),\ n \ge 1, $$
which is equivalent to the multiplicative form because `A(n,h) ≍ (nh)⁻¹ + h⁴` (both
coefficients `∫K² > 0` and `S_K²∫(p'')² > 0` are bounded away from zero; the equivalence is
recorded in the batch ledger).

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.3, Proposition 1.6 (exact asymptotic MISE;
proof in the Appendix, Proposition A.1).

**Proof formalization notes.** MISE decomposes exactly as `∫b² + ∫σ²`
(`kdeMise_eq_integrated`, Tonelli plus the a.e.-`x` bias–variance decomposition); the variance
part is pinned by `kde_integrated_variance_le` / `kde_integrated_variance_ge` (correction
`O(1/n) ≤ (nh)·h·…` absorbed into `ε/(nh)` for small `h`), and the bias part by
`kde_integrated_sq_bias_asymptotic`. The `L²` hypothesis on `p` feeding the variance lower
bound is inherited (documented input).

**Bibliographic comments.** G. S. Watson and M. R. Leadbetter, *Ann. Math. Statist.* **34**
(1963), 480–491 (exact MISE); M. S. Bartlett, *Sankhyā Ser. A* **25** (1963), 245–254, and
V. A. Epanechnikov, *Theory Probab. Appl.* **14** (1969), 153–158 (second-order form and
optimal kernel); the fixed-density optimality critique built on this expansion is due to
L. D. Brown, M. G. Low and L. H. Zhao, "Superefficiency in nonparametric function estimation,"
*Ann. Statist.* **25** (1997), 2607–2625.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- Integrability transfer along the law (replica of the `Variance.lean` helper). -/
private lemma integrable_comp_law_em {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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

/-- Affine (reflect–scale) change of variables in `∫⁻`: for `h > 0`,
`∫⁻ x, F ((z − x)/h) dx = h · ∫⁻ y, F y dy`. -/
private lemma lintegral_kernel_shift_em {F : ℝ → ℝ≥0∞} (hF : Measurable F) {h : ℝ} (hh : 0 < h)
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

/-- For a general density and square-integrable kernel, the estimator is `L²` for a.e. `x`. -/
private lemma kde_memLp_two_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ}
    (hn : 0 < n) (hh : 0 < h) (hs : IsIIDSample P X (densityMeasure p))
    (hX : ∀ i, Measurable (X i)) (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (hK : Measurable K) (hK2 : Integrable fun u => (K u) ^ 2) :
    ∀ᵐ x, MemLp (fun ω => kde X K h ω x) 2 P := by
  have hprob : IsProbabilityMeasure (densityMeasure p) := by
    rw [← (hs.law ⟨0, hn⟩).map_eq]
    exact Measure.isProbabilityMeasure_map (hs.law ⟨0, hn⟩).aemeasurable
  have hmass : (∫⁻ z, ENNReal.ofReal (p z)) = 1 := by
    have h := hprob.measure_univ
    rwa [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  have hΦmeas : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal ((K ((q.2 - q.1) / h)) ^ 2) * ENNReal.ofReal (p q.2)) :=
    (((hK.comp ((measurable_snd.sub measurable_fst).div_const h)).pow_const 2).ennreal_ofReal).mul
      ((hp.comp measurable_snd).ennreal_ofReal)
  have hGℓmeas : Measurable fun x => ∫⁻ z,
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) :=
    hΦmeas.lintegral_prod_right'
  have hD : (∫⁻ x, ∫⁻ z, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z))
      = ENNReal.ofReal h * ENNReal.ofReal (∫ u, (K u) ^ 2) := by
    rw [lintegral_lintegral_swap (f := fun x z =>
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z)) hΦmeas.aemeasurable]
    have hinner : ∀ z, (∫⁻ x, ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z))
        = ENNReal.ofReal h * ENNReal.ofReal (∫ u, (K u) ^ 2) * ENNReal.ofReal (p z) := by
      intro z
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      congr 1
      rw [lintegral_kernel_shift_em ((hK.pow_const 2).ennreal_ofReal) hh z]
      congr 1
      exact (ofReal_integral_eq_lintegral_ofReal hK2 (ae_of_all _ fun u => sq_nonneg _)).symm
    rw [lintegral_congr hinner,
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      hmass, mul_one]
  have hGℓfin : ∀ᵐ x, (∫⁻ z,
      ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z)) < ⊤ := by
    refine ae_lt_top hGℓmeas ?_
    rw [hD]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  filter_upwards [hGℓfin] with x hx
  have hGmeas : Measurable (fun z => (K ((z - x) / h)) ^ 2) :=
    (hK.comp ((measurable_id.sub_const x).div_const h)).pow_const 2
  have hnn : 0 ≤ᵐ[volume] fun z => (K ((z - x) / h)) ^ 2 * p z :=
    ae_of_all _ fun z => mul_nonneg (sq_nonneg _) (h0 z)
  have hIntGp : Integrable (fun z => (K ((z - x) / h)) ^ 2 * p z) volume := by
    refine ⟨(hGmeas.mul hp).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    have hcongr : (fun z => ENNReal.ofReal ((K ((z - x) / h)) ^ 2 * p z))
        = fun z => ENNReal.ofReal ((K ((z - x) / h)) ^ 2) * ENNReal.ofReal (p z) := by
      funext z; rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [hcongr]; exact hx
  have hmemP : ∀ i, MemLp (fun ω => K ((X i ω - x) / h)) 2 P := by
    intro i
    have haesm : AEStronglyMeasurable (fun ω => K ((X i ω - x) / h)) P :=
      (hK.comp (((hX i).sub_const x).div_const h)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq haesm]
    exact integrable_comp_law_em (g := fun z => (K ((z - x) / h)) ^ 2)
      (hs.law i) hp h0 hGmeas hIntGp
  have hfun : (∑ i : Fin n, fun ω => K ((X i ω - x) / h))
      = fun ω => ∑ i, K ((X i ω - x) / h) := by funext ω; simp only [Finset.sum_apply]
  have hsum : MemLp (fun ω => ∑ i, K ((X i ω - x) / h)) 2 P := by
    rw [← hfun]; exact memLp_finset_sum' _ (fun i _ => hmemP i)
  exact hsum.const_mul ((n : ℝ) * h)⁻¹

/-- The main term of the exact asymptotic MISE:
`A(n, h) = (nh)⁻¹·∫K² + (h⁴/4)·(∫u²K)²·∫w²`. -/
noncomputable def kdeMiseMain (K w : ℝ → ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  ((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2)
    + h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * ∫ x, (w x) ^ 2

/-- **Exact MISE decomposition**: `MISE = ∫ b²(x) dx + ∫ σ²(x) dx` (Tonelli plus the
pointwise bias–variance decomposition, valid a.e. in `x`). -/
theorem kdeMise_eq_integrated {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ}
    -- LEAN-ONLY: nonempty sample and positive bandwidth; standard side conditions
    (hn : 0 < n) (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability; standard regularity
    (hX : ∀ i, Measurable (X i)) (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (hK : Measurable K)
    -- USER-INPUT: integrable and square-integrable kernel; classical inputs
    (hK1 : Integrable K) (hK2 : Integrable fun u => (K u) ^ 2) :
    kdeMise P X K h p
      = (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
        + ∫⁻ x, kdeVarianceAt P X K h x := by
  -- Joint measurability of the estimator and the mean, for Tonelli and the sum split.
  have hjoint : Measurable (fun q : Ω × ℝ => kde X K h q.1 q.2) := by
    simp only [kde, kdeData]
    refine measurable_const.mul (Finset.measurable_sum _ (fun i _ => ?_))
    exact hK.comp (((hX i).comp measurable_fst).sub measurable_snd |>.div_const h)
  have hjkde : Measurable (fun q : ℝ × Ω => kde X K h q.2 q.1) := by
    simp only [kde, kdeData]
    refine measurable_const.mul (Finset.measurable_sum _ (fun i _ => ?_))
    exact hK.comp (((hX i).comp measurable_snd).sub measurable_fst |>.div_const h)
  have hmeanAtmeas : Measurable (fun x => kdeMeanAt P X K h x) :=
    (hjkde.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hbiasmeas : Measurable (fun x => ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2)) := by
    have : Measurable (fun x => kdeBiasAt P X K h p x) := hmeanAtmeas.sub hp
    exact (this.pow_const 2).ennreal_ofReal
  -- Tonelli swap: `MISE = ∫⁻ x, MSE(x)`.
  have hswapmeas : Measurable (Function.uncurry
      (fun ω x => ENNReal.ofReal ((kde X K h ω x - p x) ^ 2))) := by
    have huc : Function.uncurry (fun ω x => ENNReal.ofReal ((kde X K h ω x - p x) ^ 2))
        = fun q : Ω × ℝ => ENNReal.ofReal ((kde X K h q.1 q.2 - p q.2) ^ 2) := rfl
    rw [huc]
    exact ((hjoint.sub (hp.comp measurable_snd)).pow_const 2).ennreal_ofReal
  have hswap : kdeMise P X K h p = ∫⁻ x, kdeMseAt P X K h p x := by
    unfold kdeMise kdeMseAt
    rw [lintegral_lintegral_swap (f := fun ω x =>
      ENNReal.ofReal ((kde X K h ω x - p x) ^ 2)) hswapmeas.aemeasurable]
  rw [hswap]
  -- A.e.-`x` bias–variance decomposition of the pointwise MSE.
  have hae : ∀ᵐ x, kdeMseAt P X K h p x
      = ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2) + kdeVarianceAt P X K h x := by
    filter_upwards [kde_memLp_two_ae hn hh hs hX hp h0 hK hK2] with x hL2
    exact kdeMseAt_eq_bias_sq_add_variance hL2
  rw [lintegral_congr_ae hae, lintegral_add_left hbiasmeas]

/-- **Exact asymptotic MISE**: under second-order smoothness of `p` and a kernel of order `1`
with `S_K ≠ 0`, for every `ε > 0` there is `h₀ > 0` such that for all `0 < h < h₀` and all
`n ≥ 1` (uniformly in `n`):
`ofReal (A(n,h) − ε·((nh)⁻¹ + h⁴)) ≤ MISE ≤ ofReal (A(n,h) + ε·((nh)⁻¹ + h⁴))`,
where `A = kdeMiseMain K w n h`. -/
theorem kde_exact_mise {p K w : ℝ → ℝ}
    -- USER-INPUT: `p` is a probability density; the sampling model
    (hp_meas : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1)
    -- USER-INPUT: `p` is differentiable with absolutely continuous derivative and a.e.
    -- second derivative `w`; second-order smoothness inputs
    (hp1 : Differentiable ℝ p) (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s)
    -- USER-INPUT: square-integrable second derivative; second-order smoothness input
    (hw2 : MemLp w 2 volume)
    -- USER-INPUT: square-integrable density; input of the exact variance asymptotics
    -- (documented: derivable in principle, kept as an input in this batch)
    (hp2 : MemLp p 2 volume)
    -- USER-INPUT: kernel of order 1 with nonvanishing second moment `S_K ≠ 0`; classical
    -- inputs of the second-order expansion
    (hK : IsKernelOfOrder K 1) (hSK : (∫ u, u ^ 2 * K u) ≠ 0)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: square-integrable kernel and finite second moment; classical inputs
    (hK2 : Integrable fun u => (K u) ^ 2) (hKu2 : Integrable fun u => u ^ 2 * |K u|) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ), 1 ≤ n →
        IsIIDSample P X (densityMeasure p) → (∀ i, Measurable (X i)) →
          ENNReal.ofReal (kdeMiseMain K w n h - ε * (((n : ℝ) * h)⁻¹ + h ^ 4))
              ≤ kdeMise P X K h p ∧
            kdeMise P X K h p
              ≤ ENNReal.ofReal (kdeMiseMain K w n h + ε * (((n : ℝ) * h)⁻¹ + h ^ 4)) := by
  have hK1 : Integrable K := by
    have := hK.integrable_pow 0 (Nat.zero_le _); simpa using this
  intro ε hε
  -- Bias part: the exact asymptotic at tolerance `ε/2`.
  obtain ⟨h₀b, hh₀b, hbias⟩ := kde_integrated_sq_bias_asymptotic hp_meas h0 h1 hp1 hw_meas hpw hw2 hK
    hKmeas hKu2 (ε / 2) (by positivity)
  set C : ℝ := (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2 with hCdef
  have hCnn : (0 : ℝ) ≤ C :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  refine ⟨min h₀b (ε / (2 * (C + 1))), lt_min hh₀b (by positivity), ?_⟩
  intro h hh hlt Ω _ P _ n X hn1 hs hXmeas
  have hn : 0 < n := hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt_bias : h < h₀b := lt_of_lt_of_le hlt (min_le_left _ _)
  have hlt_corr : h < ε / (2 * (C + 1)) := lt_of_lt_of_le hlt (min_le_right _ _)
  -- Nonnegativity facts.
  have hV0 : (0 : ℝ) ≤ ((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2 :=
    mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _)
  have hMb0 : (0 : ℝ) ≤ h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * ∫ x, (w x) ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (integral_nonneg fun x => sq_nonneg _)
  have hD0 : (0 : ℝ) ≤ ((n : ℝ) * h)⁻¹ := by positivity
  have hh40 : (0 : ℝ) ≤ h ^ 4 := by positivity
  -- Correction smallness: `n⁻¹·C ≤ (ε/2)·(nh)⁻¹`.
  have hhC : h * C ≤ ε / 2 := by
    have hden : (0 : ℝ) < 2 * (C + 1) := by positivity
    have := (lt_div_iff₀ hden).mp hlt_corr
    nlinarith [hCnn, hε.le, this]
  have hCle : C ≤ ε / 2 / h := (le_div_iff₀ hh).mpr (by nlinarith [hhC])
  have hcorr : (n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2 ≤ ε / 2 * ((n : ℝ) * h)⁻¹ := by
    calc (n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2 = (n : ℝ)⁻¹ * C := by rw [hCdef]; ring
      _ ≤ (n : ℝ)⁻¹ * (ε / 2 / h) := mul_le_mul_of_nonneg_left hCle (by positivity)
      _ = ε / 2 * ((n : ℝ) * h)⁻¹ := by rw [mul_inv]; field_simp
  -- MISE decomposition and the three integral bounds.
  have hdecomp := kdeMise_eq_integrated hn hh hs hXmeas hp_meas h0 hKmeas hK1 hK2
  obtain ⟨hbl, hbu⟩ := hbias P X hn1 hs hXmeas h hh hlt_bias
  have hvle := kde_integrated_variance_le hh hs hXmeas hp_meas h0 hKmeas hK2
  have hvge := kde_integrated_variance_ge hn hh hs hXmeas hp_meas h0 hp2 hKmeas hK1 hK2
  rw [hdecomp]
  simp only [kdeMiseMain]
  constructor
  · -- Lower bound.
    calc ENNReal.ofReal ((((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2)
            + h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2)
            - ε * (((n : ℝ) * h)⁻¹ + h ^ 4))
        ≤ ENNReal.ofReal ((h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) - ε / 2 * h ^ 4)
            + (((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2)
              - (n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [hcorr, hε.le, hD0, hh40, mul_nonneg hε.le hD0, mul_nonneg hε.le hh40]
      _ ≤ ENNReal.ofReal (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) - ε / 2 * h ^ 4)
            + ENNReal.ofReal (((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2)
              - (n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2) := ENNReal.ofReal_add_le
      _ ≤ (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
            + ∫⁻ x, kdeVarianceAt P X K h x := add_le_add hbl hvge
  · -- Upper bound.
    calc (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
            + ∫⁻ x, kdeVarianceAt P X K h x
        ≤ ENNReal.ofReal (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) + ε / 2 * h ^ 4)
            + ENNReal.ofReal (((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2) := add_le_add hbu hvle
      _ = ENNReal.ofReal ((h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) + ε / 2 * h ^ 4)
            + ((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2) :=
          (ENNReal.ofReal_add (by nlinarith [hMb0, hε.le, hh40]) hV0).symm
      _ ≤ ENNReal.ofReal ((((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2)
            + h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2)
            + ε * (((n : ℝ) * h)⁻¹ + h ^ 4)) := by
          apply ENNReal.ofReal_le_ofReal; nlinarith [hD0, hh40, hε.le]

end StatLean.NonparametricStatistics
