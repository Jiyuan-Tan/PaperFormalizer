module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-!
# Generalized Minkowski integral inequality (L² form)

For a jointly measurable `g : α → β → ℝ≥0∞` and σ-finite measures `μ, ν`:
$$ \Bigl(\int \Bigl(\int g(u,x)\,d\mu(u)\Bigr)^2 d\nu(x)\Bigr)^{1/2}
   \;\le\; \int \Bigl(\int g(u,x)^2\,d\nu(x)\Bigr)^{1/2} d\mu(u). $$

"The `L²(ν)`-norm of an integral is at most the integral of the `L²(ν)`-norms" — the
continuous analogue of the triangle inequality, used to push `L²` moduli of continuity through
kernel-weighted integrals in the integrated-bias analysis of kernel estimators.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.3, Lemma 1.1 (generalized Minkowski
inequality; proof in the Appendix, Lemma A.1).

**Proof formalization notes.** Stated for `ℝ≥0∞`-valued integrands (the applications are
absolute values of real functions, inserted via `ENNReal.ofReal`), so no integrability side
conditions are needed. Proof route: the classical `L²` duality argument — for `S(x) = ∫ g(u,x)
dμ(u)`, bound `∫ S·φ dν` for `φ` in the unit ball of `L²(ν)` by Tonelli–Fubini
(`lintegral_lintegral_swap`) and the Cauchy–Schwarz inequality for `∫⁻`
(`ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`), then take `φ = S/‖S‖₂` (or argue via
`ENNReal.rpow` algebra directly). Alternatively search for a Mathlib `eLpNorm`-level Minkowski
integral inequality first — if one exists on the pin, this lemma is a thin wrapper.

**Bibliographic comments.** H. Minkowski, *Geometrie der Zahlen* (Leipzig, 1896); the integral
form is classical, see G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities* (Cambridge,
1934), Theorem 202.
-/

open MeasureTheory Function Set
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- The `L²` duality bound: testing `S(x) = ∫ g(u,x) dμ(u)` against an arbitrary measurable `φ`
gives the Cauchy–Schwarz estimate, after Tonelli and the `ℝ≥0∞` Cauchy–Schwarz inequality. -/
private lemma minkowski_duality_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    {g : α → β → ℝ≥0∞} (hg : Measurable (uncurry g))
    {φ : β → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ x, (∫⁻ u, g u x ∂μ) * φ x ∂ν)
      ≤ (∫⁻ u, (∫⁻ x, (g u x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ∂μ)
          * (∫⁻ x, (φ x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
  have hFmeas : Measurable fun u => (∫⁻ x, (g u x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((ENNReal.continuous_rpow_const.measurable.comp hg).lintegral_prod_right')
  calc (∫⁻ x, (∫⁻ u, g u x ∂μ) * φ x ∂ν)
      = ∫⁻ x, ∫⁻ u, g u x * φ x ∂μ ∂ν := by
        refine lintegral_congr fun x => ?_
        exact (lintegral_mul_const'' (φ x)
          (hg.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm
    _ = ∫⁻ u, ∫⁻ x, g u x * φ x ∂ν ∂μ :=
        lintegral_lintegral_swap (f := fun x u => g u x * φ x)
          (((hg.comp measurable_swap).mul (hφ.comp measurable_fst)).aemeasurable)
    _ ≤ ∫⁻ u, (∫⁻ x, (g u x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)
            * (∫⁻ x, (φ x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ∂μ := by
        refine lintegral_mono fun u => ?_
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
          (hg.comp (measurable_const.prodMk measurable_id)).aemeasurable hφ.aemeasurable
    _ = (∫⁻ u, (∫⁻ x, (g u x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ∂μ)
            * (∫⁻ x, (φ x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) :=
        lintegral_mul_const'' _ hFmeas.aemeasurable

/-- Abstract core of the Minkowski argument: if `S` is measurable and satisfies the `L²` duality
bound with constant `R`, then `∫ S² ≤ R²`. Proved by monotone truncation of `S` (via a spanning
sequence of finite-measure sets), so no finiteness of `∫ S²` is needed. -/
private lemma sq_lintegral_le_of_duality {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [SigmaFinite ν] (S : β → ℝ≥0∞) (hSmeas : Measurable S) (R : ℝ≥0∞)
    (hduality : ∀ φ : β → ℝ≥0∞, Measurable φ →
        (∫⁻ x, S x * φ x ∂ν) ≤ R * (∫⁻ x, (φ x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) :
    (∫⁻ x, (S x) ^ 2 ∂ν) ≤ R ^ 2 := by
  classical
  set B : ℕ → Set β := spanningSets ν with hB
  set Φ : ℕ → β → ℝ≥0∞ :=
    fun m x => (B m).indicator (fun x => min (S x) (m : ℝ≥0∞)) x with hΦ
  have hBmeas : ∀ m, MeasurableSet (B m) := fun m => measurableSet_spanningSets ν m
  have hΦmeas : ∀ m, Measurable (Φ m) := fun m =>
    (hSmeas.min measurable_const).indicator (hBmeas m)
  have hΦle : ∀ m x, Φ m x ≤ S x := by
    intro m x; simp only [hΦ, Set.indicator_apply]
    split_ifs with h
    · exact min_le_left _ _
    · exact zero_le
  have hsup : ∀ x, ⨆ m, Φ m x = S x := by
    intro x
    refine le_antisymm (iSup_le fun m => hΦle m x) ?_
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨m₀, hm₀⟩ := iUnion_eq_univ_iff.1 (iUnion_spanningSets ν) x
    obtain ⟨m₁, hm₁⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    have hxB : x ∈ B (max m₀ m₁) := monotone_spanningSets ν (le_max_left m₀ m₁) hm₀
    have hcm : c < (max m₀ m₁ : ℕ) := hm₁.trans_le (by exact_mod_cast le_max_right m₀ m₁)
    have hlt : c < Φ (max m₀ m₁) x := by
      simp only [hΦ, Set.indicator_of_mem hxB]; exact lt_min hc hcm
    exact hlt.trans_le (le_iSup (fun m => Φ m x) (max m₀ m₁))
  have hΦmono : Monotone Φ := by
    intro m n hmn x; simp only [hΦ, Set.indicator_apply]
    split_ifs with h1 h2
    · exact min_le_min le_rfl (by exact_mod_cast hmn)
    · exact absurd (monotone_spanningSets ν hmn h1) h2
    · exact zero_le
    · exact le_rfl
  have hΘmeas : ∀ m, Measurable fun x => S x * Φ m x := fun m => hSmeas.mul (hΦmeas m)
  have hΘmono : Monotone fun m => fun x => S x * Φ m x := by
    intro m n hmn x; exact mul_le_mul_right (hΦmono hmn x) (S x)
  have hΘsup : ∀ x, (⨆ m, S x * Φ m x) = (S x) ^ 2 := by
    intro x; rw [← ENNReal.mul_iSup, hsup x, sq]
  calc (∫⁻ x, (S x) ^ 2 ∂ν)
      = ∫⁻ x, ⨆ m, S x * Φ m x ∂ν := lintegral_congr fun x => (hΘsup x).symm
    _ = ⨆ m, ∫⁻ x, S x * Φ m x ∂ν := lintegral_iSup hΘmeas hΘmono
    _ ≤ R ^ 2 := iSup_le fun m => ?_
  -- Per-index bound `∫ S·Φ m ≤ R²`.
  set am : ℝ≥0∞ := ∫⁻ x, (Φ m x) ^ (2 : ℝ) ∂ν with ham
  have hamfin : am ≠ ⊤ := by
    have hle : am ≤ (m : ℝ≥0∞) ^ (2 : ℝ) * ν (B m) := by
      calc am ≤ ∫⁻ x, (B m).indicator (fun _ => (m : ℝ≥0∞) ^ (2 : ℝ)) x ∂ν := by
              refine lintegral_mono fun x => ?_
              simp only [hΦ, Set.indicator_apply]
              split_ifs with h
              · exact ENNReal.rpow_le_rpow (min_le_right _ _) (by norm_num)
              · rw [ENNReal.zero_rpow_of_pos (by norm_num)]
        _ = (m : ℝ≥0∞) ^ (2 : ℝ) * ν (B m) := lintegral_indicator_const (hBmeas m) _
    refine ne_top_of_le_ne_top ?_ hle
    exact ENNReal.mul_ne_top
      (by rw [ENNReal.rpow_two]; exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top m))
      (measure_spanningSets_lt_top ν m).ne
  have hlow : am ≤ ∫⁻ x, S x * Φ m x ∂ν := by
    rw [ham]; refine lintegral_mono fun x => ?_
    rw [ENNReal.rpow_two, sq]; exact mul_le_mul_left (hΦle m x) (Φ m x)
  have hup : (∫⁻ x, S x * Φ m x ∂ν) ≤ R * am ^ (1 / 2 : ℝ) := hduality (Φ m) (hΦmeas m)
  have ham2 : am ≤ R * am ^ (1 / 2 : ℝ) := hlow.trans hup
  have hsqrtle : am ^ (1 / 2 : ℝ) ≤ R := by
    by_cases h0 : am = 0
    · simp [h0, ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    · set t := am ^ (1 / 2 : ℝ) with ht
      have htfin : t ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hamfin).ne
      have htt : t * t = am := by
        rw [ht, ← pow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
          show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
      have htne0 : t ≠ 0 := fun h => h0 (by rw [← htt, h, zero_mul])
      have hcancel : t * t ≤ R * t := by rw [htt]; exact ham2
      exact (ENNReal.mul_le_mul_iff_left htne0 htfin).1 hcancel
  calc (∫⁻ x, S x * Φ m x ∂ν) ≤ R * am ^ (1 / 2 : ℝ) := hup
    _ ≤ R * R := mul_le_mul_right hsqrtle R
    _ = R ^ 2 := (sq R).symm

/-- **Generalized Minkowski inequality, `L²` form** (for `ℝ≥0∞`-valued integrands):
`‖∫ g(u, ·) dμ(u)‖_{L²(ν)} ≤ ∫ ‖g(u, ·)‖_{L²(ν)} dμ(u)`. -/
theorem lintegral_lintegral_sq_rpow_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    {g : α → β → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability, needed for the Tonelli–Fubini swap; standard
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ x, (∫⁻ u, g u x ∂μ) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ u, (∫⁻ x, (g u x) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ := by
  set R : ℝ≥0∞ := ∫⁻ u, (∫⁻ x, (g u x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ∂μ with hR
  have hkey : (∫⁻ x, (∫⁻ u, g u x ∂μ) ^ 2 ∂ν) ≤ R ^ 2 :=
    sq_lintegral_le_of_duality ν (fun x => ∫⁻ u, g u x ∂μ) hg.lintegral_prod_left R
      (fun φ hφ => minkowski_duality_bound μ ν hg hφ)
  calc (∫⁻ x, (∫⁻ u, g u x ∂μ) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ≤ (R ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hkey (by norm_num)
    _ = R := by
        rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
          ENNReal.rpow_one]
    _ = ∫⁻ u, (∫⁻ x, (g u x) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ := by
        rw [hR]; simp only [ENNReal.rpow_two]

end StatLean.NonparametricStatistics
