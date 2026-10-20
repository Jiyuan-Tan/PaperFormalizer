module
public import StatLean.RobustStatistics.MaxBias.MaxBiasLocation
public import StatLean.RobustStatistics.Core.Equivariance
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-!
# The minimax-bias property of the median (Huber)

The classical capstone of maximum-bias theory (`MMY §3.8.5`, after Huber (1964)): over
a symmetric *unimodal* center `F₀`, **no location-equivariant functional has smaller
maximum bias than the median**. The witness pair is explicit: `F₊` keeps the density
`(1−ε)f₀` up to the median's own maximum bias `b_ε` (`MMY (3.68)`) and pastes the
shifted density `(1−ε)f₀(· − 2b_ε)` beyond it; `F₋` is `F₊` shifted left by `2b_ε`.
Both are `ε`-contaminations of `F₀` — nonnegativity of the contaminating density is
exactly unimodality, its total mass is exactly the quantile equation — and location
equivariance forces `T(F₊) − T(F₋) = 2b_ε`, so one of the two values is at least `b_ε`
in absolute value.

* `minimaxWitnessDensity` — the contaminating density `g` of `MMY §3.8.5`.
* `minimaxWitnessDensity_nonneg` / `integral_minimaxWitnessDensity` — `g` is a density.
* `medianMinimaxPlus_eq_contaminate` — `F₊ ∈ F(F₀, ε)`.
* `medianMinimaxMinus_eq_contaminate` — `F₋ = F₊(· + 2b_ε) ∈ F(F₀, ε)`.
* `locationEquivariant_maxBias_ge_median` — the pigeonhole conclusion.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.)
§3.8.5 ("The minimax bias property of the median"), using (3.68); the result is
P. J. Huber, *Robust estimation of a location parameter*, Ann. Math. Statist. 35
(1964) (bib note).

**Bibliographic comments.** The minimax-bias property of the median is P. J. Huber, "Robust
estimation of a location parameter," *Ann. Math. Statist.* **35** (1964), 73–101 (see also
Huber–Ronchetti 2009, §4.2: the median minimizes the maximum asymptotic bias among
translation-equivariant functionals over symmetric unimodal centers); generalizations
beyond location are He and Simpson, *Ann. Statist.* **21** (1993), 314–337.
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- The symmetric unimodal center as a Lebesgue density measure: `P₀ = f₀ · Leb`. -/
noncomputable def densityMeasure (f₀ : ℝ → ℝ) : Measure ℝ :=
  MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (f₀ x)

/-! ### Private density plumbing

Three reusable bricks: a density measure with total mass one is a probability measure, a
mixture of two Lebesgue densities is the `contaminate` mixture of the two density measures,
and translating a density measure translates its density. All three are stated privately so
the frozen statements above stay untouched. -/

/-- A nonnegative integrable density of total mass one gives a probability measure. -/
private theorem isProbabilityMeasure_densityMeasure {u : ℝ → ℝ}
    (hint : Integrable u) (hu0 : ∀ x, 0 ≤ u x) (hmass : ∫ x, u x = 1) :
    IsProbabilityMeasure (densityMeasure u) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hu0), hmass,
    ENNReal.ofReal_one]

/-- The mixture of two Lebesgue densities is the `contaminate` mixture of the density
measures (`MMY §3.8.5`, "`f₊ = (1−ε)f₀ + εg`" at the level of measures). -/
private theorem densityMeasure_mixture {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    densityMeasure (fun x => (1 - ε) * u x + ε * v x)
      = contaminate (densityMeasure u) (densityMeasure v) ε := by
  have h1 : (0:ℝ) ≤ 1 - ε := by linarith
  refine Measure.ext fun s hs => ?_
  rw [densityMeasure, withDensity_apply _ hs, contaminate_apply, densityMeasure, densityMeasure,
    withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_const_mul _ hu.ennreal_ofReal, ← lintegral_const_mul _ hv.ennreal_ofReal,
    ← lintegral_add_left (hu.ennreal_ofReal.const_mul _)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_add (mul_nonneg h1 (hu0 x)) (mul_nonneg hε (hv0 x)),
    ENNReal.ofReal_mul h1, ENNReal.ofReal_mul hε]

/-- Translating a Lebesgue density measure translates its density (Lebesgue measure is
translation invariant). -/
private theorem map_add_densityMeasure (u : ℝ → ℝ) (c : ℝ) :
    (densityMeasure u).map (· + c) = densityMeasure (fun x => u (x - c)) := by
  refine Measure.ext fun s hs => ?_
  have hsc : MeasurableSet ((fun x : ℝ => x + c) ⁻¹' s) := (measurable_add_const c) hs
  have e1 : ((densityMeasure u).map (· + c)) s
      = ∫⁻ x, Set.indicator ((fun x : ℝ => x + c) ⁻¹' s)
          (fun y => ENNReal.ofReal (u y)) x := by
    rw [Measure.map_apply (measurable_add_const c) hs, densityMeasure,
      withDensity_apply _ hsc, ← lintegral_indicator hsc]
  have e2 : (densityMeasure fun x => u (x - c)) s
      = ∫⁻ x, Set.indicator s (fun y => ENNReal.ofReal (u (y - c))) x := by
    rw [densityMeasure, withDensity_apply _ hs, ← lintegral_indicator hs]
  have e3 : ∫⁻ x, Set.indicator s (fun y => ENNReal.ofReal (u (y - c))) x
      = ∫⁻ x, Set.indicator s (fun y => ENNReal.ofReal (u (y - c))) (x + c) :=
    (lintegral_add_right_eq_self
      (fun x => Set.indicator s (fun y => ENNReal.ofReal (u (y - c))) x) c).symm
  rw [e1, e2, e3]
  refine lintegral_congr fun x => ?_
  by_cases hx : x + c ∈ s
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem (show x ∈ (fun x : ℝ => x + c) ⁻¹' s from hx)]
    simp
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x ∉ (fun x : ℝ => x + c) ⁻¹' s from hx)]

/-- **The minimax witness density** (`MMY §3.8.5`, the display for `g`):
`g(x) = ((1−ε)/ε) (f₀(x − 2b_ε) − f₀(x))` for `x > b_ε` and `0` otherwise. -/
noncomputable def minimaxWitnessDensity (f₀ : ℝ → ℝ) (bε ε : ℝ) (x : ℝ) : ℝ :=
  if bε < x then (1 - ε) / ε * (f₀ (x - 2 * bε) - f₀ x) else 0

/-- **The witness density is nonnegative** (`MMY §3.8.5`, "it is nonnegative, since
`x ∈ (b_ε, 2b_ε)` implies `|x − 2b_ε| ≤ |x|`, and the unimodality of `f₀` yields
`f₀(x − 2b_ε) ≥ f₀(x)`; the same happens if `x > 2b_ε`"). -/
theorem minimaxWitnessDensity_nonneg {f₀ : ℝ → ℝ} {bε ε : ℝ}
    -- USER-INPUT: symmetric unimodal density; MMY §3.8.5 ("f₀(x) a nonincreasing
    -- function of |x|")
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1) (x : ℝ) :
    0 ≤ minimaxWitnessDensity f₀ bε ε x := by
  rw [minimaxWitnessDensity]
  split_ifs with h
  · -- `|x − 2b_ε| ≤ |x|` for `x > b_ε ≥ 0`, so unimodality gives `f₀(x − 2b_ε) ≥ f₀ x`.
    have hmono : f₀ x ≤ f₀ (x - 2 * bε) := by
      rcases le_or_gt 0 (x - 2 * bε) with hx | hx
      · exact huni _ _ hx (by linarith)
      · have hrefl : f₀ (x - 2 * bε) = f₀ (2 * bε - x) := by
          rw [show (2 * bε - x) = -(x - 2 * bε) by ring, hsym]
        rw [hrefl]
        exact huni _ _ (by linarith) (by linarith)
    exact mul_nonneg (div_nonneg (by linarith) hε.le) (by linarith)
  · exact le_refl 0

/-- The witness density is the `(b_ε, ∞)`-indicator of the density difference. -/
private theorem minimaxWitnessDensity_eq_indicator (f₀ : ℝ → ℝ) (bε ε : ℝ) :
    minimaxWitnessDensity f₀ bε ε
      = Set.indicator (Set.Ioi bε) fun x => (1 - ε) / ε * (f₀ (x - 2 * bε) - f₀ x) := by
  funext x
  simp [minimaxWitnessDensity, Set.indicator_apply, Set.mem_Ioi]

private theorem measurable_minimaxWitnessDensity {f₀ : ℝ → ℝ} (hmeas : Measurable f₀)
    (bε ε : ℝ) : Measurable (minimaxWitnessDensity f₀ bε ε) := by
  rw [minimaxWitnessDensity_eq_indicator]
  exact Measurable.indicator
    (measurable_const.mul ((hmeas.comp (measurable_id.sub_const (2 * bε))).sub hmeas))
    measurableSet_Ioi

private theorem integrable_minimaxWitnessDensity {f₀ : ℝ → ℝ} (hint : Integrable f₀)
    (bε ε : ℝ) : Integrable (minimaxWitnessDensity f₀ bε ε) := by
  rw [minimaxWitnessDensity_eq_indicator]
  exact (((hint.comp_sub_right (2 * bε)).sub hint).const_mul _).indicator measurableSet_Ioi

/-- **The witness density has total mass one** (`MMY §3.8.5`, "its integral equals one,
since by (3.68), `∫_{b_ε}^∞ (f₀(x − 2b_ε) − f₀(x)) dx = 2F₀(b_ε) − 1 = ε/(1−ε)`"). -/
theorem integral_minimaxWitnessDensity {f₀ : ℝ → ℝ} {bε ε : ℝ}
    -- LEAN-ONLY: measurability + integrability of the density; regularity
    (hmeas : Measurable f₀) (hint : Integrable f₀)
    (hnonneg : ∀ x, 0 ≤ f₀ x)
    -- USER-INPUT: f₀ is a probability density; MMY §3.8.5
    (hone : ∫ x, f₀ x = 1)
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1)
    -- USER-INPUT: b_ε solves the median's maximum-bias quantile equation; MMY (3.68)
    (hquant : ∫ x in Set.Iic bε, f₀ x = 1 / (2 * (1 - ε))) :
    ∫ x, minimaxWitnessDensity f₀ bε ε x = 1 := by
  have h1ε : (0:ℝ) < 1 - ε := by linarith
  -- `∫_{(b_ε,∞)} f₀(x − 2b_ε) dx = ∫_{(−b_ε,∞)} f₀` (translation invariance).
  have hshift : ∫ x in Set.Ioi bε, f₀ (x - 2 * bε) = ∫ x in Set.Ioi (-bε), f₀ x := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
      ← integral_sub_right_eq_self (fun y => (Set.Ioi (-bε)).indicator f₀ y) (2 * bε)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Set.indicator_apply, Set.mem_Ioi]
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; linarith)
  -- `∫_{(−b_ε,∞)} f₀ = ∫_{(−∞,b_ε]} f₀` (symmetry of `f₀`).
  have hrefl : ∫ x in Set.Ioi (-bε), f₀ x = ∫ x in Set.Iic bε, f₀ x := by
    have h := integral_comp_neg_Ioi (-bε) f₀
    rw [neg_neg] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => (hsym x).symm
  -- `∫_{(b_ε,∞)} f₀ = 1 − F₀(b_ε)`.
  -- NB: the `∫ … , _` body binds at precedence 60, so `+` would be swallowed without
  -- these parentheses.
  have hcompl : (∫ x in Set.Iic bε, f₀ x) + (∫ x in Set.Ioi bε, f₀ x) = 1 := by
    rw [← hone]
    have h := integral_add_compl (μ := volume) (f := f₀) (s := Set.Iic bε)
      measurableSet_Iic hint
    rwa [Set.compl_Iic] at h
  have hIoi : ∫ x in Set.Ioi bε, f₀ x = 1 - 1 / (2 * (1 - ε)) := by
    rw [hquant] at hcompl; linarith
  rw [minimaxWitnessDensity_eq_indicator, integral_indicator measurableSet_Ioi,
    integral_const_mul,
    integral_sub ((hint.comp_sub_right (2 * bε)).integrableOn) hint.integrableOn,
    hshift, hrefl, hquant, hIoi]
  field_simp
  ring

/-- **`F₊` is an `ε`-contamination of `F₀`** (`MMY §3.8.5`, "`f₊` belongs to
`F(F₀, ε)`; in fact it can be written as `f₊ = (1−ε)f₀ + εg`"): the paste-and-shift
density equals the mixture of `P₀` with the witness. -/
theorem medianMinimaxPlus_eq_contaminate {f₀ : ℝ → ℝ} {bε ε : ℝ}
    (hmeas : Measurable f₀) (hint : Integrable f₀) (hnonneg : ∀ x, 0 ≤ f₀ x)
    (hone : ∫ x, f₀ x = 1)
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1)
    (hquant : ∫ x in Set.Iic bε, f₀ x = 1 / (2 * (1 - ε))) :
    densityMeasure (fun x => if x ≤ bε then (1 - ε) * f₀ x
        else (1 - ε) * f₀ (x - 2 * bε))
      = contaminate (densityMeasure f₀)
          (densityMeasure (minimaxWitnessDensity f₀ bε ε)) ε := by
  have hne : ε ≠ 0 := hε.ne'
  have hfun : (fun x => if x ≤ bε then (1 - ε) * f₀ x else (1 - ε) * f₀ (x - 2 * bε))
      = fun x => (1 - ε) * f₀ x + ε * minimaxWitnessDensity f₀ bε ε x := by
    funext x
    by_cases h : x ≤ bε
    · rw [if_pos h, minimaxWitnessDensity, if_neg (not_lt.2 h)]
      ring
    · rw [if_neg h, minimaxWitnessDensity, if_pos (not_le.1 h)]
      field_simp
      ring
  rw [hfun]
  exact densityMeasure_mixture hmeas (measurable_minimaxWitnessDensity hmeas bε ε) hnonneg
    (minimaxWitnessDensity_nonneg hsym huni hbε hε hε1) hε.le hε1.le

/-- The left shift of `f₊` by `2b_ε` is `(1−ε)f₀` plus `ε` times the *reflected* witness
density (`MMY §3.8.5`, "which also belongs to `F(F₀, ε)` by the same argument"). The two
sides agree at the boundary point `x = −b_ε` as well, by symmetry of `f₀`, so this is an
everywhere identity — no null set is discarded. -/
private theorem minimaxWitness_reflect_shift {f₀ : ℝ → ℝ} {bε ε : ℝ}
    (hsym : ∀ x, f₀ (-x) = f₀ x) (hε : 0 < ε) (x : ℝ) :
    (if x + 2 * bε ≤ bε then (1 - ε) * f₀ (x + 2 * bε) else (1 - ε) * f₀ x)
      = (1 - ε) * f₀ x + ε * minimaxWitnessDensity f₀ bε ε (-x) := by
  have hne : ε ≠ 0 := hε.ne'
  rw [minimaxWitnessDensity]
  by_cases h : bε < -x
  · rw [if_pos h, if_pos (by linarith : x + 2 * bε ≤ bε),
      show (-x - 2 * bε) = -(x + 2 * bε) from by ring, hsym (x + 2 * bε), hsym x]
    field_simp
    ring
  · rw [if_neg h, mul_zero, add_zero]
    rw [not_lt] at h
    by_cases h2 : x + 2 * bε ≤ bε
    · rw [if_pos h2, show x = -bε from by linarith, show -bε + 2 * bε = bε from by ring,
        hsym bε]
    · rw [if_neg h2]

/-- **`F₋` is also an `ε`-contamination of `F₀`** (`MMY §3.8.5`, "define
`F₋(x) = F₊(x + 2b_ε)`, which also belongs to `F(F₀, ε)` by the same argument"): the
left shift of `F₊` by `2b_ε` lies in the gross-error neighbourhood of `P₀`. -/
theorem medianMinimaxMinus_mem_nbhd {f₀ : ℝ → ℝ} {bε ε : ℝ}
    (hmeas : Measurable f₀) (hint : Integrable f₀) (hnonneg : ∀ x, 0 ≤ f₀ x)
    (hone : ∫ x, f₀ x = 1)
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1)
    (hquant : ∫ x in Set.Iic bε, f₀ x = 1 / (2 * (1 - ε))) :
    (densityMeasure (fun x => if x ≤ bε then (1 - ε) * f₀ x
        else (1 - ε) * f₀ (x - 2 * bε))).map (· + (-(2 * bε)))
      ∈ grossErrorNbhd (densityMeasure f₀) ε := by
  have hgm0 : ∀ x, 0 ≤ minimaxWitnessDensity f₀ bε ε (-x) := fun x =>
    minimaxWitnessDensity_nonneg hsym huni hbε hε hε1 (-x)
  have hgmM : Measurable fun x => minimaxWitnessDensity f₀ bε ε (-x) :=
    (measurable_minimaxWitnessDensity hmeas bε ε).comp measurable_neg
  have hgmI : Integrable fun x => minimaxWitnessDensity f₀ bε ε (-x) :=
    (integrable_minimaxWitnessDensity hint bε ε).comp_neg
  have hgmMass : ∫ x, minimaxWitnessDensity f₀ bε ε (-x) = 1 := by
    rw [integral_neg_eq_self (minimaxWitnessDensity f₀ bε ε) volume]
    exact integral_minimaxWitnessDensity hmeas hint hnonneg hone hsym huni hbε hε hε1 hquant
  haveI : IsProbabilityMeasure (densityMeasure fun x => minimaxWitnessDensity f₀ bε ε (-x)) :=
    isProbabilityMeasure_densityMeasure hgmI hgm0 hgmMass
  refine ⟨densityMeasure fun x => minimaxWitnessDensity f₀ bε ε (-x), inferInstance, ?_⟩
  have key : (densityMeasure fun x => if x ≤ bε then (1 - ε) * f₀ x
        else (1 - ε) * f₀ (x - 2 * bε)).map (· + (-(2 * bε)))
      = densityMeasure fun x =>
          (1 - ε) * f₀ x + ε * minimaxWitnessDensity f₀ bε ε (-x) := by
    rw [map_add_densityMeasure]
    congr 1
    funext x
    show (if x - -(2 * bε) ≤ bε then (1 - ε) * f₀ (x - -(2 * bε))
        else (1 - ε) * f₀ (x - -(2 * bε) - 2 * bε))
      = (1 - ε) * f₀ x + ε * minimaxWitnessDensity f₀ bε ε (-x)
    rw [show x - -(2 * bε) = x + 2 * bε from by ring,
      show x + 2 * bε - 2 * bε = x from by ring]
    exact minimaxWitness_reflect_shift hsym hε x
  rw [key]
  exact densityMeasure_mixture hmeas hgmM hnonneg hgm0 hε.le hε1.le

/-- **The minimax-bias property of the median** (`MMY §3.8.5`; Huber (1964)): for a
symmetric unimodal center `F₀` and any functional `T` that is location equivariant on a
domain containing the witness pair, some member of the `ε`-gross-error neighbourhood of
`F₀` has `|T| ≥ b_ε` — the median's own maximum bias (`MMY (3.68)`,
`MaxBias/MaxBiasLocation.lean`). Equivariance gives `T(F₊) − T(F₋) = 2b_ε`, "and hence
`|T(F₊)|` and `|T(F₋)|` cannot both be less than `b_ε`". -/
theorem locationEquivariant_maxBias_ge_median {f₀ : ℝ → ℝ} {bε ε : ℝ}
    {T : Measure ℝ → ℝ} {𝒟 : Set (Measure ℝ)}
    (hmeas : Measurable f₀) (hint : Integrable f₀) (hnonneg : ∀ x, 0 ≤ f₀ x)
    (hone : ∫ x, f₀ x = 1)
    -- USER-INPUT: symmetric unimodal center; MMY §3.8.5
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1)
    -- USER-INPUT: b_ε solves the median's maximum-bias quantile equation; MMY (3.68)
    (hquant : ∫ x in Set.Iic bε, f₀ x = 1 / (2 * (1 - ε)))
    -- USER-INPUT: T is location equivariant on a domain containing the witness; MMY
    -- §3.8.5 ("let θ̂ be any location equivariant estimator")
    (hT : IsLocationEquivariantOn T 𝒟)
    (hD : densityMeasure (fun x => if x ≤ bε then (1 - ε) * f₀ x
        else (1 - ε) * f₀ (x - 2 * bε)) ∈ 𝒟) :
    ∃ F ∈ grossErrorNbhd (densityMeasure f₀) ε, bε ≤ |T F| := by
  haveI hwit : IsProbabilityMeasure (densityMeasure (minimaxWitnessDensity f₀ bε ε)) :=
    isProbabilityMeasure_densityMeasure (integrable_minimaxWitnessDensity hint bε ε)
      (minimaxWitnessDensity_nonneg hsym huni hbε hε hε1)
      (integral_minimaxWitnessDensity hmeas hint hnonneg hone hsym huni hbε hε hε1 hquant)
  have hplus : densityMeasure (fun x => if x ≤ bε then (1 - ε) * f₀ x
      else (1 - ε) * f₀ (x - 2 * bε)) ∈ grossErrorNbhd (densityMeasure f₀) ε :=
    ⟨_, hwit, medianMinimaxPlus_eq_contaminate hmeas hint hnonneg hone hsym huni hbε hε hε1
      hquant⟩
  have hminus := medianMinimaxMinus_mem_nbhd hmeas hint hnonneg hone hsym huni hbε hε hε1 hquant
  -- Equivariance: `T(F₋) = T(F₊) − 2b_ε`, so `|T(F₊)|` and `|T(F₋)|` cannot both be `< b_ε`.
  have hTeq := hT _ hD (-(2 * bε))
  by_cases h : bε ≤ |T (densityMeasure fun x => if x ≤ bε then (1 - ε) * f₀ x
      else (1 - ε) * f₀ (x - 2 * bε))|
  · exact ⟨_, hplus, h⟩
  · refine ⟨_, hminus, ?_⟩
    rw [hTeq]
    rw [not_le] at h
    exact le_abs.2 (Or.inr (by linarith [(abs_lt.1 h).2]))

end StatLean.RobustStatistics
