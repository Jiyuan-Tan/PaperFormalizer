module
public import StatLean.RobustStatistics.MEstimation.MLocationFunctional
public import StatLean.RobustStatistics.MEstimation.AsymptoticBreakdown
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Real.Sign

@[expose] public section

/-!
# The maximum asymptotic bias of location M-estimators — the sharp `b_ε` bound

Between the infinitesimal (influence function) and the catastrophic (breakdown point)
regimes sits the **maximum-bias curve** `MB(ε)` (`MMY §3.3`): the worst asymptotic bias
an estimator suffers over the full `ε`-contamination neighbourhood. For a location
M-estimator with nondecreasing bounded odd score `ψ`, `k = ψ(∞)`, symmetric center `P`,
and increasing population "shift score" `g(b) = ∫ ψ(x + b) dP`, the maximum bias is the
solution `b_ε` of

  `g(b) = k ε / (1 − ε)`    (`MMY (3.66)`),

every contaminated root lies in `[−b_ε, b_ε]` (`MMY (3.67)` manipulation), and
point-mass contamination pushed to `±∞` attains the bound. For the median (`ψ = sign`,
`k = 1`) the equation solves to the quantile formula

  `b_ε = F₀⁻¹( 1/(2(1 − ε)) )`    (`MMY (3.68)`),

stated here as the identity `g(b) = 2 F₀(b) − 1` for atomless `P`.

* `shiftScore` — `g(b) = ∫ ψ(x + b) dP`, with its oddness from symmetry.
* `mLocationRoot_abs_le_maxBias` — the sharp bound (`MMY §3.8.4`, proof of (3.66)).
* `maxBias_attained` — attainment in the limit `G = δ_{x₀}`, `x₀ → ∞`.
* `shiftScore_sign` — the median's `g(b) = 2 F₀(b) − 1` (`MMY (3.68)` route).

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.)
§3.3 (the neighbourhood `F_{ε,θ}` and `MB`), §3.8.4 (eqs. (3.66)–(3.68) with proofs).
The minimax-bias optimality of the median over location-equivariant functionals is the
companion file `MaxBias/MedianMinimaxBias.lean` (`MMY §3.8.5`).

**Bibliographic comments.** The maximum-bias function of a location M-estimator and its
`g(b) = kε/(1−ε)` characterization are due to Huber ("Robust estimation of a location
parameter," *Ann. Math. Statist.* **35** (1964), 73–101; book form in Huber–Ronchetti 2009,
§4.2); the systematic min–max bias program is Martin, Yohai and Zamar, *Ann. Statist.*
**17** (1989), 1608–1630, with lower-bound refinements in He and Simpson, "Lower bounds for
contamination bias: globally minimax versus locally linear estimation," *Ann. Statist.*
**21** (1993), 314–337.
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- **The shift score** `g(b) = ∫ ψ(x + b) dP` (`MMY §3.8.4`, "define for brevity the
function `g(b) = E_{F₀} ψ(x + b)`"): the population score of `MLocationFunctional`
evaluated at `−b`, `g(b) = mLocationScore ψ P (−b)`. -/
noncomputable def shiftScore (ψ : ℝ → ℝ) (P : Measure ℝ) (b : ℝ) : ℝ :=
  mLocationScore ψ P (-b)

/-- The shift score is odd for an odd score and a symmetric center (`MMY §3.8.4`,
"which is odd"): if `P` is invariant under negation and `ψ(−u) = −ψ(u)`, then
`g(−b) = −g(b)`. -/
theorem shiftScore_neg {ψ : ℝ → ℝ} {P : Measure ℝ} [IsProbabilityMeasure P] {b : ℝ}
    -- USER-INPUT: odd score; MMY §3.8.4 (k₁ = k₂ = k)
    (hψ_odd : ∀ u, ψ (-u) = -ψ u)
    -- USER-INPUT: symmetric center, F₀ symmetric about zero; MMY §3.8.4
    (hsym : P.map Neg.neg = P)
    -- LEAN-ONLY: measurability of ψ, to transport the integral; regularity
    (hψ_meas : Measurable ψ) :
    shiftScore ψ P (-b) = -shiftScore ψ P b := by
  have hneg : Measurable (Neg.neg : ℝ → ℝ) := measurable_neg
  have key : ∫ x, ψ (x - b) ∂P = ∫ x, ψ (-x - b) ∂P := by
    nth_rewrite 1 [← hsym]
    exact integral_map hneg.aemeasurable
      (hψ_meas.comp (measurable_id.sub_const b)).aestronglyMeasurable
  have hpt : ∀ x : ℝ, ψ (-x - b) = -ψ (x + b) := by
    intro x
    rw [show (-x - b) = -(x + b) by ring, hψ_odd]
  simp only [shiftScore, mLocationScore, neg_neg, sub_neg_eq_add]
  rw [key]
  simp only [hpt]
  rw [integral_neg]

/-- **The sharp maximum-bias bound** (`MMY §3.8.4`, the proof of (3.66) via (3.67)):
let `ψ` be nondecreasing, bounded by `k`, and odd; let `P` be symmetric with strictly
increasing shift score `g`, and let `b_ε` solve `g(b_ε) = kε/(1−ε)` (`MMY (3.66)`).
Then for `ε < 1/2`, every root `θ` of every `ε`-contaminated M-equation satisfies
`|θ| ≤ b_ε`: from `(1−ε) g(−θ) + ε E_G ψ(x − θ) = 0` (`MMY (3.67)`) and `|E_G ψ| ≤ k`,
`|g(θ)| ≤ kε/(1−ε) = g(b_ε)`, and strict monotonicity concludes.

This refines Round-1's `mLocationRoot_bounded_of_contamination` (`MMY (3.21)`), which
produced *some* bound `B`; here the bound is the exact maximum-bias value `b_ε`. -/
theorem mLocationRoot_abs_le_maxBias {ψ : ℝ → ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P] {k ε bε : ℝ}
    -- USER-INPUT: nondecreasing odd score bounded by k = ψ(∞); MMY §3.8.4
    (hψm : Monotone ψ) (hψ_odd : ∀ u, ψ (-u) = -ψ u) (hψb : ∀ u, |ψ u| ≤ k)
    (hk : 0 < k)
    -- USER-INPUT: symmetric center; MMY §3.8.4 ("F₀ is symmetric about zero")
    (hsym : P.map Neg.neg = P)
    -- USER-INPUT: strictly increasing shift score; MMY §3.8.4 ("it will be assumed
    -- that g is increasing; this holds either if ψ is increasing, or if F₀ has
    -- positive density everywhere")
    (hg : StrictMono (shiftScore ψ P))
    -- USER-INPUT: contamination level; MMY §3.8.4 ("let ε < 0.5")
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    -- USER-INPUT: b_ε solves the maximum-bias equation; MMY (3.66)
    (hbε : shiftScore ψ P bε = k * ε / (1 - ε)) :
    ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → ∀ θ : ℝ,
      IsMLocationRoot ψ (contaminate P Q ε) θ → |θ| ≤ bε := by
  intro Q hQ θ hθ
  haveI := hQ
  have hψmeas : Measurable ψ := hψm.measurable
  have hbd : ∃ C, ∀ u, |ψ u| ≤ C := ⟨k, hψb⟩
  have hintP : Integrable (fun x => ψ (x - θ)) P := integrable_psi_sub hψmeas hbd θ
  have hintQ : Integrable (fun x => ψ (x - θ)) Q := integrable_psi_sub hψmeas hbd θ
  have hε1 : ε ≤ 1 := by linarith
  have h1ε : (0:ℝ) < 1 - ε := by linarith
  have hsplit : (1 - ε) * (∫ x, ψ (x - θ) ∂P) + ε * (∫ x, ψ (x - θ) ∂Q) = 0 := by
    rw [← integral_contaminate hε0 hε1 hintP hintQ]; exact hθ
  -- `|E_G ψ(x − θ)| ≤ k`: the score is bounded and `Q` is a probability measure.
  have hEQ : |∫ x, ψ (x - θ) ∂Q| ≤ k := by
    have h := norm_integral_le_of_norm_le_const (μ := Q) (f := fun x => ψ (x - θ)) (C := k)
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hψb (x - θ))
    simpa [Real.norm_eq_abs] using h
  -- `(1 − ε)|g(−θ)| = ε |E_G ψ| ≤ ε k`.
  have habs : (1 - ε) * |∫ x, ψ (x - θ) ∂P| ≤ ε * k := by
    have heq : (1 - ε) * (∫ x, ψ (x - θ) ∂P) = -(ε * ∫ x, ψ (x - θ) ∂Q) := by linarith
    calc (1 - ε) * |∫ x, ψ (x - θ) ∂P| = |(1 - ε) * ∫ x, ψ (x - θ) ∂P| := by
          rw [abs_mul, abs_of_pos h1ε]
      _ = |ε * ∫ x, ψ (x - θ) ∂Q| := by rw [heq, abs_neg]
      _ = ε * |∫ x, ψ (x - θ) ∂Q| := by rw [abs_mul, abs_of_nonneg hε0]
      _ ≤ ε * k := mul_le_mul_of_nonneg_left hEQ hε0
  -- Oddness of `g` turns the score at `−θ` into `−g(θ)`.
  have hSeq : shiftScore ψ P θ = -(∫ x, ψ (x - θ) ∂P) := by
    have h := shiftScore_neg (ψ := ψ) (P := P) (b := θ) hψ_odd hsym hψmeas
    simp only [shiftScore, mLocationScore, neg_neg] at h ⊢
    linarith
  have habsS : |shiftScore ψ P θ| = |∫ x, ψ (x - θ) ∂P| := by rw [hSeq, abs_neg]
  have hkey : |shiftScore ψ P θ| ≤ shiftScore ψ P bε := by
    rw [hbε, le_div_iff₀ h1ε, habsS]
    nlinarith [habs]
  rw [abs_le] at hkey
  have hgnb : shiftScore ψ P (-bε) = -shiftScore ψ P bε := shiftScore_neg hψ_odd hsym hψmeas
  have h1 : shiftScore ψ P (-bε) ≤ shiftScore ψ P θ := by rw [hgnb]; exact hkey.1
  exact abs_le.2 ⟨hg.le_iff_le.1 h1, hg.le_iff_le.1 hkey.2⟩

/-- **The maximum bias is attained in the limit** (`MMY §3.8.4`, "by letting
`G = δ_{x₀}` in (3.67) with `x₀ → ±∞`, we see that the bound is attained"): for a
*continuous* score, point-mass contamination far enough out produces roots within any
`η` of `b_ε`. -/
theorem maxBias_attained {ψ : ℝ → ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P] {k ε bε : ℝ}
    -- USER-INPUT: continuous nondecreasing odd score with limit k at +∞; MMY §3.8.4
    -- (continuity is the Thm 10.1-style regularity used for root existence)
    (hψc : Continuous ψ) (hψm : Monotone ψ) (hψ_odd : ∀ u, ψ (-u) = -ψ u)
    (htop : Tendsto ψ atTop (𝓝 k)) (hk : 0 < k)
    -- USER-INPUT: symmetric center; MMY §3.8.4
    (hsym : P.map Neg.neg = P)
    -- USER-INPUT: strictly increasing continuous shift score; MMY §3.8.4
    (hg : StrictMono (shiftScore ψ P))
    -- USER-INPUT: contamination level, nondegenerate; MMY §3.8.4
    (hε0 : 0 < ε) (hε : ε < 1 / 2)
    -- USER-INPUT: b_ε solves the maximum-bias equation; MMY (3.66)
    (hbε : shiftScore ψ P bε = k * ε / (1 - ε)) :
    ∀ η : ℝ, 0 < η → ∃ (x₀ θ : ℝ),
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) ε) θ ∧ bε - η < θ := by
  intro η hη
  have h1ε : (0:ℝ) < 1 - ε := by linarith
  have hε1 : ε ≤ 1 := by linarith
  -- The monotone score with limit `k` at `+∞` is bounded by `k`; oddness gives `|ψ| ≤ k`.
  have hψk : ∀ u, ψ u ≤ k := fun u =>
    ge_of_tendsto htop (eventually_atTop.2 ⟨u, fun _ hv => hψm hv⟩)
  have hψb : ∀ u, |ψ u| ≤ k := by
    intro u
    have h1 := hψk u
    have h2 := hψk (-u)
    rw [hψ_odd u] at h2
    rw [abs_le]; constructor <;> linarith
  have hbot : Tendsto ψ atBot (𝓝 (-k)) := by
    have h1 : Tendsto (fun u : ℝ => ψ (-u)) atBot (𝓝 k) := htop.comp tendsto_neg_atBot_atTop
    have h2 : Tendsto (fun u : ℝ => -ψ u) atBot (𝓝 k) := by simpa [hψ_odd] using h1
    simpa using h2.neg
  -- The target level: `g(b_ε − η) < g(b_ε) = kε/(1−ε)`, so `M := g(b_ε−η)(1−ε)/ε < k`.
  have hlt : shiftScore ψ P (bε - η) < shiftScore ψ P bε := hg (by linarith)
  rw [hbε] at hlt
  have hkey : shiftScore ψ P (bε - η) * (1 - ε) < k * ε := by
    have h := mul_lt_mul_of_pos_right hlt h1ε
    rw [div_mul_cancel₀ _ h1ε.ne'] at h
    exact h
  have hMk : shiftScore ψ P (bε - η) * (1 - ε) / ε < k := (div_lt_iff₀ hε0).2 hkey
  obtain ⟨R, hR⟩ := eventually_atTop.1 (htop.eventually_const_lt hMk)
  refine ⟨R + bε, ?_⟩
  -- A root exists for the point-mass contaminated model.
  haveI : IsProbabilityMeasure (contaminate P (Measure.dirac (R + bε)) ε) :=
    isProbabilityMeasure_contaminate P _ hε0.le hε1
  obtain ⟨θ, hθ⟩ := exists_isMLocationRoot (P := contaminate P (Measure.dirac (R + bε)) ε)
    hψc hψm hbot htop hk hk
  refine ⟨θ, hθ, ?_⟩
  -- Every contaminated root lies in `[−b_ε, b_ε]` (the previous theorem).
  have hθb : |θ| ≤ bε := mLocationRoot_abs_le_maxBias hψm hψ_odd hψb hk hsym hg hε0.le hε hbε
    (Measure.dirac (R + bε)) inferInstance θ hθ
  rw [abs_le] at hθb
  -- Unfold the root equation: `(1−ε) g(−θ) + ε ψ(x₀ − θ) = 0`.
  have hintP : Integrable (fun x => ψ (x - θ)) P :=
    integrable_psi_sub hψc.measurable ⟨k, hψb⟩ θ
  have hroot : (1 - ε) * (∫ x, ψ (x - θ) ∂P) + ε * ψ (R + bε - θ) = 0 := by
    rw [← integral_contaminate_dirac hε0.le hε1 hintP (R + bε)]; exact hθ
  have hSeq : shiftScore ψ P θ = -(∫ x, ψ (x - θ) ∂P) := by
    have h := shiftScore_neg (ψ := ψ) (P := P) (b := θ) hψ_odd hsym hψc.measurable
    simp only [shiftScore, mLocationScore, neg_neg] at h ⊢
    linarith
  -- The far point-mass drives `ψ(x₀ − θ)` above the threshold `M`.
  have hψlow : shiftScore ψ P (bε - η) * (1 - ε) / ε < ψ (R + bε - θ) :=
    hR _ (by linarith [hθb.2])
  have hgt : shiftScore ψ P (bε - η) < shiftScore ψ P θ := by
    have h1 : shiftScore ψ P (bε - η) * (1 - ε) < ε * ψ (R + bε - θ) := by
      have := (div_lt_iff₀ hε0).1 hψlow
      linarith
    have h2 : (1 - ε) * shiftScore ψ P θ = ε * ψ (R + bε - θ) := by
      rw [hSeq]; linarith
    nlinarith [h1, h2]
  exact hg.lt_iff_lt.1 hgt

/-- **The median's shift score, general form**: for atomless `P`,
`g(b) = ∫ sign(x + b) dP = 1 − 2 P(−∞, −b]` — no symmetry needed at this stage. -/
theorem shiftScore_sign {P : Measure ℝ} [IsProbabilityMeasure P] {b : ℝ}
    -- USER-INPUT: atomless center (the sign integrand's null discontinuity); MMY
    -- §3.8.4 (implicit: F₀ has a density)
    (hatom : ∀ t : ℝ, P {t} = 0) :
    shiftScore Real.sign P b = 1 - 2 * P.real (Set.Iic (-b)) := by
  -- Off the null set `{-b}`, `sign (x + b) = 1 - 2·1_{(-∞,-b]}(x)`.
  have hae : (fun x => Real.sign (x - -b)) =ᵐ[P]
      fun x => 1 - 2 * (Set.Iic (-b)).indicator (fun _ => (1:ℝ)) x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hatom (-b))] with x hx
    rw [Set.mem_singleton_iff] at hx
    rcases lt_trichotomy x (-b) with h | h | h
    · rw [Set.indicator_of_mem (show x ∈ Set.Iic (-b) from h.le),
        Real.sign_of_neg (by linarith : x - -b < 0)]
      norm_num
    · exact absurd h hx
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic, not_le]; linarith),
        Real.sign_of_pos (by linarith : (0:ℝ) < x - -b)]
      norm_num
  have hindint : Integrable (fun x => (Set.Iic (-b)).indicator (fun _ => (1:ℝ)) x) P :=
    (integrable_const (1:ℝ)).indicator measurableSet_Iic
  rw [shiftScore, mLocationScore, integral_congr_ae hae,
    integral_sub (integrable_const (1:ℝ)) (hindint.const_mul 2), integral_const_mul,
    integral_indicator_const (1:ℝ) measurableSet_Iic, integral_const]
  simp

/-- **The median's shift score is the centered CDF** (`MMY §3.8.4`, "for the median,
`ψ(x) = sgn(x)` and `k = 1`, and a simple calculation shows (recalling the symmetry of
`F₀`) that `g(b) = 2F₀(b) − 1`"): symmetry turns `1 − 2F₀(−b)` into `2F₀(b) − 1`. -/
theorem shiftScore_sign_of_symm {P : Measure ℝ} [IsProbabilityMeasure P] {b : ℝ}
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: symmetric center; MMY §3.8.4 ("recalling the symmetry of F₀")
    (hsym : P.map Neg.neg = P) :
    shiftScore Real.sign P b = 2 * P.real (Set.Iic b) - 1 := by
  rw [shiftScore_sign hatom]
  -- Symmetry: `P(-∞, -b] = P[b, ∞)`; the atom at `b` is null, so `P[b, ∞) = 1 - P(-∞, b]`.
  have hpre : (Neg.neg ⁻¹' (Set.Iic (-b)) : Set ℝ) = Set.Ici b := by
    ext x; simp
  have h1 : P (Set.Iic (-b)) = P (Set.Ici b) := by
    conv_lhs => rw [← hsym]
    rw [Measure.map_apply measurable_neg measurableSet_Iic, hpre]
  have h3 : P (Set.Iic b) = P (Set.Iio b) := by
    refine le_antisymm ?_ (measure_mono Set.Iio_subset_Iic_self)
    have hsub : (Set.Iic b : Set ℝ) ⊆ Set.Iio b ∪ {b} := fun x hx => by
      rcases lt_or_eq_of_le (Set.mem_Iic.1 hx) with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc P (Set.Iic b) ≤ P (Set.Iio b ∪ {b}) := measure_mono hsub
      _ ≤ P (Set.Iio b) + P {b} := measure_union_le _ _
      _ = P (Set.Iio b) := by rw [hatom b, add_zero]
  have h2 : P.real (Set.Ici b) = 1 - P.real (Set.Iio b) := by
    rw [show (Set.Ici b : Set ℝ) = (Set.Iio b)ᶜ by rw [Set.compl_Iio],
      measureReal_compl (μ := P) measurableSet_Iio]
    simp
  have hkey : P.real (Set.Iic (-b)) = 1 - P.real (Set.Iic b) := by
    rw [measureReal_def, h1, ← measureReal_def, h2, measureReal_def, ← h3, ← measureReal_def]
  rw [hkey]; ring

/-- **The median's maximum-bias equation is the quantile equation** (`MMY (3.68)`):
for an atomless symmetric center, `b` solves the `k = 1` maximum-bias equation
`g(b) = ε/(1−ε)` iff `F₀(b) = 1/(2(1−ε))`. -/
theorem sign_maxBias_iff {P : Measure ℝ} [IsProbabilityMeasure P] {ε b : ℝ}
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: symmetric center; MMY §3.8.4
    (hsym : P.map Neg.neg = P) (hε : ε < 1) :
    shiftScore Real.sign P b = 1 * ε / (1 - ε) ↔
      P.real (Set.Iic b) = 1 / (2 * (1 - ε)) := by
  rw [shiftScore_sign_of_symm hatom hsym]
  have h : (1:ℝ) - ε ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < 1 - ε)
  constructor <;> intro h1 <;> field_simp at h1 ⊢ <;> linarith

end StatLean.RobustStatistics
