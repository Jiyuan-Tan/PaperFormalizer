module
public import StatLean.RobustStatistics.MEstimation.MLocationFunctional

@[expose] public section

/-!
# Asymptotic breakdown of monotone location M-functionals

The asymptotic contamination breakdown point of a monotone location M-estimator with
bounded score is (`MMY §3.2.1`, eq. (3.21); proof §3.8.3)

$$\varepsilon^* = \frac{\min(k_1, k_2)}{k_1 + k_2}, \qquad
  k_1 = -\psi(-\infty),\ k_2 = \psi(\infty),$$

attaining `1/2` for odd ψ. Following the statement-first design, the content is split
into the two directions that *are* eq. (3.21), without introducing an `ε*` supremum:

* `mLocationRoot_bounded_of_contamination` — **stability**: for
  `ε < min(k₁,k₂)/(k₁+k₂)`, all roots of every `ε`-contaminated M-equation lie in one
  fixed bounded interval (uniformly over the contaminating `Q`).
* `mLocationRoot_contamination_unbounded` — **sharpness**: for
  `ε > k₁/(k₁+k₂)`, point-mass contaminations `δ_{x₀}` with `x₀ → ∞` produce contaminated
  roots beyond any bound.
* `mLocationRoot_bounded_of_odd`, `huberLocationRoot_bounded` — the odd/Huber case:
  breakdown `1/2` (`MMY §3.2.1`: "if ψ is odd … the bound ε* = 0.5 is attained").

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.2.1 (eq.
(3.21)–(3.22)), §3.8.3.1 (eq. (3.61)–(3.63)).

**Bibliographic comments.** The asymptotic breakdown point `min(k₁,k₂)/(k₁+k₂)` of a
monotone-score location M-estimator — `1/2` for odd bounded scores — is due to Huber; see
Huber and Ronchetti, *Robust Statistics*, 2nd ed., Wiley, 2009, §3.2, and Hampel's
qualitative-robustness framework (*Ann. Math. Statist.* **42** (1971), 1887–1896).
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-! ### Envelopes for monotone scores with finite limits

`MMY §3.2.1`: a monotone `ψ` is trapped between its two limits, `-k₁ = ψ(-∞) ≤ ψ ≤
ψ(∞) = k₂`. (The companions in `MLocationFunctional` are file-private, so they are
re-derived here rather than exported — the frozen statements stay untouched.) -/

/-- A monotone score is bounded below by its limit at `-∞`. -/
private theorem neg_le_psi' {ψ : ℝ → ℝ} {k₁ : ℝ} (hψm : Monotone ψ)
    (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (u : ℝ) : -k₁ ≤ ψ u :=
  le_of_tendsto hbot (eventually_atBot.2 ⟨u, fun _ hv => hψm hv⟩)

/-- A monotone score is bounded above by its limit at `+∞`. -/
private theorem psi_le' {ψ : ℝ → ℝ} {k₂ : ℝ} (hψm : Monotone ψ)
    (htop : Tendsto ψ atTop (𝓝 k₂)) (u : ℝ) : ψ u ≤ k₂ :=
  ge_of_tendsto htop (eventually_atTop.2 ⟨u, fun _ hv => hψm hv⟩)

/-- A monotone score with limits `-k₁ < 0 < k₂` is bounded by `k₁ + k₂`. -/
private theorem psi_abs_le {ψ : ℝ → ℝ} {k₁ k₂ : ℝ} (hψm : Monotone ψ)
    (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (htop : Tendsto ψ atTop (𝓝 k₂))
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (u : ℝ) : |ψ u| ≤ k₁ + k₂ := by
  have h1 := neg_le_psi' hψm hbot u
  have h2 := psi_le' hψm htop u
  rw [abs_le]
  constructor <;> linarith

/-- The translation `θ ↦ x - θ` drives `θ → ∞` to `-∞`. -/
private theorem tendsto_const_sub_atTop_atBot' (x : ℝ) :
    Tendsto (fun θ : ℝ => x - θ) atTop atBot :=
  tendsto_atBot.2 fun b => eventually_atTop.2 ⟨x - b, fun _ hθ => by linarith⟩

/-- The score of a bounded `ψ` against a probability measure stays inside `[-k₁, k₂]`
(`MMY §3.8.3.1`: the contaminating part of the estimating equation can shift the ideal
score by at most `ε k₁` upward / `ε k₂` downward). -/
private theorem integral_psi_sub_mem {ψ : ℝ → ℝ} {k₁ k₂ θ : ℝ} (hlow : ∀ u, -k₁ ≤ ψ u)
    (hhigh : ∀ u, ψ u ≤ k₂) {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hiQ : Integrable (fun x => ψ (x - θ)) Q) :
    -k₁ ≤ ∫ x, ψ (x - θ) ∂Q ∧ ∫ x, ψ (x - θ) ∂Q ≤ k₂ := by
  constructor
  · simpa using integral_mono (integrable_const (-k₁)) hiQ fun x => hlow (x - θ)
  · simpa using integral_mono hiQ (integrable_const k₂) fun x => hhigh (x - θ)

/-- **Stability below the breakdown level** (`MMY` eq. (3.21), "≥" direction; §3.8.3.1):
for a monotone score with limits `-k₁ < 0 < k₂` and contamination level
`ε < min(k₁,k₂)/(k₁+k₂)`, the roots of all `ε`-contaminated M-equations are uniformly
bounded — no contaminating distribution can drive the M-functional to infinity. -/
theorem mLocationRoot_bounded_of_contamination {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ : ℝ → ℝ} {k₁ k₂ ε : ℝ}
    -- USER-INPUT: monotone score with finite limits; MMY §3.2.1 (k₁ = -ψ(-∞), k₂ = ψ(∞))
    (hψm : Monotone ψ) (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (htop : Tendsto ψ atTop (𝓝 k₂))
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    -- USER-INPUT: contamination level below the breakdown point; MMY eq. (3.21)
    (hε0 : 0 ≤ ε) (hε : ε < min k₁ k₂ / (k₁ + k₂)) :
    ∃ B : ℝ, ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → ∀ θ : ℝ,
      IsMLocationRoot ψ (contaminate P Q ε) θ → |θ| ≤ B := by
  have hlow := neg_le_psi' hψm hbot
  have hhigh := psi_le' hψm htop
  have hCb := psi_abs_le hψm hbot htop hk₁ hk₂
  have hsum : 0 < k₁ + k₂ := by linarith
  -- the two numerical consequences of `ε < min(k₁,k₂)/(k₁+k₂)` (MMY eq. (3.61))
  have hεk : ε * k₁ + ε * k₂ < min k₁ k₂ := by
    have h : ε * (k₁ + k₂) < min k₁ k₂ / (k₁ + k₂) * (k₁ + k₂) :=
      mul_lt_mul_of_pos_right hε hsum
    rw [div_mul_cancel₀ _ hsum.ne'] at h
    linarith [h]
  have hA : ε * k₂ < (1 - ε) * k₁ := by linarith [min_le_left k₁ k₂]
  have hB : ε * k₁ < (1 - ε) * k₂ := by linarith [min_le_right k₁ k₂]
  have hε1 : ε < 1 := by
    by_contra hcon
    have hcon' : (1:ℝ) ≤ ε := not_lt.mp hcon
    have : k₁ + k₂ ≤ ε * (k₁ + k₂) := le_mul_of_one_le_left hsum.le hcon'
    nlinarith [min_le_left k₁ k₂]
  -- the ideal score and its limits
  have hiP : ∀ θ : ℝ, Integrable (fun x => ψ (x - θ)) P := fun θ =>
    integrable_psi_sub hψm.measurable ⟨k₁ + k₂, hCb⟩ θ
  have hT : Tendsto (fun θ => (1 - ε) * mLocationScore ψ P θ) atTop (𝓝 ((1 - ε) * -k₁)) :=
    (tendsto_mLocationScore_atTop hψm hbot hiP).const_mul _
  have hBt : Tendsto (fun θ => (1 - ε) * mLocationScore ψ P θ) atBot (𝓝 ((1 - ε) * k₂)) :=
    (tendsto_mLocationScore_atBot hψm htop hiP).const_mul _
  obtain ⟨Bhi, hBhi⟩ := eventually_atTop.1
    (hT.eventually_lt_const (by linarith : (1 - ε) * -k₁ < -(ε * k₂)))
  obtain ⟨Blo, hBlo⟩ := eventually_atBot.1
    (hBt.eventually_const_lt (by linarith : ε * k₁ < (1 - ε) * k₂))
  refine ⟨|Bhi| + |Blo|, fun Q hQ θ hroot => ?_⟩
  haveI := hQ
  have hiQ : Integrable (fun x => ψ (x - θ)) Q :=
    integrable_psi_sub hψm.measurable ⟨k₁ + k₂, hCb⟩ θ
  -- split the contaminated estimating equation (MMY §3.8.3.1)
  have hsplit : (1 - ε) * mLocationScore ψ P θ + ε * ∫ x, ψ (x - θ) ∂Q = 0 := by
    have h0 : ∫ x, ψ (x - θ) ∂(contaminate P Q ε) = 0 := hroot
    rwa [integral_contaminate hε0 hε1.le (hiP θ) hiQ] at h0
  obtain ⟨hQlow, hQhigh⟩ := integral_psi_sub_mem hlow hhigh hiQ
  have hglow : -(ε * k₂) ≤ (1 - ε) * mLocationScore ψ P θ := by
    nlinarith [mul_nonneg hε0 (sub_nonneg.2 hQhigh)]
  have hghigh : (1 - ε) * mLocationScore ψ P θ ≤ ε * k₁ := by
    nlinarith [mul_nonneg hε0 (by linarith : (0:ℝ) ≤ (∫ x, ψ (x - θ) ∂Q) + k₁)]
  rw [abs_le]
  constructor
  · by_contra hcon
    have hcon' : θ < -(|Bhi| + |Blo|) := not_le.mp hcon
    have hθB : θ ≤ Blo := by
      have h1 := neg_abs_le Blo
      have h2 := abs_nonneg Bhi
      linarith
    linarith [hBlo θ hθB]
  · by_contra hcon
    have hcon' : |Bhi| + |Blo| < θ := not_le.mp hcon
    have hθB : Bhi ≤ θ := by
      have h1 := le_abs_self Bhi
      have h2 := abs_nonneg Blo
      linarith
    linarith [hBhi θ hθB]

/-- **Sharpness above the breakdown level** (`MMY` eq. (3.21), "≤" direction; §3.8.3.1,
eq. (3.62)–(3.63)): for `ε > k₁/(k₁+k₂)`, placing the contaminating point mass far enough
to the right produces contaminated roots beyond any bound — the M-functional explodes
to `+∞`. -/
theorem mLocationRoot_contamination_unbounded {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ : ℝ → ℝ} {k₁ k₂ ε : ℝ}
    -- USER-INPUT: continuous monotone score with finite limits; MMY §3.2.1 + Thm 10.1
    (hψc : Continuous ψ) (hψm : Monotone ψ)
    (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (htop : Tendsto ψ atTop (𝓝 k₂))
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    -- USER-INPUT: contamination level above the breakdown point; MMY eq. (3.22) (ε₁*)
    (hε : k₁ / (k₁ + k₂) < ε) (hε1 : ε < 1) :
    ∀ B : ℝ, ∃ (x₀ θ : ℝ), B < θ ∧
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) ε) θ := by
  intro B
  have hlow := neg_le_psi' hψm hbot
  have hCb := psi_abs_le hψm hbot htop hk₁ hk₂
  have hsum : 0 < k₁ + k₂ := by linarith
  have hε0 : 0 < ε := lt_trans (div_pos hk₁ hsum) hε
  -- the numerical consequence of `ε > k₁/(k₁+k₂)` (MMY eq. (3.62))
  have hk1lt : k₁ < ε * (k₁ + k₂) := by
    have h : k₁ / (k₁ + k₂) * (k₁ + k₂) < ε * (k₁ + k₂) := mul_lt_mul_of_pos_right hε hsum
    rwa [div_mul_cancel₀ _ hsum.ne'] at h
  have hkey : (1 - ε) * k₁ < ε * k₂ := by nlinarith
  have hiP : ∀ θ : ℝ, Integrable (fun x => ψ (x - θ)) P := fun θ =>
    integrable_psi_sub hψm.measurable ⟨k₁ + k₂, hCb⟩ θ
  -- the contaminated score at the point mass `x₀`, evaluated beyond `B`
  have hε1' : 0 < 1 - ε := by linarith
  -- (i) push the point mass right until the contaminated score at `B + 1` is positive
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.1 ((htop.const_mul ε).eventually_const_lt hkey)
  set x₀ : ℝ := B + 1 + u₀ with hx₀
  have hxs : x₀ - (B + 1) = u₀ := by rw [hx₀]; ring
  have hglowB : -k₁ ≤ mLocationScore ψ P (B + 1) := by
    simpa using! integral_mono (integrable_const (-k₁)) (hiP (B + 1))
      fun x => hlow (x - (B + 1))
  have hpos : 0 < (1 - ε) * mLocationScore ψ P (B + 1) + ε * ψ (x₀ - (B + 1)) := by
    have h2 : (1 - ε) * k₁ < ε * ψ (x₀ - (B + 1)) := by
      rw [hxs]; exact hu₀ u₀ le_rfl
    linarith [mul_le_mul_of_nonneg_left hglowB hε1'.le]
  -- (ii) as `θ → ∞` both parts of the contaminated score fall to `-k₁ < 0`
  have hcT : Tendsto (fun θ => (1 - ε) * mLocationScore ψ P θ + ε * ψ (x₀ - θ)) atTop
      (𝓝 ((1 - ε) * -k₁ + ε * -k₁)) :=
    ((tendsto_mLocationScore_atTop hψm hbot hiP).const_mul _).add
      ((hbot.comp (tendsto_const_sub_atTop_atBot' x₀)).const_mul _)
  obtain ⟨θ', hθ'⟩ := eventually_atTop.1
    (hcT.eventually_lt_const (by linarith : (1 - ε) * -k₁ + ε * -k₁ < 0))
  -- (iii) the intermediate value theorem on `[B + 1, max (B+1) θ']`
  have hle : B + 1 ≤ max (B + 1) θ' := le_max_left _ _
  have hneg : (1 - ε) * mLocationScore ψ P (max (B + 1) θ') + ε * ψ (x₀ - max (B + 1) θ') < 0 :=
    hθ' _ (le_max_right _ _)
  have hcont : Continuous fun θ => (1 - ε) * mLocationScore ψ P θ + ε * ψ (x₀ - θ) :=
    (continuous_const.mul (continuous_mLocationScore hψc ⟨k₁ + k₂, hCb⟩)).add
      (continuous_const.mul (hψc.comp (continuous_const.sub continuous_id)))
  obtain ⟨θ, hθmem, hθ0⟩ :=
    intermediate_value_Icc' hle hcont.continuousOn (Set.mem_Icc.2 ⟨hneg.le, hpos.le⟩)
  have hroot : ∫ x, ψ (x - θ) ∂(contaminate P (Measure.dirac x₀) ε) = 0 := by
    rw [integral_contaminate_dirac hε0.le hε1.le (hiP θ)]
    exact hθ0
  exact ⟨x₀, θ, by linarith [hθmem.1], hroot⟩

/-- **Odd scores break down at `1/2`** (`MMY §3.2.1`: `k₁ = k₂` gives `ε* = 0.5`): for
`ε < 1/2` the contaminated roots stay uniformly bounded. -/
theorem mLocationRoot_bounded_of_odd {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ : ℝ → ℝ} {k ε : ℝ}
    -- USER-INPUT: monotone score with symmetric limits ∓k; MMY §3.2.1 (odd ψ)
    (hψm : Monotone ψ) (hbot : Tendsto ψ atBot (𝓝 (-k))) (htop : Tendsto ψ atTop (𝓝 k))
    (hk : 0 < k)
    -- USER-INPUT: contamination level below one half; MMY §3.2.1
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ∃ B : ℝ, ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → ∀ θ : ℝ,
      IsMLocationRoot ψ (contaminate P Q ε) θ → |θ| ≤ B := by
  refine mLocationRoot_bounded_of_contamination hψm hbot htop hk hk hε0 ?_
  have hkey : min k k / (k + k) = 1 / 2 := by
    rw [min_self, div_eq_iff (ne_of_gt (by linarith : (0:ℝ) < k + k))]
    ring
  rw [hkey]
  exact hε

/-- **The Huber location functional has asymptotic breakdown point `1/2`**
(`MMY §3.2.1`): the Huber score is monotone with limits `∓c`, so contaminated roots stay
bounded for every `ε < 1/2`. -/
theorem huberLocationRoot_bounded {P : Measure ℝ} [IsProbabilityMeasure P] {c ε : ℝ}
    (hc : 0 < c) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ∃ B : ℝ, ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → ∀ θ : ℝ,
      IsMLocationRoot (huberPsi c) (contaminate P Q ε) θ → |θ| ≤ B :=
  mLocationRoot_bounded_of_odd (huberPsi_monotone c) (huberPsi_tendsto_atBot c)
    (huberPsi_tendsto_atTop hc.le) hc hε0 hε

end StatLean.RobustStatistics
