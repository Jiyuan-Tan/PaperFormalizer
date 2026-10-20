module
public import StatLean.RobustStatistics.Core.Contamination
public import StatLean.RobustStatistics.LocationScale.Huber
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# The population M-location functional — roots of `E_P ψ(x - θ) = 0`

The asymptotic value of a location M-estimator at a distribution `P` is a root `θ` of the
population estimating equation `∫ ψ(x - θ) dP = 0` (`MMY §2.3.2`, eq. (2.22); §3.7,
eq. (3.51)). This file develops the root set as the *population-level concept*: the
population score `λ(θ) = ∫ ψ(x - θ) dP`, its continuity and monotonicity, existence of
roots by the intermediate value theorem (`MMY` Theorem 10.4 route), uniqueness under
strict monotonicity, and the mean as the special case `ψ = id`.

* `IsMLocationRoot ψ P θ` — `θ` solves the population M-equation (eq. (2.22)).
* `mLocationScore` — the population score `λ(θ) = ∫ ψ(x - θ) dP`.
* continuity (dominated convergence), antitonicity, and limits at `±∞` of `λ`.
* `exists_isMLocationRoot` — existence for bounded monotone continuous `ψ` with limits of
  opposite sign (`MMY` Thm 10.4).
* `isMLocationRoot_unique_of_strictMono` — uniqueness (`MMY` Thm 10.1(d) population form).
* `isMLocationRoot_id_iff` — `ψ = id` recovers the mean (`MMY §2.3.2`).

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.3.2 (eq.
(2.22)), §3.7 (eq. (3.51)), §10.1–10.2 (Theorems 10.1, 10.4, 10.5).

**Bibliographic comments.** Treating an estimator as a functional of the underlying
distribution goes back to R. von Mises, "On the asymptotic distribution of differentiable
statistical functions," *Ann. Math. Statist.* **18** (1947), 309–348; the population
M-equation and its root theory are Huber (1964) and ch. 3 of Huber and Ronchetti, *Robust
Statistics*, 2nd ed., Wiley, 2009.
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- **Population M-location root** (`MMY §2.3.2`, eq. (2.22)): `θ` solves
`∫ ψ(x - θ) dP = 0`. Beware the Bochner junk value: for non-integrable scores the
integral is `0` and the predicate holds vacuously — theorems consuming roots carry the
integrability of the score as an explicit input. -/
def IsMLocationRoot (ψ : ℝ → ℝ) (P : Measure ℝ) (θ : ℝ) : Prop :=
  ∫ x, ψ (x - θ) ∂P = 0

/-- The **population score** `λ(θ) = ∫ ψ(x - θ) dP` (`MMY §10.2`, eq. (10.5)). -/
noncomputable def mLocationScore (ψ : ℝ → ℝ) (P : Measure ℝ) (θ : ℝ) : ℝ :=
  ∫ x, ψ (x - θ) ∂P

theorem isMLocationRoot_iff_mLocationScore_eq_zero {ψ : ℝ → ℝ} {P : Measure ℝ} {θ : ℝ} :
    IsMLocationRoot ψ P θ ↔ mLocationScore ψ P θ = 0 := Iff.rfl

/-! ### Pointwise envelopes for monotone scores with finite limits

A monotone `ψ` is trapped between its two limits, `ψ(-∞) = -k₁ ≤ ψ ≤ k₂ = ψ(∞)`
(`MMY §3.2.1`). These private helpers supply the domination envelopes used throughout the
file (and are re-derived, not exported, so the frozen statements stay untouched). -/

/-- A monotone score is bounded below by its limit at `-∞`. -/
private theorem neg_le_psi {ψ : ℝ → ℝ} {k₁ : ℝ} (hψm : Monotone ψ)
    (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (u : ℝ) : -k₁ ≤ ψ u :=
  le_of_tendsto hbot (eventually_atBot.2 ⟨u, fun _ hv => hψm hv⟩)

/-- A monotone score is bounded above by its limit at `+∞`. -/
private theorem psi_le {ψ : ℝ → ℝ} {k₂ : ℝ} (hψm : Monotone ψ)
    (htop : Tendsto ψ atTop (𝓝 k₂)) (u : ℝ) : ψ u ≤ k₂ :=
  ge_of_tendsto htop (eventually_atTop.2 ⟨u, fun _ hv => hψm hv⟩)

/-- A monotone score with two finite limits is bounded (`MMY` Def 2.2: ψ-functions are
bounded). -/
private theorem psi_bounded {ψ : ℝ → ℝ} {k₁ k₂ : ℝ} (hψm : Monotone ψ)
    (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (htop : Tendsto ψ atTop (𝓝 k₂)) :
    ∃ C, ∀ u, |ψ u| ≤ C := by
  refine ⟨|k₁| + |k₂|, fun u => ?_⟩
  have h1 := neg_le_psi hψm hbot u
  have h2 := psi_le hψm htop u
  have h3 := le_abs_self k₁
  have h4 := le_abs_self k₂
  have h5 := abs_nonneg k₁
  have h6 := abs_nonneg k₂
  rw [abs_le]
  constructor <;> linarith

/-- Bounded measurable scores are integrable against a probability measure (the standing
integrability input for ψ-functions, `MMY` Def 2.2). -/
theorem integrable_psi_sub {ψ : ℝ → ℝ} {P : Measure ℝ} [IsProbabilityMeasure P]
    -- LEAN-ONLY: measurability of the score; automatic for the monotone/continuous ψ used
    (hψm : Measurable ψ)
    -- USER-INPUT: bounded score; MMY Def 2.2 context (ψ-functions are bounded)
    (hψb : ∃ C, ∀ u, |ψ u| ≤ C) (θ : ℝ) :
    Integrable (fun x => ψ (x - θ)) P := by
  obtain ⟨C, hC⟩ := hψb
  have hmeas : Measurable fun x : ℝ => ψ (x - θ) := hψm.comp (measurable_id.sub_const θ)
  refine Integrable.mono' (integrable_const C) hmeas.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs] using hC (x - θ)

/-- **Continuity of the population score** for bounded continuous `ψ` (dominated
convergence; `MMY §10.2`, the step making Theorem 10.4's IVT work). -/
theorem continuous_mLocationScore {ψ : ℝ → ℝ} {P : Measure ℝ} [IsProbabilityMeasure P]
    -- USER-INPUT: continuous score; MMY Thm 10.4 context
    (hψc : Continuous ψ)
    -- USER-INPUT: bounded score; MMY Def 2.2 context
    (hψb : ∃ C, ∀ u, |ψ u| ≤ C) :
    Continuous (mLocationScore ψ P) := by
  obtain ⟨C, hC⟩ := hψb
  have hint : ∀ θ : ℝ, Integrable (fun x => ψ (x - θ)) P := fun θ =>
    integrable_psi_sub hψc.measurable ⟨C, hC⟩ θ
  rw [continuous_iff_continuousAt]
  intro θ₀
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := P)
    (F := fun θ (x : ℝ) => ψ (x - θ)) (f := fun x => ψ (x - θ₀)) (l := 𝓝 θ₀)
    (fun _ => C)
    (Eventually.of_forall fun θ => (hint θ).aestronglyMeasurable)
    (Eventually.of_forall fun θ => Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC (x - θ))
    (integrable_const C)
    (Eventually.of_forall fun x =>
      (hψc.comp (continuous_const.sub continuous_id)).continuousAt)
  exact hlim

/-- The population score is antitone for monotone `ψ` (`MMY §10.1`: `Ψ(x,θ)` is
nonincreasing in `θ`). -/
theorem antitone_mLocationScore {ψ : ℝ → ℝ} {P : Measure ℝ} [IsProbabilityMeasure P]
    -- USER-INPUT: monotone score; MMY §2.3.1 (monotone M-estimators)
    (hψm : Monotone ψ)
    -- LEAN-ONLY: integrability of the translated scores, so the integral comparison is
    -- meaningful (bounded ψ discharges it via `integrable_psi_sub`)
    (hint : ∀ θ, Integrable (fun x => ψ (x - θ)) P) :
    Antitone (mLocationScore ψ P) := fun a b hab =>
  integral_mono (hint b) (hint a) fun x => hψm (by linarith)

/-- The translation `θ ↦ x - θ` drives `θ → ∞` to `-∞`. -/
private theorem tendsto_const_sub_atTop_atBot (x : ℝ) :
    Tendsto (fun θ : ℝ => x - θ) atTop atBot :=
  tendsto_atBot.2 fun b => eventually_atTop.2 ⟨x - b, fun _ hθ => by linarith⟩

/-- The translation `θ ↦ x - θ` drives `θ → -∞` to `+∞`. -/
private theorem tendsto_const_sub_atBot_atTop (x : ℝ) :
    Tendsto (fun θ : ℝ => x - θ) atBot atTop :=
  tendsto_atTop.2 fun b => eventually_atBot.2 ⟨x - b, fun _ hθ => by linarith⟩

/-- The population score inherits the limit of `ψ` at `-∞` as `θ → ∞` (dominated
convergence; `MMY §3.8.3`, eq. (3.62)–(3.63) machinery).

**Amendment to the frozen statement (wave F).** The hypothesis-free form is *false*: with
`ψ = max (· , -1)` (monotone, `ψ(-∞) = -1`) and a `P` with no first moment the translated
scores are never `P`-integrable, so `mLocationScore ψ P` is the Bochner junk value `0` at
every `θ` and cannot tend to `-k₁ = -1`. The minimal repair is the LEAN-ONLY
integrability input already carried by `antitone_mLocationScore`; every call site has it
(bounded ψ discharges it via `integrable_psi_sub`). -/
theorem tendsto_mLocationScore_atTop {ψ : ℝ → ℝ} {P : Measure ℝ} [IsProbabilityMeasure P]
    {k₁ : ℝ}
    -- USER-INPUT: monotone score with limit -k₁ at -∞; MMY §3.2.1
    (hψm : Monotone ψ) (hbot : Tendsto ψ atBot (𝓝 (-k₁)))
    -- LEAN-ONLY: integrability of the translated scores, ruling out the Bochner junk
    -- value (see the amendment note above)
    (hint : ∀ θ, Integrable (fun x => ψ (x - θ)) P) :
    Tendsto (mLocationScore ψ P) atTop (𝓝 (-k₁)) := by
  have hlow := neg_le_psi hψm hbot
  have hbd : Integrable (fun x : ℝ => |k₁| + |ψ (x - 0)|) P :=
    (integrable_const |k₁|).add (hint 0).abs
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := P)
    (F := fun θ (x : ℝ) => ψ (x - θ)) (f := fun _ : ℝ => -k₁) (l := atTop)
    (fun x => |k₁| + |ψ (x - 0)|)
    (Eventually.of_forall fun θ => (hint θ).aestronglyMeasurable)
    (eventually_atTop.2 ⟨0, fun θ hθ => Eventually.of_forall fun x => by
      have h1 : ψ (x - θ) ≤ ψ (x - 0) := hψm (by linarith)
      have h2 := hlow (x - θ)
      have h3 := le_abs_self k₁
      have h4 := le_abs_self (ψ (x - 0))
      have h5 := abs_nonneg k₁
      have h6 := abs_nonneg (ψ (x - 0))
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith⟩)
    hbd
    (Eventually.of_forall fun x => hbot.comp (tendsto_const_sub_atTop_atBot x))
  simpa [mLocationScore] using! hlim

/-- The population score inherits the limit of `ψ` at `+∞` as `θ → -∞`.

**Amendment to the frozen statement (wave F).** See `tendsto_mLocationScore_atTop`: the
LEAN-ONLY integrability input is required to rule out the Bochner junk value. -/
theorem tendsto_mLocationScore_atBot {ψ : ℝ → ℝ} {P : Measure ℝ} [IsProbabilityMeasure P]
    {k₂ : ℝ}
    -- USER-INPUT: monotone score with limit k₂ at +∞; MMY §3.2.1
    (hψm : Monotone ψ) (htop : Tendsto ψ atTop (𝓝 k₂))
    -- LEAN-ONLY: integrability of the translated scores, ruling out the Bochner junk value
    (hint : ∀ θ, Integrable (fun x => ψ (x - θ)) P) :
    Tendsto (mLocationScore ψ P) atBot (𝓝 k₂) := by
  have hhigh := psi_le hψm htop
  have hbd : Integrable (fun x : ℝ => |k₂| + |ψ (x - 0)|) P :=
    (integrable_const |k₂|).add (hint 0).abs
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := P)
    (F := fun θ (x : ℝ) => ψ (x - θ)) (f := fun _ : ℝ => k₂) (l := atBot)
    (fun x => |k₂| + |ψ (x - 0)|)
    (Eventually.of_forall fun θ => (hint θ).aestronglyMeasurable)
    (eventually_atBot.2 ⟨0, fun θ hθ => Eventually.of_forall fun x => by
      have h1 : ψ (x - 0) ≤ ψ (x - θ) := hψm (by linarith)
      have h2 := hhigh (x - θ)
      have h3 := le_abs_self k₂
      have h4 := neg_abs_le (ψ (x - 0))
      have h5 := abs_nonneg k₂
      have h6 := abs_nonneg (ψ (x - 0))
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith⟩)
    hbd
    (Eventually.of_forall fun x => htop.comp (tendsto_const_sub_atBot_atTop x))
  simpa [mLocationScore] using! hlim

/-- **Existence of a population root** (`MMY` Theorem 10.4 route): a continuous monotone
score with limits `-k₁ < 0 < k₂` produces a continuous population score crossing zero, so
the intermediate value theorem yields a root. -/
theorem exists_isMLocationRoot {ψ : ℝ → ℝ} {P : Measure ℝ} [IsProbabilityMeasure P]
    {k₁ k₂ : ℝ}
    -- USER-INPUT: continuous monotone score; MMY Thm 10.1/10.4
    (hψc : Continuous ψ) (hψm : Monotone ψ)
    -- USER-INPUT: score limits of opposite sign (MMY (10.3): lim_{θ→θ₁} Ψ > 0 > lim_{θ→θ₂} Ψ)
    (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (htop : Tendsto ψ atTop (𝓝 k₂))
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    ∃ θ : ℝ, IsMLocationRoot ψ P θ := by
  obtain ⟨C, hC⟩ := psi_bounded hψm hbot htop
  have hint : ∀ θ : ℝ, Integrable (fun x => ψ (x - θ)) P := fun θ =>
    integrable_psi_sub hψc.measurable ⟨C, hC⟩ θ
  have hcont : Continuous (mLocationScore ψ P) := continuous_mLocationScore hψc ⟨C, hC⟩
  have hT : Tendsto (mLocationScore ψ P) atTop (𝓝 (-k₁)) :=
    tendsto_mLocationScore_atTop hψm hbot hint
  have hB : Tendsto (mLocationScore ψ P) atBot (𝓝 k₂) :=
    tendsto_mLocationScore_atBot hψm htop hint
  obtain ⟨b, hb⟩ := eventually_atTop.1 (hT.eventually_lt_const (by linarith : -k₁ < 0))
  obtain ⟨a, ha⟩ := eventually_atBot.1 (hB.eventually_const_lt (by linarith : (0:ℝ) < k₂))
  have hab : min a b ≤ max a b := min_le_max
  have hga : 0 < mLocationScore ψ P (min a b) := ha _ (min_le_left a b)
  have hgb : mLocationScore ψ P (max a b) < 0 := hb _ (le_max_right a b)
  have hmem : (0 : ℝ) ∈ Set.Icc (mLocationScore ψ P (max a b)) (mLocationScore ψ P (min a b)) :=
    ⟨hgb.le, hga.le⟩
  obtain ⟨θ, -, hθ⟩ :=
    intermediate_value_Icc' hab hcont.continuousOn hmem
  exact ⟨θ, hθ⟩

/-- **Uniqueness of the population root** for strictly monotone scores (`MMY` Theorem
10.1(d), population form). -/
theorem isMLocationRoot_unique_of_strictMono {ψ : ℝ → ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P] {θ₁ θ₂ : ℝ}
    -- USER-INPUT: strictly monotone score; MMY Thm 10.1(d)
    (hψ : StrictMono ψ)
    -- LEAN-ONLY: the two root scores are genuinely integrable, ruling out Bochner junk
    -- roots (see the `IsMLocationRoot` docstring)
    (hint₁ : Integrable (fun x => ψ (x - θ₁)) P)
    (hint₂ : Integrable (fun x => ψ (x - θ₂)) P)
    (h₁ : IsMLocationRoot ψ P θ₁) (h₂ : IsMLocationRoot ψ P θ₂) :
    θ₁ = θ₂ := by
  have key : ∀ a b : ℝ, a < b → Integrable (fun x => ψ (x - a)) P →
      Integrable (fun x => ψ (x - b)) P → IsMLocationRoot ψ P a → IsMLocationRoot ψ P b →
      False := by
    intro a b hab hia hib hra hrb
    have hra' : ∫ x, ψ (x - a) ∂P = 0 := hra
    have hrb' : ∫ x, ψ (x - b) ∂P = 0 := hrb
    have hpos : ∀ x : ℝ, 0 < ψ (x - a) - ψ (x - b) := fun x =>
      sub_pos.2 (hψ (by linarith : x - b < x - a))
    have hd : Integrable (fun x => ψ (x - a) - ψ (x - b)) P := hia.sub hib
    have hz : ∫ x, (ψ (x - a) - ψ (x - b)) ∂P = 0 := by
      rw [integral_sub hia hib, hra', hrb', sub_zero]
    have hsupp : Function.support (fun x => ψ (x - a) - ψ (x - b)) = Set.univ := by
      ext x
      simp [Function.mem_support, (hpos x).ne']
    have hlt : 0 < ∫ x, (ψ (x - a) - ψ (x - b)) ∂P := by
      rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hd, hsupp, measure_univ]
      exact zero_lt_one
    exact absurd hz hlt.ne'
  rcases lt_trichotomy θ₁ θ₂ with h | h | h
  · exact (key θ₁ θ₂ h hint₁ hint₂ h₁ h₂).elim
  · exact h
  · exact (key θ₂ θ₁ h hint₂ hint₁ h₂ h₁).elim

/-- **The identity score recovers the mean** (`MMY §2.3.2`: for `ψ(x) = x`, eq. (2.22)
gives `μ₀ = E x`). -/
theorem isMLocationRoot_id_iff {P : Measure ℝ} [IsProbabilityMeasure P] {θ : ℝ}
    -- USER-INPUT: P has a well-defined mean; MMY §2.3.2
    (hP : Integrable id P) :
    IsMLocationRoot id P θ ↔ θ = ∫ x, x ∂P := by
  have hid : Integrable (fun x : ℝ => x) P := hP
  have hsplit : ∫ x, (id (x - θ)) ∂P = (∫ x, x ∂P) - θ := by
    simp only [id_eq]
    rw [integral_sub hid (integrable_const θ)]
    simp
  rw [IsMLocationRoot, hsplit, sub_eq_zero]
  exact eq_comm

/-- Population Huber roots exist for every probability measure (`MMY §2.3.2` + Thm
10.4): the Huber score is continuous, monotone, with limits `∓c`. -/
theorem exists_isMLocationRoot_huber {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ}
    (hc : 0 < c) :
    ∃ θ : ℝ, IsMLocationRoot (huberPsi c) P θ :=
  exists_isMLocationRoot (huberPsi_continuous c) (huberPsi_monotone c)
    (huberPsi_tendsto_atBot c) (huberPsi_tendsto_atTop hc.le) hc hc

end StatLean.RobustStatistics
