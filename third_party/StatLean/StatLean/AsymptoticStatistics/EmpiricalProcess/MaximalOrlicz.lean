module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import StatLean.AsymptoticStatistics.EmpiricalProcess.MaximalBernstein
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.IdentDistrib

@[expose] public section

/-!
# Orlicz machinery for the finite-class supremum bound

This file proves the finite-class supremum bound of vdV §19.6 Lemma 19.33.

The proof follows the tight Orlicz route rather than a naive union bound. Key ingredients:

1. **Orlicz functions** `ψ₁(x) = exp x − 1`, `ψ₂(x) = exp(x²) − 1`, with
   inverses `ψ₁⁻¹(u) = log(1+u)` and `ψ₂⁻¹(u) = √(log(1+u))`. Convexity
   of `ψ₁` on ℝ follows from `Real.convexOn_exp`. Convexity of `ψ₂` on
   `[0, ∞)` requires the composition `exp ∘ (·)²` argument (we restrict
   to non-negative arguments because the Orlicz norm is always applied
   to `|X|`).

2. **Tail-to-Orlicz integral lemmas.** Sub-exponential tail
   `μ{|X| > x} ≤ 2 exp(−x/c)` integrated against `ψ₁(·/c)`'s derivative
   yields `∫ ψ₁(|X|/(2c)) dμ ≤ 1` — i.e. `‖X‖_{ψ₁} ≤ 2c`. Analogously for
   sub-Gaussian tails and `ψ₂`.

3. **Max bound via Jensen.** For convex `ψ` and finite class
   `{X_i : i ∈ ι}` with `‖X_i‖_ψ ≤ a` for all `i`,
   `∫ ⨆_i |X_i|/a dμ ≤ ψ⁻¹(|ι|)`. Applied to `ψ₁`: `≤ log(1 + |ι|)`;
   applied to `ψ₂`: `≤ √(log(1 + |ι|))`.

4. **Truncation at threshold.** Split each `G_n f = A_f + B_f` via
   `1{|f| > b}` for an appropriate threshold `b`. Apply Bernstein
   (`bernstein_inequality`) to derive
   sub-exponential tails for `A_f` and sub-Gaussian tails for `B_f`.

5. **Combination.** Triangle inequality gives
   `∫ ⨆_i |G_n f_i| dμ ≤ K · (M log(1+|ι|)/√n + σ √log(1+|ι|))`.

The principal declarations are `finite_sup_bound_aux` and
`finite_sup_bound_orlicz_core`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.6.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter Real
open scoped ENNReal Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Orlicz functions ψ₁ and ψ₂. -/

/-- The Orlicz function `ψ₁(x) = exp x − 1`.

vdV §19.6: the natural Orlicz function for sub-exponential tails. -/
noncomputable def psi_1 (x : ℝ) : ℝ := Real.exp x - 1

/-- The Orlicz function `ψ₂(x) = exp(x²) − 1`.

vdV §19.6: the natural Orlicz function for sub-Gaussian tails. -/
noncomputable def psi_2 (x : ℝ) : ℝ := Real.exp (x ^ 2) - 1

/-- Inverse of `ψ₁`: `ψ₁⁻¹(u) = log(1 + u)`. -/
noncomputable def psi_1_inv (u : ℝ) : ℝ := Real.log (1 + u)

/-- Inverse of `ψ₂` on `[0, ∞)`: `ψ₂⁻¹(u) = √log(1 + u)`. -/
noncomputable def psi_2_inv (u : ℝ) : ℝ := Real.sqrt (Real.log (1 + u))

/-! ### Trivial closed facts about ψ₁, ψ₂. -/

@[simp] lemma psi_1_zero : psi_1 0 = 0 := by
  unfold psi_1; rw [Real.exp_zero]; ring

@[simp] lemma psi_2_zero : psi_2 0 = 0 := by
  unfold psi_2; rw [show (0 : ℝ) ^ 2 = 0 from by ring, Real.exp_zero]; ring

@[simp] lemma psi_1_inv_zero : psi_1_inv 0 = 0 := by
  unfold psi_1_inv; simp

@[simp] lemma psi_2_inv_zero : psi_2_inv 0 = 0 := by
  unfold psi_2_inv; simp

/-- `ψ₁` is monotone on ℝ. -/
lemma psi_1_monotone : Monotone psi_1 := by
  intro x y hxy
  unfold psi_1
  exact sub_le_sub_right (Real.exp_monotone hxy) 1

/-- `ψ₁` is convex on ℝ.

This follows from `convexOn_exp` (the convexity of the exponential
function on ℝ) by subtracting the constant `1`. -/
lemma psi_1_convexOn : ConvexOn ℝ Set.univ psi_1 := by
  -- `ψ₁ = exp − 1`.  Pointwise subtraction of a constant from a convex
  -- function is convex; use `convexOn_exp` (convexity of `Real.exp`) +
  -- `ConvexOn.sub_const` semantics by hand.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hexp := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  -- `hexp : Real.exp (a • x + b • y) ≤ a • Real.exp x + b • Real.exp y`.
  -- Goal (after `unfold psi_1`):
  --   `Real.exp (a • x + b • y) - 1 ≤ a • (Real.exp x - 1) + b • (Real.exp y - 1)`.
  -- RHS = `a • exp x + b • exp y - (a + b) = a • exp x + b • exp y - 1`.
  unfold psi_1
  have hsmul_sub : ∀ (c r : ℝ), c • (r - 1) = c • r - c := by
    intro c r; simp [smul_eq_mul, mul_sub]
  rw [hsmul_sub a (Real.exp x), hsmul_sub b (Real.exp y)]
  have hab' : a + b = 1 := hab
  -- `a • exp x - a + (b • exp y - b) = (a • exp x + b • exp y) - 1`.
  have heq : a • Real.exp x - a + (b • Real.exp y - b)
      = a • Real.exp x + b • Real.exp y - 1 := by
    have : a • Real.exp x - a + (b • Real.exp y - b)
        = (a • Real.exp x + b • Real.exp y) - (a + b) := by ring
    rw [this, hab']
  linarith [hexp, heq]

/-- The image of a non-negative real under `ψ₁` is non-negative. -/
lemma psi_1_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psi_1 x := by
  unfold psi_1
  have h1 : Real.exp 0 ≤ Real.exp x := Real.exp_monotone hx
  rw [Real.exp_zero] at h1
  linarith

/-- The image of a non-negative real under `ψ₂` is non-negative. -/
lemma psi_2_nonneg_of_nonneg {x : ℝ} (_hx : 0 ≤ x) : 0 ≤ psi_2 x := by
  unfold psi_2
  have h1 : Real.exp 0 ≤ Real.exp (x ^ 2) := Real.exp_monotone (sq_nonneg _)
  rw [Real.exp_zero] at h1
  linarith

/-! ### Pisier ψ-max maximal inequalities.

The lemmas below state vdV's Pisier ψ_p-max maximal inequality
(Lem 8.4 in the Pisier formulation; used in the proof of Lem 19.33 in
vdV §19.6) in terms of the underlying *tail bound*
on each `Z_i`, rather than the Orlicz norm `‖Z_i‖_{ψ_p}` directly.

The proof combines two estimates:

* `psi_p_layer_cake_meas_bound` — pure measure-theory bridge.
  Combines Mathlib's `lintegral_eq_lintegral_meas_lt` (layer-cake formula),
  `measure_iUnion_fintype_le` (finite-union bound), the per-`i` tail
  hypothesis, `ENNReal.ofReal_sum_of_nonneg`, and the level-set cap
  at `1` via `prob_le_one` (from `IsProbabilityMeasure μ`).
* `psi_p_calculus_integral_bound` — pure real-analysis calculus
  integral: `∫⁻ t in Ioi 0, min 1 (ofReal(N · 2 · exp(−tail))) dt
  ≤ ofReal(12 · scale · ψ_p⁻¹(1 + N))`.

Constants `12` here come from the standard Pisier ψ-max constant
combined with the ψ-norm → L¹ bridge (`E|Z| ≤ ‖Z‖_{ψ_p}` for `p = 1, 2`
under the convention that `ψ_p(0) = 0` and `ψ_p` is convex; the bridge
is `E|Z| = ∫ |Z| dμ ≤ ‖Z‖_{ψ_p} · ψ_p⁻¹(E[ψ_p(|Z|/‖Z‖_{ψ_p})])
≤ ‖Z‖_{ψ_p} · ψ_p⁻¹(1)`, finite since the Orlicz norm is the infimum
making the expectation `≤ 1`). The constant `24` in
`orlicz_bernstein_max_l1_bound` is `2 · 12` from the triangle
decomposition into sub-Gaussian and sub-exponential halves.
-/

/-- **ψ₂ layer-cake bridge** — measure-theory side of the ψ₂ Pisier
maximal inequality used in `orlicz_psi2_max_l1_bound`.

Combines the layer-cake formula (Mathlib `lintegral_eq_lintegral_meas_lt`),
the finite-union bound on `{ω | t < ⨆_i |Z_i ω|}`, and the per-`i`
sub-Gaussian tail hypothesis, capping the level-set measure at `1` via
`IsProbabilityMeasure μ`, to produce the layer-cake form

`∫⁻ ω, ofReal(⨆_i |Z_i ω|) ∂μ ≤ ∫⁻ t in Ioi 0,
    min 1 (ofReal((Fintype.card ι : ℝ) · 2 · exp(-t²/(2σ²))))`.

Pipeline:
* empty-ι case → both sides 0 (via `Real.iSup_of_isEmpty`);
* nonempty case → `lintegral_eq_lintegral_meas_lt` (after proving
  pointwise non-negativity of ⨆ and measurability via `Finset.sup'`)
  → `lintegral_mono_ae` + `ae_restrict_iff'` reduction to pointwise
  → set decomposition `{ω | t < ⨆_i ...} = ⋃ i, {ω | t < |Z_i ω|}`
  (via contrapositive of `ciSup_le` + `le_ciSup`) → cap by `1` via
  `le_min`/`prob_le_one` → union bound + `ENNReal.ofReal_sum_of_nonneg`
  + `Finset.sum_const` + `nsmul_eq_mul` for the explicit form.
-/
private lemma psi2_layer_cake_meas_bound
    {ι : Type*} [Fintype ι] {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (_Z : ι → Ξ → ℝ) (_hZ_meas : ∀ i, Measurable (_Z i))
    {σ_eff : ℝ} (_hσ_eff : 0 ≤ σ_eff)
    (_h_tail : ∀ i, ∀ t : ℝ, 0 < t →
        μ {ω | t < |_Z i ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * σ_eff ^ 2)))) :
    ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, |_Z i ω|) ∂μ
      ≤ ∫⁻ t in Set.Ioi (0:ℝ),
          min 1 (ENNReal.ofReal ((Fintype.card ι : ℝ) *
            (2 * Real.exp (-(t ^ 2) / (2 * σ_eff ^ 2))))) ∂volume := by
  -- Empty-ι edge case: ⨆ over empty = 0, so LHS lintegral = 0.
  by_cases hι : Nonempty ι
  swap
  · rw [not_nonempty_iff] at hι
    have h_sup_zero : ∀ ω : Ξ, (⨆ i : ι, |_Z i ω|) = 0 := fun ω =>
      Real.iSup_of_isEmpty _
    simp_rw [h_sup_zero, ENNReal.ofReal_zero, MeasureTheory.lintegral_zero]
    exact zero_le
  -- ===== Nonempty ι. =====
  -- Step 1: pointwise non-negativity of ⨆_i |Z_i ω|.
  have h_iSup_nn : ∀ ω, 0 ≤ ⨆ i : ι, |_Z i ω| := by
    intro ω
    obtain ⟨i₀⟩ := hι
    have h_bdd : BddAbove (Set.range fun i : ι => |_Z i ω|) :=
      Set.Finite.bddAbove (Set.finite_range _)
    exact le_trans (abs_nonneg _) (le_ciSup h_bdd i₀)
  -- Step 2: measurability of ω ↦ ⨆_i |Z_i ω| via Finset.sup'.
  have h_iSup_meas : Measurable (fun ω => ⨆ i : ι, |_Z i ω|) := by
    have h_fun_eq : (fun ω => ⨆ i : ι, |_Z i ω|)
        = Finset.univ.sup' Finset.univ_nonempty
            (fun i (ω : Ξ) => |_Z i ω|) := by
      funext ω
      rw [← Finset.sup'_univ_eq_ciSup]
      exact (Finset.sup'_apply Finset.univ_nonempty
        (fun i (ω : Ξ) => |_Z i ω|) ω).symm
    rw [h_fun_eq]
    exact Finset.measurable_sup' Finset.univ_nonempty
      (fun i _ => (_hZ_meas i).norm)
  -- Step 3: layer-cake formula.
  rw [lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall h_iSup_nn) h_iSup_meas.aemeasurable]
  -- Step 4: reduce to pointwise via lintegral_mono_ae.
  apply MeasureTheory.lintegral_mono_ae
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall ?_
  intro t ht
  -- ht : t ∈ Set.Ioi 0, i.e. 0 < t.
  rw [Set.mem_Ioi] at ht
  haveI : Nonempty ι := hι
  -- Set decomposition: {ω | t < ⨆_i |Z_i ω|} = ⋃ i, {ω | t < |Z_i ω|}.
  have h_set_eq : {ω | t < ⨆ i : ι, |_Z i ω|}
      = ⋃ i : ι, {ω | t < |_Z i ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hlt
      -- Contrapositive of ciSup_le.
      by_contra hne
      push Not at hne
      have h_sup_le : (⨆ i : ι, |_Z i ω|) ≤ t :=
        ciSup_le hne
      linarith
    · rintro ⟨i, hi⟩
      have h_bdd_ω : BddAbove (Set.range fun i : ι => |_Z i ω|) :=
        Set.Finite.bddAbove (Set.finite_range _)
      exact lt_of_lt_of_le hi (le_ciSup h_bdd_ω i)
  rw [h_set_eq]
  -- Cap by 1 + ofReal bound. Both bounds combine via `le_min`.
  refine le_min prob_le_one ?_
  -- The union bound gives
  -- `μ (⋃ i, {ω | t < |Z_i ω|}) ≤ ofReal((card) · 2 · exp(...))`.
  -- Chain: μ (⋃) ≤ ∑ μ ≤ ∑ ofReal(2 exp(...)) = ofReal(∑ 2 exp(...)) = ofReal(card · 2 · exp(...)).
  have h_2exp_nn : 0 ≤ 2 * Real.exp (-(t ^ 2) / (2 * σ_eff ^ 2)) := by positivity
  calc μ (⋃ i : ι, {ω | t < |_Z i ω|})
      ≤ ∑ i : ι, μ {ω | t < |_Z i ω|} :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι,
          ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * σ_eff ^ 2))) :=
        Finset.sum_le_sum (fun i _ => _h_tail i t ht)
    _ = ENNReal.ofReal
          (∑ _i : ι, 2 * Real.exp (-(t ^ 2) / (2 * σ_eff ^ 2))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => h_2exp_nn)]
    _ = ENNReal.ofReal
          ((Fintype.card ι : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * σ_eff ^ 2)))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **ψ₂ deterministic calculus integral** used in
`orlicz_psi2_max_l1_bound`.

Pure real-analysis (no probability content):
`∫⁻ t in Ioi 0, min 1 (ofReal((N:ℝ) · 2 · exp(-t²/(2σ²)))) dt
  ≤ ofReal(12 · σ · √log(1 + N))`.

The `N ≥ 1` case is closed via the textbook split-at-crossover argument:
split the domain at the crossover threshold
`t* := σ · √(2 · log(1 + 2N))` (where the exponential bound first dips
below 1).
* For `t ≤ t*`: the integrand is bounded by `1`, contributing `≤ t*`.
* For `t > t*`: `t² ≥ t · t*` so `exp(-t²/(2σ²)) ≤ exp(-t · t*/(2σ²))`,
  giving the integrand `≤ 2N · exp(a · t)` with `a := -t*/(2σ²) < 0`.
  This integrates to `4Nσ² / ((1+2N) · t*)`, bounded by `t*` itself (using
  `2N ≤ (1+2N) log(1+2N)` for `N ≥ 1`, since `log 3 > 1`).
* Sum: `t* + t* = 2σ · √(2 log(1 + 2N)) ≤ 4σ · √log(1 + N) ≤ 12 σ √log(1 + N)`
  (using `log(1+2N) ≤ 2 log(1+N)` for `N ≥ 1`).

Edge cases:
* `N = 0` is closed inline (integrand identically 0).
* The `σ = 0` corner is excluded by the signature `0 < σ`.  At σ = 0,
  Lean's `a/0 = 0` convention makes `exp(-(t²)/(2·0²)) = exp 0 = 1`, so
  the integrand for N ≥ 1 is `min 1 (ofReal(2N)) = 1` and LHS = ∞ over
  `Ioi 0`, while RHS = 0 — the statement is mathematically false for
  σ = 0, N ≥ 1, so `0 < σ` propagates up through
  `orlicz_psi2_max_l1_bound`, with the `σ_eff = 0` cases split inline in
  `orlicz_bernstein_{truncated,}max_l1_bound`, and the
  `M = σ = 0 ⇒ g ≡ 0 ⇒ Z ≡ 0` corner dispatched at the outermost
  `finite_sup_bound_orlicz_core` level.
-/
private lemma psi2_calculus_integral_bound
    (N : ℕ) {σ : ℝ} (hσ_pos : 0 < σ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        min 1 (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))))
        ∂volume
      ≤ ENNReal.ofReal (12 * σ * Real.sqrt (Real.log (1 + N))) := by
  -- Edge case N = 0: integrand identically 0; LHS = 0; RHS = 0.
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h_integrand : ∀ t : ℝ,
        min (1 : ℝ≥0∞)
          (ENNReal.ofReal (((0 : ℕ) : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))))
        = 0 := by
      intro t
      simp [ENNReal.ofReal_zero]
    simp_rw [h_integrand]
    rw [MeasureTheory.lintegral_zero]
    exact zero_le
  -- N ≥ 1, σ > 0: textbook split-at-crossover.
  have hNr_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNr_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h_1p2N_pos : (0 : ℝ) < 1 + 2 * (N : ℝ) := by linarith
  have h_1pN_pos : (0 : ℝ) < 1 + (N : ℝ) := by linarith
  have h_log_2N_pos : 0 < Real.log (1 + 2 * (N : ℝ)) :=
    Real.log_pos (by linarith)
  have h_log_N_pos : 0 < Real.log (1 + (N : ℝ)) :=
    Real.log_pos (by linarith)
  have h_2log2N_pos : 0 < 2 * Real.log (1 + 2 * (N : ℝ)) := by linarith
  have h_sqrt_2log2N_pos : 0 < Real.sqrt (2 * Real.log (1 + 2 * (N : ℝ))) :=
    Real.sqrt_pos.mpr h_2log2N_pos
  set tstar : ℝ := σ * Real.sqrt (2 * Real.log (1 + 2 * (N : ℝ))) with hts_def
  have hts_pos : 0 < tstar := mul_pos hσ_pos h_sqrt_2log2N_pos
  have hts_nn : 0 ≤ tstar := hts_pos.le
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
  have hσ_sq_pos : 0 < σ ^ 2 := by positivity
  have h2σ_sq_pos : 0 < 2 * σ ^ 2 := by positivity
  -- tstar² = 2σ² · log(1+2N).
  have h_tstar_sq : tstar ^ 2 = 2 * σ ^ 2 * Real.log (1 + 2 * (N : ℝ)) := by
    rw [hts_def, mul_pow, Real.sq_sqrt h_2log2N_pos.le]
    ring
  -- Step 1: split Ioi 0 = Ioc 0 tstar ∪ Ioi tstar.
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 tstar ∪ Set.Ioi tstar from
        (Set.Ioc_union_Ioi_eq_Ioi hts_nn).symm,
      MeasureTheory.lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
  -- Step 2: first piece — integrand bounded by 1.
  have h_first : ∫⁻ t in Set.Ioc 0 tstar,
        min (1 : ℝ≥0∞)
          (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))))
        ∂volume
      ≤ ENNReal.ofReal tstar := by
    calc ∫⁻ t in Set.Ioc 0 tstar,
            min (1 : ℝ≥0∞)
              (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))))
            ∂volume
        ≤ ∫⁻ _t in Set.Ioc 0 tstar, (1 : ℝ≥0∞) ∂volume := by
            apply MeasureTheory.lintegral_mono
            intro t; exact min_le_left _ _
      _ = volume (Set.Ioc (0:ℝ) tstar) := MeasureTheory.setLIntegral_one _
      _ = ENNReal.ofReal (tstar - 0) := Real.volume_Ioc
      _ = ENNReal.ofReal tstar := by rw [sub_zero]
  -- Step 3: second piece via Gaussian-to-exponential bridge with `a := -tstar/(2σ²)`.
  set a : ℝ := -tstar / (2 * σ ^ 2) with ha_def
  have ha_neg : a < 0 := by
    rw [ha_def, neg_div]
    exact neg_lt_zero.mpr (div_pos hts_pos h2σ_sq_pos)
  have h_integrable :
      MeasureTheory.IntegrableOn
        (fun t => 2 * (N : ℝ) * Real.exp (a * t)) (Set.Ioi tstar) volume :=
    (integrableOn_exp_mul_Ioi ha_neg tstar).const_mul (2 * (N : ℝ))
  have h_pt_nn : ∀ t : ℝ, 0 ≤ 2 * (N : ℝ) * Real.exp (a * t) := fun t =>
    mul_nonneg (by linarith) (Real.exp_pos _).le
  -- Pointwise: for t > tstar, integrand bounded by `ofReal(2N · exp(a · t))`.
  have h_ptwise : ∀ t : ℝ, tstar < t →
      min (1 : ℝ≥0∞)
          (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))))
        ≤ ENNReal.ofReal (2 * (N : ℝ) * Real.exp (a * t)) := by
    intro t ht
    have ht_pos' : 0 < t := lt_trans hts_pos ht
    have h_sq_ge : t * tstar ≤ t ^ 2 := by nlinarith [hts_nn, ht.le]
    have h_at_eq : a * t = -(t * tstar) / (2 * σ ^ 2) := by
      rw [ha_def]; ring
    have h_div_le : -(t ^ 2) / (2 * σ ^ 2) ≤ a * t := by
      rw [h_at_eq]
      have h_neg : -(t ^ 2) ≤ -(t * tstar) := by linarith
      exact div_le_div_of_nonneg_right h_neg h2σ_sq_pos.le
    have h_exp_le : Real.exp (-(t ^ 2) / (2 * σ ^ 2)) ≤ Real.exp (a * t) :=
      Real.exp_le_exp.mpr h_div_le
    refine le_trans (min_le_right _ _) ?_
    apply ENNReal.ofReal_le_ofReal
    have h_exp_nn : 0 ≤ Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := (Real.exp_pos _).le
    nlinarith [hNr_pos.le, h_exp_le, h_exp_nn]
  -- a · tstar = -log(1+2N).
  have h_a_ts : a * tstar = -Real.log (1 + 2 * (N : ℝ)) := by
    have h_aux : a * tstar = -(tstar ^ 2) / (2 * σ ^ 2) := by
      rw [ha_def]; ring
    rw [h_aux, h_tstar_sq]
    field_simp
  -- exp(a · tstar) = 1/(1+2N).
  have h_exp_a_ts : Real.exp (a * tstar) = (1 + 2 * (N : ℝ))⁻¹ := by
    rw [h_a_ts, Real.exp_neg, Real.exp_log h_1p2N_pos]
  -- Second-piece bound: tail integral ≤ tstar (key inequality `2N ≤ (1+2N) log(1+2N)`).
  have h_second : ∫⁻ t in Set.Ioi tstar,
        min (1 : ℝ≥0∞)
          (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))))
        ∂volume
      ≤ ENNReal.ofReal tstar := by
    have h_1p2N_ne : (1 + 2 * (N : ℝ)) ≠ 0 := ne_of_gt h_1p2N_pos
    have hts_ne : tstar ≠ 0 := ne_of_gt hts_pos
    have h2σ_sq_ne : 2 * σ ^ 2 ≠ 0 := ne_of_gt h2σ_sq_pos
    -- Tail integral closed form: 4Nσ²/((1+2N) · tstar).
    have h_tail_value :
        (∫ t in Set.Ioi tstar, 2 * (N : ℝ) * Real.exp (a * t) ∂volume)
          = 4 * (N : ℝ) * σ ^ 2 / ((1 + 2 * (N : ℝ)) * tstar) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi ha_neg]
      rw [h_a_ts, Real.exp_neg, Real.exp_log h_1p2N_pos]
      rw [ha_def]
      field_simp
      ring
    -- 4Nσ²/((1+2N) tstar) ≤ tstar (from 2N ≤ (1+2N) log(1+2N) for N ≥ 1).
    have h_tail_bound :
        4 * (N : ℝ) * σ ^ 2 / ((1 + 2 * (N : ℝ)) * tstar) ≤ tstar := by
      rw [div_le_iff₀ (mul_pos h_1p2N_pos hts_pos)]
      rw [show tstar * ((1 + 2 * (N : ℝ)) * tstar)
            = (1 + 2 * (N : ℝ)) * tstar ^ 2 from by ring]
      rw [h_tstar_sq]
      -- Goal: 4Nσ² ≤ (1+2N) · (2σ² · log(1+2N)).
      have h_log3_gt_1 : (1 : ℝ) < Real.log 3 := by
        have he : Real.exp 1 < 3 := Real.exp_one_lt_three
        have h1 : Real.log (Real.exp 1) < Real.log 3 :=
          Real.log_lt_log (Real.exp_pos 1) he
        rwa [Real.log_exp] at h1
      have h_log_2N_ge_log3 : Real.log 3 ≤ Real.log (1 + 2 * (N : ℝ)) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h_log_2N_gt_1 : (1 : ℝ) < Real.log (1 + 2 * (N : ℝ)) :=
        lt_of_lt_of_le h_log3_gt_1 h_log_2N_ge_log3
      have h_key :
          (1 + 2 * (N : ℝ)) * Real.log (1 + 2 * (N : ℝ)) > 2 * (N : ℝ) := by
        have h_mul := mul_lt_mul_of_pos_left h_log_2N_gt_1 h_1p2N_pos
        nlinarith [h_mul, hNr_ge_one]
      nlinarith [hσ_sq_pos, h_key, h_1p2N_pos.le]
    calc ∫⁻ t in Set.Ioi tstar,
            min (1 : ℝ≥0∞)
              (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))))
            ∂volume
        ≤ ∫⁻ t in Set.Ioi tstar,
            ENNReal.ofReal (2 * (N : ℝ) * Real.exp (a * t)) ∂volume := by
            apply MeasureTheory.lintegral_mono_ae
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
            exact Filter.Eventually.of_forall (fun t ht => h_ptwise t ht)
      _ = ENNReal.ofReal
            (∫ t in Set.Ioi tstar, 2 * (N : ℝ) * Real.exp (a * t) ∂volume) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              h_integrable (Filter.Eventually.of_forall h_pt_nn)).symm
      _ = ENNReal.ofReal (4 * (N : ℝ) * σ ^ 2 / ((1 + 2 * (N : ℝ)) * tstar)) := by
            rw [h_tail_value]
      _ ≤ ENNReal.ofReal tstar := ENNReal.ofReal_le_ofReal h_tail_bound
  -- Combine: tstar + tstar = 2 tstar ≤ 12 σ √log(1+N).
  refine le_trans (add_le_add h_first h_second) ?_
  rw [← ENNReal.ofReal_add hts_nn hts_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hts_def]
  -- log(1+2N) ≤ 2 log(1+N) for N ≥ 1 (since 1+2N ≤ (1+N)²).
  have h_log_split : Real.log (1 + 2 * (N : ℝ)) ≤ 2 * Real.log (1 + (N : ℝ)) := by
    have h_sq_ge : 1 + 2 * (N : ℝ) ≤ (1 + (N : ℝ)) ^ 2 := by nlinarith [hNr_pos.le]
    have h_log_sq : Real.log ((1 + (N : ℝ)) ^ 2) = 2 * Real.log (1 + (N : ℝ)) := by
      rw [sq, Real.log_mul h_1pN_pos.ne' h_1pN_pos.ne']; ring
    calc Real.log (1 + 2 * (N : ℝ))
        ≤ Real.log ((1 + (N : ℝ)) ^ 2) := Real.log_le_log h_1p2N_pos h_sq_ge
      _ = 2 * Real.log (1 + (N : ℝ)) := h_log_sq
  -- √(2 log(1+2N)) ≤ 2 √log(1+N).
  have h_sqrt_le :
      Real.sqrt (2 * Real.log (1 + 2 * (N : ℝ)))
        ≤ 2 * Real.sqrt (Real.log (1 + (N : ℝ))) := by
    have h_sqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)
    have h_rw : (2 : ℝ) * Real.sqrt (Real.log (1 + (N : ℝ)))
        = Real.sqrt (4 * Real.log (1 + (N : ℝ))) := by
      rw [← h_sqrt4, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    rw [h_rw]
    apply Real.sqrt_le_sqrt
    linarith
  have h_sqrtL_nn : (0 : ℝ) ≤ Real.sqrt (Real.log (1 + (N : ℝ))) :=
    Real.sqrt_nonneg _
  -- Conclude: 2 σ √(2 log(1+2N)) ≤ 2 σ · 2 √log(1+N) = 4 σ √log(1+N) ≤ 12 σ √log(1+N).
  nlinarith [h_sqrt_le, hσ_pos.le, h_sqrtL_nn]

/-- **Pisier ψ₂ maximal inequality** (sub-Gaussian envelope on L¹ of finite sup).

For a finite family `Z : ι → Ξ → ℝ` of real-valued measurable random
variables with a uniform sub-Gaussian-style tail bound
`μ{|Z_i| > t} ≤ 2 · exp(-t² / (2 · σ_eff²))` for every `t > 0`, the L¹-norm
of the supremum is controlled:

`∫⁻ ⨆_i |Z_i| dμ ≤ 12 · σ_eff · √log(1 + |ι|)`.

The signature requires `0 < σ_eff`; the `σ_eff = 0` corner is structurally
false here (vacuous tail hypothesis cannot force `Z ≡ 0`) and is handled
in `finite_sup_bound_orlicz_core` via the `M = σ = 0 ⇒ g ≡ 0`
case. The proof uses `psi2_layer_cake_meas_bound`
(measure-theory bridge) and `psi2_calculus_integral_bound` (real-analysis
integral).
-/
private lemma orlicz_psi2_max_l1_bound
    {ι : Type*} [Fintype ι] {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (_Z : ι → Ξ → ℝ) (_hZ_meas : ∀ i, Measurable (_Z i))
    {σ_eff : ℝ} (_hσ_eff : 0 < σ_eff)
    (_h_tail : ∀ i, ∀ t : ℝ, 0 < t →
        μ {ω | t < |_Z i ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * σ_eff ^ 2)))) :
    ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, |_Z i ω|) ∂μ
      ≤ ENNReal.ofReal
          (12 * σ_eff * Real.sqrt (Real.log (1 + Fintype.card ι))) := by
  refine le_trans
    (psi2_layer_cake_meas_bound _Z _hZ_meas _hσ_eff.le _h_tail) ?_
  exact psi2_calculus_integral_bound (Fintype.card ι) _hσ_eff

/-- **ψ₁ layer-cake bridge** — measure-theory side of the ψ₁ Pisier
maximal inequality used in `orlicz_psi1_max_l1_bound`.

Parallel to `psi2_layer_cake_meas_bound` with sub-exponential tail
`2 · exp(-t/ρ)` in place of sub-Gaussian `2 · exp(-t²/(2σ²))`.

Same pipeline as `psi2_layer_cake_meas_bound`: empty-ι trivial + nonempty
case via layer-cake + lintegral_mono_ae + set decomp + union bound + cap.
-/
private lemma psi1_layer_cake_meas_bound
    {ι : Type*} [Fintype ι] {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (_Z : ι → Ξ → ℝ) (_hZ_meas : ∀ i, Measurable (_Z i))
    {ρ_eff : ℝ} (_hρ_eff : 0 < ρ_eff)
    (_h_tail : ∀ i, ∀ t : ℝ, 0 < t →
        μ {ω | t < |_Z i ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-t / ρ_eff))) :
    ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, |_Z i ω|) ∂μ
      ≤ ∫⁻ t in Set.Ioi (0:ℝ),
          min 1 (ENNReal.ofReal ((Fintype.card ι : ℝ) *
            (2 * Real.exp (-t / ρ_eff)))) ∂volume := by
  -- Empty-ι edge case: ⨆ over empty = 0, so LHS lintegral = 0.
  by_cases hι : Nonempty ι
  swap
  · rw [not_nonempty_iff] at hι
    have h_sup_zero : ∀ ω : Ξ, (⨆ i : ι, |_Z i ω|) = 0 := fun ω =>
      Real.iSup_of_isEmpty _
    simp_rw [h_sup_zero, ENNReal.ofReal_zero, MeasureTheory.lintegral_zero]
    exact zero_le
  -- ===== Nonempty ι. =====
  -- Step 1: pointwise non-negativity of ⨆_i |Z_i ω|.
  have h_iSup_nn : ∀ ω, 0 ≤ ⨆ i : ι, |_Z i ω| := by
    intro ω
    obtain ⟨i₀⟩ := hι
    have h_bdd : BddAbove (Set.range fun i : ι => |_Z i ω|) :=
      Set.Finite.bddAbove (Set.finite_range _)
    exact le_trans (abs_nonneg _) (le_ciSup h_bdd i₀)
  -- Step 2: measurability of ω ↦ ⨆_i |Z_i ω| via Finset.sup'.
  have h_iSup_meas : Measurable (fun ω => ⨆ i : ι, |_Z i ω|) := by
    have h_fun_eq : (fun ω => ⨆ i : ι, |_Z i ω|)
        = Finset.univ.sup' Finset.univ_nonempty
            (fun i (ω : Ξ) => |_Z i ω|) := by
      funext ω
      rw [← Finset.sup'_univ_eq_ciSup]
      exact (Finset.sup'_apply Finset.univ_nonempty
        (fun i (ω : Ξ) => |_Z i ω|) ω).symm
    rw [h_fun_eq]
    exact Finset.measurable_sup' Finset.univ_nonempty
      (fun i _ => (_hZ_meas i).norm)
  -- Step 3: layer-cake formula.
  rw [lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall h_iSup_nn) h_iSup_meas.aemeasurable]
  -- Step 4: reduce to pointwise via lintegral_mono_ae.
  apply MeasureTheory.lintegral_mono_ae
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall ?_
  intro t ht
  rw [Set.mem_Ioi] at ht
  haveI : Nonempty ι := hι
  -- Set decomposition: {ω | t < ⨆_i |Z_i ω|} = ⋃ i, {ω | t < |Z_i ω|}.
  have h_set_eq : {ω | t < ⨆ i : ι, |_Z i ω|}
      = ⋃ i : ι, {ω | t < |_Z i ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hlt
      by_contra hne
      push Not at hne
      have h_sup_le : (⨆ i : ι, |_Z i ω|) ≤ t :=
        ciSup_le hne
      linarith
    · rintro ⟨i, hi⟩
      have h_bdd_ω : BddAbove (Set.range fun i : ι => |_Z i ω|) :=
        Set.Finite.bddAbove (Set.finite_range _)
      exact lt_of_lt_of_le hi (le_ciSup h_bdd_ω i)
  rw [h_set_eq]
  -- Cap by 1 + ofReal bound. Both bounds combine via `le_min`.
  refine le_min prob_le_one ?_
  -- Chain: μ (⋃) ≤ ∑ μ ≤ ∑ ofReal(2 exp(-t/ρ)) = ofReal(card · 2 · exp(-t/ρ)).
  have h_2exp_nn : 0 ≤ 2 * Real.exp (-t / ρ_eff) := by positivity
  calc μ (⋃ i : ι, {ω | t < |_Z i ω|})
      ≤ ∑ i : ι, μ {ω | t < |_Z i ω|} :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (2 * Real.exp (-t / ρ_eff)) :=
        Finset.sum_le_sum (fun i _ => _h_tail i t ht)
    _ = ENNReal.ofReal (∑ _i : ι, 2 * Real.exp (-t / ρ_eff)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => h_2exp_nn)]
    _ = ENNReal.ofReal
          ((Fintype.card ι : ℝ) * (2 * Real.exp (-t / ρ_eff))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **ψ₁ deterministic calculus integral** used in
`orlicz_psi1_max_l1_bound`.

Pure real-analysis (no probability content):
`∫⁻ t in Ioi 0, min 1 (ofReal((N:ℝ) · 2 · exp(-t/ρ))) dt
  ≤ ofReal(12 · ρ · log(1 + N))`.

Proof: split at the crossover threshold
`t* := ρ · log(1 + 2N)` (where the exponential bound first dips below 1).
* For `t ≤ t*`: integrand bounded by `1`, contributing `t* = ρ · log(1 + 2N)`.
* For `t > t*`: integrand = `(2N) · exp(-t/ρ)`, integrates to
  `ρ · (2N) · exp(-t*/ρ) = ρ · (2N)/(1 + 2N) ≤ ρ`.
* Sum: `ρ · log(1 + 2N) + ρ = ρ · (log(1 + 2N) + 1) ≤ 12 · ρ · log(1 + N)`
  (slack absorbs small-N edges).
* Edge cases `N = 0` and `ρ = 0` (in spirit; here `ρ > 0`) make LHS = 0.
-/
private lemma psi1_calculus_integral_bound
    (N : ℕ) {ρ : ℝ} (_hρ : 0 < ρ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        min 1 (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-t / ρ))))
        ∂volume
      ≤ ENNReal.ofReal (12 * ρ * Real.log (1 + N)) := by
  -- Edge case N = 0: integrand identically 0; LHS = 0; RHS = 0.
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h_integrand : ∀ t : ℝ,
        min (1 : ℝ≥0∞)
          (ENNReal.ofReal (((0 : ℕ) : ℝ) * (2 * Real.exp (-t / ρ))))
        = 0 := by
      intro t
      simp [ENNReal.ofReal_zero]
    simp_rw [h_integrand]
    rw [MeasureTheory.lintegral_zero]
    exact zero_le
  -- N ≥ 1 case: split Ioi 0 = Ioc 0 R ∪ Ioi R with R := ρ·log(1+2N).
  -- On (0, R]: integrand ≤ 1; contribution ≤ R.
  -- On (R, ∞): integrand ≤ 2Nr·exp(-t/ρ); tail integral ≤ ρ.
  -- Total ≤ R + ρ = ρ(log(1+2N) + 1) ≤ 12ρ·log(1+N) for N ≥ 1.
  have hNr_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNr_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h_1p2N_pos : (0 : ℝ) < 1 + 2 * (N : ℝ) := by linarith
  have h_1pN_pos : (0 : ℝ) < 1 + (N : ℝ) := by linarith
  have h_log_2N_pos : 0 < Real.log (1 + 2 * (N : ℝ)) :=
    Real.log_pos (by linarith)
  have h_log_N_pos : 0 < Real.log (1 + (N : ℝ)) :=
    Real.log_pos (by linarith)
  set R : ℝ := ρ * Real.log (1 + 2 * (N : ℝ)) with hR_def
  have hR_pos : 0 < R := mul_pos _hρ h_log_2N_pos
  have hR_nn : 0 ≤ R := hR_pos.le
  have hρ_ne : ρ ≠ 0 := ne_of_gt _hρ
  -- Step 1: Ioi 0 = Ioc 0 R ∪ Ioi R, disjoint.
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 R ∪ Set.Ioi R from
        (Set.Ioc_union_Ioi_eq_Ioi hR_nn).symm,
      MeasureTheory.lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
  -- Step 2: first piece — bound by 1, integrate to ofReal R.
  have h_first : ∫⁻ t in Set.Ioc 0 R,
        min (1 : ℝ≥0∞)
          (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-t / ρ)))) ∂volume
      ≤ ENNReal.ofReal R := by
    calc ∫⁻ t in Set.Ioc 0 R,
            min (1 : ℝ≥0∞)
              (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-t / ρ)))) ∂volume
        ≤ ∫⁻ _t in Set.Ioc 0 R, (1 : ℝ≥0∞) ∂volume := by
            apply MeasureTheory.lintegral_mono
            intro t; exact min_le_left _ _
      _ = volume (Set.Ioc (0:ℝ) R) := MeasureTheory.setLIntegral_one _
      _ = ENNReal.ofReal (R - 0) := Real.volume_Ioc
      _ = ENNReal.ofReal R := by rw [sub_zero]
  -- Step 3: second piece — bound integrand by ofReal(2N·exp(-t/ρ)).
  have h_a_neg : (-1 : ℝ) / ρ < 0 := by
    rw [neg_div]; exact neg_lt_zero.mpr (one_div_pos.mpr _hρ)
  have h_integrable :
      MeasureTheory.IntegrableOn
        (fun t => 2 * (N : ℝ) * Real.exp ((-1 / ρ) * t)) (Set.Ioi R) volume :=
    (integrableOn_exp_mul_Ioi h_a_neg R).const_mul (2 * (N : ℝ))
  have h_pt_nn : ∀ t : ℝ, 0 ≤ 2 * (N : ℝ) * Real.exp ((-1 / ρ) * t) := by
    intro t
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  -- Pointwise: min 1 X ≤ ofReal(2 N · exp((-1/ρ) t)).
  have h_ptwise : ∀ t : ℝ,
      min (1 : ℝ≥0∞)
          (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-t / ρ))))
        ≤ ENNReal.ofReal (2 * (N : ℝ) * Real.exp ((-1 / ρ) * t)) := by
    intro t
    refine le_trans (min_le_right _ _) ?_
    apply le_of_eq
    congr 1
    have h_arg : (-1 / ρ) * t = -t / ρ := by ring
    rw [h_arg]; ring
  -- Compute tail integral: ∫ in Ioi R, 2N · exp(a·t) = 2N · (-exp(aR)/a) with a = -1/ρ.
  have h_exp_R : Real.exp (-R / ρ) = (1 + 2 * (N : ℝ))⁻¹ := by
    have h_R_div : -R / ρ = -Real.log (1 + 2 * (N : ℝ)) := by
      rw [hR_def]; field_simp
    rw [h_R_div, Real.exp_neg, Real.exp_log h_1p2N_pos]
  have h_tail_integral :
      (∫ t in Set.Ioi R, 2 * (N : ℝ) * Real.exp ((-1 / ρ) * t) ∂volume)
        = 2 * (N : ℝ) * ρ * Real.exp (-R / ρ) := by
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi h_a_neg]
    rw [show (-1 / ρ) * R = -R / ρ from by ring]
    field_simp
  have h_second : ∫⁻ t in Set.Ioi R,
        min (1 : ℝ≥0∞)
          (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-t / ρ)))) ∂volume
      ≤ ENNReal.ofReal ρ := by
    calc ∫⁻ t in Set.Ioi R,
            min (1 : ℝ≥0∞)
              (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-t / ρ)))) ∂volume
        ≤ ∫⁻ t in Set.Ioi R,
            ENNReal.ofReal (2 * (N : ℝ) * Real.exp ((-1 / ρ) * t)) ∂volume :=
            MeasureTheory.lintegral_mono h_ptwise
      _ = ENNReal.ofReal
            (∫ t in Set.Ioi R, 2 * (N : ℝ) * Real.exp ((-1 / ρ) * t) ∂volume) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              h_integrable (Filter.Eventually.of_forall h_pt_nn)).symm
      _ = ENNReal.ofReal (2 * (N : ℝ) * ρ * Real.exp (-R / ρ)) := by
            rw [h_tail_integral]
      _ = ENNReal.ofReal (ρ * (2 * (N : ℝ) / (1 + 2 * (N : ℝ)))) := by
            rw [h_exp_R]
            congr 1
            rw [← div_eq_mul_inv]
            ring
      _ ≤ ENNReal.ofReal ρ := by
            apply ENNReal.ofReal_le_ofReal
            have h_frac_le : 2 * (N : ℝ) / (1 + 2 * (N : ℝ)) ≤ 1 := by
              rw [div_le_one h_1p2N_pos]; linarith
            nlinarith [_hρ.le, h_frac_le]
  -- Combine: LHS ≤ ofReal R + ofReal ρ = ofReal (R + ρ) ≤ ofReal (12 ρ log(1+N)).
  refine le_trans (add_le_add h_first h_second) ?_
  rw [← ENNReal.ofReal_add hR_nn _hρ.le]
  apply ENNReal.ofReal_le_ofReal
  -- R + ρ = ρ(log(1+2N) + 1) ≤ 12ρ·log(1+N).
  rw [hR_def]
  -- log(1+2N) ≤ log(2(1+N)) = log 2 + log(1+N).
  have h_log_split :
      Real.log (1 + 2 * (N : ℝ)) ≤ Real.log 2 + Real.log (1 + (N : ℝ)) := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
          (by linarith : (1 + (N : ℝ) : ℝ) ≠ 0)]
    exact Real.log_le_log h_1p2N_pos (by linarith)
  -- log 2 ≤ log(1 + N) since 2 ≤ 1 + N.
  have h_log2_le : Real.log 2 ≤ Real.log (1 + (N : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  -- 1/2 ≤ log 2 (uses Real.log_two_gt_d9 ≈ 0.6931).
  have h_log2_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h_1_le_2logN : (1 : ℝ) ≤ 2 * Real.log (1 + (N : ℝ)) := by
    have : (1:ℝ)/2 ≤ Real.log (1 + (N : ℝ)) := le_trans h_log2_ge_half h_log2_le
    linarith
  nlinarith [h_log_split, h_log2_le, h_1_le_2logN, h_log_N_pos.le, _hρ.le]

/-- **Pisier ψ₁ maximal inequality** (sub-exponential envelope on L¹ of finite sup).

For a finite family `Z : ι → Ξ → ℝ` of real-valued measurable random
variables with a uniform sub-exponential-style tail bound
`μ{|Z_i| > t} ≤ 2 · exp(-t / ρ_eff)` for every `t > 0`, the L¹-norm of
the supremum is controlled:

`∫⁻ ⨆_i |Z_i| dμ ≤ 12 · ρ_eff · log(1 + |ι|)`.

Chains through the two named lemmas `psi1_layer_cake_meas_bound`
(measure-theory bridge) and `psi1_calculus_integral_bound`
(real-analysis integral).
-/
private lemma orlicz_psi1_max_l1_bound
    {ι : Type*} [Fintype ι] {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (_Z : ι → Ξ → ℝ) (_hZ_meas : ∀ i, Measurable (_Z i))
    {ρ_eff : ℝ} (_hρ_eff : 0 < ρ_eff)
    (_h_tail : ∀ i, ∀ t : ℝ, 0 < t →
        μ {ω | t < |_Z i ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-t / ρ_eff))) :
    ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, |_Z i ω|) ∂μ
      ≤ ENNReal.ofReal (12 * ρ_eff * Real.log (1 + Fintype.card ι)) := by
  refine le_trans (psi1_layer_cake_meas_bound _Z _hZ_meas _hρ_eff _h_tail) ?_
  exact psi1_calculus_integral_bound (Fintype.card ι) _hρ_eff

/-! ### Bernstein-tail → L¹-sup envelope via Pisier ψ₁/ψ₂ truncation.

The proof is decomposed into two truncation-piece lemmas
(sub-Gaussian truncated piece via ψ₂, sub-exponential residual piece via
ψ₁), each derived from the corresponding Pisier estimate and a
Bernstein tail calculation. The theorem `orlicz_bernstein_max_l1_bound`
combines them by pointwise supremum decomposition and lintegral additivity.
-/

/-- **Truncated-piece L¹-sup envelope** (routes via Pisier ψ₂).

For a Bernstein-tail family `Z : ι → Ξ → ℝ` with `0 < M_eff`, truncating
each `|Z_i|` at the crossover threshold `T := σ_eff² / M_eff` produces a
family `A_i := min(|Z_i|, T)` whose Bernstein tail collapses to a clean
sub-Gaussian envelope: for `0 < t < T` we have `t · M_eff < T · M_eff = σ²`,
so `σ² + t M_eff < 2σ²` and the Bernstein tail
`2 exp(-t²/(4(σ²+t M_eff)))` is bounded by `2 exp(-t²/(8 σ²))` — sub-Gaussian
with effective scale `2σ_eff`.  For `t ≥ T`, `A_i ≤ T < t` makes the tail
trivial.

The Pisier ψ₂-max inequality (`orlicz_psi2_max_l1_bound`, applied with
`σ_eff' := 2 σ_eff`) then yields

`∫⁻ ⨆_i A_i dμ ≤ 12 · 2 σ_eff · √log(1+|ι|) = 24 · σ_eff · √log(1+|ι|)`.

Depends on `orlicz_psi2_max_l1_bound` (under `0 < σ_eff`).  The
`σ_eff = 0` corner is handled inline: at σ_eff = 0 the truncation
threshold `T := σ_eff² / M_eff = 0` makes the truncated piece
`min(|Z|, 0) = 0` pointwise, so LHS = 0 = RHS trivially.
Independent of `orlicz_bernstein_residual_max_l1_bound`. -/
private lemma orlicz_bernstein_truncated_max_l1_bound
    {ι : Type*} [Fintype ι] {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (_Z : ι → Ξ → ℝ) (_hZ_meas : ∀ i, Measurable (_Z i))
    {σ_eff M_eff : ℝ} (_hσ_eff : 0 ≤ σ_eff) (_hM_pos : 0 < M_eff)
    (_h_tail : ∀ i, ∀ t : ℝ, 0 < t →
        μ {ω | t < |_Z i ω|}
          ≤ ENNReal.ofReal
              (2 * Real.exp (-(t ^ 2) / (4 * (σ_eff ^ 2 + t * M_eff))))) :
    ∫⁻ ω, ENNReal.ofReal
        (⨆ i : ι, min (|_Z i ω|) (σ_eff ^ 2 / M_eff)) ∂μ
      ≤ ENNReal.ofReal
          (24 * σ_eff * Real.sqrt (Real.log (1 + Fintype.card ι))) := by
  -- σ_eff = 0 corner: T = 0 ⇒ min(|Z|, 0) = 0 ⇒ LHS = 0 = RHS.
  rcases eq_or_lt_of_le _hσ_eff with hσ_zero | hσ_pos
  · -- σ_eff = 0.
    have hT_zero : σ_eff ^ 2 / M_eff = 0 := by
      rw [← hσ_zero]; norm_num
    have h_min_zero : ∀ i ω, min (|_Z i ω|) (σ_eff ^ 2 / M_eff) = 0 := by
      intro i ω; rw [hT_zero]; exact min_eq_right (abs_nonneg _)
    have h_iSup_zero : ∀ ω, (⨆ i : ι, min (|_Z i ω|) (σ_eff ^ 2 / M_eff)) = 0 := by
      intro ω
      simp_rw [h_min_zero]
      by_cases hι : Nonempty ι
      · exact ciSup_const
      · rw [not_nonempty_iff] at hι; exact Real.iSup_of_isEmpty _
    simp_rw [h_iSup_zero, ENNReal.ofReal_zero, MeasureTheory.lintegral_zero]
    exact zero_le
  -- σ_eff > 0: existing textbook argument.
  set T : ℝ := σ_eff ^ 2 / M_eff with hT_def
  have hT_nn : 0 ≤ T := div_nonneg (sq_nonneg _) _hM_pos.le
  -- Sub-Gaussian tail for the truncated family `min(|Z|, T)`.
  have h_tail_Y : ∀ i, ∀ t : ℝ, 0 < t →
      μ {ω | t < |min (|_Z i ω|) T|}
        ≤ ENNReal.ofReal
            (2 * Real.exp (-(t ^ 2) / (2 * (2 * σ_eff) ^ 2))) := by
    intro i t ht
    have h_min_nn : ∀ ω, 0 ≤ min (|_Z i ω|) T :=
      fun ω => le_min (abs_nonneg _) hT_nn
    have h_set_abs_eq :
        {ω | t < |min (|_Z i ω|) T|} = {ω | t < min (|_Z i ω|) T} := by
      ext ω
      simp only [Set.mem_setOf_eq, abs_of_nonneg (h_min_nn ω)]
    rw [h_set_abs_eq]
    by_cases ht_T : t < T
    · -- {t < min(|Z i|, T)} = {t < |Z i|}
      have h_set_eq : {ω | t < min (|_Z i ω|) T} = {ω | t < |_Z i ω|} := by
        ext ω
        simp only [Set.mem_setOf_eq, lt_min_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, ht_T⟩⟩
      rw [h_set_eq]
      refine (_h_tail i t ht).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      -- t < T = σ²/M means tM < σ²
      have htM_lt : t * M_eff < σ_eff ^ 2 := by
        rw [hT_def] at ht_T
        rwa [lt_div_iff₀ _hM_pos] at ht_T
      -- Denominators: A := 4(σ² + tM) > 0; B := 2(2σ)² = 8σ² ≥ A.
      have htM_pos : 0 < t * M_eff := mul_pos ht _hM_pos
      have hA_pos : 0 < 4 * (σ_eff ^ 2 + t * M_eff) := by
        nlinarith [sq_nonneg σ_eff]
      have hA_le_B : 4 * (σ_eff ^ 2 + t * M_eff) ≤ 2 * (2 * σ_eff) ^ 2 := by
        nlinarith [sq_nonneg σ_eff, htM_lt]
      have ht2_nn : 0 ≤ t ^ 2 := sq_nonneg _
      -- t²/B ≤ t²/A (smaller denominator = larger quotient).
      have h_div : t ^ 2 / (2 * (2 * σ_eff) ^ 2)
                  ≤ t ^ 2 / (4 * (σ_eff ^ 2 + t * M_eff)) := by
        by_cases hσ_pos : 0 < σ_eff
        · have hB_pos : 0 < 2 * (2 * σ_eff) ^ 2 := by positivity
          exact div_le_div_of_nonneg_left ht2_nn hA_pos hA_le_B
        · -- σ = 0, so B = 0 and t²/B = 0; RHS ≥ 0.
          have hσ_le_zero : σ_eff ≤ 0 := not_lt.mp hσ_pos
          have hσ_zero : σ_eff = 0 := le_antisymm hσ_le_zero _hσ_eff
          have h_LHS_zero : t ^ 2 / (2 * (2 * σ_eff) ^ 2) = 0 := by
            rw [hσ_zero]; norm_num
          linarith [div_nonneg ht2_nn hA_pos.le, h_LHS_zero]
      -- Bridge `-(t²)/X` and `-(t²/X)` via `neg_div`.
      have h_neg1 : -(t ^ 2) / (4 * (σ_eff ^ 2 + t * M_eff))
                  = -(t ^ 2 / (4 * (σ_eff ^ 2 + t * M_eff))) := neg_div _ _
      have h_neg2 : -(t ^ 2) / (2 * (2 * σ_eff) ^ 2)
                  = -(t ^ 2 / (2 * (2 * σ_eff) ^ 2)) := neg_div _ _
      linarith [h_div, h_neg1, h_neg2]
    · -- t ≥ T, so {t < min(|Z i|, T)} = ∅ and tail = 0.
      have ht_T_ge : T ≤ t := not_lt.mp ht_T
      have h_empty : {ω | t < min (|_Z i ω|) T} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (min_le_right _ _).trans ht_T_ge
      rw [h_empty]; simp
  -- Apply Pisier ψ₂ with σ_eff' := 2 σ_eff (positive since σ_eff > 0).
  have h_pisier := orlicz_psi2_max_l1_bound
    (_Z := fun i ω => min (|_Z i ω|) T)
    (fun i => ((_hZ_meas i).norm).min measurable_const)
    (σ_eff := 2 * σ_eff)
    (by linarith : (0 : ℝ) < 2 * σ_eff)
    h_tail_Y
  -- Rewrite |min(|Z i|, T)| to min(|Z i|, T) in the LHS of h_pisier.
  have h_iSup_abs_eq : ∀ ω,
      (⨆ i : ι, |min (|_Z i ω|) T|) = (⨆ i : ι, min (|_Z i ω|) T) := by
    intro ω
    apply iSup_congr
    intro i; exact abs_of_nonneg (le_min (abs_nonneg _) hT_nn)
  simp_rw [h_iSup_abs_eq] at h_pisier
  refine h_pisier.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have h_const : (12 : ℝ) * (2 * σ_eff) = 24 * σ_eff := by ring
  rw [h_const]

/-- **Residual-piece L¹-sup envelope** (routes via Pisier ψ₁).

For a Bernstein-tail family `Z : ι → Ξ → ℝ` with `0 < M_eff`, the residual
past the crossover threshold `T := σ_eff² / M_eff` is
`B_i := max(0, |Z_i| - T) = (|Z_i| - T)_+`.  For every `t > 0`,
`μ{B_i > t} = μ{|Z_i| > T+t}`, and the Bernstein tail at `T+t` simplifies
to a sub-exponential envelope:

  `exp(-(T+t)²/(4(σ²+(T+t)M))) ≤ exp(-t/(8 M_eff))`

The algebraic core (using `σ² = T·M`) reduces to `t(2T+t) ≤ 2(T+t)²`, i.e.,
`0 ≤ 2T² + 2Tt + t²` — a sum of nonnegative squares.

The Pisier ψ₁-max inequality (`orlicz_psi1_max_l1_bound`, applied with
`ρ_eff := 8 M_eff`) then yields

`∫⁻ ⨆_i B_i dμ ≤ 12 · 8 M_eff · log(1+|ι|) = 96 · M_eff · log(1+|ι|)`.

Depends on `orlicz_psi1_max_l1_bound`. Independent of
`orlicz_bernstein_truncated_max_l1_bound`. -/
private lemma orlicz_bernstein_residual_max_l1_bound
    {ι : Type*} [Fintype ι] {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (_Z : ι → Ξ → ℝ) (_hZ_meas : ∀ i, Measurable (_Z i))
    {σ_eff M_eff : ℝ} (_hσ_eff : 0 ≤ σ_eff) (_hM_pos : 0 < M_eff)
    (_h_tail : ∀ i, ∀ t : ℝ, 0 < t →
        μ {ω | t < |_Z i ω|}
          ≤ ENNReal.ofReal
              (2 * Real.exp (-(t ^ 2) / (4 * (σ_eff ^ 2 + t * M_eff))))) :
    ∫⁻ ω, ENNReal.ofReal
        (⨆ i : ι, max 0 (|_Z i ω| - σ_eff ^ 2 / M_eff)) ∂μ
      ≤ ENNReal.ofReal
          (96 * M_eff * Real.log (1 + Fintype.card ι)) := by
  set T : ℝ := σ_eff ^ 2 / M_eff with hT_def
  have hT_nn : 0 ≤ T := div_nonneg (sq_nonneg _) _hM_pos.le
  -- Key identity: σ² = T · M (since T = σ²/M and M > 0).
  have hσ_eq : σ_eff ^ 2 = T * M_eff := by
    rw [hT_def]; field_simp
  -- Sub-exponential tail for the residual family `max(0, |Z| - T)`.
  have h_tail_B : ∀ i, ∀ t : ℝ, 0 < t →
      μ {ω | t < |max 0 (|_Z i ω| - T)|}
        ≤ ENNReal.ofReal (2 * Real.exp (-t / (8 * M_eff))) := by
    intro i t ht
    have h_max_nn : ∀ ω, 0 ≤ max 0 (|_Z i ω| - T) := fun ω => le_max_left _ _
    have h_set_abs_eq :
        {ω | t < |max 0 (|_Z i ω| - T)|} = {ω | t < max 0 (|_Z i ω| - T)} := by
      ext ω
      simp only [Set.mem_setOf_eq, abs_of_nonneg (h_max_nn ω)]
    rw [h_set_abs_eq]
    -- {t < max 0 (|Z|-T)} = {T+t < |Z|} (since t > 0, the `t < 0` disjunct is vacuous).
    have h_set_eq :
        {ω | t < max 0 (|_Z i ω| - T)} = {ω | T + t < |_Z i ω|} := by
      ext ω
      simp only [Set.mem_setOf_eq, lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h; right; linarith
    rw [h_set_eq]
    -- Apply Bernstein at `T + t`.
    have hTt_pos : 0 < T + t := by linarith
    refine (_h_tail i (T + t) hTt_pos).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hA_pos : 0 < 4 * (σ_eff ^ 2 + (T + t) * M_eff) := by
      have h_Tt_M : 0 < (T + t) * M_eff := mul_pos hTt_pos _hM_pos
      nlinarith [sq_nonneg σ_eff]
    have h8M_pos : 0 < 8 * M_eff := by linarith
    -- Algebraic core: 4 M_eff t (2T + t) ≤ 8 M_eff (T+t)², i.e., t(2T+t) ≤ 2(T+t)².
    have h_key :
        t * (4 * (σ_eff ^ 2 + (T + t) * M_eff))
          ≤ (T + t) ^ 2 * (8 * M_eff) := by
      rw [hσ_eq]
      nlinarith [sq_nonneg T, sq_nonneg t, mul_nonneg hT_nn ht.le,
        _hM_pos, mul_pos ht _hM_pos]
    -- Convert h_key to a div inequality: t/(8M) ≤ (T+t)²/(4(σ²+(T+t)M)).
    have h_div_ineq :
        t / (8 * M_eff)
          ≤ (T + t) ^ 2 / (4 * (σ_eff ^ 2 + (T + t) * M_eff)) :=
      (div_le_div_iff₀ h8M_pos hA_pos).mpr h_key
    -- Negate via `neg_div` and conclude.
    have h_neg1 :
        -((T + t) ^ 2) / (4 * (σ_eff ^ 2 + (T + t) * M_eff))
          = -((T + t) ^ 2 / (4 * (σ_eff ^ 2 + (T + t) * M_eff))) := neg_div _ _
    have h_neg2 : -t / (8 * M_eff) = -(t / (8 * M_eff)) := neg_div _ _
    linarith [h_div_ineq, h_neg1, h_neg2]
  -- Apply Pisier ψ₁ with ρ_eff := 8 M_eff.
  have h_meas_B : ∀ i, Measurable (fun ω => max 0 (|_Z i ω| - T)) := by
    intro i
    exact measurable_const.max (((_hZ_meas i).norm).sub measurable_const)
  have h_pisier := orlicz_psi1_max_l1_bound
    (_Z := fun i ω => max 0 (|_Z i ω| - T))
    h_meas_B
    (ρ_eff := 8 * M_eff)
    (by linarith)
    h_tail_B
  -- Rewrite |max 0 (|Z|-T)| to max 0 (|Z|-T) inside the supremum.
  have h_iSup_abs_eq : ∀ ω,
      (⨆ i : ι, |max 0 (|_Z i ω| - T)|)
        = (⨆ i : ι, max 0 (|_Z i ω| - T)) := by
    intro ω
    apply iSup_congr
    intro i; exact abs_of_nonneg (le_max_left _ _)
  simp_rw [h_iSup_abs_eq] at h_pisier
  refine h_pisier.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have h_const : (12 : ℝ) * (8 * M_eff) = 96 * M_eff := by ring
  rw [h_const]

/-- **Bernstein-tail to L¹-sup envelope.**

For a finite family `Z : ι → Ξ → ℝ` of real-valued measurable random
variables satisfying the **mixed sub-Gaussian / sub-exponential tail**
of Bernstein-type
`μ{|Z_i| > t} ≤ 2 · exp(-t² / (4 · (σ_eff² + t · M_eff)))` for every
`t > 0`, the L¹-norm of the supremum is controlled:

`∫⁻ ⨆_i |Z_i| dμ ≤ 96 · (M_eff · log(1+|ι|) + σ_eff · √log(1+|ι|))`.

Uses the two truncation-piece lemmas
(`orlicz_bernstein_truncated_max_l1_bound` for the sub-Gaussian truncated
piece + `orlicz_bernstein_residual_max_l1_bound` for the sub-exponential
residual piece) when `0 < M_eff`; falls back to direct invocation of
`orlicz_psi2_max_l1_bound` with `σ_eff' := √2 · σ_eff` in the degenerate
`M_eff = 0` case (where the Bernstein tail is purely sub-Gaussian).

Requires `0 < σ_eff ∨ 0 < M_eff` (i.e. not both zero).  The
`σ_eff = M_eff = 0` corner is structurally false (tail hypothesis is
vacuous, conclusion `LHS ≤ 0` requires `Z ≡ 0` which cannot be derived at
this layer) and is handled in `finite_sup_bound_orlicz_core`
via the `M = σ = 0 ⇒ g ≡ 0 ⇒ Z ≡ 0` case.

The constant `96` absorbs the truncated `24σ √L` and residual `96 M L`
contributions into a single ceiling. The theorem `finite_sup_bound` states the
result with an existential constant `∃ K > 0, ...`. -/
private lemma orlicz_bernstein_max_l1_bound
    {ι : Type*} [Fintype ι] {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (Z : ι → Ξ → ℝ) (hZ_meas : ∀ i, Measurable (Z i))
    {σ_eff M_eff : ℝ} (hσ_eff : 0 ≤ σ_eff) (hM_eff : 0 ≤ M_eff)
    (hσM_pos : 0 < σ_eff ∨ 0 < M_eff)
    (h_tail : ∀ i, ∀ t : ℝ, 0 < t →
        μ {ω | t < |Z i ω|}
          ≤ ENNReal.ofReal
              (2 * Real.exp (-(t ^ 2) / (4 * (σ_eff ^ 2 + t * M_eff))))) :
    ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, |Z i ω|) ∂μ
      ≤ ENNReal.ofReal
          (96 * (M_eff * Real.log (1 + Fintype.card ι)
            + σ_eff * Real.sqrt (Real.log (1 + Fintype.card ι)))) := by
  -- Numerical setup.
  have h_log_nn : 0 ≤ Real.log (1 + Fintype.card ι) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ Fintype.card ι := by positivity
    linarith
  have h_sqrtL_nn : 0 ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) :=
    Real.sqrt_nonneg _
  -- ===== Edge case: Empty ι. =====
  by_cases hι : Nonempty ι
  swap
  · -- ⨆ over empty = 0 in ℝ; LHS lintegral = 0.
    rw [not_nonempty_iff] at hι
    have h_sup_zero : ∀ ω : Ξ, (⨆ i : ι, |Z i ω|) = 0 := fun ω =>
      Real.iSup_of_isEmpty _
    simp_rw [h_sup_zero, ENNReal.ofReal_zero, MeasureTheory.lintegral_zero]
    exact zero_le
  -- ===== Main case split: M_eff > 0 vs M_eff = 0. =====
  by_cases hM_pos : 0 < M_eff
  · -- M_eff > 0: truncation argument.
    set T : ℝ := σ_eff ^ 2 / M_eff with hT_def
    have hT_nn : 0 ≤ T := div_nonneg (sq_nonneg _) hM_pos.le
    -- Pointwise: |Z i ω| = min |Z i ω| T + max 0 (|Z i ω| - T).
    have h_decomp_ptwise : ∀ i ω,
        |Z i ω| = min (|Z i ω|) T + max 0 (|Z i ω| - T) := by
      intro i ω
      rcases le_or_gt (|Z i ω|) T with h | h
      · rw [min_eq_left h, max_eq_left (sub_nonpos_of_le h)]
        ring
      · rw [min_eq_right h.le, max_eq_right (sub_nonneg.mpr h.le)]
        ring
    -- BddAbove of finite ranges.
    have h_bddA : ∀ ω, BddAbove (Set.range fun i : ι => min (|Z i ω|) T) :=
      fun ω => Set.Finite.bddAbove (Set.finite_range _)
    have h_bddB : ∀ ω, BddAbove (Set.range fun i : ι => max 0 (|Z i ω| - T)) :=
      fun ω => Set.Finite.bddAbove (Set.finite_range _)
    -- Pointwise sup decomposition.
    have h_sup_le : ∀ ω,
        ⨆ i : ι, |Z i ω|
          ≤ (⨆ i : ι, min (|Z i ω|) T)
            + (⨆ i : ι, max 0 (|Z i ω| - T)) := by
      intro ω
      refine ciSup_le ?_
      intro i
      rw [h_decomp_ptwise i ω]
      exact add_le_add (le_ciSup (h_bddA ω) i) (le_ciSup (h_bddB ω) i)
    -- ENNReal version of the pointwise inequality.
    have h_ofReal_le : ∀ ω,
        ENNReal.ofReal (⨆ i : ι, |Z i ω|)
          ≤ ENNReal.ofReal (⨆ i : ι, min (|Z i ω|) T)
            + ENNReal.ofReal (⨆ i : ι, max 0 (|Z i ω| - T)) := by
      intro ω
      calc ENNReal.ofReal (⨆ i : ι, |Z i ω|)
          ≤ ENNReal.ofReal ((⨆ i : ι, min (|Z i ω|) T)
              + (⨆ i : ι, max 0 (|Z i ω| - T))) :=
            ENNReal.ofReal_le_ofReal (h_sup_le ω)
        _ ≤ ENNReal.ofReal (⨆ i : ι, min (|Z i ω|) T)
            + ENNReal.ofReal (⨆ i : ι, max 0 (|Z i ω| - T)) :=
            ENNReal.ofReal_add_le
    -- Measurability of the truncated-piece sup (for lintegral additivity).
    have h_min_meas : ∀ i, Measurable (fun ω => min (|Z i ω|) T) := by
      intro i; exact ((hZ_meas i).norm).min measurable_const
    have h_iSup_A_meas : Measurable (fun ω => ⨆ i : ι, min (|Z i ω|) T) := by
      have h_fun_eq : (fun ω => ⨆ i : ι, min (|Z i ω|) T)
          = Finset.univ.sup' Finset.univ_nonempty
              (fun i (ω : Ξ) => min (|Z i ω|) T) := by
        funext ω
        rw [← Finset.sup'_univ_eq_ciSup]
        exact (Finset.sup'_apply Finset.univ_nonempty
          (fun i (ω : Ξ) => min (|Z i ω|) T) ω).symm
      rw [h_fun_eq]
      exact Finset.measurable_sup' Finset.univ_nonempty
        (fun i _ => h_min_meas i)
    have h_ofReal_iSup_A_meas : Measurable
        (fun ω => ENNReal.ofReal (⨆ i : ι, min (|Z i ω|) T)) :=
      h_iSup_A_meas.ennreal_ofReal
    -- Integrate and split.
    have h_step1 : ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, |Z i ω|) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, min (|Z i ω|) T) ∂μ
          + ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, max 0 (|Z i ω| - T)) ∂μ := by
      calc ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, |Z i ω|) ∂μ
          ≤ ∫⁻ ω, (ENNReal.ofReal (⨆ i : ι, min (|Z i ω|) T)
              + ENNReal.ofReal (⨆ i : ι, max 0 (|Z i ω| - T))) ∂μ :=
            MeasureTheory.lintegral_mono h_ofReal_le
        _ = ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, min (|Z i ω|) T) ∂μ
            + ∫⁻ ω, ENNReal.ofReal (⨆ i : ι, max 0 (|Z i ω| - T)) ∂μ :=
            MeasureTheory.lintegral_add_left h_ofReal_iSup_A_meas _
    -- Apply the two truncation-piece lemmas.
    have hA_bound := orlicz_bernstein_truncated_max_l1_bound
        Z hZ_meas hσ_eff hM_pos h_tail
    have hB_bound := orlicz_bernstein_residual_max_l1_bound
        Z hZ_meas hσ_eff hM_pos h_tail
    refine le_trans h_step1 ?_
    refine le_trans (add_le_add hA_bound hB_bound) ?_
    -- ofReal(24 σ √L) + ofReal(96 M L) = ofReal(24 σ √L + 96 M L)
    --   ≤ ofReal(96 (M L + σ √L)).
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [hσ_eff, hM_eff, h_log_nn, h_sqrtL_nn]
  · -- M_eff = 0: pure sub-Gaussian; invoke `orlicz_psi2_max_l1_bound` directly.
    have hM_le_zero : M_eff ≤ 0 := not_lt.mp hM_pos
    have hM_zero : M_eff = 0 := le_antisymm hM_le_zero hM_eff
    -- Since M_eff = 0, the hypothesis `0 < σ_eff ∨ 0 < M_eff` forces
    -- `0 < σ_eff`.
    have hσ_pos : 0 < σ_eff := by
      rcases hσM_pos with h | h
      · exact h
      · linarith
    -- The Bernstein tail with `M_eff = 0` reduces to `2 exp(-t²/(4σ²))`, which
    -- matches the ψ₂ form `2 exp(-t²/(2 σ_eff'²))` with `σ_eff' = √2 σ_eff`.
    have h_tail_psi2 : ∀ i, ∀ t : ℝ, 0 < t →
        μ {ω | t < |Z i ω|}
          ≤ ENNReal.ofReal
              (2 * Real.exp (-(t ^ 2) / (2 * (Real.sqrt 2 * σ_eff) ^ 2))) := by
      intro i t ht
      have h0 := h_tail i t ht
      rw [hM_zero] at h0
      -- Rewrite `4 (σ² + t·0) = 2 (√2 σ)²` to match ψ₂'s form.
      have h_denom :
          4 * (σ_eff ^ 2 + t * 0) = 2 * (Real.sqrt 2 * σ_eff) ^ 2 := by
        have h_sq2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 :=
          Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
        rw [mul_pow, h_sq2]; ring
      rw [h_denom] at h0
      exact h0
    have hσ_eff' : 0 < Real.sqrt 2 * σ_eff :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)) hσ_pos
    have hpsi2 := orlicz_psi2_max_l1_bound
        (_Z := Z) hZ_meas (σ_eff := Real.sqrt 2 * σ_eff) hσ_eff' h_tail_psi2
    refine le_trans hpsi2 ?_
    rw [hM_zero]
    apply ENNReal.ofReal_le_ofReal
    -- 12 · (√2 · σ) · √L ≤ 96 · (0 · L + σ · √L) = 96 · σ · √L.
    have h_sqrt2_le : Real.sqrt 2 ≤ 8 := by
      have h1 : Real.sqrt 2 ≤ Real.sqrt 64 :=
        Real.sqrt_le_sqrt (by norm_num)
      have h2 : Real.sqrt (64 : ℝ) = 8 := by
        rw [show (64 : ℝ) = 8 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 8)]
      linarith
    have h_sqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have h_prod_nn : 0 ≤ σ_eff * Real.sqrt (Real.log (1 + Fintype.card ι)) :=
      mul_nonneg hσ_eff h_sqrtL_nn
    calc 12 * (Real.sqrt 2 * σ_eff)
            * Real.sqrt (Real.log (1 + Fintype.card ι))
        = (12 * Real.sqrt 2)
            * (σ_eff * Real.sqrt (Real.log (1 + Fintype.card ι))) := by ring
      _ ≤ 96 * (σ_eff * Real.sqrt (Real.log (1 + Fintype.card ι))) := by
            apply mul_le_mul_of_nonneg_right _ h_prod_nn
            nlinarith [h_sqrt2_le, h_sqrt2_nn]
      _ = 96 * (0 * Real.log (1 + Fintype.card ι)
            + σ_eff * Real.sqrt (Real.log (1 + Fintype.card ι))) := by ring

/-! ### Main Orlicz-route closure of `finite_sup_bound`. -/

/-- **Orlicz-route core.** The full
mathematical content of vdV §19.6 Lem 19.33 — the truncation-plus-Jensen
argument that turns Bernstein's inequality (Lemma 19.32)
into the finite-class supremum bound.

**Proof outline (vdV §19.6):**

1. **Truncation.** For each `f_i = g_i`, split via `1{|G_n f_i| > b}` for
   threshold `b = M log(1+|ι|)/√n`:
   * `A_i = G_n f_i · 1{|G_n f_i| ≤ b}` (sub-Gaussian piece, ψ₂-tail)
   * `B_i = G_n f_i · 1{|G_n f_i| > b}` (sub-exponential piece, ψ₁-tail)
2. **Sub-Gaussian Orlicz norm of A_i.** From Bernstein for the bounded
   piece: `μ{|A_i| > x} ≤ 2 exp(−x²/(8σ²))` for `x ≤ b`, giving
   `‖A_i‖_{ψ₂} ≤ C₁ σ`.
3. **Sub-exponential Orlicz norm of B_i.** From Bernstein for the
   unbounded piece: `μ{|B_i| > x} ≤ 2 exp(−x √n /(8M))`, giving
   `‖B_i‖_{ψ₁} ≤ C₂ M / √n`.
4. **Max via Jensen.** `∫ ⨆_i |A_i| dμ ≤ ψ₂⁻¹(|ι|) · max_i ‖A_i‖_{ψ₂}
   = √log(1+|ι|) · C₁ σ`. Analogously for `B_i` and `ψ₁`.
5. **Triangle.** `∫ ⨆_i |G_n f_i| dμ ≤ ∫ ⨆_i |A_i| dμ + ∫ ⨆_i |B_i| dμ`,
   yielding `K = 24 = max(8 C₁, 8 C₂)`.

The proof derives the Bernstein tail bound on each `G_n (g i)` via
`bernstein_inequality_aux`, then applies `orlicz_bernstein_max_l1_bound` to the
truncated ψ₁ and ψ₂ estimates. -/
private lemma finite_sup_bound_orlicz_core
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {ι : Type*} [Fintype ι] (g : ι → Ω → ℝ) (hg_meas : ∀ i, Measurable (g i))
    {M σ : ℝ} (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hg_bdd : ∀ i ω, |g i ω| ≤ M)
    (hg_var : ∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ σ ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ω, ENNReal.ofReal
        (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
      ≤ ENNReal.ofReal
          (96 * (M * Real.log (1 + Fintype.card ι) / Real.sqrt n
            + σ * Real.sqrt (Real.log (1 + Fintype.card ι)))) := by
  -- Set up `Z i ω := G_n (g i) ω`.
  set Z : ι → Ξ → ℝ := fun i ω =>
    empiricalProcess P n (fun j : Fin n => X j.val ω) (g i) with hZ_def
  -- Measurability of each `Z i` in ω.
  have hZ_meas : ∀ i, Measurable (Z i) := by
    intro i
    -- `empiricalProcess P n X' (g i) = √n * (n⁻¹ * Σ_j g i (X' j) - ∫ g i dP)`.
    -- For `X' j = X j.val ω`, this is measurable in ω.
    simp only [hZ_def, empiricalProcess, empiricalAvg]
    refine Measurable.const_mul ?_ _
    refine Measurable.sub ?_ measurable_const
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ ?_
    intro j _
    exact (hg_meas i).comp (hX_meas j.val)
  -- Numerical preliminaries.
  have hn_pos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hsqrtn_pos : 0 < Real.sqrt n := by
    apply Real.sqrt_pos.mpr; exact_mod_cast hn_pos
  have hM_over_sqrtn_nn : 0 ≤ M / Real.sqrt n := div_nonneg hM hsqrtn_pos.le
  -- Outermost dispatch: M = σ = 0 ⇒ g ≡ 0 ⇒ Z ≡ 0 ⇒ trivial.
  by_cases h_degen : M = 0 ∧ σ = 0
  · obtain ⟨hM_zero, hσ_zero⟩ := h_degen
    -- g_i ≡ 0 (from |g i ω| ≤ M = 0).
    have hg_zero : ∀ i ω, g i ω = 0 := by
      intro i ω
      have := hg_bdd i ω
      rw [hM_zero] at this
      have h_abs : |g i ω| = 0 := le_antisymm this (abs_nonneg _)
      exact abs_eq_zero.mp h_abs
    -- empiricalProcess on the zero function ≡ 0.
    have hEP_zero : ∀ i (ω : Ξ),
        empiricalProcess P n (fun j : Fin n => X j.val ω) (g i) = 0 := by
      intro i ω
      simp only [empiricalProcess, empiricalAvg]
      have h_sum_zero : ∑ j : Fin n, g i (X j.val ω) = 0 := by
        apply Finset.sum_eq_zero
        intro j _; exact hg_zero i (X j.val ω)
      have h_int_zero : ∫ x, g i x ∂P = 0 := by
        simp_rw [hg_zero]; exact MeasureTheory.integral_zero _ _
      rw [h_sum_zero, h_int_zero]; ring
    -- Conclude LHS = 0.
    have h_integrand_zero : ∀ ω : Ξ, ENNReal.ofReal
        (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) = 0 := by
      intro ω
      have h_const : ∀ i : ι,
          |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)| = 0 := by
        intro i; rw [hEP_zero i ω, abs_zero]
      have h_sup : (⨆ i : ι,
          |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) = 0 := by
        simp_rw [h_const]
        by_cases hι : Nonempty ι
        · exact ciSup_const
        · rw [not_nonempty_iff] at hι; exact Real.iSup_of_isEmpty _
      rw [h_sup, ENNReal.ofReal_zero]
    simp_rw [h_integrand_zero]
    rw [MeasureTheory.lintegral_zero]
    exact zero_le
  -- Non-degenerate: at least one of σ > 0 or M > 0.
  have hσM_pos : 0 < σ ∨ 0 < M / Real.sqrt n := by
    push Not at h_degen
    rcases eq_or_lt_of_le hM with hM_eq | hM_pos
    · -- M = 0: then σ ≠ 0, so σ > 0 (since hσ : 0 ≤ σ).
      have hσ_ne : σ ≠ 0 := h_degen hM_eq.symm
      left; exact lt_of_le_of_ne hσ (Ne.symm hσ_ne)
    · -- M > 0: then M / √n > 0.
      right; exact div_pos hM_pos hsqrtn_pos
  -- Derive the Bernstein tail uniformly in i (in the form
  -- `_ ≤ 2 exp(-t²/(4 (σ² + t · (M / √n))))`).
  have h_tail : ∀ i, ∀ t : ℝ, 0 < t →
      μ {ω | t < |Z i ω|}
        ≤ ENNReal.ofReal
            (2 * Real.exp (-(t ^ 2) / (4 * (σ ^ 2 + t * (M / Real.sqrt n))))) := by
    intro i t ht
    -- Bernstein gives the bound with denominator
    -- `4 * (σ² + t * M / √n) = 4 * (σ² + t * (M / √n))` via `mul_div_assoc`.
    have hbern := bernstein_inequality_aux P (g i) (hg_meas i) hM hσ
      (hg_bdd i) (hg_var i) hX_meas hX_iindep hX_idem hX_law n hn ht
    -- Rewrite `t * M / √n` to `t * (M / √n)` inside the exponent.
    have heq : t * M / Real.sqrt n = t * (M / Real.sqrt n) := by
      rw [mul_div_assoc]
    -- Replace inside `hbern`.
    -- `hbern : μ {...} ≤ ofReal (2 * exp(-t² / (4 * (σ² + t * M / √n))))`.
    -- Goal:    `μ {...} ≤ ofReal (2 * exp(-t² / (4 * (σ² + t * (M / √n)))))`.
    rw [heq] at hbern
    exact hbern
  -- Apply the Bernstein maximal inequality.
  have h_assembly :=
    orlicz_bernstein_max_l1_bound (Z := Z) hZ_meas (σ_eff := σ)
      (M_eff := M / Real.sqrt n) hσ hM_over_sqrtn_nn hσM_pos h_tail
  -- Its conclusion has `96 * ((M / √n) * log + σ * √log)`; the goal
  -- has `96 * (M * log / √n + σ * √log)`.  Bridge by `mul_div_assoc`.
  refine le_trans h_assembly ?_
  apply le_of_eq
  congr 1
  field_simp

/-- **Explicit-constant form of vdV Lemma 19.33.**

The universal constant is `96`, as proved by
`finite_sup_bound_orlicz_core`. This finite-class inequality is used in the
chaining arguments of Lemmas 19.34 and 19.36.

Here `P` is the common law, `g` is the finite class, and `X` is an iid sample
realized on the probability space `(Ξ, μ)`. -/
lemma finite_sup_bound_96
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {ι : Type*} [Fintype ι] (g : ι → Ω → ℝ) (hg_meas : ∀ i, Measurable (g i))
    {M σ : ℝ} (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hg_bdd : ∀ i ω, |g i ω| ≤ M)
    (hg_var : ∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ σ ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ω, ENNReal.ofReal
        (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
      ≤ ENNReal.ofReal
          (96 * (M * Real.log (1 + Fintype.card ι) / Real.sqrt n
            + σ * Real.sqrt (Real.log (1 + Fintype.card ι)))) := by
  exact finite_sup_bound_orlicz_core P hX_meas hX_iindep hX_idem hX_law
    g hg_meas hM hσ hg_bdd hg_var n hn

/-- The finite-class Orlicz estimate in existential-constant form. It follows
from `finite_sup_bound_orlicz_core` with the universal constant `96`. -/
lemma finite_sup_bound_aux
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {ι : Type*} [Fintype ι] (g : ι → Ω → ℝ) (hg_meas : ∀ i, Measurable (g i))
    {M σ : ℝ} (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hg_bdd : ∀ i ω, |g i ω| ≤ M)
    (hg_var : ∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ σ ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧
      ∫⁻ ω, ENNReal.ofReal
          (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
        ≤ ENNReal.ofReal
            (K * (M * Real.log (1 + Fintype.card ι) / Real.sqrt n
              + σ * Real.sqrt (Real.log (1 + Fintype.card ι)))) := by
  refine ⟨96, by norm_num, ?_⟩
  exact finite_sup_bound_orlicz_core P hX_meas hX_iindep hX_idem hX_law
    g hg_meas hM hσ hg_bdd hg_var n hn

/-- **Uniform-constant form of `finite_sup_bound`** — the existential `∃ K` is
hoisted *before* the family / class / scale / `n` arguments, so a single universal
`K` works for all finite classes simultaneously.  This is the shape needed by the
chaining leaves, which must quantify their constant `c` before `∀ Φ ∀ δ ∀ n`.

The witness is the concrete numeral `96` exposed by `finite_sup_bound_orlicz_core`
(the Orlicz-route core proves the bound with the *literal* `96`, no existential),
so no information is lost relative to `finite_sup_bound`. -/
lemma finite_sup_bound_uniform
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type*} [Fintype ι] (g : ι → Ω → ℝ),
        (∀ i, Measurable (g i)) →
        ∀ {M σ : ℝ}, 0 ≤ M → 0 ≤ σ →
          (∀ i ω, |g i ω| ≤ M) →
          (∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ σ ^ 2) →
          ∀ (n : ℕ), 1 ≤ n →
            ∫⁻ ω, ENNReal.ofReal
                (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
              ≤ ENNReal.ofReal
                  (K * (M * Real.log (1 + Fintype.card ι) / Real.sqrt n
                    + σ * Real.sqrt (Real.log (1 + Fintype.card ι)))) := by
  refine ⟨96, by norm_num, ?_⟩
  intro ι _ g hg_meas M σ hM hσ hg_bdd hg_var n hn
  exact finite_sup_bound_orlicz_core P hX_meas hX_iindep hX_idem hX_law
    g hg_meas hM hσ hg_bdd hg_var n hn

end AsymptoticStatistics.EmpiricalProcess
