module
public import StatLean.PointEstimation.Equivariance.Defs
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Location equivariance — constant risk and the structure of the equivariant class

The concrete location model on `Fin (m+1) → ℝ`: data `X` with joint density `f(x − ξ𝟙)`,
loss `ρ(d − ξ)`. This file establishes the two facts that reduce minimum risk equivariant
estimation to an ordinary minimization problem.

* **Constant risk** (`locRisk_const`): the risk of a location-equivariant estimator does
  not depend on `ξ`, so it equals its value `locRisk f ρ δ` at `ξ = 0`.
* **Structure of the equivariant class**: relative to any fixed equivariant `δ₀`,
  * `isLocEquivariant_iff_sub_invariant` — `δ` is equivariant iff `δ − δ₀` is
    translation-invariant;
  * `isLocInvariant_iff_factors_diffs` — a translation-invariant function is exactly a
    function of the differences `y = (x₁ − xₙ, …, x_{n−1} − xₙ)` (with a measurable
    factorization when the function is measurable);
  * `isLocEquivariant_iff_exists_diffs_rep` — combining the two, `δ` is equivariant iff
    `δ = δ₀ − v ∘ diffs` for some `v`.

The last item is what turns "minimize risk over the equivariant class" into "choose one
number `v(y)` per value of the maximal invariant", i.e. the conditional minimization
carried out in `LocationMRE`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.1 (First
Examples), Theorem 1.4 (equivariance forces constant bias, risk and variance), Lemmas 1.6 and
1.7, and Theorem 1.8 (the general equivariant estimator is `δ₀ − v` of the differences).
(`TPE2 §3.1 Thm 1.4, Lem 1.6–1.7, Thm 1.8`.)

**Proof formalization notes.**
* `diffs` is indexed so that `n = m + 1` observations produce `m` differences. The
  classical statement splits into `n ≥ 2` (function of the differences) and `n = 1`
  (constant); here `m = 0` makes `Fin 0 → ℝ` a subsingleton, so the single statement
  covers both cases with no case split.
* The measurable factorization uses the explicit section `y ↦ Fin.snoc y 0` of `diffs`
  (appending a zero last coordinate), which is measurable and satisfies
  `diffs (Fin.snoc y 0) = y`; this is why the measurable version needs no descriptive
  set theory.
* `locRisk_const` needs no regularity of the density beyond what `locationFamily`
  already encodes: it is a pure change of variables `x ↦ x + ξ𝟙` under `lintegral_map`,
  so only measurability of `ρ` and `δ` enters. This is a (weakening) deviation from the
  classical statement, which assumes a density throughout.
* Losses are real functions pushed through `ENNReal.ofReal` inside `∫⁻` (junk-value
  discipline inherited from `locRisk`).

**Bibliographic comments.** Equivariant estimation of a location parameter, together with
the reduction to the differences as maximal invariant, is due to E. J. G. Pitman, "The
estimation of the location and scale parameters of a continuous population of any given
form," *Biometrika* **30** (1939), 391–421. The general group-theoretic formulation of
which this is the leading special case is due to G. A. Hunt and C. Stein (unpublished
manuscript, 1946), first reported in print by M. A. Girshick and L. J. Savage, "Bayes and
minimax estimates for quadratic loss functions," *Proc. Second Berkeley Symp. Math.
Statist. Probab.*, Univ. California Press, 1951, 53–73.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section Location

variable {m n : ℕ}

/-! ### Elementary closure properties -/

/-- Translating the data by a constant shift leaves the differences unchanged. -/
private lemma diffs_add_smul_one (x : Fin (m + 1) → ℝ) (a : ℝ) :
    diffs (x + a • (1 : Fin (m + 1) → ℝ)) = diffs x := by
  funext i
  simp only [diffs, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  ring

/-- Every data point equals the section `Fin.snoc (diffs x) 0` shifted by its last
coordinate. This exhibits `x` and `Fin.snoc (diffs x) 0` as translates, which is the
engine of the factorization through the differences. -/
private lemma eq_snoc_diffs_add (x : Fin (m + 1) → ℝ) :
    x = Fin.snoc (diffs x) (0 : ℝ) + (x (Fin.last m)) • (1 : Fin (m + 1) → ℝ) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
        mul_one, zero_add]
  | cast i =>
      simp only [Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
        mul_one, diffs]
      ring

/-- Appending a zero last coordinate is a measurable map. -/
private lemma measurable_snoc_zero :
    Measurable (fun y : Fin m → ℝ => (Fin.snoc y (0 : ℝ) : Fin (m + 1) → ℝ)) := by
  apply measurable_pi_lambda
  intro j
  induction j using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact measurable_const
  | cast i => simp only [Fin.snoc_castSucc]; exact measurable_pi_apply i

/-- The difference statistic is measurable. -/
theorem measurable_diffs : Measurable (diffs : (Fin (m + 1) → ℝ) → Fin m → ℝ) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.castSucc).sub (measurable_pi_apply (Fin.last m))

/-- Appending a zero last coordinate is a section of `diffs`. -/
theorem diffs_snoc (y : Fin m → ℝ) : diffs (Fin.snoc y (0 : ℝ)) = y := by
  funext i
  simp only [diffs, Fin.snoc_castSucc, Fin.snoc_last, sub_zero]

/-- Subtracting a constant preserves location equivariance. Together with
`locRisk_const` this is the whole content of the risk-unbiasedness of a minimum risk
equivariant estimator. -/
theorem IsLocEquivariant.sub_const {δ : (Fin n → ℝ) → ℝ} (hδ : IsLocEquivariant δ)
    (a : ℝ) : IsLocEquivariant fun x => δ x - a := by
  intro b x
  show δ (x + b • (1 : Fin n → ℝ)) - a = (δ x - a) + b
  rw [hδ b x]; ring

/-- Subtracting a translation-invariant function from an equivariant estimator leaves it
equivariant. -/
theorem IsLocEquivariant.sub_invariant {δ : (Fin n → ℝ) → ℝ} {u : (Fin n → ℝ) → ℝ}
    (hδ : IsLocEquivariant δ) (hu : IsLocInvariant u) :
    IsLocEquivariant fun x => δ x - u x := by
  intro b x
  show δ (x + b • (1 : Fin n → ℝ)) - u (x + b • (1 : Fin n → ℝ)) = (δ x - u x) + b
  rw [hδ b x, hu b x]; ring

/-! ### Constant risk -/

/-- **The risk of a location-equivariant estimator does not depend on the parameter.**
For loss `ρ(d − ξ)` the risk at `ξ` equals the risk at `ξ = 0`, namely `locRisk f ρ δ`.

Consequently "uniformly minimize the risk over the equivariant class" is the ordinary
minimization of one number, which is the definition of a minimum risk equivariant
estimator. The classical statement asserts the same constancy for the bias and the
variance; those follow by the identical change of variables and are not needed
downstream. -/
theorem locRisk_const (f : (Fin n → ℝ) → ℝ) (ρ : ℝ → ℝ) (δ : (Fin n → ℝ) → ℝ)
    -- LEAN-ONLY: measurability of the loss; needed only to run `lintegral_map`
    (hρ : Measurable ρ)
    -- LEAN-ONLY: measurability of the estimator; same role, no scope change
    (hδ : Measurable δ)
    -- USER-INPUT: the estimator is location equivariant, `δ(x + a𝟙) = δ(x) + a`
    (hδeq : IsLocEquivariant δ)
    (ξ : ℝ) :
    ∫⁻ x, ENNReal.ofReal (ρ (δ x - ξ)) ∂(locationFamily f ξ) = locRisk f ρ δ := by
  unfold locationFamily locRisk
  have hmap_meas : Measurable (fun x : Fin n → ℝ => x + ξ • (1 : Fin n → ℝ)) := by fun_prop
  have hint_meas : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (ρ (δ x - ξ))) :=
    ENNReal.measurable_ofReal.comp (hρ.comp (hδ.sub_const ξ))
  rw [lintegral_map hint_meas hmap_meas]
  refine lintegral_congr fun x => ?_
  rw [hδeq ξ x, add_sub_cancel_right]

/-! ### Structure of the equivariant class -/

/-- **An estimator is equivariant iff it differs from a fixed equivariant estimator by a
translation-invariant function.** -/
theorem isLocEquivariant_iff_sub_invariant {δ₀ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: a reference equivariant estimator, the caller's free choice
    (h₀ : IsLocEquivariant δ₀)
    (δ : (Fin n → ℝ) → ℝ) :
    IsLocEquivariant δ ↔ IsLocInvariant fun x => δ x - δ₀ x := by
  constructor
  · intro hδ a x
    show δ (x + a • (1 : Fin n → ℝ)) - δ₀ (x + a • (1 : Fin n → ℝ)) = δ x - δ₀ x
    rw [hδ a x, h₀ a x]; ring
  · intro hu a x
    have hux := hu a x
    show δ (x + a • (1 : Fin n → ℝ)) = δ x + a
    simp only at hux
    rw [h₀ a x] at hux
    linarith

/-- **A function of the data is translation-invariant iff it factors through the
differences.** For `m = 0` (a single observation) the target `Fin 0 → ℝ` is a
subsingleton, so the statement specialises to "invariant iff constant". -/
theorem isLocInvariant_iff_factors_diffs (u : (Fin (m + 1) → ℝ) → ℝ) :
    IsLocInvariant u ↔ ∃ v : (Fin m → ℝ) → ℝ, ∀ x, u x = v (diffs x) := by
  constructor
  · intro hu
    refine ⟨fun y => u (Fin.snoc y 0), fun x => ?_⟩
    conv_lhs => rw [eq_snoc_diffs_add x]
    exact hu (x (Fin.last m)) (Fin.snoc (diffs x) 0)
  · rintro ⟨v, hv⟩ a x
    rw [hv, hv, diffs_add_smul_one]

/-- Measurable version of the factorization through the differences: a measurable
translation-invariant function factors through `diffs` **measurably**. This is the form
consumed by the conditional-minimization argument, where the factor is integrated
against a conditional distribution. -/
theorem isLocInvariant_iff_factors_diffs_measurable (u : (Fin (m + 1) → ℝ) → ℝ) :
    (Measurable u ∧ IsLocInvariant u) ↔
      ∃ v : (Fin m → ℝ) → ℝ, Measurable v ∧ ∀ x, u x = v (diffs x) := by
  constructor
  · rintro ⟨humeas, hu⟩
    refine ⟨fun y => u (Fin.snoc y 0), humeas.comp measurable_snoc_zero, fun x => ?_⟩
    conv_lhs => rw [eq_snoc_diffs_add x]
    exact hu (x (Fin.last m)) (Fin.snoc (diffs x) 0)
  · rintro ⟨v, hvmeas, hv⟩
    refine ⟨?_, fun a x => by rw [hv, hv, diffs_add_smul_one]⟩
    have hueq : u = fun x => v (diffs x) := funext hv
    rw [hueq]; exact hvmeas.comp measurable_diffs

/-- **Representation of the equivariant class.** Relative to a fixed equivariant `δ₀`,
the equivariant estimators are exactly `δ₀ − v ∘ diffs` as `v` ranges over all functions
of the differences. -/
theorem isLocEquivariant_iff_exists_diffs_rep {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: a reference equivariant estimator, the caller's free choice
    (h₀ : IsLocEquivariant δ₀)
    (δ : (Fin (m + 1) → ℝ) → ℝ) :
    IsLocEquivariant δ ↔ ∃ v : (Fin m → ℝ) → ℝ, ∀ x, δ x = δ₀ x - v (diffs x) := by
  rw [isLocEquivariant_iff_sub_invariant h₀, isLocInvariant_iff_factors_diffs]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun y => - v y, fun x => ?_⟩
    have hvx := hv x; dsimp only at hvx ⊢; linarith
  · rintro ⟨v, hv⟩
    refine ⟨fun y => - v y, fun x => ?_⟩
    have hvx := hv x; dsimp only at hvx ⊢; linarith

/-- Measurable version of the representation of the equivariant class: measurable
equivariant estimators correspond to measurable functions of the differences. -/
theorem isLocEquivariant_iff_exists_diffs_rep_measurable {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: a reference equivariant estimator, the caller's free choice
    (h₀ : IsLocEquivariant δ₀)
    -- LEAN-ONLY: measurability of the reference estimator; transfers measurability
    -- between `δ` and the factor `v`, no scope change
    (h₀meas : Measurable δ₀)
    (δ : (Fin (m + 1) → ℝ) → ℝ) :
    (Measurable δ ∧ IsLocEquivariant δ) ↔
      ∃ v : (Fin m → ℝ) → ℝ, Measurable v ∧ ∀ x, δ x = δ₀ x - v (diffs x) := by
  constructor
  · rintro ⟨hδm, hδeq⟩
    have hinv : IsLocInvariant (fun x => δ x - δ₀ x) :=
      (isLocEquivariant_iff_sub_invariant h₀ δ).mp hδeq
    obtain ⟨v, hvm, hv⟩ :=
      (isLocInvariant_iff_factors_diffs_measurable _).mp ⟨hδm.sub h₀meas, hinv⟩
    refine ⟨fun y => - v y, hvm.neg, fun x => ?_⟩
    have hvx := hv x; simp only [Pi.sub_apply] at hvx ⊢; linarith
  · rintro ⟨v, hvm, hv⟩
    have heq : IsLocEquivariant δ :=
      (isLocEquivariant_iff_exists_diffs_rep h₀ δ).mpr ⟨v, hv⟩
    have hueq : δ = fun x => δ₀ x - v (diffs x) := funext hv
    exact ⟨by rw [hueq]; exact h₀meas.sub (hvm.comp measurable_diffs), heq⟩

end Location

end StatLean.PointEstimation
