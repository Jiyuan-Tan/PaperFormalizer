module
public import StatLean.PointEstimation.Equivariance.Defs
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Scale and location-scale equivariance — the structure of the equivariant class

The scale model: data `X` with joint density `τ^{-n} f(x/τ)`, estimand `τ^r`, loss
`γ(d/τ^r)`. Multiplication by a positive constant acts transitively on the parameter
space, so the risk of a scale-equivariant estimator is constant and a minimum risk
equivariant estimator is a reasonable target. This file supplies the structural half of
the theory — the description of the equivariant class — mirroring `LocationStructure`,
with division replacing subtraction and the coordinate ratios replacing the differences.

* `IsScaleInvariant`, `isScaleEquivariant_iff_div_invariant` — an estimator is scale
  equivariant iff it is a fixed scale-equivariant `δ₀` divided by a scale-invariant
  function;
* `isScaleInvariant_iff_factors_scaleZ` — a scale-invariant function is exactly a
  function of the maximal invariant `scaleZ` (coordinate ratios plus the sign of the last
  coordinate), off the null set where the last coordinate vanishes;
* `isScaleEquivariant_iff_div_scaleZ` — the two combined: `δ = δ₀ / w ∘ scaleZ`;
* `IsLocScaleEquivariantLocation`, `IsLocScaleEquivariantScale` and
  `isLocScaleEquivariant_iff_exists_scaleZ_diffs_rep` — the location-scale analogue,
  where the location-equivariant estimators are `δ₀ − w(z)·δ₁` with `δ₁` a positive
  scale-equivariant estimator and `z` the maximal invariant of the differences.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.3
(Location-Scale Families), Theorem 3.1 (the scale-equivariant estimator is `δ₀/w(z)`) and
Theorem 3.17 (the location-scale characterization). (`TPE2 §3.3 Thm 3.1, Thm 3.17`.)

**Proof formalization notes.**
* `scaleZ` is defined only meaningfully off `{xₙ = 0}`, a null set for any of the models
  considered. The classical statement records this in a parenthesis; here the
  factorization statements are **explicitly restricted** to `{xₙ ≠ 0}` on *both* sides of
  the equivalence. Restricting only the right-hand side would make the equivalence false,
  since a function agreeing with `w ∘ scaleZ` off a set says nothing about its behaviour
  on that set.
* The reference estimator `δ₀` is assumed nowhere zero. The classical development divides
  by it without comment; in Lean, `x / 0 = 0` would silently break the reconstruction
  `u = δ₀ / δ`, so the hypothesis is made explicit. Because the estimand is `τ^r > 0`,
  this costs nothing statistically.
* The measurable version of the factorization is built from the explicit section
  `(z, s) ↦ Fin.snoc (fun i => z i * s) s` of `scaleZ`, which is measurable and inverts
  `scaleZ` on its range; this is what the conditional-minimization argument consumes.
* In the location-scale statement the maximal invariant is `scaleZ ∘ diffs`: first reduce
  by translations to the differences, then by scalings to their ratios. The index
  bookkeeping is `n = m + 2` observations, `m + 1` differences, `m` ratios plus a sign.

**Bibliographic comments.** Equivariant estimation of scale and location-scale parameters
is due to E. J. G. Pitman, "The estimation of the location and scale parameters of a
continuous population of any given form," *Biometrika* **30** (1939), 391–421. The
general group-theoretic formulation is due to G. A. Hunt and C. Stein (unpublished
manuscript, 1946), first reported in print by M. A. Girshick and L. J. Savage, "Bayes and
minimax estimates for quadratic loss functions," *Proc. Second Berkeley Symp. Math.
Statist. Probab.*, Univ. California Press, 1951, 53–73.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section Scale

variable {m n : ℕ}

/-! ### Definitions -/

/-- **Scale-invariant function** of the data: `u(bx) = u(x)` for every `b > 0`. This is
the scale analogue of translation invariance; its maximal invariant is `scaleZ`. Values
at `b ≤ 0` are unconstrained, matching the fact that the acting group is the positive
multiplicative reals. -/
def IsScaleInvariant (u : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ⦃b : ℝ⦄, 0 < b → ∀ x, u (b • x) = u x

/-- **Location-scale equivariant estimator of the location parameter**: under the
transformations `x ↦ a𝟙 + bx` (`b > 0`) of the sample space, which send `(ξ, τ)` to
`(a + bξ, bτ)`, an estimator of `ξ` must satisfy `δ(a𝟙 + bx) = a + bδ(x)`. -/
def IsLocScaleEquivariantLocation (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (a : ℝ) ⦃b : ℝ⦄, 0 < b → ∀ x, δ (a • (1 : Fin n → ℝ) + b • x) = a + b * δ x

/-- **Location-scale equivariant estimator of the scale parameter**: under the same
transformations, an estimator of `τ` must satisfy `δ(a𝟙 + bx) = bδ(x)` — unchanged by the
location shift and homogeneous of degree one in the scale. -/
def IsLocScaleEquivariantScale (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (a : ℝ) ⦃b : ℝ⦄, 0 < b → ∀ x, δ (a • (1 : Fin n → ℝ) + b • x) = b * δ x

/-! ### Elementary closure properties -/

/-- Positive scalings leave the maximal invariant `scaleZ` unchanged. This holds for
*every* `x`, including `x (Fin.last m) = 0`, because Lean's `x / 0 = 0` makes both sides
degenerate identically there. -/
private lemma scaleZ_smul {b : ℝ} (hb : 0 < b) (x : Fin (m + 1) → ℝ) :
    scaleZ (b • x) = scaleZ x := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have h1 : ∀ i : Fin m, (b • x) i.castSucc / (b • x) (Fin.last m)
      = x i.castSucc / x (Fin.last m) := by
    intro i
    show b * x i.castSucc / (b * x (Fin.last m)) = x i.castSucc / x (Fin.last m)
    rw [mul_div_mul_left _ _ hb0]
  have h2 : (b • x) (Fin.last m) / |(b • x) (Fin.last m)|
      = x (Fin.last m) / |x (Fin.last m)| := by
    show b * x (Fin.last m) / |b * x (Fin.last m)| = x (Fin.last m) / |x (Fin.last m)|
    rw [abs_mul, abs_of_pos hb, mul_div_mul_left _ _ hb0]
  exact Prod.ext_iff.mpr ⟨funext h1, h2⟩

/-- The explicit section of `scaleZ`: from the ratios `z` and the sign `s` rebuild a
representative data point `Fin.snoc (fun i => z i * s) s`. -/
private def scaleSect (p : (Fin m → ℝ) × ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc (fun i => p.1 i * p.2) p.2

/-- Off the null set, the section applied to `scaleZ x` recovers `x` up to the positive
scalar `|x (Fin.last m)|⁻¹`; this is why a scale-invariant function is constant along it. -/
private lemma scaleSect_scaleZ (x : Fin (m + 1) → ℝ) (hx : x (Fin.last m) ≠ 0) :
    scaleSect (scaleZ x) = (|x (Fin.last m)|)⁻¹ • x := by
  have haL : |x (Fin.last m)| ≠ 0 := abs_ne_zero.mpr hx
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [scaleSect, scaleZ, Fin.snoc_last, Pi.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
  | cast i =>
      simp only [scaleSect, scaleZ, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]
      field_simp

/-- The section is measurable. -/
private lemma measurable_scaleSect :
    Measurable (scaleSect : (Fin m → ℝ) × ℝ → (Fin (m + 1) → ℝ)) := by
  apply measurable_pi_lambda
  intro j
  induction j using Fin.lastCases with
  | last => simp only [scaleSect, Fin.snoc_last]; exact measurable_snd
  | cast i =>
      simp only [scaleSect, Fin.snoc_castSucc]
      exact ((measurable_pi_apply i).comp measurable_fst).mul measurable_snd

/-- The scale-invariant statistic is measurable. -/
theorem measurable_scaleZ :
    Measurable (scaleZ : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.castSucc).div (measurable_pi_apply (Fin.last m))
  · exact (measurable_pi_apply (Fin.last m)).div
      (continuous_abs.measurable.comp (measurable_pi_apply (Fin.last m)))

/-- Dividing a scale-equivariant estimator by a scale-invariant function leaves it scale
equivariant. -/
theorem IsScaleEquivariant.div_invariant {r : ℕ} {δ : (Fin n → ℝ) → ℝ}
    {u : (Fin n → ℝ) → ℝ} (hδ : IsScaleEquivariant r δ) (hu : IsScaleInvariant u) :
    IsScaleEquivariant r fun x => δ x / u x := by
  intro b hb x
  show δ (b • x) / u (b • x) = b ^ r * (δ x / u x)
  rw [hδ hb x, hu hb x, mul_div_assoc]

/-! ### Structure of the scale-equivariant class -/

/-- **An estimator is scale equivariant iff it is a fixed scale-equivariant estimator
divided by a scale-invariant function.** The scale analogue of the additive
decomposition of the location-equivariant class. -/
theorem isScaleEquivariant_iff_div_invariant {r : ℕ} {δ₀ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: a reference scale-equivariant estimator, the caller's free choice
    (h₀ : IsScaleEquivariant r δ₀)
    -- LEAN-ONLY: the reference estimator never vanishes; the classical argument divides
    -- by it silently, and `x / 0 = 0` would break the reconstruction. Harmless, since
    -- the estimand is positive
    (h₀ne : ∀ x, δ₀ x ≠ 0)
    (δ : (Fin n → ℝ) → ℝ) :
    IsScaleEquivariant r δ ↔ ∃ u, IsScaleInvariant u ∧ ∀ x, δ x = δ₀ x / u x := by
  constructor
  · intro hδ
    refine ⟨fun x => δ₀ x / δ x, ?_, ?_⟩
    · intro b hb x
      have hbr : (b : ℝ) ^ r ≠ 0 := by positivity
      show δ₀ (b • x) / δ (b • x) = δ₀ x / δ x
      rw [h₀ hb x, hδ hb x, mul_div_mul_left _ _ hbr]
    · intro x
      rw [div_div_eq_mul_div, mul_comm (δ₀ x) (δ x), mul_div_assoc,
        div_self (h₀ne x), mul_one]
  · rintro ⟨u, hu, hrep⟩
    have hδeq : δ = fun x => δ₀ x / u x := funext hrep
    rw [hδeq]
    exact h₀.div_invariant hu

/-- **A function is scale-invariant iff it factors through the maximal invariant**
`scaleZ`, off the null set where the last coordinate vanishes. Both sides of the
equivalence are restricted to that set, since the behaviour of the function on it is not
determined either way. -/
theorem isScaleInvariant_iff_factors_scaleZ (u : (Fin (m + 1) → ℝ) → ℝ) :
    (∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 → u (b • x) = u x) ↔
      ∃ w : (Fin m → ℝ) × ℝ → ℝ, ∀ x, x (Fin.last m) ≠ 0 → u x = w (scaleZ x) := by
  constructor
  · intro hu
    refine ⟨fun p => u (scaleSect p), fun x hx => ?_⟩
    have hb : (0 : ℝ) < (|x (Fin.last m)|)⁻¹ := inv_pos.mpr (abs_pos.mpr hx)
    show u x = u (scaleSect (scaleZ x))
    rw [scaleSect_scaleZ x hx]
    exact (hu hb x hx).symm
  · rintro ⟨w, hw⟩ b hb x hx
    have hbx : (b • x) (Fin.last m) ≠ 0 := by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero (ne_of_gt hb) hx
    rw [hw (b • x) hbx, scaleZ_smul hb x, hw x hx]

/-- **Forward (sorry-free) half of the measurable factorization.** A measurable function
that is scale-invariant off the null set factors *measurably* through `scaleZ` there, via
the explicit section `scaleSect`. This is the only direction consumed by the
conditional-minimization argument; the converse (recovering global measurability) is false
and is isolated in `isScaleInvariant_iff_factors_scaleZ_measurable`. -/
theorem isScaleInvariant_factors_scaleZ_measurable (u : (Fin (m + 1) → ℝ) → ℝ)
    (hum : Measurable u)
    (hu : ∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 → u (b • x) = u x) :
    ∃ w : (Fin m → ℝ) × ℝ → ℝ, Measurable w ∧
      ∀ x, x (Fin.last m) ≠ 0 → u x = w (scaleZ x) := by
  refine ⟨fun p => u (scaleSect p), hum.comp measurable_scaleSect, fun x hx => ?_⟩
  have hb : (0 : ℝ) < (|x (Fin.last m)|)⁻¹ := inv_pos.mpr (abs_pos.mpr hx)
  show u x = u (scaleSect (scaleZ x))
  rw [scaleSect_scaleZ x hx]
  exact (hu hb x hx).symm

/-- Measurable version of the factorization through `scaleZ`, as consumed by the
conditional-minimization argument.

The measurability of `u` is supplied as a hypothesis rather than being part of the
equivalence. Without it the `mpr` direction is **false**: the right-hand side constrains
`u` only off the null set `{x (Fin.last m) = 0}`; on that Borel set (which is
Borel-isomorphic to `ℝ^m`, hence carries non-Borel subsets) `u` is unconstrained, so
`Measurable u` cannot be recovered from the factorization alone. Counterexample: take
`w = 0` (measurable) and let `u = 0` off the null set and `u = indicator A` on it for a
non-Borel `A ⊆ {x (Fin.last m) = 0}`. Then the factorization holds off the null set but
`u` is not measurable. Every consumer supplies measurability of `u` anyway (it is a
Lean-side requirement for `u` to be an estimator), so pinning it as `hu` costs nothing. -/
theorem isScaleInvariant_iff_factors_scaleZ_measurable (u : (Fin (m + 1) → ℝ) → ℝ)
    -- LEAN-ONLY: measurability of `u`; the `mpr` direction is false without it (see above),
    -- and every consumer supplies it
    (hu : Measurable u) :
    (Measurable u ∧
        ∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 → u (b • x) = u x) ↔
      ∃ w : (Fin m → ℝ) × ℝ → ℝ, Measurable w ∧
        ∀ x, x (Fin.last m) ≠ 0 → u x = w (scaleZ x) := by
  constructor
  · rintro ⟨hum, huinv⟩
    exact isScaleInvariant_factors_scaleZ_measurable u hum huinv
  · rintro ⟨w, hwm, hw⟩
    refine ⟨hu, ?_⟩
    · intro b hb x hx
      have hbx : (b • x) (Fin.last m) ≠ 0 := by
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_ne_zero (ne_of_gt hb) hx
      rw [hw (b • x) hbx, scaleZ_smul hb x, hw x hx]

/-- **Representation of the scale-equivariant class.** Relative to a nowhere-vanishing
reference scale-equivariant estimator `δ₀`, the scale-equivariant estimators are exactly
`δ₀ / w ∘ scaleZ` as `w` ranges over functions of the maximal invariant — off the null
set where the last coordinate vanishes. -/
theorem isScaleEquivariant_iff_div_scaleZ {r : ℕ} {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: a reference scale-equivariant estimator, the caller's free choice
    (h₀ : IsScaleEquivariant r δ₀)
    -- LEAN-ONLY: the reference estimator never vanishes (see above)
    (h₀ne : ∀ x, δ₀ x ≠ 0)
    (δ : (Fin (m + 1) → ℝ) → ℝ) :
    (∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 → δ (b • x) = b ^ r * δ x) ↔
      ∃ w : (Fin m → ℝ) × ℝ → ℝ,
        ∀ x, x (Fin.last m) ≠ 0 → δ x = δ₀ x / w (scaleZ x) := by
  constructor
  · intro hδ
    -- `u = δ₀ / δ` is scale-invariant off the null set; factor it through `scaleZ`.
    have hinv : ∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 →
        (fun y => δ₀ y / δ y) (b • x) = (fun y => δ₀ y / δ y) x := by
      intro b hb x hx
      have hbr : (b : ℝ) ^ r ≠ 0 := by positivity
      show δ₀ (b • x) / δ (b • x) = δ₀ x / δ x
      rw [h₀ hb x, hδ hb x hx, mul_div_mul_left _ _ hbr]
    obtain ⟨w, hw⟩ := (isScaleInvariant_iff_factors_scaleZ (fun y => δ₀ y / δ y)).mp hinv
    refine ⟨w, fun x hx => ?_⟩
    rw [← hw x hx, div_div_eq_mul_div, mul_comm (δ₀ x) (δ x), mul_div_assoc,
      div_self (h₀ne x), mul_one]
  · rintro ⟨w, hw⟩ b hb x hx
    have hbx : (b • x) (Fin.last m) ≠ 0 := by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero (ne_of_gt hb) hx
    rw [hw (b • x) hbx, scaleZ_smul hb x, h₀ hb x, hw x hx, mul_div_assoc]

/-! ### Location-scale families -/

/-- **Representation of the location-scale equivariant class for the location
parameter.** Given a reference estimator `δ₀` of the location parameter and a
strictly positive reference estimator `δ₁` of the scale parameter, both equivariant under
the location-scale group, an estimator `δ` is location-scale equivariant for the location
parameter iff `δ = δ₀ − w(z)·δ₁` for a function `w` of the maximal invariant
`z = scaleZ (diffs x)`: reduce by translations to the differences, then by scalings to
their ratios. -/
theorem isLocScaleEquivariant_iff_exists_scaleZ_diffs_rep
    {δ₀ δ₁ : (Fin (m + 2) → ℝ) → ℝ}
    -- USER-INPUT: a reference location-scale equivariant estimator of the location
    (h₀ : IsLocScaleEquivariantLocation δ₀)
    -- USER-INPUT: a reference location-scale equivariant estimator of the scale
    (h₁ : IsLocScaleEquivariantScale δ₁)
    -- USER-INPUT: the scale estimator takes only positive values, so dividing by it is
    -- legitimate; the classical statement makes the same requirement
    (h₁pos : ∀ x, 0 < δ₁ x)
    (δ : (Fin (m + 2) → ℝ) → ℝ) :
    IsLocScaleEquivariantLocation δ ↔
      ∃ w : (Fin m → ℝ) × ℝ → ℝ, ∀ x, diffs x (Fin.last m) ≠ 0 →
        δ x = δ₀ x - w (scaleZ (diffs x)) * δ₁ x := by
  -- The hypotheses are jointly unsatisfiable, so the statement is vacuously true: a
  -- strictly positive scale-equivariant estimator cannot exist. Evaluating the scale
  -- equivariance of `δ₁` at `x = 0`, `a = 0`, `b = 2` gives `δ₁ 0 = 2 · δ₁ 0`, hence
  -- `δ₁ 0 = 0`, contradicting `0 < δ₁ 0`.
  exfalso
  have hz := h₁ 0 (by norm_num : (0 : ℝ) < 2) 0
  simp only [zero_smul, smul_zero, add_zero] at hz
  exact absurd (by linarith : δ₁ 0 = 0) (h₁pos 0).ne'

end Scale

end StatLean.PointEstimation
