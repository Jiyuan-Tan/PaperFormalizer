module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section

/-!
# Outer expectation `E*`

The **outer expectation** `E*[X]` of a (possibly non-measurable) function
`X : Ω → ℝ≥0∞` with respect to a measure `μ` is the infimum of `∫⁻ U ∂μ`
over all *measurable majorants* `U ≥ X`:
`E*[X] = ⨅ {U : Measurable, X ≤ U}, ∫⁻ U ∂μ`.

This is the outer-integral construction used to give meaning to weak
convergence of non-measurable maps (van der Vaart, *Asymptotic Statistics*
§18.1; Hoffmann-Jørgensen; van der Vaart–Wellner, *Weak Convergence and
Empirical Processes*, Ch. 1.2). It is the cornerstone primitive of the
abstract-Donsker / empirical-process framework, where the empirical process
need not be Borel measurable.

## Main definitions

* `MeasureTheory.outerExpectation μ X` — the outer expectation `E*[X]`.
* `MeasureTheory.Measure.outerMeasureStar μ A` — the outer measure
  `P*(A) = E*[1_A]`.

## Main results

* `outerExpectation_eq_lintegral` — for measurable `X`, `E*[X] = ∫⁻ X`.
* `outerExpectation_mono` — monotonicity in `X`.
* `outerExpectation_add_le` — countable subadditivity (the binary case):
  `E*[X + Y] ≤ E*[X] + E*[Y]`.

Additional results cover `const_smul`, `const`, `outerMeasureStar` and its
basic properties, and Markov's inequality.

## Implementation notes

The infimum is taken over the **subtype** `{U // Measurable U ∧ X ≤ U}`
rather than a bounded `⨅ U ∈ {…}`, keeping a single clean `iInf` so the
`ENNReal` infimum-manipulation lemmas (`ENNReal.iInf_add`, `le_iInf`,
`iInf_le`, …) apply directly. The
majorant subtype is always inhabited by the constant `⊤` function, recorded
as the `Nonempty` instance below.
-/

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Outer expectation `E*[X]` of a (possibly non-measurable) function
`X : Ω → ℝ≥0∞`: the infimum of `∫⁻ U ∂μ` over all measurable majorants
`U ≥ X` (van der Vaart §18.1; Hoffmann-Jørgensen / van der Vaart–Wellner
Ch. 1.2).

The index is the **subtype** `{U // Measurable U ∧ X ≤ U}` (inlined rather
than wrapped in a named type, so the `MeasurableSpace` instance and the
subtype coercion to `Ω → ℝ≥0∞` stay transparent to elaboration). This keeps a
single clean `iInf` so the `ENNReal` infimum-manipulation lemmas apply
directly.

Constitutive (vdV §18.1 p.258): the outer integral is *defined* as this
infimum over measurable majorants; the measurability and majorization
conditions on `U` are part of the definition. -/
noncomputable def outerExpectation (μ : Measure Ω) (X : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ U : {U : Ω → ℝ≥0∞ // Measurable U ∧ X ≤ U}, ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ

/-- The majorant subtype is always inhabited: the constant `⊤` function is a
measurable majorant of any `X`. (Recorded so the `iInf` is over a nonempty
index, which some `ENNReal` infimum lemmas require.) -/
instance (X : Ω → ℝ≥0∞) :
    Nonempty {U : Ω → ℝ≥0∞ // Measurable U ∧ X ≤ U} :=
  ⟨⟨fun _ => ⊤, measurable_const, le_top⟩⟩

/-! ### Fundamental lemmas -/

/-- For a measurable `X`, the outer expectation reduces to
the ordinary lower Lebesgue integral: `E*[X] = ∫⁻ X`. -/
theorem outerExpectation_eq_lintegral {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hX : Measurable X) : outerExpectation μ X = ∫⁻ ω, X ω ∂μ := by
  refine le_antisymm ?_ ?_
  · -- `X` is itself a measurable majorant of `X`, so the infimum is `≤ ∫⁻ X`.
    exact iInf_le (fun U : {U : Ω → ℝ≥0∞ // Measurable U ∧ X ≤ U} =>
      ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ) ⟨X, hX, le_rfl⟩
  · -- Every majorant `U ≥ X` has `∫⁻ X ≤ ∫⁻ U`.
    refine le_iInf fun U => ?_
    exact lintegral_mono U.2.2

/-- Outer expectation is monotone in the integrand. -/
theorem outerExpectation_mono {μ : Measure Ω} {X Y : Ω → ℝ≥0∞} (hXY : X ≤ Y) :
    outerExpectation μ X ≤ outerExpectation μ Y := by
  -- Every measurable majorant of `Y` is a measurable majorant of `X`
  -- (by `X ≤ Y ≤ U`), so the infimum over the larger constraint set on `Y`
  -- dominates the infimum over the smaller constraint set on `X`.
  refine le_iInf fun V => ?_
  exact iInf_le (fun U : {U : Ω → ℝ≥0∞ // Measurable U ∧ X ≤ U} =>
    ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ) ⟨(V : Ω → ℝ≥0∞), V.2.1, le_trans hXY V.2.2⟩

/-- Binary subadditivity of outer expectation:
`E*[X + Y] ≤ E*[X] + E*[Y]`.

Countable subadditivity of `E*` underlies the outer-integration framework, and
the binary case is the crux. The proof pulls the two infima out of the sum on the right via
`ENNReal.iInf_add` / `ENNReal.add_iInf`, then bounds `E*[X+Y]` by the sum
majorant `U + V` and uses additivity of the lower integral
(`lintegral_add_left`, available because the majorants carry measurability). -/
theorem outerExpectation_add_le {μ : Measure Ω} (X Y : Ω → ℝ≥0∞) :
    outerExpectation μ (X + Y) ≤ outerExpectation μ X + outerExpectation μ Y := by
  -- Unfold all three outer expectations, then pull both infima out of the
  -- sum on the right-hand side.
  simp only [outerExpectation]
  rw [ENNReal.iInf_add]
  refine le_iInf fun U => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun V => ?_
  -- `U + V` is a measurable majorant of `X + Y`.
  have hUVmeas : Measurable (fun ω => (U : Ω → ℝ≥0∞) ω + (V : Ω → ℝ≥0∞) ω) :=
    U.2.1.add V.2.1
  have hUVmaj : (X + Y) ≤ fun ω => (U : Ω → ℝ≥0∞) ω + (V : Ω → ℝ≥0∞) ω := by
    intro ω
    exact add_le_add (U.2.2 ω) (V.2.2 ω)
  -- Bound `E*[X+Y]` by the integral of this majorant, then split the integral.
  calc
    (⨅ W : {W : Ω → ℝ≥0∞ // Measurable W ∧ (X + Y) ≤ W},
          ∫⁻ ω, (W : Ω → ℝ≥0∞) ω ∂μ)
        ≤ ∫⁻ ω, ((U : Ω → ℝ≥0∞) ω + (V : Ω → ℝ≥0∞) ω) ∂μ :=
          iInf_le (fun W : {W : Ω → ℝ≥0∞ // Measurable W ∧ (X + Y) ≤ W} =>
            ∫⁻ ω, (W : Ω → ℝ≥0∞) ω ∂μ) ⟨_, hUVmeas, hUVmaj⟩
    _ = (∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ) + ∫⁻ ω, (V : Ω → ℝ≥0∞) ω ∂μ :=
          lintegral_add_left U.2.1 _

/-- Outer expectation respects `μ`-almost-everywhere equality of the integrand:
if `X =ᵐ[μ] Y` then `E*[X] = E*[Y]`.

Crucial for the weak-convergence application: the outer integrand is only ever
pinned down `μ`-a.e., so the readout must not see a null-set perturbation.

The proof is symmetric, so it suffices to show one inequality
`E*[Y] ≤ E*[X]` for any `X =ᵐ[μ] Y` (applied also with `X`, `Y` swapped). Take a
measurable majorant `U ≥ X`. Let `t` be a measurable null superset of the
disagreement set `{ω | X ω ≠ Y ω}` (`exists_measurable_superset_of_null`). Then
`U' := U + t.indicator (fun _ => ⊤)` is a measurable majorant of `Y` (off `t`,
`Y = X ≤ U`; on `t`, `U' = ⊤`), and `U' =ᵐ[μ] U` (they differ only on the null
set `t`), so `∫⁻ U' = ∫⁻ U` by `lintegral_congr_ae`. Hence
`E*[Y] ≤ ∫⁻ U' = ∫⁻ U`; take the infimum over `U`. -/
theorem outerExpectation_congr_ae {μ : Measure Ω} {X Y : Ω → ℝ≥0∞}
    (h : X =ᵐ[μ] Y) : outerExpectation μ X = outerExpectation μ Y := by
  -- One-directional helper: `E*[B] ≤ E*[A]` whenever `A =ᵐ[μ] B`.
  have key : ∀ A B : Ω → ℝ≥0∞, A =ᵐ[μ] B →
      outerExpectation μ B ≤ outerExpectation μ A := by
    intro A B hAB
    -- A measurable null superset `t` of the disagreement set.
    obtain ⟨t, hsub, ht_meas, ht_null⟩ :=
      exists_measurable_superset_of_null hAB
    -- Bound `E*[B]` by `∫⁻ U` for every measurable majorant `U` of `A`.
    refine le_iInf fun U => ?_
    -- The patched majorant `U' = U + t.indicator (fun _ => ⊤)`.
    set U' : Ω → ℝ≥0∞ := fun ω => (U : Ω → ℝ≥0∞) ω + t.indicator (fun _ => ⊤) ω
      with hU'def
    have hU'_meas : Measurable U' :=
      U.2.1.add (measurable_const.indicator ht_meas)
    -- `U'` majorizes `B` everywhere.
    have hU'_maj : B ≤ U' := by
      intro ω
      by_cases hω : ω ∈ t
      · -- On `t`, `U' ω = ⊤`.
        simp [hU'def, Set.indicator_of_mem hω]
      · -- Off `t`, `A ω = B ω ≤ U ω = U' ω` (off the disagreement set).
        have hAeqB : A ω = B ω := by
          by_contra hne
          exact hω (hsub hne)
        have hind : t.indicator (fun _ => (⊤ : ℝ≥0∞)) ω = 0 :=
          Set.indicator_of_notMem hω _
        simp only [hU'def, hind, add_zero]
        rw [← hAeqB]
        exact U.2.2 ω
    -- `U' =ᵐ[μ] U`: they differ only on the null set `t` (where `tᶜ` is co-null).
    have hU'_ae : U' =ᵐ[μ] (U : Ω → ℝ≥0∞) := by
      filter_upwards [compl_mem_ae_iff.2 ht_null] with ω hωt
      rw [Set.mem_compl_iff] at hωt
      simp [hU'def, hωt]
    -- `E*[B] ≤ ∫⁻ U' = ∫⁻ U`.
    calc outerExpectation μ B
        ≤ ∫⁻ ω, U' ω ∂μ :=
          iInf_le (fun W : {W : Ω → ℝ≥0∞ // Measurable W ∧ B ≤ W} =>
            ∫⁻ ω, (W : Ω → ℝ≥0∞) ω ∂μ) ⟨U', hU'_meas, hU'_maj⟩
      _ = ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ := lintegral_congr_ae hU'_ae
  exact le_antisymm (key Y X h.symm) (key X Y h)

/-! ### Scaling, constants, the induced outer measure, and Markov -/

/-- Outer expectation commutes with scaling by a finite constant.

Requires `c ≠ ⊤`: at `c = ⊤` the scaled function jumps to `⊤` off the support
of `X`, and `lintegral_const_mul` needs the finiteness side-condition. The `0`
case is handled by `c = 0` simp. The proof should send each majorant `U` of `X`
to the majorant `c • U` of `c • X` (and back, dividing by `c`), matching
`∫⁻ (c • U) = c • ∫⁻ U` via `lintegral_const_mul`. -/
theorem outerExpectation_const_smul {μ : Measure Ω} (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (X : Ω → ℝ≥0∞) :
    outerExpectation μ (c • X) = c • outerExpectation μ X := by
  -- `c • ·` on `ℝ≥0∞`-functions is pointwise multiplication.
  have hsmul : (c • X) = fun ω => c * X ω := by
    funext ω; simp [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, smul_eq_mul]
  -- Unfold both outer expectations, then pull `c` inside the RHS infimum.
  simp only [outerExpectation]
  rw [ENNReal.mul_iInf (fun h => absurd h hc)]
  -- `c * ∫⁻ V = ∫⁻ (c • V)` for each majorant `V` of `X`.
  refine le_antisymm ?_ ?_
  · -- `E*[c·X] ≤ ⨅_V (c * ∫⁻ V)`: each `c • V` is a measurable majorant of `c·X`.
    refine le_iInf fun V => ?_
    rw [← lintegral_const_mul c V.2.1]
    refine iInf_le (fun U : {U : Ω → ℝ≥0∞ // Measurable U ∧ (fun ω => c * X ω) ≤ U} =>
      ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ)
      ⟨fun ω => c * (V : Ω → ℝ≥0∞) ω, measurable_const.mul V.2.1, ?_⟩
    intro ω; dsimp only; gcongr; exact V.2.2 ω
  · -- `⨅_V (c * ∫⁻ V) ≤ E*[c·X]`: for `c ≠ 0`, divide each majorant `U` of `c·X` by `c`.
    rcases eq_or_ne c 0 with hc0 | hc0
    · simp [hc0]
    refine le_iInf fun U => ?_
    -- `c⁻¹ • U` is a measurable majorant of `X`.
    refine le_trans (iInf_le (fun V : {V : Ω → ℝ≥0∞ // Measurable V ∧ X ≤ V} =>
      c * ∫⁻ ω, (V : Ω → ℝ≥0∞) ω ∂μ)
      ⟨fun ω => c⁻¹ * (U : Ω → ℝ≥0∞) ω, measurable_const.mul U.2.1, ?_⟩) ?_
    · intro ω
      -- `X ω ≤ c⁻¹ * U ω` from `c * X ω ≤ U ω`.
      rw [← ENNReal.mul_le_iff_le_inv hc0 hc]
      exact U.2.2 ω
    · -- `c * ∫⁻ (c⁻¹ • U) = ∫⁻ U`.
      rw [← lintegral_const_mul c (measurable_const.fun_mul U.2.1)]
      refine lintegral_mono fun ω => ?_
      rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hc, one_mul]

/-- Outer expectation of a constant function: `E*[fun _ => c] = c * μ univ`. -/
theorem outerExpectation_const {μ : Measure Ω} (c : ℝ≥0∞) :
    outerExpectation μ (fun _ => c) = c * μ Set.univ := by
  rw [outerExpectation_eq_lintegral measurable_const, lintegral_const]

/-- The **outer measure** induced by `μ`: `P*(A) = E*[1_A]`, the outer
expectation of the indicator of `A`. -/
noncomputable def Measure.outerMeasureStar (μ : Measure Ω) (A : Set Ω) : ℝ≥0∞ :=
  outerExpectation μ (A.indicator 1)

/-- For a measurable set, the outer measure agrees with the measure. -/
theorem outerMeasureStar_eq_measure {μ : Measure Ω} {A : Set Ω}
    (hA : MeasurableSet A) : μ.outerMeasureStar A = μ A := by
  rw [Measure.outerMeasureStar,
    outerExpectation_eq_lintegral (measurable_one.indicator hA),
    lintegral_indicator hA]
  simp

/-- **Markov's inequality** for outer expectation: the outer measure of the
super-level set `{ω | t ≤ X ω}` is bounded by `E*[X] / t`.

Requires `t ≠ ⊤`: in the divided form the bound at `t = ⊤` would read
`P*({X = ⊤}) ≤ E*[X] / ⊤ = 0`, which is false whenever `X = ⊤` on a set of
positive outer measure (e.g. `X ≡ ⊤`). The undivided form `t · P*({t ≤ X}) ≤
E*[X]` does hold at `t = ⊤`, but the `div` rearrangement does not. -/
theorem outerExpectation_markov {μ : Measure Ω} {X : Ω → ℝ≥0∞} (t : ℝ≥0∞)
    (ht : t ≠ 0) (ht' : t ≠ ⊤) :
    μ.outerMeasureStar {ω | t ≤ X ω} ≤ outerExpectation μ X / t := by
  -- Pointwise: `t · 1_{t ≤ X} ≤ X`.
  have hpt : (t • ({ω | t ≤ X ω}).indicator (1 : Ω → ℝ≥0∞)) ≤ X := by
    intro ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Set.indicator_apply]
    split_ifs with hω
    · simpa using hω
    · simp
  -- `t · P*({t ≤ X}) = E*[t · 1_{t ≤ X}] ≤ E*[X]`, then divide by `t`.
  rw [ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl ht'), mul_comm,
    Measure.outerMeasureStar, ← smul_eq_mul, ← outerExpectation_const_smul t ht']
  exact outerExpectation_mono hpt

end MeasureTheory
