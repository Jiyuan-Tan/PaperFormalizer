module
public import StatLean.StatisticalModels.Coarsening.Basic
public import StatLean.AsymptoticStatistics.Operators.CAR

@[expose] public section

/-!
# The CAR bridge — MAR missingness is coarsening at random

**C6.** The model-level missingness mechanism of this slice satisfies the semiparametric
layer's coarsening-at-random predicate: for a MAR mechanism, the full-data law disintegrates
over the observed data through an explicit reconstruction kernel concentrated on the
coarsening fibres —
`IsMAR ρ → IsCoarseningAtRandom missingObserve (fullLaw Q ρ)`
(`AsymptoticStatistics.Operators.CAR.IsCoarseningAtRandom`, imported — never redefined).
This is the bridge that lets the missing-data *models* of this slice consume the
semiparametric observed-data theory (observed tangent spaces, information-loss operator,
influence-function lifts) of vdV §25.6.

**Scope honesty.** `IsCoarseningAtRandom` is a *single-measure* predicate, and on standard
Borel carriers a single-measure CAR disintegration exists for essentially any mechanism (see
the remark in `Operators/CAR.lean`) — so the Prop alone does not isolate MAR. Moreover the
kernel built here (`carKernel Q`) depends on the outcome law `Q` through `Q.condKernel`, so
it is *not* θ-free in a parametric reading. The value of this theorem is the explicit,
slice-wise reconstruction kernel — deterministic recovery on complete cases, a `Y ∣ X`
redraw on incomplete ones — whose correctness on the incomplete slice is exactly what MAR
buys. The substantive family-level bridge (one θ-free reconstruction kernel serving every
outcome law simultaneously, the form the semiparametric theory actually consumes) is a named
future debt (`D-C1`).

This file deliberately imports another area's concept layer (`Operators.CAR`) — the
sanctioned adapter exception, same pattern as `Adapters/`.

**Reference.** D. F. Heitjan and D. B. Rubin, "Ignorability and coarse data," *Ann.
Statist.* **19** (1991), 2244–2253 (`HR91`; CAR as the generalization of MAR); R. D. Gill,
M. J. van der Laan, and J. M. Robins, "Coarsening at random: characterizations, conjectures,
counter-examples," Springer LNS **123** (1997), 255–294 (the disintegration
characterization); vdV §25.6.

**Proof formalization notes.** The reconstruction kernel is glued by `Kernel.piecewise` on
the clopen observed event `{o | o.2.1 = true}`: on the complete-case slice the full datum is
recovered deterministically (`(x, r, ry) ↦ (x, ry, true)`); on the incomplete slice the
outcome is redrawn from the conditional law of `Y` given `X` under `Q` (`Q.condKernel`,
disintegrating over the standard Borel factor `ℝ`) — MAR is exactly what makes the
`Y ∣ X, R = 0` conditional equal the `Y ∣ X` conditional. The bind identity is verified
slice-by-slice against `Ignorability.observedLaw_restrict_true/false`; the fibre condition is
definitional on the deterministic slice and holds by construction on the other. Designated
XL theorem of the batch — the single allowed carry.

**Bibliographic comments.** That MAR is the single-outcome instance of CAR is `HR91`'s
founding observation; the kernel-disintegration formulation is Gill–van der Laan–Robins
(1997), which is also the form the `Operators.CAR` layer fixes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.StatisticalModels.Coarsening

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-! ### The reconstruction kernel and its two branches -/

/-- The observed complete-case event `{r = true}` is measurable. -/
private theorem measurableSet_obsTrue :
    MeasurableSet {o : 𝓧 × Bool × ℝ | o.2.1 = true} :=
  measurable_snd.fst (measurableSet_singleton true)

private theorem measurable_recTrue :
    Measurable fun o : 𝓧 × Bool × ℝ => (o.1, o.2.2, true) :=
  measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_const)

private theorem measurable_recFalse :
    Measurable fun p : 𝓧 × ℝ => (p.1, p.2, false) :=
  measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

/-- The reconstruction kernel of the CAR disintegration: on the complete-case slice the full
datum is recovered deterministically from the observed one; on the incomplete slice the masked
outcome is redrawn from the conditional law of `Y` given `X` under `Q`. -/
private noncomputable def carKernel (Q : Measure (𝓧 × ℝ)) [IsFiniteMeasure Q] :
    Kernel (𝓧 × Bool × ℝ) (𝓧 × ℝ × Bool) :=
  Kernel.piecewise measurableSet_obsTrue
    (Kernel.deterministic (fun o : 𝓧 × Bool × ℝ => (o.1, o.2.2, true)) measurable_recTrue)
    ((Kernel.deterministic (fun o : 𝓧 × Bool × ℝ => o.1) measurable_fst ⊗ₖ
        Q.condKernel.comap (fun p : (𝓧 × Bool × ℝ) × 𝓧 => p.2) measurable_snd).map
      (fun p : 𝓧 × ℝ => (p.1, p.2, false)))

private theorem carKernel_apply_true (Q : Measure (𝓧 × ℝ)) [IsFiniteMeasure Q]
    {o : 𝓧 × Bool × ℝ} (ho : o.2.1 = true) {A : Set (𝓧 × ℝ × Bool)} (hA : MeasurableSet A) :
    carKernel Q o A = A.indicator 1 (o.1, o.2.2, true) := by
  rw [carKernel, Kernel.piecewise_apply',
    if_pos (show o ∈ {o : 𝓧 × Bool × ℝ | o.2.1 = true} from ho),
    Kernel.deterministic_apply' _ _ hA]
  rfl

private theorem carKernel_apply_false (Q : Measure (𝓧 × ℝ)) [IsFiniteMeasure Q]
    {o : 𝓧 × Bool × ℝ} (ho : o.2.1 = false) {A : Set (𝓧 × ℝ × Bool)} (hA : MeasurableSet A) :
    carKernel Q o A = Q.condKernel o.1 {y | (o.1, y, false) ∈ A} := by
  have hne : o ∉ {o : 𝓧 × Bool × ℝ | o.2.1 = true} := by simp [Set.mem_setOf_eq, ho]
  rw [carKernel, Kernel.piecewise_apply', if_neg hne,
    Kernel.map_apply' _ measurable_recFalse _ hA,
    Kernel.compProd_apply (measurable_recFalse hA)]
  rw [Kernel.lintegral_deterministic']
  · rw [Kernel.comap_apply]
    rfl
  · exact Kernel.measurable_kernel_prodMk_left (measurable_recFalse hA)

/-! ### Bookkeeping bricks -/

/-- The full-data reassociation `((x, y), r) ↦ (x, y, r)` is measurable. -/
private theorem measurable_fullAssoc :
    Measurable fun p : (𝓧 × ℝ) × Bool => (p.1.1, p.1.2, p.2) :=
  measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)

/-- The composite `missingObserve ∘ reassociation`, read off the `compProd` carrier. -/
private theorem measurable_obsComp :
    Measurable fun p : (𝓧 × ℝ) × Bool => (p.1.1, p.2, if p.2 then p.1.2 else 0) :=
  measurable_missingObserve.comp measurable_fullAssoc

/-- `observedLaw` as a single pushforward of the `compProd` measure (map/map fusion). -/
private theorem observedLaw_eq_map (Q : Measure (𝓧 × ℝ)) (ρ : Kernel (𝓧 × ℝ) Bool) :
    observedLaw Q ρ = (Q ⊗ₘ ρ).map fun p => (p.1.1, p.2, if p.2 then p.1.2 else 0) := by
  rw [observedLaw, fullLaw, Measure.map_map measurable_missingObserve measurable_fullAssoc]
  rfl

/-- Two-point evaluation of a `Bool` measure on an arbitrary event. -/
private theorem bool_measure_split (ν : Measure Bool) (S : Set Bool) :
    ν S = S.indicator 1 true * ν {true} + S.indicator 1 false * ν {false} := by
  rw [← lintegral_indicator_one S.toFinite.measurableSet, lintegral_bool]

/-- **C6, the CAR bridge** (`HR91`; Gill–van der Laan–Robins 1997; vdV §25.6): a MAR
missingness mechanism makes the coarsening map `missingObserve` coarsening-at-random for the
full-data law — the model-level missing-data slice plugs into the semiparametric
observed-data theory. Single-measure instance witnessed by the explicit slice-wise kernel
`carKernel Q`; see the module docstring's scope-honesty note (family-level θ-free bridge =
debt `D-C1`). -/
theorem isCoarseningAtRandom_of_isMAR [MeasurableSingletonClass 𝓧]
    (Q : Measure (𝓧 × ℝ)) [IsProbabilityMeasure Q] {ρ : Kernel (𝓧 × ℝ) Bool}
    [IsMarkovKernel ρ]
    -- USER-INPUT: missing at random; Rubin76 §2, HR91
    (hMAR : IsMAR ρ) :
    AsymptoticStatistics.Operators.CAR.IsCoarseningAtRandom
      (missingObserve (𝓧 := 𝓧)) (fullLaw Q ρ) := by
  obtain ⟨ρ', hρ⟩ := hMAR
  refine ⟨carKernel Q, ?_, ?_⟩
  · -- the disintegration identity, verified slice by slice on the response indicator
    ext A hA
    have hκ : Measurable fun o : 𝓧 × Bool × ℝ => carKernel Q o A :=
      Kernel.measurable_coe _ hA
    have hInd : Measurable (A.indicator (1 : 𝓧 × ℝ × Bool → ℝ≥0∞)) :=
      measurable_one.indicator hA
    have hT : Measurable fun a : 𝓧 × ℝ => A.indicator 1 (a.1, a.2, true) * ρ a {true} :=
      (hInd.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))).mul
        (Kernel.measurable_coe ρ (measurableSet_singleton true))
    rw [Measure.bind_apply hA (Kernel.measurable _).aemeasurable]
    change _ = ∫⁻ o, carKernel Q o A ∂(observedLaw Q ρ)
    rw [observedLaw_eq_map, lintegral_map hκ measurable_obsComp,
      Measure.lintegral_compProd
        (f := fun p : (𝓧 × ℝ) × Bool => carKernel Q (p.1.1, p.2, if p.2 then p.1.2 else 0) A)
        (hκ.comp measurable_obsComp)]
    rw [fullLaw, Measure.map_apply measurable_fullAssoc hA,
      Measure.compProd_apply (measurable_fullAssoc hA)]
    -- both sides are two-point `Bool` integrals against `Q`; the complete-case terms agree
    have hL : ∫⁻ a : 𝓧 × ℝ, ρ a
          (Prod.mk a ⁻¹' ((fun p : (𝓧 × ℝ) × Bool => (p.1.1, p.1.2, p.2)) ⁻¹' A)) ∂Q
        = ∫⁻ a : 𝓧 × ℝ, (A.indicator 1 (a.1, a.2, true) * ρ a {true}
            + A.indicator 1 (a.1, a.2, false) * ρ a {false}) ∂Q :=
      lintegral_congr fun a => bool_measure_split _ _
    have hR : ∫⁻ a : 𝓧 × ℝ, ∫⁻ b : Bool,
          carKernel Q ((a, b).1.1, (a, b).2, if (a, b).2 then (a, b).1.2 else 0) A ∂ρ a ∂Q
        = ∫⁻ a : 𝓧 × ℝ, (A.indicator 1 (a.1, a.2, true) * ρ a {true}
            + Q.condKernel a.1 {y | (a.1, y, false) ∈ A} * ρ a {false}) ∂Q := by
      refine lintegral_congr fun a => ?_
      rw [lintegral_bool, carKernel_apply_true Q rfl hA, carKernel_apply_false Q rfl hA]
      rfl
    rw [hL, hR, lintegral_add_left hT, lintegral_add_left hT]
    congr 1
    -- the incomplete slice: MAR makes the weight a function of the covariate alone, so the
    -- redrawn outcome is governed by the conditional law of `Y` given `X`
    subst hρ
    have hfst : Q.fst = Q.map Prod.fst := rfl
    have hset : ∀ x : 𝓧, MeasurableSet {y : ℝ | (x, y, false) ∈ A} := fun x =>
      (measurable_const.prodMk (measurable_id.prodMk measurable_const)) hA
    have hH : Measurable fun x : 𝓧 =>
        Q.condKernel x {y | (x, y, false) ∈ A} * ρ' x {false} := by
      refine Measurable.mul ?_ (Kernel.measurable_coe _ (measurableSet_singleton false))
      exact Kernel.measurable_kernel_prodMk_left
        (measurable_fst.prodMk (measurable_snd.prodMk measurable_const) hA)
    have hG : Measurable fun p : 𝓧 × ℝ =>
        A.indicator (1 : 𝓧 × ℝ × Bool → ℝ≥0∞) (p.1, p.2, false) * ρ' p.1 {false} :=
      (hInd.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))).mul
        ((Kernel.measurable_coe ρ' (measurableSet_singleton false)).comp measurable_fst)
    simp only [Kernel.comap_apply]
    rw [show (∫⁻ a : 𝓧 × ℝ, Q.condKernel a.1 {y | (a.1, y, false) ∈ A} * ρ' a.1 {false} ∂Q)
        = ∫⁻ x : 𝓧, Q.condKernel x {y | (x, y, false) ∈ A} * ρ' x {false} ∂Q.fst from by
      rw [hfst, lintegral_map hH measurable_fst]]
    conv_lhs => rw [← Q.disintegrate Q.condKernel]
    rw [Measure.lintegral_compProd hG]
    refine lintegral_congr fun x => ?_
    have hf : Measurable fun b : ℝ => A.indicator (1 : 𝓧 × ℝ × Bool → ℝ≥0∞) (x, b, false) :=
      hInd.comp (by fun_prop)
    change ∫⁻ b : ℝ, A.indicator (1 : 𝓧 × ℝ × Bool → ℝ≥0∞) (x, b, false) * ρ' x {false}
        ∂Q.condKernel x = _
    rw [lintegral_mul_const _ hf]
    congr 1
    exact lintegral_indicator_one (hset x)
  · -- the fibre condition: the observed incomplete points carry the masked slot `0`
    have hMS : ∀ o : 𝓧 × Bool × ℝ,
        MeasurableSet {z : 𝓧 × ℝ × Bool | ¬ missingObserve z = o} :=
      fun o => (measurable_missingObserve (measurableSet_singleton o)).compl
    have hNmeas : MeasurableSet {o : 𝓧 × Bool × ℝ | o.2.1 = false ∧ o.2.2 ≠ 0} :=
      (measurable_snd.fst (measurableSet_singleton false)).inter
        (measurable_snd.snd (measurableSet_singleton (0 : ℝ))).compl
    have hN : observedLaw Q ρ {o : 𝓧 × Bool × ℝ | o.2.1 = false ∧ o.2.2 ≠ 0} = 0 := by
      rw [observedLaw_eq_map, Measure.map_apply measurable_obsComp hNmeas,
        show (fun p : (𝓧 × ℝ) × Bool => (p.1.1, p.2, if p.2 then p.1.2 else 0)) ⁻¹'
            {o : 𝓧 × Bool × ℝ | o.2.1 = false ∧ o.2.2 ≠ 0} = ∅ from by
          ext p; cases hp : p.2 <;> simp [hp], measure_empty]
    change ∀ᵐ o ∂(observedLaw Q ρ), _
    refine ae_iff.mpr (measure_mono_null (fun o ho => ?_) hN)
    obtain ⟨x, r, y⟩ := o
    simp only [Set.mem_setOf_eq] at ho ⊢
    by_contra hcon
    push Not at hcon
    refine ho ?_
    rw [ae_iff]
    cases r with
    | true =>
        rw [carKernel_apply_true Q rfl (hMS _)]
        simp [missingObserve]
    | false =>
        rw [carKernel_apply_false Q rfl (hMS _),
          show {b : ℝ | ((x, false, y).1, b, false) ∈
              {z : 𝓧 × ℝ × Bool | ¬ missingObserve z = (x, false, y)}} = ∅ from by
            ext b; simp [missingObserve, hcon rfl], measure_empty]

end StatLean.StatisticalModels.Coarsening
