module
public import StatLean.Bayesian.DirichletLaplace.NormalMeansModel

@[expose] public section

/-!
# Converting a test into a posterior-mass bound (the testing lemma)

The Ghosal–Ghosh–van der Vaart step that turns a good frequentist test `A` (a "reject `θ ∈ C`"
region) into a bound on the truth-averaged posterior mass of `C`. Starting from the posterior ↔
ratio bridge (`NormalMeansModel.lintegral_posterior_eq_lintegral_ratio`), the truth-average of the
ratio `dlNumer θ₀ Π C / dlDenom θ₀ Π` is bounded in three moves:

1. `lintegral_ratio_split` — cut at the denominator event `{dlDenom < dbar}`. On the bad event the ratio
   is `≤ 1` (`dlRatio_le_one_ae`), contributing at most `P₀{dlDenom < dbar}` (this is discharged
   separately by the denominator lower bound, `C7`).
2. `lintegral_ratio_on_event_le_test` — the change-of-measure core: for a test `A` with uniform
   Type-II error `K θ Aᶜ ≤ b` on `θ ∈ C`, Fubini (`lintegral_dlNumer_eq_prior`-style) gives
   `∫_{Aᶜ} dlNumer θ₀ Π C dP₀ = ∫_C K θ Aᶜ dΠ ≤ Π C · b`.
3. `lintegral_ratio_on_event_le_test'` — assemble: on `{dlDenom ≥ dbar}` bound `ratio ≤ 1` on `A` and
   `ratio ≤ dlNumer/dbar` on `Aᶜ`, giving `≤ P₀ A + Π C · b / dbar`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, J. Amer. Statist. Assoc. 110 (2015), 1479–1490 (arXiv:1401.5398). §6 (the
testing/denominator decomposition). Underlying framework: Ghosal–Ghosh–van der Vaart, *Ann.
Statist.* 28 (2000), 500–531 (the test-based posterior-contraction lemma).

**Proof formalization notes.** `lintegral_ratio_split` splits the `lintegral` over the measurable
event `{y | dlDenom θ₀ Π y < dbar}` and bounds the restricted ratio by the measure of the event via
`dlRatio_le_one_ae`. `lintegral_ratio_on_event_le_test` is the pure change-of-measure step: it
rewrites `∫_{Aᶜ} dlNumer θ₀ Π C dP₀` by Tonelli into `∫_C (∫_{Aᶜ} dlLR dP₀) dΠ`, identifies the inner
integral as `K θ Aᶜ` (via `gaussShiftKernel_eq_withDensity` + `withDensity_apply`), and bounds it by
`b`. `lintegral_ratio_on_event_le_test'` combines the two: on `{dlDenom ≥ dbar}`, `dlNumer/dlDenom ≤`
`𝟙_A + (dlNumer/dbar)·𝟙_{Aᶜ}` pointwise (using `dlDenom ≥ dbar` and `ENNReal.div_le_div_left`), integrate,
then pull the constant `dbar⁻¹` out with `lintegral_mul_const`.
*Deviation D4:* the test `A` and its error bound `b` are supplied by the two-parameter midpoint tests
of `GaussianTests` (C8) with `b ≤ e^{−(d−ρ)²/8}`; this file is agnostic to their construction.

**Bibliographic comments.** Splitting off the small-denominator event and controlling the remainder
with a test is the measure-theoretic heart of Bayesian posterior-consistency theory; the "evidence
lower bound" `dbar = e^{−r²}·Π(B_r)` that instantiates `dbar` downstream is the Kullback–Leibler
prior-mass quantity of Ghosal–Ghosh–van der Vaart (2000) and Castillo–van der Vaart (*Ann. Statist.*
40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- The posterior ratio is `≤ 1` pointwise (`dlNumer ≤ dlDenom`). -/
private lemma dlRatio_le_one (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    (C : Set (EuclideanSpace ℝ ι)) (y : EuclideanSpace ℝ ι) :
    dlNumer θ₀ π C y / dlDenom θ₀ π y ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact dlNumer_le_dlDenom θ₀ π C y)

/-- **Change-of-measure with a test indicator** (BPPD §6, C6 Fubini): the truth-integral of the
un-normalized numerator on the acceptance region `Aᶜ` equals `∫_C K θ Aᶜ dΠ`. -/
private theorem dlNumer_setLIntegral_compl (θ₀ : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [SFinite π] {C A : Set (EuclideanSpace ℝ ι)}
    (hA : MeasurableSet A) :
    ∫⁻ y in Aᶜ, dlNumer θ₀ π C y ∂(gaussShiftKernel ι θ₀)
      = ∫⁻ θ in C, (gaussShiftKernel ι θ) Aᶜ ∂π := by
  simp only [dlNumer]
  rw [lintegral_lintegral_swap (f := fun (y θ : EuclideanSpace ℝ ι) => dlLR θ₀ θ y)
    ((measurable_dlLR_uncurry θ₀).comp measurable_swap).aemeasurable]
  have heq : (fun θ : EuclideanSpace ℝ ι =>
        ∫⁻ y in Aᶜ, dlLR θ₀ θ y ∂(gaussShiftKernel ι θ₀))
      = fun θ => (gaussShiftKernel ι θ) Aᶜ := by
    funext θ
    rw [gaussShiftKernel_eq_withDensity θ₀ θ, withDensity_apply _ hA.compl]
  rw [heq]

/-- **Denominator-event split.** The truth-averaged posterior ratio is bounded by the mass of the
small-denominator event `{dlDenom < dbar}` (where the ratio is `≤ 1`) plus the ratio integral on the
good event `{dlDenom ≥ dbar}`. -/
theorem lintegral_ratio_split (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    (C : Set (EuclideanSpace ℝ ι)) (dbar : ℝ≥0∞) :
    ∫⁻ y, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀)
      ≤ (gaussShiftKernel ι θ₀) {y | dlDenom θ₀ π y < dbar}
        + ∫⁻ y in {y | dbar ≤ dlDenom θ₀ π y},
            dlNumer θ₀ π C y / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀) := by
  set P₀ := gaussShiftKernel ι θ₀
  set S := {y : EuclideanSpace ℝ ι | dlDenom θ₀ π y < dbar} with hSdef
  have hScompl : Sᶜ = {y : EuclideanSpace ℝ ι | dbar ≤ dlDenom θ₀ π y} := by
    ext y; simp only [hSdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  -- `P₀ ≤ P₀.restrict S + P₀.restrict Sᶜ` by subadditivity (no measurability of `S` needed).
  have hStepA : P₀ ≤ P₀.restrict S + P₀.restrict Sᶜ := by
    rw [Measure.le_iff]
    intro t ht
    rw [Measure.add_apply, Measure.restrict_apply ht, Measure.restrict_apply ht]
    have h := measure_le_inter_add_diff P₀ t S
    rwa [Set.diff_eq] at h
  calc ∫⁻ y, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂P₀
      ≤ ∫⁻ y, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂(P₀.restrict S + P₀.restrict Sᶜ) :=
        lintegral_mono' hStepA (le_refl _)
    _ = ∫⁻ y in S, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂P₀
          + ∫⁻ y in Sᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂P₀ :=
        lintegral_add_measure _ _ _
    _ ≤ P₀ S + ∫⁻ y in Sᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂P₀ := by
        gcongr
        calc ∫⁻ y in S, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂P₀
            ≤ ∫⁻ _ in S, 1 ∂P₀ :=
              lintegral_mono fun y => dlRatio_le_one θ₀ π C y
          _ = P₀ S := setLIntegral_one S
    _ = P₀ S + ∫⁻ y in {y | dbar ≤ dlDenom θ₀ π y},
          dlNumer θ₀ π C y / dlDenom θ₀ π y ∂P₀ := by rw [hScompl]

/-- **Change-of-measure core of the testing lemma** (BPPD §6, via C6 Fubini): for a measurable test
region `A` whose Type-II error `K θ Aᶜ` is uniformly `≤ b` over `θ ∈ C`, the truth-integral of the
un-normalized numerator on the acceptance region `Aᶜ` is at most `Π C · b`. -/
theorem lintegral_ratio_on_event_le_test (θ₀ : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [SFinite π] {C A : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target and test regions measurable (regularity)
    (hC : MeasurableSet C) (hA : MeasurableSet A) {b : ℝ≥0∞}
    -- USER-INPUT: `A` has uniform Type-II error `≤ b` over `C`; the test property, BPPD §6 / C8
    (hb : ∀ θ ∈ C, gaussShiftKernel ι θ Aᶜ ≤ b) :
    ∫⁻ y in Aᶜ, dlNumer θ₀ π C y ∂(gaussShiftKernel ι θ₀) ≤ π C * b := by
  rw [dlNumer_setLIntegral_compl θ₀ π hA]
  calc ∫⁻ θ in C, (gaussShiftKernel ι θ) Aᶜ ∂π
      ≤ ∫⁻ _ in C, b ∂π := by
        refine lintegral_mono_ae ((ae_restrict_iff' hC).mpr (Filter.Eventually.of_forall ?_))
        intro θ hθ; exact hb θ hθ
    _ = π C * b := by rw [setLIntegral_const, mul_comm]

/-- **Testing lemma, on-event form** (BPPD §6): on the good denominator event `{dlDenom ≥ dbar}` the
truth-averaged posterior ratio of `C` is at most the Type-I error `P₀ A` of the test plus
`Π C · b / dbar`, where `b` bounds the Type-II error of the test over `C`. -/
theorem lintegral_ratio_on_event_le_test' (θ₀ : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [SFinite π] {C A : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target and test regions measurable (regularity)
    (hC : MeasurableSet C) (hA : MeasurableSet A) {dbar : ℝ≥0∞}
    -- USER-INPUT: positive evidence threshold dbar (instantiated as e^{−r²}·Π(B_r) downstream)
    (hdbar : dbar ≠ 0) {b : ℝ≥0∞}
    -- USER-INPUT: `A` has uniform Type-II error `≤ b` over `C`; the test property, BPPD §6 / C8
    (hb : ∀ θ ∈ C, gaussShiftKernel ι θ Aᶜ ≤ b) :
    ∫⁻ y in {y | dbar ≤ dlDenom θ₀ π y},
        dlNumer θ₀ π C y / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀)
      ≤ (gaussShiftKernel ι θ₀) A + π C * b / dbar := by
  set P₀ := gaussShiftKernel ι θ₀
  -- `dlDenom` is measurable (as the predictive density of `dlLR θ₀`), so the event is measurable.
  have hdenom_meas : Measurable (fun y => dlDenom θ₀ π y) := by
    have hEq : (fun y => dlDenom θ₀ π y) = predictiveDensity (dlLR θ₀) π := by
      funext y; rw [dlDenom, dlNumer, setLIntegral_univ]; rfl
    rw [hEq]; exact measurable_predictiveDensity (measurable_dlLR_uncurry θ₀)
  have hEmeas : MeasurableSet {y : EuclideanSpace ℝ ι | dbar ≤ dlDenom θ₀ π y} :=
    measurableSet_le measurable_const hdenom_meas
  -- On the good event `dbar ≤ dlDenom`, the ratio is dominated by `𝟙_A + (dlNumer/dbar)·𝟙_{Aᶜ}`.
  have hbound : ∀ y ∈ {y : EuclideanSpace ℝ ι | dbar ≤ dlDenom θ₀ π y},
      dlNumer θ₀ π C y / dlDenom θ₀ π y
        ≤ A.indicator (fun _ => (1 : ℝ≥0∞)) y
          + Aᶜ.indicator (fun y => dlNumer θ₀ π C y / dbar) y := by
    intro y hy
    by_cases hyA : y ∈ A
    · have hval : A.indicator (fun _ => (1 : ℝ≥0∞)) y
          + Aᶜ.indicator (fun y => dlNumer θ₀ π C y / dbar) y = 1 := by
        simp [Set.indicator_apply, Set.mem_compl_iff, hyA]
      rw [hval]; exact dlRatio_le_one θ₀ π C y
    · have hval : A.indicator (fun _ => (1 : ℝ≥0∞)) y
          + Aᶜ.indicator (fun y => dlNumer θ₀ π C y / dbar) y = dlNumer θ₀ π C y / dbar := by
        simp [Set.indicator_apply, Set.mem_compl_iff, hyA]
      rw [hval]; exact ENNReal.div_le_div (le_refl _) hy
  calc ∫⁻ y in {y | dbar ≤ dlDenom θ₀ π y}, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂P₀
      ≤ ∫⁻ y in {y | dbar ≤ dlDenom θ₀ π y},
          (A.indicator (fun _ => (1 : ℝ≥0∞)) y
            + Aᶜ.indicator (fun y => dlNumer θ₀ π C y / dbar) y) ∂P₀ :=
        lintegral_mono_ae ((ae_restrict_iff' hEmeas).mpr (Filter.Eventually.of_forall hbound))
    _ ≤ ∫⁻ y, (A.indicator (fun _ => (1 : ℝ≥0∞)) y
          + Aᶜ.indicator (fun y => dlNumer θ₀ π C y / dbar) y) ∂P₀ :=
        setLIntegral_le_lintegral _ _
    _ = P₀ A + (∫⁻ y in Aᶜ, dlNumer θ₀ π C y ∂P₀) / dbar := by
        rw [lintegral_add_left (measurable_const.indicator hA)]
        congr 1
        · exact lintegral_indicator_one hA
        · rw [lintegral_indicator hA.compl]
          simp_rw [div_eq_mul_inv]
          rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hdbar), ← div_eq_mul_inv]
    _ ≤ P₀ A + π C * b / dbar := by
        gcongr
        exact lintegral_ratio_on_event_le_test θ₀ π hC hA hb

end StatLean.Bayesian
