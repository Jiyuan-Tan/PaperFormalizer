module
public import StatLean.HypothesisTesting.MLR.Defs
public import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# Stochastic ordering and the monotone quantile coupling

Two laws on the real line are **stochastically ordered**, `F₁ ≤ F₀` pointwise, exactly when
they can be realized simultaneously on one probability space by two nondecreasing functions
of a single random variable, one everywhere below the other:
$$ F_1(x) \le F_0(x) \ \ \forall x \iff \exists\, f_0 \le f_1 \text{ nondecreasing, } V :
\ f_0(V) \sim F_0, \ \ f_1(V) \sim F_1 . $$
The realization is explicit: take `V` uniform on `(0,1)` and `f_i` the quantile function of
`F_i`, which is nondecreasing and satisfies `f_i(y) ≤ x ↔ y ≤ F_i(x)`; the ordering of the
distribution functions then transfers pointwise to the ordering of the quantiles.

Contents:
* `cdf_le_of_monotone_coupling` — a monotone coupling forces the ordering of the
  distribution functions (the easy direction);
* `exists_monotone_coupling_of_cdf_le` — the ordering produces a coupling, with `V`
  uniform on `(0,1)` (the substantive direction, stated constructively);
* `cdf_le_iff_exists_monotone_coupling` — the two combined.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.4 (Distributions with Monotone Likelihood Ratio), Lemma 3.4.1 (the
monotone quantile coupling for stochastically ordered families) and Lemma 3.4.2 (monotone
likelihood ratio makes `E_θ ψ` monotone for monotone `ψ`). (`TSH4 §3.4 Lem 3.4.1, Lem 3.4.2`.)

**Proof formalization notes.**
* Distribution functions are written as `fun x => (μ (Set.Iic x)).toReal` rather than
  through a separate cumulative-distribution-function object, so that the statement is
  about the measures themselves and no compatibility lemma is needed.
* The coupling is stated with the uniform law written as
  `volume.restrict (Set.Icc 0 1)`, which makes `exists_monotone_coupling_of_cdf_le`
  constructive: the existential is over the two monotone maps only, not over the
  probability space. The endpoints carry no Lebesgue mass, so this is the uniform law on
  `(0,1)` of the classical statement; the closed interval is chosen to match the
  inverse-transform brick below.
* Consequently the monotonicity in `exists_monotone_coupling_of_cdf_le` is `MonotoneOn …
  (Set.Ioo 0 1)`, and the domination `f₀ ≤ f₁` is asserted on `Set.Ioo 0 1` only: with the
  uniform law fixed to `[0,1]`, both global readings are false (explicit counterexamples in
  that theorem's docstring), and the restriction to `(0,1)` costs nothing since it carries
  full mass. `cdf_le_iff_exists_monotone_coupling`, which is free to choose the law of the
  coupling variable, does get the global `Monotone` form, by reading the quantiles through
  the increasing reparametrization `unitParam : ℝ → (0,1)`.
* The intended construction takes `f_i := quantile F_i` for the shared left-continuous
  `quantile F p = sInf {x | p ≤ F x}`. Its Galois-connection lemma `quantile_le_iff`
  (`quantile F p ≤ x ↔ p ≤ F x`) turns the pointwise inequality of the distribution
  functions directly into `f₀ ≤ f₁` and gives monotonicity via `quantile_mono`, while
  `map_quantile_uniform` identifies the two pushforward laws.
* Measurability of the two maps is not part of the conclusion: it follows from
  monotonicity (`Monotone.measurable`), so the pushforwards are automatically defined.

**Bibliographic comments.** The equivalence between stochastic ordering and the existence
of a monotone coupling is due to E. L. Lehmann ("Ordered families of distributions,"
*Ann. Math. Statist.* **26** (1955), 399–419); it is the one-dimensional case of the
coupling theorem of V. Strassen ("The existence of probability measures with given
marginals," *Ann. Math. Statist.* **36** (1965), 423–439). Its use for families with
monotone likelihood ratio is systematized in S. Karlin and H. Rubin ("The theory of
decision procedures for distributions with monotone likelihood ratio," *Ann. Math.
Statist.* **27** (1956), 272–299).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.HypothesisTesting

/-! ### The arctangent reparametrization of the unit interval

The classical coupling uses the quantile functions on `(0,1)`, which are monotone only
*there*: the junk values `quantile F p = 0` for `p ∉ (0,1)` destroy global monotonicity, and
no globally monotone map can push a compactly supported law onto a full-support one (see
`exists_monotone_coupling_of_cdf_le`). Precomposing with an increasing homeomorphism
`unitParam : ℝ ≃ (0,1)` repairs this: `quantile F ∘ unitParam` is monotone on all of `ℝ`,
and the coupling variable becomes `unitParamInv`-pushed uniform noise instead of uniform
noise itself. -/

/-- The increasing parametrization `ℝ → (0,1)`, `v ↦ arctan v / π + 1/2`. -/
private noncomputable def unitParam (v : ℝ) : ℝ := Real.arctan v / Real.pi + 1 / 2

/-- Its inverse on `(0,1)`, `p ↦ tan (π (p - 1/2))`. -/
private noncomputable def unitParamInv (p : ℝ) : ℝ := Real.tan (Real.pi * (p - 1 / 2))

private lemma unitParam_mem_Ioo (v : ℝ) : unitParam v ∈ Set.Ioo (0 : ℝ) 1 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : -(Real.pi / 2) < Real.arctan v := Real.neg_pi_div_two_lt_arctan v
  have h2 : Real.arctan v < Real.pi / 2 := Real.arctan_lt_pi_div_two v
  have hlo : -(1 / 2 : ℝ) < Real.arctan v / Real.pi := by rw [lt_div_iff₀ hπ]; linarith
  have hhi : Real.arctan v / Real.pi < 1 / 2 := by rw [div_lt_iff₀ hπ]; linarith
  unfold unitParam
  exact ⟨by linarith, by linarith⟩

private lemma monotone_unitParam : Monotone unitParam := by
  intro a b hab
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h : Real.arctan a ≤ Real.arctan b := Real.arctan_mono hab
  have hd : 0 ≤ (Real.arctan b - Real.arctan a) / Real.pi :=
    div_nonneg (by linarith) hπ.le
  rw [sub_div] at hd
  unfold unitParam
  linarith

private lemma unitParam_unitParamInv {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    unitParam (unitParamInv p) = p := by
  obtain ⟨hp0, hp1⟩ := hp
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : -(Real.pi / 2) < Real.pi * (p - 1 / 2) := by nlinarith
  have h2 : Real.pi * (p - 1 / 2) < Real.pi / 2 := by nlinarith
  unfold unitParam unitParamInv
  rw [Real.arctan_tan h1 h2]
  have hcancel : Real.pi * (p - 1 / 2) / Real.pi = p - 1 / 2 := by
    rw [mul_comm Real.pi (p - 1 / 2), mul_div_assoc, div_self (ne_of_gt hπ), mul_one]
  rw [hcancel]
  ring

private lemma measurable_unitParamInv : Measurable unitParamInv := by
  have htan : Measurable Real.tan := by
    have h : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
    rw [h]
    exact Real.continuous_sin.measurable.div Real.continuous_cos.measurable
  exact htan.comp (measurable_const.mul (measurable_id.sub_const _))

/-! ### Regularity of the sublevel sets of a distribution function -/

/-- Above level `0` the sublevel set of a distribution function is bounded below, so the
`quantile` infimum is not the `sInf`-of-an-unbounded-set junk value. -/
private lemma bddBelow_setOf_le_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] {a : ℝ}
    (ha : 0 < a) : BddBelow {x : ℝ | a ≤ cdf μ x} := by
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp ((tendsto_cdf_atBot μ).eventually_lt_const ha)
  refine ⟨b, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq] at hy
  by_contra hc
  push_neg at hc
  exact absurd (hb y hc.le) (not_lt.mpr hy)

/-- Below level `1` the sublevel set of a distribution function is nonempty, so the
`quantile` infimum is not the `sInf ∅` junk value. -/
private lemma nonempty_setOf_le_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] {a : ℝ}
    (ha : a < 1) : {x : ℝ | a ≤ cdf μ x}.Nonempty := by
  obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt ha).exists
  exact ⟨y, hy.le⟩

/-- The reparametrized quantile function `quantile (cdf μ) ∘ unitParam` is monotone on the
whole line — the junk levels `p ∉ (0,1)` are never reached. -/
private lemma monotone_quantile_unitParam (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone fun v => quantile (⇑(cdf μ)) (unitParam v) := by
  intro a b hab
  exact quantile_mono _ (monotone_unitParam hab)
    (bddBelow_setOf_le_cdf μ (unitParam_mem_Ioo a).1)
    (nonempty_setOf_le_cdf μ (unitParam_mem_Ioo b).2)

/-- The uniform law on `[0,1]` is a probability measure. -/
private lemma isProbabilityMeasure_unitUniform :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  simp

/-- **The coupling identity.** Pushing the `unitParamInv`-image of the uniform law forward
by the reparametrized quantile function recovers `μ`: the reparametrization cancels on
`(0,1)`, which is a full-measure subset, and `map_quantile_uniform` finishes. -/
private lemma map_quantile_unitParam (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).map unitParamInv).map
        (fun v => quantile (⇑(cdf μ)) (unitParam v)) = μ := by
  rw [Measure.map_map (monotone_quantile_unitParam μ).measurable measurable_unitParamInv]
  have hres : volume.restrict (Set.Icc (0 : ℝ) 1) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hcongr : ((fun v => quantile (⇑(cdf μ)) (unitParam v)) ∘ unitParamInv)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] quantile (⇑(cdf μ)) := by
    rw [hres]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    simp only [Function.comp_apply, unitParam_unitParamInv hp]
  rw [Measure.map_congr hcongr]
  exact map_quantile_uniform μ (⇑(cdf μ)) fun x => by rw [cdf_eq_real, measureReal_def]

/-- **A monotone coupling orders the distribution functions.** If `f₀ ≤ f₁` are
nondecreasing and push a common law `ν` forward to `μ₀` and `μ₁`, then `μ₁` puts less mass
on every lower ray: `F₁ ≤ F₀` pointwise. -/
theorem cdf_le_of_monotone_coupling
    -- USER-INPUT: the two laws on the real line
    (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    -- USER-INPUT: the law of the coupling variable `V`
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    -- USER-INPUT: the two realizations
    (f₀ f₁ : ℝ → ℝ)
    -- USER-INPUT: both nondecreasing (measurability follows, so it is not assumed)
    (hf₀ : Monotone f₀) (hf₁ : Monotone f₁)
    -- USER-INPUT: one everywhere below the other — clause (a) of the classical statement
    (hle : ∀ v, f₀ v ≤ f₁ v)
    -- USER-INPUT: the two pushforwards are the given laws — clause (b)
    (hmap₀ : ν.map f₀ = μ₀) (hmap₁ : ν.map f₁ = μ₁) :
    ∀ x : ℝ, (μ₁ (Set.Iic x)).toReal ≤ (μ₀ (Set.Iic x)).toReal := by
  intro x
  have hm0 : Measurable f₀ := hf₀.measurable
  have hm1 : Measurable f₁ := hf₁.measurable
  have e0 : μ₀ (Set.Iic x) = ν {v | f₀ v ≤ x} := by
    rw [← hmap₀, Measure.map_apply hm0 measurableSet_Iic]; rfl
  have e1 : μ₁ (Set.Iic x) = ν {v | f₁ v ≤ x} := by
    rw [← hmap₁, Measure.map_apply hm1 measurableSet_Iic]; rfl
  rw [e0, e1]
  refine ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono ?_)
  exact fun v hv => le_trans (hle v) hv

/-- **The stochastic ordering produces a monotone coupling.** If `F₁ ≤ F₀` pointwise then
both laws are realized as nondecreasing functions of a single variable uniform on `(0,1)`,
one below the other. Constructively: the two maps are the quantile functions of `μ₀` and
`μ₁`.

**Documented deviation from the printed form (forced).** The printed statement is
transcribed with `MonotoneOn … (Set.Ioo 0 1)` and the domination `f₀ v ≤ f₁ v` restricted to
`v ∈ Set.Ioo 0 1`, rather than with global `Monotone f₀ : ℝ → ℝ` and `∀ v`. The global
reading is **FALSE**, in both of its clauses, and both failures are artefacts of the
transcription rather than of the mathematics — the classical coupling is a statement about
the uniform law on the *open* interval `(0,1)`, which is where the quantile functions live.

*Counterexample to global `Monotone`.* Take `μ₀ = μ₁ = 𝒩(0,1)`, for which `hcdf` holds with
equality. If `f₀ : ℝ → ℝ` were globally monotone with `(volume.restrict (Icc 0 1)).map f₀
= μ₀`, then for every real `M` the set `{v ∈ (0,1) | f₀ v < -M}` has positive Lebesgue
measure (it has measure `Φ(-M) > 0`), hence is nonempty; so `inf_{v ∈ (0,1)} f₀ v = -∞`,
while `Monotone f₀` forces `f₀ 0 ≤ f₀ v` for every `v > 0`, i.e. that infimum is `≥ f₀ 0`,
a real number. Contradiction: no global monotone realization exists.

*Counterexample to `∀ v, f₀ v ≤ f₁ v` for the quantile maps.* At the junk level `p = 1` the
two quantiles need not be ordered: with `μ₀ = δ₅` and `μ₁ = 5 + Exp(1)` one has `F₁ ≤ F₀`,
`quantile F₀ 1 = 5`, but `{x | 1 ≤ F₁ x} = ∅` so `quantile F₁ 1 = sInf ∅ = 0 < 5`. Only the
levels in `(0,1)` — a set of full measure for the uniform law, so the coupling is unaffected
— are ordered. -/
theorem exists_monotone_coupling_of_cdf_le
    -- USER-INPUT: the two laws on the real line
    (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    -- USER-INPUT: the stochastic ordering `F₁ ≤ F₀`, the hypothesis of the result
    (hcdf : ∀ x : ℝ, (μ₁ (Set.Iic x)).toReal ≤ (μ₀ (Set.Iic x)).toReal) :
    ∃ f₀ f₁ : ℝ → ℝ, MonotoneOn f₀ (Set.Ioo 0 1) ∧ MonotoneOn f₁ (Set.Ioo 0 1) ∧
      (∀ v ∈ Set.Ioo (0 : ℝ) 1, f₀ v ≤ f₁ v) ∧
      (volume.restrict (Set.Icc (0 : ℝ) 1)).map f₀ = μ₀ ∧
      (volume.restrict (Set.Icc (0 : ℝ) 1)).map f₁ = μ₁ := by
  have hcdfc : ∀ x : ℝ, cdf μ₁ x ≤ cdf μ₀ x := by
    intro x
    simp only [cdf_eq_real, measureReal_def]
    exact hcdf x
  have hmonoOn : ∀ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ),
      MonotoneOn (quantile ⇑(cdf μ)) (Set.Ioo 0 1) := by
    intro μ _ a ha b hb hab
    exact quantile_mono _ hab (bddBelow_setOf_le_cdf μ ha.1) (nonempty_setOf_le_cdf μ hb.2)
  refine ⟨quantile ⇑(cdf μ₀), quantile ⇑(cdf μ₁), hmonoOn μ₀ ‹_›, hmonoOn μ₁ ‹_›,
    fun p hp => ?_, ?_, ?_⟩
  · -- `F₁ ≤ F₀` transfers to the quantiles through the Galois property.
    obtain ⟨hp0, hp1⟩ := hp
    have hq1 : p ≤ cdf μ₁ (quantile (⇑(cdf μ₁)) p) :=
      (quantile_le_iff (monotone_cdf (μ := μ₁)) (fun y => (cdf μ₁).right_continuous y)
        (nonempty_setOf_le_cdf μ₁ hp1) (bddBelow_setOf_le_cdf μ₁ hp0)).mp le_rfl
    exact (quantile_le_iff (monotone_cdf (μ := μ₀)) (fun y => (cdf μ₀).right_continuous y)
      (nonempty_setOf_le_cdf μ₀ hp1) (bddBelow_setOf_le_cdf μ₀ hp0)).mpr
      (le_trans hq1 (hcdfc _))
  · exact map_quantile_uniform μ₀ (⇑(cdf μ₀)) fun x => by rw [cdf_eq_real, measureReal_def]
  · exact map_quantile_uniform μ₁ (⇑(cdf μ₁)) fun x => by rw [cdf_eq_real, measureReal_def]

/-- **The characterization.** Stochastic ordering of two laws on the real line is
equivalent to the existence of a monotone coupling of them. -/
theorem cdf_le_iff_exists_monotone_coupling
    -- USER-INPUT: the two laws on the real line
    (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] :
    (∀ x : ℝ, (μ₁ (Set.Iic x)).toReal ≤ (μ₀ (Set.Iic x)).toReal) ↔
      ∃ (ν : Measure ℝ) (_ : IsProbabilityMeasure ν) (f₀ f₁ : ℝ → ℝ),
        Monotone f₀ ∧ Monotone f₁ ∧ (∀ v, f₀ v ≤ f₁ v) ∧
          ν.map f₀ = μ₀ ∧ ν.map f₁ = μ₁ := by
  constructor
  · -- The existential over `ν` here (absent from `exists_monotone_coupling_of_cdf_le`, which
    -- pins `ν` to the uniform law and therefore only gets `MonotoneOn … (Ioo 0 1)`) is
    -- exactly the freedom needed: take `ν` supported on the whole line and the coupling maps
    -- to be the quantile functions read through the increasing reparametrization
    -- `unitParam : ℝ → (0,1)`.
    intro hcdf
    have hcdfc : ∀ x : ℝ, cdf μ₁ x ≤ cdf μ₀ x := by
      intro x
      simp only [cdf_eq_real, measureReal_def]
      exact hcdf x
    -- (The reparametrization is what buys the *global* `Monotone`; see the docstring of
    -- `exists_monotone_coupling_of_cdf_le`.)
    haveI := isProbabilityMeasure_unitUniform
    refine ⟨(volume.restrict (Set.Icc (0 : ℝ) 1)).map unitParamInv,
      Measure.isProbabilityMeasure_map measurable_unitParamInv.aemeasurable,
      (fun v => quantile (⇑(cdf μ₀)) (unitParam v)),
      (fun v => quantile (⇑(cdf μ₁)) (unitParam v)),
      monotone_quantile_unitParam μ₀, monotone_quantile_unitParam μ₁, ?_,
      map_quantile_unitParam μ₀, map_quantile_unitParam μ₁⟩
    -- `F₁ ≤ F₀` transfers to the quantiles through the Galois property.
    intro v
    obtain ⟨hp0, hp1⟩ := unitParam_mem_Ioo v
    set p := unitParam v with hpdef
    have hq1 : p ≤ cdf μ₁ (quantile (⇑(cdf μ₁)) p) :=
      (quantile_le_iff (monotone_cdf (μ := μ₁)) (fun y => (cdf μ₁).right_continuous y)
        (nonempty_setOf_le_cdf μ₁ hp1) (bddBelow_setOf_le_cdf μ₁ hp0)).mp le_rfl
    exact (quantile_le_iff (monotone_cdf (μ := μ₀)) (fun y => (cdf μ₀).right_continuous y)
      (nonempty_setOf_le_cdf μ₀ hp1) (bddBelow_setOf_le_cdf μ₀ hp0)).mpr
      (le_trans hq1 (hcdfc _))
  · rintro ⟨ν, hν, f₀, f₁, hf₀, hf₁, hle, hmap₀, hmap₁⟩
    haveI := hν
    exact cdf_le_of_monotone_coupling μ₀ μ₁ ν f₀ f₁ hf₀ hf₁ hle hmap₀ hmap₁

end StatLean.HypothesisTesting
