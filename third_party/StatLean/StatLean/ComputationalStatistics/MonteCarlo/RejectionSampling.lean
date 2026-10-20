module
public import StatLean.ComputationalStatistics.Core.Defs
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

/-!
# Rejection sampling (the acceptance/rejection method)

The correctness of Gentle's Algorithm 2.1 (ECS §2.1): draw `Y` from a proposal
with density `q`, draw `U ~ U(0,1)` independently, and accept `Y` when
`U ≤ p(Y)/(c·q(Y))`, where `p` is the target density and `c·q` majorizes `p`.
Then

* `rejectionSampling_acceptProb` — the acceptance probability is `1/c`;
* `rejectionSampling_restrict_map` — the accepted-restricted first marginal is
  `c⁻¹ · (ν.withDensity p)` (the workhorse identity);
* `rejectionSampling_conditionalLaw` — **the accepted draw has exactly the
  target law**: `Law(Y | accept) = ν.withDensity p`.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.1, Algorithm 2.1 and the correctness display
`Pr(Z ≤ x) = ∫_{−∞}^x p_X(t) dt` on p. 40.  (`ECS §2.1`.)

**Proof formalization notes.**

* Densities are `ℝ≥0∞`-valued against an arbitrary σ-finite base measure `ν`
  (Gentle's remark that the discussion covers mass functions verbatim is then
  automatic: take `ν = Measure.count`).
* The acceptance region is stated in the **multiplicative form**
  `ofReal u * (c * q y) ≤ p y`, which is junk-free at `q y = 0`; it agrees with
  the book's `u ≤ p/(cq)` off the `Q`-null set `{q = 0}`.
* `c ≠ 0` is required for the marginal identity (at `c = 0` the accept region
  is everything and the claim is false); `c ≥ 1` is *derivable* from the
  majorization plus `∫⁻ p dν = 1` and is not assumed.
* The proposal-normalization hypothesis `∫⁻ q dν = 1` is genuinely needed (the
  book's `g_Y` *is* a probability density): the first frozen statements omitted
  it and were **refuted** at the `q ≡ ∞` corner — the machine-checked falsity
  witnesses for the unrepaired statements are retained below as `private`
  lemmas documenting why the hypothesis is there.
* The geometric law of the number of trials to first acceptance (ECS §2.1,
  p. 40) is deferred to a later round: it needs the infinite i.i.d. proposal
  stream and a hitting-time construction, orthogonal to the correctness core.

**Bibliographic comments.** The method is von Neumann's ("Various techniques
used in connection with random digits," *NBS Applied Math. Series* **12**
(1951), 36–38); the majorizing-density formulation is standard since
Devroye, *Non-Uniform Random Variate Generation*, Springer, 1986, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

/-- The **uniform distribution on `[0,1]`**: Lebesgue measure restricted to the
unit interval.  The auxiliary randomization of the acceptance step. -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance isProbabilityMeasure_uniform01 : IsProbabilityMeasure uniform01 :=
  ⟨by simp [uniform01, Real.volume_Icc]⟩

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {ν : Measure 𝓧} [SigmaFinite ν]
  {p q : 𝓧 → ℝ≥0∞} {c : ℝ≥0∞}

/-- The **acceptance region** of Algorithm 2.1 (ECS §2.1): the pairs `(y, u)`
with `u·c·q(y) ≤ p(y)`.  Multiplicative form of the book's `u ≤ p(y)/(c·q(y))`;
the two agree wherever `q y ≠ 0`, hence `Q`-a.e. -/
def rejectionAccept (p q : 𝓧 → ℝ≥0∞) (c : ℝ≥0∞) : Set (𝓧 × ℝ) :=
  {yu | ENNReal.ofReal yu.2 * (c * q yu.1) ≤ p yu.1}

/-- The acceptance region is measurable. -/
theorem measurableSet_rejectionAccept
    -- LEAN-ONLY: measurability of the target density (regularity)
    (hp : Measurable p)
    -- LEAN-ONLY: measurability of the proposal density (regularity)
    (hq : Measurable q) :
    MeasurableSet (rejectionAccept p q c) :=
  measurableSet_le
    ((ENNReal.measurable_ofReal.comp measurable_snd).mul ((hq.comp measurable_fst).const_mul c))
    (hp.comp measurable_fst)

/-!
### Falsity witnesses for the `q = ∞` corner

The three correctness identities below were **false as first frozen** (before
the `∫⁻ q dν = 1` hypothesis was added): nothing in the original hypotheses
excluded `q y = ∞` on a set of positive `ν`-measure.  At such a `y`
the acceptance section is `{u | ofReal u · ∞ ≤ p y} = Iic 0`, which is
`uniform01`-null, so the accepted mass contributed by `y` is `q y · 0 = 0`,
whereas the claimed right-hand side contributes `c⁻¹ · p y > 0`.

The witness is `𝓧 = Unit`, `ν = δ`, `p ≡ 1`, `q ≡ ∞`, `c = 1`: every hypothesis
of all three theorems holds, but the acceptance region is a null set.  See
`LANE-REPORT.md`.
-/

/-- The acceptance region of the `q ≡ ∞` witness is a null set for the joint
proposal, even though `p ≡ 1` is a probability density majorized by `1 · q`. -/
private lemma rejectionAccept_unit_top_eq_zero :
    (((Measure.dirac (() : Unit)).withDensity fun _ => ∞).prod uniform01)
        (rejectionAccept (fun _ : Unit => 1) (fun _ : Unit => ∞) 1) = 0 := by
  have hsec : ∀ y : Unit,
      Prod.mk y ⁻¹' rejectionAccept (fun _ : Unit => 1) (fun _ : Unit => ∞) 1
        = Set.Iic (0 : ℝ) := by
    intro y
    ext u
    simp only [Set.mem_preimage, rejectionAccept, Set.mem_setOf_eq, one_mul, Set.mem_Iic]
    rcases le_or_gt u 0 with hu | hu
    · simp [ENNReal.ofReal_eq_zero.mpr hu, hu]
    · have hne : ENNReal.ofReal u ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact hu
      simp [ENNReal.mul_top hne, hu.not_ge]
  have huni : uniform01 (Set.Iic (0 : ℝ)) = 0 := by
    rw [uniform01, Measure.restrict_apply measurableSet_Iic]
    refine measure_mono_null (fun x hx => ?_) (measure_singleton (0 : ℝ))
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc] at hx
    exact Set.mem_singleton_iff.mpr (le_antisymm hx.1 hx.2.1)
  rw [Measure.prod_apply (measurableSet_rejectionAccept measurable_const measurable_const)]
  simp [hsec, huni]

/-- **Falsity witness** for `rejectionSampling_acceptProb`: at `q ≡ ∞` the
acceptance probability is `0`, not `c⁻¹ = 1`. -/
private lemma not_rejectionSampling_acceptProb :
    ¬ ∀ (p q : Unit → ℝ≥0∞) (c : ℝ≥0∞), Measurable p → Measurable q →
        (∫⁻ z, p z ∂(Measure.dirac (() : Unit)) = 1) → (∀ y, p y ≤ c * q y) →
        c ≠ 0 → c ≠ ∞ →
        (((Measure.dirac (() : Unit)).withDensity q).prod uniform01)
            (rejectionAccept p q c) = c⁻¹ := by
  intro h
  have h1 := h (fun _ => 1) (fun _ => ∞) 1 measurable_const measurable_const (by simp)
    (by simp) one_ne_zero ENNReal.one_ne_top
  rw [rejectionAccept_unit_top_eq_zero] at h1
  simp at h1

/-- **Falsity witness** for `rejectionSampling_restrict_map`: at `q ≡ ∞` the
accepted-restricted first marginal is the zero measure, not `c⁻¹ · δ`. -/
private lemma not_rejectionSampling_restrict_map :
    ¬ ∀ (p q : Unit → ℝ≥0∞) (c : ℝ≥0∞), Measurable p → Measurable q →
        (∀ y, p y ≤ c * q y) → c ≠ 0 → c ≠ ∞ →
        ((((Measure.dirac (() : Unit)).withDensity q).prod uniform01).restrict
            (rejectionAccept p q c)).map Prod.fst
          = c⁻¹ • (Measure.dirac (() : Unit)).withDensity p := by
  intro h
  have h1 := congrArg (fun μ : Measure Unit => μ Set.univ)
    (h (fun _ => 1) (fun _ => ∞) 1 measurable_const measurable_const (by simp)
      one_ne_zero ENNReal.one_ne_top)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.smul_apply,
    withDensity_apply _ MeasurableSet.univ] at h1
  rw [rejectionAccept_unit_top_eq_zero] at h1
  simp at h1

/-- **Falsity witness** for `rejectionSampling_conditionalLaw`: at `q ≡ ∞` the
conditioning set is null, so the conditional law is the zero measure. -/
private lemma not_rejectionSampling_conditionalLaw :
    ¬ ∀ (p q : Unit → ℝ≥0∞) (c : ℝ≥0∞), Measurable p → Measurable q →
        (∫⁻ z, p z ∂(Measure.dirac (() : Unit)) = 1) → (∀ y, p y ≤ c * q y) →
        c ≠ 0 → c ≠ ∞ →
        (ProbabilityTheory.cond (((Measure.dirac (() : Unit)).withDensity q).prod uniform01)
            (rejectionAccept p q c)).map Prod.fst
          = (Measure.dirac (() : Unit)).withDensity p := by
  intro h
  have h1 := congrArg (fun μ : Measure Unit => μ Set.univ)
    (h (fun _ => 1) (fun _ => ∞) 1 measurable_const measurable_const (by simp) (by simp)
      one_ne_zero ENNReal.one_ne_top)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    ProbabilityTheory.cond_apply' MeasurableSet.univ, Set.inter_univ,
    withDensity_apply _ MeasurableSet.univ] at h1
  rw [rejectionAccept_unit_top_eq_zero] at h1
  simp at h1

/-!
### The pointwise section computation

The whole content of the three identities is one pointwise fact: for a proposal
value `y` with `q y ≠ ∞`, the `uniform01`-measure of the acceptance section
above `y`, weighted by `q y`, is exactly `c⁻¹ · p y`.
-/

set_option linter.unusedSectionVars false in
/-- The `y`-section of the acceptance region is the interval `Iic r` with
`ENNReal.ofReal r = p y / (c * q y)`, so `q y · uniform01 (section) = c⁻¹ · p y`.
This is where `q y ≠ ∞` (a consequence of `∫⁻ q dν = 1`) is used. -/
private lemma uniform01_section_mul (henv : ∀ y, p y ≤ c * q y) (hc0 : c ≠ 0)
    (hcT : c ≠ ∞) {y : 𝓧} (hy : q y ≠ ∞) :
    q y * uniform01 {u : ℝ | ENNReal.ofReal u * (c * q y) ≤ p y} = c⁻¹ * p y := by
  rcases eq_or_ne (q y) 0 with h0 | h0
  · have hp0 : p y = 0 := le_antisymm (by simpa [h0] using henv y) (zero_le)
    simp [h0, hp0]
  · have hA0 : c * q y ≠ 0 := mul_ne_zero hc0 h0
    have hAT : c * q y ≠ ∞ := ENNReal.mul_ne_top hcT hy
    have hpA : p y ≤ c * q y := henv y
    have hpT : p y ≠ ∞ := ne_top_of_le_ne_top hAT hpA
    have hdivT : p y / (c * q y) ≠ ∞ := ENNReal.div_ne_top hpT hA0
    have hdiv1 : p y / (c * q y) ≤ 1 := ENNReal.div_le_of_le_mul (by simpa using hpA)
    set r : ℝ := (p y / (c * q y)).toReal with hr
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    have hr1 : r ≤ 1 := by
      rw [hr, ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top hdiv1
    have hofReal : ENNReal.ofReal r = p y / (c * q y) := ENNReal.ofReal_toReal hdivT
    -- the section is `Iic r`
    have hsec : {u : ℝ | ENNReal.ofReal u * (c * q y) ≤ p y} = Set.Iic r := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_Iic]
      constructor
      · intro hu
        rcases le_or_gt u 0 with hu0 | hu0
        · exact hu0.trans hr0
        · have h1 : ENNReal.ofReal u ≤ p y / (c * q y) :=
            ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl hAT) |>.mpr hu
          rw [← hofReal] at h1
          exact (ENNReal.ofReal_le_ofReal_iff hr0).mp h1
      · intro hu
        have h1 : ENNReal.ofReal u ≤ p y / (c * q y) := by
          rw [← hofReal]; exact ENNReal.ofReal_le_ofReal hu
        calc ENNReal.ofReal u * (c * q y) ≤ p y / (c * q y) * (c * q y) := by gcongr
          _ = p y := ENNReal.div_mul_cancel hA0 hAT
    -- and `uniform01 (Iic r) = ofReal r`
    have huni : uniform01 (Set.Iic r) = ENNReal.ofReal r := by
      rw [uniform01, Measure.restrict_apply measurableSet_Iic]
      have hset : Set.Iic r ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 r := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hr1⟩⟩
      rw [hset, Real.volume_Icc, sub_zero]
    rw [hsec, huni, hofReal, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl hcT)]
    have hcalc : q y * (p y * (c⁻¹ * (q y)⁻¹)) = q y * (q y)⁻¹ * (c⁻¹ * p y) := by ring
    rw [hcalc, ENNReal.mul_inv_cancel h0 hy, one_mul]

set_option linter.unusedSectionVars false in
/-- **Accepted-restricted marginal identity**: restricting the joint proposal
`(Y, U) ~ (ν.withDensity q) ⊗ U(0,1)` to the acceptance region, the law of `Y`
is `c⁻¹ · (ν.withDensity p)`.  This is the workhorse behind both the
acceptance probability and the conditional-law theorem. -/
theorem rejectionSampling_restrict_map
    -- LEAN-ONLY: measurability of the target density (regularity)
    (hp : Measurable p)
    -- LEAN-ONLY: measurability of the proposal density (regularity)
    (hq : Measurable q)
    -- USER-INPUT: the proposal density integrates to one; ECS §2.1
    (hq1 : ∫⁻ z, q z ∂ν = 1)
    -- USER-INPUT: the scaled proposal majorizes the target, `p ≤ c·q`; ECS §2.1
    (henv : ∀ y, p y ≤ c * q y)
    -- USER-INPUT: a positive, finite envelope constant; ECS §2.1
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    (((ν.withDensity q).prod uniform01).restrict (rejectionAccept p q c)).map
        Prod.fst
      = c⁻¹ • ν.withDensity p := by
  have hA : MeasurableSet (rejectionAccept p q c) := measurableSet_rejectionAccept hp hq
  have hqae : ∀ᵐ y ∂ν, q y ≠ ∞ := by
    have hfin : ∫⁻ z, q z ∂ν ≠ ∞ := by rw [hq1]; exact ENNReal.one_ne_top
    filter_upwards [ae_lt_top hq hfin] with y hy using hy.ne
  refine Measure.ext fun S hS => ?_
  have hSm : MeasurableSet (Prod.fst ⁻¹' S : Set (𝓧 × ℝ)) := measurable_fst hS
  -- the `y`-section of the accepted part of the cylinder over `S`
  have hsec : ∀ y : 𝓧,
      uniform01 (Prod.mk y ⁻¹' ((Prod.fst ⁻¹' S : Set (𝓧 × ℝ)) ∩ rejectionAccept p q c))
        = S.indicator
            (fun y => uniform01 {u : ℝ | ENNReal.ofReal u * (c * q y) ≤ p y}) y := by
    intro y
    by_cases hyS : y ∈ S
    · have he : Prod.mk y ⁻¹' ((Prod.fst ⁻¹' S : Set (𝓧 × ℝ)) ∩ rejectionAccept p q c)
          = {u : ℝ | ENNReal.ofReal u * (c * q y) ≤ p y} := by
        ext u; simp [rejectionAccept, hyS]
      rw [he, Set.indicator_of_mem hyS]
    · have he : Prod.mk y ⁻¹' ((Prod.fst ⁻¹' S : Set (𝓧 × ℝ)) ∩ rejectionAccept p q c)
          = (∅ : Set ℝ) := by
        ext u; simp [hyS]
      rw [he, Set.indicator_of_notMem hyS, measure_empty]
  rw [Measure.map_apply measurable_fst hS, Measure.restrict_apply hSm,
    Measure.prod_apply (hSm.inter hA),
    lintegral_withDensity_eq_lintegral_mul _ hq
      (measurable_measure_prodMk_left (hSm.inter hA)),
    Measure.smul_apply, smul_eq_mul, withDensity_apply _ hS]
  simp only [Pi.mul_apply]
  have key : ∀ᵐ y ∂ν,
      q y * uniform01 (Prod.mk y ⁻¹' ((Prod.fst ⁻¹' S : Set (𝓧 × ℝ)) ∩ rejectionAccept p q c))
        = S.indicator (fun y => c⁻¹ * p y) y := by
    filter_upwards [hqae] with y hy
    rw [hsec y]
    by_cases hyS : y ∈ S
    · rw [Set.indicator_of_mem hyS, Set.indicator_of_mem hyS]
      exact uniform01_section_mul henv hc0 hcT hy
    · rw [Set.indicator_of_notMem hyS, Set.indicator_of_notMem hyS, mul_zero]
  rw [lintegral_congr_ae key, lintegral_indicator hS,
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0)]

/-- **Acceptance probability of rejection sampling** (ECS §2.1, p. 40): the
joint proposal puts mass exactly `1/c` on the acceptance region. -/
theorem rejectionSampling_acceptProb
    -- LEAN-ONLY: measurability of the target density (regularity)
    (hp : Measurable p)
    -- LEAN-ONLY: measurability of the proposal density (regularity)
    (hq : Measurable q)
    -- USER-INPUT: the proposal density integrates to one; ECS §2.1
    (hq1 : ∫⁻ z, q z ∂ν = 1)
    -- USER-INPUT: the target density integrates to one; ECS §2.1
    (hp1 : ∫⁻ z, p z ∂ν = 1)
    -- USER-INPUT: the scaled proposal majorizes the target, `p ≤ c·q`; ECS §2.1
    (henv : ∀ y, p y ≤ c * q y)
    -- USER-INPUT: a positive, finite envelope constant; ECS §2.1
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    ((ν.withDensity q).prod uniform01) (rejectionAccept p q c) = c⁻¹ := by
  have h := congrArg (fun μ : Measure 𝓧 => μ Set.univ)
    (rejectionSampling_restrict_map hp hq hq1 henv hc0 hcT)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.smul_apply,
    smul_eq_mul, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  rw [h, hp1, mul_one]

/-- **Rejection sampling returns exactly the target law** (ECS §2.1,
Algorithm 2.1 and the display on p. 40): conditionally on acceptance, the
proposed draw has law `ν.withDensity p`. -/
theorem rejectionSampling_conditionalLaw
    -- LEAN-ONLY: measurability of the target density (regularity)
    (hp : Measurable p)
    -- LEAN-ONLY: measurability of the proposal density (regularity)
    (hq : Measurable q)
    -- USER-INPUT: the proposal density integrates to one; ECS §2.1
    (hq1 : ∫⁻ z, q z ∂ν = 1)
    -- USER-INPUT: the target density integrates to one; ECS §2.1
    (hp1 : ∫⁻ z, p z ∂ν = 1)
    -- USER-INPUT: the scaled proposal majorizes the target, `p ≤ c·q`; ECS §2.1
    (henv : ∀ y, p y ≤ c * q y)
    -- USER-INPUT: a positive, finite envelope constant; ECS §2.1
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    (ProbabilityTheory.cond ((ν.withDensity q).prod uniform01)
        (rejectionAccept p q c)).map Prod.fst
      = ν.withDensity p := by
  rw [ProbabilityTheory.cond, Measure.map_smul,
    rejectionSampling_restrict_map hp hq hq1 henv hc0 hcT,
    rejectionSampling_acceptProb hp hq hq1 hp1 henv hc0 hcT, smul_smul,
    inv_inv, ENNReal.mul_inv_cancel hc0 hcT, one_smul]

end StatLean.ComputationalStatistics
