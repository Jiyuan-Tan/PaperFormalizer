module
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Gross-error contamination — the ε-mixture `(1-ε)P + εQ`

The fundamental perturbation model of robust statistics: the observed distribution is not
the ideal `P` but the *ε-contaminated* mixture $(1-\varepsilon)P + \varepsilon Q$ where a
fraction `ε` of the data comes from an arbitrary outlier-generating distribution `Q`
(`MMY §2.2`, eq. (2.6)–(2.7)). The gross-error neighbourhood collects all such mixtures
(`MMY §3.3`, eq. (3.3)).

* `contaminate P Q ε` — the mixture `(1-ε) • P + ε • Q`, real contamination weight.
* `grossErrorNbhd P ε` — the contamination neighbourhood `{(1-ε)P + εQ : Q probability}`.
* algebra: endpoints, self-contamination, probability instance, measure of a set,
  integrability and integral formulas, pushforward, and neighbourhood nesting.

**Design note (real weight, clamped coefficients).** The weight is a *real* `ε`, encoded
through `ENNReal.ofReal`, so that curves `t ↦ contaminate P Q t` are literally real-parameter
families — the influence function is a one-sided derivative in `t` at `0`
(`Core/InfluenceFunction.lean`). For `ε ∈ [0,1]` the definition is the book's mixture; outside
`[0,1]` the coefficients clamp at `0` (junk values, never used by the theorems). The
definition is definitionally the mixture form
`ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q` used by the von Mises calculus in
`StatLean/AsymptoticStatistics/Core/MassMethod.lean`, so those results apply verbatim.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.2 (eq. (2.6),
(2.7): departures from normality via mixtures), §3.3 (eq. (3.3): contamination
neighbourhoods).

**Bibliographic comments.** The contaminated-distribution model enters with J. W. Tukey, "A
survey of sampling from contaminated distributions," in *Contributions to Probability and
Statistics: Essays in Honor of Harold Hotelling*, Stanford Univ. Press, 1960, pp. 448–485;
the ε-contamination *neighbourhood* as the domain of a minimax problem is P. J. Huber,
"Robust estimation of a location parameter," *Ann. Math. Statist.* **35** (1964), 73–101.
Systematic treatments: Huber and Ronchetti, *Robust Statistics*, 2nd ed., Wiley, 2009,
§1.2 and ch. 4.
-/

open MeasureTheory

namespace StatLean.RobustStatistics

variable {Ω : Type*} [MeasurableSpace Ω] {Ω' : Type*} [MeasurableSpace Ω']

/-- **ε-contamination** of `P` by `Q` (`MMY §2.2`, eq. (2.6)): the mixture
`(1-ε) • P + ε • Q` with real weight `ε`. Coefficients clamp at `0` outside `ε ∈ [0,1]`
(junk values: `contaminate P Q ε = Q` for `ε ≥ 1`, `= P` for `ε ≤ 0`). -/
noncomputable def contaminate (P Q : Measure Ω) (ε : ℝ) : Measure Ω :=
  ENNReal.ofReal (1 - ε) • P + ENNReal.ofReal ε • Q

/-- Zero contamination is the ideal model. -/
@[simp] theorem contaminate_zero (P Q : Measure Ω) : contaminate P Q 0 = P := by
  simp [contaminate]

/-- Full contamination is the outlier distribution. -/
@[simp] theorem contaminate_one (P Q : Measure Ω) : contaminate P Q 1 = Q := by
  simp [contaminate]

/-- Contaminating `P` by itself changes nothing (for `ε ∈ [0,1]`). -/
theorem contaminate_self (P : Measure Ω) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    contaminate P P ε = P := by
  refine Measure.ext fun s _ => ?_
  simp only [contaminate, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [← add_mul, ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1 - ε) h0,
    show (1 - ε) + ε = (1 : ℝ) from by ring, ENNReal.ofReal_one, one_mul]

/-- The measure of a set under the contaminated mixture. -/
theorem contaminate_apply (P Q : Measure Ω) (ε : ℝ) (s : Set Ω) :
    contaminate P Q ε s = ENNReal.ofReal (1 - ε) * P s + ENNReal.ofReal ε * Q s := by
  simp only [contaminate, Measure.add_apply, Measure.smul_apply, smul_eq_mul]

/-- The mixture of two probability measures with weights in `[0,1]` is a probability
measure. -/
theorem isProbabilityMeasure_contaminate (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (contaminate P Q ε) := by
  refine ⟨?_⟩
  rw [contaminate_apply, measure_univ, measure_univ, mul_one, mul_one,
    ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1 - ε) h0,
    show (1 - ε) + ε = (1 : ℝ) from by ring, ENNReal.ofReal_one]

/-- Integrability passes to the contaminated mixture. (Named without the `Integrable.`
prefix: inside a declaration `Integrable.contaminate`, the bare name `contaminate` would
resolve recursively to the theorem itself.) -/
theorem integrable_contaminate {P Q : Measure Ω} {f : Ω → ℝ} (hfP : Integrable f P)
    (hfQ : Integrable f Q) (ε : ℝ) : Integrable f (contaminate P Q ε) :=
  (hfP.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hfQ.smul_measure ENNReal.ofReal_ne_top)

/-- Integrability against the mixture implies integrability against the ideal component
(for `ε < 1`). -/
theorem Integrable.of_contaminate_left {P Q : Measure Ω} {f : Ω → ℝ} {ε : ℝ} (h1 : ε < 1)
    (hf : Integrable f (contaminate P Q ε)) : Integrable f P := by
  have hf' : Integrable f (ENNReal.ofReal (1 - ε) • P) ∧
      Integrable f (ENNReal.ofReal ε • Q) := integrable_add_measure.mp hf
  have hne : ENNReal.ofReal (1 - ε) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).mp hf'.1

/-- The integral against the contaminated mixture is the convex combination of the
component integrals (`MMY §2.2`, the total-probability decomposition behind eq. (2.7)). -/
theorem integral_contaminate {P Q : Measure Ω} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    {f : Ω → ℝ} (hfP : Integrable f P) (hfQ : Integrable f Q) :
    ∫ x, f x ∂(contaminate P Q ε) = (1 - ε) * ∫ x, f x ∂P + ε * ∫ x, f x ∂Q := by
  rw [contaminate, integral_add_measure (hfP.smul_measure ENNReal.ofReal_ne_top)
      (hfQ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - ε), ENNReal.toReal_ofReal h0,
    smul_eq_mul, smul_eq_mul]

/-- Point-mass contamination integral: contaminating with `δ_{x₀}` adds an `ε f x₀` term.
This is the mixture entering the influence function (`MMY §3.1`, eq. (3.4)). -/
theorem integral_contaminate_dirac [MeasurableSingletonClass Ω] {P : Measure Ω} {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {f : Ω → ℝ} (hfP : Integrable f P) (x₀ : Ω) :
    ∫ x, f x ∂(contaminate P (Measure.dirac x₀) ε) = (1 - ε) * ∫ x, f x ∂P + ε * f x₀ := by
  rw [integral_contaminate h0 h1 hfP (integrable_dirac (by simp)), integral_dirac]

/-- Measurable pushforward commutes with contamination. -/
theorem map_contaminate {P Q : Measure Ω} {f : Ω → Ω'} (hf : Measurable f) (ε : ℝ) :
    (contaminate P Q ε).map f = contaminate (P.map f) (Q.map f) ε := by
  simp only [contaminate, Measure.map_add _ _ hf, Measure.map_smul]

/-! ### The gross-error neighbourhood -/

/-- The **gross-error (contamination) neighbourhood** of `P` at level `ε`
(`MMY §3.3`, eq. (3.3)): all mixtures `(1-ε)P + εQ` with `Q` a probability measure. -/
def grossErrorNbhd (P : Measure Ω) (ε : ℝ) : Set (Measure Ω) :=
  {R | ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ R = contaminate P Q ε}

/-- The contaminated mixture belongs to the neighbourhood. -/
theorem contaminate_mem_grossErrorNbhd (P Q : Measure Ω) [IsProbabilityMeasure Q] (ε : ℝ) :
    contaminate P Q ε ∈ grossErrorNbhd P ε :=
  ⟨Q, inferInstance, rfl⟩

/-- At level `0` the neighbourhood degenerates to `{P}` (the sample space must carry a
probability measure for the neighbourhood to be nonempty, hence the `[IsProbabilityMeasure P]`
witness). -/
theorem grossErrorNbhd_zero (P : Measure Ω) [IsProbabilityMeasure P] :
    grossErrorNbhd P 0 = {P} := by
  ext R
  simp only [grossErrorNbhd, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨Q, -, rfl⟩
    exact contaminate_zero P Q
  · intro hR
    exact ⟨P, inferInstance, by rw [contaminate_zero]; exact hR⟩

/-- **Neighbourhood nesting**: contamination neighbourhoods grow with the level,
`0 ≤ ε ≤ δ ≤ 1` implies `𝒩_ε(P) ⊆ 𝒩_δ(P)`. -/
theorem grossErrorNbhd_mono (P : Measure Ω) [IsProbabilityMeasure P] {ε δ : ℝ}
    (h0 : 0 ≤ ε) (hεδ : ε ≤ δ) (hδ1 : δ ≤ 1) (hδ : 0 < δ) :
    grossErrorNbhd P ε ⊆ grossErrorNbhd P δ := by
  rintro R ⟨Q, hQ, rfl⟩
  haveI := hQ
  have hr0 : 0 ≤ ε / δ := div_nonneg h0 hδ.le
  have hr1 : ε / δ ≤ 1 := (div_le_one hδ).mpr hεδ
  refine ⟨contaminate P Q (ε / δ), isProbabilityMeasure_contaminate P Q hr0 hr1, ?_⟩
  refine Measure.ext fun s _ => ?_
  simp only [contaminate_apply]
  have hd : ENNReal.ofReal δ * ENNReal.ofReal (1 - ε / δ) = ENNReal.ofReal (δ - ε) := by
    rw [← ENNReal.ofReal_mul hδ.le]
    congr 1
    field_simp
  have he : ENNReal.ofReal δ * ENNReal.ofReal (ε / δ) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hδ.le]
    congr 1
    field_simp
  have key : ENNReal.ofReal (1 - δ) * P s
      + ENNReal.ofReal δ * (ENNReal.ofReal (1 - ε / δ) * P s + ENNReal.ofReal (ε / δ) * Q s)
      = (ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ * ENNReal.ofReal (1 - ε / δ)) * P s
        + ENNReal.ofReal δ * ENNReal.ofReal (ε / δ) * Q s := by
    ring
  rw [key, hd, he, ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1 - δ)
      (by linarith : (0:ℝ) ≤ δ - ε), show (1 - δ) + (δ - ε) = 1 - ε from by ring]

end StatLean.RobustStatistics
