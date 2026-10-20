module
public import StatLean.HypothesisTesting.Tests.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# The sign-change identity for symmetric tests of symmetry

Tests of the hypothesis that a distribution is symmetric about the origin are usually
built from the ranks of the absolute observations together with the signs. Such tests are
calibrated under the assumption that the observations are an i.i.d. sample from a
continuous distribution symmetric about the origin. That assumption is often the doubtful
part of the model — the observations may be gathered under different experimental
conditions and need be neither identically distributed nor even independent.

The identity below shows that for tests **symmetric in their arguments** the calibration
survives this loss of assumptions entirely. If a symmetric critical function has mean `α`
under every independent sample from continuous distributions symmetric about the origin, then
it has mean `α` under *any* joint distribution invariant under the `2^N` coordinatewise
sign changes — no independence, no common distribution. In the paired-comparison design
this invariance is guaranteed by construction, since the treatment is assigned at random
within each pair; so the stated significance level is exactly right regardless of how the
pairs differ from one another.

The mechanism is that the null-calibration forces the *average over the `2^N` sign
patterns* of the test to equal `α` almost everywhere, and sign-change invariance of the joint
law makes the conditional distribution of the signs given the absolute values uniform over
those `2^N` patterns — so the pointwise average is exactly the conditional expectation.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.10
(The Hypothesis of Symmetry), Lemma 6.10.1 (the sign-change identity for testing symmetry).
(`TSH4 §6.10 Lem 6.10.1`.)

## The transcribed identity is FALSE, and the repair carried out here

`not_integral_eq_of_sign_invariant` refutes the identity as printed, with `N = 1`, `α = 0`,
`φ = 1_{\{0\}}` and `Q = δ₀`; a second counterexample in its docstring has no zeros and no
ties. The calibration hypothesis pins the sign-average to `α` only off a set null for every
*non-atomic* law, and a sign-change invariant `Q` may sit entirely on that set.

Two **documented amendments** are therefore made to the printed statement, and the amended
statement `integral_eq_of_sign_invariant` is proved in full.

1. `Q ≪ volume` (absolute continuity of the joint law with respect to Lebesgue measure on
   `ℝ^N`). This amendment is *forced*: the counterexamples are atomic laws, and for `N = 1`
   they survive amendment 2 as well (see below), so no weakening of the calibration class can
   remove the need for it. It is the first of the two repairs the source's own argument
   silently uses.
2. The calibration class is the **independent, not necessarily identically distributed**
   one: `φ` is assumed to have mean `α` under `⊗ᵢ Dᵢ` for every family of continuous
   distributions symmetric about the origin, rather than only under the i.i.d. products
   `D^{⊗N}`. This amendment is *not* forced — the i.i.d. form is presumably still true — but
   it is what the proof below uses, and dropping it is a genuine gap: passing from "mean `α`
   under every i.i.d. continuous symmetric sample" to the pointwise sign-average identity is a
   completeness statement for the class of order statistics from non-atomic laws, whose
   standard proof is an inclusion–exclusion (equivalently, a polynomial-coefficient extraction)
   over the `N^N` terms of `(∑ᵢ wᵢUᵢ)^{⊗N}` and is not formalized here. With independent
   marginals the same conclusion is one application of the product structure, which is what is
   done below.

With amendment 2 the permutation-symmetry hypothesis of the printed statement is not needed and
is dropped; the identity holds for every critical function. For `N = 1` the two calibration
classes coincide, so the counterexample of `not_integral_eq_of_sign_invariant` refutes the
amended statement as well once `Q ≪ volume` is dropped: both amendments are visible in that one
example.

**Main results.**
* `signFlip` — the coordinatewise sign-change transformation;
* `measurable_signFlip` — its measurability;
* `signAverage` — the average of a test over the `2^N` sign patterns;
* `not_integral_eq_of_sign_invariant` — the counterexample refuting the printed identity;
* `integral_eq_of_sign_invariant` — the amended identity.

**Proof formalization notes.**
* The `2^N` sign changes are indexed by `Fin N → Bool` and applied through `signFlip`.
  They are *not* packaged as a group action: the statement quantifies over the family of
  transformations directly, which is all the argument uses and avoids importing a group
  structure on the index type.
* The null class is transcribed with `Measure.pi D` for an arbitrary family `D` of
  distributions which are **continuous** (no atoms, `Dᵢ {t} = 0`) and **symmetric about the
  origin** (`Dᵢ` invariant under negation); see amendment 2 above.
* The engine is `pi_symmetrize_eq`: the product of the *symmetrizations* of measures `νᵢ` is
  the uniform average of the `2^N` sign-flips of `⊗ᵢνᵢ`. Hence integrating `φ` against a
  product of symmetric laws is integrating `signAverage φ` against an arbitrary product law.
  Taking `νᵢ` to be normalized Lebesgue measure on a box turns the calibration hypothesis into
  "the average of `signAverage φ` over every box is `α`", and `Measure.pi_eq` upgrades that to
  an identity of measures on each cube `[-R,R]^N`, hence to `signAverage φ = α` a.e.

**Bibliographic comments.** Randomization within matched pairs as the source of exact
significance levels for sign and signed-rank procedures goes back to R. A. Fisher (*The
Design of Experiments*, Oliver & Boyd, 1935). The observation that a symmetric rank test
retains its level under any sign-change-invariant joint law — dispensing with both
independence and identical distribution — belongs to the non-parametric program of
E. L. Lehmann and C. Stein ("On the theory of some non-parametric hypotheses," *Ann. Math.
Statist.* **20** (1949), 28–45), and was developed further in E. L. Lehmann's work of the
1950s. The one-sample signed-rank statistic itself is due to F. Wilcoxon ("Individual
comparisons by ranking methods," *Biometrics Bull.* **1** (1945), 80–83).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

/-- **Coordinatewise sign change**: flip the sign of the coordinates selected by `ε`. The
`2^N` maps obtained as `ε` ranges over `Fin N → Bool` are the sign-change transformations
of the sample space. -/
def signFlip {N : ℕ} (ε : Fin N → Bool) (z : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if ε i then -(z i) else z i

/-- Sign changes are measurable. -/
theorem measurable_signFlip {N : ℕ} (ε : Fin N → Bool) :
    Measurable (signFlip ε) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : ε i = true
  · have : (fun z : Fin N → ℝ => signFlip ε z i) = fun z => -(z i) := by
      funext z; simp only [signFlip, if_pos h]
    rw [this]; exact (measurable_pi_apply i).neg
  · have : (fun z : Fin N → ℝ => signFlip ε z i) = fun z => z i := by
      funext z; simp only [signFlip, if_neg h]
    rw [this]; exact measurable_pi_apply i

/-- The **sign-average** of a test: its mean over the `2^N` coordinatewise sign changes. It is
a function of the absolute values alone, and the identity below is the statement that the
calibration hypothesis pins it to the level `α`. -/
noncomputable def signAverage {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) : ℝ :=
  (Fintype.card (Fin N → Bool) : ℝ)⁻¹ * ∑ ε : Fin N → Bool, φ (signFlip ε z)

/-- A critical function is integrable against any finite measure. -/
private lemma integrable_of_isCriticalFn {X : Type*} [MeasurableSpace X] {φ : X → ℝ}
    (hφ : IsCriticalFn φ) (μ : Measure X) [IsFiniteMeasure μ] : Integrable φ μ :=
  (integrable_const (1 : ℝ)).mono' hφ.1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ.2 x).1]; exact (hφ.2 x).2)

/-- The sign-average of a critical function is a critical function. -/
private lemma isCriticalFn_signAverage {N : ℕ} {φ : (Fin N → ℝ) → ℝ} (hφ : IsCriticalFn φ) :
    IsCriticalFn (signAverage φ) := by
  have hcard : (0 : ℝ) < (Fintype.card (Fin N → Bool) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨measurable_const.mul
    (Finset.measurable_sum _ fun ε _ => hφ.1.comp (measurable_signFlip ε)), fun z => ?_⟩
  refine Set.mem_Icc.2 ⟨mul_nonneg (le_of_lt (inv_pos.2 hcard))
    (Finset.sum_nonneg fun ε _ => (hφ.2 _).1), ?_⟩
  have hsum : ∑ ε : Fin N → Bool, φ (signFlip ε z)
      ≤ (Fintype.card (Fin N → Bool) : ℝ) := by
    calc ∑ ε : Fin N → Bool, φ (signFlip ε z) ≤ ∑ _ε : Fin N → Bool, (1 : ℝ) :=
          Finset.sum_le_sum fun ε _ => (hφ.2 _).2
      _ = (Fintype.card (Fin N → Bool) : ℝ) := by simp [Finset.card_univ]
  calc (Fintype.card (Fin N → Bool) : ℝ)⁻¹ * ∑ ε : Fin N → Bool, φ (signFlip ε z)
      ≤ (Fintype.card (Fin N → Bool) : ℝ)⁻¹ * (Fintype.card (Fin N → Bool) : ℝ) := by
        gcongr
    _ = 1 := inv_mul_cancel₀ hcard.ne'

/-! ### Symmetrization of a law on the line -/

/-- The **symmetrization** of a measure on the line: the average of `ν` and its reflection. -/
private noncomputable def symmetrize (ν : Measure ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (ν + ν.map (fun t : ℝ => -t))

private lemma symmetrize_apply (ν : Measure ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    symmetrize ν s = (2 : ℝ≥0∞)⁻¹ * (ν s + ν ((fun t : ℝ => -t) ⁻¹' s)) := by
  simp only [symmetrize, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply measurable_neg hs, smul_eq_mul]

private instance instIsProbabilityMeasureSymmetrize (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (symmetrize ν) := by
  constructor
  rw [symmetrize_apply ν MeasurableSet.univ, Set.preimage_univ, measure_univ]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private lemma symmetrize_map_neg (ν : Measure ℝ) :
    (symmetrize ν).map (fun t : ℝ => -t) = symmetrize ν := by
  ext s hs
  have hdouble : (fun t : ℝ => -t) ⁻¹' ((fun t : ℝ => -t) ⁻¹' s) = s := by ext t; simp
  rw [Measure.map_apply measurable_neg hs, symmetrize_apply ν (measurable_neg hs),
    symmetrize_apply ν hs, hdouble, add_comm]

private lemma symmetrize_singleton (ν : Measure ℝ) (hν : ∀ t : ℝ, ν {t} = 0) (t : ℝ) :
    symmetrize ν {t} = 0 := by
  have hpre : (fun u : ℝ => -u) ⁻¹' {t} = {-t} := by
    ext u; simp [neg_eq_iff_eq_neg, eq_comm]
  rw [symmetrize_apply ν (measurableSet_singleton t), hpre, hν, hν]
  simp

/-- **The engine.** The product of the symmetrizations of `νᵢ` is the uniform average of the
`2^N` sign-flips of `⊗ᵢ νᵢ`. -/
private lemma pi_symmetrize_eq {N : ℕ} (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] :
    Measure.pi (fun i => symmetrize (ν i))
      = ((2 : ℝ≥0∞) ^ N)⁻¹ • ∑ ε : Fin N → Bool, (Measure.pi ν).map (signFlip ε) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  have hpi : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hstep : ∀ ε : Fin N → Bool, ((Measure.pi ν).map (signFlip ε)) (Set.univ.pi s)
      = ∏ i, (ν i) (if ε i then (fun t : ℝ => -t) ⁻¹' (s i) else s i) := by
    intro ε
    have hpre : signFlip ε ⁻¹' (Set.univ.pi s)
        = Set.univ.pi (fun i => if ε i then (fun t : ℝ => -t) ⁻¹' (s i) else s i) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_univ_pi, signFlip]
      refine forall_congr' fun i => ?_
      cases hε : ε i <;> simp [hε]
    rw [Measure.map_apply (measurable_signFlip ε) hpi, hpre, Measure.pi_pi]
  rw [Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply,
    Finset.sum_congr rfl fun ε _ => hstep ε]
  have hsym : ∀ i, symmetrize (ν i) (s i)
      = ∑ b : Bool, (2 : ℝ≥0∞)⁻¹ * (ν i) (if b then (fun t : ℝ => -t) ⁻¹' (s i) else s i) := by
    intro i
    have h1 : (if (true : Bool) then (fun t : ℝ => -t) ⁻¹' (s i) else s i)
        = (fun t : ℝ => -t) ⁻¹' (s i) := if_pos rfl
    have h2 : (if (false : Bool) then (fun t : ℝ => -t) ⁻¹' (s i) else s i) = s i := by simp
    rw [symmetrize_apply (ν i) (hs i), Fintype.sum_bool, h1, h2]
    ring
  rw [Finset.prod_congr rfl fun i _ => hsym i, Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow]

/-- Integrating `φ` against a product of symmetric laws is integrating its sign-average
against the underlying product law. -/
private lemma integral_pi_symmetrize {N : ℕ} {φ : (Fin N → ℝ) → ℝ} (hφ : IsCriticalFn φ)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] :
    ∫ z, φ z ∂(Measure.pi fun i => symmetrize (ν i))
      = ∫ z, signAverage φ z ∂(Measure.pi ν) := by
  classical
  have hintmap : ∀ ε : Fin N → Bool, Integrable φ ((Measure.pi ν).map (signFlip ε)) := by
    intro ε
    haveI : IsProbabilityMeasure ((Measure.pi ν).map (signFlip ε)) :=
      Measure.isProbabilityMeasure_map (measurable_signFlip ε).aemeasurable
    exact integrable_of_isCriticalFn hφ _
  have hintcomp : ∀ ε : Fin N → Bool,
      Integrable (fun z => φ (signFlip ε z)) (Measure.pi ν) :=
    fun ε => integrable_of_isCriticalFn
      ⟨hφ.1.comp (measurable_signFlip ε), fun z => hφ.2 _⟩ _
  have heach : ∀ ε : Fin N → Bool, ∫ z, φ z ∂((Measure.pi ν).map (signFlip ε))
      = ∫ z, φ (signFlip ε z) ∂(Measure.pi ν) := fun ε =>
    integral_map (measurable_signFlip ε).aemeasurable hφ.1.aestronglyMeasurable
  have hRHS : ∫ z, signAverage φ z ∂(Measure.pi ν)
      = (Fintype.card (Fin N → Bool) : ℝ)⁻¹ *
        ∑ ε : Fin N → Bool, ∫ z, φ (signFlip ε z) ∂(Measure.pi ν) := by
    unfold signAverage
    rw [integral_const_mul, integral_finset_sum _ fun ε _ => hintcomp ε]
  rw [pi_symmetrize_eq ν, integral_smul_measure,
    integral_finset_sum_measure (fun ε _ => hintmap ε),
    Finset.sum_congr rfl fun ε _ => heach ε, hRHS]
  have hcard : (Fintype.card (Fin N → Bool) : ℝ) = 2 ^ N := by
    simp [Fintype.card_fun]
  rw [hcard, smul_eq_mul]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow]
  norm_num

/-! ### Normalized restrictions of Lebesgue measure -/

/-- Lebesgue measure normalized on a set of finite positive measure. -/
private noncomputable def unifOn (s : Set ℝ) : Measure ℝ := (volume s)⁻¹ • volume.restrict s

private lemma unifOn_apply (s : Set ℝ) {t : Set ℝ} (ht : MeasurableSet t) :
    unifOn s t = (volume s)⁻¹ * volume (t ∩ s) := by
  simp only [unifOn, Measure.smul_apply, Measure.restrict_apply ht, smul_eq_mul]

private lemma isProbabilityMeasure_unifOn {s : Set ℝ} (h0 : volume s ≠ 0)
    (h1 : volume s ≠ ⊤) : IsProbabilityMeasure (unifOn s) := by
  constructor
  rw [unifOn_apply s MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel h0 h1

private lemma unifOn_singleton (s : Set ℝ) (t : ℝ) : unifOn s {t} = 0 := by
  rw [unifOn_apply s (measurableSet_singleton t)]
  have : volume ({t} ∩ s) = 0 :=
    measure_mono_null Set.inter_subset_left (measure_singleton t)
  rw [this, mul_zero]

private lemma pi_unifOn {N : ℕ} (s : Fin N → Set ℝ)
    (h0 : ∀ i, volume (s i) ≠ 0) (h1 : ∀ i, volume (s i) ≠ ⊤) :
    Measure.pi (fun i => unifOn (s i))
      = (∏ i, (volume (s i))⁻¹) • volume.restrict (Set.univ.pi s) := by
  haveI : ∀ i, IsProbabilityMeasure (unifOn (s i)) := fun i =>
    isProbabilityMeasure_unifOn (h0 i) (h1 i)
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (MeasurableSet.univ_pi ht), ← Set.pi_inter_distrib, volume_pi,
    Measure.pi_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (unifOn_apply (s i) (ht i)).symm

/-! ### The sign-average is the level, almost everywhere -/

/-- The calibration hypothesis, read on boxes: the average of the sign-average of `φ` over any
box of finite positive side lengths is `α`. -/
private lemma setIntegral_signAverage {N : ℕ} {α : ℝ} {φ : (Fin N → ℝ) → ℝ}
    (hφ : IsCriticalFn φ)
    (hnull : ∀ D : Fin N → Measure ℝ, (∀ i, IsProbabilityMeasure (D i)) →
      (∀ i, ∀ t : ℝ, D i {t} = 0) → (∀ i, (D i).map (fun t : ℝ => -t) = D i) →
      ∫ z, φ z ∂(Measure.pi D) = α)
    (s : Fin N → Set ℝ)
    (h0 : ∀ i, volume (s i) ≠ 0) (h1 : ∀ i, volume (s i) ≠ ⊤) :
    ∫ z in Set.univ.pi s, signAverage φ z = α * (∏ i, volume (s i)).toReal := by
  haveI hprob : ∀ i, IsProbabilityMeasure (unifOn (s i)) := fun i =>
    isProbabilityMeasure_unifOn (h0 i) (h1 i)
  have hcal := hnull (fun i => symmetrize (unifOn (s i))) (fun i => inferInstance)
    (fun i t => symmetrize_singleton _ (unifOn_singleton (s i)) t)
    (fun i => symmetrize_map_neg _)
  rw [integral_pi_symmetrize hφ (fun i => unifOn (s i)), pi_unifOn s h0 h1,
    integral_smul_measure] at hcal
  have hprodne : (∏ i, volume (s i)) ≠ ⊤ :=
    (ENNReal.prod_lt_top fun i _ => lt_of_le_of_ne le_top (h1 i)).ne
  have hprod0 : (∏ i, volume (s i)) ≠ 0 := by
    simp only [ne_eq, Finset.prod_eq_zero_iff, not_exists]
    exact fun i hi => h0 i hi.2
  have hinvprod : (∏ i, (volume (s i))⁻¹) = (∏ i, volume (s i))⁻¹ :=
    (ENNReal.prod_inv_distrib fun i _ j _ _ => Or.inl (h0 i)).symm
  have hinv : ((∏ i, (volume (s i))⁻¹).toReal) = ((∏ i, volume (s i)).toReal)⁻¹ := by
    rw [hinvprod, ENNReal.toReal_inv]
  have hposR : (0 : ℝ) < (∏ i, volume (s i)).toReal :=
    ENNReal.toReal_pos hprod0 hprodne
  rw [hinv, smul_eq_mul] at hcal
  field_simp at hcal
  linarith [hcal]

/-- **The repaired sign-average lemma.** Under the amended (independent, continuous, symmetric)
calibration hypothesis, the sign-average of `φ` equals the level `α` Lebesgue-almost
everywhere. This is exactly the step that fails for the printed statement, where the conclusion
is claimed `Q`-a.e. for an arbitrary sign-change-invariant `Q`; see
`not_integral_eq_of_sign_invariant`. -/
private lemma signAverage_ae_eq_const {N : ℕ} {α : ℝ} {φ : (Fin N → ℝ) → ℝ}
    (hφ : IsCriticalFn φ)
    (hnull : ∀ D : Fin N → Measure ℝ, (∀ i, IsProbabilityMeasure (D i)) →
      (∀ i, ∀ t : ℝ, D i {t} = 0) → (∀ i, (D i).map (fun t : ℝ => -t) = D i) →
      ∫ z, φ z ∂(Measure.pi D) = α) :
    signAverage φ =ᵐ[volume] fun _ => α := by
  classical
  -- The level is nonnegative: it is the mean of a nonnegative function.
  have hIcc0 : volume (Set.Icc (-(1 : ℝ)) 1) ≠ 0 := by
    rw [Real.volume_Icc]; norm_num
  have hIcctop : volume (Set.Icc (-(1 : ℝ)) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hα0 : 0 ≤ α := by
    haveI : IsProbabilityMeasure (unifOn (Set.Icc (-(1 : ℝ)) 1)) :=
      isProbabilityMeasure_unifOn hIcc0 hIcctop
    have h := hnull (fun _ => symmetrize (unifOn (Set.Icc (-(1 : ℝ)) 1)))
      (fun _ => inferInstance)
      (fun _ t => symmetrize_singleton _ (unifOn_singleton _) t)
      (fun _ => symmetrize_map_neg _)
    rw [← h]
    exact integral_nonneg fun z => (hφ.2 z).1
  -- The box identity.
  have hbox := setIntegral_signAverage hφ hnull
  set g : (Fin N → ℝ) → ℝ := signAverage φ with hgdef
  have hgcrit : IsCriticalFn g := isCriticalFn_signAverage hφ
  -- The `N = 0` case is degenerate: the sample space is a single point.
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hz : ∀ z w : Fin 0 → ℝ, z = w := fun z w => funext fun i => i.elim0
    have h := hbox (fun _ => Set.Icc (-(1 : ℝ)) 1) (fun i => i.elim0) (fun i => i.elim0)
    have hpiuniv : (Set.univ.pi fun _ : Fin 0 => Set.Icc (-(1 : ℝ)) 1) = Set.univ := by
      ext w; simp
    rw [hpiuniv, Measure.restrict_univ] at h
    simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.toReal_one, mul_one] at h
    refine Filter.Eventually.of_forall fun z => ?_
    have huniv : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
      rw [volume_pi]; simp
    have hconst : ∀ w : Fin 0 → ℝ, g w = g z := fun w => by rw [hz w z]
    rw [integral_congr_ae (Filter.Eventually.of_forall hconst), integral_const,
      measureReal_def, huniv] at h
    simpa using h
  -- The main case. Fix a coordinate to carry the constant `α`.
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  obtain ⟨i₀⟩ := (inferInstance : Nonempty (Fin N))
  set c : Fin N → ℝ≥0∞ := fun i => if i = i₀ then ENNReal.ofReal α else 1 with hcdef
  have hcprod : ∏ i, c i = ENNReal.ofReal α := by
    rw [hcdef]; simp
  have hcne : ∀ i, c i ≠ ⊤ := by
    intro i; rw [hcdef]; by_cases h : i = i₀ <;> simp [h]
  -- The core computation: the `ofReal`-lintegral of `g` over a box.
  have hcore : ∀ s : Fin N → Set ℝ, (∀ i, MeasurableSet (s i)) → (∀ i, volume (s i) ≠ ⊤) →
      ∫⁻ z in Set.univ.pi s, ENNReal.ofReal (g z)
        = ENNReal.ofReal α * ∏ i, volume (s i) := by
    intro s hs h1
    by_cases h0 : ∃ i, volume (s i) = 0
    · obtain ⟨i, hi⟩ := h0
      have hzero : (∏ i, volume (s i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hi
      have hnull' : volume (Set.univ.pi s) = 0 := by
        rw [volume_pi, Measure.pi_pi]; exact hzero
      rw [setLIntegral_measure_zero _ _ hnull', hzero, mul_zero]
    · push_neg at h0
      have hprodne : (∏ i, volume (s i)) ≠ ⊤ :=
        (ENNReal.prod_lt_top fun i _ => lt_of_le_of_ne le_top (h1 i)).ne
      have hvol : volume (Set.univ.pi s) = ∏ i, volume (s i) := by
        rw [volume_pi, Measure.pi_pi]
      haveI : IsFiniteMeasure (volume.restrict (Set.univ.pi s)) := by
        constructor
        rw [Measure.restrict_apply_univ, hvol]
        exact lt_of_le_of_ne le_top hprodne
      have hint : Integrable g (volume.restrict (Set.univ.pi s)) :=
        integrable_of_isCriticalFn hgcrit _
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun z => (hgcrit.2 z).1),
        hbox s h0 h1, ENNReal.ofReal_mul hα0, ENNReal.ofReal_toReal hprodne]
  -- On each cube the two measures agree, because both are the same product measure.
  set cube : ℕ → Set (Fin N → ℝ) :=
    fun R => Set.univ.pi (fun _ : Fin N => Set.Icc (-(R : ℝ)) R) with hcube
  have hcubeMeas : ∀ R, MeasurableSet (cube R) := fun R =>
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hicc : ∀ R : ℕ, volume (Set.Icc (-(R : ℝ)) R) ≠ ⊤ := by
    intro R; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hmeasEq : ∀ R : ℕ,
      (volume.withDensity fun z => ENNReal.ofReal (g z)).restrict (cube R)
        = ((ENNReal.ofReal α) • (volume : Measure (Fin N → ℝ))).restrict (cube R) := by
    intro R
    haveI hfin : ∀ i : Fin N, IsFiniteMeasure
        ((c i) • (volume.restrict (Set.Icc (-(R : ℝ)) R))) := by
      intro i
      constructor
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top (hcne i))
        (lt_of_le_of_ne le_top (hicc R))
    have key : ∀ ρ : Measure (Fin N → ℝ),
        (∀ t : Fin N → Set ℝ, (∀ i, MeasurableSet (t i)) →
          ρ (Set.univ.pi t) = ENNReal.ofReal α * ∏ i, volume (t i ∩ Set.Icc (-(R : ℝ)) R)) →
        Measure.pi (fun i => (c i) • (volume.restrict (Set.Icc (-(R : ℝ)) R))) = ρ := by
      intro ρ hρ
      refine Measure.pi_eq fun t ht => ?_
      rw [hρ t ht]
      have : ∀ i, ((c i) • (volume.restrict (Set.Icc (-(R : ℝ)) R))) (t i)
          = c i * volume (t i ∩ Set.Icc (-(R : ℝ)) R) := by
        intro i
        rw [Measure.smul_apply, Measure.restrict_apply (ht i), smul_eq_mul]
      rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_mul_distrib, hcprod]
    have h1 := key ((volume.withDensity fun z => ENNReal.ofReal (g z)).restrict (cube R))
      (fun t ht => by
        rw [Measure.restrict_apply (MeasurableSet.univ_pi ht), hcube, ← Set.pi_inter_distrib,
          withDensity_apply _ (MeasurableSet.univ_pi fun i => (ht i).inter measurableSet_Icc)]
        exact hcore _ (fun i => (ht i).inter measurableSet_Icc)
          (fun i => ne_top_of_le_ne_top (hicc R) (measure_mono Set.inter_subset_right)))
    have h2 := key (((ENNReal.ofReal α) • (volume : Measure (Fin N → ℝ))).restrict (cube R))
      (fun t ht => by
        rw [Measure.restrict_apply (MeasurableSet.univ_pi ht), hcube, ← Set.pi_inter_distrib,
          Measure.smul_apply, smul_eq_mul, volume_pi, Measure.pi_pi])
    rw [← h1, h2]
  -- Hence `g = α` almost everywhere on each cube, hence almost everywhere.
  have haeR : ∀ R : ℕ, g =ᵐ[volume.restrict (cube R)] fun _ => α := by
    intro R
    have h1 := hmeasEq R
    rw [restrict_withDensity (hcubeMeas R), Measure.restrict_smul,
      ← withDensity_const] at h1
    haveI : IsFiniteMeasure (volume.restrict (cube R)) := by
      constructor
      rw [Measure.restrict_apply_univ, hcube, volume_pi, Measure.pi_pi]
      exact ENNReal.prod_lt_top fun i _ => lt_of_le_of_ne le_top (hicc R)
    have hfin : ∫⁻ z, ENNReal.ofReal (g z) ∂(volume.restrict (cube R)) ≠ ⊤ := by
      have hle : ∫⁻ z, ENNReal.ofReal (g z) ∂(volume.restrict (cube R))
          ≤ ∫⁻ _z, (1 : ℝ≥0∞) ∂(volume.restrict (cube R)) :=
        lintegral_mono fun z => ENNReal.ofReal_le_one.2 (hgcrit.2 z).2
      rw [lintegral_one] at hle
      exact ne_of_lt (lt_of_le_of_lt hle (measure_lt_top _ _))
    have h2 := (withDensity_eq_iff
      (hgcrit.1.ennreal_ofReal.aemeasurable) aemeasurable_const hfin).1 h1
    filter_upwards [h2] with z hz
    exact (ENNReal.ofReal_eq_ofReal_iff (hgcrit.2 z).1 hα0).1 hz
  have hBm : MeasurableSet {z : Fin N → ℝ | ¬ g z = α} :=
    (hgcrit.1 (measurableSet_singleton α)).compl
  have huniv : (Set.univ : Set (Fin N → ℝ)) = ⋃ R : ℕ, cube R := by
    ext z
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ i, |z i| ≤ M := Finite.exists_le fun i => |z i|
    obtain ⟨R, hR⟩ := exists_nat_ge M
    refine ⟨R, Set.mem_univ_pi.2 fun i => ?_⟩
    exact Set.mem_Icc.2 (abs_le.1 ((hM i).trans hR))
  rw [Filter.EventuallyEq, ae_iff]
  have hsplit : {z : Fin N → ℝ | ¬ g z = α}
      = ⋃ R : ℕ, ({z : Fin N → ℝ | ¬ g z = α} ∩ cube R) := by
    rw [← Set.inter_iUnion, ← huniv, Set.inter_univ]
  rw [hsplit]
  refine measure_iUnion_null fun R => ?_
  have := haeR R
  rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply hBm] at this
  exact this

/-- **Refutation of the sign-change identity as transcribed.** The identity below is *not*
a theorem for an arbitrary permutation-symmetric critical function and an arbitrary
sign-change-invariant law.

Counterexample: `N = 1`, `α = 0`, `φ = 1_{\{0\}}`, `Q = δ₀`. Then `φ` is a critical function,
it is (vacuously) symmetric in its single argument, every i.i.d. sample from a continuous
symmetric `D` gives it mean `D{0} = 0 = α`, and `δ₀` is invariant under both coordinatewise
sign changes because `-0 = 0`; but `∫ φ dQ = φ 0 = 1 ≠ 0 = α`.

The failure is not confined to the degenerate point `0`. Taking `α = 1/2`,
`φ = 1/2 + (1/2)·1_{\{t₀, -t₀\}}` and `Q = ½ δ_{t₀} + ½ δ_{-t₀}` with `t₀ > 0` gives a
counterexample with no zeros and no ties, so adding "`Q` charges no zeros and no ties" does
not repair it. What the calibration hypothesis really delivers is that the sign-average
equals `α` off a set null for every *non-atomic* law; a sign-change-invariant `Q` may live
on that set.

Since `N = 1`, the i.i.d. calibration class used here coincides with the larger
independent-non-identically-distributed class of the amended `integral_eq_of_sign_invariant`
below: the counterexample refutes that form too, absent the amendment `Q ≪ volume`. -/
theorem not_integral_eq_of_sign_invariant :
    ¬ ∀ (N : ℕ) (α : ℝ) (φ : (Fin N → ℝ) → ℝ), IsCriticalFn φ →
        (∀ (σ : Equiv.Perm (Fin N)) (z : Fin N → ℝ), φ (z ∘ σ) = φ z) →
        (∀ D : Measure ℝ, IsProbabilityMeasure D → (∀ t : ℝ, D {t} = 0) →
          D.map (fun t => -t) = D →
          ∫ z, φ z ∂(Measure.pi fun _ : Fin N => D) = α) →
        ∀ Q : Measure (Fin N → ℝ), IsProbabilityMeasure Q →
          (∀ ε : Fin N → Bool, Q.map (signFlip ε) = Q) →
          ∫ z, φ z ∂Q = α := by
  intro h
  classical
  have hSmeas : MeasurableSet ({0} : Set (Fin 1 → ℝ)) := measurableSet_singleton _
  have hmeas : Measurable (Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ)) :=
    measurable_const.indicator hSmeas
  have hcrit : IsCriticalFn (Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ)) := by
    refine ⟨hmeas, fun z => ?_⟩
    by_cases hz : z ∈ ({0} : Set (Fin 1 → ℝ))
    · rw [Set.indicator_of_mem hz]; norm_num
    · rw [Set.indicator_of_notMem hz]; norm_num
  have hsym : ∀ (σ : Equiv.Perm (Fin 1)) (z : Fin 1 → ℝ),
      Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ) (z ∘ σ)
        = Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ) z := by
    intro σ z
    have hz : z ∘ σ = z := funext fun i => congrArg z (Subsingleton.elim _ _)
    rw [hz]
  have hsingleton : ({0} : Set (Fin 1 → ℝ)) = Set.univ.pi fun _ => ({0} : Set ℝ) := by
    ext z; simp [funext_iff]
  have hnull : ∀ D : Measure ℝ, IsProbabilityMeasure D → (∀ t : ℝ, D {t} = 0) →
      D.map (fun t => -t) = D →
      ∫ z, Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ) z
        ∂(Measure.pi fun _ : Fin 1 => D) = 0 := by
    intro D hD hatom _
    haveI := hD
    have hzero : (Measure.pi fun _ : Fin 1 => D) {(0 : Fin 1 → ℝ)} = 0 := by
      rw [hsingleton, Measure.pi_pi]
      simp [hatom]
    rw [integral_indicator_one hSmeas]
    simp [measureReal_def, hzero]
  have hQinv : ∀ ε : Fin 1 → Bool,
      (Measure.dirac (0 : Fin 1 → ℝ)).map (signFlip ε) = Measure.dirac 0 := by
    intro ε
    rw [Measure.map_dirac' (measurable_signFlip ε)]
    congr 1
    funext i
    by_cases hε : ε i <;> simp [signFlip, hε]
  have hcontra := h 1 0 _ hcrit hsym hnull (Measure.dirac 0) inferInstance hQinv
  rw [integral_dirac' _ _ hmeas.stronglyMeasurable,
    Set.indicator_of_mem (Set.mem_singleton _)] at hcontra
  norm_num at hcontra

/-- **A test calibrated on continuous symmetric distributions keeps its level under any
sign-change-invariant law absolutely continuous with respect to Lebesgue measure.**

This is the printed Lemma 6.10.1 with the two documented amendments described in the module
header: the joint law `Q` is assumed absolutely continuous (this is *forced*: see
`not_integral_eq_of_sign_invariant` for the atomic counterexamples), and the calibration
hypothesis is imposed over independent — not necessarily identically distributed — continuous
symmetric samples. Under amendment 2 the permutation-symmetry hypothesis of the printed
statement is not needed.

If a critical function has mean `α` under every independent sample from continuous
distributions symmetric about the origin, then it has mean `α` under every absolutely
continuous joint law invariant under the `2^N` coordinatewise sign changes — in particular
without assuming the coordinates independent or identically distributed. -/
theorem integral_eq_of_sign_invariant {N : ℕ} {α : ℝ} {φ : (Fin N → ℝ) → ℝ}
    -- USER-INPUT: `φ` is a critical function
    (hφ : IsCriticalFn φ)
    -- USER-INPUT (AMENDED): `φ` has mean `α` under every independent sample from continuous
    -- distributions symmetric about the origin
    (hnull : ∀ D : Fin N → Measure ℝ, (∀ i, IsProbabilityMeasure (D i)) →
      (∀ i, ∀ t : ℝ, D i {t} = 0) → (∀ i, (D i).map (fun t : ℝ => -t) = D i) →
      ∫ z, φ z ∂(Measure.pi D) = α)
    {Q : Measure (Fin N → ℝ)} [IsProbabilityMeasure Q]
    -- USER-INPUT: the joint law is unchanged by all `2^N` coordinatewise sign changes
    (hQ : ∀ ε : Fin N → Bool, Q.map (signFlip ε) = Q)
    -- AMENDMENT (forced): the joint law charges no Lebesgue-null set
    (hQac : Q ≪ volume) :
    ∫ z, φ z ∂Q = α := by
  have hφmeas : Measurable φ := hφ.1
  have hInt : Integrable φ Q := integrable_of_isCriticalFn hφ Q
  have hIntg : ∀ ε : Fin N → Bool, Integrable (fun z => φ (signFlip ε z)) Q := fun ε =>
    integrable_of_isCriticalFn ⟨hφmeas.comp (measurable_signFlip ε), fun z => hφ.2 _⟩ Q
  -- each sign change is `Q`-measure preserving, so it leaves the integral of `φ` unchanged.
  have hEach : ∀ ε : Fin N → Bool, ∫ z, φ (signFlip ε z) ∂Q = ∫ z, φ z ∂Q := by
    intro ε
    have h : ∫ y, φ y ∂(Q.map (signFlip ε)) = ∫ z, φ (signFlip ε z) ∂Q :=
      integral_map (measurable_signFlip ε).aemeasurable hφmeas.aestronglyMeasurable
    rw [hQ ε] at h; exact h.symm
  -- the average over the `2^N` patterns has the same `Q`-integral as `φ` itself.
  set M : ℝ := (Fintype.card (Fin N → Bool) : ℝ) with hMdef
  have hMne : M ≠ 0 := by
    rw [hMdef]; exact_mod_cast Fintype.card_ne_zero
  have hAvg : ∫ z, signAverage φ z ∂Q = ∫ z, φ z ∂Q := by
    unfold signAverage
    rw [integral_const_mul, integral_finset_sum Finset.univ (fun ε _ => hIntg ε)]
    rw [Finset.sum_congr rfl (fun ε _ => hEach ε), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hMdef, ← mul_assoc, inv_mul_cancel₀ hMne, one_mul]
  -- the completeness step makes that average `α` off a Lebesgue-null, hence `Q`-null, set.
  have hConst : ∫ z, signAverage φ z ∂Q = α := by
    rw [integral_congr_ae ((signAverage_ae_eq_const hφ hnull).filter_mono hQac.ae_le)]
    simp
  rw [← hAvg, hConst]

end StatLean.HypothesisTesting
