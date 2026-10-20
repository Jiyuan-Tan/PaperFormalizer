module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
public import StatLean.AsymptoticStatistics.ForMathlib.L2
public import StatLean.AsymptoticStatistics.ForMathlib.RandomRadiusEntropy
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Changing envelopes and their Lindeberg calculus

This file develops the population/envelope estimates used in the
finite-dimensional-convergence part of van der Vaart Theorem 19.28. It does
not choose an encoding of an empirical sample or of a triangular array.

The theorem `envelope_lindeberg_vector` turns a changing-envelope Lindeberg
condition into the centered Euclidean-vector tail condition for a row-iid
triangular Lindeberg theorem.

Reference: van der Vaart, *Asymptotic Statistics*, Theorem 19.28, p.282.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open Filter MeasureTheory Topology
open scoped ENNReal

variable {Ω T : Type*} [MeasurableSpace Ω]

/-- `Φ` is a changing envelope for the row classes
`{f n t : t ∈ T}` when it dominates every member pointwise.

Constitutive (vdV Theorem 19.28 p.282): the displayed Lindeberg condition is
imposed on an envelope `Fₙ` of the entire row class.  Edge behavior: if `T` is
empty the domination clause is vacuous; no artificial nonemptiness assumption
is added. -/
def ChangingEnvelope (f : ℕ → T → Ω → ℝ) (Φ : ℕ → Ω → ℝ) : Prop :=
  ∀ n t x, |f n t x| ≤ Φ n x

/-- The changing-envelope Lindeberg condition preceding vdV Theorem 19.28.

It records both uniform boundedness of the second moments `P Φₙ²` and, for
every `ε > 0`, convergence to zero of
`P[Φₙ² 1{|Φₙ| > ε√n}]`.  The nonnegative integrals are `ℝ≥0∞`-valued, so a
non-integrable envelope is represented honestly by `∞`.  Edge behavior at
`n = 0` uses Lean's `√0 = 0`; the asymptotic clause is unaffected by this
single row. -/
def ChangingLindeberg (P : Measure Ω) (Φ : ℕ → Ω → ℝ) : Prop :=
  (∃ K : ℝ≥0∞, K < ∞ ∧
      ∀ n, (∫⁻ x, ENNReal.ofReal ((Φ n x) ^ 2) ∂P) ≤ K) ∧
    ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ => ∫⁻ x in {x | ε * Real.sqrt n < |Φ n x|},
          ENNReal.ofReal ((Φ n x) ^ 2) ∂P)
        atTop (nhds 0)

/-- The changing-Lindeberg squared-envelope tail at scale `ε`.

This is the exact extended-valued tail appearing in `ChangingLindeberg`; no
measurability or finiteness is imposed by the definition. -/
noncomputable def changingLindebergTail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Φ : ℕ → Ω → ℝ) (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | ε * Real.sqrt n < |Φ n x|},
    ENNReal.ofReal ((Φ n x) ^ 2) ∂P

/-- Choose a positive antitone null scale along which the
changing-Lindeberg squared-envelope tail still converges to zero. -/
theorem ChangingLindeberg.exists_pos_antitone_tail_scale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Φ : ℕ → Ω → ℝ} (hLin : ChangingLindeberg P Φ) :
    ∃ ε : ℕ → ℝ,
      (∀ n, 0 < ε n) ∧
      Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun n => changingLindebergTail P Φ n (ε n))
        atTop (𝓝 0) := by
  apply AsymptoticStatistics.ForMathlib.exists_pos_antitone_scale_tendsto_zero_diagonal
  intro ε hε
  simpa [changingLindebergTail] using hLin.2 ε hε

/-- Jointly diagonalize the changing-Lindeberg tail and division by
an arbitrary extended-nonnegative null sequence. -/
theorem ChangingLindeberg.exists_pos_antitone_tail_scale_div
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Φ : ℕ → Ω → ℝ} (hLin : ChangingLindeberg P Φ)
    (b : ℕ → ℝ≥0∞) (hb : Tendsto b atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ,
      (∀ n, 0 < ε n) ∧
      Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun n => changingLindebergTail P Φ n (ε n))
        atTop (𝓝 0) ∧
      Tendsto (fun n => b n / ENNReal.ofReal (ε n))
        atTop (𝓝 0) := by
  let T : ℕ → ℝ → ℝ≥0∞ := fun n ε =>
    changingLindebergTail P Φ n ε + b n / ENNReal.ofReal ε
  have hT : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => T n ε) atTop (𝓝 0) := by
    intro ε hε
    have htail : Tendsto (fun n => changingLindebergTail P Φ n ε)
        atTop (𝓝 0) := by
      simpa [changingLindebergTail] using hLin.2 ε hε
    have hratio : Tendsto (fun n => b n / ENNReal.ofReal ε)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.div_const hb
        (Or.inr (ENNReal.ofReal_ne_zero_iff.mpr hε))
    simpa [T] using htail.add hratio
  obtain ⟨ε, hεpos, hεanti, hεzero, hdiag⟩ :=
    AsymptoticStatistics.ForMathlib.exists_pos_antitone_scale_tendsto_zero_diagonal T hT
  refine ⟨ε, hεpos, hεanti, hεzero, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hdiag
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun n => by
        exact le_add_of_nonneg_right (zero_le))
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hdiag
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun n => by
        exact le_add_of_nonneg_left (zero_le))

/-- A measurable envelope satisfying the changing Lindeberg condition belongs
to `L²(P)` in every row. -/
lemma ChangingLindeberg.envelope_memLp_two
    {P : Measure Ω} {Φ : ℕ → Ω → ℝ} (hLin : ChangingLindeberg P Φ)
    (hΦmeas : ∀ n, Measurable (Φ n)) (n : ℕ) :
    MemLp (Φ n) 2 P := by
  rw [memLp_two_iff_integrable_sq (hΦmeas n).aestronglyMeasurable]
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((hΦmeas n).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x => sq_nonneg (Φ n x))).mp
  obtain ⟨K, hK, hKbound⟩ := hLin.1
  exact ne_top_of_le_ne_top hK.ne (hKbound n)

/-- A measurable changing-Lindeberg envelope has an integrable absolute value
in every row under a population probability law. -/
lemma ChangingLindeberg.envelope_abs_integrable
    {P : Measure Ω} {Φ : ℕ → Ω → ℝ} (hLin : ChangingLindeberg P Φ)
    (hΦmeas : ∀ n, Measurable (Φ n))
    [IsProbabilityMeasure P] (n : ℕ) :
    Integrable (fun x => |Φ n x|) P := by
  simpa only [Real.norm_eq_abs] using
    (hLin.envelope_memLp_two hΦmeas n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) |>.norm

set_option linter.unusedSectionVars false in
/-- A changing envelope dominates each member of every row. -/
lemma ChangingEnvelope.member_abs_le
    {f : ℕ → T → Ω → ℝ} {Φ : ℕ → Ω → ℝ}
    (hΦ : ChangingEnvelope f Φ) (n : ℕ) (t : T) (x : Ω) :
    |f n t x| ≤ Φ n x := by
  exact hΦ n t x

set_option linter.unusedSectionVars false in
/-- A changing envelope dominates rowwise increments by `2 Φₙ`. -/
lemma ChangingEnvelope.increment_abs_le
    {f : ℕ → T → Ω → ℝ} {Φ : ℕ → Ω → ℝ}
    (hΦ : ChangingEnvelope f Φ) (n : ℕ) (s t : T) (x : Ω) :
    |f n s x - f n t x| ≤ 2 * Φ n x := by
  calc
    |f n s x - f n t x| ≤ |f n s x| + |f n t x| := abs_sub _ _
    _ ≤ Φ n x + Φ n x := add_le_add (hΦ n s x) (hΦ n t x)
    _ = 2 * Φ n x := by ring

/-- Centering one class member costs its pointwise envelope plus the population
mean of the absolute envelope.

The measurability and integrability assumptions are the analytic conditions
needed to interpret the Bochner means. -/
lemma ChangingEnvelope.centered_abs_le
    {f : ℕ → T → Ω → ℝ} {Φ : ℕ → Ω → ℝ} {P : Measure Ω}
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf : ∀ n t, Integrable (f n t) P)
    (hΦmeas : ∀ n, Measurable (Φ n))
    [IsProbabilityMeasure P]
    (n : ℕ) (t : T) (x : Ω) :
    |f n t x - ∫ y, f n t y ∂P| ≤
      Φ n x + ∫ y, |Φ n y| ∂P := by
  have hΦint := hLin.envelope_abs_integrable hΦmeas n
  calc
    |f n t x - ∫ y, f n t y ∂P| ≤ |f n t x| + |∫ y, f n t y ∂P| := abs_sub _ _
    _ ≤ Φ n x + ∫ y, |f n t y| ∂P :=
      add_le_add (hΦ n t x) (by simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (f n t))
    _ ≤ Φ n x + ∫ y, |Φ n y| ∂P :=
      add_le_add_right (integral_mono (hf n t).abs hΦint
        (fun y => (hΦ n t y).trans (le_abs_self _))) _

/-- A finite linear combination of centered coordinates is dominated by the
sum of the corresponding envelope bounds. This gives the scalar tail reduction
in the Cramér--Wold form of the triangular Lindeberg argument. -/
lemma changingEnvelope_centered_finset_sum_abs_le
    {f : ℕ → T → Ω → ℝ} {Φ : ℕ → Ω → ℝ} {P : Measure Ω}
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf : ∀ n t, Integrable (f n t) P)
    (hΦmeas : ∀ n, Measurable (Φ n))
    [IsProbabilityMeasure P]
    {k : ℕ} (a : Fin k → ℝ) (t : Fin k → T) (n : ℕ) (x : Ω) :
    |∑ j, a j * (f n (t j) x - ∫ y, f n (t j) y ∂P)| ≤
      (∑ j, |a j|) * (Φ n x + ∫ y, |Φ n y| ∂P) := by
  classical
  calc
    |∑ j, a j * (f n (t j) x - ∫ y, f n (t j) y ∂P)|
        ≤ ∑ j, |a j * (f n (t j) x - ∫ y, f n (t j) y ∂P)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |a j| * |f n (t j) x - ∫ y, f n (t j) y ∂P| := by
      simp only [abs_mul]
    _ ≤ ∑ j, |a j| * (Φ n x + ∫ y, |Φ n y| ∂P) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (hΦ.centered_abs_le hLin hf hΦmeas n (t j) x) (abs_nonneg _)
    _ = (∑ j, |a j|) * (Φ n x + ∫ y, |Φ n y| ∂P) := by
      rw [Finset.sum_mul]

/-- A square-tail Lindeberg condition survives a uniformly bounded `L¹` shift
and a fixed positive dilation. -/
lemma lindeberg_of_shifted_envelope
    {P : Measure Ω} {Φ g : ℕ → Ω → ℝ}
    (hLin : ChangingLindeberg P Φ) (hΦmeas : ∀ n, Measurable (Φ n))
    [IsProbabilityMeasure P] {A : ℝ} (hA : 0 < A)
    (hg : ∀ n x, |g n x| ≤ A * (|Φ n x| + ∫ y, |Φ n y| ∂P))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => ∫⁻ x in {x | ε * Real.sqrt n < |g n x|},
        ENNReal.ofReal ((g n x) ^ 2) ∂P) atTop (nhds 0) := by
  obtain ⟨K, hKtop, hKbound⟩ := hLin.1
  have hmean_le : ∀ n, ∫ x, |Φ n x| ∂P ≤ Real.sqrt K.toReal := by
    intro n
    have hΦL2 := hLin.envelope_memLp_two hΦmeas n
    have hsq_int := hΦL2.integrable_sq
    have hsq_le : ∫ x, (Φ n x) ^ 2 ∂P ≤ K.toReal := by
      have h := ENNReal.toReal_mono hKtop.ne (hKbound n)
      rw [← ofReal_integral_eq_lintegral_ofReal hsq_int
        (Eventually.of_forall fun x => sq_nonneg (Φ n x))] at h
      simpa [ENNReal.toReal_ofReal (AsymptoticStatistics.L2Utils.integral_sq_nonneg P (Φ n))]
        using h
    have hcs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq P
      hΦL2.norm (memLp_const (p := 2) (1 : ℝ))
    calc
      ∫ x, |Φ n x| ∂P ≤ |∫ x, |Φ n x| ∂P| := le_abs_self _
      _ ≤ Real.sqrt (∫ x, (Φ n x) ^ 2 ∂P) := by
        simpa [Real.norm_eq_abs] using hcs
      _ ≤ Real.sqrt K.toReal := Real.sqrt_le_sqrt hsq_le
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      2 * A * Real.sqrt K.toReal ≤ ε * Real.sqrt n := by
    exact ((Filter.Tendsto.const_mul_atTop hε
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop _)
  have hδ : 0 < ε / (2 * A) := div_pos hε (mul_pos two_pos hA)
  have htail := hLin.2 (ε / (2 * A)) hδ
  have hupper : ∀ᶠ n : ℕ in atTop,
      (∫⁻ x in {x | ε * Real.sqrt n < |g n x|}, ENNReal.ofReal ((g n x) ^ 2) ∂P)
        ≤ ENNReal.ofReal (4 * A ^ 2) *
          ∫⁻ x in {x | (ε / (2 * A)) * Real.sqrt n < |Φ n x|},
            ENNReal.ofReal ((Φ n x) ^ 2) ∂P := by
    filter_upwards [hthreshold] with n hn
    have hdata : ∀ x, ε * Real.sqrt n < |g n x| →
        (ε / (2 * A)) * Real.sqrt n < |Φ n x| ∧
          (g n x) ^ 2 ≤ 4 * A ^ 2 * (Φ n x) ^ 2 := by
      intro x hx
      have hm : 2 * A * (∫ y, |Φ n y| ∂P) ≤ ε * Real.sqrt n :=
        (mul_le_mul_of_nonneg_left (hmean_le n) (by positivity)).trans hn
      have hlarge := lt_of_lt_of_le hx (hg n x)
      have hΦlarge : (ε / (2 * A)) * Real.sqrt n < |Φ n x| := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (mul_pos two_pos hA)]
        nlinarith
      have hmΦ : ∫ y, |Φ n y| ∂P ≤ |Φ n x| := by
        nlinarith
      have habs : |g n x| ≤ 2 * A * |Φ n x| :=
        (hg n x).trans <| calc
          A * (|Φ n x| + ∫ y, |Φ n y| ∂P)
              ≤ A * (|Φ n x| + |Φ n x|) :=
            mul_le_mul_of_nonneg_left (add_le_add_right hmΦ _) hA.le
          _ = 2 * A * |Φ n x| := by ring
      refine ⟨hΦlarge, ?_⟩
      calc
        (g n x) ^ 2 = |g n x| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * A * |Φ n x|) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
        _ = 4 * A ^ 2 * |Φ n x| ^ 2 := by ring
        _ = 4 * A ^ 2 * (Φ n x) ^ 2 := by rw [sq_abs]
    calc
      (∫⁻ x in {x | ε * Real.sqrt n < |g n x|}, ENNReal.ofReal ((g n x) ^ 2) ∂P)
          ≤ ∫⁻ x in {x | ε * Real.sqrt n < |g n x|},
              ENNReal.ofReal (4 * A ^ 2 * (Φ n x) ^ 2) ∂P :=
        setLIntegral_mono ((measurable_const.mul ((hΦmeas n).pow_const 2)).ennreal_ofReal)
          (fun x hx => ENNReal.ofReal_le_ofReal (hdata x hx).2)
      _ = ENNReal.ofReal (4 * A ^ 2) *
          ∫⁻ x in {x | ε * Real.sqrt n < |g n x|}, ENNReal.ofReal ((Φ n x) ^ 2) ∂P := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * A ^ 2)]
      _ ≤ ENNReal.ofReal (4 * A ^ 2) *
          ∫⁻ x in {x | (ε / (2 * A)) * Real.sqrt n < |Φ n x|},
            ENNReal.ofReal ((Φ n x) ^ 2) ∂P :=
        mul_le_mul_right (lintegral_mono_set (fun x hx => (hdata x hx).1)) _
  have hscaled := ENNReal.Tendsto.const_mul htail
    (Or.inr (ENNReal.ofReal_ne_top (r := 4 * A ^ 2)))
  simp only [mul_zero] at hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscaled
    (Eventually.of_forall fun _ => zero_le) hupper

/-- The centered finite-coordinate vector cut from a changing class.

Constitutive (vdV Theorem 19.28 p.282): Proposition 2.27 is applied to
finite coordinate selections after subtracting their population means.  Edge
behavior: for `k = 0` this is the unique zero vector. -/
noncomputable def centeredCoordinateVector
    (P : Measure Ω) (f : ℕ → T → Ω → ℝ) {k : ℕ}
    (t : Fin k → T) (n : ℕ) (x : Ω) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => f n (t j) x - ∫ y, f n (t j) y ∂P)

/-- The changing-envelope condition gives the finite-linear-combination
Lindeberg tail required in a scalar Cramér--Wold reduction. -/
theorem changingLindeberg_centered_linearCombination
    {f : ℕ → T → Ω → ℝ} {Φ : ℕ → Ω → ℝ} {P : Measure Ω}
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf : ∀ n t, Measurable (f n t))
    (hΦmeas : ∀ n, Measurable (Φ n))
    [IsProbabilityMeasure P]
    {k : ℕ} (a : Fin k → ℝ) (t : Fin k → T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => ∫⁻ x in
        {x | ε * Real.sqrt n <
          |∑ j, a j * (f n (t j) x - ∫ y, f n (t j) y ∂P)|},
        ENNReal.ofReal
          ((∑ j, a j * (f n (t j) x - ∫ y, f n (t j) y ∂P)) ^ 2) ∂P)
      atTop (nhds 0) := by
  classical
  let A : ℝ := ∑ j, |a j|
  by_cases hA0 : A = 0
  · have ha : ∀ j, a j = 0 := by
      intro j
      apply abs_eq_zero.mp
      apply le_antisymm
      · calc |a j| ≤ ∑ i, |a i| := Finset.single_le_sum
              (fun i _ => abs_nonneg (a i)) (Finset.mem_univ j)
          _ = 0 := hA0
      · exact abs_nonneg _
    simp [ha]
  · have hA : 0 < A :=
      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Ne.symm hA0)
    have hfint : ∀ n s, Integrable (f n s) P := by
      intro n s
      exact (MemLp.mono' (hLin.envelope_memLp_two hΦmeas n).norm
        (hf n s).aestronglyMeasurable (Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using (hΦ n s x).trans (le_abs_self _))).integrable
            (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    apply lindeberg_of_shifted_envelope (hLin := hLin) (hΦmeas := hΦmeas)
      (A := A) hA (g := fun n x =>
        ∑ j, a j * (f n (t j) x - ∫ y, f n (t j) y ∂P)) _ ε hε
    intro n x
    exact (changingEnvelope_centered_finset_sum_abs_le hΦ hLin hfint hΦmeas a t n x).trans <|
      mul_le_mul_of_nonneg_left (add_le_add (le_abs_self (Φ n x)) le_rfl) hA.le

/-- The changing-envelope condition gives the centered Euclidean-vector
Lindeberg tail used by the row-iid triangular CLT.

Its conclusion is the finite-coordinate input to the row-iid triangular
Lindeberg theorem. -/
theorem envelope_lindeberg_vector
    {f : ℕ → T → Ω → ℝ} {Φ : ℕ → Ω → ℝ} {P : Measure Ω}
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf : ∀ n t, Measurable (f n t))
    (hΦmeas : ∀ n, Measurable (Φ n))
    [IsProbabilityMeasure P]
    {k : ℕ} (t : Fin k → T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => ∫⁻ x in
        {x | ε * Real.sqrt n < ‖centeredCoordinateVector P f t n x‖},
        ENNReal.ofReal (‖centeredCoordinateVector P f t n x‖ ^ 2) ∂P)
      atTop (nhds 0) := by
  classical
  have hfint : ∀ n s, Integrable (f n s) P := by
    intro n s
    exact (MemLp.mono' (hLin.envelope_memLp_two hΦmeas n).norm
      (hf n s).aestronglyMeasurable (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using (hΦ n s x).trans (le_abs_self _))).integrable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let A : ℝ := max 1 k
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  simpa only [abs_norm] using lindeberg_of_shifted_envelope
    (hLin := hLin) (hΦmeas := hΦmeas) (A := A) hA
    (g := fun n x => ‖centeredCoordinateVector P f t n x‖) (by
      intro n x
      have hnorm : ‖centeredCoordinateVector P f t n x‖ ≤
          ∑ j, |centeredCoordinateVector P f t n x j| := by
        rw [EuclideanSpace.norm_eq]
        apply Real.sqrt_le_iff.mpr
        refine ⟨Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
        simpa only [Real.norm_eq_abs] using
          (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
            (f := fun j => |centeredCoordinateVector P f t n x j|)
            (fun _ _ => abs_nonneg _))
      calc
        |‖centeredCoordinateVector P f t n x‖| =
            ‖centeredCoordinateVector P f t n x‖ := abs_norm _
        _ ≤ ∑ j, |centeredCoordinateVector P f t n x j| := hnorm
        _ ≤ ∑ _j : Fin k, (Φ n x + ∫ y, |Φ n y| ∂P) :=
          Finset.sum_le_sum fun j _ => by
            simpa only [centeredCoordinateVector] using
              hΦ.centered_abs_le hLin hfint hΦmeas n (t j) x
        _ = (k : ℝ) * (Φ n x + ∫ y, |Φ n y| ∂P) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ A * (|Φ n x| + ∫ y, |Φ n y| ∂P) := by
          have hB : 0 ≤ |Φ n x| + ∫ y, |Φ n y| ∂P :=
            add_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
          calc
            (k : ℝ) * (Φ n x + ∫ y, |Φ n y| ∂P)
                ≤ (k : ℝ) * (|Φ n x| + ∫ y, |Φ n y| ∂P) :=
              mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) le_rfl) (by positivity)
            _ ≤ A * (|Φ n x| + ∫ y, |Φ n y| ∂P) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hB) ε hε

end AsymptoticStatistics.EmpiricalProcess
