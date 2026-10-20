module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

/-!
# Empirical process — definition

Given i.i.d. data $X_1, \dots, X_n$ with common law $P$ on a sample space
$\Omega'$ and a function $f : \Omega' \to \mathbb{R}$, the *empirical process*
indexed by $f$ is the centered sample average
$$ X_f \;=\; \frac{1}{n} \sum_{i=1}^{n} f(X_i) \;-\; \mathbb{E}_P f. $$
This file defines `empiricalProcess` and proves its deterministic pointwise
algebra: linearity, invisibility of constants, the oscillation bounds
$|X_f| \le 2\|f\|_\infty$ and $|X_f - X_g| \le 2\|f-g\|_\infty$, and
measurability. These pointwise facts are the engines for the WLOG reductions
and the full-supremum ("no countability hypothesis") honesty argument in the
Lipschitz law of large numbers (HDP Theorem 8.2.3).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, Definition 8.2.5, Eq. (8.23).

**Proof formalization notes.** The index is a plain function argument
`f : Ω' → ℝ` (no function-class carrier at definition level); the data enter
as a family `X : Fin n → Ω → Ω'` on an abstract probability space `Ω`, and
i.i.d.-ness is a *hypothesis of the theorems*, never of the definition. Edge
behavior: for `n = 0` the sample term is `(0 : ℝ)⁻¹ * 0 = 0`, so
`X_f = −E_P f`; for non-integrable `f` the Bochner integral is Mathlib's junk
`0` and `X_f` degenerates to the raw sample average. This
`ConcentrationInequalities` empirical process is the *unscaled deviation*; it
deliberately coexists with the √n-scaled, realized-sample
`StatLean.AsymptoticStatistics.EmpiricalProcess.empiricalProcess` (vdV
convention) — the two serve different reference texts and neither imports the
other (cross-area concept-layer imports are forbidden by the project charter).

**Bibliographic comments.** Empirical processes as random functionals indexed
by function classes go back to the Glivenko–Cantelli theorem (1933) and were
systematized by R. M. Dudley, "Central limit theorems for empirical measures,"
*Ann. Probab.* 6 (1978), 899–929; the modern treatment is van der
Vaart–Wellner, *Weak Convergence and Empirical Processes*, Springer 1996.
-/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {P : Measure Ω'} {n : ℕ} {X : Fin n → Ω → Ω'} {f g : Ω' → ℝ}

/-- **Empirical process** (HDP §8.2, Definition 8.2.5, Eq. (8.23)):
`X_f(ω) = n⁻¹ ∑ᵢ f(Xᵢ(ω)) − ∫ f dP`, the centered sample average of `f`
along the data `X` with population law `P`. Edge behavior: `n = 0` gives the
pure population term `−∫ f dP` (the `(0 : ℝ)⁻¹` junk is multiplied by an
empty sum); non-integrable `f` makes the population term Mathlib's junk `0`. -/
noncomputable def empiricalProcess (P : Measure Ω') (n : ℕ)
    (X : Fin n → Ω → Ω') (f : Ω' → ℝ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (X i ω) - ∫ x, f x ∂P

@[simp] theorem empiricalProcess_zero_fun (P : Measure Ω') (n : ℕ)
    (X : Fin n → Ω → Ω') :
    empiricalProcess P n X (fun _ => 0) = fun _ => 0 := by
  funext ω
  simp [empiricalProcess]

/-- Constants are invisible to the empirical process (HDP §8.2): the sample
average and the population mean of a constant cancel. -/
theorem empiricalProcess_const [NeZero n] [IsProbabilityMeasure P] (c : ℝ) :
    empiricalProcess P n X (fun _ => c) = fun _ => 0 := by
  funext ω
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp [empiricalProcess, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, inv_mul_cancel_left₀ hn]

/-- Scalar homogeneity of the empirical process (engine for the `L = 1`
reduction in Theorem 8.2.3). -/
theorem empiricalProcess_const_mul (c : ℝ)
    -- LEAN-ONLY: integrability so the Bochner integral is genuinely linear;
    -- automatic for the bounded classes of HDP §8.2.
    (hf : Integrable f P) (ω : Ω) :
    empiricalProcess P n X (fun x => c * f x) ω
      = c * empiricalProcess P n X f ω := by
  simp only [empiricalProcess, integral_const_mul, ← Finset.mul_sum]
  ring

/-- `X_{f−g} = X_f − X_g` pointwise (HDP §8.2, p. 230). -/
theorem empiricalProcess_sub
    -- LEAN-ONLY: integrability so `∫ (f − g) = ∫ f − ∫ g`; automatic for the
    -- bounded classes of HDP §8.2.
    (hf : Integrable f P) (hg : Integrable g P) (ω : Ω) :
    empiricalProcess P n X (f - g) ω
      = empiricalProcess P n X f ω - empiricalProcess P n X g ω := by
  simp only [empiricalProcess, Pi.sub_apply, Finset.sum_sub_distrib,
    integral_sub hf hg, mul_sub]
  ring

/-- Translation invariance `X_{f+c} = X_f` (HDP §8.2, p. 230; engine for the
`[0,1]`-valued reduction in Theorem 8.2.3). -/
theorem empiricalProcess_add_const [NeZero n] [IsProbabilityMeasure P]
    -- LEAN-ONLY: integrability so `∫ (f + c) = ∫ f + c`.
    (hf : Integrable f P) (c : ℝ) :
    empiricalProcess P n X (fun x => f x + c) = empiricalProcess P n X f := by
  funext ω
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h1 : ∫ x, (f x + c) ∂P = (∫ x, f x ∂P) + c := by
    rw [integral_add hf (integrable_const c), integral_const]
    simp
  have h2 : (∑ i, (f (X i ω) + c)) = (∑ i, f (X i ω)) + (n : ℝ) * c := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  simp only [empiricalProcess, h1, h2, mul_add, inv_mul_cancel_left₀ hn]
  ring

/-- Uniform bound `|X_f| ≤ 2‖f‖_∞` (HDP §8.2): one factor from the sample
average, one from the population mean. Holds for every `n` (including `0`). -/
theorem abs_empiricalProcess_le [IsProbabilityMeasure P] {B : ℝ}
    -- USER-INPUT: uniform bound on the class member; HDP §8.2 (Boolean /
    -- `[0,1]`-valued classes have `B = 1`).
    (hB : ∀ x, |f x| ≤ B) (ω : Ω) :
    |empiricalProcess P n X f ω| ≤ 2 * B := by
  -- The sample space is nonempty because `P` is a probability measure.
  have hΩ' : Nonempty Ω' := by
    by_contra h
    have huniv : (Set.univ : Set Ω') = ∅ :=
      Set.univ_eq_empty_iff.mpr (not_nonempty_iff.mp h)
    have : (1 : ℝ≥0∞) = 0 := by
      rw [← measure_univ (μ := P), huniv, measure_empty]
    exact one_ne_zero this
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (Classical.arbitrary Ω'))
  -- Sample-average term.
  have hsum : |(n : ℝ)⁻¹ * ∑ i, f (X i ω)| ≤ B := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using hB0
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have h1 : |∑ i, f (X i ω)| ≤ (n : ℝ) * B := by
        calc |∑ i, f (X i ω)| ≤ ∑ i, |f (X i ω)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hB _
          _ = (n : ℝ) * B := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
      calc |(n : ℝ)⁻¹ * ∑ i, f (X i ω)|
          = (n : ℝ)⁻¹ * |∑ i, f (X i ω)| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hn'.le)]
        _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * B) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn'.le)
        _ = B := inv_mul_cancel_left₀ (ne_of_gt hn') B
  -- Population term.
  have hint : |∫ x, f x ∂P| ≤ B := by
    have h := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := B)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hB x)
    simpa [Real.norm_eq_abs, measure_univ, ENNReal.toReal_one, mul_one]
      using h
  calc |empiricalProcess P n X f ω|
      = |(n : ℝ)⁻¹ * ∑ i, f (X i ω) - ∫ x, f x ∂P| := rfl
    _ ≤ |(n : ℝ)⁻¹ * ∑ i, f (X i ω)| + |∫ x, f x ∂P| := by
        simpa [Real.norm_eq_abs] using
          norm_sub_le ((n : ℝ)⁻¹ * ∑ i, f (X i ω)) (∫ x, f x ∂P)
    _ ≤ B + B := add_le_add hsum hint
    _ = 2 * B := (two_mul B).symm

/-- Pointwise oscillation bound `|X_f − X_g| ≤ 2‖f−g‖_∞` (HDP §8.2): the
deterministic engine of the full-supremum honesty argument — the empirical
process is `2`-Lipschitz in `f` for the sup metric, uniformly in `ω`. -/
theorem abs_empiricalProcess_sub_le [IsProbabilityMeasure P] {δ : ℝ}
    -- LEAN-ONLY: integrability of the class members (bounded ⇒ integrable in
    -- the book's setting).
    (hf : Integrable f P) (hg : Integrable g P)
    -- USER-INPUT: sup-distance bound between class members; HDP §8.2.
    (hδ : ∀ x, |f x - g x| ≤ δ) (ω : Ω) :
    |empiricalProcess P n X f ω - empiricalProcess P n X g ω| ≤ 2 * δ := by
  rw [← empiricalProcess_sub hf hg ω]
  exact abs_empiricalProcess_le (f := f - g) (fun x => hδ x) ω

/-- Measurability of `ω ↦ X_f(ω)` (LEAN-ONLY regularity). -/
theorem measurable_empiricalProcess
    (hf : Measurable f) (hX : ∀ i, Measurable (X i)) :
    Measurable (empiricalProcess P n X f) := by
  unfold empiricalProcess
  exact ((Finset.measurable_sum Finset.univ fun i _ =>
    hf.comp (hX i)).const_mul _).sub measurable_const

end StatLean.ConcentrationInequalities
