module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

/-!
# A Gaussian / sub-Gaussian maximal inequality

For a **finite** family `Z : ι → Ω → ℝ` of sub-Gaussian random variables, each
with proxy variance `≤ c` (`ProbabilityTheory.HasSubgaussianMGF (Z i) c μ`), the
expected maximum is controlled by `√(2 c · log(card))`:

* `expectation_iSup_le_of_subgaussian`  (one-sided)
    `∫ ω, ⨆ i, Z i ω ∂μ ≤ Real.sqrt (2 * c * Real.log (Fintype.card ι))`.
* `expectation_iSup_abs_le_of_subgaussian`  (absolute-value form, the
    building block the chaining consumer needs)
    `∫ ω, ⨆ i, |Z i ω| ∂μ ≤ Real.sqrt (2 * c * Real.log (2 * Fintype.card ι))`.

The proof is the classical **MGF / Jensen** argument (no layer-cake): for any
`λ > 0`, convexity of `exp` (Jensen, `ConvexOn.map_integral_le`) gives
`exp (λ · E[⨆ Z]) ≤ E[exp (λ · ⨆ Z)] ≤ ∑ᵢ mgf (Z i) λ ≤ card · exp (c λ²/2)`,
hence `E[⨆ Z] ≤ log(card)/λ + c λ /2`; optimising at `λ = √(2 log card / c)`
yields `√(2 c log card)`.  The absolute-value form follows by indexing the
doubled family `Z` and `-Z` over `ι ⊕ ι` (`|Z i| = max (Z i) (-Z i)`).

This is a `ForMathlib/` theorem-agnostic primitive.

**Relation to `StatLean.ConcentrationInequalities`.** The library's
concentration area proves the closely related
`StatLean.ConcentrationInequalities.expectation_max_le`
(`ConcentrationInequalities/Maximal/FiniteMaximal.lean`): a `Fin d`-indexed,
`IsSubGaussian`-phrased `E[max] ≤ √(2σ² log d)`. The two cannot share a home
today because cross-area imports are restricted to `ForMathlib/` layers and
that lemma lives in a concept layer; this generic-`Fintype`,
`HasSubgaussianMGF`-phrased version is the **promotion candidate** — when the
concentration area is next touched, `expectation_max_le` should be re-derived
from this file and the shared statement promoted to a common `ForMathlib`
home (tracked in the PR notes; do not add a third copy).
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

-- The auxiliary lemmas are stated for `Fintype ι` to share the index typeclass with the
-- headline theorems (whose bounds involve `Fintype.card ι`); some only use the induced
-- `Finite ι`, which this linter flags.
set_option linter.unusedFintypeInType false

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {ι : Type*} [Fintype ι]

/-- AE-strong-measurability of a finite pointwise supremum of AE-measurable functions. -/
lemma aestronglyMeasurable_iSup [Nonempty ι] {Z : ι → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ) :
    AEStronglyMeasurable (fun ω ↦ ⨆ i, Z i ω) μ := by
  have hfun : (fun ω ↦ ⨆ i, Z i ω)
      = Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Z i) := by
    funext ω
    rw [Finset.sup'_apply, Finset.sup'_univ_eq_ciSup]
  rw [hfun]
  refine Finset.sup'_induction _ _ (p := fun g ↦ AEStronglyMeasurable g μ)
    (fun _ hf _ hg ↦ hf.sup hg) (fun i _ ↦ hZ i)

/-- The pointwise maximum of finitely many integrable functions is integrable. -/
lemma integrable_iSup_of_forall_integrable [Nonempty ι] {Z : ι → Ω → ℝ}
    (hZ : ∀ i, Integrable (Z i) μ) :
    Integrable (fun ω ↦ ⨆ i, Z i ω) μ := by
  refine Integrable.mono' (g := fun ω ↦ ∑ i, |Z i ω|) ?_
    (aestronglyMeasurable_iSup (fun i ↦ (hZ i).aestronglyMeasurable)) ?_
  · exact integrable_finset_sum _ (fun i _ ↦ (hZ i).abs)
  · refine Filter.Eventually.of_forall (fun ω ↦ ?_)
    rw [Real.norm_eq_abs, ← Finset.sup'_univ_eq_ciSup (fun i ↦ Z i ω)]
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ Z i ω)
    rw [hj]
    exact Finset.single_le_sum (f := fun i ↦ |Z i ω|)
      (fun i _ ↦ abs_nonneg _) (Finset.mem_univ j)

/-- `exp (λ · ⨆ Z)` is integrable when each `exp (λ · Z i)` is. -/
lemma integrable_exp_iSup_of_subgaussian [Nonempty ι] {Z : ι → Ω → ℝ} {c : ℝ≥0}
    (hZ : ∀ i, HasSubgaussianMGF (Z i) c μ) (lam : ℝ) :
    Integrable (fun ω ↦ Real.exp (lam * ⨆ i, Z i ω)) μ := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.exp (lam * ⨆ i, Z i ω)) μ :=
    (Real.continuous_exp.comp_aestronglyMeasurable
      ((aestronglyMeasurable_iSup (fun i ↦ (hZ i).aestronglyMeasurable)).const_smul lam))
  refine Integrable.mono' (g := fun ω ↦ ∑ i, Real.exp (lam * Z i ω)) ?_ hmeas ?_
  · exact integrable_finset_sum _ (fun i _ ↦ (hZ i).integrable_exp_mul lam)
  · refine Filter.Eventually.of_forall (fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    rw [← Finset.sup'_univ_eq_ciSup (fun i ↦ Z i ω)]
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ Z i ω)
    rw [hj]
    calc Real.exp (lam * Z j ω)
        ≤ ∑ i, Real.exp (lam * Z i ω) :=
          Finset.single_le_sum (f := fun i ↦ Real.exp (lam * Z i ω))
            (fun i _ ↦ Real.exp_nonneg _) (Finset.mem_univ j)

/-- **Sub-Gaussian maximal inequality (one-sided).** For a finite nonempty index
family `ι` and `Z : ι → Ω → ℝ` with each `Z i` sub-Gaussian with proxy variance
`≤ c` under a probability measure `μ`,
`E[⨆ i, Z i] ≤ √(2 c · log (card ι))`. -/
theorem expectation_iSup_le_of_subgaussian [IsProbabilityMeasure μ] [Nonempty ι]
    {Z : ι → Ω → ℝ} {c : ℝ≥0} (hc : 0 < c) (hcard : 2 ≤ Fintype.card ι)
    (hZ : ∀ i, HasSubgaussianMGF (Z i) c μ) :
    ∫ ω, ⨆ i, Z i ω ∂μ ≤ Real.sqrt (2 * c * Real.log (Fintype.card ι)) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  set L : ℝ := Real.log N with hL
  set c' : ℝ := (c : ℝ) with hc'
  have hc'pos : 0 < c' := by rw [hc']; exact_mod_cast hc
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hcard
  have hNpos : 0 < N := by linarith
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos; linarith
  set m : ℝ := ∫ ω, ⨆ i, Z i ω ∂μ with hm
  have hSint : Integrable (fun ω ↦ ⨆ i, Z i ω) μ :=
    integrable_iSup_of_forall_integrable (fun i ↦ (hZ i).integrable)
  -- Master inequality: ∀ λ > 0,  λ * m ≤ L + c' * λ^2 / 2.
  have master : ∀ lam : ℝ, 0 < lam → lam * m ≤ L + c' * lam ^ 2 / 2 := by
    intro lam hlam
    -- Jensen: exp (λ m) = exp (∫ λ S) ≤ ∫ exp (λ S).
    have hjensen : Real.exp (lam * m) ≤ ∫ ω, Real.exp (lam * ⨆ i, Z i ω) ∂μ := by
      have hconv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
      have key := hconv.map_integral_le (f := fun ω ↦ lam * ⨆ i, Z i ω)
        Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall (fun _ ↦ Set.mem_univ _))
        (hSint.const_mul lam) (integrable_exp_iSup_of_subgaussian hZ lam)
      rwa [integral_const_mul, ← hm] at key
    -- ∫ exp (λ S) ≤ ∑ mgf (Z i) λ ≤ N * exp (c' λ²/2).
    have hsum : ∫ ω, Real.exp (lam * ⨆ i, Z i ω) ∂μ
        ≤ N * Real.exp (c' * lam ^ 2 / 2) := by
      have hbound : (fun ω ↦ Real.exp (lam * ⨆ i, Z i ω))
          ≤ᵐ[μ] fun ω ↦ ∑ i, Real.exp (lam * Z i ω) := by
        refine Filter.Eventually.of_forall (fun ω ↦ ?_)
        simp only
        rw [← Finset.sup'_univ_eq_ciSup (fun i ↦ Z i ω)]
        obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ Z i ω)
        rw [hj]
        exact Finset.single_le_sum (f := fun i ↦ Real.exp (lam * Z i ω))
          (fun i _ ↦ Real.exp_nonneg _) (Finset.mem_univ j)
      calc ∫ ω, Real.exp (lam * ⨆ i, Z i ω) ∂μ
          ≤ ∫ ω, ∑ i, Real.exp (lam * Z i ω) ∂μ :=
            integral_mono_ae (integrable_exp_iSup_of_subgaussian hZ lam)
              (integrable_finset_sum _ (fun i _ ↦ (hZ i).integrable_exp_mul lam)) hbound
        _ = ∑ i, ∫ ω, Real.exp (lam * Z i ω) ∂μ :=
            integral_finset_sum _ (fun i _ ↦ (hZ i).integrable_exp_mul lam)
        _ = ∑ _i : ι, mgf (Z _i) μ lam := by rfl
        _ ≤ ∑ _i : ι, Real.exp (c' * lam ^ 2 / 2) :=
            Finset.sum_le_sum (fun i _ ↦ by
              have := (hZ i).mgf_le lam
              simpa [hc'] using this)
        _ = N * Real.exp (c' * lam ^ 2 / 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
    -- Combine and take logs.
    have hcomb : Real.exp (lam * m) ≤ N * Real.exp (c' * lam ^ 2 / 2) := hjensen.trans hsum
    have hpos : (0 : ℝ) < N * Real.exp (c' * lam ^ 2 / 2) :=
      mul_pos hNpos (Real.exp_pos _)
    have hlog := Real.log_le_log (Real.exp_pos _) hcomb
    rw [Real.log_exp, Real.log_mul (ne_of_gt hNpos) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp, ← hL] at hlog
    linarith
  -- Optimise λ = √(2L/c'). Write s = √(2L/c'), t = √(2 c' L); then s·t = 2L.
  set s : ℝ := Real.sqrt (2 * L / c') with hs
  set t : ℝ := Real.sqrt (2 * c' * L) with ht
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (by positivity)
  have htnn : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
  have hssq : s ^ 2 = 2 * L / c' := by rw [hs]; exact Real.sq_sqrt (by positivity)
  have hst : s * t = 2 * L := by
    rw [hs, ht, ← Real.sqrt_mul (by positivity)]
    rw [show 2 * L / c' * (2 * c' * L) = (2 * L) ^ 2 by
      field_simp]
    exact Real.sqrt_sq (by positivity)
  have hopt := master s hspos
  rw [hssq] at hopt
  -- RHS of master: L + c' * (2L/c')/2 = 2L = s·t.
  have hRHS : L + c' * (2 * L / c') / 2 = s * t := by rw [hst]; field_simp; ring
  rw [hRHS] at hopt
  -- s·m ≤ s·t with s > 0 ⟹ m ≤ t = √(2 c' L) = √(2 c · log card).
  have hmt : m ≤ t := le_of_mul_le_mul_left (by linarith [hopt]) hspos
  exact hmt

/-- The doubled family `Z, -Z` indexed by `ι ⊕ ι`. -/
private def doubledFam (Z : ι → Ω → ℝ) : ι ⊕ ι → Ω → ℝ :=
  Sum.elim Z (fun i ↦ -Z i)

/-- For a finite index, `⨆ p : ι ⊕ ι, (doubledFam Z) p ω = ⨆ i, |Z i ω|`:
the sup of `Z` and `-Z` over the doubled index is the sup of `|Z|`. -/
private lemma iSup_doubled_eq_iSup_abs [Nonempty ι] (Z : ι → Ω → ℝ) (ω : Ω) :
    ⨆ p : ι ⊕ ι, doubledFam Z p ω = ⨆ i, |Z i ω| := by
  apply le_antisymm
  · refine ciSup_le (fun p ↦ ?_)
    cases p with
    | inl i =>
        exact (le_abs_self (Z i ω)).trans
          (le_ciSup (Finite.bddAbove_range (fun i ↦ |Z i ω|)) i)
    | inr i =>
        exact (neg_le_abs (Z i ω)).trans
          (le_ciSup (Finite.bddAbove_range (fun i ↦ |Z i ω|)) i)
  · refine ciSup_le (fun i ↦ ?_)
    rcases abs_choice (Z i ω) with h | h
    · rw [h]
      exact le_ciSup (Finite.bddAbove_range (doubledFam Z · ω)) (Sum.inl i)
    · rw [h]
      exact le_ciSup (Finite.bddAbove_range (doubledFam Z · ω)) (Sum.inr i)

/-- **Sub-Gaussian maximal inequality (absolute value).** The building block the
chaining consumer needs:
`E[⨆ i, |Z i|] ≤ √(2 c · log (2 · card ι))`. -/
theorem expectation_iSup_abs_le_of_subgaussian [IsProbabilityMeasure μ] [Nonempty ι]
    {Z : ι → Ω → ℝ} {c : ℝ≥0} (hc : 0 < c)
    (hZ : ∀ i, HasSubgaussianMGF (Z i) c μ) :
    ∫ ω, ⨆ i, |Z i ω| ∂μ ≤ Real.sqrt (2 * c * Real.log (2 * Fintype.card ι)) := by
  -- Each member of the doubled family is sub-Gaussian with the same proxy variance.
  have hW : ∀ p : ι ⊕ ι, HasSubgaussianMGF (doubledFam Z p) c μ := by
    rintro (i | i)
    · exact hZ i
    · exact (hZ i).neg
  -- card (ι ⊕ ι) = 2 * card ι ≥ 2.
  have hcard2 : 2 ≤ Fintype.card (ι ⊕ ι) := by
    rw [Fintype.card_sum]
    have : 1 ≤ Fintype.card ι := Fintype.card_pos
    omega
  -- Apply the one-sided bound to the doubled family and rewrite the sup.
  have hcore := expectation_iSup_le_of_subgaussian (μ := μ) hc hcard2 hW
  have hrw : (fun ω ↦ ⨆ p : ι ⊕ ι, doubledFam Z p ω) = fun ω ↦ ⨆ i, |Z i ω| := by
    funext ω; exact iSup_doubled_eq_iSup_abs Z ω
  rw [hrw] at hcore
  rw [Fintype.card_sum] at hcore
  -- card ι + card ι = 2 * card ι.
  have : ((Fintype.card ι + Fintype.card ι : ℕ) : ℝ) = 2 * (Fintype.card ι : ℝ) := by
    push_cast; ring
  rw [this] at hcore
  exact hcore

end ProbabilityTheory
