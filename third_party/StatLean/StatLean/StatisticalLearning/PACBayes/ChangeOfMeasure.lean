module
public import StatLean.StatisticalLearning.PACBayes.Defs
public import Mathlib.InformationTheory.KullbackLeibler.Basic

@[expose] public section

/-!
# The change-of-measure inequality (Donsker–Varadhan, discrete)

The engine of every PAC-Bayes bound (SSBD Eq. (31.2)): for probability
measures `Q ≪ P` on a countable index and any functional `f`,
`E_Q[f] ≤ D(Q‖P) + log E_P[e^f]`.

**Reference.** SSBD §31.1, Eq. (31.2) ("change of measure + Jensen").
Transcription: `notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** Proved for a countable discrete index (Round-1
scope): write `E_Q[f] − D(Q‖P)` as `E_Q[log(e^f · (dP/dQ))]` on the support of
`Q` and apply Jensen for `log` — all sums, no Radon–Nikodym analysis beyond
the discrete density `k ↦ P{k}/Q{k}`. `klDiv` is Mathlib's ℝ≥0∞-valued KL;
finiteness is a hypothesis (`Q ≪ P` alone does not preclude `D = ∞`, in which
case the inequality is vacuous anyway but the `toReal` junk would corrupt the
statement).
-/

open MeasureTheory InformationTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {ι : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
  [Countable ι]

-- The proof goes through Mathlib's tilted-measure/`llr` API, which needs no
-- discreteness; the instance is kept for the countable Round-1 interface.
set_option linter.unusedSectionVars false in
/-- **Change of measure / Donsker–Varadhan upper bound** (SSBD Eq. (31.2)):
for probability measures `Q ≪ P` on a countable discrete index with
`D(Q‖P) < ∞`, and `f` with `Q`-integrable value and `P`-integrable
exponential, `E_Q[f] ≤ D(Q‖P) + log E_P[e^f]`. -/
theorem gibbsAvg_le_klDiv_add_log_integral_exp
    (P Q : Measure ι) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : ι → ℝ)
    -- USER-INPUT: absolute continuity `Q ≪ P`; SSBD §31.1 (implicit in
    -- `D(Q‖P) < ∞` for densities — made explicit here)
    (hac : Q ≪ P)
    -- USER-INPUT: finite KL divergence; SSBD Thm 31.1 (the bound is trivial
    -- otherwise)
    (hkl : klDiv Q P ≠ ⊤)
    -- LEAN-ONLY: `Q`-integrability of `f` (bounded functionals downstream)
    (hf : Integrable f Q)
    -- LEAN-ONLY: `P`-integrability of `e^f` (bounded functionals downstream)
    (hexp : Integrable (fun k => Real.exp (f k)) P) :
    gibbsAvg Q f ≤ (klDiv Q P).toReal +
      Real.log (∫ k, Real.exp (f k) ∂P) := by
  classical
  obtain ⟨-, hllr⟩ := klDiv_ne_top_iff.mp hkl
  have hZpos : 0 < ∫ k, Real.exp (f k) ∂P := integral_exp_pos hexp
  have hPf : IsProbabilityMeasure (P.tilted f) := isProbabilityMeasure_tilted hexp
  have hacf : Q ≪ P.tilted f := hac.trans (absolutelyContinuous_tilted hexp)
  -- Pointwise on the support of `Q`, the log-likelihood ratio against the tilted
  -- measure splits: `log dQ/dP_f = −f + log E_P[e^f] + log dQ/dP`.
  have key : llr Q (P.tilted f) =ᵐ[Q]
      fun k => -f k + Real.log (∫ k, Real.exp (f k) ∂P) + llr Q P k := by
    have h1 := (toReal_rnDeriv_tilted_right Q P hexp).filter_mono hac.ae_le
    filter_upwards [h1, Measure.rnDeriv_pos hac,
      hac.ae_le (Measure.rnDeriv_lt_top Q P)] with k hk hkpos hklt
    have hr : (0 : ℝ) < (Q.rnDeriv P k).toReal := ENNReal.toReal_pos hkpos.ne' hklt.ne
    simp only [llr_def]
    rw [hk, Real.log_mul (by positivity) hr.ne',
      Real.log_mul (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hint : Integrable (llr Q (P.tilted f)) Q := by
    have h : Integrable
        (fun k => -f k + Real.log (∫ k, Real.exp (f k) ∂P) + llr Q P k) Q :=
      (hf.neg.add (integrable_const _)).add hllr
    exact h.congr key.symm
  -- Gibbs' inequality for `D(Q‖P_f) ≥ 0`.
  have hnn := integral_llr_add_sub_measure_univ_nonneg hacf hint
  simp only [probReal_univ, add_sub_cancel_right] at hnn
  -- Split the integral (the lambda shapes must be pinned down, else `Pi.neg`/`Pi.add`
  -- block the `integral_add` rewrite).
  have hIneg : Integrable (fun a : ι => -f a) Q := hf.neg
  have hI1 : Integrable
      (fun a : ι => -f a + Real.log (∫ k, Real.exp (f k) ∂P)) Q :=
    hIneg.add (integrable_const _)
  have hsplit : ∫ a, (-f a + Real.log (∫ k, Real.exp (f k) ∂P) + llr Q P a) ∂Q
      = -(∫ a, f a ∂Q) + Real.log (∫ k, Real.exp (f k) ∂P)
        + ∫ a, llr Q P a ∂Q := by
    rw [integral_add hI1 hllr, integral_add hIneg (integrable_const _), integral_neg,
      integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [integral_congr_ae key, hsplit] at hnn
  rw [gibbsAvg, toReal_klDiv_of_measure_eq hac (by simp)]
  linarith

end StatLean.StatisticalLearning
