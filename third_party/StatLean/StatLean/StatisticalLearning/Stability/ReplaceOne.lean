module
public import StatLean.StatisticalLearning.Stability.Defs
public import StatLean.StatisticalLearning.Core.SampleLaw
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Replace-one exchangeability of the i.i.d. sample law

The measure-theoretic engine of SSBD Theorem 13.2: on
`(sampleLaw D n).prod D`, swapping the `i`-th coordinate with the extra
point — `(s, z') ↦ (s[i ↦ z'], sᵢ)` — is measure-preserving (exchangeability
of i.i.d. draws), together with the two evaluation identities it feeds:
`E[ℓ(A(S), z')] = E_S[L_D(A(S))]` and `n⁻¹∑ᵢ E[ℓ(A(S), sᵢ)] = E_S[L_S(A(S))]`.

**Reference.** SSBD Theorem 13.2 proof ("since `S` and `z'` are drawn i.i.d.,
swap the roles of `zᵢ` and `z'`"). Transcription:
`notes/statistical_learning/book_statements/ch12-13.md`.

**Formalization notes.** The swap reduces to a coordinate permutation of the
`(n+1)`-fold product via `(Fin n → Z) × Z ≃ᵐ (Fin (n+1) → Z)`
(`MeasurableEquiv.piFinSuccAbove`-style, cf. CLAUDE.md §7.14–15) and
permutation invariance of `Measure.pi`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ}

section Swap

/-- LEAN-ONLY: the measurable equivalence `(Fin n → Z) × Z ≃ᵐ (Fin (n+1) → Z)`
given by `Fin.snoc` — it appends the fresh point as the last coordinate. -/
private def snocEquivM (Z : Type*) [MeasurableSpace Z] (n : ℕ) :
    (Sample Z n × Z) ≃ᵐ (Fin (n + 1) → Z) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) (Fin.last n)).symm

private theorem coe_snocEquivM :
    ⇑(snocEquivM Z n) = fun p : Sample Z n × Z => Fin.snoc p.1 p.2 := by
  funext p
  simp [snocEquivM, MeasurableEquiv.prodComm, Fin.snocEquiv]

private theorem coe_snocEquivM_symm :
    ⇑(snocEquivM Z n).symm =
      fun x : Fin (n + 1) → Z => (fun j : Fin n => x j.castSucc, x (Fin.last n)) := by
  funext x
  simp [snocEquivM, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    Fin.snocEquiv, MeasurableEquiv.trans, MeasurableEquiv.symm, Equiv.symm_trans_apply,
    Fin.init_def]

/-- LEAN-ONLY: `Fin.snoc` transports the joint law of `(S, z')` to the
`(n+1)`-fold i.i.d. law. -/
private theorem measurePreserving_snocEquivM :
    MeasurePreserving (snocEquivM Z n) ((sampleLaw D n).prod D)
      (Measure.pi fun _ : Fin (n + 1) => D) :=
  (MeasurePreserving.symm _
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D)
        (Fin.last n))).comp Measure.measurePreserving_swap

/-- **Replace-one exchangeability** (SSBD Thm 13.2 proof step): the swap
`(s, z') ↦ (replaceOne s i z', sᵢ)` preserves `(sampleLaw D n).prod D`. -/
theorem measurePreserving_replaceOne_swap (i : Fin n) :
    MeasurePreserving
      (fun p : Sample Z n × Z => (replaceOne p.1 i p.2, p.1 i))
      ((sampleLaw D n).prod D) ((sampleLaw D n).prod D) := by
  classical
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.castSucc (Fin.last n) with hσdef
  -- the coordinate transposition is measure-preserving for the `(n+1)`-fold law
  have hperm : MeasurePreserving
      (fun x : Fin (n + 1) → Z => fun b => x (σ b))
      (Measure.pi fun _ : Fin (n + 1) => D) (Measure.pi fun _ : Fin (n + 1) => D) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => D) σ
    have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) => Z) σ) =
        fun x : Fin (n + 1) → Z => fun b => x (σ b) := by
      funext x b
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, hσdef,
        Equiv.symm_swap]
    rwa [hfun] at h
  -- conjugate it through `snoc`
  have hcomp := ((measurePreserving_snocEquivM (D := D)).symm _).comp
    (hperm.comp (measurePreserving_snocEquivM (D := D)))
  have hfun : (fun p : Sample Z n × Z => (replaceOne p.1 i p.2, p.1 i)) =
      ⇑(snocEquivM Z n).symm ∘ ((fun x : Fin (n + 1) → Z => fun b => x (σ b)) ∘
        ⇑(snocEquivM Z n)) := by
    funext p
    simp only [Function.comp_apply, coe_snocEquivM, coe_snocEquivM_symm]
    refine Prod.ext ?_ ?_
    · funext j
      by_cases hj : j = i
      · subst hj
        simp [hσdef, Equiv.swap_apply_left, replaceOne]
      · have h1 : j.castSucc ≠ i.castSucc := by
          simpa [Fin.castSucc_inj] using hj
        have h2 : j.castSucc ≠ Fin.last n := Fin.ne_of_lt j.castSucc_lt_last
        simp [hσdef, Equiv.swap_apply_of_ne_of_ne h1 h2, replaceOne,
          Function.update_of_ne hj]
    · simp [hσdef, Equiv.swap_apply_right]
  rw [hfun]
  exact hcomp

end Swap

/-- The fresh point evaluates the true risk (SSBD Thm 13.2 proof:
`E_S[L_D(A(S))] = E_{S,z'}[ℓ(A(S), z')]`). -/
theorem integral_loss_fresh_eq_integral_risk (ℓ : H → Z → ℝ)
    (A : Sample Z n → H)
    -- LEAN-ONLY: joint integrability of the fresh-point loss (the book's
    -- expectations presuppose it)
    (hint : Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) p.2) ((sampleLaw D n).prod D)) :
    ∫ p : Sample Z n × Z, ℓ (A p.1) p.2 ∂((sampleLaw D n).prod D) =
      ∫ s, risk D ℓ (A s) ∂(sampleLaw D n) := by
  rw [integral_prod _ hint]
  rfl

/-- The index-averaged in-sample loss evaluates the empirical risk
(SSBD Thm 13.2 proof: `E_S[L_S(A(S))] = E_{S,i}[ℓ(A(S), zᵢ)]`). -/
theorem sum_integral_loss_at_coord_eq_integral_empRisk (ℓ : H → Z → ℝ)
    (A : Sample Z n → H)
    -- LEAN-ONLY: integrability of each in-sample loss coordinate
    (hint : ∀ i : Fin n, Integrable
      (fun s : Sample Z n => ℓ (A s) (s i)) (sampleLaw D n))
    -- USER-INPUT: at least one example; SSBD §13.2 (implicit)
    (hn : 1 ≤ n) :
    (n : ℝ)⁻¹ * ∑ i : Fin n,
        ∫ s, ℓ (A s) (s i) ∂(sampleLaw D n) =
      ∫ s, empRisk ℓ s (A s) ∂(sampleLaw D n) := by
  have h1 : ∫ s, empRisk ℓ s (A s) ∂(sampleLaw D n) =
      (n : ℝ)⁻¹ * ∫ s, ∑ i : Fin n, ℓ (A s) (s i) ∂(sampleLaw D n) := by
    simp only [empRisk]
    exact integral_const_mul _ _
  rw [h1, integral_finset_sum _ fun i _ => hint i]

end StatLean.StatisticalLearning
