module
public import StatLean.StatisticalLearning.Stability.ReplaceOne

@[expose] public section

/-!
# Stable rules do not overfit

SSBD Theorem 13.2 — the exact expectation identity
`E_S[L_D(A(S)) − L_S(A(S))] = E_{(S,z'),i}[ℓ(A(S^{(i)}), zᵢ) − ℓ(A(S), zᵢ)]`
(the overfitting gap *is* the averaged replace-one stability gap), and SSBD
Theorem 13.12 (Exercise 13.3): an on-average-stable AERM learns its class in
expectation with rate `ε₁(n) + ε₂(n)`.

**Reference.** SSBD §13.2, Theorem 13.2; Exercise 13.3 (Theorem 13.12).
Transcription: `notes/statistical_learning/book_statements/ch12-13.md`.

**Formalization notes.** Theorem 13.2 is pure exchangeability: expand both
sides via `ReplaceOne.lean`'s three bricks — no concentration. Theorem 13.12
chains the identity with `E[min_h L_S(h)] ≤ min_h L_D(h)` (Jensen for minima);
the min over the class is the `sInf`-image `bestRisk`, and its empirical
counterpart needs a `BddBelow` guard from loss nonnegativity.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ} {ℓ : H → Z → ℝ}

/-- **SSBD Theorem 13.2** (stable rules do not overfit — the identity): the
expected overfitting gap of any learning rule equals its averaged replace-one
stability gap. -/
theorem integral_risk_sub_empRisk_eq_stabilityGap (A : Sample Z n → H)
    -- LEAN-ONLY: joint integrability of the fresh-point loss
    (hint₁ : Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) p.2) ((sampleLaw D n).prod D))
    -- LEAN-ONLY: joint integrability of the replaced-rule in-sample losses
    (hint₂ : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z => ℓ (A (replaceOne p.1 i p.2)) (p.1 i))
      ((sampleLaw D n).prod D))
    -- LEAN-ONLY: integrability of each in-sample loss coordinate
    (hint₃ : ∀ i : Fin n, Integrable
      (fun s : Sample Z n => ℓ (A s) (s i)) (sampleLaw D n))
    -- USER-INPUT: at least one example; SSBD §13.2 (implicit)
    (hn : 1 ≤ n) :
    ∫ s, (risk D ℓ (A s) - empRisk ℓ s (A s)) ∂(sampleLaw D n) =
      stabilityGap D ℓ A := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- the in-sample losses are integrable on the joint law, through `Prod.fst`
  have hfst : MeasurePreserving (Prod.fst : Sample Z n × Z → Sample Z n)
      ((sampleLaw D n).prod D) (sampleLaw D n) := measurePreserving_fst
  have hint₃' : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) (p.1 i)) ((sampleLaw D n).prod D) := by
    intro i
    simpa [Function.comp_def] using hfst.integrable_comp_of_integrable (hint₃ i)
  have hrisk : Integrable (fun s => risk D ℓ (A s)) (sampleLaw D n) :=
    hint₁.integral_prod_left
  have hemp : Integrable (fun s => empRisk ℓ s (A s)) (sampleLaw D n) := by
    simp only [empRisk]
    exact (integrable_finset_sum _ fun i _ => hint₃ i).const_mul _
  -- the two coordinate-wise identities
  have hcoord : ∀ i : Fin n,
      ∫ p : Sample Z n × Z, ℓ (A p.1) (p.1 i) ∂((sampleLaw D n).prod D) =
        ∫ s, ℓ (A s) (s i) ∂(sampleLaw D n) := by
    intro i
    have h := integral_map (φ := (Prod.fst : Sample Z n × Z → Sample Z n))
      (f := fun s : Sample Z n => ℓ (A s) (s i)) hfst.measurable.aemeasurable
      (by rw [hfst.map_eq]; exact (hint₃ i).aestronglyMeasurable)
    rw [hfst.map_eq] at h
    exact h.symm
  have hswap : ∀ i : Fin n,
      ∫ p : Sample Z n × Z, ℓ (A (replaceOne p.1 i p.2)) (p.1 i) ∂((sampleLaw D n).prod D) =
        ∫ p : Sample Z n × Z, ℓ (A p.1) p.2 ∂((sampleLaw D n).prod D) := by
    intro i
    have hT := measurePreserving_replaceOne_swap (D := D) i
    have h := integral_map
      (φ := fun p : Sample Z n × Z => (replaceOne p.1 i p.2, p.1 i))
      (f := fun q : Sample Z n × Z => ℓ (A q.1) q.2) hT.measurable.aemeasurable
      (by rw [hT.map_eq]; exact hint₁.aestronglyMeasurable)
    rw [hT.map_eq] at h
    exact h.symm
  -- per-index evaluation of the stability gap summands
  have key : ∀ i : Fin n,
      ∫ p : Sample Z n × Z,
          (ℓ (A (replaceOne p.1 i p.2)) (p.1 i) - ℓ (A p.1) (p.1 i)) ∂((sampleLaw D n).prod D) =
        (∫ p : Sample Z n × Z, ℓ (A p.1) p.2 ∂((sampleLaw D n).prod D)) -
          ∫ s, ℓ (A s) (s i) ∂(sampleLaw D n) := by
    intro i
    rw [integral_sub (hint₂ i) (hint₃' i), hswap i, hcoord i]
  rw [integral_sub hrisk hemp, ← integral_loss_fresh_eq_integral_risk ℓ A hint₁,
    ← sum_integral_loss_at_coord_eq_integral_empRisk ℓ A hint₃ hn, stabilityGap]
  simp only [key, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **SSBD Theorem 13.12** (stability + AERM ⇒ learnability, in expectation,
fixed `n` form): if `A`'s replace-one gap is `≤ ε₁` and `A` is an
`ε₂`-approximate ERM in expectation, then
`E_S[L_D(A(S))] ≤ inf_{h∈𝓗} L_D(h) + ε₁ + ε₂`. -/
theorem integral_risk_le_bestRisk_add_of_stable_of_aerm
    (A : Sample Z n → H) {𝓗 : Set H} {ε₁ ε₂ : ℝ}
    -- USER-INPUT: stability at size `n`; SSBD Thm 13.12 (`ε₁(m)`)
    (hstab : stabilityGap D ℓ A ≤ ε₁)
    -- USER-INPUT: AERM in expectation against every fixed competitor;
    -- SSBD Exercise 13.3 (`E[L_S(A(S)) − min_h L_S(h)] ≤ ε₂` relaxed to the
    -- per-competitor form `E[L_S(A(S))] ≤ E[L_S(h)] + ε₂`)
    (haerm : ∀ h ∈ 𝓗,
      ∫ s, empRisk ℓ s (A s) ∂(sampleLaw D n) ≤
        (∫ s, empRisk ℓ s h ∂(sampleLaw D n)) + ε₂)
    -- USER-INPUT: nonempty class; SSBD Thm 13.12 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: per-hypothesis integrable loss; SSBD Remark 3.1
    (hint : ∀ h ∈ 𝓗, Integrable (ℓ h) D)
    -- LEAN-ONLY: integrability bundle for Theorem 13.2's identity
    (hint₁ : Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) p.2) ((sampleLaw D n).prod D))
    (hint₂ : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z => ℓ (A (replaceOne p.1 i p.2)) (p.1 i))
      ((sampleLaw D n).prod D))
    (hint₃ : ∀ i : Fin n, Integrable
      (fun s : Sample Z n => ℓ (A s) (s i)) (sampleLaw D n))
    -- LEAN-ONLY: bounded-below risk image (from loss nonnegativity)
    (hbdd : BddBelow (risk D ℓ '' 𝓗))
    -- USER-INPUT: at least one example; SSBD §13.2 (implicit)
    (hn : 1 ≤ n) :
    ∫ s, risk D ℓ (A s) ∂(sampleLaw D n) ≤ bestRisk D 𝓗 ℓ + ε₁ + ε₂ := by
  -- (13.15): decompose the expected risk into the empirical part and the gap
  have hrisk : Integrable (fun s => risk D ℓ (A s)) (sampleLaw D n) :=
    hint₁.integral_prod_left
  have hemp : Integrable (fun s => empRisk ℓ s (A s)) (sampleLaw D n) := by
    simp only [empRisk]
    exact (integrable_finset_sum _ fun i _ => hint₃ i).const_mul _
  have h132 := integral_risk_sub_empRisk_eq_stabilityGap A hint₁ hint₂ hint₃ hn
  rw [integral_sub hrisk hemp] at h132
  -- against every competitor in the class
  have hkey : ∀ b ∈ risk D ℓ '' 𝓗,
      (∫ s, risk D ℓ (A s) ∂(sampleLaw D n)) - ε₁ - ε₂ ≤ b := by
    rintro b ⟨h, hh, rfl⟩
    have h1 := haerm h hh
    have h2 : ∫ s, empRisk ℓ s h ∂(sampleLaw D n) = risk D ℓ h :=
      integral_empRisk (hint h hh) hn
    rw [h2] at h1
    linarith
  have := le_csInf (h𝓗.image (risk D ℓ)) hkey
  simp only [bestRisk] at *
  linarith

end StatLean.StatisticalLearning
