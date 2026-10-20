module
public import StatLean.StatisticalLearning.Core.SampleLaw

@[expose] public section

/-!
# ERM on a representative sample, and uniform convergence ⇒ agnostic PAC

The deterministic heart of learning via uniform convergence: on an
`ε/2`-representative sample every (approximate) empirical risk minimizer is
`ε`-optimal in true risk (SSBD Lemma 4.2), and hence a class with the uniform
convergence property is agnostically PAC learnable by any ERM selector with
`m(ε,δ) ≤ m^{UC}(ε/2, δ)` (SSBD Corollary 4.4).

**Reference.** SSBD §4.1 (Lemma 4.2, Corollary 4.4). Transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.** Lemma 4.2's three-inequality chain
`L_D(h_S) ≤ L_S(h_S) + ε/2 ≤ L_S(g) + ε/2 ≤ L_D(g) + ε` is verbatim; the
`sInf`-image form of the best-in-class risk requires a `BddBelow` side
condition, discharged from loss nonnegativity in the corollaries. The ERM
*selector* `A` is data (the book's `ERM_𝓗` paradigm — a choice function),
per the repo's hypothesis discipline for minimizers.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ} {𝓗 : Set H} {ℓ : H → Z → ℝ}

/-- **SSBD Lemma 4.2** (`ε/2`-representative ⇒ ERM is `ε`-good): on an
`ε/2`-representative sample, any empirical risk minimizer `h` satisfies
`L_D(h) ≤ inf_{g∈𝓗} L_D(g) + ε`. -/
theorem risk_le_bestRisk_add_of_isERM_of_uniformDeviation {s : Sample Z n}
    {h : H} {ε : ℝ}
    -- USER-INPUT: the sample is `ε/2`-representative; SSBD Lemma 4.2
    (hrep : UniformDeviationLE D 𝓗 ℓ s (ε / 2))
    -- USER-INPUT: `h` is an ERM hypothesis; SSBD Lemma 4.2 (`h_S ∈ argmin`)
    (hERM : IsERM 𝓗 ℓ s h)
    -- LEAN-ONLY: bounded-below risk image, so the `sInf` is genuine
    (hbdd : BddBelow (risk D ℓ '' 𝓗)) :
    risk D ℓ h ≤ bestRisk D 𝓗 ℓ + ε := by
  have key : risk D ℓ h - ε ≤ bestRisk D 𝓗 ℓ := by
    refine le_csInf ⟨risk D ℓ h, ⟨h, hERM.1, rfl⟩⟩ ?_
    rintro x ⟨g, hg, rfl⟩
    -- `L_D(h) ≤ L_S(h) + ε/2`
    have h1 : risk D ℓ h ≤ empRisk ℓ s h + ε / 2 := by
      have := (abs_sub_le_iff.mp (hrep h hERM.1)).2
      linarith
    -- `L_S(h) ≤ L_S(g)`
    have h2 : empRisk ℓ s h ≤ empRisk ℓ s g := hERM.2 g hg
    -- `L_S(g) ≤ L_D(g) + ε/2`
    have h3 : empRisk ℓ s g ≤ risk D ℓ g + ε / 2 := by
      have := (abs_sub_le_iff.mp (hrep g hg)).1
      linarith
    linarith
  linarith

/-- **SSBD Lemma 4.2, approximate-ERM form**: an `η`-approximate empirical risk
minimizer on an `ε/2`-representative sample is `(ε + η)`-optimal. -/
theorem risk_le_bestRisk_add_of_isApproxERM_of_uniformDeviation
    {s : Sample Z n} {h : H} {ε η : ℝ}
    -- USER-INPUT: the sample is `ε/2`-representative; SSBD Lemma 4.2
    (hrep : UniformDeviationLE D 𝓗 ℓ s (ε / 2))
    -- USER-INPUT: `h` is an `η`-approximate ERM; SSBD §2.3 (approximate form)
    (hERM : IsApproxERM 𝓗 ℓ s η h)
    -- LEAN-ONLY: bounded-below risk image, so the `sInf` is genuine
    (hbdd : BddBelow (risk D ℓ '' 𝓗)) :
    risk D ℓ h ≤ bestRisk D 𝓗 ℓ + (ε + η) := by
  have key : risk D ℓ h - (ε + η) ≤ bestRisk D 𝓗 ℓ := by
    refine le_csInf ⟨risk D ℓ h, ⟨h, hERM.1, rfl⟩⟩ ?_
    rintro x ⟨g, hg, rfl⟩
    have h1 : risk D ℓ h ≤ empRisk ℓ s h + ε / 2 := by
      have := (abs_sub_le_iff.mp (hrep h hERM.1)).2
      linarith
    have h2 : empRisk ℓ s h ≤ empRisk ℓ s g + η := hERM.2 g hg
    have h3 : empRisk ℓ s g ≤ risk D ℓ g + ε / 2 := by
      have := (abs_sub_le_iff.mp (hrep g hg)).1
      linarith
    linarith
  linarith

/-- **SSBD Corollary 4.4** (uniform convergence ⇒ agnostic PAC via ERM): if
`𝓗` has the uniform convergence property with witness `mUC`, then any ERM
selector `A` is an agnostic PAC learner with `mSC ε δ = mUC (ε/2) δ`. -/
theorem isAgnosticPACLearnerWith_of_hasUniformConvergenceWith
    {mUC : ℝ → ℝ → ℕ} {A : ∀ m : ℕ, Sample Z m → H}
    -- USER-INPUT: the class has uniform convergence with witness `mUC`;
    -- SSBD Definition 4.3
    (hUC : HasUniformConvergenceWith 𝓗 ℓ mUC)
    -- USER-INPUT: `A` is an ERM selector (the book's `ERM_𝓗` choice
    -- function is data); SSBD §2.3
    (hA : ∀ (m : ℕ) (s : Sample Z m), IsERM 𝓗 ℓ s (A m s))
    -- USER-INPUT: nonnegative loss; SSBD §3.2.1 (`ℓ : 𝓗 × Z → ℝ₊`) —
    -- supplies `BddBelow` of every risk image
    (hpos : ∀ h z, 0 ≤ ℓ h z) :
    IsAgnosticPACLearnerWith 𝓗 ℓ A (fun ε δ => mUC (ε / 2) δ) := by
  intro D hD ε δ hε hδ hδ1 m hm
  haveI := hD
  -- the risk image is bounded below by `0`, so the `sInf` is genuine
  have hbdd : BddBelow (risk D ℓ '' 𝓗) := by
    refine ⟨0, ?_⟩
    rintro x ⟨g, _, rfl⟩
    exact risk_nonneg (hpos g)
  -- every `ε/2`-representative sample makes the ERM output `ε`-optimal
  have hsub : {s : Sample Z m | UniformDeviationLE D 𝓗 ℓ s (ε / 2)} ⊆
      {s : Sample Z m | risk D ℓ (A m s) ≤ bestRisk D 𝓗 ℓ + ε} := fun s hs =>
    risk_le_bestRisk_add_of_isERM_of_uniformDeviation hs (hA m s) hbdd
  exact le_trans (hUC D hD (ε / 2) δ (by linarith) hδ hδ1 m hm)
    (measure_mono hsub)

end StatLean.StatisticalLearning
