module
public import StatLean.StatisticalModels.Coarsening.Basic
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Ignorability — the observed-data law factorizes over the two slices

**C5 (Rubin's factorization, exact measure form).** Under a MAR mechanism with propensity
`π(x) = ρ' x {true}`, the observed-data law decomposes over the response indicator:

* complete-case slice (`r = true`): the outcome law reweighted by the propensity —
  `Q.withDensity (π ∘ fst)` transported by `(x, y) ↦ (x, true, y)`;
* incomplete slice (`r = false`): the covariate marginal reweighted by `1 − π` —
  `(Q.map fst).withDensity (1 − π)` transported by `x ↦ (x, false, 0)`;

and the two slices reassemble the observed law. This is the measure-level content of Rubin's
observed-data likelihood `[f_θ(x,y) π_φ(x)]^r [(∫ f_θ(x,y)\,dy)(1−π_φ(x))]^{1−r}` — the
θ-part and the φ-part sit in different factors, so the mechanism is *ignorable* for
likelihood inference about the outcome law: the dominated corollary exhibits the
complete-case density as exactly `f · (π ∘ fst)`.

*Book vs Lean:* the slice decomposition is stated for **arbitrary** outcome laws — no
domination, no densities; Rubin's dominated formulation is the corollary, strictly weaker.
The distinctness-of-parameters clause and the Bayesian reading of ignorability are named
future work (D-C4). The formal agreement lemma with the semiparametric
`Examples.MARMean.marMean_Ψ` estimand (C4) is deliberately not stated: it would import an
assembly-layer example file for a near-`rfl` transport; the connection is documented at
`Coarsening.IPW` instead (deviation recorded in the batch ledger).

**Reference.** D. B. Rubin, "Inference and missing data," *Biometrika* **63** (1976),
581–592, §2–3 (the ignorability theorem) (`Rubin76 §2–3`); R. J. A. Little and D. B. Rubin,
*Statistical Analysis with Missing Data*, 3rd ed., Wiley, 2019, §6.2 (verify §) (`LR §6.2`).

**Proof formalization notes.** Both slice lemmas are `Measure.ext` computations: unfold
`observedLaw`/`fullLaw` through `Measure.map_apply`/`Measure.compProd_apply` (mind the
un-β-reduced integrands — `simp_rw`/`change`), split the event by the Bool coordinate, and
evaluate the inner Bernoulli integral (`Coarsening.Basic.lintegral_bool`). On the `false`
slice the masked coordinate is the constant `0`, whence the pushforward from the covariate
marginal alone.

**Bibliographic comments.** Ignorability is Rubin's (1976) — the observation that under MAR
(+ distinct parameters) the missingness mechanism drops out of the likelihood; the
slice-decomposition form is the standard modern proof (LR §6.2).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatLean.StatisticalModels.Coarsening

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The full-data reassociation `((x, y), r) ↦ (x, y, r)` is measurable. -/
private theorem measurable_fullAssoc' :
    Measurable fun p : (𝓧 × ℝ) × Bool => (p.1.1, p.1.2, p.2) :=
  measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)

/-- The composite `missingObserve ∘ reassociation`, read off the `compProd` carrier. -/
private theorem measurable_obsComp :
    Measurable fun p : (𝓧 × ℝ) × Bool => (p.1.1, p.2, if p.2 then p.1.2 else 0) :=
  measurable_missingObserve.comp measurable_fullAssoc'

/-- `observedLaw` as a single pushforward of the `compProd` measure (map/map fusion). -/
private theorem observedLaw_eq_map (Q : Measure (𝓧 × ℝ)) (ρ : Kernel (𝓧 × ℝ) Bool) :
    observedLaw Q ρ = (Q ⊗ₘ ρ).map fun p => (p.1.1, p.2, if p.2 then p.1.2 else 0) := by
  rw [observedLaw, fullLaw, Measure.map_map measurable_missingObserve measurable_fullAssoc']
  rfl

/-- **C5a, complete-case slice** (`Rubin76 §2–3`): under MAR, the observed law restricted to
`{r = true}` is the propensity-reweighted outcome law, transported to the observed carrier. -/
theorem observedLaw_restrict_true (Q : Measure (𝓧 × ℝ)) [IsProbabilityMeasure Q]
    (ρ' : Kernel 𝓧 Bool) [IsMarkovKernel ρ'] :
    (observedLaw Q (ρ'.comap Prod.fst measurable_fst)).restrict {o | o.2.1 = true}
      = (Q.withDensity fun p => ρ' p.1 {true}).map
          (fun p : 𝓧 × ℝ => (p.1, true, p.2)) := by
  have hh : Measurable (fun p : 𝓧 × ℝ => (p.1, true, p.2)) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have hS : MeasurableSet {o : 𝓧 × Bool × ℝ | o.2.1 = true} :=
    measurable_snd.fst (measurableSet_singleton true)
  ext A hA
  rw [Measure.restrict_apply hA, observedLaw_eq_map,
    Measure.map_apply measurable_obsComp (hA.inter hS),
    Measure.compProd_apply (measurable_obsComp (hA.inter hS)),
    Measure.map_apply hh hA, withDensity_apply _ (hh hA),
    ← lintegral_indicator (hh hA)]
  refine lintegral_congr fun q => ?_
  rw [Kernel.comap_apply]
  by_cases hq : q ∈ (fun p : 𝓧 × ℝ => (p.1, true, p.2)) ⁻¹' A
  · rw [Set.indicator_of_mem hq]
    congr 1
    ext r; cases r <;> simp_all [Set.mem_preimage]
  · rw [Set.indicator_of_notMem hq, ← measure_empty (μ := ρ' q.1)]
    congr 1
    ext r; cases r <;> simp_all [Set.mem_preimage]

/-- **C5b, incomplete slice** (`Rubin76 §2–3`): under MAR, the observed law restricted to
`{r = false}` is the `(1−π)`-reweighted covariate marginal, carried to the observed carrier
with the masked outcome slot. -/
theorem observedLaw_restrict_false (Q : Measure (𝓧 × ℝ)) [IsProbabilityMeasure Q]
    (ρ' : Kernel 𝓧 Bool) [IsMarkovKernel ρ'] :
    (observedLaw Q (ρ'.comap Prod.fst measurable_fst)).restrict {o | o.2.1 = false}
      = ((Q.map Prod.fst).withDensity fun x => ρ' x {false}).map
          (fun x : 𝓧 => (x, false, 0)) := by
  have hk : Measurable (fun x : 𝓧 => (x, false, (0 : ℝ))) :=
    measurable_id.prodMk (measurable_const.prodMk measurable_const)
  have hS : MeasurableSet {o : 𝓧 × Bool × ℝ | o.2.1 = false} :=
    measurable_snd.fst (measurableSet_singleton false)
  have hd : Measurable fun x : 𝓧 => ρ' x {false} :=
    Kernel.measurable_coe ρ' (measurableSet_singleton false)
  ext A hA
  rw [Measure.restrict_apply hA, observedLaw_eq_map,
    Measure.map_apply measurable_obsComp (hA.inter hS),
    Measure.compProd_apply (measurable_obsComp (hA.inter hS)),
    Measure.map_apply hk hA, withDensity_apply _ (hk hA),
    ← lintegral_indicator (hk hA), lintegral_map (hd.indicator (hk hA)) measurable_fst]
  refine lintegral_congr fun q => ?_
  rw [Kernel.comap_apply]
  by_cases hq : q.1 ∈ (fun x : 𝓧 => (x, false, (0 : ℝ))) ⁻¹' A
  · rw [Set.indicator_of_mem hq]
    congr 1
    ext r; cases r <;> simp_all [Set.mem_preimage]
  · rw [Set.indicator_of_notMem hq, ← measure_empty (μ := ρ' q.1)]
    congr 1
    ext r; cases r <;> simp_all [Set.mem_preimage]

/-- The two slices reassemble the observed law (the factorization is exhaustive). -/
theorem observedLaw_eq_restrict_add (Q : Measure (𝓧 × ℝ)) [IsProbabilityMeasure Q]
    (ρ : Kernel (𝓧 × ℝ) Bool) [IsMarkovKernel ρ] :
    observedLaw Q ρ
      = (observedLaw Q ρ).restrict {o | o.2.1 = true}
          + (observedLaw Q ρ).restrict {o | o.2.1 = false} := by
  have hS : MeasurableSet {o : 𝓧 × Bool × ℝ | o.2.1 = true} :=
    measurable_snd.fst (measurableSet_singleton true)
  have hcompl : {o : 𝓧 × Bool × ℝ | o.2.1 = true}ᶜ = {o : 𝓧 × Bool × ℝ | o.2.1 = false} := by
    ext o; simp [Bool.not_eq_true]
  rw [← hcompl, Measure.restrict_add_restrict_compl hS]

/-- **C5', the dominated corollary (Rubin's observed-data likelihood factor)**: when the
outcome law is dominated, `Q = ν.withDensity f`, the complete-case slice carries the density
`f(x, y) · π(x)` — the `θ`-factor times the `φ`-factor, whence ignorability (`Rubin76 §3`;
`LR §6.2`). -/
theorem observedLaw_restrict_true_withDensity (ν : Measure (𝓧 × ℝ)) [SigmaFinite ν]
    (f : 𝓧 × ℝ → ℝ≥0∞) (ρ' : Kernel 𝓧 Bool) [IsMarkovKernel ρ']
    -- LEAN-ONLY: measurable density (withDensity commutation)
    (hf : Measurable f)
    [IsProbabilityMeasure (ν.withDensity f)] :
    (observedLaw (ν.withDensity f) (ρ'.comap Prod.fst measurable_fst)).restrict
        {o | o.2.1 = true}
      = (ν.withDensity fun p => f p * ρ' p.1 {true}).map
          (fun p : 𝓧 × ℝ => (p.1, true, p.2)) := by
  have hd : Measurable fun p : 𝓧 × ℝ => ρ' p.1 {true} :=
    (Kernel.measurable_coe ρ' (measurableSet_singleton true)).comp measurable_fst
  rw [observedLaw_restrict_true _ ρ', ← withDensity_mul _ hf hd]
  rfl

end StatLean.StatisticalModels.Coarsening
