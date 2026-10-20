module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Finite product measures and densities (`∫⁻ ∏ = ∏ ∫⁻`, `pi_withDensity`)

Two bricks about homogeneous finite products that the pinned Mathlib lacks (only the Bochner
version `integral_fintype_prod_eq_prod` exists):

* `lintegral_pi_prod` — Tonelli for a product of coordinate functions,
  $$\int \prod_i f_i(x_i)\,d\mu^{\otimes n} = \prod_i \int f_i\,d\mu;$$
* `pi_withDensity` — a finite product of `withDensity` measures is `withDensity` of the product
  density, $\bigotimes_i \mu\!\cdot\!f_i = \mu^{\otimes n}\cdot\big(x \mapsto \prod_i f_i(x_i)\big).$

These power the iid-kernel density representation (`StatLean.Bayesian.ForMathlib.IIDKernel`) and
hence every `n`-observation posterior in the Bayesian area.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.3, p. 13 (iid samples and product likelihoods; implicit
measure-theoretic background).

**Proof formalization notes.** Candidate for upstreaming to Mathlib (kept in the area's
`ForMathlib/` layer, namespace `StatLean.Bayesian`, until then). `lintegral_pi_prod` is proved by
induction on `n`, peeling one coordinate with `MeasureTheory.measurePreserving_piFinSuccAbove` and
finishing with the binary `lintegral_prod_mul`; `pi_withDensity` follows on boxes via
`Measure.pi_eq`, `withDensity_apply`, and `Measure.restrict_pi_pi`.

**Bibliographic comments.** Product measures and the Fubini–Tonelli theorem are classical measure
theory (G. Fubini 1907; L. Tonelli 1909); the countable-product construction used for iid models
is due to C. Ionescu-Tulcea and, in the probabilistic setting, A. N. Kolmogorov
(*Grundbegriffe*, 1933). The statistical reading — an iid sample as a product experiment — is
standard.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- Heterogeneous Tonelli for coordinate products (private engine; the homogeneous
`lintegral_pi_prod` and the box computation in `pi_withDensity` both consume it). Mirrors the
Bochner `integral_fin_nat_prod_eq_prod`, peeling one coordinate with `piFinSuccAbove`. -/
private theorem lintegral_pi_prod_hetero {n : ℕ} {α : Fin n → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : (i : Fin n) → Measure (α i)) (hμ : ∀ i, SigmaFinite (μ i))
    {f : (i : Fin n) → α i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  induction n with
  | zero => haveI := hμ; simp [Measure.pi_empty_univ]
  | succ n ih =>
      haveI := hμ
      have hg : Measurable fun z : (j : Fin n) → α j.succ => ∏ i, f i.succ (z i) :=
        Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _) (fun b => ∏ i, f i (b i))]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.cons_zero]
      refine (lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun i => μ i.succ)
        (f := f 0) (g := fun z : (j : Fin n) → α j.succ => ∏ i, f i.succ (z i))
        (hf 0).aemeasurable hg.aemeasurable).trans ?_
      rw [ih (μ := fun i => μ i.succ) (fun i => hμ i.succ) (f := fun i => f i.succ)
          (fun i => hf i.succ)]

/-- **Tonelli for coordinate products** over a homogeneous finite product measure:
`∫⁻ x, ∏ i, f i (x i) ∂(⨂ⁿ μ) = ∏ i, ∫⁻ y, f i y ∂μ`. -/
theorem lintegral_pi_prod {n : ℕ} (μ : Measure 𝓧) [SigmaFinite μ]
    {f : Fin n → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: coordinate integrands are measurable (regularity)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi fun _ : Fin n => μ) = ∏ i, ∫⁻ y, f i y ∂μ :=
  lintegral_pi_prod_hetero (fun _ => μ) (fun _ => inferInstance) hf

/-- **A finite product of `withDensity` measures is `withDensity` of the product density.** -/
theorem pi_withDensity {n : ℕ} (μ : Measure 𝓧) [SigmaFinite μ]
    {f : Fin n → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: coordinate densities are measurable (regularity)
    (hf : ∀ i, Measurable (f i))
    -- LEAN-ONLY: each factor is σ-finite (holds for finite-mass densities; needed by Measure.pi)
    [∀ i : Fin n, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i))
      = (Measure.pi fun _ : Fin n => μ).withDensity fun x => ∏ i, f i (x i) := by
  have hprod : Measurable fun x : Fin n → 𝓧 => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  refine Measure.pi_eq (μ := fun i => μ.withDensity (f i)) (fun s hs => ?_)
  calc ((Measure.pi fun _ : Fin n => μ).withDensity fun x => ∏ i, f i (x i)) (Set.univ.pi s)
      = ∫⁻ x in Set.univ.pi s, ∏ i, f i (x i) ∂(Measure.pi fun _ : Fin n => μ) :=
        withDensity_apply _ (MeasurableSet.univ_pi hs)
    _ = ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi fun i => μ.restrict (s i)) := by
        rw [Measure.restrict_pi_pi]
    _ = ∏ i, ∫⁻ y, f i y ∂(μ.restrict (s i)) :=
        lintegral_pi_prod_hetero (fun i => μ.restrict (s i)) (fun _ => inferInstance) hf
    _ = ∏ i, (μ.withDensity (f i)) (s i) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [withDensity_apply _ (hs i)]

end StatLean.Bayesian
