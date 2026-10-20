module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import StatLean.Bayesian.ForMathlib.PiWithDensity

@[expose] public section

/-!
# Finite-index (`Fintype`) products: Tonelli, densities, and subtype splits

`Fintype`-index upgrades of the `Fin n` product bricks in
`StatLean.Bayesian.ForMathlib.PiWithDensity`, together with the two subtype-split
lemmas that the Dirichlet–Laplace tensorization step (BPPD eq. (26)) needs.

* `lintegral_pi_prod_fintype` / `pi_withDensity_fintype` — the homogeneous
  `∫⁻ ∏ = ∏ ∫⁻` and `⨂ withDensity = withDensity ∏` identities over an arbitrary
  finite index `ι` (the `Fin n` versions lifted through `Fintype.equivFin`).
* `pi_map_restrict_subtype` — pushing a product of probability measures forward
  under the coordinate restriction `x ↦ x|_{S}` returns the product over the
  subtype `S = {i // p i}`; the complementary probability factors integrate out.
* `lintegral_pi_split` — split-Tonelli: an lintegral against `⨂_ι μ` becomes the
  iterated lintegral over the `p`-coordinates (outer) and the `¬p`-coordinates
  (inner), the point reassembled through `Equiv.piEquivPiSubtypeProd`.

**Reference.** Mathlib-level bricks (no book statement of their own) consumed by
the Dirichlet–Laplace posterior-contraction proof (Bhattacharya–Pati–Pillai–Dunson,
*Dirichlet–Laplace priors for optimal shrinkage*, JASA 2015 / arXiv:1401.5398;
tag `BPPD §X.Y`): they provide the product / subtype-split Tonelli used to
tensorize the posterior likelihood ratio into its `S₀ᶜ`-submodel factor
(BPPD eq. (26), §6).

**Proof formalization notes.** The two `_fintype` upgrades transport the `Fin n`
statements through `MeasureTheory.measurePreserving_piCongrLeft` along
`Fintype.equivFin`; `pi_map_restrict_subtype` composes
`MeasureTheory.measurePreserving_piEquivPiSubtypeProd` with the first-marginal
identity `MeasureTheory.Measure.map_fst_prod` (the `¬p` factor being a probability
measure); `lintegral_pi_split` is that same measure-preserving equivalence followed
by the product-measure Tonelli `MeasureTheory.lintegral_prod`. Candidate for
upstreaming; kept in the area `ForMathlib/` layer (namespace `StatLean.Bayesian`).

**Bibliographic comments.** Product measures and the Fubini–Tonelli theorem are
classical measure theory (Fubini 1907; Tonelli 1909), used here only in their
finite-product / iid-experiment form.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {ι : Type*} [Fintype ι]

/-- Heterogeneous Tonelli over `Fin n` (private engine; re-derivation of the `Fin n`
peeling used to seed the `Fintype` transport). Mirrors the Bochner
`integral_fin_nat_prod_eq_prod`, peeling one coordinate with `piFinSuccAbove`. -/
private theorem lintegral_pi_prod_hetero_fin {n : ℕ} {α : Fin n → Type*}
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

/-- Heterogeneous Tonelli over an arbitrary finite index (private engine; transports
`lintegral_pi_prod_hetero_fin` along `Fintype.equivFin ι` via
`measurePreserving_piCongrLeft`). -/
private theorem lintegral_pi_prod_hetero_fintype {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) (hμ : ∀ i, SigmaFinite (μ i))
    {f : (i : ι) → α i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  haveI := hμ
  let e := (Fintype.equivFin ι).symm
  rw [(measurePreserving_piCongrLeft μ e).lintegral_map_equiv
      (fun x => ∏ i, f i (x i)) (MeasurableEquiv.piCongrLeft α e)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [lintegral_pi_prod_hetero_fin (fun i' => μ (e i')) (fun i' => hμ (e i'))
      (f := fun i' => f (e i')) (fun i' => hf (e i'))]

/-- **Tonelli for coordinate products over an arbitrary finite index.** The
`Fintype ι` upgrade of `lintegral_pi_prod`:
`∫⁻ x, ∏ i, f i (x i) ∂(⨂_ι μ) = ∏ i, ∫⁻ y, f i y ∂μ`. -/
theorem lintegral_pi_prod_fintype (μ : Measure 𝓧) [SigmaFinite μ]
    {f : ι → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: coordinate integrands measurable (regularity for Tonelli); no scope change
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi fun _ : ι => μ) = ∏ i, ∫⁻ y, f i y ∂μ :=
  lintegral_pi_prod_hetero_fintype (fun _ => μ) (fun _ => inferInstance) hf

/-- **A finite product of `withDensity` measures is `withDensity` of the product
density**, over an arbitrary finite index `ι` (the `Fintype` upgrade of
`pi_withDensity`). -/
theorem pi_withDensity_fintype (μ : Measure 𝓧) [SigmaFinite μ]
    {f : ι → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: coordinate densities measurable (regularity); no scope change
    (hf : ∀ i, Measurable (f i))
    -- LEAN-ONLY: each factor σ-finite (needed by `Measure.pi`); holds for finite-mass densities
    [∀ i : ι, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i))
      = (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f i (x i) := by
  have hprod : Measurable fun x : ι → 𝓧 => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  refine Measure.pi_eq (μ := fun i => μ.withDensity (f i)) (fun s hs => ?_)
  calc ((Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f i (x i)) (Set.univ.pi s)
      = ∫⁻ x in Set.univ.pi s, ∏ i, f i (x i) ∂(Measure.pi fun _ : ι => μ) :=
        withDensity_apply _ (MeasurableSet.univ_pi hs)
    _ = ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi fun i => μ.restrict (s i)) := by
        rw [Measure.restrict_pi_pi]
    _ = ∏ i, ∫⁻ y, f i y ∂(μ.restrict (s i)) :=
        lintegral_pi_prod_hetero_fintype (fun i => μ.restrict (s i)) (fun _ => inferInstance) hf
    _ = ∏ i, (μ.withDensity (f i)) (s i) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [withDensity_apply _ (hs i)]

/-- **Coordinate restriction marginalizes a product of probability measures.**
Pushing `⨂_ι μ` forward under the restriction `x ↦ (fun i : {i // p i} => x i)`
returns the product over the subtype `{i // p i}`; the complementary factors, being
probability measures, integrate out to `1`. -/
theorem pi_map_restrict_subtype {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    -- LEAN-ONLY: complementary factors are probability measures (so they marginalize to 1)
    [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    (Measure.pi μ).map (fun x : ∀ i, α i => fun i : Subtype p => x i.val)
      = Measure.pi (fun i : Subtype p => μ i.val) := by
  have hmp := measurePreserving_piEquivPiSubtypeProd μ p
  have hcomp : (fun x : ∀ i, α i => fun i : Subtype p => x i.val)
      = Prod.fst ∘ ⇑(MeasurableEquiv.piEquivPiSubtypeProd α p) := rfl
  rw [hcomp, ← Measure.map_map measurable_fst
      (MeasurableEquiv.piEquivPiSubtypeProd α p).measurable, hmp.map_eq]
  exact Measure.fst_prod

/-- **Split-Tonelli over a predicate `p`.** An lintegral against the full product
measure equals the iterated lintegral over the `p`-coordinates (outer) and the
`¬p`-coordinates (inner), with the integrand evaluated at the point reassembled by
`Equiv.piEquivPiSubtypeProd`. -/
theorem lintegral_pi_split {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (p : ι → Prop) [DecidablePred p]
    {f : (∀ i, α i) → ℝ≥0∞}
    -- LEAN-ONLY: integrand measurable (regularity for Tonelli on the product); no scope change
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(Measure.pi μ)
      = ∫⁻ xS, ∫⁻ xSc, f ((Equiv.piEquivPiSubtypeProd p α).symm (xS, xSc))
          ∂(Measure.pi fun i : {i // ¬ p i} => μ i.val)
          ∂(Measure.pi fun i : Subtype p => μ i.val) := by
  have hmp := measurePreserving_piEquivPiSubtypeProd μ p
  rw [← hmp.symm.lintegral_comp hf,
    lintegral_prod (fun a => f ((MeasurableEquiv.piEquivPiSubtypeProd α p).symm a))
      (hf.comp (MeasurableEquiv.piEquivPiSubtypeProd α p).symm.measurable).aemeasurable]
  rfl

end StatLean.Bayesian
