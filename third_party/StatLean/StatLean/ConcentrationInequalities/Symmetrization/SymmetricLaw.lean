module
public import StatLean.ConcentrationInequalities.Symmetrization.Rademacher
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# Symmetric laws and Rademacher mixing

A real random variable $X$ is *symmetric* if $-X \overset{d}{=} X$; at the
level of laws, $\nu$ is symmetric if $(\mathrm{neg})_\#\nu = \nu$. This file
proves HDP Lemma 6.3.1 (constructing symmetric distributions) in the two
forms consumed by the Gaussian symmetrization Lemma 6.6.2: for an independent
Rademacher sign $\xi$ and symmetric $X$,
$$ \xi X \overset{d}{=} X \qquad\text{and}\qquad \xi |X| \overset{d}{=} X, $$
together with the joint vector versions
$(\varepsilon_i g_i)_i \overset{d}{=} (g_i)_i$ and
$(\varepsilon_i |g_i|)_i \overset{d}{=} (g_i)_i$ for independent symmetric
coordinates.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3, Lemma 6.3.1(b) (p. 179) and its use on
p. 186 (proof of Lemma 6.6.2).

**Proof formalization notes.** The scalar mixing identities are proved at the
level of laws by `Measure.prod_apply` and a four-piece partition of the line
(`{x ≥ 0}`, `{x > 0}`, `{x ≤ 0}`, `{x < 0}`) — **no atom condition needed**
(the possible atom at `0` is handled by the overlap of the closed/open
pieces). Vector versions are assembled by the same
`MeasurableEquiv.arrowProdEquivProdArrow` + `measurePreserving_pi` pattern as
`SignFlip.lean`, stated in the exact `(signVec N).prod (Measure.pi ν)` order
in which `Gaussian.lean` consumes them. Gaussian symmetry via
`gaussianReal_map_neg`. Named-sorry fallback of this work item:
`IsSymmetricLaw.map_mul_abs_rad` (the `|·|` partition case); the plain mixing
identity and the vector assemblies proven.

**Bibliographic comments.** Symmetrization by an independent sign is
classical (P. Lévy, *Théorie de l'addition des variables aléatoires*, 1937).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Symmetric law** (HDP §6.3, p. 179): a law `ν` on `ℝ` is symmetric if it
is invariant under negation, `(−·)#ν = ν`. Edge behavior: no probability
hypothesis at definition level — any measure qualifies if negation-invariant. -/
def IsSymmetricLaw (ν : Measure ℝ) : Prop :=
  ν.map (fun x => -x) = ν

/-- The Rademacher law is symmetric (HDP §6.3). -/
theorem isSymmetricLaw_radLaw : IsSymmetricLaw radLaw :=
  radLaw_map_neg

/-- Centered Gaussians are symmetric (HDP §6.3); via `gaussianReal_map_neg`. -/
theorem isSymmetricLaw_gaussianReal (v : ℝ≥0) :
    IsSymmetricLaw (gaussianReal 0 v) := by
  unfold IsSymmetricLaw
  rw [gaussianReal_map_neg, neg_zero]

/-- **Rademacher mixing** (HDP §6.3, Lemma 6.3.1(b)): for an independent sign
`ξ` and symmetric `X`, `ξX =ᵈ X`, at the level of laws on the product
`radLaw.prod ν`. -/
theorem IsSymmetricLaw.map_mul_rad {ν : Measure ℝ} [IsProbabilityMeasure ν]
    -- USER-INPUT: ν symmetric; HDP §6.3 Lemma 6.3.1(b)
    (hν : IsSymmetricLaw ν) :
    (radLaw.prod ν).map (fun p => p.1 * p.2) = ν := by
  have hmul : Measurable (fun p : ℝ × ℝ => p.1 * p.2) := measurable_fst.mul measurable_snd
  unfold radLaw
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ hmul, Measure.map_smul, Measure.map_smul,
    Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map hmul measurable_prodMk_left, Measure.map_map hmul measurable_prodMk_left]
  have h1 : (fun p : ℝ × ℝ => p.1 * p.2) ∘ (Prod.mk (1 : ℝ)) = id := by funext y; simp
  have h2 : (fun p : ℝ × ℝ => p.1 * p.2) ∘ (Prod.mk (-1 : ℝ)) = (fun y => -y) := by
    funext y; simp
  rw [h1, h2, Measure.map_id, show ν.map (fun y => -y) = ν from hν,
    ← add_smul, ENNReal.inv_two_add_inv_two, one_smul]

/-- **Rademacher mixing with absolute value** (HDP §6.3, Lemma 6.3.1(b)):
`ξ|X| =ᵈ X` for symmetric `X`. Named-sorry debt candidate of this work item
(four-piece partition of the line at `0`; no atom condition needed). -/
theorem IsSymmetricLaw.map_mul_abs_rad {ν : Measure ℝ} [IsProbabilityMeasure ν]
    -- USER-INPUT: ν symmetric; HDP §6.3 Lemma 6.3.1(b)
    (hν : IsSymmetricLaw ν) :
    (radLaw.prod ν).map (fun p => p.1 * |p.2|) = ν := by
  have hmul : Measurable (fun p : ℝ × ℝ => p.1 * |p.2|) :=
    measurable_fst.mul measurable_snd.abs
  -- Key: for *any* measure, the paired pushforwards of `(|·|, -|·|)` and
  -- `(id, -·)` have equal sums (unordered pair `{|y|, -|y|} = {y, -y}`).
  set s := Set.Ici (0 : ℝ) with hs_def
  have hs : MeasurableSet s := measurableSet_Ici
  have hmap_split : ∀ g : ℝ → ℝ, Measurable g →
      ν.map g = (ν.restrict s).map g + (ν.restrict sᶜ).map g := by
    intro g hg
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := ν) hs]
    rw [Measure.map_add _ _ hg]
  have c1 : (ν.restrict s).map (fun y => |y|) = (ν.restrict s).map (fun y => y) :=
    Measure.map_congr <| by
      filter_upwards [ae_restrict_mem hs] with y hy; exact abs_of_nonneg hy
  have c2 : (ν.restrict s).map (fun y => -|y|) = (ν.restrict s).map (fun y => -y) :=
    Measure.map_congr <| by
      filter_upwards [ae_restrict_mem hs] with y hy; rw [abs_of_nonneg hy]
  have c3 : (ν.restrict sᶜ).map (fun y => |y|) = (ν.restrict sᶜ).map (fun y => -y) :=
    Measure.map_congr <| by
      filter_upwards [ae_restrict_mem hs.compl] with y hy
      exact abs_of_neg (by simpa [hs_def, not_le] using hy)
  have c4 : (ν.restrict sᶜ).map (fun y => -|y|) = (ν.restrict sᶜ).map (fun y => y) :=
    Measure.map_congr <| by
      filter_upwards [ae_restrict_mem hs.compl] with y hy
      rw [abs_of_neg (by simpa [hs_def, not_le] using hy), neg_neg]
  have hsum : ν.map (fun y => |y|) + ν.map (fun y => -|y|)
      = ν.map (fun y => y) + ν.map (fun y => -y) := by
    rw [hmap_split (fun y => |y|) (by fun_prop),
      hmap_split (fun y => -|y|) (by fun_prop),
      hmap_split (fun y => y) (by fun_prop),
      hmap_split (fun y => -y) (by fun_prop), c1, c2, c3, c4]
    abel
  -- Assemble as in `map_mul_rad`.
  unfold radLaw
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ hmul, Measure.map_smul, Measure.map_smul,
    Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map hmul measurable_prodMk_left, Measure.map_map hmul measurable_prodMk_left]
  have h1 : (fun p : ℝ × ℝ => p.1 * |p.2|) ∘ (Prod.mk (1 : ℝ)) = (fun y => |y|) := by
    funext y; simp
  have h2 : (fun p : ℝ × ℝ => p.1 * |p.2|) ∘ (Prod.mk (-1 : ℝ)) = (fun y => -|y|) := by
    funext y; simp
  rw [h1, h2, ← smul_add, hsum, smul_add, Measure.map_id',
    show ν.map (fun y => -y) = ν from hν, ← add_smul, ENNReal.inv_two_add_inv_two, one_smul]

/-- Vector assembly of the scalar mixing identities. Given a measurable scalar
combining map `f : ℝ × ℝ → ℝ` whose pushforward of `radLaw.prod (ν i)` is
`ν i` for each coordinate, the coordinatewise map assembles to `Measure.pi ν`
on the product `signVec ⊗ pi ν`. -/
-- LEAN-ONLY: `arrowProdEquivProdArrow` + `pi_map_pi` gluing.
private lemma map_signVec_prod_pi {N : ℕ} {ν : Fin N → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)] (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hfν : ∀ i, (radLaw.prod (ν i)).map f = ν i) :
    ((signVec N).prod (Measure.pi ν)).map (fun p i => f (p.1 i, p.2 i))
      = Measure.pi ν := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N) with he
  have hmp : MeasurePreserving e
      (Measure.pi fun i => radLaw.prod (ν i))
      ((Measure.pi fun _ : Fin N => radLaw).prod (Measure.pi ν)) :=
    measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N) (fun _ => radLaw) ν
  have hsymm := (MeasurePreserving.symm e hmp).map_eq
  haveI : ∀ i, SigmaFinite ((radLaw.prod (ν i)).map f) := fun i => by
    rw [hfν i]; infer_instance
  have hfam : Measurable (fun w : Fin N → ℝ × ℝ => fun i => f (w i)) :=
    measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))
  have hcomp : (fun p : (Fin N → ℝ) × (Fin N → ℝ) => fun i => f (p.1 i, p.2 i))
      = (fun w : Fin N → ℝ × ℝ => fun i => f (w i)) ∘ e.symm := rfl
  rw [show signVec N = Measure.pi fun _ : Fin N => radLaw from rfl, hcomp,
    ← Measure.map_map hfam e.symm.measurable, hsymm, Measure.pi_map_pi (fun i => hf.aemeasurable)]
  simp_rw [hfν]

/-- Joint vector mixing `(εᵢXᵢ)ᵢ =ᵈ (Xᵢ)ᵢ` for independent symmetric
coordinates (HDP §6.6, p. 186: `(εᵢgᵢ) =ᵈ (gᵢ)`). -/
theorem map_signVec_mul_pi {N : ℕ} {ν : Fin N → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)]
    -- USER-INPUT: symmetric coordinates; HDP §6.3 Lemma 6.3.1(b)
    (hν : ∀ i, IsSymmetricLaw (ν i)) :
    ((signVec N).prod (Measure.pi ν)).map (fun p i => p.1 i * p.2 i)
      = Measure.pi ν :=
  map_signVec_prod_pi (fun w => w.1 * w.2) (measurable_fst.mul measurable_snd)
    (fun i => (hν i).map_mul_rad)

/-- Joint vector mixing with absolute values `(εᵢ|Xᵢ|)ᵢ =ᵈ (Xᵢ)ᵢ` for
independent symmetric coordinates (HDP §6.6, p. 186: `(εᵢ|gᵢ|) =ᵈ (gᵢ)`,
Lemma 6.3.1(b)). -/
theorem map_signVec_mul_abs_pi {N : ℕ} {ν : Fin N → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)]
    -- USER-INPUT: symmetric coordinates; HDP §6.3 Lemma 6.3.1(b)
    (hν : ∀ i, IsSymmetricLaw (ν i)) :
    ((signVec N).prod (Measure.pi ν)).map (fun p i => p.1 i * |p.2 i|)
      = Measure.pi ν :=
  map_signVec_prod_pi (fun w => w.1 * |w.2|)
    (measurable_fst.mul measurable_snd.abs) (fun i => (hν i).map_mul_abs_rad)

end StatLean.ConcentrationInequalities
