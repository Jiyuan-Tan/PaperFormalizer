module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# The sign flip: conditional coordinate swap of two independent copies

The crux of symmetrization. For two independent copies
$(X_1,\dots,X_N)$, $(X_1',\dots,X_N')$ with $X_i, X_i' \sim \nu_i$, and any
deterministic sign pattern $c \in \{\pm 1\}^N$,
$$ \Bigl(c_i\,(X_i - X_i')\Bigr)_{i \le N}
   \;\overset{d}{=}\; \Bigl(X_i - X_i'\Bigr)_{i \le N}, $$
because swapping $X_i \leftrightarrow X_i'$ in exactly the coordinates with
$c_i = -1$ is measure-preserving on the product of two copies of
$\bigotimes_i \nu_i$. This is Lemma 6.3.1(c) + Exercise 6.16(b) of HDP in
vector form ("$X - X'$ is symmetric"), packaged as the measure-preservation
statement `measurePreserving_condSwap` and its integral consequence
`integral_flip_diff`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3, Lemma 6.3.1(c) and Exercise 6.16(b)
(used in the proof of Lemma 6.3.2, pp. 180–181).

**Proof formalization notes.** The conditional swap is assembled
coordinatewise: per index `i` the map on `E × E` is `id` or `Prod.swap`
according to `σ i`, each factor `(ν i).prod (ν i)` being swap-invariant
(`measurePreserving_swap`); the family is glued by `measurePreserving_pi` and
conjugated through `MeasurableEquiv.arrowProdEquivProdArrow`
(`measurePreserving_arrowProdEquivProdArrow` handles varying factors `ν i`).
This route avoids Sum-type reindexing (`sumPiEquivProdPi`) and its `Eq.rec`
casts entirely — both directions of `arrowProdEquivProdArrow` are cast-free
lambda terms. The integral identity `integral_flip_diff` is a pure change of
variables (`Measure.map` + `integral_map`) and needs **no** integrability
hypotheses. Named-sorry fallback of this work item:
`measurePreserving_condSwap` (with `integral_flip_diff` derived from it).

**Bibliographic comments.** The symmetrization device of comparing a sum with
the difference of two independent copies goes back to P. Lévy (1937) and was
developed for Banach-space-valued sums by J.-P. Kahane, *Some Random Series of
Functions* (1968), and Ledoux–Talagrand, *Probability in Banach Spaces*
(1991), §6.1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The conditional coordinate swap is measure-preserving** (engine of HDP
§6.3, Lemma 6.3.1(c) / Exercise 6.16(b)): on the product of two independent
copies of `⊗ᵢ νᵢ`, swapping the two copies in exactly the coordinates selected
by `σ` preserves the measure. Named-sorry debt candidate of this work item. -/
theorem measurePreserving_condSwap {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ν : Fin N → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (σ : Fin N → Bool) :
    MeasurePreserving
      (fun w : (Fin N → E) × (Fin N → E) =>
        (fun i => if σ i then w.1 i else w.2 i,
         fun i => if σ i then w.2 i else w.1 i))
      ((Measure.pi ν).prod (Measure.pi ν))
      ((Measure.pi ν).prod (Measure.pi ν)) := by
  classical
  set e := MeasurableEquiv.arrowProdEquivProdArrow E E (Fin N) with he_def
  have he : MeasurePreserving e (Measure.pi fun i => (ν i).prod (ν i))
      ((Measure.pi ν).prod (Measure.pi ν)) :=
    measurePreserving_arrowProdEquivProdArrow E E (Fin N) ν ν
  have hh : ∀ i, MeasurePreserving (fun p : E × E => if σ i then p else Prod.swap p)
      ((ν i).prod (ν i)) ((ν i).prod (ν i)) := by
    intro i
    by_cases hσ : σ i
    · simpa [hσ] using! MeasurePreserving.id ((ν i).prod (ν i))
    · simpa [hσ] using Measure.measurePreserving_swap (μ := ν i) (ν := ν i)
  have hH : MeasurePreserving
      (fun (u : Fin N → E × E) i => if σ i then u i else Prod.swap (u i))
      (Measure.pi fun i => (ν i).prod (ν i)) (Measure.pi fun i => (ν i).prod (ν i)) :=
    measurePreserving_pi _ _ hh
  have hcomp := he.comp (hH.comp (MeasurePreserving.symm e he))
  have hFeq : (fun w : (Fin N → E) × (Fin N → E) =>
        (fun i => if σ i then w.1 i else w.2 i, fun i => if σ i then w.2 i else w.1 i))
      = ⇑e ∘ ((fun (u : Fin N → E × E) i => if σ i then u i else Prod.swap (u i)) ∘ ⇑e.symm) := by
    funext w
    have h1 : (⇑e ∘ ((fun (u : Fin N → E × E) i => if σ i then u i else Prod.swap (u i))
          ∘ ⇑e.symm)) w
        = (fun i => (if σ i then (w.1 i, w.2 i) else Prod.swap (w.1 i, w.2 i)).1,
           fun i => (if σ i then (w.1 i, w.2 i) else Prod.swap (w.1 i, w.2 i)).2) := rfl
    rw [h1]
    refine Prod.ext ?_ ?_
    · funext i; rcases hσ : σ i with _ | _ <;> simp [hσ]
    · funext i; rcases hσ : σ i with _ | _ <;> simp [hσ]
  rw [hFeq]
  exact hcomp

/-- **The flip identity** (HDP §6.3, proof of Lemma 6.3.2): for a fixed sign
pattern `c ∈ {±1}^N`, `(cᵢ(Xᵢ − Xᵢ'))ᵢ =ᵈ (Xᵢ − Xᵢ')ᵢ`, hence the expected
norms of the signed and unsigned difference sums agree. Pure change of
variables — no integrability hypotheses needed. -/
theorem integral_flip_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    (ν : Fin N → Measure E) [∀ i, IsProbabilityMeasure (ν i)] {c : Fin N → ℝ}
    -- USER-INPUT: fixed deterministic sign pattern; HDP §6.3 Lemma 6.3.2 proof
    (hc : ∀ i, c i = 1 ∨ c i = -1) :
    ∫ w, ‖∑ i, c i • (w.1 i - w.2 i)‖ ∂((Measure.pi ν).prod (Measure.pi ν))
      = ∫ w, ‖∑ i, (w.1 i - w.2 i)‖ ∂((Measure.pi ν).prod (Measure.pi ν)) := by
  classical
  set μ := (Measure.pi ν).prod (Measure.pi ν) with hμ
  set σ : Fin N → Bool := fun i => if c i = 1 then true else false with hσdef
  have hσtrue : ∀ i, c i = 1 → σ i = true := fun i h => by simp [hσdef, h]
  have hσfalse : ∀ i, c i = -1 → σ i = false := fun i h => by
    simp only [hσdef]; rw [if_neg (by rw [h]; norm_num)]
  have hF := measurePreserving_condSwap ν σ
  set F := (fun w : (Fin N → E) × (Fin N → E) =>
      (fun i => if σ i then w.1 i else w.2 i, fun i => if σ i then w.2 i else w.1 i))
    with hFdef
  set g : (Fin N → E) × (Fin N → E) → ℝ := fun w => ‖∑ i, (w.1 i - w.2 i)‖ with hgdef
  have hg_meas : AEStronglyMeasurable g μ := by
    refine (Measurable.norm ?_).aestronglyMeasurable
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact ((measurable_pi_apply i).comp measurable_fst).sub
      ((measurable_pi_apply i).comp measurable_snd)
  have hcomp_eq : ∀ w, g (F w) = ‖∑ i, c i • (w.1 i - w.2 i)‖ := by
    intro w
    simp only [hgdef, hFdef]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases hc i with hci | hci
    · rw [hσtrue i hci, hci]; simp
    · rw [hσfalse i hci, hci]; simp [neg_smul]
  have hFμ : MeasurePreserving F μ μ := hF
  have hmap : ∫ w, g w ∂μ = ∫ w, g (F w) ∂μ := by
    conv_lhs => rw [← hFμ.map_eq]
    exact integral_map hFμ.measurable.aemeasurable (hFμ.map_eq.symm ▸ hg_meas)
  rw [hmap]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  exact (hcomp_eq w).symm

end StatLean.ConcentrationInequalities
