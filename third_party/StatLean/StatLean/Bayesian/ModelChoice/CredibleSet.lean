module
public import StatLean.Bayesian.ModelChoice.Defs

@[expose] public section

/-!
# Credible sets — basic properties

Basic calculus of `γ`-credible set families (`IsCredibleSet post m C γ`: posterior mass of `C x`
is at least `1 − γ`, a.e. data): monotonicity in the level and in the sets, and the trivial
full-space family.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §2.3
(posterior intervals / highest posterior density regions), p. 32.

**Proof formalization notes.** All three lemmas are one-line filter/order arguments
(`tsub_le_tsub_left` for the level, `measure_mono` for the sets, `measure_univ` for the trivial
family — the last needs the posterior values to be probability measures, e.g. any Markov `post`).
The decision-theoretic refinement (HPD regions minimize volume at fixed credibility, Gelman §2.3) is a Batch-3 target recorded in `notes/bayesian/roadmap.md`.

**Bibliographic comments.** Credible regions are the Bayesian counterpart of Neyman's confidence
sets; the highest-posterior-density convention is systematized in G. E. P. Box and G. C. Tiao,
*Bayesian Inference in Statistical Analysis* (Addison-Wesley, 1973).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  {post : Kernel 𝓧 Θ} {m : Measure 𝓧} {C D : 𝓧 → Set Θ} {γ γ' : ℝ≥0∞}

/-- A `γ`-credible family is `γ'`-credible for any looser level `γ ≤ γ'`. -/
theorem IsCredibleSet.mono_level (h : IsCredibleSet post m C γ)
    -- USER-INPUT: the target level is looser; Gelman §2.3
    (hγ : γ ≤ γ') :
    IsCredibleSet post m C γ' := by
  filter_upwards [h] with x hx
  exact le_trans (tsub_le_tsub_left hγ 1) hx

/-- Enlarging the sets preserves credibility. -/
theorem IsCredibleSet.mono_set (h : IsCredibleSet post m C γ)
    -- USER-INPUT: pointwise enlargement of the credible sets; Gelman §2.3
    (hCD : ∀ x, C x ⊆ D x) :
    IsCredibleSet post m D γ := by
  filter_upwards [h] with x hx
  exact le_trans hx (measure_mono (hCD x))

/-- The full-space family is `γ`-credible at every level (for a Markov posterior kernel). -/
theorem isCredibleSet_univ [IsMarkovKernel post] (γ : ℝ≥0∞) :
    IsCredibleSet post m (fun _ => Set.univ) γ := by
  refine ae_of_all m fun x => ?_
  rw [measure_univ]
  exact tsub_le_self

end StatLean.Bayesian
