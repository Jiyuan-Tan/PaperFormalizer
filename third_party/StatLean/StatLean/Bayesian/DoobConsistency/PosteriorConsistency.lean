module
public import StatLean.Bayesian.DoobConsistency.PosteriorMartingale
public import StatLean.Bayesian.DoobConsistency.Accessible

@[expose] public section

/-!
# Doob's posterior consistency theorem

Assembly of Doob's consistency theorem: for an identifiable model on a standard Borel sample space
with a Polish parameter space, and **any** prior probability measure `π`, the posterior is
strongly consistent at `π`-almost every parameter. No smoothness, dominatedness, or
compactness is assumed.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.4 (Consistency), Theorem 10.10, p. 149 (statement), proof pp. 149–150.

**Proof formalization notes.** Combine `posterior_ae_tendsto_indicator` (Lévy upward, with
the retraction from `exists_measurable_retraction`) over a countable family of balls
(rational radii around a countable dense set of `Θ`), upgrade indicator convergence at the
true parameter to ball-mass convergence to one, and disintegrate the `doobJoint`-a.s.
statement back to `π`-a.e. `θ` with `K θ`-iid-a.s. data (Fubini for `compProd`,
`Measure.ae_ae_of_ae_compProd`). The statement is the ball form of consistency (equivalent
to vdV's weak convergence to `δ_θ` for point limits). vdV's Euclidean sample-space
assumption is generalized to standard Borel; his Lemmas 10.12/10.13 are absorbed into the
explicit retraction of `Accessible.lean`.

**Bibliographic comments.** J. L. Doob, *Application of the theory of martingales*, in *Le
Calcul des Probabilités et ses Applications*, Colloques Internationaux du CNRS **13**,
Paris, 1949, pp. 23–27 — the original martingale proof of posterior consistency off a null
set of parameters. The sharpness of the null-set caveat is discussed by P. Diaconis and
D. Freedman, *On the consistency of Bayes estimates*, Annals of Statistics **14** (1986),
1–26 (with discussion), who construct priors with large inconsistency sets; L. Schwartz,
*On Bayes procedures*, Zeitschrift für Wahrscheinlichkeitstheorie **4** (1965), 10–26,
gives the complementary everywhere-consistency theory under testing conditions.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- **Doob's consistency theorem.** Let `𝓧` be standard Borel, let `Θ` be a
Polish metric parameter space (Borel σ-algebra), and let the model `θ ↦ K θ` be
identifiable. Then for every prior probability measure `π`, the posterior is strongly
consistent at `π`-almost every `θ`: `K θ`-iid-almost-surely, the posterior mass of every
`ε`-ball around `θ` tends to one. -/
theorem doob_consistency [MetricSpace Θ] [PolishSpace Θ] [BorelSpace Θ] [Nonempty Θ]
    [StandardBorelSpace 𝓧]
    (K : Kernel Θ 𝓧) [IsMarkovKernel K]
    -- USER-INPUT: identifiability, `P_θ ≠ P_{θ'}` for `θ ≠ θ'`; vdV §10.20
    (hK_inj : Function.Injective fun θ => K θ)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    ∀ᵐ θ ∂π, StronglyConsistentAt K π θ := by
  classical
  obtain ⟨g, hgmeas, hg⟩ := exists_measurable_retraction K hK_inj π
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense Θ
  haveI : Countable ↥D := hDcount.to_subtype
  -- Lévy upward convergence for the countable family of balls with centres in `D` and
  -- rational radii
  have hball : ∀ p : ↥D × ℚ, ∀ᵐ ω ∂(doobJoint K π),
      Tendsto (fun n => (((iidKernel K n)†π) (doobData n ω)
          (Metric.ball (p.1 : Θ) (p.2 : ℝ))).toReal) atTop
        (𝓝 ((Metric.ball (p.1 : Θ) (p.2 : ℝ)).indicator (fun _ => (1 : ℝ)) ω.2)) := fun _ =>
    posterior_ae_tendsto_indicator K π ⟨g, hgmeas, hg⟩ Metric.isOpen_ball.measurableSet
  have hmain : ∀ᵐ ω ∂(doobJoint K π), ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ((iidKernel K n)†π) (doobData n ω) (Metric.ball ω.2 ε)) atTop
        (𝓝 1) := by
    filter_upwards [(ae_all_iff (ι := ↥D × ℚ)).2 hball] with ω hω ε hε
    -- a ball of the countable family squeezed between `ω.2` and `ball ω.2 ε`
    obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.mp (hDdense ω.2) (ε / 4) (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
    have hmem : ω.2 ∈ Metric.ball d (q : ℝ) := Metric.mem_ball.mpr (hd.trans hq1)
    have hsub : Metric.ball d (q : ℝ) ⊆ Metric.ball ω.2 ε := by
      refine Metric.ball_subset_ball' ?_
      rw [dist_comm]
      linarith
    have hconv : Tendsto (fun n => (((iidKernel K n)†π) (doobData n ω)
        (Metric.ball d (q : ℝ))).toReal) atTop
        (𝓝 ((Metric.ball d (q : ℝ)).indicator (fun _ => (1 : ℝ)) ω.2)) := hω (⟨d, hdD⟩, q)
    rw [Set.indicator_of_mem hmem] at hconv
    have hle1 : ∀ n : ℕ, (((iidKernel K n)†π) (doobData n ω) (Metric.ball d (q : ℝ))).toReal
        ≤ (((iidKernel K n)†π) (doobData n ω) (Metric.ball ω.2 ε)).toReal := fun n =>
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    have hle2 : ∀ n : ℕ, (((iidKernel K n)†π) (doobData n ω) (Metric.ball ω.2 ε)).toReal
        ≤ 1 := by
      intro n
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have hsq : Tendsto (fun n => (((iidKernel K n)†π) (doobData n ω)
        (Metric.ball ω.2 ε)).toReal) atTop (𝓝 1) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hconv tendsto_const_nhds hle1 hle2
    rw [← ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top _ _) ENNReal.one_ne_top]
    simpa using hsq
  -- disintegrate the joint statement back to `π`-a.e. `θ`
  simp only [doobJoint] at hmain
  have hfin := Measure.ae_ae_of_ae_compProd (ae_of_ae_map measurable_swap.aemeasurable hmain)
  filter_upwards [hfin] with θ hθ
  simp only [iidSeqKernel_apply] at hθ
  exact hθ

end StatLean.Bayesian
