module
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Probability.Notation

@[expose] public section

/-!
# The natural statistic of an exponential family is itself exponentially distributed

If `X` follows an exponential family with natural statistic `T`, then `T(X)` follows an
exponential family on the statistic's own scale, with the *identity* as natural statistic, the
push-forward of the reference measure as reference measure, and the *same* log-partition
function:
$$ \frac{dP^T_\eta}{d(\nu \circ T^{-1})}(t)
   \;=\; \exp\bigl(\langle \eta, t\rangle - A(\eta)\bigr). $$
This is why all inference about `η` may be carried out on the statistic's scale, and it is
the reduction under which completeness of `T` is proved.

* `ExpFamily.statFamily` — the exponential family carried by the natural statistic;
* `ExpFamily.map_stat_P` — the law of `T` under `P_η` is the corresponding member;
* `ExpFamily.natSet_statFamily` — the two families share their natural parameter set;
* `ExpFamily.logPartition_statFamily` — and their log-partition function.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), Theorem 5.17 (the natural statistic is itself exponentially
distributed). (`TPE2 §1.5 Thm 5.17`.)

**Proof formalization notes.**
* `map_stat_P` is stated for **every** `η`, not only for natural parameters: off the natural
  parameter set both sides are the zero measure, since `natSet_statFamily` shows the two
  families become undefined simultaneously. Keeping the statement unconditional means
  consumers never carry a membership side condition through a push-forward.
* The proof is the observation that the tilting density `x ↦ exp⟨η, T x⟩` factors through `T`,
  so tilting commutes with the push-forward along `T`: on a measurable set `S`,
  `∫_{T⁻¹S} exp⟨η, T x⟩ dν = ∫_S exp⟨η, t⟩ d(ν ∘ T⁻¹)` by `setLIntegral_map`, and the two
  normalizers agree for the same reason — which is exactly `logPartition_statFamily`.
* Combining `map_stat_P` with the i.i.d. product family `ExpFamily.pow` of
  `ExponentialFamily.Basic` gives the classical corollary that a sum `∑ᵢ T(Xᵢ)` of
  independent natural statistics from a common one-parameter family is again exponentially
  distributed: apply `map_stat_P` to `E.pow n`, whose natural statistic is that sum.

**Bibliographic comments.** That the natural statistic of an exponential family is itself
exponentially distributed, and that the class is therefore closed under convolution of
independent components, is part of the classical theory: R. A. Fisher ("Two new properties of
mathematical likelihood," *Proc. R. Soc. Lond. A* **144** (1934), 285–307), G. Darmois ("Sur
les lois de probabilité à estimation exhaustive," *C. R. Acad. Sci. Paris* **200** (1935),
1265–1266), B. O. Koopman ("On distributions admitting a sufficient statistic," *Trans. Amer.
Math. Soc.* **39** (1936), 399–409), E. J. G. Pitman ("Sufficient statistics and intrinsic
accuracy," *Proc. Camb. Phil. Soc.* **32** (1936), 567–579); see also O. Barndorff-Nielsen
(*Information and Exponential Families in Statistical Theory*, Wiley, 1978, Ch. 8).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

namespace ExpFamily

/-- The **exponential family carried by the natural statistic**: the reference measure is the
push-forward of `E.base` along `E.stat`, and the natural statistic is the identity. The
members of this family are the laws of `E.stat` under the members of `E`
(`ExpFamily.map_stat_P`). -/
noncomputable def statFamily (E : ExpFamily 𝓧 V) : ExpFamily V V :=
  ⟨E.base.map E.stat, id, measurable_id⟩

variable [OpensMeasurableSpace V]

/-- The tilting integrand `t ↦ exp⟨η, t⟩` on the statistic's own scale is measurable. -/
private theorem measurable_exp_inner_id (η : V) : Measurable fun t : V => Real.exp ⟪η, t⟫_ℝ :=
  (continuous_const.inner continuous_id).measurable.exp

/-- **The natural statistic is exponentially distributed**: the law of `T` under `P_η` is the
member of the statistic's own exponential family at the same natural parameter. -/
theorem map_stat_P (E : ExpFamily 𝓧 V) (η : V) :
    (E.P η).map E.stat = E.statFamily.P η := by
  have hZ : ∫ t, Real.exp ⟪η, t⟫_ℝ ∂(E.base.map E.stat)
      = ∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base :=
    integral_map E.stat_meas.aemeasurable (measurable_exp_inner_id η).aestronglyMeasurable
  ext S hS
  rw [show E.P η = E.base.tilted (fun x => ⟪η, E.stat x⟫_ℝ) from rfl,
    Measure.map_apply E.stat_meas hS, tilted_apply' _ _ (E.stat_meas hS),
    show E.statFamily.P η = (E.base.map E.stat).tilted (fun t => ⟪η, t⟫_ℝ) from rfl,
    tilted_apply' _ _ hS,
    setLIntegral_map hS ((measurable_exp_inner_id η).div_const _).ennreal_ofReal E.stat_meas]
  simp only [hZ]

/-- The two families have the **same natural parameter set**. -/
theorem natSet_statFamily (E : ExpFamily 𝓧 V) : E.statFamily.natSet = E.natSet := by
  ext η
  simp only [ExpFamily.natSet, statFamily, id_eq, Set.mem_setOf_eq]
  exact integrable_map_measure (measurable_exp_inner_id η).aestronglyMeasurable
    E.stat_meas.aemeasurable

/-- The two families have the **same log-partition function**: the density of the law of `T`
is `exp(⟨η, t⟩ − A(η))` with the *original* `A`. -/
theorem logPartition_statFamily (E : ExpFamily 𝓧 V) :
    E.statFamily.logPartition = E.logPartition := by
  funext η
  simp only [ExpFamily.logPartition, statFamily, id_eq]
  congr 1
  exact integral_map E.stat_meas.aemeasurable (measurable_exp_inner_id η).aestronglyMeasurable

end ExpFamily

end StatLean.PointEstimation
