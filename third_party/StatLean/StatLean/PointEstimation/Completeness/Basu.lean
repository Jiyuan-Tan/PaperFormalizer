module
public import StatLean.PointEstimation.Completeness.Defs
public import StatLean.PointEstimation.Sufficiency.Defs
public import StatLean.PointEstimation.Sufficiency.Basic
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Independence of a complete sufficient statistic from an ancillary statistic

If `T` is a boundedly complete sufficient statistic for a family of probability measures and
`V` is ancillary — its law does not depend on the parameter — then `T` and `V` are
independent under every member of the family. The argument is short and is the reason
completeness is the right strengthening of sufficiency: for a measurable set `A`, the
conditional probability `η_A(t) = P(V ∈ A ∣ T = t)` is parameter-free by sufficiency, its
mean `E_θ[η_A(T)] = P_θ(V ∈ A)` is parameter-free by ancillarity, and completeness applied to
`η_A − P(V ∈ A)` — a function bounded by `1` — forces `η_A` to be constant almost everywhere.
Constancy of the conditional probability is exactly independence.

* `IsCompleteFamily.boundedlyComplete` / `completeStat_boundedlyCompleteStat` — completeness
  implies bounded completeness for families of probability measures;
* `indepFun_of_boundedlyComplete_sufficient` — the independence theorem.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), Theorem 6.21 (Basu: a complete sufficient statistic is independent of
every ancillary statistic). (`TPE2 §1.6 Thm 6.21`.)

**Proof formalization notes.**
* The theorem is stated with **bounded** completeness, which is all the proof consumes: the
  test function `η_A − P(V ∈ A)` is bounded by `1`. Stating it this way makes it strictly
  more applicable than the version assuming full completeness, and
  `completeStat_boundedlyCompleteStat` bridges the two whenever a caller has the stronger
  hypothesis.
* Sufficiency is taken in the kernel (graph/compProd) form. That form is what delivers the
  single θ-free determination `η_A(t) = Q t (V ⁻¹' A)` of the conditional probability
  simultaneously for all `A`, together with the fibre property that makes
  `E_θ[η_A(T)] = P_θ(V ∈ A)` a plain disintegration identity rather than an a.e. juggling
  argument.
* Both statistics are required measurable; `T` because the completeness hypothesis is about
  the family of its laws, and `V` because `Q t (V ⁻¹' A)` must be a measurable function of
  `t`. Neither codomain needs any structure beyond a measurable space, so the ancillary
  statistic is allowed to take values in a space different from the sufficient statistic's.
* `completeStat_boundedlyCompleteStat` is the specialization of `IsCompleteFamily.
  boundedlyComplete` to laws of a statistic; measurability of the statistic enters only to
  know that each pushed-forward law is again a probability measure, under which a bounded
  measurable function is automatically integrable.

**Bibliographic comments.** Completeness and its role in unbiased estimation and similar
regions are due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased
estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236). The independence
result proved here is due to D. Basu ("On statistics independent of a complete sufficient
statistic," *Sankhyā* **15** (1955), 377–380).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S S' : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S] [MeasurableSpace S']

/-- For a family of **probability** measures, completeness implies bounded completeness: a
bounded measurable function is integrable against every member. -/
theorem IsCompleteFamily.boundedlyComplete {Q : Θ → Measure S}
    -- LEAN-ONLY: the laws are probability measures, so bounded ⇒ integrable; the implication
    -- fails for infinite measures and the classical statement is always about probabilities
    [∀ θ, IsProbabilityMeasure (Q θ)]
    -- USER-INPUT: completeness of the family
    (h : IsCompleteFamily Q) :
    IsBoundedlyCompleteFamily Q := by
  intro f hf hbound hzero
  obtain ⟨C, hC⟩ := hbound
  refine h f hf (fun θ => ?_) hzero
  refine ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
  exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- Statistic form: a complete statistic of a family of probability measures is boundedly
complete. -/
theorem completeStat_boundedlyCompleteStat {P : Θ → Measure 𝓧} {T : 𝓧 → S}
    -- LEAN-ONLY: the model consists of probability measures; see
    -- `IsCompleteFamily.boundedlyComplete`
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the statistic is measurable
    (hT : Measurable T)
    -- USER-INPUT: completeness of the statistic
    (h : IsCompleteStat P T) :
    IsBoundedlyCompleteStat P T := by
  haveI : ∀ θ, IsProbabilityMeasure ((P θ).map T) :=
    fun θ => Measure.isProbabilityMeasure_map hT.aemeasurable
  exact h.boundedlyComplete

/-- **Basu's theorem**: a boundedly complete sufficient statistic is independent of every
ancillary statistic, under every member of the family. -/
theorem indepFun_of_boundedlyComplete_sufficient {P : Θ → Measure 𝓧} {T : 𝓧 → S} {V : 𝓧 → S'}
    -- LEAN-ONLY: the model consists of probability measures; independence is a statement
    -- about probabilities and the disintegration argument needs total mass one
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the sufficient statistic is measurable
    (hT : Measurable T)
    -- USER-INPUT: the ancillary statistic is measurable
    (hV : Measurable V)
    -- USER-INPUT: sufficiency of `T`, in the θ-free Markov-kernel form
    (hsuff : HasSufficientKernel P T)
    -- USER-INPUT: bounded completeness of `T`; the classical hypothesis, and all the proof
    -- uses (the test function is a conditional probability, bounded by one)
    (hcomp : IsBoundedlyCompleteStat P T)
    -- USER-INPUT: ancillarity of `V`: its law does not depend on the parameter
    (hanc : IsAncillary P V) :
    ∀ θ, IndepFun T V (P θ) := by
  obtain ⟨Q, hQ, hgraph⟩ := hsuff
  haveI := hQ
  have hsl : ∀ θ', IsProbabilityMeasure ((P θ').map T) :=
    fun θ' => Measure.isProbabilityMeasure_map hT.aemeasurable
  intro θ
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro B A hB hA
  -- the bounded real test function `f t = Q t (V ∈ A)`
  set f : S → ℝ := fun t => (Q t (V ⁻¹' A)).toReal with hf
  have hfmeas : Measurable f := (Q.measurable_coe (hV hA)).ennreal_toReal
  have hf0 : ∀ t, 0 ≤ f t := fun t => by simp only [hf]; exact ENNReal.toReal_nonneg
  have hf1 : ∀ t, f t ≤ 1 := fun t => by
    simp only [hf]; rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  set c : ℝ := (P θ (V ⁻¹' A)).toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c ≤ 1 := by
    rw [hc, ← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  -- ancillarity makes `P_θ(V ∈ A)` parameter-free
  have hanc' : ∀ θ', P θ' (V ⁻¹' A) = P θ (V ⁻¹' A) := by
    intro θ'
    rw [← Measure.map_apply hV hA, ← Measure.map_apply hV hA, hanc θ' θ]
  -- reconstruction identity, `ℝ≥0∞`- and `ℝ`-level
  have hlint : ∀ θ', ∫⁻ t, Q t (V ⁻¹' A) ∂((P θ').map T) = P θ' (V ⁻¹' A) := by
    intro θ'
    calc ∫⁻ t, Q t (V ⁻¹' A) ∂((P θ').map T)
        = (Q ∘ₘ (statLaw P T θ')) (V ⁻¹' A) :=
          (Measure.bind_apply (hV hA) Q.aemeasurable).symm
      _ = P θ' (V ⁻¹' A) := by rw [statLaw_snd P hT hgraph θ']
  have hrecon : ∀ θ', ∫ s, f s ∂((P θ').map T) = (P θ' (V ⁻¹' A)).toReal := by
    intro θ'
    simp only [hf]
    rw [integral_toReal (Q.measurable_coe (hV hA)).aemeasurable
      (Filter.Eventually.of_forall fun t => measure_lt_top (Q t) _), hlint θ']
  -- the test function `f - c` has identically zero mean
  have hzero' : ∀ θ', ∫ s, (f s - c) ∂((P θ').map T) = 0 := by
    intro θ'
    haveI := hsl θ'
    have hfint : Integrable f ((P θ').map T) :=
      ⟨hfmeas.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := 1)
          (Filter.Eventually.of_forall fun t => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]; exact hf1 t)⟩
    rw [integral_sub hfint (integrable_const c), hrecon θ', integral_const,
      probReal_univ, one_smul, hanc' θ', hc, sub_self]
  -- bounded completeness forces the conditional probability to be constant a.e.
  have hae : (fun t => Q t (V ⁻¹' A)) =ᵐ[statLaw P T θ] fun _ => P θ (V ⁻¹' A) := by
    have hbc : (fun t => f t - c) =ᵐ[statLaw P T θ] 0 :=
      hcomp (fun t => f t - c) (hfmeas.sub measurable_const)
        ⟨1, fun t => abs_le.mpr ⟨by linarith [hf0 t, hc1], by linarith [hf1 t, hc0]⟩⟩ hzero' θ
    filter_upwards [hbc] with t ht
    simp only [Pi.zero_apply] at ht
    have hft : f t = c := sub_eq_zero.mp ht
    have h1 : Q t (V ⁻¹' A) = ENNReal.ofReal (f t) := by
      simp only [hf]; rw [ENNReal.ofReal_toReal (measure_ne_top (Q t) _)]
    rw [h1, hft, hc, ENNReal.ofReal_toReal (measure_ne_top (P θ) _)]
  -- assemble the product formula through the graph identity
  have hgm : Measurable (fun x : 𝓧 => (T x, x)) := hT.prodMk measurable_id
  have hpre : T ⁻¹' B ∩ V ⁻¹' A = (fun x => (T x, x)) ⁻¹' (B ×ˢ (V ⁻¹' A)) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
  haveI : IsProbabilityMeasure (statLaw P T θ) := hsl θ
  have key : P θ (T ⁻¹' B ∩ V ⁻¹' A) = ∫⁻ t in B, Q t (V ⁻¹' A) ∂(statLaw P T θ) := by
    rw [hpre, ← Measure.map_apply hgm (hB.prod (hV hA)), hgraph θ,
      Measure.compProd_apply_prod hB (hV hA)]
  calc P θ (T ⁻¹' B ∩ V ⁻¹' A)
      = ∫⁻ t in B, Q t (V ⁻¹' A) ∂(statLaw P T θ) := key
    _ = ∫⁻ _t in B, P θ (V ⁻¹' A) ∂(statLaw P T θ) :=
        lintegral_congr_ae (ae_restrict_of_ae hae)
    _ = P θ (V ⁻¹' A) * (statLaw P T θ) B := by rw [setLIntegral_const]
    _ = P θ (T ⁻¹' B) * P θ (V ⁻¹' A) := by
        rw [mul_comm]; congr 1; rw [statLaw, Measure.map_apply hT hB]

end StatLean.PointEstimation
