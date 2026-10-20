module
public import StatLean.Bayesian.DoobConsistency.Defs
public import StatLean.Bayesian.DoobConsistency.Basic
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Function.FactorsThrough

@[expose] public section

/-!
# Accessibility: the parameter is a measurable function of the data sequence

The measure-theoretic heart of Doob's consistency theorem, the parameter-recovery identity: under
identifiability,
there is a measurable `g : 𝓧^ℕ → Θ` with `g(X₁, X₂, …) = Θ̄` almost surely under the joint
law. vdV proves this via "accessible functions" and the monotone-class Lemmas 10.12/10.13;
here the retraction is constructed explicitly, absorbing both lemmas:

* `exists_countable_measure_determining` — a countable measure-determining family of sets
  in a standard Borel space (countably generated σ-algebra; π-system uniqueness);
* `empirical_freq_ae_tendsto` — the strong law for the empirical frequencies
  `n⁻¹ #{i < n : Xᵢ ∈ A} → K θ (A)`, `K θ`-iid-a.s.;
* `exists_measurable_retraction` — the headline the parameter-recovery identity: the map
  `F : θ ↦ (K θ (Aₘ))ₘ ∈ ℝ^ℕ` is measurable and injective (identifiability +
  determining family), hence a measurable embedding by Lusin–Souslin; composing a
  measurable retraction of `F` with the empirical-limit map recovers `Θ̄` from the data
  a.s.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.4, proof of
Theorem 10.10, pp. 149–150 (accessible functions; the strong law step), and p. 151,
Lemmas 10.12–10.13 (absorbed by the explicit construction).

**Proof formalization notes.** Lusin–Souslin is `Measurable.measurableEmbedding` (injective
Borel maps between standard Borel spaces are embeddings); the retraction is assembled from
`MeasurableEmbedding.measurableSet_range` and `measurable_rangeSplitting`, with a default
value off the range (`[Nonempty Θ]`). The lift of the per-`θ` a.s. statement to the joint
law is `Measure.ae_compProd_of_ae_ae` (the convergence event is jointly measurable —
countably many measurable conditions). The empirical-limit map is made globally defined via
`limsup`-type expressions, measurable by countable operations.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- **A countable measure-determining family** in a standard Borel space: countably many
measurable sets such that two probability measures agreeing on all of them are equal
(countable generating π-system + `ext_of_generate_finite`). -/
theorem exists_countable_measure_determining (𝓧 : Type*) [MeasurableSpace 𝓧]
    [StandardBorelSpace 𝓧] :
    ∃ A : ℕ → Set 𝓧, (∀ m, MeasurableSet (A m)) ∧
      ∀ (P Q : Measure 𝓧), IsProbabilityMeasure P → IsProbabilityMeasure Q →
        (∀ m, P (A m) = Q (A m)) → P = Q := by
  classical
  -- a countable generating sequence, closed under finite intersections
  set b : ℕ → Set 𝓧 := MeasurableSpace.natGeneratingSequence 𝓧 with hb
  set e : ℕ → Finset ℕ := fun n => (Encodable.decode n).getD ∅ with he
  set A : ℕ → Set 𝓧 := fun n => ⋂ i ∈ (e n : Set ℕ), b i with hAdef
  have hesurj : ∀ s : Finset ℕ, e (Encodable.encode s) = s := by
    intro s; simp [he]
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact MeasurableSet.biInter (Finset.countable_toSet _) fun i _ =>
      MeasurableSpace.measurableSet_natGeneratingSequence i
  have hpi : IsPiSystem (Set.range A) := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ -
    refine ⟨Encodable.encode (e n ∪ e m), ?_⟩
    simp only [hAdef, hesurj, Finset.coe_union, Set.biInter_union]
  have hgen : (inferInstance : MeasurableSpace 𝓧)
      = MeasurableSpace.generateFrom (Set.range A) := by
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
    · refine le_trans (le_of_eq
        (MeasurableSpace.generateFrom_natGeneratingSequence 𝓧).symm)
        (MeasurableSpace.generateFrom_mono ?_)
      rintro _ ⟨i, rfl⟩
      exact ⟨Encodable.encode ({i} : Finset ℕ), by simp [hAdef, hesurj, hb]⟩
    · rintro _ ⟨n, rfl⟩
      exact hAmeas n
  refine ⟨A, hAmeas, fun P Q hP hQ hPQ => ?_⟩
  haveI := hP
  haveI := hQ
  refine ext_of_generate_finite (Set.range A) hgen hpi ?_ (by simp)
  rintro _ ⟨n, rfl⟩
  exact hPQ n

/-- **The strong law for empirical frequencies**: for every `θ` and measurable `A`,
`K θ`-iid-almost-surely the empirical frequency of `A` among the first `n` observations
converges to `(K θ A).toReal`. -/
theorem empirical_freq_ae_tendsto (K : Kernel Θ 𝓧) [IsMarkovKernel K] (θ : Θ)
    {A : Set 𝓧}
    -- LEAN-ONLY: measurable event (regularity)
    (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => K θ),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, A.indicator 1 (ω i))
        atTop (𝓝 (K θ A).toReal) := by
  classical
  have hind : Measurable (A.indicator (1 : 𝓧 → ℝ)) := measurable_one.indicator hA
  set μ : Measure (ℕ → 𝓧) := Measure.infinitePi fun _ : ℕ => K θ with hμ
  set X : ℕ → (ℕ → 𝓧) → ℝ := fun i ω => A.indicator (1 : 𝓧 → ℝ) (ω i) with hX
  have hXmeas : ∀ i, Measurable (X i) := fun i => hind.comp (measurable_pi_apply i)
  have hmapeval : ∀ i : ℕ, μ.map (fun ω : ℕ → 𝓧 => ω i) = K θ := fun i =>
    Measure.infinitePi_map_eval _ i
  have hmap : ∀ i, μ.map (X i) = (K θ).map (A.indicator (1 : 𝓧 → ℝ)) := by
    intro i
    rw [show X i = (A.indicator (1 : 𝓧 → ℝ)) ∘ (fun ω : ℕ → 𝓧 => ω i) from rfl,
      ← Measure.map_map hind (measurable_pi_apply i), hmapeval i]
  have hindep : iIndepFun X μ :=
    ProbabilityTheory.iIndepFun_infinitePi (Ω := fun _ : ℕ => 𝓧) (P := fun _ : ℕ => K θ)
      (X := fun _ : ℕ => A.indicator (1 : 𝓧 → ℝ)) fun _ => hind
  have hX0 : X 0 = ((fun ω : ℕ → 𝓧 => ω 0) ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext ω; simp [hX, Set.indicator_apply]
  have hint : Integrable (X 0) μ := by
    rw [hX0]
    exact (integrable_const _).indicator (hA.preimage (measurable_pi_apply 0))
  have hmean : ∫ ω, X 0 ω ∂μ = (K θ A).toReal := by
    rw [hX0, integral_indicator_const _ (hA.preimage (measurable_pi_apply 0)),
      measureReal_def, ← Measure.map_apply (measurable_pi_apply 0) hA, hmapeval 0]
    simp
  have hlln := ProbabilityTheory.strong_law_ae X hint (fun i j hij => hindep.indepFun hij)
    (fun i => ⟨(hXmeas i).aemeasurable, (hXmeas 0).aemeasurable, by rw [hmap i, hmap 0]⟩)
  rw [hmean] at hlln
  filter_upwards [hlln] with ω hω
  simpa only [smul_eq_mul] using hω

/-- **The parameter-recovery identity**: under identifiability (`θ ↦ K θ` injective), with `𝓧`
standard
Borel and `Θ` standard Borel and nonempty, there is a measurable `g : 𝓧^ℕ → Θ` recovering
the parameter from the data sequence almost surely under the joint law. -/
theorem exists_measurable_retraction [StandardBorelSpace Θ] [Nonempty Θ]
    [StandardBorelSpace 𝓧]
    (K : Kernel Θ 𝓧) [IsMarkovKernel K]
    -- USER-INPUT: identifiability, `P_θ ≠ P_{θ'}` for `θ ≠ θ'`; vdV §10.20
    (hK_inj : Function.Injective fun θ => K θ)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    ∃ g : (ℕ → 𝓧) → Θ, Measurable g ∧
      ∀ᵐ ω ∂(doobJoint K π), g ω.1 = ω.2 := by
  classical
  obtain ⟨A, hAmeas, hAdet⟩ := exists_countable_measure_determining 𝓧
  -- the moment map `θ ↦ (K θ (Aₘ))ₘ`, measurable and injective by identifiability
  set F : Θ → (ℕ → ℝ) := fun θ m => (K θ (A m)).toReal with hF
  have hFmeas : Measurable F :=
    measurable_pi_lambda _ fun m => (K.measurable_coe (hAmeas m)).ennreal_toReal
  have hFinj : Function.Injective F := by
    intro θ θ' h
    refine hK_inj (hAdet (K θ) (K θ') inferInstance inferInstance fun m => ?_)
    have hm : (K θ (A m)).toReal = (K θ' (A m)).toReal := congrFun h m
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hm
  have hFemb : MeasurableEmbedding F := hFmeas.measurableEmbedding hFinj
  obtain ⟨Finv, hFinvmeas, hFinv⟩ :=
    hFemb.exists_measurable_extend (g := (id : Θ → Θ)) measurable_id fun _ => inferInstance
  -- the empirical-limit map, globally defined by `limsup`
  set E : (ℕ → 𝓧) → (ℕ → ℝ) := fun ω m =>
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (A m).indicator 1 (ω i)) atTop
    with hE
  have hEmeas : Measurable E := by
    refine measurable_pi_lambda _ fun m => Measurable.limsup fun n => ?_
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_one.indicator (hAmeas m)).comp (measurable_pi_apply i))
  refine ⟨Finv ∘ E, hFinvmeas.comp hEmeas, ?_⟩
  -- the strong law identifies the empirical limits with `F θ`, `K θ`-iid-a.s.
  have hae : ∀ θ : Θ, ∀ᵐ ω ∂(iidSeqKernel K θ), E ω = F θ := by
    intro θ
    rw [iidSeqKernel_apply]
    have hm : ∀ m : ℕ, ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => K θ), E ω m = F θ m := by
      intro m
      filter_upwards [empirical_freq_ae_tendsto K θ (hAmeas m)] with ω hω
      exact hω.limsup_eq
    filter_upwards [(ae_all_iff (ι := ℕ)).2 hm] with ω hω
    exact funext hω
  have hS : MeasurableSet {ω : (ℕ → 𝓧) × Θ | E ω.1 = F ω.2} :=
    measurableSet_eq_fun (hEmeas.comp measurable_fst) (hFmeas.comp measurable_snd)
  have h1 : ∀ᵐ ω ∂(doobJoint K π), E ω.1 = F ω.2 := by
    rw [doobJoint, ae_map_iff measurable_swap.aemeasurable hS]
    exact Measure.ae_compProd_of_ae_ae (measurable_swap hS) (ae_of_all _ hae)
  filter_upwards [h1] with ω hω
  change Finv (E ω.1) = ω.2
  rw [hω]
  exact congrFun hFinv ω.2

end StatLean.Bayesian
