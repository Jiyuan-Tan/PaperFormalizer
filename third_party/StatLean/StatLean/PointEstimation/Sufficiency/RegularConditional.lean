module
public import StatLean.PointEstimation.Sufficiency.Factorization
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Disintegration.CondCDF

@[expose] public section

/-!
# From per-event determinations to a θ-free regular conditional distribution

The definition of sufficiency only asks that *each* event `A` admit a determination of
`P_θ(A ∣ T = t)` free of `θ`. What decision theory actually uses is stronger: a single θ-free
Markov kernel `Q : S ⇝ 𝓧` which, for each fixed `t`, is a genuine probability measure and
which disintegrates the joint law of `(T(X), X)` under every member. On a standard Borel
sample space the two coincide.

* `hasSufficientKernel_of_isSufficient_dominated` — the **dominated** version: for a family
  dominated by a σ-finite measure on a standard Borel sample space, a sufficient statistic
  admits a θ-free reconstruction kernel. This is the version the rest of the area consumes.
* `hasSufficientKernel_of_isSufficient` — the general standard Borel version, without
  domination.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 2 (The Probability
Background), §2.6 (Sufficient Statistics), Theorem 2.6.1 (existence of a θ-free regular
conditional distribution given a sufficient statistic). (`TSH4 Thm 2.6.1`.)

**Proof formalization notes.**
* The dominated route avoids gluing per-event determinations altogether. Fix an equivalent
  countable mixture `ν` of members of the family and let `Q` be the conditional kernel of the
  graph law of `(T, id)` under `ν`, which exists on a standard Borel sample space
  (`MeasureTheory.Measure.condKernel`, requiring `[StandardBorelSpace 𝓧]` and `[Nonempty 𝓧]`
  on the *second* factor of the product; no condition on the value space `S` of the
  statistic). The Halmos–Savage criterion then shows that this single kernel disintegrates
  the graph law of *every* member: the density `dP_θ/dν` is a function of `T`, so tilting the
  disintegration of `ν` by it changes only the first marginal.
* `[Nonempty 𝓧]` is a technical requirement of Mathlib's disintegration API (a Markov kernel
  must have somewhere to put its mass) and is no restriction: the family consists of
  probability measures, so the sample space is nonempty whenever the parameter set is.
* The general (undominated) version genuinely needs the gluing argument: the per-`θ`
  disintegrations `Q_θ` agree only `statLaw P T θ`-almost everywhere, and for an uncountable
  parameter set no single `Q_θ` can serve (take `P θ = δ_θ` on `ℝ` with `T = id`: the kernel
  is pinned down at *every* point of `S`). The kernel is therefore built from the θ-free
  per-event determinations themselves, through the conditional distribution *functions*:
  `e := embeddingReal 𝓧` embeds the sample space into `ℝ`, the determinations `k q` of the
  half-lines `e ⁻¹' Iic q` (`q : ℚ`) form a θ-free rational CDF `f (·, t) q = (k q t).toReal`,
  `ProbabilityTheory.stieltjesOfMeasurableRat` repairs it off the bad set,
  `IsCondKernelCDF.toKernel` reads a Markov kernel `S ⇝ ℝ` off the repair, and
  `Kernel.borelMarkovFromReal` transports it back to `S ⇝ 𝓧`. Sufficiency enters exactly once,
  as the set-`lintegral` identity
  `∫⁻ b in B, k q b ∂(statLaw P T θ) = ρ_θ (B ×ˢ Iic q)` for the graph law `ρ_θ` of `(T, e)`,
  which is `IsRatCondKernelCDF.setIntegral` after the `ENNReal`-to-real passage. The
  almost-sure Stieltjes-point property is *imported* rather than reproved: it holds for
  Mathlib's `preCDF ρ_θ`, and `f` agrees with it `statLaw P T θ`-a.e. at every rational by
  uniqueness of set integrals, `ℚ` being countable. The `Unit`-indexed kernel API
  (`Kernel.const Unit ·`) is what carries the measure-level statement into the kernel-level
  disintegration lemmas, and `Measure.compProd` is definitionally the `Unit`-fibre of
  `Kernel.compProd`, which is how the conclusion comes back down.
* Both statements deliver the graph/compProd carrier `HasSufficientKernel` rather than a
  bare reconstruction identity, so that the fiber property of `Sufficiency.Basic` comes for
  free at the point of use.

**Bibliographic comments.** The existence of θ-free conditional distributions given a
sufficient statistic on Euclidean sample spaces is classical; the measure-theoretic treatment
for dominated families is due to P. R. Halmos and L. J. Savage ("Application of the
Radon–Nikodym theorem to the theory of sufficient statistics," *Ann. Math. Statist.* **20**
(1949), 225–241), and the decision-theoretic formulation, in which the reconstruction kernel
is the object of interest, to R. R. Bahadur ("Sufficiency and statistical decision
functions," *Ann. Math. Statist.* **25** (1954), 423–462; "Statistics and subfields," *Ann.
Math. Statist.* **26** (1955), 490–497).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- Tilting the first marginal of a compProd by a density of the first coordinate. -/
private theorem compProd_withDensity_left (μ : Measure S) [SFinite μ] (Q : Kernel S 𝓧)
    [IsSFiniteKernel Q] {w : S → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w) ⊗ₘ Q = (μ ⊗ₘ Q).withDensity (fun p => w p.1) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs, ← lintegral_indicator hs,
      Measure.lintegral_compProd
        ((show Measurable fun p : S × 𝓧 => w p.1 from hw.comp measurable_fst).indicator hs),
      lintegral_withDensity_eq_lintegral_mul _ hw (Kernel.measurable_kernel_prodMk_left hs)]
  refine lintegral_congr fun a => ?_
  rw [Pi.mul_apply]
  have hind : (fun x => s.indicator (fun p => w p.1) (a, x))
      = (Prod.mk a ⁻¹' s).indicator (fun _ => w a) := by
    funext x
    by_cases hx : (a, x) ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_preimage.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt Set.mem_preimage.mp hx)]
  rw [hind, lintegral_indicator_const (measurable_prodMk_left hs)]

/-- **Dominated existence of a θ-free reconstruction kernel.** On a standard Borel sample
space, a sufficient statistic for a family dominated by a σ-finite measure admits a single
θ-free Markov kernel disintegrating the graph law of `(T, id)` under every member. -/
theorem hasSufficientKernel_of_isSufficient_dominated [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model is dominated by the σ-finite measure `μ`; classical setup
    (hdom : ∀ θ, P θ ≪ μ)
    -- USER-INPUT: sufficiency of `T` in the per-event sense
    (hsuf : IsSufficient P T) :
    HasSufficientKernel P T := by
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · haveI : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary 𝓧)) :=
      Measure.dirac.isProbabilityMeasure
    exact ⟨Kernel.const S (Measure.dirac (Classical.arbitrary 𝓧)), inferInstance,
      fun θ => (hΘ.false θ).elim⟩
  obtain ⟨θs, c, ν, hν, hcpos, hcsum, hdomν, -⟩ :=
    exists_equivalent_countable_mixture P μ hdom
  haveI : IsProbabilityMeasure ν := ⟨by
    rw [hν, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hcsum⟩
  have he : Measurable (fun x => (T x, x)) := hT.prodMk measurable_id
  haveI : IsProbabilityMeasure (ν.map fun x => (T x, x)) :=
    Measure.isProbabilityMeasure_map he.aemeasurable
  have hρfst : (ν.map fun x => (T x, x)).fst = ν.map T :=
    Measure.fst_map_prodMk measurable_id
  set Q : Kernel S 𝓧 := (ν.map fun x => (T x, x)).condKernel with hQdef
  have hρcompProd : (ν.map T) ⊗ₘ Q = ν.map fun x => (T x, x) := by
    rw [hQdef, ← hρfst]; exact Measure.disintegrate _ _
  refine ⟨Q, Measure.instIsMarkovKernelCondKernel _, fun θ => ?_⟩
  obtain ⟨w, hw, hweq⟩ := rnDeriv_comp_of_isSufficient P hT θs c ν hν hdomν hsuf θ
  have hPθ : P θ = ν.withDensity (fun x => w (T x)) :=
    calc P θ = ν.withDensity ((P θ).rnDeriv ν) :=
          (Measure.withDensity_rnDeriv_eq (P θ) ν (hdomν θ)).symm
      _ = ν.withDensity (fun x => w (T x)) := withDensity_congr_ae hweq
  have hmapwd : (ν.withDensity (fun x => w (T x))).map (fun x => (T x, x))
      = (ν.map fun x => (T x, x)).withDensity (fun q => w q.1) := by
    refine Measure.ext fun C hC => ?_
    rw [Measure.map_apply he hC, withDensity_apply _ (he hC), withDensity_apply _ hC,
        setLIntegral_map hC (show Measurable fun q : S × 𝓧 => w q.1 from hw.comp measurable_fst) he]
  have hmapT : (ν.withDensity (fun x => w (T x))).map T = (ν.map T).withDensity w := by
    refine Measure.ext fun C hC => ?_
    rw [Measure.map_apply hT hC, withDensity_apply _ (hT hC), withDensity_apply _ hC,
        setLIntegral_map hC hw hT]
  have hstat : statLaw P T θ = (ν.map T).withDensity w := by rw [statLaw, hPθ, hmapT]
  calc (P θ).map (fun x => (T x, x))
      = (ν.map fun x => (T x, x)).withDensity (fun q => w q.1) := by rw [hPθ, hmapwd]
    _ = ((ν.map T) ⊗ₘ Q).withDensity (fun q => w q.1) := by rw [hρcompProd]
    _ = ((ν.map T).withDensity w) ⊗ₘ Q := (compProd_withDensity_left (ν.map T) Q hw).symm
    _ = (statLaw P T θ) ⊗ₘ Q := by rw [hstat]

private lemma kernel_fst_const {S' α : Type*} [MeasurableSpace S'] [MeasurableSpace α]
    (μ : Measure (S' × α)) :
    Kernel.fst (Kernel.const Unit μ) = Kernel.const Unit μ.fst := by
  ext u s hs
  rw [Kernel.fst_apply' _ _ hs, Kernel.const_apply, Kernel.const_apply, Measure.fst_apply hs]
  rfl

/-- **General existence of a θ-free reconstruction kernel** on a standard Borel sample space,
without any domination assumption.

The per-event determinations are glued into a single kernel through the conditional
distribution *functions*, not through any disintegration of a single member: the sample space
is embedded into `ℝ` by `e := embeddingReal 𝓧`, the determinations `k q` of the rational
half-lines `e ⁻¹' Iic q` assemble into a θ-free rational CDF `f (·, t) q = (k q t).toReal`,
`stieltjesOfMeasurableRat` repairs it off the bad set, and `borelMarkovFromReal` transports
the resulting Markov kernel `S ⇝ ℝ` back to `S ⇝ 𝓧`. The one place where a *single* member
enters is the almost-sure Stieltjes-point property, and there it is harmless: it is imported
from Mathlib's own rational CDF `preCDF (ρ θ)` of the graph law of `(T, e)` under that member,
to which `f` is a.e. equal at every rational (both have set-`lintegral` `ρ θ (B ×ˢ Iic q)`,
and `ℚ` is countable). The kernel itself never depends on the member. -/
theorem hasSufficientKernel_of_isSufficient [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- USER-INPUT: sufficiency of `T` in the per-event sense
    (hsuf : IsSufficient P T) :
    HasSufficientKernel P T := by
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · haveI : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary 𝓧)) :=
      Measure.dirac.isProbabilityMeasure
    exact ⟨Kernel.const S (Measure.dirac (Classical.arbitrary 𝓧)), inferInstance,
      fun θ => (hΘ.false θ).elim⟩
  -- the measurable embedding of the standard Borel sample space into `ℝ`
  have he : MeasurableEmbedding (embeddingReal 𝓧) := measurableEmbedding_embeddingReal 𝓧
  set e := embeddingReal 𝓧 with hedef
  have hemb : Measurable fun x => (T x, e x) := hT.prodMk he.measurable
  have hA : ∀ q : ℚ, MeasurableSet (e ⁻¹' (Set.Iic (q : ℝ))) :=
    fun _ => he.measurable measurableSet_Iic
  -- the θ-free determinations of the rational half-lines
  choose k hkm hk1 hk using fun q : ℚ => hsuf (hA q)
  -- the graph law of `(T, e)`, a measure on `S × ℝ`
  set ρ : Θ → Measure (S × ℝ) := fun θ => (P θ).map fun x => (T x, e x) with hρdef
  haveI hρprob : ∀ θ, IsProbabilityMeasure (ρ θ) :=
    fun θ => Measure.isProbabilityMeasure_map hemb.aemeasurable
  haveI hνprob : ∀ θ, IsProbabilityMeasure (statLaw P T θ) := fun θ => by
    unfold statLaw; exact Measure.isProbabilityMeasure_map hT.aemeasurable
  have hρfst : ∀ θ, (ρ θ).fst = statLaw P T θ :=
    fun _ => Measure.fst_map_prodMk he.measurable
  -- the defining identity of the determinations, read on the graph law
  have hkey : ∀ (θ : Θ) (q : ℚ) {B : Set S}, MeasurableSet B →
      ∫⁻ b in B, k q b ∂(statLaw P T θ) = ρ θ (B ×ˢ Set.Iic (q : ℝ)) := by
    intro θ q B hB
    rw [statLaw, setLIntegral_map hB (hkm q) hT, hρdef]
    simp only
    rw [Measure.map_apply hemb (hB.prod measurableSet_Iic), hk q θ hB]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, Set.mem_Iic]
    exact and_comm
  -- the θ-free rational conditional CDF
  set f : Unit × S → ℚ → ℝ := fun p q => (k q p.2).toReal with hfdef
  have hfapp : ∀ (p : Unit × S) (q : ℚ), f p q = (k q p.2).toReal := fun _ _ => rfl
  have hfm : Measurable f := by
    rw [measurable_pi_iff]
    exact fun q => ((hkm q).comp measurable_snd).ennreal_toReal
  have hf1 : ∀ (p : Unit × S) (q : ℚ), f p q ≤ 1 := by
    intro p q
    rw [hfapp]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hk1 q p.2)
  have hint : ∀ (θ : Θ) (q : ℚ) (a : Unit),
      Integrable (fun b : S => f (a, b) q) (statLaw P T θ) := by
    intro θ q a
    refine ⟨(((hkm q).ennreal_toReal).comp measurable_id).aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := 1) ?_
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hfapp]; exact ENNReal.toReal_nonneg)]
    exact hf1 (a, b) q
  -- the Stieltjes-point property, imported from Mathlib's own rational CDF of `ρ θ`
  have hstp : ∀ (θ : Θ) (a : Unit), ∀ᵐ b ∂(statLaw P T θ), IsRatStieltjesPoint f (a, b) := by
    intro θ a
    have hmain := (isRatCondKernelCDF_preCDF (ρ θ)).isRatStieltjesPoint_ae ()
    rw [Kernel.const_apply, hρfst θ] at hmain
    have hq : ∀ q : ℚ, k q =ᵐ[statLaw P T θ] preCDF (ρ θ) q := by
      intro q
      refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (hkm q) measurable_preCDF ?_
      intro B hB _
      rw [hkey θ q hB, ← hρfst θ, setLIntegral_preCDF_fst (ρ θ) q hB,
        Measure.IicSnd_apply _ _ hB]
    have hall : ∀ᵐ b ∂(statLaw P T θ), ∀ q : ℚ, k q b = preCDF (ρ θ) q b :=
      ae_all_iff.2 hq
    filter_upwards [hmain, hall] with b hb hball
    have hfun : f (a, b) = fun r : ℚ => (preCDF (ρ θ) r b).toReal := by
      funext r
      rw [hfapp, hball r]
    exact ⟨by rw [hfun]; exact hb.mono, by rw [hfun]; exact hb.tendsto_atTop_one,
      by rw [hfun]; exact hb.tendsto_atBot_zero, by rw [hfun]; exact hb.iInf_rat_gt_eq⟩
  -- `f` is a rational conditional kernel CDF of the graph law under *every* member
  have hrat : ∀ θ, IsRatCondKernelCDF f (Kernel.const Unit (ρ θ))
      (Kernel.const Unit (statLaw P T θ)) := by
    intro θ
    refine ⟨hfm, fun a => ?_, fun a q => ?_, fun a B hB q => ?_⟩
    · rw [Kernel.const_apply]; exact hstp θ a
    · rw [Kernel.const_apply]; exact hint θ q a
    · rw [Kernel.const_apply, Kernel.const_apply]
      simp only [hfapp]
      rw [integral_toReal ((hkm q).aemeasurable.restrict)
        (.of_forall fun b => lt_of_le_of_lt (hk1 q b) ENNReal.one_lt_top),
        hkey θ q hB, measureReal_def]
  -- the θ-free Stieltjes family and the kernel it defines
  set F : Unit × S → StieltjesFunction ℝ := stieltjesOfMeasurableRat f hfm with hFdef
  have hCDF : ∀ θ, IsCondKernelCDF F (Kernel.const Unit (ρ θ))
      (Kernel.const Unit (statLaw P T θ)) :=
    fun θ => isCondKernelCDF_stieltjesOfMeasurableRat (hrat θ)
  set η : Kernel (Unit × S) ℝ := (hCDF (Classical.arbitrary Θ)).toKernel F with hηdef
  haveI : IsMarkovKernel η := instIsMarkovKernel_toKernel
  have hcp : ∀ θ, (Kernel.const Unit (statLaw P T θ)) ⊗ₖ η = Kernel.const Unit (ρ θ) := by
    intro θ
    have h := compProd_toKernel (hCDF θ)
    rwa [show (hCDF θ).toKernel F = η from rfl] at h
  -- transport the real kernel back to the sample space
  refine ⟨Kernel.comap (Kernel.borelMarkovFromReal 𝓧 η) (fun s => ((), s))
    (measurable_const.prodMk measurable_id), inferInstance, fun θ => ?_⟩
  have hgraphfst : ((P θ).map fun x => (T x, x)).fst = statLaw P T θ :=
    Measure.fst_map_prodMk measurable_id'
  have hmain : Kernel.fst (Kernel.const Unit ((P θ).map fun x => (T x, x)))
      ⊗ₖ Kernel.borelMarkovFromReal 𝓧 η
      = Kernel.const Unit ((P θ).map fun x => (T x, x)) := by
    refine Kernel.compProd_fst_borelMarkovFromReal _ η ?_
    have hmapeq : Kernel.map (Kernel.const Unit ((P θ).map fun x => (T x, x)))
        (Prod.map (id : S → S) e) = Kernel.const Unit (ρ θ) := by
      rw [Kernel.map_const _ (measurable_id.prodMap he.measurable),
        Measure.map_map (measurable_id.prodMap he.measurable) (hT.prodMk measurable_id')]
      rfl
    rw [hmapeq, kernel_fst_const, hρfst θ]
    exact hcp θ
  rw [kernel_fst_const, hgraphfst] at hmain
  have hpm : Kernel.prodMkLeft Unit (Kernel.comap (Kernel.borelMarkovFromReal 𝓧 η)
      (fun s => ((), s)) (measurable_const.prodMk measurable_id))
      = Kernel.borelMarkovFromReal 𝓧 η := by
    ext p s hs
    rw [Kernel.prodMkLeft_apply, Kernel.comap_apply]
  calc (P θ).map (fun x => (T x, x))
      = (Kernel.const Unit (statLaw P T θ) ⊗ₖ Kernel.borelMarkovFromReal 𝓧 η) () := by
        rw [hmain, Kernel.const_apply]
    _ = statLaw P T θ ⊗ₘ Kernel.comap (Kernel.borelMarkovFromReal 𝓧 η) (fun s => ((), s))
          (measurable_const.prodMk measurable_id) := by
        rw [Measure.compProd, hpm]

end StatLean.PointEstimation
