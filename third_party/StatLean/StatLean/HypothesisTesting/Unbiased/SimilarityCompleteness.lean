module
public import StatLean.HypothesisTesting.Tests.Defs
public import StatLean.PointEstimation.Sufficiency.Defs
public import StatLean.PointEstimation.Completeness.Defs
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-!
# Similar tests have Neyman structure iff the sufficient statistic is boundedly complete

Fix a boundary family `{P_θ : θ ∈ ω}` and a statistic `T` that is sufficient for it, with
θ-free conditional (Markov) kernel `Q`. A test `φ` is **similar** on `ω` when its power is
identically `α` there, and it has **Neyman structure** when its *conditional* size given
`T = t` equals `α`. Neyman structure always implies similarity (average the conditional
size); the converse — every similar test has Neyman structure — holds exactly when the
family of laws of `T` on `ω` is **boundedly complete**:

* `hasNeymanStructure_of_boundedlyComplete` — bounded completeness ⇒ every similar test has
  Neyman structure;
* `boundedlyComplete_of_forall_similar_hasNeymanStructure` — the converse.

This is the engine that reduces optimal similar tests to a family of one-dimensional
conditional Neyman–Pearson problems, one on each surface `T = t`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.3 (Similarity and Completeness), Theorem 4.3.2 (similar tests have
Neyman structure iff the sufficient statistic is boundedly complete), together with Theorem
4.3.1 (completeness of the natural statistic of a full-rank family). (`TSH4 §4.3 Thm 4.3.2,
Thm 4.3.1`.)

**Proof formalization notes.**
* *The almost-everywhere carrier.* The source states both the Neyman-structure condition and
  the completeness conclusion "a.e. `𝒫^T`", meaning: outside one exceptional set that is
  null under **every** member of the family. For a *fixed* function this is literally
  equivalent to the per-parameter form `∀ θ ∈ ω, ∀ᵐ t ∂(statLaw P T θ), …` used below
  (both say that `{t | …}` has measure zero under every `statLaw P T θ`, `θ ∈ ω`), so we
  quantify over every boundary parameter rather than fixing a single dominating reference
  measure `ν`. Instantiating `HasNeymanStructure` at `ν := statLaw P T θ` for each `θ ∈ ω`
  is exactly that reading.
* Sufficiency enters in the graph (`compProd`) form: `(P θ).map (x ↦ (T x, x)) =
  statLaw P T θ ⊗ₘ Q`. Beyond disintegration this pins `Q t` to the fibre `{x | T x = t}`
  for a.e. `t`, which the converse direction needs in order to compute the conditional size
  of a test of the form `c·f(T ·) + α`.
* Sufficiency and bounded completeness are required only on the boundary family, so both
  are stated for the restriction `fun θ : ω => …`; a sufficient statistic for the whole
  model restricts to one for any subfamily, but the converse is false for completeness, and
  the boundary subfamily is the one the applications complete.
* The converse direction needs `0 < α < 1`: the perturbation `φ = c·f(T ·) + α` used to
  contradict bounded completeness is a critical function only for `c ≤ min(α, 1−α)/M`,
  which is positive precisely then.

**Bibliographic comments.** Similar regions and the notion of Neyman structure are due to
J. Neyman ("Sur la vérification des hypothèses statistiques composées," *Bull. Soc. Math.
France* **63** (1935), 246–266; "Outline of a theory of statistical estimation based on the
classical theory of probability," *Phil. Trans. R. Soc. A* **236** (1937), 333–380). The
equivalence with (bounded) completeness of the sufficient statistic, and the completeness
concept itself, are due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and
unbiased estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236).
-/

open MeasureTheory ProbabilityTheory
open StatLean.PointEstimation

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 𝓣 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓣]

/-- **Bounded completeness ⇒ Neyman structure.**

If the laws of the sufficient statistic `T` over the boundary set `ω` form a boundedly
complete family, then every similar level-`α` test has Neyman structure: its conditional
size given `T = t` equals `α` for almost every `t`, under every boundary parameter.

Proof route: similarity says `∫ (φ − α) dP_θ = 0` for `θ ∈ ω`; disintegrating along `T`
turns this into `∫ ψ d(statLaw P T θ) = 0` for the bounded measurable function
`ψ t = ∫ φ dQ_t − α`; bounded completeness forces `ψ = 0` a.e. -/
theorem hasNeymanStructure_of_boundedlyComplete
    {P : Θ → Measure 𝓧} {ω : Set Θ} {T : 𝓧 → 𝓣} {Q : Kernel 𝓣 𝓧} {α : ℝ} {φ : 𝓧 → ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: `T` is measurable; part of the statistic's data
    (hT : Measurable T)
    -- USER-INPUT: `Q` is a Markov kernel — the θ-free conditional distribution given `T`
    (hQ : IsMarkovKernel Q)
    -- USER-INPUT: `T` is sufficient for the boundary family, in graph (disintegration) form
    (hsuff : ∀ θ ∈ ω, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- USER-INPUT: the laws of `T` over the boundary set are boundedly complete
    (hcomplete : IsBoundedlyCompleteFamily fun θ : ω => statLaw P T (θ : Θ))
    -- USER-INPUT: `φ` is a randomized test
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: `φ` is similar of size `α` on the boundary set
    (hsim : IsSimilar P ω α φ) :
    ∀ θ ∈ ω, HasNeymanStructure T Q (statLaw P T θ) α φ := by
  haveI := hQ
  haveI hstatprob : ∀ θ, IsProbabilityMeasure (statLaw P T θ) := fun θ => by
    rw [statLaw]; exact Measure.isProbabilityMeasure_map hT.aemeasurable
  -- the conditional size `t ↦ ∫ φ dQ_t`, measurable and bounded by `1`
  have hcond_meas : Measurable (fun t => ∫ x, φ x ∂(Q t)) :=
    (StronglyMeasurable.integral_kernel (κ := Q) hφ.1.stronglyMeasurable).measurable
  have hcond_bd : ∀ t, |∫ x, φ x ∂(Q t)| ≤ 1 := fun t => by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, φ x ∂(Q t)‖ ≤ 1 * (Q t Set.univ).toReal :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [(hφ.2 x).1], (hφ.2 x).2⟩)
      _ = 1 := by rw [measure_univ, ENNReal.toReal_one, mul_one]
  have hcond_int : ∀ θ, Integrable (fun t => ∫ x, φ x ∂(Q t)) (statLaw P T θ) := fun θ =>
    Integrable.of_bound hcond_meas.aestronglyMeasurable 1
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hcond_bd t)
  -- the disintegration identity `∫ φ dP_θ = ∫ (∫ φ dQ_t) d(statLaw)`
  have hdis : ∀ θ ∈ ω, ∫ x, φ x ∂(P θ) = ∫ t, (∫ x, φ x ∂(Q t)) ∂(statLaw P T θ) := by
    intro θ hθ
    have hfm : Measurable (fun x => (T x, x)) := hT.prodMk measurable_id
    have hgm : Measurable (fun z : 𝓣 × 𝓧 => φ z.2) := hφ.1.comp measurable_snd
    have hint' : Integrable (fun z : 𝓣 × 𝓧 => φ z.2) ((statLaw P T θ) ⊗ₘ Q) :=
      Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hφ.2 z.2).1], (hφ.2 z.2).2⟩)
    calc ∫ x, φ x ∂(P θ)
        = ∫ z, φ z.2 ∂((P θ).map (fun x => (T x, x))) :=
          (integral_map hfm.aemeasurable hgm.aestronglyMeasurable).symm
      _ = ∫ z, φ z.2 ∂((statLaw P T θ) ⊗ₘ Q) := by rw [hsuff θ hθ]
      _ = ∫ t, (∫ x, φ x ∂(Q t)) ∂(statLaw P T θ) := Measure.integral_compProd hint'
  -- the deviation `ψ t = ∫ φ dQ_t − α` integrates to `0` over every boundary law
  set ψ : 𝓣 → ℝ := fun t => (∫ x, φ x ∂(Q t)) - α with hψ_def
  have hψ_meas : Measurable ψ := hcond_meas.sub measurable_const
  have hψ_bdd : ∃ C, ∀ s, |ψ s| ≤ C := ⟨1 + |α|, fun t => by
    have h1 := hcond_bd t
    have h2 : |ψ t| ≤ |∫ x, φ x ∂(Q t)| + |α| := by
      change |(∫ x, φ x ∂(Q t)) - α| ≤ |∫ x, φ x ∂(Q t)| + |α|
      rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans_eq ?_; rw [abs_neg]
    linarith⟩
  have hzero : ∀ θ : ω, ∫ s, ψ s ∂(statLaw P T (θ : Θ)) = 0 := by
    intro θ
    have hθω : (θ : Θ) ∈ ω := θ.2
    simp only [hψ_def]
    rw [integral_sub (hcond_int _) (integrable_const α), integral_const,
      probReal_univ, smul_eq_mul, one_mul, ← hdis (θ : Θ) hθω]
    have hval : ∫ x, φ x ∂(P (θ : Θ)) = α := hsim (θ : Θ) hθω
    rw [hval, sub_self]
  -- bounded completeness forces `ψ = 0` a.e., i.e. conditional size `α`
  have hae := hcomplete ψ hψ_meas hψ_bdd hzero
  intro θ hθ
  filter_upwards [hae ⟨θ, hθ⟩] with t ht
  have : (∫ x, φ x ∂(Q t)) - α = 0 := ht
  linarith

/-- **Neyman structure for all similar tests ⇒ bounded completeness.**

Converse direction. Let `f` be bounded measurable with `∫ f d(statLaw) = 0` at every boundary
parameter. The perturbation `ψ = c·f(T ·) + α`, with `c = min(α, 1−α)/M` and `M` a positive
bound for `|f|`, is a critical function of power `c·∫ f d(statLaw) + α = α`, hence similar; so
`hall` gives `∀ᵐ t, ∫ ψ dQ_t = α`, i.e. `h t := ∫ f(T x) dQ_t = 0` for a.e. `t`.

It remains to identify `h` with `f`. Rather than exhibiting the fibre support of `Q` — which
would need the diagonal `{(t,x) | T x = t}` to be measurable, hence a standard-Borel structure
on `𝓣` absent from the signature — we test the graph identity `hsuff` against the *bounded
measurable weight* `g = h − f`: integrating `(t,x) ↦ g t · f (T x)` over
`(P θ).map (x ↦ (T x, x)) = statLaw ⊗ₘ Q` two ways gives `∫ g·f = ∫ g·h` over `statLaw`,
i.e. `∫ (h − f)² d(statLaw) = 0`, whence `h = f` a.e. Combining with `h = 0` a.e. yields
`f = 0` a.e. This route needs no hypothesis beyond the frozen signature. -/
theorem boundedlyComplete_of_forall_similar_hasNeymanStructure
    {P : Θ → Measure 𝓧} {ω : Set Θ} {T : 𝓧 → 𝓣} {Q : Kernel 𝓣 𝓧} {α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: `T` is measurable; part of the statistic's data
    (hT : Measurable T)
    -- USER-INPUT: `Q` is a Markov kernel — the θ-free conditional distribution given `T`
    (hQ : IsMarkovKernel Q)
    -- USER-INPUT: `T` is sufficient for the boundary family, in graph (disintegration) form
    (hsuff : ∀ θ ∈ ω, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; the perturbing test
    -- `c·f(T ·) + α` is a critical function only then, no scope change (α ∈ {0,1} is
    -- degenerate for testing)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: every similar level-`α` test has Neyman structure with respect to `T`
    (hall : ∀ φ : 𝓧 → ℝ, IsCriticalFn φ → IsSimilar P ω α φ →
      ∀ θ ∈ ω, HasNeymanStructure T Q (statLaw P T θ) α φ) :
    IsBoundedlyCompleteFamily fun θ : ω => statLaw P T (θ : Θ) := by
  haveI := hQ
  haveI hstatprob : ∀ θ, IsProbabilityMeasure (statLaw P T θ) := fun θ => by
    rw [statLaw]; exact Measure.isProbabilityMeasure_map hT.aemeasurable
  intro f hf hbd hzero θ
  obtain ⟨C₀, hC₀⟩ := hbd
  -- a strictly positive bound for `f`, so that the perturbation constant is well defined
  set M : ℝ := max C₀ 1 with hM_def
  have hM : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfM : ∀ s, |f s| ≤ M := fun s => (hC₀ s).trans (le_max_left _ _)
  have hfT : Measurable fun x => f (T x) := hf.comp hT
  -- the conditional average `h t = ∫ f(T x) dQ_t`, measurable and bounded by `M`
  set h : 𝓣 → ℝ := fun t => ∫ x, f (T x) ∂(Q t) with hh_def
  have hh_meas : Measurable h :=
    (StronglyMeasurable.integral_kernel (κ := Q) hfT.stronglyMeasurable).measurable
  have hh_bd : ∀ t, |h t| ≤ M := fun t => by
    rw [hh_def, ← Real.norm_eq_abs]
    calc ‖∫ x, f (T x) ∂(Q t)‖ ≤ M * (Q t Set.univ).toReal :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs]; exact hfM (T x))
      _ = M := by rw [measure_univ, ENNReal.toReal_one, mul_one]
  -- ## Step 1: the perturbation `ψ = c·(f∘T) + α` is a similar critical function
  set m : ℝ := min α (1 - α) with hm_def
  have hm : 0 < m := lt_min hα₀ (by linarith)
  have hmα : m ≤ α := min_le_left _ _
  have hmα' : m ≤ 1 - α := min_le_right _ _
  set c : ℝ := m / M with hc_def
  have hc : 0 < c := div_pos hm hM
  have hcM : c * M = m := by rw [hc_def]; field_simp
  set ψ : 𝓧 → ℝ := fun x => c * f (T x) + α with hψ_def
  have hcf_bd : ∀ x, |c * f (T x)| ≤ m := fun x => by
    rw [abs_mul, abs_of_pos hc]
    calc c * |f (T x)| ≤ c * M := by gcongr; exact hfM (T x)
      _ = m := hcM
  have hψ_crit : IsCriticalFn ψ := by
    refine ⟨(measurable_const.mul hfT).add measurable_const, fun x => ?_⟩
    have h1 := abs_le.mp (hcf_bd x)
    exact Set.mem_Icc.mpr ⟨by simp only [hψ_def]; linarith [h1.1],
      by simp only [hψ_def]; linarith [h1.2]⟩
  -- integrability of the perturbing summand against any probability measure
  have hcf_int : ∀ (μ : Measure 𝓧) [IsProbabilityMeasure μ],
      Integrable (fun x => c * f (T x)) μ := fun μ _ =>
    Integrable.of_bound (measurable_const.mul hfT).aestronglyMeasurable m
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hcf_bd x)
  have hψ_sim : IsSimilar P ω α ψ := by
    intro θ' hθ'
    have hmap : ∫ x, f (T x) ∂(P θ') = ∫ t, f t ∂(statLaw P T θ') := by
      rw [statLaw, integral_map hT.aemeasurable hf.aestronglyMeasurable]
    rw [power]
    simp only [hψ_def]
    rw [integral_add (hcf_int (P θ')) (integrable_const α), integral_const, probReal_univ,
      one_smul, integral_const_mul, hmap, hzero ⟨θ', hθ'⟩, mul_zero, zero_add]
  -- Neyman structure of `ψ` at the chosen boundary parameter forces `h = 0` a.e.
  have hns := hall ψ hψ_crit hψ_sim (θ : Θ) θ.2
  have hh0 : ∀ᵐ t ∂(statLaw P T (θ : Θ)), h t = 0 := by
    filter_upwards [hns] with t ht
    simp only [hψ_def] at ht
    rw [integral_add (hcf_int (Q t)) (integrable_const α), integral_const, probReal_univ,
      one_smul, integral_const_mul] at ht
    have : c * h t = 0 := by rw [hh_def]; linarith
    exact (mul_eq_zero.mp this).resolve_left hc.ne'
  -- ## Step 2: `h = f` a.e. — no fibre-support argument needed, only the graph identity
  -- tested against the bounded measurable weight `g = h − f`
  set ν : Measure 𝓣 := statLaw P T (θ : Θ) with hν_def
  set g : 𝓣 → ℝ := fun t => h t - f t with hg_def
  have hg_meas : Measurable g := hh_meas.sub hf
  have hg_bd : ∀ t, |g t| ≤ 2 * M := fun t => by
    rw [hg_def]
    calc |h t - f t| ≤ |h t| + |f t| := abs_sub _ _
      _ ≤ M + M := add_le_add (hh_bd t) (hfM t)
      _ = 2 * M := by ring
  have hFmeas : Measurable fun z : 𝓣 × 𝓧 => g z.1 * f (T z.2) :=
    (hg_meas.comp measurable_fst).mul (hfT.comp measurable_snd)
  have hFint : Integrable (fun z : 𝓣 × 𝓧 => g z.1 * f (T z.2)) (ν ⊗ₘ Q) :=
    Integrable.of_bound hFmeas.aestronglyMeasurable ((2 * M) * M) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hg_bd z.1) (hfM (T z.2)) (abs_nonneg _) (by positivity))
  -- the graph identity: integrating `g(t)·f(T x)` two ways
  have hchain : ∫ t, g t * f t ∂ν = ∫ t, g t * h t ∂ν := by
    have e1 : ∫ t, g t * f t ∂ν = ∫ x, g (T x) * f (T x) ∂(P (θ : Θ)) := by
      rw [hν_def, statLaw, integral_map hT.aemeasurable (hg_meas.fun_mul hf).aestronglyMeasurable]
    have e2 : ∫ x, g (T x) * f (T x) ∂(P (θ : Θ))
        = ∫ z, g z.1 * f (T z.2) ∂((P (θ : Θ)).map (fun x => (T x, x))) := by
      have hfm : Measurable (fun x => (T x, x)) := hT.prodMk measurable_id
      rw [integral_map hfm.aemeasurable hFmeas.aestronglyMeasurable]
    have e3 : ∫ z, g z.1 * f (T z.2) ∂((P (θ : Θ)).map (fun x => (T x, x)))
        = ∫ t, (∫ x, g t * f (T x) ∂(Q t)) ∂ν := by
      rw [hsuff (θ : Θ) θ.2, ← hν_def]; exact Measure.integral_compProd hFint
    have e4 : ∫ t, (∫ x, g t * f (T x) ∂(Q t)) ∂ν = ∫ t, g t * h t ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      rw [integral_const_mul]
    rw [e1, e2, e3, e4]
  -- bounded measurable products are integrable against the probability law `ν`
  have hgh_int : Integrable (fun t => g t * h t) ν :=
    Integrable.of_bound ((hg_meas.mul hh_meas)).aestronglyMeasurable ((2 * M) * M)
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hg_bd t) (hh_bd t) (abs_nonneg _) (by positivity))
  have hgf_int : Integrable (fun t => g t * f t) ν :=
    Integrable.of_bound ((hg_meas.mul hf)).aestronglyMeasurable ((2 * M) * M)
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hg_bd t) (hfM t) (abs_nonneg _) (by positivity))
  -- hence `∫ (h − f)² dν = 0`, so `h = f` a.e.
  have hsq : ∫ t, (g t) ^ 2 ∂ν = 0 := by
    have hrw : (fun t => (g t) ^ 2) = fun t => g t * h t - g t * f t := by
      funext t; rw [hg_def]; ring
    rw [hrw, integral_sub hgh_int hgf_int, ← hchain, sub_self]
  have hg0 : ∀ᵐ t ∂ν, g t = 0 := by
    have hsq_int : Integrable (fun t => (g t) ^ 2) ν := by
      have hrw : (fun t => (g t) ^ 2) = fun t => g t * h t - g t * f t := by
        funext t; rw [hg_def]; ring
      rw [hrw]; exact hgh_int.sub hgf_int
    have := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg (g t)) hsq_int).mp hsq
    filter_upwards [this] with t ht
    exact pow_eq_zero_iff two_ne_zero |>.mp ht
  -- ## Step 3: combine `h = 0` a.e. with `h − f = 0` a.e.
  filter_upwards [hh0, hg0] with t ht0 htg
  rw [hg_def] at htg
  simp only [Pi.zero_apply]
  linarith [ht0, htg]

end StatLean.HypothesisTesting
