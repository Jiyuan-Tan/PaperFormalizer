module
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Conditional distributions under a product-form density tilt

Let `ρ` be a measure on a product `𝓤 × 𝓣` (with `𝓤` standard Borel) and let
$$P = \rho \cdot \bigl(g(u)\,k(t)\bigr)$$
be the measure obtained from `ρ` by a density that **factorises** into a `u`-part and a
`t`-part. The `t`-part reweights only the second marginal, so it cancels from every
conditional law: the conditional distribution of `U` given `T = t` under `P` is the
*normalised `g`-tilt* of the conditional distribution under `ρ`,
$$P(\mathrm du \mid T = t) \;=\; \frac{g(u)\,\rho(\mathrm du \mid T = t)}
    {\int g \, \mathrm d\rho(\cdot \mid T = t)} ,$$
for `P`-almost every value `t` of the conditioning variable.

This is the engine behind **conditional exponential families**: in a multiparameter
exponential family with sufficient statistic `T` and interest statistic `U`, the density
relative to a fixed base measure factorises exactly in this way (the nuisance parameters
enter only through `k`), so the conditional law of `U` given `T = t` depends on the
interest parameter alone. Everything about conditional tests — similar regions, Neyman
structure, the conditional construction of unbiased tests — is downstream of this single
cancellation.

## Main results

* `condTiltNormalizer` — the conditional normalising constant `t ↦ ∫ g dρ(· | T = t)`.
* `measurable_condTiltNormalizer` — its measurability in `t`.
* `condTiltNormalizer_pos_lt_top_ae` — it is strictly positive and finite for almost every
  `t` under the tilted measure.
* `condDistrib_fst_withDensity_tilt` — the tilt identity above, as an almost-everywhere
  equality of the two `condDistrib` kernels.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.4 (UMP Unbiased Tests for Multiparameter Exponential Families),
supporting material for Lemma 4.4.1: conditional distributions under a product-form density
tilt. (`TSH4 §4.4 Lem 4.4.1`.)

**Proof formalization notes.**
* Densities are `ℝ≥0∞`-valued (`g k : 𝓤 → ℝ≥0∞`, `𝓣 → ℝ≥0∞`), matching
  `MeasureTheory.Measure.withDensity` natively and avoiding `ENNReal.ofReal` bookkeeping;
  a real nonnegative density is fed in as `ENNReal.ofReal ∘ p`.
* Mathlib's `condDistrib` is only defined for finite measures, so `ρ` and the tilted
  measure `P` are assumed finite. The σ-finite case reduces to this one by exhausting
  `𝓤 × 𝓣` along an increasing sequence of finite pieces and using a.e.-uniqueness of the
  disintegration; that reduction is *not* formalised here — the finite case is what the
  conditional-test applications use (all measures involved are probability measures).
* Neither the positivity nor the finiteness of the normaliser is a hypothesis: both are
  consequences of `P` being finite and are isolated in
  `condTiltNormalizer_pos_lt_top_ae`. Where the normaliser vanishes or blows up, the
  tilted second marginal puts no mass, so the a.e. statement is unaffected.
* The proof route is `Measure.compProd_map_condDistrib` in both directions: expand `P` as
  `(P.map Prod.snd) ⊗ₘ condDistrib Prod.fst Prod.snd P`, expand the right-hand side the
  same way from `ρ`, and conclude by a.e.-uniqueness of the disintegration
  (`Measure.eq_condKernel_of_measure_eq_compProd`-style), the two composed measures being
  equal by `lintegral_withDensity` on rectangles.
* `P` is a variable constrained by the equation `hP` rather than a literal
  `ρ.withDensity …` in the statement, so that the finiteness instance for `P` can be
  supplied by the caller.

**Bibliographic comments.** Conditional probability given a σ-algebra is due to
A. N. Kolmogorov, *Grundbegriffe der Wahrscheinlichkeitsrechnung*, Springer, 1933;
existence of *regular* conditional distributions on standard Borel spaces is due to
J. L. Doob, *Stochastic Processes*, Wiley, 1953, Ch. I §9, building on V. A. Rokhlin's
theory of Lebesgue spaces ("On the fundamental ideas of measure theory," *Mat. Sbornik*
**25** (1949), 107–150). The statistical use of the cancellation formalised here — the
conditional law of the interest statistic given a sufficient statistic, and the resulting
similar regions — goes back to J. Neyman ("Sur la vérification des hypothèses statistiques
composées," *Bull. Soc. Math. France* **63** (1935), 246–266) and E. L. Lehmann and
H. Scheffé ("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10**
(1950), 305–340).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {𝓤 𝓣 : Type*} [MeasurableSpace 𝓤] [StandardBorelSpace 𝓤] [Nonempty 𝓤]
  [MeasurableSpace 𝓣]

/-- The **conditional normalising constant** of a `u`-density `g` with respect to a measure
`ρ` on `𝓤 × 𝓣`: the mass of `g` under the conditional law of the first coordinate given
that the second coordinate equals `t`,
`C(t) = ∫ g(u) ρ(du | T = t)`.

Values `0` and `∞` are permitted by the definition; both occur only on a null set of `t`
for the tilted measure (`condTiltNormalizer_pos_lt_top_ae`). -/
noncomputable def condTiltNormalizer (ρ : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    (g : 𝓤 → ℝ≥0∞) (t : 𝓣) : ℝ≥0∞ :=
  ∫⁻ u, g u ∂(condDistrib Prod.fst Prod.snd ρ t)

/-- The conditional normalising constant is a measurable function of the conditioning
value. Consequence of the joint measurability of a kernel's `lintegral`
(`ProbabilityTheory.Kernel.measurable_lintegral`). -/
lemma measurable_condTiltNormalizer (ρ : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    {g : 𝓤 → ℝ≥0∞}
    -- USER-INPUT: the `u`-density is measurable.
    (hg : Measurable g) :
    Measurable (condTiltNormalizer ρ g) :=
  hg.lintegral_kernel

/-- In `ℝ≥0∞`, `a⁻¹ * a ≤ 1` for every `a` (equal to `1` when `0 < a < ∞`, and to `0` at the two
degenerate values). Used to bound the total mass of the normalised `g`-tilt kernel by `1`. -/
private lemma condTilt_inv_mul_le_one (a : ℝ≥0∞) : a⁻¹ * a ≤ 1 := by
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  rcases eq_or_ne a ⊤ with h' | h'
  · simp [h']
  · rw [ENNReal.inv_mul_cancel h h']

/-- Pointwise algebraic identity behind the tilt cancellation: for a measure `μ` on `Ω`, writing
`C = ∫ g dμ`, the `F`-weighted mass of `g` equals `C` times the `F`-weighted mass of the normalised
tilt `C⁻¹ · g`. Both degenerate values `C = 0` and `C = ∞` are handled (using finiteness of
`c · C`), which is why this holds `ρ_T`-almost everywhere and not just where `0 < C < ∞`. -/
private lemma condTilt_integrand_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {g F : Ω → ℝ≥0∞} (hg : Measurable g) (hF : Measurable F) (c : ℝ≥0∞)
    (hfin : c * (∫⁻ u, g u ∂μ) < ⊤) :
    ∫⁻ u, g u * c * F u ∂μ
      = (c * (∫⁻ u, g u ∂μ)) * ∫⁻ u, ((∫⁻ u, g u ∂μ)⁻¹ * g u) * F u ∂μ := by
  set C := ∫⁻ u, g u ∂μ with hCdef
  have hG : ∫⁻ u, (C⁻¹ * g u) * F u ∂μ = C⁻¹ * ∫⁻ u, g u * F u ∂μ := by
    rw [← lintegral_const_mul C⁻¹ (hg.fun_mul hF)]
    exact lintegral_congr fun u => by rw [mul_assoc]
  have hL : ∫⁻ u, g u * c * F u ∂μ = c * ∫⁻ u, g u * F u ∂μ := by
    rw [← lintegral_const_mul c (hg.fun_mul hF)]
    exact lintegral_congr fun u => by rw [mul_comm (g u) c, mul_assoc]
  rw [hL, hG]
  set G := ∫⁻ u, g u * F u ∂μ with hGdef
  rcases eq_or_ne C 0 with hC0 | hC0
  · have hgae : g =ᵐ[μ] 0 := (lintegral_eq_zero_iff hg).mp hC0
    have hG0 : G = 0 :=
      (lintegral_eq_zero_iff (hg.mul hF)).mpr (by filter_upwards [hgae] with u hu; simp [hu])
    rw [hG0, hC0]; simp
  rcases eq_or_ne C ⊤ with hCtop | hCtop
  · have hc0 : c = 0 := by
      by_contra hc
      rw [hCtop, ENNReal.mul_top hc] at hfin
      exact absurd hfin (lt_irrefl _)
    rw [hc0]; simp
  · rw [← mul_assoc, mul_assoc c C C⁻¹, ENNReal.mul_inv_cancel hC0 hCtop, mul_one]

/-- Master disintegration identity: integrating a measurable `F` against `ρ` equals integrating
its swapped section against the conditional law of the first coordinate given the second, averaged
over the second marginal. This is `Measure.compProd_map_condDistrib` composed with the swap. -/
private lemma lintegral_condDistrib_swap (ρ : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    {F : 𝓤 × 𝓣 → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂ρ
      = ∫⁻ t, ∫⁻ u, F (u, t) ∂(condDistrib Prod.fst Prod.snd ρ t) ∂(ρ.map Prod.snd) := by
  have hswap : (ρ.map Prod.snd) ⊗ₘ condDistrib Prod.fst Prod.snd ρ
      = ρ.map fun a => (Prod.snd a, Prod.fst a) :=
    compProd_map_condDistrib measurable_fst.aemeasurable
  have hmap : Measurable fun a : 𝓤 × 𝓣 => (Prod.snd a, Prod.fst a) := by fun_prop
  have hmeas : Measurable fun q : 𝓣 × 𝓤 => F (q.2, q.1) := by fun_prop
  calc ∫⁻ p, F p ∂ρ
      = ∫⁻ q, F (q.2, q.1) ∂(ρ.map fun a => (Prod.snd a, Prod.fst a)) := by
        rw [lintegral_map hmeas hmap]
    _ = ∫⁻ q, F (q.2, q.1) ∂((ρ.map Prod.snd) ⊗ₘ condDistrib Prod.fst Prod.snd ρ) := by
        rw [hswap]
    _ = ∫⁻ t, ∫⁻ u, F (u, t) ∂(condDistrib Prod.fst Prod.snd ρ t) ∂(ρ.map Prod.snd) :=
        Measure.lintegral_compProd hmeas

/-- The second marginal of the product-form tilt `ρ · (g(u) k(t))` is the `t`-marginal of `ρ`
reweighted by `k(t)·C(t)`, with `C` the conditional normaliser. Key structural identity behind both
the positivity/finiteness and the cancellation. -/
private lemma map_snd_withDensity_tilt (ρ : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    {g : 𝓤 → ℝ≥0∞} {k : 𝓣 → ℝ≥0∞} (hg : Measurable g) (hk : Measurable k) :
    (ρ.withDensity fun p => g p.1 * k p.2).map Prod.snd
      = (ρ.map Prod.snd).withDensity fun t => k t * condTiltNormalizer ρ g t := by
  have hdens : Measurable fun p : 𝓤 × 𝓣 => g p.1 * k p.2 := by fun_prop
  have hkC : Measurable fun t => k t * condTiltNormalizer ρ g t :=
    hk.mul (measurable_condTiltNormalizer ρ hg)
  ext B hB
  rw [Measure.map_apply measurable_snd hB, withDensity_apply _ (measurable_snd hB),
    ← lintegral_indicator (measurable_snd hB) (fun p => g p.1 * k p.2),
    lintegral_condDistrib_swap ρ (hdens.indicator (measurable_snd hB)),
    withDensity_apply _ hB, ← lintegral_indicator hB (fun t => k t * condTiltNormalizer ρ g t)]
  refine lintegral_congr fun t => ?_
  by_cases htB : t ∈ B
  · have hind : ∀ u, (Prod.snd ⁻¹' B).indicator (fun p => g p.1 * k p.2) (u, t) = g u * k t :=
      fun u => Set.indicator_of_mem (Set.mem_preimage.mpr htB) _
    simp only [hind]
    rw [lintegral_mul_const _ hg, Set.indicator_of_mem htB]
    exact mul_comm _ _
  · have hind : ∀ u, (Prod.snd ⁻¹' B).indicator (fun p => g p.1 * k p.2) (u, t) = 0 :=
      fun u => Set.indicator_of_notMem (fun h => htB (Set.mem_preimage.mp h)) _
    simp only [hind, lintegral_zero, Set.indicator_of_notMem htB]

/-- Under the tilted measure, the conditional normalising constant is strictly positive and
finite almost everywhere in the conditioning variable.

Positivity: on `{C = 0}` the `g`-tilt contributes no mass, so the second marginal of the
tilted measure vanishes there. Finiteness: the total mass of the tilted measure is
`∫ k(t) C(t) dρ_T(t)`, which is finite by assumption, so `k · C < ∞` almost everywhere,
and the tilted second marginal is carried by `{k > 0}`. -/
lemma condTiltNormalizer_pos_lt_top_ae (ρ P : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    [IsFiniteMeasure P] {g : 𝓤 → ℝ≥0∞} {k : 𝓣 → ℝ≥0∞}
    -- USER-INPUT: the `u`-density is measurable.
    (hg : Measurable g)
    -- USER-INPUT: the `t`-density is measurable.
    (hk : Measurable k)
    -- USER-INPUT: `P` is the product-form tilt of `ρ`.
    (hP : P = ρ.withDensity fun p => g p.1 * k p.2) :
    ∀ᵐ t ∂(P.map Prod.snd),
      0 < condTiltNormalizer ρ g t ∧ condTiltNormalizer ρ g t < ⊤ := by
  have hC := measurable_condTiltNormalizer ρ hg
  have hMS : P.map Prod.snd
      = (ρ.map Prod.snd).withDensity fun t => k t * condTiltNormalizer ρ g t := by
    rw [hP]; exact map_snd_withDensity_tilt ρ hg hk
  -- The total `k·C` mass is finite (it is the mass of `P`), so `k·C < ∞` a.e. on `ρ_T`.
  have hfin : ∀ᵐ t ∂(ρ.map Prod.snd), k t * condTiltNormalizer ρ g t < ⊤ := by
    refine ae_lt_top (hk.mul hC) ?_
    have hmass : ∫⁻ t, k t * condTiltNormalizer ρ g t ∂(ρ.map Prod.snd)
        = (P.map Prod.snd) Set.univ := by
      rw [hMS, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [hmass]; exact measure_ne_top _ _
  rw [hMS, ae_withDensity_iff (hk.fun_mul hC)]
  filter_upwards [hfin] with t htfin hne0
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne (condTiltNormalizer ρ g t) 0 with h | h
    · exact (hne0 (by rw [h, mul_zero])).elim
    · exact pos_iff_ne_zero.mpr h
  · rcases eq_or_ne (condTiltNormalizer ρ g t) ⊤ with h | h
    · exfalso
      have hk0 : k t ≠ 0 := fun hk0 => hne0 (by rw [hk0, zero_mul])
      rw [h, ENNReal.mul_top hk0] at htfin
      exact absurd htfin (lt_irrefl _)
    · exact lt_top_iff_ne_top.mpr h

/-- **Conditional law under a product-form tilt.**

If `P = ρ · (g(u) k(t))`, then for `P`-almost every value `t` of the second coordinate the
conditional law of the first coordinate given the second is the `g`-tilt of the
corresponding conditional law under `ρ`, renormalised:
$$P(\cdot \mid T = t) \;=\; C(t)^{-1}\,\bigl(g \cdot \rho(\cdot \mid T = t)\bigr),
  \qquad C(t) = \int g \,\mathrm d\rho(\cdot \mid T = t).$$

The `t`-factor `k` has disappeared: it changes the marginal law of `T` but not the
conditional law of `U` given `T`. -/
theorem condDistrib_fst_withDensity_tilt (ρ P : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    [IsFiniteMeasure P] {g : 𝓤 → ℝ≥0∞} {k : 𝓣 → ℝ≥0∞}
    -- USER-INPUT: the `u`-density is measurable.
    (hg : Measurable g)
    -- USER-INPUT: the `t`-density is measurable.
    (hk : Measurable k)
    -- USER-INPUT: `P` is the product-form tilt of `ρ`.
    (hP : P = ρ.withDensity fun p => g p.1 * k p.2) :
    ∀ᵐ t ∂(P.map Prod.snd),
      condDistrib Prod.fst Prod.snd P t
        = (condTiltNormalizer ρ g t)⁻¹ •
            ((condDistrib Prod.fst Prod.snd ρ t).withDensity g) := by
  have hC := measurable_condTiltNormalizer ρ hg
  have hd : Measurable (Function.uncurry fun t u => (condTiltNormalizer ρ g t)⁻¹ * g u) := by
    have hrw : (Function.uncurry fun t u => (condTiltNormalizer ρ g t)⁻¹ * g u)
        = fun p : 𝓣 × 𝓤 => (condTiltNormalizer ρ g p.1)⁻¹ * g p.2 := rfl
    rw [hrw]; exact ((hC.inv).comp measurable_fst).mul (hg.comp measurable_snd)
  set κρ := condDistrib Prod.fst Prod.snd ρ with hκρ
  set cand : Kernel 𝓣 𝓤 := Kernel.withDensity κρ (fun t u => (condTiltNormalizer ρ g t)⁻¹ * g u)
    with hcand
  haveI hcandFin : IsFiniteKernel cand := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun t => ?_⟩⟩
    rw [hcand, Kernel.withDensity_apply' _ hd, Measure.restrict_univ, lintegral_const_mul _ hg]
    exact condTilt_inv_mul_le_one _
  have hMS : P.map Prod.snd
      = (ρ.map Prod.snd).withDensity fun t => k t * condTiltNormalizer ρ g t := by
    rw [hP]; exact map_snd_withDensity_tilt ρ hg hk
  have hfin_ae : ∀ᵐ t ∂(ρ.map Prod.snd), k t * condTiltNormalizer ρ g t < ⊤ := by
    refine ae_lt_top (hk.mul hC) ?_
    have hmass : ∫⁻ t, k t * condTiltNormalizer ρ g t ∂(ρ.map Prod.snd)
        = (P.map Prod.snd) Set.univ := by
      rw [hMS, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [hmass]; exact measure_ne_top _ _
  have hfst : (P.map fun a => (Prod.snd a, Prod.fst a)).fst = P.map Prod.snd :=
    Measure.fst_map_prodMk measurable_fst
  -- The candidate kernel disintegrates `P` (swapped); this is where Target 2's cancellation enters.
  have hcompProd : (P.map fun a => (Prod.snd a, Prod.fst a)) = (P.map Prod.snd) ⊗ₘ cand := by
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    have hFswap : Measurable fun p : 𝓤 × 𝓣 => F (p.2, p.1) := by fun_prop
    have hLHS : ∫⁻ z, F z ∂(P.map fun a => (Prod.snd a, Prod.fst a))
        = ∫⁻ t, ∫⁻ u, g u * k t * F (t, u) ∂(κρ t) ∂(ρ.map Prod.snd) := by
      rw [lintegral_map hF (by fun_prop : Measurable fun a : 𝓤 × 𝓣 => (Prod.snd a, Prod.fst a)),
        hP, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hFswap]
      simp only [Pi.mul_apply]
      rw [lintegral_condDistrib_swap ρ
        (show Measurable fun p : 𝓤 × 𝓣 => g p.1 * k p.2 * F (p.2, p.1) by fun_prop)]
    have hRHS : ∫⁻ z, F z ∂((P.map Prod.snd) ⊗ₘ cand)
        = ∫⁻ t, (k t * condTiltNormalizer ρ g t)
            * ∫⁻ u, ((condTiltNormalizer ρ g t)⁻¹ * g u) * F (t, u) ∂(κρ t)
            ∂(ρ.map Prod.snd) := by
      rw [Measure.lintegral_compProd hF, hMS,
        lintegral_withDensity_eq_lintegral_mul _ (hk.fun_mul hC) hF.lintegral_kernel_prod_right']
      simp only [Pi.mul_apply]
      refine lintegral_congr fun t => ?_
      congr 1
      rw [hcand, Kernel.lintegral_withDensity κρ hd t
        (show Measurable fun u => F (t, u) from hF.comp measurable_prodMk_left)]
    rw [hLHS, hRHS]
    refine lintegral_congr_ae ?_
    filter_upwards [hfin_ae] with t htfin
    exact condTilt_integrand_eq (κρ t) hg (hF.comp measurable_prodMk_left) (k t) htfin
  haveI : IsFiniteMeasure (P.map fun a => (Prod.snd a, Prod.fst a)) := by
    rw [hcompProd]; infer_instance
  have hκeq : (P.map fun a => (Prod.snd a, Prod.fst a))
      = (P.map fun a => (Prod.snd a, Prod.fst a)).fst ⊗ₘ cand := by
    rw [hfst]; exact hcompProd
  have huniq := eq_condKernel_of_measure_eq_compProd cand hκeq
  rw [hfst] at huniq
  filter_upwards [huniq] with t ht
  have hden : (fun u => (condTiltNormalizer ρ g t)⁻¹ * g u)
      = (condTiltNormalizer ρ g t)⁻¹ • g := by funext u; simp [smul_eq_mul]
  rw [show condDistrib Prod.fst Prod.snd P
        = (P.map fun a => (Prod.snd a, Prod.fst a)).condKernel from by rw [condDistrib],
      ← ht, hcand, Kernel.withDensity_apply _ hd, hden, withDensity_smul _ hg]

end StatLean.HypothesisTesting
