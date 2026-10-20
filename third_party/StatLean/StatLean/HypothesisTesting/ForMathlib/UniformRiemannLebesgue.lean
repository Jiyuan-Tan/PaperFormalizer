module
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-!
# Riemann–Lebesgue, uniformly over a family

The Riemann–Lebesgue lemma says that the oscillatory integral `∫ f(x) e^{isx} dx` of a fixed
`L¹` function tends to `0` as `|s| → ∞`. Several applications need the convergence to be
**uniform over a family of `L¹` functions** — most notably the multivariate Cramér condition
for a law carried by a curve, where the family is the set of projections of the law onto the
directions of a compact sphere.

Uniformity is false for an arbitrary family (translates `f(· − a)`, `a ∈ ℝ`, all have the same
modulus of transform, and the transform of a *single* function does not decay uniformly along
any family that is not relatively compact). It is true, and easy, on a **totally bounded**
subset of `L¹`: approximate every member of the family to within `ε/2` by one of finitely many
functions, apply Riemann–Lebesgue to each of those, and use that the transform is a contraction
from `L¹` to `L^∞`.

## Contents

* `fourierOsc` — the oscillatory integral `∫ e^{i x s} f(x) dx`, normalised exactly as `charFun`
  is, so that `charFun (volume.withDensity p) = fourierOsc p`;
* `tendsto_fourierOsc_cocompact` — the Riemann–Lebesgue lemma in this normalisation, obtained
  from Mathlib's `Real.tendsto_integral_exp_smul_cocompact` by the reparametrisation
  `s = −2πw`;
* `norm_fourierOsc_sub_le` — the contraction property `‖ℱf(s) − ℱg(s)‖ ≤ ‖f − g‖_{L¹}`,
  valid for every `s`;
* `eventually_norm_fourierOsc_le_of_totallyBounded` — **the headline**: Riemann–Lebesgue holds
  uniformly over any family admitting finite `ε`-nets in `L¹`;
* `exists_finset_l1Net_of_isCompact` — a family parametrised continuously (in `L¹`) by a
  compact set admits finite `ε`-nets;
* `eventually_norm_fourierOsc_le_of_isCompact` — the two combined, in the form applications
  consume;
* `quadPhaseInt`, `eventually_norm_quadPhaseInt_le` — the application to a **quadratic phase**:
  for a fixed `L¹` density `f`, `∫ f(y) e^{i(t₀y + t₁y²)} dy → 0` as `|t₀| → ∞`, uniformly over
  `|t₁| ≤ M`. This is the "linear regime" of the two-regime decomposition of the multivariate
  Cramér condition for a parabola-carried law;
* `autoCorr`, `sq_ofReal_norm_quadPhaseInt`, `exists_bound_norm_quadPhaseInt_large` — the
  complementary regime `|t₁| → ∞`, **uniformly in `t₀`**. This is *not* a Riemann–Lebesgue
  statement about the twists `e^{it₁y²}f` (they are not relatively compact in `L¹` over an
  unbounded set of `t₁`), and it is proved instead through the **autocorrelation identity**
  `|I|² = ∫ e^{i(t₀h + t₁h²)} ℱg_h(2t₁h) dh` with `g_h(z) = f(z + h)\overline{f(z)}`, which
  moves the oscillation into the *frequency* `2t₁h` of an ordinary Fourier transform and leaves
  `t₀` inside a unimodular factor;
* `exists_bound_norm_quadPhaseInt_of_integrable` — the two regimes combined, with no hypothesis
  on `f` beyond `f ∈ L¹`: `|∫ f(y)e^{i(t₀y + t₁y²)}dy| ≤ ε` once `|t₀| + |t₁|` is large.

## Proof formalization notes

* The `L¹`-continuity hypothesis of `exists_finset_l1Net_of_isCompact` is phrased elementarily,
  as `∀ δ > 0, ∃ U ∈ 𝓝[K] a, ∀ b ∈ U, ∫ ‖f b − f a‖ ≤ δ`, rather than through `MeasureTheory.Lp`
  and its quotient by a.e. equality. Nothing is lost — the applications produce exactly this
  statement, from dominated convergence — and it avoids having to lift a family of honest
  functions into the `Lp` quotient and back.
* The `ε`-net hypothesis is likewise stated as a `Finset` of *indices* rather than of `L¹`
  elements, which is what a finite subcover of a compact parameter set produces.

**Reference.** No textbook states the uniform form proved here; this is a technical brick. Its
consumers are the Cramér-condition hypotheses of the Edgeworth expansions in E. L. Lehmann and
J. P. Romano, *Testing Statistical Hypotheses*, 4th ed., Springer, Cham, 2022, §13.3 (Edgeworth
Expansions), where **Cramér's condition** is assumption (13.30) of Theorem 13.3.1 (p. 624) and
its multivariate analogue is the hypothesis of the studentized expansion (p. 627, referred there
to Hall, *The Bootstrap and Edgeworth Expansion*, 1992, Chapter 2); Lehmann–Romano assume the
condition rather than verify it. The classical single-function statement is the Riemann–Lebesgue lemma;
the use of a Cramér condition to control characteristic functions away from the origin goes
back to H. Cramér, *Random Variables and Probability Distributions*, Cambridge University
Press, 1937, §10.
-/

open Filter MeasureTheory
open scoped Topology

namespace StatLean.HypothesisTesting

/-! ## The oscillatory integral and the Riemann–Lebesgue lemma -/

section FourierOsc

/-- The oscillatory integral `∫ e^{i x s} f(x) dx`, normalised exactly as `charFun` is: for a
density `p`, `charFun (volume.withDensity p) s = fourierOsc p s`. -/
noncomputable def fourierOsc (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp ((x * s : ℝ) * Complex.I) * f x

/-- `fourierOsc` is Mathlib's Fourier integral at the rescaled argument `w = −s/(2π)`. -/
lemma fourierOsc_eq_fourierIntegral (f : ℝ → ℂ) (s : ℝ) :
    fourierOsc f s = ∫ x : ℝ, Real.fourierChar (-(x * (-(2 * Real.pi)⁻¹ * s))) • f x := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hex : (2 * Real.pi * -(x * (-(2 * Real.pi)⁻¹ * s)) : ℝ) = x * s := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  change Complex.exp ((x * s : ℝ) * Complex.I) * f x
    = Real.fourierChar (-(x * (-(2 * Real.pi)⁻¹ * s))) • f x
  rw [Circle.smul_def, Real.fourierChar_apply, hex, smul_eq_mul]

/-- **The Riemann–Lebesgue lemma**, in the `charFun` normalisation: for any `f`, the
oscillatory integral `∫ e^{ixs} f(x) dx` tends to `0` as `s` leaves every compact set. -/
theorem tendsto_fourierOsc_cocompact (f : ℝ → ℂ) :
    Tendsto (fourierOsc f) (Filter.cocompact ℝ) (𝓝 0) := by
  have hRL : Tendsto (fun w : ℝ => ∫ x : ℝ, Real.fourierChar (-(x * w)) • f x)
      (Filter.cocompact ℝ) (𝓝 0) := Real.tendsto_integral_exp_smul_cocompact f
  have hc : (-(2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    simp [hpi]
  have hmap : Tendsto (fun s : ℝ => -(2 * Real.pi)⁻¹ * s)
      (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
    le_of_eq (Homeomorph.mulLeft₀ (-(2 * Real.pi)⁻¹ : ℝ) hc).map_cocompact
  exact (hRL.comp hmap).congr fun s => (fourierOsc_eq_fourierIntegral f s).symm

/-- **The oscillatory integral is a contraction from `L¹` to `L^∞`**, uniformly in the
frequency: `‖ℱf(s) − ℱg(s)‖ ≤ ∫ ‖f − g‖` for every `s`. This is the only estimate the
uniformity argument uses, and it is what makes an `L¹` `ε`-net enough. -/
theorem norm_fourierOsc_sub_le {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (s : ℝ) :
    ‖fourierOsc f s - fourierOsc g s‖ ≤ ∫ x : ℝ, ‖f x - g x‖ := by
  have hnorm : ∀ (x : ℝ) (z : ℂ),
      ‖Complex.exp ((x * s : ℝ) * Complex.I) * z‖ = ‖z‖ := by
    intro x z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hmul : ∀ h : ℝ → ℂ, Integrable h →
      Integrable fun x : ℝ => Complex.exp ((x * s : ℝ) * Complex.I) * h x := by
    intro h hh
    refine Integrable.mono' hh.norm ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_exp.comp
        (by fun_prop)).aestronglyMeasurable.mul hh.aestronglyMeasurable
    · exact le_of_eq (hnorm x (h x))
  rw [fourierOsc, fourierOsc, ← integral_sub (hmul f hf) (hmul g hg)]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change ‖Complex.exp ((x * s : ℝ) * Complex.I) * f x
    - Complex.exp ((x * s : ℝ) * Complex.I) * g x‖ = ‖f x - g x‖
  rw [← mul_sub, hnorm]

end FourierOsc

/-! ## Uniformity over a totally bounded family

The whole content of this section is the two-line estimate

`‖ℱf_i(s)‖ ≤ ‖ℱf_j(s)‖ + ‖f_i − f_j‖_{L¹}`,

with `j` ranging over a **finite** `ε`-net: the first term is eventually small by
Riemann–Lebesgue applied to each of the finitely many net elements, and the second is small by
the choice of the net. Total boundedness is exactly the hypothesis that makes the first
"eventually" uniform, since a finite intersection of eventualities is an eventuality. -/

section Uniform

variable {ι : Type*}

/-- **Riemann–Lebesgue holds uniformly over a totally bounded family of `L¹` functions.**

`S` is a set of indices, `f i` the corresponding functions, and the hypothesis `hnet` is total
boundedness of `{f i : i ∈ S}` in `L¹`, phrased as the existence of finite `δ`-nets *indexed by
`S`* — which is the form a finite subcover of a compact parameter set produces. -/
theorem eventually_norm_fourierOsc_le_of_totallyBounded (f : ι → ℝ → ℂ) (S : Set ι)
    (hf : ∀ i ∈ S, Integrable (f i))
    (hnet : ∀ δ : ℝ, 0 < δ → ∃ J : Finset ι, ↑J ⊆ S ∧
      ∀ i ∈ S, ∃ j ∈ J, (∫ x : ℝ, ‖f i x - f j x‖) ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in Filter.cocompact ℝ, ∀ i ∈ S, ‖fourierOsc (f i) s‖ ≤ ε := by
  obtain ⟨J, hJS, hJ⟩ := hnet (ε / 2) (by linarith)
  have hJev : ∀ j ∈ J, ∀ᶠ s in Filter.cocompact ℝ, ‖fourierOsc (f j) s‖ ≤ ε / 2 := by
    intro j _
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.1
      (tendsto_fourierOsc_cocompact (f j)) (ε / 2) (by linarith)] with s hs
    exact hs.le
  filter_upwards [Filter.eventually_all_finset J |>.2 hJev] with s hs i hi
  obtain ⟨j, hjJ, hij⟩ := hJ i hi
  have hjS : j ∈ S := hJS (Finset.mem_coe.2 hjJ)
  have hsub := norm_fourierOsc_sub_le (hf i hi) (hf j hjS) s
  have htri : ‖fourierOsc (f i) s‖
      ≤ ‖fourierOsc (f i) s - fourierOsc (f j) s‖ + ‖fourierOsc (f j) s‖ := by
    simpa using norm_add_le (fourierOsc (f i) s - fourierOsc (f j) s) (fourierOsc (f j) s)
  have hj2 := hs j hjJ
  linarith

/-- **A family parametrised continuously in `L¹` by a compact set is totally bounded.**
The finite `δ`-net is a finite subcover of the parameter set by the neighbourhoods on which the
`L¹` modulus of continuity is below `δ`. -/
theorem exists_finset_l1Net_of_isCompact {α : Type*} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) (f : α → ℝ → ℂ)
    (hcont : ∀ a ∈ K, ∀ δ : ℝ, 0 < δ → ∃ U ∈ 𝓝 a, ∀ b ∈ U,
      (∫ x : ℝ, ‖f b x - f a x‖) ≤ δ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : Finset α, ↑J ⊆ K ∧ ∀ a ∈ K, ∃ j ∈ J, (∫ x : ℝ, ‖f a x - f j x‖) ≤ δ := by
  choose! U hUmem hUbd using fun a (ha : a ∈ K) => hcont a ha δ hδ
  obtain ⟨t, htK, htcover⟩ := hK.elim_nhds_subcover U (fun a ha => hUmem a ha)
  refine ⟨t, fun a ha => htK a (Finset.mem_coe.1 ha), fun a ha => ?_⟩
  obtain ⟨j, hjt, haU⟩ := Set.mem_iUnion₂.1 (htcover ha)
  exact ⟨j, hjt, hUbd j (htK j hjt) a haU⟩

/-- **Riemann–Lebesgue, uniformly over a compactly parametrised family.** The form the
applications consume: a compact parameter set `K`, an `L¹`-continuous dependence, and the
conclusion that `∫ e^{ixs} f_a(x) dx` is eventually below `ε` *simultaneously* for all `a ∈ K`.

This is the soft route to the uniformity statements that multivariate Cramér conditions need:
the directions form a compact sphere, and only the `L¹`-continuity of the projected densities
has to be checked. -/
theorem eventually_norm_fourierOsc_le_of_isCompact {α : Type*} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) (f : α → ℝ → ℂ) (hf : ∀ a ∈ K, Integrable (f a))
    (hcont : ∀ a ∈ K, ∀ δ : ℝ, 0 < δ → ∃ U ∈ 𝓝 a, ∀ b ∈ U,
      (∫ x : ℝ, ‖f b x - f a x‖) ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in Filter.cocompact ℝ, ∀ a ∈ K, ‖fourierOsc (f a) s‖ ≤ ε :=
  eventually_norm_fourierOsc_le_of_totallyBounded f K hf
    (fun _ hδ => exists_finset_l1Net_of_isCompact hK f hcont hδ) hε

end Uniform

/-! ## The application: an oscillatory integral with a quadratic phase

For a law carried by the parabola `y ↦ (y, y²)` — the law of `(X − μ, (X − μ)² − σ²)` that the
studentized Edgeworth expansion runs on — the characteristic function in the direction
`t = (t₀, t₁)` is, up to a unimodular factor, `∫ f(y) e^{i(t₀y + t₁y²)} dy` with `f` the density
of `X − μ`. A multivariate Cramér condition asks for this to stay away from `1` as `‖t‖ → ∞`,
uniformly.

Two regimes have to be treated separately, and only the first is a Riemann–Lebesgue statement:

* `|t₁|` bounded. Then `‖t‖ → ∞` forces `|t₀| → ∞`, and the integral is the Fourier transform,
  at frequency `t₀`, of the **twisted density** `y ↦ e^{it₁y²}f(y)`. The twists form a family
  parametrised by the compact interval `|t₁| ≤ M`, continuously in `L¹` — dominated convergence,
  with dominating function `2‖f‖` — so `eventually_norm_fourierOsc_le_of_isCompact` applies and
  gives decay uniform in `t₁`. That is `eventually_norm_quadPhaseInt_le` below.
* `|t₁| → ∞`. Here the phase is genuinely quadratic and no `L¹` family is compact: the twists
  `e^{it₁y²}f` oscillate away from each other in `L¹`. The classical estimate is van der
  Corput's second-derivative test; what is proved below instead is the soft **autocorrelation
  identity** `|I|² = ∫ e^{i(t₀h + t₁h²)} ĝ_h(2t₁h) dh` with `g_h(z) = f(z + h)\overline{f(z)}`,
  which needs no smoothness, no compact support and no bounded variation — dominated convergence
  in `h` against `‖g_h‖₁` (integrable, with `∫‖g_h‖₁ dh = ‖f‖₁²`) takes `|t₁| → ∞`. -/

section QuadraticPhase

/-- The density twisted by the quadratic part of the phase: `y ↦ e^{i t y²} f(y)`. -/
noncomputable def quadTwist (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ :=
  fun y => Complex.exp ((t * y ^ 2 : ℝ) * Complex.I) * f y

/-- The oscillatory integral with a quadratic phase, `∫ f(y) e^{i(t₀y + t₁y²)} dy`. -/
noncomputable def quadPhaseInt (f : ℝ → ℂ) (t₀ t₁ : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp ((t₀ * y + t₁ * y ^ 2 : ℝ) * Complex.I) * f y

/-- Twisting the density turns a quadratic phase into a linear one. -/
lemma quadPhaseInt_eq_fourierOsc (f : ℝ → ℂ) (t₀ t₁ : ℝ) :
    quadPhaseInt f t₀ t₁ = fourierOsc (quadTwist f t₁) t₀ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change Complex.exp ((t₀ * y + t₁ * y ^ 2 : ℝ) * Complex.I) * f y
    = Complex.exp ((y * t₀ : ℝ) * Complex.I)
        * (Complex.exp ((t₁ * y ^ 2 : ℝ) * Complex.I) * f y)
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The twist does not change the modulus, hence preserves integrability. -/
lemma integrable_quadTwist {f : ℝ → ℂ} (hf : Integrable f) (t : ℝ) :
    Integrable (quadTwist f t) := by
  refine Integrable.mono' hf.norm ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · rw [quadTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The twists depend on the quadratic coefficient continuously in `L¹`.** Dominated
convergence with the dominating function `2‖f‖`: this is what makes the family over a compact
range of coefficients totally bounded, and hence Riemann–Lebesgue uniform over it. -/
lemma exists_nhds_integral_norm_quadTwist_sub_le {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ U ∈ 𝓝 a, ∀ b ∈ U, (∫ y : ℝ, ‖quadTwist f b y - quadTwist f a y‖) ≤ δ := by
  set Φ : ℝ → ℝ → ℝ := fun b y => ‖quadTwist f b y - quadTwist f a y‖ with hΦ
  have hmeas : ∀ b : ℝ, AEStronglyMeasurable (Φ b) (volume : Measure ℝ) := by
    intro b
    exact (((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable).sub ((Complex.continuous_exp.comp
        (by fun_prop)).aestronglyMeasurable.mul hf.aestronglyMeasurable)).norm
  have hbd : ∀ b : ℝ, ∀ y : ℝ, ‖Φ b y‖ ≤ 2 * ‖f y‖ := by
    intro b y
    have h1 : ‖quadTwist f b y‖ = ‖f y‖ := by
      rw [quadTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h2 : ‖quadTwist f a y‖ = ‖f y‖ := by
      rw [quadTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have := norm_sub_le (quadTwist f b y) (quadTwist f a y)
    rw [h1, h2] at this
    rw [hΦ, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    linarith
  have hcontpt : ∀ y : ℝ, ContinuousAt (fun b : ℝ => Φ b y) a := by
    intro y
    refine Continuous.continuousAt ?_
    exact ((Complex.continuous_exp.comp (by fun_prop)).mul continuous_const).sub
      continuous_const |>.norm
  have hCA : ContinuousAt (fun b : ℝ => ∫ y : ℝ, Φ b y) a :=
    continuousAt_of_dominated (Filter.Eventually.of_forall fun b => hmeas b)
      (Filter.Eventually.of_forall fun b =>
        Filter.Eventually.of_forall fun y => hbd b y)
      (hf.norm.const_mul 2) (Filter.Eventually.of_forall hcontpt)
  have hzero : (∫ y : ℝ, Φ a y) = 0 := by
    simp [hΦ]
  have hev : ∀ᶠ b in 𝓝 a, (∫ y : ℝ, Φ b y) ≤ δ := by
    have hlt := Metric.tendsto_nhds.1 hCA δ hδ
    filter_upwards [hlt] with b hb
    have hnn : 0 ≤ ∫ y : ℝ, Φ b y := integral_nonneg fun y => norm_nonneg _
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hnn] at hb
    exact hb.le
  obtain ⟨U, hU, hUb⟩ := Filter.eventually_iff_exists_mem.1 hev
  exact ⟨U, hU, hUb⟩

/-- **The linear regime of the quadratic-phase estimate.**

For a fixed `L¹` function `f` and a fixed bound `M`, `∫ f(y)e^{i(t₀y + t₁y²)} dy → 0` as
`|t₀| → ∞`, **uniformly over `|t₁| ≤ M`**. This is Riemann–Lebesgue applied to the compactly
parametrised family of twisted densities `e^{it₁y²}f`, and it is one of the two regimes a
multivariate Cramér condition for a parabola-carried law decomposes into. -/
theorem eventually_norm_quadPhaseInt_le {f : ℝ → ℂ} (hf : Integrable f) (M : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ t₀ in Filter.cocompact ℝ, ∀ t₁ : ℝ, |t₁| ≤ M → ‖quadPhaseInt f t₀ t₁‖ ≤ ε := by
  have hmain := eventually_norm_fourierOsc_le_of_isCompact (K := Set.Icc (-M) M)
    isCompact_Icc (quadTwist f) (fun a _ => integrable_quadTwist hf a)
    (fun a _ δ hδ => exists_nhds_integral_norm_quadTwist_sub_le hf a hδ) hε
  filter_upwards [hmain] with t₀ ht₀ t₁ ht₁
  rw [quadPhaseInt_eq_fourierOsc]
  exact ht₀ t₁ (Set.mem_Icc.2 (abs_le.1 ht₁))

/-- An eventuality along `cocompact ℝ` is a statement about all large `|s|`. -/
lemma exists_abs_le_of_eventually_cocompact {p : ℝ → Prop}
    (hp : ∀ᶠ s in Filter.cocompact ℝ, p s) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℝ, R ≤ |s| → p s := by
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup] at hp
  obtain ⟨hbot, htop⟩ := hp
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 hbot
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 htop
  refine ⟨max 1 (max |a| |b|), lt_of_lt_of_le one_pos (le_max_left _ _), fun s hs => ?_⟩
  have hb' : |b| ≤ max 1 (max |a| |b|) := le_trans (le_max_right _ _) (le_max_right _ _)
  have ha' : |a| ≤ max 1 (max |a| |b|) := le_trans (le_max_left _ _) (le_max_right _ _)
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at hs
    exact hb s (le_trans (le_trans (le_abs_self b) hb') hs)
  · rw [abs_of_neg h] at hs
    exact ha s (by linarith [neg_abs_le a])

/-! ### The large-coefficient regime, via the autocorrelation identity

The complementary regime `|t₁| → ∞` is *not* a Riemann–Lebesgue statement about the twists
`e^{it₁y²}f`: as `t₁` ranges over an unbounded set those twists are not relatively compact in
`L¹`, so no `ε`-net exists and the argument of the previous section has nothing to bite on.

What is true — and this is the content of the section — is that the estimate holds for **every**
`f ∈ L¹`, uniformly in the linear coefficient `t₀`, by the autocorrelation identity

`|I(t₀,t₁)|² = ∫ e^{i(t₀h + t₁h²)} · ℱg_h(2t₁h) dh`,  `g_h(z) = f(z + h)\overline{f(z)}`.

The identity is elementary: `I \overline{I}` is a double integral over `(y,z)`, the substitution
`y = z + h` (translation invariance of Lebesgue measure in the *inner* variable — no
two-dimensional change of variables is needed) turns the phase into
`t₀h + t₁h² + 2t₁hz`, and Fubini exchanges the order. Fubini is licensed by
`∫∫|f(z + h)f(z)| dz dh = ‖f‖₁²`.

The estimate then follows by dominated convergence in `t₁` along `cocompact ℝ`: for each fixed
`h ≠ 0` the inner frequency `2t₁h` leaves every compact set, so `ℱg_h(2t₁h) → 0` by the ordinary
Riemann–Lebesgue lemma, while `‖ℱg_h(2t₁h)‖ ≤ ‖g_h‖₁` is an integrable dominating function of
`h`. Crucially the linear coefficient `t₀` survives only inside a unimodular factor, so the
resulting bound is uniform in `t₀` — which is exactly what the multivariate Cramér condition for
a parabola-carried law needs and what van der Corput's second-derivative test would otherwise
have to supply. -/

/-- The **autocorrelation of `f` at lag `h`**: `z ↦ f(z + h)\overline{f(z)}`. -/
noncomputable def autoCorr (f : ℝ → ℂ) (h : ℝ) : ℝ → ℂ :=
  fun z => f (z + h) * (starRingEnd ℂ) (f z)

/-- The integrand of `quadPhaseInt`, isolated so that the autocorrelation computation can be
carried out on it. -/
noncomputable def quadKer (f : ℝ → ℂ) (t₀ t₁ : ℝ) : ℝ → ℂ :=
  fun y => Complex.exp ((t₀ * y + t₁ * y ^ 2 : ℝ) * Complex.I) * f y

lemma quadPhaseInt_eq_integral_quadKer (f : ℝ → ℂ) (t₀ t₁ : ℝ) :
    quadPhaseInt f t₀ t₁ = ∫ y : ℝ, quadKer f t₀ t₁ y := rfl

lemma norm_quadKer (f : ℝ → ℂ) (t₀ t₁ y : ℝ) : ‖quadKer f t₀ t₁ y‖ = ‖f y‖ := by
  rw [quadKer, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma stronglyMeasurable_quadKer {f : ℝ → ℂ} (hf : StronglyMeasurable f) (t₀ t₁ : ℝ) :
    StronglyMeasurable (quadKer f t₀ t₁) :=
  (Complex.continuous_exp.comp (by fun_prop)).stronglyMeasurable.mul hf

lemma integrable_quadKer {f : ℝ → ℂ} (hf : Integrable f) (t₀ t₁ : ℝ) :
    Integrable (quadKer f t₀ t₁) := by
  refine Integrable.mono' hf.norm ?_
    (Filter.Eventually.of_forall fun y => le_of_eq (norm_quadKer f t₀ t₁ y))
  exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
    hf.aestronglyMeasurable

/-- **The oscillatory integral is bounded by the `L¹` norm**, at every frequency. -/
lemma norm_fourierOsc_le {g : ℝ → ℂ} (hg : Integrable g) (s : ℝ) :
    ‖fourierOsc g s‖ ≤ ∫ z : ℝ, ‖g z‖ := by
  have h0 : (0 : ℝ → ℂ) = fun _ => (0 : ℂ) := rfl
  have hzero : fourierOsc (fun _ => (0 : ℂ)) s = 0 := by simp [fourierOsc]
  have hzero' : fourierOsc (0 : ℝ → ℂ) s = 0 := by simp [fourierOsc]
  have h := norm_fourierOsc_sub_le hg (integrable_zero ℝ ℂ volume) s
  simpa [hzero, hzero'] using h

/-- The pointwise identity behind the autocorrelation: shifting the argument of the phase kernel
by `h` and multiplying by the conjugate at the base point leaves the phase
`t₀h + t₁h² + 2t₁hz`, whose `z`-dependence is *linear*. -/
lemma quadKer_shift_mul_conj (f : ℝ → ℂ) (t₀ t₁ z h : ℝ) :
    quadKer f t₀ t₁ (z + h) * (starRingEnd ℂ) (quadKer f t₀ t₁ z)
      = Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
          * (Complex.exp ((z * (2 * t₁ * h) : ℝ) * Complex.I) * autoCorr f h z) := by
  have hconj : (starRingEnd ℂ) (Complex.exp ((t₀ * z + t₁ * z ^ 2 : ℝ) * Complex.I))
      = Complex.exp ((-(t₀ * z + t₁ * z ^ 2) : ℝ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hexp : ∀ a b : ℝ, Complex.exp ((a : ℝ) * Complex.I) * Complex.exp ((b : ℝ) * Complex.I)
      = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
    intro a b
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsum : t₀ * (z + h) + t₁ * (z + h) ^ 2 + -(t₀ * z + t₁ * z ^ 2)
      = t₀ * h + t₁ * h ^ 2 + z * (2 * t₁ * h) := by ring
  simp only [quadKer, autoCorr, map_mul, hconj]
  calc Complex.exp ((t₀ * (z + h) + t₁ * (z + h) ^ 2 : ℝ) * Complex.I) * f (z + h) *
        (Complex.exp ((-(t₀ * z + t₁ * z ^ 2) : ℝ) * Complex.I) * (starRingEnd ℂ) (f z))
      = Complex.exp ((t₀ * (z + h) + t₁ * (z + h) ^ 2 : ℝ) * Complex.I) *
          Complex.exp ((-(t₀ * z + t₁ * z ^ 2) : ℝ) * Complex.I) *
          (f (z + h) * (starRingEnd ℂ) (f z)) := by ring
    _ = Complex.exp (((t₀ * h + t₁ * h ^ 2 + z * (2 * t₁ * h) : ℝ) : ℂ) * Complex.I) *
          (f (z + h) * (starRingEnd ℂ) (f z)) := by rw [hexp, hsum]
    _ = _ := by rw [← hexp]; ring

/-- **The autocorrelation is integrable on the product**, with `∫∫ = ‖f‖₁²`. This is what
licenses Fubini in the autocorrelation identity, and it is the only place the `L¹` hypothesis on
`f` is used quantitatively. -/
lemma integrable_uncurry_autoCorr {f : ℝ → ℂ} (hf : Integrable f) (hfm : StronglyMeasurable f) :
    Integrable (Function.uncurry fun z h : ℝ => autoCorr f h z)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hshift : StronglyMeasurable fun p : ℝ × ℝ => f (p.1 + p.2) :=
    hfm.comp_measurable (by fun_prop)
  have hbase : StronglyMeasurable fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.1) :=
    (hfm.comp_measurable measurable_fst).star
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun z h : ℝ => autoCorr f h z)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hshift.mul hbase).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
  · have hrw : (fun y : ℝ => Function.uncurry (fun z h : ℝ => autoCorr f h z) (z, y))
        = fun y : ℝ => f (z + y) * (starRingEnd ℂ) (f z) := rfl
    rw [hrw]
    exact (hf.comp_add_left z).mul_const _
  · have hcongr : ∀ z : ℝ,
        (∫ h : ℝ, ‖Function.uncurry (fun z h : ℝ => autoCorr f h z) (z, h)‖)
          = (∫ y : ℝ, ‖f y‖) * ‖f z‖ := by
      intro z
      have h1 : ∀ h : ℝ, ‖Function.uncurry (fun z h : ℝ => autoCorr f h z) (z, h)‖
          = ‖f (z + h)‖ * ‖f z‖ := by
        intro h
        simp [Function.uncurry, autoCorr]
      rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
      rw [integral_mul_const]
      congr 1
      exact integral_add_left_eq_self (fun y : ℝ => ‖f y‖) z
    refine Integrable.congr (hf.norm.const_mul (∫ y : ℝ, ‖f y‖)) ?_
    exact Filter.Eventually.of_forall fun z => (hcongr z).symm

/-- **The autocorrelation identity.**

`|∫ f(y)e^{i(t₀y + t₁y²)}dy|² = ∫ e^{i(t₀h + t₁h²)} · ℱ(f(· + h)\overline{f})(2t₁h) dh.`

The linear coefficient `t₀` appears on the right only inside a unimodular factor, so taking
moduli produces a bound that is uniform in `t₀`. -/
theorem sq_ofReal_norm_quadPhaseInt {f : ℝ → ℂ} (hf : Integrable f)
    (hfm : StronglyMeasurable f) (t₀ t₁ : ℝ) :
    ((‖quadPhaseInt f t₀ t₁‖ : ℝ) : ℂ) ^ 2
      = ∫ h : ℝ, Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
          * fourierOsc (autoCorr f h) (2 * t₁ * h) := by
  have hK : Integrable (quadKer f t₀ t₁) := integrable_quadKer hf t₀ t₁
  have hKm : StronglyMeasurable (quadKer f t₀ t₁) := stronglyMeasurable_quadKer hfm t₀ t₁
  -- the two-variable integrand `Φ z h = K(z + h) conj (K z)`
  set Φ : ℝ → ℝ → ℂ := fun z h => quadKer f t₀ t₁ (z + h) *
    (starRingEnd ℂ) (quadKer f t₀ t₁ z) with hΦdef
  have hΦm : AEStronglyMeasurable (Function.uncurry Φ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have h1 : StronglyMeasurable fun p : ℝ × ℝ => quadKer f t₀ t₁ (p.1 + p.2) :=
      hKm.comp_measurable (by fun_prop)
    have h2 : StronglyMeasurable fun p : ℝ × ℝ => (starRingEnd ℂ) (quadKer f t₀ t₁ p.1) :=
      (hKm.comp_measurable measurable_fst).star
    exact (h1.mul h2).aestronglyMeasurable
  have hnormeq : ∀ p : ℝ × ℝ, ‖Function.uncurry Φ p‖
      = ‖Function.uncurry (fun z h : ℝ => autoCorr f h z) p‖ := by
    rintro ⟨z, h⟩
    simp [Function.uncurry, hΦdef, autoCorr, norm_quadKer]
  have hΦint : Integrable (Function.uncurry Φ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine Integrable.mono' (integrable_uncurry_autoCorr hf hfm).norm hΦm ?_
    exact Filter.Eventually.of_forall fun p => le_of_eq (hnormeq p)
  -- step 1: the square of the modulus is the iterated integral of `Φ`
  have hstep1 : ((‖quadPhaseInt f t₀ t₁‖ : ℝ) : ℂ) ^ 2 = ∫ z : ℝ, ∫ h : ℝ, Φ z h := by
    have hinner : ∀ z : ℝ, (∫ h : ℝ, Φ z h)
        = quadPhaseInt f t₀ t₁ * (starRingEnd ℂ) (quadKer f t₀ t₁ z) := by
      intro z
      have htr : (∫ h : ℝ, Φ z h)
          = ∫ y : ℝ, quadKer f t₀ t₁ y * (starRingEnd ℂ) (quadKer f t₀ t₁ z) :=
        integral_add_left_eq_self
          (fun y : ℝ => quadKer f t₀ t₁ y * (starRingEnd ℂ) (quadKer f t₀ t₁ z)) z
      have hmc : (∫ y : ℝ, quadKer f t₀ t₁ y * (starRingEnd ℂ) (quadKer f t₀ t₁ z))
          = (∫ y : ℝ, quadKer f t₀ t₁ y) * (starRingEnd ℂ) (quadKer f t₀ t₁ z) :=
        integral_mul_const _ _
      rw [htr, hmc, ← quadPhaseInt_eq_integral_quadKer]
    have houter : (∫ z : ℝ, quadPhaseInt f t₀ t₁ * (starRingEnd ℂ) (quadKer f t₀ t₁ z))
        = quadPhaseInt f t₀ t₁ * ∫ z : ℝ, (starRingEnd ℂ) (quadKer f t₀ t₁ z) :=
      integral_const_mul _ _
    have hconjint : (∫ z : ℝ, (starRingEnd ℂ) (quadKer f t₀ t₁ z))
        = (starRingEnd ℂ) (quadPhaseInt f t₀ t₁) := by
      rw [quadPhaseInt_eq_integral_quadKer]
      exact integral_conj
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner), houter, hconjint,
      Complex.mul_conj']
  -- step 2: Fubini, then evaluate the inner integral
  have hstep2 : (∫ z : ℝ, ∫ h : ℝ, Φ z h) = ∫ h : ℝ, ∫ z : ℝ, Φ z h :=
    integral_integral_swap hΦint
  have hstep3 : ∀ h : ℝ, (∫ z : ℝ, Φ z h)
      = Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
          * fourierOsc (autoCorr f h) (2 * t₁ * h) := by
    intro h
    have hpt : ∀ z : ℝ, Φ z h
        = Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
            * (Complex.exp ((z * (2 * t₁ * h) : ℝ) * Complex.I) * autoCorr f h z) :=
      fun z => quadKer_shift_mul_conj f t₀ t₁ z h
    have hpull : (∫ z : ℝ, Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
          * (Complex.exp ((z * (2 * t₁ * h) : ℝ) * Complex.I) * autoCorr f h z))
        = Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
          * ∫ z : ℝ, Complex.exp ((z * (2 * t₁ * h) : ℝ) * Complex.I) * autoCorr f h z :=
      integral_const_mul _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hpull]
    rfl
  rw [hstep1, hstep2, integral_congr_ae (Filter.Eventually.of_forall hstep3)]

/-- The modulus bound extracted from the autocorrelation identity: the square of the modulus is
bounded by an integral **free of `t₀`**. -/
theorem sq_norm_quadPhaseInt_le {f : ℝ → ℂ} (hf : Integrable f)
    (hfm : StronglyMeasurable f) (t₀ t₁ : ℝ) :
    ‖quadPhaseInt f t₀ t₁‖ ^ 2 ≤ ∫ h : ℝ, ‖fourierOsc (autoCorr f h) (2 * t₁ * h)‖ := by
  have hid := sq_ofReal_norm_quadPhaseInt hf hfm t₀ t₁
  have hnormsq : ‖((‖quadPhaseInt f t₀ t₁‖ : ℝ) : ℂ) ^ 2‖ = ‖quadPhaseInt f t₀ t₁‖ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hbd : ‖∫ h : ℝ, Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
        * fourierOsc (autoCorr f h) (2 * t₁ * h)‖
      ≤ ∫ h : ℝ, ‖Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
        * fourierOsc (autoCorr f h) (2 * t₁ * h)‖ :=
    norm_integral_le_integral_norm _
  have hcongr : (∫ h : ℝ, ‖Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
        * fourierOsc (autoCorr f h) (2 * t₁ * h)‖)
      = ∫ h : ℝ, ‖fourierOsc (autoCorr f h) (2 * t₁ * h)‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    change ‖Complex.exp ((t₀ * h + t₁ * h ^ 2 : ℝ) * Complex.I)
        * fourierOsc (autoCorr f h) (2 * t₁ * h)‖ = ‖fourierOsc (autoCorr f h) (2 * t₁ * h)‖
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [← hnormsq, hid]
  exact hbd.trans_eq hcongr

/-- **The dominated-convergence step.** For each fixed lag `h ≠ 0` the inner frequency `2t₁h`
leaves every compact set as `|t₁| → ∞`, so the transform of the autocorrelation tends to `0`;
`‖g_h‖₁` dominates, and it is integrable in `h` because `∫∫|f(z + h)f(z)| = ‖f‖₁²`. -/
theorem tendsto_integral_norm_fourierOsc_autoCorr {f : ℝ → ℂ} (hf : Integrable f)
    (hfm : StronglyMeasurable f) :
    Filter.Tendsto (fun t₁ : ℝ => ∫ h : ℝ, ‖fourierOsc (autoCorr f h) (2 * t₁ * h)‖)
      (Filter.cocompact ℝ) (𝓝 0) := by
  haveI : (Filter.cocompact ℝ).IsCountablyGenerated := by
    rw [cocompact_eq_atBot_atTop]; infer_instance
  have hAint := integrable_uncurry_autoCorr hf hfm
  obtain ⟨hslice, hbound⟩ := (integrable_prod_iff' (hAint.aestronglyMeasurable)).1 hAint
  -- the dominating function
  set B : ℝ → ℝ := fun h => ∫ z : ℝ, ‖autoCorr f h z‖ with hBdef
  have hBint : Integrable B := hbound
  -- measurability in `h` of the transformed autocorrelation
  have hmeas : ∀ t₁ : ℝ, AEStronglyMeasurable
      (fun h : ℝ => ‖fourierOsc (autoCorr f h) (2 * t₁ * h)‖) volume := by
    intro t₁
    have hshift : StronglyMeasurable fun p : ℝ × ℝ => f (p.2 + p.1) :=
      hfm.comp_measurable (by fun_prop)
    have hbase : StronglyMeasurable fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.2) :=
      (hfm.comp_measurable measurable_snd).star
    have hphase : StronglyMeasurable
        fun p : ℝ × ℝ => Complex.exp ((p.2 * (2 * t₁ * p.1) : ℝ) * Complex.I) :=
      (Complex.continuous_exp.comp (by fun_prop)).stronglyMeasurable
    have hprod : StronglyMeasurable fun p : ℝ × ℝ =>
        Complex.exp ((p.2 * (2 * t₁ * p.1) : ℝ) * Complex.I) * (f (p.2 + p.1) *
          (starRingEnd ℂ) (f p.2)) := hphase.mul (hshift.mul hbase)
    exact (hprod.integral_prod_right').norm.aestronglyMeasurable
  -- the domination
  have hdom : ∀ t₁ : ℝ, ∀ᵐ h : ℝ,
      ‖‖fourierOsc (autoCorr f h) (2 * t₁ * h)‖‖ ≤ B h := by
    intro t₁
    filter_upwards [hslice] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_fourierOsc_le hh _
  -- the pointwise limit
  have hlim : ∀ᵐ h : ℝ, Filter.Tendsto
      (fun t₁ : ℝ => ‖fourierOsc (autoCorr f h) (2 * t₁ * h)‖) (Filter.cocompact ℝ) (𝓝 0) := by
    have hne : ∀ᵐ h : ℝ, h ≠ 0 := by
      have : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
      filter_upwards [MeasureTheory.compl_mem_ae_iff.2 this] with h hh
      simpa using hh
    filter_upwards [hne] with h hh
    have hmapc : Filter.Tendsto (fun t₁ : ℝ => 2 * t₁ * h)
        (Filter.cocompact ℝ) (Filter.cocompact ℝ) := by
      have hc : (2 * h : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hh
      have hbase : Filter.Tendsto (fun s : ℝ => (2 * h) * s)
          (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
        le_of_eq (Homeomorph.mulLeft₀ (2 * h : ℝ) hc).map_cocompact
      exact hbase.congr (fun s : ℝ => by ring)
    have := (tendsto_fourierOsc_cocompact (autoCorr f h)).comp hmapc
    simpa using this.norm
  have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := Filter.cocompact ℝ)
    (F := fun t₁ h : ℝ => ‖fourierOsc (autoCorr f h) (2 * t₁ * h)‖)
    (f := fun _ : ℝ => (0 : ℝ)) B
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall hdom) hBint hlim
  simpa using this

/-- **The large-coefficient regime of the quadratic-phase estimate — the residue of (M3)(i).**

For every `f ∈ L¹` and every `ε > 0` there is an `M` beyond which
`|∫ f(y)e^{i(t₀y + t₁y²)}dy| ≤ ε` for **all** `t₀` as soon as `|t₁| ≥ M`. No smoothness, no
compact support and no bounded variation are assumed: the autocorrelation identity converts the
statement into ordinary Riemann–Lebesgue at the frequencies `2t₁h`, and the uniformity in `t₀`
is automatic because `t₀` survives only in a unimodular factor. -/
theorem exists_bound_norm_quadPhaseInt_large {f : ℝ → ℂ} (hf : Integrable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ t₀ t₁ : ℝ, M ≤ |t₁| → ‖quadPhaseInt f t₀ t₁‖ ≤ ε := by
  -- replace `f` by a strongly measurable representative; `quadPhaseInt` does not see the change
  obtain ⟨g, hgm, hfg⟩ := hf.1
  have hg : Integrable g := hf.congr hfg
  have hqp : ∀ t₀ t₁ : ℝ, quadPhaseInt f t₀ t₁ = quadPhaseInt g t₀ t₁ := by
    intro t₀ t₁
    refine integral_congr_ae ?_
    filter_upwards [hfg] with y hy
    rw [hy]
  have htend := tendsto_integral_norm_fourierOsc_autoCorr hg hgm
  have hev : ∀ᶠ t₁ in Filter.cocompact ℝ,
      (∫ h : ℝ, ‖fourierOsc (autoCorr g h) (2 * t₁ * h)‖) ≤ ε ^ 2 := by
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.1 htend (ε ^ 2) (by positivity)] with t₁ ht₁
    calc (∫ h : ℝ, ‖fourierOsc (autoCorr g h) (2 * t₁ * h)‖)
        ≤ ‖∫ h : ℝ, ‖fourierOsc (autoCorr g h) (2 * t₁ * h)‖‖ := le_abs_self _
      _ ≤ ε ^ 2 := ht₁.le
  obtain ⟨M, hM, hMbd⟩ := exists_abs_le_of_eventually_cocompact hev
  refine ⟨M, hM, fun t₀ t₁ ht₁ => ?_⟩
  have h1 : ‖quadPhaseInt g t₀ t₁‖ ^ 2 ≤ ε ^ 2 :=
    (sq_norm_quadPhaseInt_le hg hgm t₀ t₁).trans (hMbd t₁ ht₁)
  have h2 : (0 : ℝ) ≤ ‖quadPhaseInt g t₀ t₁‖ := norm_nonneg _
  rw [hqp]
  nlinarith [h1, h2, hε]

/-- **The two regimes combine.** Taking the complementary large-coefficient estimate as an
explicit hypothesis — it is *not* a Riemann–Lebesgue statement, see the section note — the
quadratic-phase integral is uniformly small once `|t₀| + |t₁|` is large, which is exactly the
cocompact bound a multivariate Cramér condition asks for. -/
theorem exists_bound_norm_quadPhaseInt {f : ℝ → ℂ} (hf : Integrable f) {ε : ℝ} (hε : 0 < ε)
    {M : ℝ} (hM : 0 < M)
    -- the large-coefficient regime: van der Corput, or the autocorrelation identity
    (hlarge : ∀ t₀ t₁ : ℝ, M ≤ |t₁| → ‖quadPhaseInt f t₀ t₁‖ ≤ ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ t₀ t₁ : ℝ, R ≤ |t₀| + |t₁| → ‖quadPhaseInt f t₀ t₁‖ ≤ ε := by
  obtain ⟨R₀, hR₀, hR⟩ := exists_abs_le_of_eventually_cocompact
    (eventually_norm_quadPhaseInt_le hf M hε)
  refine ⟨R₀ + M, by linarith, fun t₀ t₁ ht => ?_⟩
  rcases le_or_gt M |t₁| with h | h
  · exact hlarge t₀ t₁ h
  · exact hR t₀ (by linarith) t₁ h.le

/-- **The Cramér-type bound for a quadratic phase, unconditionally.** Combining the two regimes:
for every `L¹` function `f` and every `ε > 0`, `|∫ f(y)e^{i(t₀y + t₁y²)}dy| ≤ ε` once
`|t₀| + |t₁|` is large. This is the cocompact decay that a multivariate Cramér condition for a
law carried by the parabola `y ↦ (y, y²)` consumes, and it is now free of hypotheses beyond
`f ∈ L¹`. -/
theorem exists_bound_norm_quadPhaseInt_of_integrable {f : ℝ → ℂ} (hf : Integrable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ t₀ t₁ : ℝ, R ≤ |t₀| + |t₁| → ‖quadPhaseInt f t₀ t₁‖ ≤ ε := by
  obtain ⟨M, hM, hMbd⟩ := exists_bound_norm_quadPhaseInt_large hf hε
  exact exists_bound_norm_quadPhaseInt hf hε hM hMbd

end QuadraticPhase

end StatLean.HypothesisTesting
