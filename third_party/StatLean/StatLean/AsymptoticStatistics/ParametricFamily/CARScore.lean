module
public import StatLean.AsymptoticStatistics.ForMathlib.ConditionalQMD
public import StatLean.AsymptoticStatistics.ForMathlib.CondExpL2
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Coarsening-At-Random restriction on conditional scores (vdV §25.5.3)

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.3,
book p.380.

The *family-level* CAR restriction: the conditional censoring densities
`rₜ(δ | y)` depend on `(y, δ)` only through the observed coarsening
`x = M(y, δ)` (they are `M⁻¹(σ_𝓧)`-measurable). This is the substantive content
of Coarsening At Random beyond a single-measure disintegration — it is a
statement about the whole differentiable family `t ↦ rₜ`.

Its consequence for the score (vdV p.380): "Because the conditional densities
satisfy CAR, the function `b₀(δ | y)` must actually be a function `b(x)` of `x`
only." The theorem `conditionalScore_factorsThrough` proves this descent by an
L²-closedness argument.

-/

open MeasureTheory Filter Topology ProbabilityTheory
open AsymptoticStatistics.ForMathlib.ConditionalQMD
open AsymptoticStatistics.ForMathlib.CondExpL2
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.ParametricFamily.CARScore

variable {𝓨 𝓓 𝓧 : Type*}
  [MeasurableSpace 𝓨] [MeasurableSpace 𝓓] [MeasurableSpace 𝓧]
  {Q : Measure 𝓨} [IsProbabilityMeasure Q]
  {ν : Measure 𝓓} [SigmaFinite ν] {r : Kernel 𝓨 𝓓} [IsMarkovKernel r]

/-- *Coarsening At Random, family form* (vdV §25.5.3, book p.380).

The differentiable family `t ↦ γ.curve t` satisfies CAR w.r.t. the coarsening
map `M : 𝓨 × 𝓓 → 𝓧` if, for every `t`, the `ν`-density of each fibre
`(y, δ) ↦ ((curve t y).rnDeriv ν δ).toReal` is `(M⁻¹σ_𝓧)`-measurable a.e.
w.r.t. `Q ⊗ ν`: the conditional density depends on `(y, δ)` only through the
observed `x = M(y, δ)`.

This is a genuine external hypothesis: CAR is the defining
restriction of the coarsening model, false for outcome-dependent missingness. It
is the family-level strengthening of the single-measure disintegration clause in
`Operators.CAR.IsCoarseningAtRandom`. -/
def IsCARFamily (M : 𝓨 × 𝓓 → 𝓧) (γ : ConditionalQMDPath Q ν r) : Prop :=
  ∀ t : ℝ,
    AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
      (fun p : 𝓨 × 𝓓 => ((γ.curve t p.1).rnDeriv ν p.2).toReal) (Q.prod ν)

/-- Fibrewise square-root conditional density on the product `𝓨 × 𝓓`:
`√pₜ(y, δ) = √(((curve t y).rnDeriv ν δ).toReal)`. -/
private noncomputable def condSqrt (γ : ConditionalQMDPath Q ν r) (t : ℝ) :
    𝓨 × 𝓓 → ℝ :=
  fun p => Real.sqrt ((γ.curve t p.1).rnDeriv ν p.2).toReal

/-- The product-level score times the reference square-root density `b₀ · √p₀`.
This is the function shown below to be `(M⁻¹σ_𝓧)`-measurable. -/
private noncomputable def condScoreSqrt (γ : ConditionalQMDPath Q ν r) :
    𝓨 × 𝓓 → ℝ :=
  fun p => γ.score p.1 p.2 * condSqrt γ 0 p

/-- The product-level QMD remainder appearing in `γ.qmd_limit`. -/
private noncomputable def condRem (γ : ConditionalQMDPath Q ν r) (t : ℝ) :
    𝓨 × 𝓓 → ℝ :=
  fun p => condSqrt γ t p - condSqrt γ 0 p
    - (t / 2) * γ.score p.1 p.2 * condSqrt γ 0 p

/-- Product-space `L²`-membership of the conditional square-root density:
`√pₜ ∈ L²(Q ⊗ ν)`, where `pₜ(y, δ) = ((curve t y).rnDeriv ν δ).toReal`.

The measurability of `pₜ` is supplied by the CAR hypothesis, so no joint
measurability of the bare fibrewise kernel density is
needed. The joint integral is finite by Tonelli and the fibrewise Radon–Nikodym
mass identity: `∫∫ pₜ d(Q ⊗ ν) = ∫ (curve t y) univ dQ = 1`, since each fibre
`curve t y` is a probability measure dominated by `ν`. A *finite* dominating `ν`
is *not* required — `σ`-finiteness of `ν` suffices for both Tonelli and the
fibrewise `Measure.lintegral_rnDeriv`. -/
private lemma condSqrtDensity_memLp (γ : ConditionalQMDPath Q ν r) (t : ℝ)
    (h_meas : AEStronglyMeasurable
      (fun p : 𝓨 × 𝓓 => ((γ.curve t p.1).rnDeriv ν p.2).toReal) (Q.prod ν)) :
    MemLp (condSqrt γ t) 2 (Q.prod ν) := by
  have h_sqrt_meas : AEStronglyMeasurable (condSqrt γ t) (Q.prod ν) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable h_meas
  rw [memLp_two_iff_integrable_sq h_sqrt_meas]
  -- `(√pₜ)² = pₜ` pointwise.
  have h_sq : (fun p : 𝓨 × 𝓓 => condSqrt γ t p ^ 2)
      = fun p => ((γ.curve t p.1).rnDeriv ν p.2).toReal := by
    funext p; simp only [condSqrt]; exact Real.sq_sqrt ENNReal.toReal_nonneg
  rw [h_sq]
  -- `pₜ` is integrable: nonneg, measurable, and `∫⁻ pₜ ≤ 1`.
  refine ⟨h_meas, ?_⟩
  -- Rewrite the `enorm` of the nonneg density as `ofReal`.
  have h_enorm : (fun p : 𝓨 × 𝓓 => ‖((γ.curve t p.1).rnDeriv ν p.2).toReal‖ₑ)
      = fun p => ENNReal.ofReal ((γ.curve t p.1).rnDeriv ν p.2).toReal := by
    funext p; rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
  -- Tonelli on the (jointly measurable) `ofReal`-density.
  have h_ton :
      ∫⁻ p : 𝓨 × 𝓓, ENNReal.ofReal ((γ.curve t p.1).rnDeriv ν p.2).toReal ∂(Q.prod ν)
        = ∫⁻ y, ∫⁻ δ, ENNReal.ofReal ((γ.curve t y).rnDeriv ν δ).toReal ∂ν ∂Q :=
    lintegral_prod _
      (ENNReal.measurable_ofReal.comp_aemeasurable h_meas.aemeasurable)
  have h_bound :
      ∫⁻ p : 𝓨 × 𝓓, ‖((γ.curve t p.1).rnDeriv ν p.2).toReal‖ₑ ∂(Q.prod ν) ≤ 1 := by
    rw [h_enorm, h_ton]
    calc ∫⁻ y, ∫⁻ δ, ENNReal.ofReal ((γ.curve t y).rnDeriv ν δ).toReal ∂ν ∂Q
        ≤ ∫⁻ _y : 𝓨, 1 ∂Q := by
          refine lintegral_mono (fun y => ?_)
          calc ∫⁻ δ, ENNReal.ofReal ((γ.curve t y).rnDeriv ν δ).toReal ∂ν
              ≤ ∫⁻ δ, (γ.curve t y).rnDeriv ν δ ∂ν :=
                lintegral_mono (fun _ => ENNReal.ofReal_toReal_le)
            _ = (γ.curve t y) Set.univ := Measure.lintegral_rnDeriv (γ.curve_absCont t y)
            _ = 1 := measure_univ
      _ = 1 := by rw [lintegral_const, one_mul, measure_univ]
  exact lt_of_le_of_lt h_bound ENNReal.one_lt_top

/-- The weighted conditional score controlled by the joint QMD limit belongs to
`L²(Q ⊗ ν)`.  CAR supplies the joint measurability of the conditional densities. -/
private lemma condScoreSqrt_memLp
    (M : 𝓨 × 𝓓 → 𝓧) (hM : Measurable M) (γ : ConditionalQMDPath Q ν r)
    (hCAR : IsCARFamily M γ) :
    MemLp (condScoreSqrt γ) 2 (Q.prod ν) := by
  have hm : MeasurableSpace.comap M ‹MeasurableSpace 𝓧›
      ≤ (inferInstance : MeasurableSpace (𝓨 × 𝓓)) := hM.comap_le
  have h_score_meas : AEStronglyMeasurable
      (fun p : 𝓨 × 𝓓 => γ.score p.1 p.2) (Q.prod ν) :=
    γ.score_meas.aestronglyMeasurable
  have hpR_meas : ∀ t, AEStronglyMeasurable
      (fun p : 𝓨 × 𝓓 => ((γ.curve t p.1).rnDeriv ν p.2).toReal) (Q.prod ν) :=
    fun t => (hCAR t).mono hm
  have hSQ_mem : ∀ t, MemLp (condSqrt γ t) 2 (Q.prod ν) :=
    fun t => condSqrtDensity_memLp γ t (hpR_meas t)
  have hRem_meas : ∀ t, AEStronglyMeasurable (condRem γ t) (Q.prod ν) := by
    intro t
    change AEStronglyMeasurable (fun p : 𝓨 × 𝓓 =>
      (condSqrt γ t p - condSqrt γ 0 p)
        - (t / 2) * γ.score p.1 p.2 * condSqrt γ 0 p) (Q.prod ν)
    exact (((hSQ_mem t).sub (hSQ_mem 0)).aestronglyMeasurable).sub
      ((h_score_meas.const_mul (t / 2)).mul (hSQ_mem 0).aestronglyMeasurable)
  have h_qmd : Tendsto (fun t : ℝ =>
      eLpNorm (condRem γ t) 2 (Q.prod ν) / ENNReal.ofReal |t|) (𝓝[≠] 0) (𝓝 0) :=
    γ.qmd_limit
  obtain ⟨t₀, ht₀_ne, ht₀_lt⟩ : ∃ t : ℝ, t ≠ 0 ∧
      eLpNorm (condRem γ t) 2 (Q.prod ν) < ENNReal.ofReal |t| := by
    have h_lt_one : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        eLpNorm (condRem γ t) 2 (Q.prod ν) / ENNReal.ofReal |t| < 1 :=
      h_qmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
    have h_ne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 :=
      eventually_nhdsWithin_of_forall (fun _ ht => ht)
    obtain ⟨t, htlt, htne⟩ := (h_lt_one.and h_ne).exists
    refine ⟨t, htne, ?_⟩
    have habs : (0 : ℝ) < |t| := abs_pos.mpr htne
    have h0 : ENNReal.ofReal |t| ≠ 0 := (ENNReal.ofReal_pos.mpr habs).ne'
    have htop : ENNReal.ofReal |t| ≠ ⊤ := ENNReal.ofReal_ne_top
    calc eLpNorm (condRem γ t) 2 (Q.prod ν)
        = eLpNorm (condRem γ t) 2 (Q.prod ν) / ENNReal.ofReal |t|
            * ENNReal.ofReal |t| := by rw [ENNReal.div_mul_cancel h0 htop]
      _ < 1 * ENNReal.ofReal |t| := ENNReal.mul_lt_mul_left h0 htop htlt
      _ = ENNReal.ofReal |t| := one_mul _
  have hRem_mem₀ : MemLp (condRem γ t₀) 2 (Q.prod ν) :=
    ⟨hRem_meas t₀, lt_trans ht₀_lt ENNReal.ofReal_lt_top⟩
  have hG_scaled_mem : MemLp (fun p => (t₀ / 2) * condScoreSqrt γ p) 2 (Q.prod ν) := by
    have h_eq : (fun p : 𝓨 × 𝓓 => (t₀ / 2) * condScoreSqrt γ p)
        = fun p => (condSqrt γ t₀ p - condSqrt γ 0 p) - condRem γ t₀ p := by
      funext p; simp only [condRem, condScoreSqrt]; ring
    rw [h_eq]
    exact ((hSQ_mem t₀).sub (hSQ_mem 0)).sub hRem_mem₀
  have h2 := hG_scaled_mem.const_mul (2 / t₀)
  have h_eq : (fun p => (2 / t₀) * ((t₀ / 2) * condScoreSqrt γ p)) = condScoreSqrt γ := by
    funext p
    have hc : (2 / t₀) * (t₀ / 2) = 1 := by field_simp
    rw [← mul_assoc, hc, one_mul]
  rwa [h_eq] at h2

/-- *Weighted-score measurability* (vdV §25.5.3, book p.380).

The product `b₀ · √p₀ = (score · √p₀)` is `(M⁻¹σ_𝓧)`-measurable a.e.-`Q ⊗ ν`.

From the joint QMD limit `γ.qmd_limit`, the
difference quotients `qₜ = (√pₜ − √p₀)/(t/2)` converge in `L²(Q ⊗ ν)` to
`score · √p₀`. Under `IsCARFamily M γ` each `√pₜ`, `√p₀` is `(M⁻¹σ_𝓧)`-measurable
(square-root of a CAR-measurable density), so each `qₜ` is; the
`(M⁻¹σ_𝓧)`-measurable functions form an `L²(Q ⊗ ν)`-closed subspace
(`MeasureTheory.isClosed_aestronglyMeasurable`, `hm := hM.comap_le`), so the
`L²`-limit `score · √p₀` inherits `(M⁻¹σ_𝓧)`-measurability.

The two analytic ingredients are as follows.  First, `L²`-membership of the
fibrewise `√pₜ` on the product comes from
`condSqrtDensity_memLp` (Tonelli + `Measure.lintegral_rnDeriv`, giving
`∫∫ pₜ d(Q ⊗ ν) = ∫ (curve t y) univ dQ = 1`); the measurability of `pₜ` is
supplied by `IsCARFamily`, so no joint measurability of the bare kernel density
— and in particular no strengthening of `ν` to a finite measure — is needed
(`σ`-finiteness of `ν` suffices throughout). Second, the closed-subspace convergence
is `IsClosed.mem_of_tendsto` against `isClosed_aestronglyMeasurable`, with the
`L²`-convergence `qₜ → score · √p₀` read off from `γ.qmd_limit` via
`eLpNorm (qₜ − score·√p₀) = ofReal 2 · (eLpNorm (condRem γ t) / ofReal |t|)`. -/
private lemma score_mul_sqrt_aestronglyMeasurable_comap
    (M : 𝓨 × 𝓓 → 𝓧) (hM : Measurable M) (γ : ConditionalQMDPath Q ν r)
    (hCAR : IsCARFamily M γ) :
    AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
      (fun p : 𝓨 × 𝓓 => γ.score p.1 p.2
        * Real.sqrt ((γ.curve 0 p.1).rnDeriv ν p.2).toReal) (Q.prod ν) := by
  classical
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  -- Keep the observed sub-σ-algebra `m = M⁻¹σ_𝓧` explicit so the ambient
  -- product σ-algebra remains available.
  have hm : MeasurableSpace.comap M ‹MeasurableSpace 𝓧›
      ≤ (inferInstance : MeasurableSpace (𝓨 × 𝓓)) := hM.comap_le
  -- The goal function is `condScoreSqrt γ` (definitionally).
  change AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
    (condScoreSqrt γ) (Q.prod ν)
  -- `√pₜ` is `m`-measurable a.e. (CAR at `t`) and lies in `L²(Q ⊗ ν)`.
  have hSQ_meas_m : ∀ t, AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
      (condSqrt γ t) (Q.prod ν) :=
    fun t => Real.continuous_sqrt.comp_aestronglyMeasurable (hCAR t)
  have hpR_meas : ∀ t, AEStronglyMeasurable
      (fun p : 𝓨 × 𝓓 => ((γ.curve t p.1).rnDeriv ν p.2).toReal) (Q.prod ν) :=
    fun t => (hCAR t).mono hm
  have hSQ_mem : ∀ t, MemLp (condSqrt γ t) 2 (Q.prod ν) :=
    fun t => condSqrtDensity_memLp γ t (hpR_meas t)
  -- Reinterpret the joint QMD limit through `condRem` (defeq unfold).
  have h_qmd : Tendsto (fun t : ℝ =>
      eLpNorm (condRem γ t) 2 (Q.prod ν) / ENNReal.ofReal |t|) (𝓝[≠] 0) (𝓝 0) :=
    γ.qmd_limit
  have hG_mem : MemLp (condScoreSqrt γ) 2 (Q.prod ν) :=
    condScoreSqrt_memLp M hM γ hCAR
  -- (2) The difference quotients `q t = (2/t)(√pₜ − √p₀)`, `m`-measurable and `L²`.
  set q : ℝ → 𝓨 × 𝓓 → ℝ :=
    fun t p => (2 / t) * (condSqrt γ t p - condSqrt γ 0 p) with hq_def
  have hq_mem : ∀ t, MemLp (q t) 2 (Q.prod ν) :=
    fun t => ((hSQ_mem t).sub (hSQ_mem 0)).const_mul (2 / t)
  have hq_meas_m : ∀ t, AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
      (q t) (Q.prod ν) :=
    fun t => ((hSQ_meas_m t).sub (hSQ_meas_m 0)).const_mul (2 / t)
  -- (3) `q t → G` in `L²`: `eLpNorm (q t − G) = ofReal 2 · (eLpNorm (condRem γ t)/ofReal|t|)`.
  have h_eLp_tendsto : Tendsto
      (fun t : ℝ => eLpNorm (q t - condScoreSqrt γ) 2 (Q.prod ν)) (𝓝[≠] 0) (𝓝 0) := by
    have h_main : Tendsto (fun t : ℝ =>
        ENNReal.ofReal 2 * (eLpNorm (condRem γ t) 2 (Q.prod ν) / ENNReal.ofReal |t|))
        (𝓝[≠] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul h_qmd
        (Or.inr (by simp : (ENNReal.ofReal 2) ≠ ⊤))
      simpa using h
    refine h_main.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ht
    have habs : (0 : ℝ) < |t| := abs_pos.mpr htne
    -- pointwise `q t − G = (2/t) • condRem γ t`.
    have hpt : q t - condScoreSqrt γ = (2 / t) • condRem γ t := by
      funext p
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq_def, condScoreSqrt, condRem]
      field_simp
    rw [hpt, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, ← ENNReal.mul_comm_div]
    -- ENNReal algebra: `ofReal|2/t| · E = ofReal 2 · (E / ofReal|t|)`.
    congr 1
    rw [abs_div, ENNReal.ofReal_div_of_pos habs]
    congr 1
    norm_num
  -- (4) Closed-subspace argument.
  have hclosed : IsClosed
      {f : Lp ℝ 2 (Q.prod ν) |
        AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›] (⇑f) (Q.prod ν)} :=
    isClosed_aestronglyMeasurable hm
  have htends : Tendsto (fun t : ℝ => (hq_mem t).toLp (q t)) (𝓝[≠] (0 : ℝ))
      (𝓝 (hG_mem.toLp (condScoreSqrt γ))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' q hq_mem (condScoreSqrt γ) hG_mem]
    exact h_eLp_tendsto
  have h_evt_mem : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (hq_mem t).toLp (q t)
        ∈ {f : Lp ℝ 2 (Q.prod ν) |
            AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
              (⇑f) (Q.prod ν)} :=
    Filter.Eventually.of_forall fun t =>
      (hq_meas_m t).congr (MemLp.coeFn_toLp (hq_mem t)).symm
  have h_mem : AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
      (⇑(hG_mem.toLp (condScoreSqrt γ))) (Q.prod ν) :=
    hclosed.mem_of_tendsto htends h_evt_mem
  exact h_mem.congr (MemLp.coeFn_toLp hG_mem)

/-- *CAR ⟹ the conditional score is a function of the observed data* (vdV
§25.5.3, book p.380).

Under `IsCARFamily M γ`, the per-fibre score `b₀(δ | y) = γ.score y δ` is,
`P_full = Q ⊗ₘ r`-a.e., `(M⁻¹σ_𝓧)`-measurable — i.e. it factors as `b(x)`
through the coarsening map. This is the descent from CAR on the densities to CAR
on the score.

Book excerpt (vdV p.380): "Because the conditional densities satisfy CAR, the
function `b₀(δ | y)` must actually be a function `b(x)` of `x` only."

The conclusion is stated a.e.-`Q ⊗ₘ r` (= `P_full`), NOT a.e.-`Q ⊗ ν`: on the
null-set `{p₀ = 0}` the score is unconstrained by the QMD limit (which only sees
`score · √p₀`), so the factorization can only hold where the reference density is
positive — exactly the `Q ⊗ₘ r`-support.

The proof uses that `score · √p₀` is `(M⁻¹σ_𝓧)`-measurable a.e.-`Q ⊗ ν`
(`score_mul_sqrt_aestronglyMeasurable_comap`),
and so is `p₀` itself (`hCAR 0` at `curve 0 = r`); both transfer to `Q ⊗ₘ r` via
`Q ⊗ₘ r ≪ Q ⊗ ν`. Where `p₀ > 0` (`Q ⊗ₘ r`-a.e., proved inline: fibrewise
`Measure.rnDeriv_pos (r y ≪ ν)` lifted through `Measure.ae_compProd_of_ae_ae`,
using the joint-measurable a.e.-representative of `p₀` that `hCAR 0` supplies for
the measurable set) one has `score = (score · √p₀) · (√p₀)⁻¹`, a product of
`(M⁻¹σ_𝓧)`-measurable functions.

`hM : Measurable M` states that the coarsening map is measurable, a standing
regularity assumption on the observation mechanism). -/
theorem conditionalScore_factorsThrough
    (M : 𝓨 × 𝓓 → 𝓧) (hM : Measurable M) (γ : ConditionalQMDPath Q ν r)
    (hCAR : IsCARFamily M γ) :
    AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
      (Function.uncurry γ.score) (Q ⊗ₘ r) := by
  -- The observed σ-algebra and the reference square-root density.
  set m : MeasurableSpace (𝓨 × 𝓓) := MeasurableSpace.comap M ‹MeasurableSpace 𝓧›
    with hm_def
  -- Part A: `score · √p₀` is `m`-measurable a.e.-`Q ⊗ ν`.
  have hSq : AEStronglyMeasurable[m]
      (fun p : 𝓨 × 𝓓 => γ.score p.1 p.2
        * Real.sqrt ((γ.curve 0 p.1).rnDeriv ν p.2).toReal) (Q.prod ν) :=
    score_mul_sqrt_aestronglyMeasurable_comap M hM γ hCAR
  -- `p₀` itself is `m`-measurable a.e.-`Q ⊗ ν` (CAR at `t = 0`).
  have hp0 : AEStronglyMeasurable[m]
      (fun p : 𝓨 × 𝓓 => ((γ.curve 0 p.1).rnDeriv ν p.2).toReal) (Q.prod ν) := hCAR 0
  -- `Q ⊗ₘ r ≪ Q ⊗ ν` since each fibre `r y ≪ ν`.
  have hac : (Q ⊗ₘ r) ≪ Q.prod ν := by
    have hkey : ∀ᵐ y ∂Q, r y ≪ (Kernel.const 𝓨 ν) y := by
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Kernel.const_apply, ← γ.curve_at_zero]
      exact γ.curve_absCont 0 y
    have h := Measure.AbsolutelyContinuous.compProd_right
      (μ := Q) (κ := r) (η := Kernel.const 𝓨 ν) hkey
    rwa [Measure.compProd_const] at h
  -- Transfer both to `Q ⊗ₘ r`.
  have hSq' := hSq.mono_ac hac
  have hp0' := hp0.mono_ac hac
  -- `(√p₀)⁻¹` is `m`-measurable a.e.-`Q ⊗ₘ r` (`x ↦ (√x)⁻¹` is measurable),
  -- using an `m`-strongly-measurable representative of `p₀`, since
  -- `x ↦ x⁻¹` is not continuous at `0` on ℝ (no `ContinuousInv ℝ`).
  have hg : Measurable (fun x : ℝ => (Real.sqrt x)⁻¹) :=
    Real.continuous_sqrt.measurable.inv
  obtain ⟨p0', hp0'_meas, hp0'_eq⟩ := hp0'
  have h_inv : AEStronglyMeasurable[m]
      (fun p : 𝓨 × 𝓓 => (Real.sqrt ((γ.curve 0 p.1).rnDeriv ν p.2).toReal)⁻¹)
      (Q ⊗ₘ r) :=
    ⟨fun p => (Real.sqrt (p0' p))⁻¹,
      (hg.comp hp0'_meas.measurable).stronglyMeasurable,
      by filter_upwards [hp0'_eq] with p hp; rw [hp]⟩
  -- `Q ⊗ₘ r`-a.e. positivity of `p₀`, proved inline. The measurable set for the
  -- compProd lift comes from the ambient-measurable a.e.-representative of `p₀`
  -- supplied by `hCAR 0` (`hp0`), sidestepping joint measurability of the bare
  -- fibrewise `ν`-density.
  have hpos : ∀ᵐ p ∂(Q ⊗ₘ r), 0 < ((γ.curve 0 p.1).rnDeriv ν p.2).toReal := by
    obtain ⟨p0'', hp0''_meas, hp0''_eq⟩ := (hp0.mono hM.comap_le).mono_ac hac
    -- fibrewise positivity, transported onto the representative `p0''`
    have h_fib : ∀ᵐ y ∂Q, ∀ᵐ δ ∂(r y), 0 < p0'' (y, δ) := by
      have h_eq_fib : ∀ᵐ y ∂Q, ∀ᵐ δ ∂(r y),
          ((γ.curve 0 y).rnDeriv ν δ).toReal = p0'' (y, δ) :=
        Measure.ae_ae_of_ae_compProd hp0''_eq
      filter_upwards [h_eq_fib] with y hy
      have hpos_fib : ∀ᵐ δ ∂(r y), 0 < ((γ.curve 0 y).rnDeriv ν δ).toReal := by
        have hac_y : γ.curve 0 y ≪ ν := γ.curve_absCont 0 y
        have h1 : ∀ᵐ δ ∂(γ.curve 0 y), 0 < (γ.curve 0 y).rnDeriv ν δ :=
          Measure.rnDeriv_pos hac_y
        have h2 : ∀ᵐ δ ∂(γ.curve 0 y), (γ.curve 0 y).rnDeriv ν δ < ⊤ :=
          hac_y.ae_le (Measure.rnDeriv_lt_top (γ.curve 0 y) ν)
        have hry : r y = γ.curve 0 y := by rw [γ.curve_at_zero]
        rw [hry]
        filter_upwards [h1, h2] with δ hδ1 hδ2
        exact ENNReal.toReal_pos hδ1.ne' hδ2.ne
      filter_upwards [hpos_fib, hy] with δ hδpos hδeq
      rwa [hδeq] at hδpos
    have hset := measurableSet_lt (measurable_const (a := (0 : ℝ)))
      hp0''_meas.measurable
    have hpos'' : ∀ᵐ p ∂(Q ⊗ₘ r), 0 < p0'' p :=
      Measure.ae_compProd_of_ae_ae hset h_fib
    filter_upwards [hpos'', hp0''_eq] with p hp hpeq
    rwa [hpeq]
  -- Where `p₀ > 0`, `score = (score · √p₀) · (√p₀)⁻¹`.
  have h_eq : Function.uncurry γ.score =ᵐ[Q ⊗ₘ r]
      (fun p : 𝓨 × 𝓓 =>
        (γ.score p.1 p.2 * Real.sqrt ((γ.curve 0 p.1).rnDeriv ν p.2).toReal)
          * (Real.sqrt ((γ.curve 0 p.1).rnDeriv ν p.2).toReal)⁻¹) := by
    filter_upwards [hpos] with p hp
    have hs : Real.sqrt ((γ.curve 0 p.1).rnDeriv ν p.2).toReal ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hp)
    simp only [Function.uncurry]
    rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
  exact (hSq'.mul h_inv).congr h_eq.symm

/-- The bare conditional score is square-integrable under the full-data law
`Q ⊗ₘ r` when the supplied conditional-QMD path satisfies CAR
(vdV §25.5.3, book p.380).

The CAR hypothesis supplies the joint density measurability needed to pass from
the weighted score controlled by the QMD limit to the raw score under the
reference full-data law. -/
theorem conditionalScore_memLp_compProd_of_car
    (M : 𝓨 × 𝓓 → 𝓧)
    (hM : Measurable M) -- the observed coarsening map is measurable.
    (γ : ConditionalQMDPath Q ν r)
    (hCAR : IsCARFamily M γ) : -- the supplied conditional path satisfies CAR.
    MemLp (Function.uncurry γ.score) 2 (Q ⊗ₘ r) := by
  have hscore_meas : AEStronglyMeasurable (Function.uncurry γ.score) (Q ⊗ₘ r) :=
    (conditionalScore_factorsThrough M hM γ hCAR).mono hM.comap_le
  rw [memLp_two_iff_integrable_sq hscore_meas]
  have hweighted : Integrable (fun p => condScoreSqrt γ p ^ 2) (Q.prod ν) :=
    (condScoreSqrt_memLp M hM γ hCAR).integrable_sq
  have hweighted_prod :=
    (integrable_prod_iff hweighted.aestronglyMeasurable).mp hweighted
  have hfibre : ∀ᵐ y ∂Q, Integrable (fun δ => γ.score y δ ^ 2) (r y) := by
    filter_upwards [hweighted_prod.1] with y hy
    have h_eq : (fun δ => condScoreSqrt γ (y, δ) ^ 2) = fun δ =>
        ((γ.curve 0 y).rnDeriv ν δ).toReal * γ.score y δ ^ 2 := by
      funext δ
      simp only [condScoreSqrt, condSqrt, mul_pow,
        Real.sq_sqrt ENNReal.toReal_nonneg]
      ring
    rw [h_eq] at hy
    have h := (integrable_toReal_rnDeriv_mul_iff
      (γ.curve_absCont 0 y)).mp hy
    simpa only [γ.curve_at_zero] using h
  have hnorm_eq : (fun y => ∫ δ, ‖γ.score y δ ^ 2‖ ∂(r y)) =
      fun y => ∫ δ, ‖condScoreSqrt γ (y, δ) ^ 2‖ ∂ν := by
    funext y
    calc
      ∫ δ, ‖γ.score y δ ^ 2‖ ∂(r y)
          = ∫ δ, ‖γ.score y δ ^ 2‖ ∂(γ.curve 0 y) := by rw [γ.curve_at_zero]
      _ = ∫ δ, ((γ.curve 0 y).rnDeriv ν δ).toReal
            * ‖γ.score y δ ^ 2‖ ∂ν :=
        (integral_toReal_rnDeriv_mul (γ.curve_absCont 0 y)).symm
      _ = ∫ δ, ‖condScoreSqrt γ (y, δ) ^ 2‖ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun δ => ?_)
        simp only [condScoreSqrt, condSqrt, mul_pow,
          Real.norm_of_nonneg (sq_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg]
        rw [Real.norm_of_nonneg
          (mul_nonneg (sq_nonneg (γ.score y δ)) ENNReal.toReal_nonneg)]
        ring
  refine (Measure.integrable_compProd_iff (hscore_meas.pow 2)).2 ⟨hfibre, ?_⟩
  change Integrable (fun y => ∫ δ, ‖γ.score y δ ^ 2‖ ∂(r y)) Q
  rw [hnorm_eq]
  exact hweighted_prod.2

/-- The observed `L²₀` score supplied by a conditional-QMD path satisfying CAR
(vdV §25.5.3, book p.380).

The CAR hypothesis is used to descend the bare conditional score through the
measurable coarsening map. Square-integrability follows from
`conditionalScore_memLp_compProd_of_car`, and mean zero follows from
`conditionalScore_fibre_mean_zero`. -/
noncomputable def conditionalQMDObservedScore
    (M : 𝓨 × 𝓓 → 𝓧)
    (hM : Measurable M) -- the observed coarsening map is measurable.
    (γ : ConditionalQMDPath Q ν r)
    (hCAR : IsCARFamily M γ) : -- the supplied conditional path satisfies CAR.
    ↥(AsymptoticStatistics.Core.Hilbert.L2ZeroMean ((Q ⊗ₘ r).map M)) := by
  have hscore := conditionalScore_memLp_compProd_of_car M hM γ hCAR
  let scoreLp : Lp ℝ 2 (Q ⊗ₘ r) := hscore.toLp (Function.uncurry γ.score)
  have hscoreLp_meas :
      AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace 𝓧›]
        (scoreLp : 𝓨 × 𝓓 → ℝ) (Q ⊗ₘ r) :=
    (conditionalScore_factorsThrough M hM γ hCAR).congr
      (MemLp.coeFn_toLp hscore).symm
  let scoreMeas : lpMeas ℝ ℝ
      (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r) :=
    ⟨scoreLp, mem_lpMeas_iff_aestronglyMeasurable.mpr hscoreLp_meas⟩
  let observedLp : Lp ℝ 2 ((Q ⊗ₘ r).map M) := doobL2Equiv hM scoreMeas
  have hpull : (fun p => observedLp (M p)) =ᵐ[Q ⊗ₘ r]
      Function.uncurry γ.score :=
    (doobL2Equiv_comp_apply hM scoreMeas).trans (MemLp.coeFn_toLp hscore)
  have hscore_int : Integrable (Function.uncurry γ.score) (Q ⊗ₘ r) :=
    hscore.integrable one_le_two
  have hscore_mean : ∫ p, Function.uncurry γ.score p ∂(Q ⊗ₘ r) = 0 := by
    rw [Measure.integral_compProd hscore_int]
    exact integral_eq_zero_of_ae (conditionalScore_fibre_mean_zero γ)
  have hobserved_mean : ∫ x, observedLp x ∂((Q ⊗ₘ r).map M) = 0 := by
    rw [integral_map hM.aemeasurable (Lp.aestronglyMeasurable observedLp)]
    rw [integral_congr_ae hpull]
    exact hscore_mean
  refine ⟨observedLp, ?_⟩
  unfold AsymptoticStatistics.Core.Hilbert.L2ZeroMean
  rw [LinearMap.mem_ker]
  change AsymptoticStatistics.Core.Hilbert.integralL2 ((Q ⊗ₘ r).map M) observedLp = 0
  unfold AsymptoticStatistics.Core.Hilbert.integralL2
    AsymptoticStatistics.Core.Hilbert.oneL2
  rw [innerSL_apply_apply, L2.inner_def]
  calc
    ∫ x, ⟪((memLp_const (1 : ℝ)).toLp (fun _ : 𝓧 => 1)) x, observedLp x⟫_ℝ
        ∂((Q ⊗ₘ r).map M) = ∫ x, observedLp x ∂((Q ⊗ₘ r).map M) := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_const (1 : ℝ)).coeFn_toLp] with x hx
          rw [hx]
          change observedLp x * 1 = observedLp x
          ring
    _ = 0 := hobserved_mean

/-- Pulling the observed conditional-QMD/CAR score back along `M` recovers the
bare conditional score `b₀(δ | y)` almost everywhere under `Q ⊗ₘ r`
(vdV §25.5.3, book p.380). -/
theorem conditionalQMDObservedScore_pullback
    (M : 𝓨 × 𝓓 → 𝓧)
    (hM : Measurable M) -- the observed coarsening map is measurable.
    (γ : ConditionalQMDPath Q ν r)
    (hCAR : IsCARFamily M γ) : -- the supplied conditional path satisfies CAR.
    (fun p =>
      (((conditionalQMDObservedScore M hM γ hCAR :
          ↥(AsymptoticStatistics.Core.Hilbert.L2ZeroMean ((Q ⊗ₘ r).map M))) :
          Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M p))
      =ᵐ[Q ⊗ₘ r] Function.uncurry γ.score := by
  unfold conditionalQMDObservedScore
  exact (doobL2Equiv_comp_apply hM _).trans
    (MemLp.coeFn_toLp (conditionalScore_memLp_compProd_of_car M hM γ hCAR))

end AsymptoticStatistics.ParametricFamily.CARScore
