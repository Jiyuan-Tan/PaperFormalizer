module
public import StatLean.StatisticalLearning.PACBayes.ChangeOfMeasure
public import StatLean.StatisticalLearning.Core.SampleLaw
public import StatLean.StatisticalLearning.FiniteClass.UniformConvergence
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import StatLean.ConcentrationInequalities.SubGaussian.Bounded
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# The PAC-Bayes generalization bound

SSBD Theorem 31.1: for a `[0,1]`-valued loss, prior `P`, and `δ ∈ (0,1)`,
with probability `≥ 1 − δ` over `S ∼ Dⁿ`, **simultaneously for every**
(possibly sample-dependent) posterior `Q`,
`L_D(Q) ≤ L_S(Q) + √((D(Q‖P) + ln(2n/δ)) / (2(n−1)))`.

**Reference.** SSBD §31.1, Theorem 31.1 and Exercise 31.1. Transcription:
`notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** Proof chain exactly as the book: Markov on
`e^{f(S)}` for `f(S) = sup_Q (2(n−1) E_Q[Δ²] − D(Q‖P))`, change of measure +
Jensen (`ChangeOfMeasure.lean`) to kill the sup over `Q`, Fubini, the moment
lemma `E[e^{2(n−1)Δ(h)²}] ≤ 2n` from Hoeffding's two-sided tail, and Jensen
for `x²`. **Deviation from the book:** SSBD states `ln(m/δ)` from
`E[e^{2(m−1)Δ²}] ≤ m`, whose Exercise-31.1 derivation uses only the one-sided
tail `P[Δ ≥ ε] ≤ e^{−2mε²}` — but the exponent involves `Δ²`, which needs the
two-sided tail `P[|Δ| ≥ ε] ≤ 2e^{−2mε²}`; the honest constant is
`E ≤ 2m − 1 ≤ 2m`, so this file freezes `ln(2n/δ)`. The `∀ Q` inside the
event is genuine (the book's "even such that depend on `S`"): the event is
the sup-free moment inequality, from which every `Q` is handled pointwise.
-/

open MeasureTheory InformationTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z ι : Type*} [MeasurableSpace Z] [MeasurableSpace ι]
  [DiscreteMeasurableSpace ι] [Countable ι]

/-- **Moment bound from a sub-Gaussian tail** (SSBD Exercise 31.1, honest
two-sided form): if `P[|Y| ≥ ε] ≤ 2e^{−2nε²}` for all `ε > 0` and `2 ≤ n`,
then `E[e^{2(n−1)Y²}] ≤ 2n`. (Book claims `n` from the one-sided tail; the
`Δ²` exponent needs both tails, giving `2n − 1 ≤ 2n` — see module notes.) -/
theorem integral_exp_sq_le_of_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} {n : ℕ}
    -- LEAN-ONLY: measurability of `Y` (layer-cake regularity)
    (hY : Measurable Y)
    -- USER-INPUT: two-sided sub-Gaussian tail; SSBD Ex. 31.1 (corrected)
    (htail : ∀ ε : ℝ, 0 < ε →
      μ.real {ω | ε ≤ |Y ω|} ≤ 2 * Real.exp (-2 * n * ε ^ 2))
    -- USER-INPUT: `n ≥ 2`; SSBD Thm 31.1 (`m − 1 > 0`)
    (hn : 2 ≤ n) :
    ∫ ω, Real.exp (2 * (n - 1 : ℝ) * Y ω ^ 2) ∂μ ≤ 2 * n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hcpos : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  set s : ℝ := (n : ℝ) / ((n : ℝ) - 1) with hs
  have hs1 : 1 < s := by rw [hs, lt_div_iff₀ hn1]; linarith
  have hgnn : 0 ≤ᵐ[μ] fun ω => Real.exp (2 * ((n : ℝ) - 1) * Y ω ^ 2) :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hgm : Measurable fun ω => Real.exp (2 * ((n : ℝ) - 1) * Y ω ^ 2) :=
    (((hY.pow_const 2).const_mul _).exp)
  -- Tail bound for the level sets above `t = 1`, in the `rpow` form `2 t^{-s}`.
  have hbound : ∀ t ∈ Set.Ioi (1 : ℝ),
      μ {a | t ≤ Real.exp (2 * ((n : ℝ) - 1) * Y a ^ 2)} ≤
        ENNReal.ofReal (2 * t ^ (-s)) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have htpos : (0 : ℝ) < t := lt_trans one_pos ht1
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    have hqpos : 0 < Real.log t / (2 * ((n : ℝ) - 1)) := div_pos hlogt hcpos
    have hεpos : 0 < Real.sqrt (Real.log t / (2 * ((n : ℝ) - 1))) :=
      Real.sqrt_pos.mpr hqpos
    have hεsq : Real.sqrt (Real.log t / (2 * ((n : ℝ) - 1))) ^ 2
        = Real.log t / (2 * ((n : ℝ) - 1)) := Real.sq_sqrt hqpos.le
    have hsub : {a | t ≤ Real.exp (2 * ((n : ℝ) - 1) * Y a ^ 2)} ⊆
        {a | Real.sqrt (Real.log t / (2 * ((n : ℝ) - 1))) ≤ |Y a|} := by
      intro a ha
      simp only [Set.mem_setOf_eq] at ha ⊢
      have hlog : Real.log t ≤ 2 * ((n : ℝ) - 1) * Y a ^ 2 := by
        have := Real.log_le_log htpos ha
        rwa [Real.log_exp] at this
      have hq : Real.log t / (2 * ((n : ℝ) - 1)) ≤ Y a ^ 2 :=
        (div_le_iff₀ hcpos).mpr (by linarith)
      calc Real.sqrt (Real.log t / (2 * ((n : ℝ) - 1)))
          ≤ Real.sqrt (Y a ^ 2) := Real.sqrt_le_sqrt hq
        _ = |Y a| := Real.sqrt_sq_eq_abs _
    have hexpeq : Real.exp (-2 * (n : ℝ) *
        Real.sqrt (Real.log t / (2 * ((n : ℝ) - 1))) ^ 2) = t ^ (-s) := by
      rw [hεsq, Real.rpow_def_of_pos htpos, hs]
      congr 1
      field_simp
    have hmr : μ.real {a | Real.sqrt (Real.log t / (2 * ((n : ℝ) - 1))) ≤ |Y a|}
        ≤ 2 * t ^ (-s) := by
      rw [← hexpeq]; exact htail _ hεpos
    refine le_trans (measure_mono hsub) ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hmr
  -- Layer cake, split at `t = 1`.
  have hmain : ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * ((n : ℝ) - 1) * Y ω ^ 2)) ∂μ
      ≤ ENNReal.ofReal (2 * n) := by
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
      Set.Ioc_disjoint_Ioi le_rfl
    rw [lintegral_eq_lintegral_meas_le μ hgnn hgm.aemeasurable,
      ← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one (α := ℝ)),
      lintegral_union measurableSet_Ioi hdisj]
    have h1 : ∫⁻ t in Set.Ioc (0 : ℝ) 1,
        μ {a | t ≤ Real.exp (2 * ((n : ℝ) - 1) * Y a ^ 2)} ≤ 1 := by
      calc ∫⁻ t in Set.Ioc (0 : ℝ) 1,
            μ {a | t ≤ Real.exp (2 * ((n : ℝ) - 1) * Y a ^ 2)}
          ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) :=
            lintegral_mono fun _ => prob_le_one
        _ = 1 := by
            rw [lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ioc]
            norm_num
    have hint : IntegrableOn (fun t : ℝ => 2 * t ^ (-s)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul 2
    have hvalnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] fun t : ℝ => 2 * t ^ (-s) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have : (0 : ℝ) < t := lt_trans one_pos ht
      positivity
    have hval : ∫ t in Set.Ioi (1 : ℝ), 2 * t ^ (-s) = 2 * ((n : ℝ) - 1) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos]
      rw [Real.one_rpow, hs]
      field_simp
      have hne : -(n : ℝ) + ((n : ℝ) - 1) = -1 := by ring
      rw [hne]
      norm_num
    have h2 : ∫⁻ t in Set.Ioi (1 : ℝ),
        μ {a | t ≤ Real.exp (2 * ((n : ℝ) - 1) * Y a ^ 2)}
        ≤ ENNReal.ofReal (2 * ((n : ℝ) - 1)) := by
      calc ∫⁻ t in Set.Ioi (1 : ℝ),
            μ {a | t ≤ Real.exp (2 * ((n : ℝ) - 1) * Y a ^ 2)}
          ≤ ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * t ^ (-s)) :=
            setLIntegral_mono' measurableSet_Ioi hbound
        _ = ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), 2 * t ^ (-s)) :=
            (ofReal_integral_eq_lintegral_ofReal hint hvalnn).symm
        _ = ENNReal.ofReal (2 * ((n : ℝ) - 1)) := by rw [hval]
    calc _ ≤ 1 + ENNReal.ofReal (2 * ((n : ℝ) - 1)) := add_le_add h1 h2
      _ = ENNReal.ofReal (1 + 2 * ((n : ℝ) - 1)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by linarith), ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (2 * n) := ENNReal.ofReal_le_ofReal (by linarith)
  rw [integral_eq_lintegral_of_nonneg_ae hgnn hgm.aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (2 * ((n : ℝ) - 1) * Y ω ^ 2)) ∂μ).toReal
      ≤ (ENNReal.ofReal (2 * n)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 2 * n := ENNReal.toReal_ofReal (by positivity)

/-- Upgrade a strict two-sided tail `μ{ε < |V|} ≤ 2e^{−2nε²}` to the closed
form `μ{ε ≤ |V|} ≤ 2e^{−2nε²}`, by letting the level increase to `ε` from
below (the bound is continuous in the level). -/
private theorem measureReal_ge_le_of_measure_gt_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {V : Ω → ℝ} {m : ℕ}
    (h : ∀ ε : ℝ, 0 < ε →
      μ {ω | ε < |V ω|} ≤ ENNReal.ofReal (2 * Real.exp (-2 * m * ε ^ 2)))
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |V ω|} ≤ 2 * Real.exp (-2 * m * ε ^ 2) := by
  have hcont : Continuous fun x : ℝ => 2 * Real.exp (-2 * (m : ℝ) * x ^ 2) := by fun_prop
  have hlim : Filter.Tendsto (fun x : ℝ => 2 * Real.exp (-2 * (m : ℝ) * x ^ 2))
      (nhdsWithin ε (Set.Iio ε)) (nhds (2 * Real.exp (-2 * (m : ℝ) * ε ^ 2))) :=
    (hcont.tendsto ε).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  have hIoo : Set.Ioo (ε / 2) ε ∈ nhdsWithin ε (Set.Iio ε) :=
    mem_nhdsLT_iff_exists_Ioo_subset.mpr ⟨ε / 2, half_lt_self hε, subset_rfl⟩
  filter_upwards [hIoo] with x hx
  have hxpos : 0 < x := lt_trans (half_pos hε) hx.1
  have hsub : {ω | ε ≤ |V ω|} ⊆ {ω | x < |V ω|} := fun ω hω => lt_of_lt_of_le hx.2 hω
  have hle := le_trans (measure_mono hsub) (h x hxpos)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

/-- Jensen for `x ↦ x²` against a probability measure: `(E g)² ≤ E g²`. -/
private theorem sq_integral_le_integral_sq {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] {g : α → ℝ} (hg : MemLp g 2 ν) :
    (∫ a, g a ∂ν) ^ 2 ≤ ∫ a, g a ^ 2 ∂ν := by
  have h := ProbabilityTheory.variance_nonneg g ν
  rw [ProbabilityTheory.variance_eq_sub hg] at h
  simp only [Pi.pow_apply] at h
  linarith

/-- The deviation `Δ(k) = L_D(k) − L_S(k)` of SSBD (31.1). -/
private noncomputable def pbDev (D : Measure Z) (F : ι → Z → ℝ) {n : ℕ}
    (s : Sample Z n) (k : ι) : ℝ :=
  risk D F k - empRisk F s k

/-- The prior exponential moment `E_{k∼P}[e^{2(n−1)Δ(k)²}]` of SSBD (31.3). -/
private noncomputable def pbMoment (D : Measure Z) (P : Measure ι) (F : ι → Z → ℝ)
    {n : ℕ} (s : Sample Z n) : ℝ :=
  ∫ k, Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2) ∂P

/-- **SSBD Theorem 31.1 (PAC-Bayes)**: for a countable hypothesis index,
`[0,1]`-valued loss family `F`, prior `P`, and `δ ∈ (0,1)`, with probability
`≥ 1 − δ` over `S ∼ Dⁿ` (`n ≥ 2`), simultaneously for every posterior `Q ≪ P`
with finite KL,
`L_D(Q) ≤ L_S(Q) + √((D(Q‖P) + ln(2n/δ)) / (2(n−1)))`
(constant `2n` in place of the book's `n` — module notes). -/
theorem pac_bayes (D : Measure Z) [IsProbabilityMeasure D]
    (P : Measure ι) [IsProbabilityMeasure P] (F : ι → Z → ℝ) {n : ℕ}
    {δ : ℝ}
    -- USER-INPUT: loss range in `[0,1]`; SSBD Thm 31.1
    (hrange : ∀ k z, F k z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of the loss family; SSBD Remark 3.1
    (hmeas : ∀ k, Measurable (F k))
    -- USER-INPUT: `n ≥ 2`; SSBD Thm 31.1 (`m − 1 > 0` in the denominator)
    (hn : 2 ≤ n)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD Thm 31.1
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | ∀ Q : Measure ι,
        IsProbabilityMeasure Q → Q ≪ P → klDiv Q P ≠ ⊤ →
          gibbsAvg Q (fun k => risk D F k) ≤
            gibbsAvg Q (fun k => empRisk F s k) +
              Real.sqrt (((klDiv Q P).toReal + Real.log (2 * n / δ)) /
                (2 * (n - 1 : ℝ)))} := by
  have hn1' : 1 ≤ n := le_trans (by norm_num) hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hcpos : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  have hGbar : (0 : ℝ) < 2 * (n : ℝ) / δ := div_pos (by linarith) hδ
  -- (31.1) pointwise bounds on the deviation
  have hrisk : ∀ k : ι, risk D F k ∈ Set.Icc (0 : ℝ) 1 :=
    fun k => risk_mem_Icc (hrange k) (hmeas k)
  have hemp : ∀ (s : Sample Z n) (k : ι), empRisk F s k ∈ Set.Icc (0 : ℝ) 1 :=
    fun s k => empRisk_mem_Icc (hrange k) hn1' s
  have hdev : ∀ (s : Sample Z n) (k : ι), |pbDev D F s k| ≤ 1 := by
    intro s k
    have h1 := Set.mem_Icc.mp (hrisk k)
    have h2 := Set.mem_Icc.mp (hemp s k)
    simp only [pbDev, abs_le]
    constructor <;> [linarith [h1.1, h2.2]; linarith [h1.2, h2.1]]
  have hdevsq : ∀ (s : Sample Z n) (k : ι), pbDev D F s k ^ 2 ≤ 1 := by
    intro s k
    nlinarith [hdev s k, abs_nonneg (pbDev D F s k), sq_abs (pbDev D F s k)]
  have hexpbd : ∀ (s : Sample Z n) (k : ι),
      Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2) ≤
        Real.exp (2 * ((n : ℝ) - 1)) := by
    intro s k
    exact Real.exp_le_exp.mpr (by nlinarith [hdevsq s k])
  have hdevmeas : ∀ k : ι, Measurable fun s : Sample Z n => pbDev D F s k := by
    intro k
    simp only [pbDev]
    exact measurable_const.sub (measurable_empRisk (hmeas k))
  -- (31.4) the per-hypothesis exponential moment, from Hoeffding + Exercise 31.1
  have hmoment : ∀ k : ι,
      ∫ s, Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2) ∂(sampleLaw D n)
        ≤ 2 * n := by
    intro k
    refine integral_exp_sq_le_of_tail (hdevmeas k) ?_ hn
    refine measureReal_ge_le_of_measure_gt_le ?_
    intro x hx
    have hset : {s : Sample Z n | x < |pbDev D F s k|}
        = {s : Sample Z n | x < |empRisk F s k - risk D F k|} := by
      ext s
      simp only [Set.mem_setOf_eq, pbDev]
      rw [abs_sub_comm]
    rw [hset]
    exact measure_empRisk_deviation_le (hrange k) (hmeas k) hn1' hx
  -- joint measurability and integrability on the product `Dⁿ ⊗ P`
  have huc : Measurable (Function.uncurry fun (s : Sample Z n) (k : ι) =>
      Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2)) := by
    refine measurable_from_prod_countable_left ?_
    intro k
    exact (((hdevmeas k).pow_const 2).const_mul _).exp
  have hprod : Integrable (Function.uncurry fun (s : Sample Z n) (k : ι) =>
      Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2))
      ((sampleLaw D n).prod P) := by
    refine (integrable_const (Real.exp (2 * ((n : ℝ) - 1)))).mono'
      huc.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨s, k⟩
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    exact hexpbd s k
  -- (31.5) Fubini: the mean of the prior moment is at most `2n`
  have hGint : Integrable (fun s => pbMoment D P F s) (sampleLaw D n) := by
    simp only [pbMoment]
    exact hprod.integral_prod_left
  have hGnn : ∀ s : Sample Z n, 0 ≤ pbMoment D P F s := fun s =>
    integral_nonneg fun k => (Real.exp_pos _).le
  have hGmean : ∫ s, pbMoment D P F s ∂(sampleLaw D n) ≤ 2 * n := by
    have hswap : ∫ s, pbMoment D P F s ∂(sampleLaw D n)
        = ∫ k, (∫ s, Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2)
            ∂(sampleLaw D n)) ∂P := by
      simp only [pbMoment]
      exact integral_integral_swap hprod
    rw [hswap]
    calc ∫ k, (∫ s, Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2)
          ∂(sampleLaw D n)) ∂P
        ≤ ∫ _ : ι, (2 * (n : ℝ)) ∂P := by
          refine integral_mono_of_nonneg (ae_of_all _ fun k =>
            integral_nonneg fun s => (Real.exp_pos _).le) (integrable_const _)
            (ae_of_all _ hmoment)
      _ = 2 * n := by simp
  -- (31.6) Markov on the prior moment
  have hmarkov : (sampleLaw D n).real
      {s | 2 * (n : ℝ) / δ ≤ pbMoment D P F s} ≤ δ := by
    have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hGnn) hGint
      (2 * (n : ℝ) / δ)
    have h2 : 2 * (n : ℝ) / δ *
        (sampleLaw D n).real {s | 2 * (n : ℝ) / δ ≤ pbMoment D P F s} ≤ 2 * n :=
      le_trans h hGmean
    have h3 := (le_div_iff₀' hGbar).mpr h2
    have hδ' : δ ≠ 0 := ne_of_gt hδ
    have hnne : (2 : ℝ) * (n : ℝ) ≠ 0 := by positivity
    have heq : 2 * (n : ℝ) / (2 * (n : ℝ) / δ) = δ := by field_simp
    rwa [heq] at h3
  have hmarkovE : (sampleLaw D n) {s | 2 * (n : ℝ) / δ ≤ pbMoment D P F s}
      ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (sampleLaw D n) _)]
    exact ENNReal.ofReal_le_ofReal hmarkov
  -- the complement of the bad event implies the PAC-Bayes bound for every `Q`
  have hsubset : {s : Sample Z n | 2 * (n : ℝ) / δ ≤ pbMoment D P F s}ᶜ ⊆
      {s | ∀ Q : Measure ι, IsProbabilityMeasure Q → Q ≪ P → klDiv Q P ≠ ⊤ →
        gibbsAvg Q (fun k => risk D F k) ≤
          gibbsAvg Q (fun k => empRisk F s k) +
            Real.sqrt (((klDiv Q P).toReal + Real.log (2 * n / δ)) /
              (2 * (n - 1 : ℝ)))} := by
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hs
    intro Q hQ hQP hQkl
    haveI := hQ
    -- integrability of the bounded functionals
    have hdevQ : Integrable (fun k => pbDev D F s k) Q :=
      (integrable_const (1 : ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable
        (ae_of_all _ fun k => by rw [Real.norm_eq_abs]; exact hdev s k)
    have hsqQ : Integrable (fun k => pbDev D F s k ^ 2) Q :=
      (integrable_const (1 : ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable
        (ae_of_all _ fun k => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hdevsq s k)
    have hfQ : Integrable
        (fun k => 2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2) Q := hsqQ.const_mul _
    have hexpP : Integrable
        (fun k => Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2)) P :=
      (integrable_const (Real.exp (2 * ((n : ℝ) - 1)))).mono'
        Measurable.of_discrete.aestronglyMeasurable
        (ae_of_all _ fun k => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexpbd s k)
    have hriskQ : Integrable (fun k => risk D F k) Q :=
      (integrable_const (1 : ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable
        (ae_of_all _ fun k => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Set.mem_Icc.mp (hrisk k)).1]
          exact (Set.mem_Icc.mp (hrisk k)).2)
    have hempQ : Integrable (fun k => empRisk F s k) Q :=
      (integrable_const (1 : ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable
        (ae_of_all _ fun k => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Set.mem_Icc.mp (hemp s k)).1]
          exact (Set.mem_Icc.mp (hemp s k)).2)
    -- (31.2) change of measure
    have hcm := gibbsAvg_le_klDiv_add_log_integral_exp P Q
      (fun k => 2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2) hQP hQkl hfQ hexpP
    have hgibbs : gibbsAvg Q (fun k => 2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2)
        = 2 * ((n : ℝ) - 1) * ∫ k, pbDev D F s k ^ 2 ∂Q := by
      simp only [gibbsAvg]
      exact integral_const_mul _ _
    have hGpos : 0 < pbMoment D P F s := by
      have hone : (1 : ℝ) ≤ ∫ k, Real.exp (2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2) ∂P := by
        have hmono := integral_mono (integrable_const (1 : ℝ)) hexpP (fun k => by
          have h0 : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) * pbDev D F s k ^ 2 :=
            mul_nonneg hcpos.le (sq_nonneg _)
          have := Real.exp_le_exp.mpr h0
          rwa [Real.exp_zero] at this)
        simpa using hmono
      simpa only [pbMoment] using lt_of_lt_of_le one_pos hone
    have hlog : Real.log (pbMoment D P F s) ≤ Real.log (2 * (n : ℝ) / δ) :=
      Real.log_le_log hGpos hs.le
    -- Jensen for `x ↦ x²`
    have hmemlp : MemLp (fun k => pbDev D F s k) 2 Q :=
      (memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable 1
        (ae_of_all _ fun k => by rw [Real.norm_eq_abs]; exact hdev s k)).mono_exponent le_top
    have hjensen := sq_integral_le_integral_sq hmemlp
    have hdiff : ∫ k, pbDev D F s k ∂Q
        = gibbsAvg Q (fun k => risk D F k) - gibbsAvg Q (fun k => empRisk F s k) := by
      simp only [pbDev, gibbsAvg]
      exact integral_sub hriskQ hempQ
    rw [hdiff] at hjensen
    rw [hgibbs] at hcm
    -- assemble
    have hkey : (gibbsAvg Q (fun k => risk D F k) -
        gibbsAvg Q (fun k => empRisk F s k)) ^ 2 * (2 * ((n : ℝ) - 1))
        ≤ (klDiv Q P).toReal + Real.log (2 * (n : ℝ) / δ) := by
      have h1 : (gibbsAvg Q (fun k => risk D F k) -
          gibbsAvg Q (fun k => empRisk F s k)) ^ 2 * (2 * ((n : ℝ) - 1))
          ≤ (∫ k, pbDev D F s k ^ 2 ∂Q) * (2 * ((n : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right hjensen hcpos.le
      have h2 : (∫ k, pbDev D F s k ^ 2 ∂Q) * (2 * ((n : ℝ) - 1))
          = 2 * ((n : ℝ) - 1) * ∫ k, pbDev D F s k ^ 2 ∂Q := by ring
      simp only [pbMoment] at hlog
      linarith [hcm, hlog, h1, h2.le, h2.ge]
    have hB : (gibbsAvg Q (fun k => risk D F k) -
        gibbsAvg Q (fun k => empRisk F s k)) ^ 2
        ≤ ((klDiv Q P).toReal + Real.log (2 * (n : ℝ) / δ)) / (2 * ((n : ℝ) - 1)) :=
      (le_div_iff₀ hcpos).mpr hkey
    have hfin : gibbsAvg Q (fun k => risk D F k) -
        gibbsAvg Q (fun k => empRisk F s k) ≤
        Real.sqrt (((klDiv Q P).toReal + Real.log (2 * (n : ℝ) / δ)) /
          (2 * ((n : ℝ) - 1))) := by
      calc gibbsAvg Q (fun k => risk D F k) - gibbsAvg Q (fun k => empRisk F s k)
          ≤ |gibbsAvg Q (fun k => risk D F k) - gibbsAvg Q (fun k => empRisk F s k)| :=
            le_abs_self _
        _ = Real.sqrt ((gibbsAvg Q (fun k => risk D F k) -
              gibbsAvg Q (fun k => empRisk F s k)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ _ := Real.sqrt_le_sqrt hB
    linarith [hfin]
  -- complement bookkeeping
  have hcover : (1 : ℝ≥0∞) ≤
      sampleLaw D n {s | ∀ Q : Measure ι, IsProbabilityMeasure Q → Q ≪ P →
        klDiv Q P ≠ ⊤ →
          gibbsAvg Q (fun k => risk D F k) ≤
            gibbsAvg Q (fun k => empRisk F s k) +
              Real.sqrt (((klDiv Q P).toReal + Real.log (2 * n / δ)) /
                (2 * (n - 1 : ℝ)))} + ENNReal.ofReal δ := by
    calc (1 : ℝ≥0∞) = sampleLaw D n Set.univ := (measure_univ).symm
      _ = sampleLaw D n
            ({s : Sample Z n | 2 * (n : ℝ) / δ ≤ pbMoment D P F s}ᶜ ∪
              {s : Sample Z n | 2 * (n : ℝ) / δ ≤ pbMoment D P F s}) := by
          rw [Set.compl_union_self]
      _ ≤ sampleLaw D n {s : Sample Z n | 2 * (n : ℝ) / δ ≤ pbMoment D P F s}ᶜ +
            sampleLaw D n {s : Sample Z n | 2 * (n : ℝ) / δ ≤ pbMoment D P F s} :=
          measure_union_le _ _
      _ ≤ _ := add_le_add (measure_mono hsubset) hmarkovE
  rw [ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]
  exact tsub_le_iff_right.mpr hcover

end StatLean.StatisticalLearning
