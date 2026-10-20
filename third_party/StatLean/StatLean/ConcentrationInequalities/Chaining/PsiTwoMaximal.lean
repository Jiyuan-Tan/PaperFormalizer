module
public import StatLean.ConcentrationInequalities.Orlicz.Defs
public import StatLean.ConcentrationInequalities.Orlicz.SubGaussianTail
public import StatLean.ConcentrationInequalities.Chaining.TailToExpectation
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# ψ₂-norm maximal inequality (no centering)

For $N$ (not necessarily centered, not necessarily independent) random
variables with $\|Y_i\|_{\psi_2} \le L$,
$$ \mathbb{P}\Bigl(\max_{i \le N} |Y_i| > \tau\Bigr) \le 2 N e^{-\tau^2/L^2},
   \qquad
   \mathbb{E}\Bigl[\max_{i \le N} |Y_i|\Bigr] \le 2 L \sqrt{\log(2N)}, $$
together with the first-moment bound $\mathbb{E}|Y| \le \sqrt{\pi}\, L$.
This is the per-level engine for the *no-mean-zero* two-sided chaining forms
(8.13)/(8.14)/(8.15), which the book stresses require no centering.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.5, Eq. (2.22) / Exercise 2.5.10 (maximal
inequality in ψ₂-norm), §2.5.2 (moment equivalences).

**Proof formalization notes.** Bridge-B1 consumption
(`measure_abs_ge_le_of_subGaussianNorm_le`, normalization `c = 1`, tail
`2exp(−τ²/L²)`) is confined to this file and to
`Chaining/SubGaussianIncrements.lean`. The route is B1 per-variable tail +
union bound + layer-cake (`Chaining/TailToExpectation.lean`) — deliberately
avoiding centering / ψ₂-norm-of-a-constant lemmas that are outside the frozen
Orlicz interface. Committed constants (book's unnamed absolute constants):
expectation bound `2·L·√(log(2N))` — split the layer cake at
`a = L√(log(2N))`; the Gaussian-tail remainder is
`≤ L/(2√log 2) ≤ 0.74·L√(log(2N))`, slack to the frozen numeral `2`. First
moment: `E|Y| ≤ ∫₀^∞ 2exp(−t²/L²) dt = √π·L`, exact. All tail lemmas carry
`[IsProbabilityMeasure μ]` (bridge B1 requires it). Named-sorry fallback of
this work item: `expectation_abs_max_le` (with `tail_abs_max_le` and the
first moment proved; `DudleyTail` needs only the tail form).

**Bibliographic comments.** Maximal inequalities under ψ₂-norm bounds are
folklore consequences of the Cramér–Chernoff method and Orlicz-norm calculus;
systematic treatments are Buldygin–Kozachenko, *Metric Characterization of
Random Variables and Random Processes*, AMS 2000, and van der Vaart–Wellner,
*Weak Convergence and Empirical Processes*, Springer 1996, §2.2 (Orlicz-norm
maximal inequalities).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **ψ₂ maximal inequality — tail bound** (HDP §2.5, Eq. (2.22)): union
bound over the B1 per-variable tails, no centering. -/
theorem tail_abs_max_le {ι : Type*}
    -- USER-INPUT: probability-space context (bridge B1 requires it); HDP §2.5
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hs : s.Nonempty) {Y : ι → Ω → ℝ} {L : ℝ≥0}
    -- LEAN-ONLY: nondegenerate scale so the tail RHS is meaningful
    (hL : 0 < L)
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hm : ∀ i ∈ s, AEMeasurable (Y i) μ)
    -- USER-INPUT: uniform ψ₂-norm bound ‖Y_i‖_{ψ₂} ≤ L; HDP §2.5, Eq (2.22)
    (hY : ∀ i ∈ s, subGaussianNorm (Y i) μ ≤ (L : ℝ≥0∞))
    -- USER-INPUT: τ ≥ 0; HDP §2.5
    {τ : ℝ} (hτ : 0 ≤ τ) :
    μ {ω | τ < ⨆ i ∈ s, |Y i ω|}
      ≤ ENNReal.ofReal (2 * (s.card : ℝ) * Real.exp (-τ ^ 2 / (L : ℝ) ^ 2)) := by
  -- The max exceeds `τ` only if some coordinate does.
  have hsub : {ω | τ < ⨆ i ∈ s, |Y i ω|} ⊆ ⋃ i ∈ s, {ω | τ ≤ |Y i ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    have hle : (⨆ i ∈ s, |Y i ω|) ≤ τ :=
      Real.iSup_le (fun i => Real.iSup_le (fun hi => (hcon i hi).le) hτ) hτ
    linarith
  calc μ {ω | τ < ⨆ i ∈ s, |Y i ω|}
      ≤ μ (⋃ i ∈ s, {ω | τ ≤ |Y i ω|}) := measure_mono hsub
    _ ≤ ∑ i ∈ s, μ {ω | τ ≤ |Y i ω|} := measure_biUnion_finset_le s _
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal (2 * Real.exp (-τ ^ 2 / (L : ℝ) ^ 2)) :=
        Finset.sum_le_sum fun i hi =>
          measure_abs_ge_le_of_subGaussianNorm_le (hm i hi) hL (hY i hi) hτ
    _ = ENNReal.ofReal (2 * (s.card : ℝ) * Real.exp (-τ ^ 2 / (L : ℝ) ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; ring

/-- **First moment from the ψ₂-norm** (HDP §2.5.2): layer-cake over the B1
tail, `E|Y| ≤ ∫₀^∞ 2exp(−t²/L²) dt = √π·L` (exact constant). -/
theorem integral_abs_le_of_subGaussianNorm_le
    -- USER-INPUT: probability-space context (bridge B1 requires it); HDP §2.5
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {L : ℝ≥0}
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hm : AEMeasurable Y μ)
    -- USER-INPUT: ψ₂-norm bound ‖Y‖_{ψ₂} ≤ L; HDP §2.5.2
    (hY : subGaussianNorm Y μ ≤ (L : ℝ≥0∞)) :
    ∫ ω, |Y ω| ∂μ ≤ Real.sqrt Real.pi * L := by
  -- For any strictly positive scale `K ≥ ‖Y‖_{ψ₂}`, the tail-to-expectation step gives
  -- `E|Y| ≤ √π·K`.  Taking `K ↓ L` yields the claim (covers `L = 0` uniformly).
  have key : ∀ K : ℝ≥0, 0 < K → subGaussianNorm Y μ ≤ (K : ℝ≥0∞) →
      ∫ ω, |Y ω| ∂μ ≤ Real.sqrt Real.pi * (K : ℝ) := by
    intro K hKpos hYK
    have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
    have htail : ∀ u : ℝ, 0 ≤ u →
        μ {ω | 0 + (K : ℝ) * u < |Y ω|} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
      intro u hu
      have ht0 : (0 : ℝ) ≤ (K : ℝ) * u := mul_nonneg K.coe_nonneg hu
      have hbr := measure_abs_ge_le_of_subGaussianNorm_le (hm) hKpos hYK ht0
      have heq : -((K : ℝ) * u) ^ 2 / (K : ℝ) ^ 2 = -u ^ 2 := by field_simp
      calc μ {ω | 0 + (K : ℝ) * u < |Y ω|}
          ≤ μ {ω | (K : ℝ) * u ≤ |Y ω|} :=
            measure_mono fun ω hω => le_of_lt (by simpa using hω)
        _ ≤ ENNReal.ofReal (2 * Real.exp (-((K : ℝ) * u) ^ 2 / (K : ℝ) ^ 2)) := hbr
        _ = ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by rw [heq]
    have := integral_le_of_tail_le hm.abs
      (Filter.Eventually.of_forall fun ω => abs_nonneg _) le_rfl K.coe_nonneg htail
    simpa using this
  -- shrink `K = L + δ` to `L`
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hδ : 0 < (c - Real.sqrt Real.pi * L) / Real.sqrt Real.pi :=
    div_pos (by linarith) hπ
  set δ : ℝ≥0 := ((c - Real.sqrt Real.pi * L) / Real.sqrt Real.pi).toNNReal with hδdef
  have hδpos : 0 < δ := Real.toNNReal_pos.mpr hδ
  have hK : (0 : ℝ≥0) < L + δ := hδpos.trans_le le_add_self
  have hYK : subGaussianNorm Y μ ≤ ((L + δ : ℝ≥0) : ℝ≥0∞) :=
    hY.trans (by exact_mod_cast le_add_of_nonneg_right (zero_le (a := δ)))
  have hbd := key (L + δ) hK hYK
  have hval : Real.sqrt Real.pi * ((L + δ : ℝ≥0) : ℝ) = c := by
    have hcoe : (δ : ℝ) = (c - Real.sqrt Real.pi * L) / Real.sqrt Real.pi := by
      rw [hδdef]; exact Real.coe_toNNReal _ hδ.le
    push_cast
    rw [mul_add, hcoe]
    field_simp [hπ.ne']
    ring
  rw [hval] at hbd
  exact hbd

-- Raised limit: the finite `⨆ i ∈ s` carrier forces expensive `whnf` unfolding of the
-- `Finset`-to-`Set` coercion when discharging the `AEMeasurable.biSup` measurability side goal.
set_option maxHeartbeats 1000000 in
/-- **ψ₂ maximal inequality — expectation bound** (HDP §2.5, Eq. (2.22)):
`E max|Y_i| ≤ 2·L·√(log(2N))`, no centering. Frozen numeral `2` (split at
`L√(log 2N)`; Gaussian-tail remainder ≤ 0.74·L√(log 2N), see file notes). -/
theorem expectation_abs_max_le {ι : Type*}
    -- USER-INPUT: probability-space context; HDP §2.5
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hs : s.Nonempty) {Y : ι → Ω → ℝ} {L : ℝ≥0}
    -- LEAN-ONLY: nondegenerate scale for the split-point optimization
    (hL : 0 < L)
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hm : ∀ i ∈ s, AEMeasurable (Y i) μ)
    -- USER-INPUT: uniform ψ₂-norm bound ‖Y_i‖_{ψ₂} ≤ L; HDP §2.5, Eq (2.22)
    (hY : ∀ i ∈ s, subGaussianNorm (Y i) μ ≤ (L : ℝ≥0∞)) :
    ∫ ω, ⨆ i ∈ s, |Y i ω| ∂μ
      ≤ 2 * (L : ℝ) * Real.sqrt (Real.log (2 * s.card)) := by
  classical
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hcard : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hs.card_pos
  -- `log(2N) ≥ 1/2`, so the Gaussian-tail remainder is dominated by the split point.
  have hlog2N : (1 : ℝ) / 2 ≤ Real.log (2 * s.card) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hehalf : Real.exp (1 / 2) ≤ 2 := by
      have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ), hsq]
    nlinarith [hcard, hehalf]
  have hlogpos : 0 < Real.log (2 * s.card) := by linarith
  have hS : 0 < Real.sqrt (Real.log (2 * s.card)) := Real.sqrt_pos.mpr hlogpos
  set S : ℝ := Real.sqrt (Real.log (2 * s.card)) with hSdef
  have hS2 : S ^ 2 = Real.log (2 * s.card) := Real.sq_sqrt hlogpos.le
  set a₀ : ℝ := (L : ℝ) * S with ha₀def
  have ha₀pos : 0 < a₀ := by rw [ha₀def]; positivity
  have hβ : (0 : ℝ) < 1 / (L : ℝ) ^ 2 := by positivity
  -- nonnegativity and measurability of the max
  have hZnn : 0 ≤ᵐ[μ] fun ω => ⨆ i ∈ s, |Y i ω| :=
    Filter.Eventually.of_forall fun ω =>
      Real.iSup_nonneg fun i => Real.iSup_nonneg fun _ => abs_nonneg _
  have hZm : AEMeasurable (fun ω => ⨆ i ∈ s, |Y i ω|) μ :=
    AEMeasurable.biSup (↑s) s.finite_toSet.countable
      fun i hi => (hm i (Finset.mem_coe.mp hi)).abs
  -- the union-bound tail
  have htail : ∀ t : ℝ, 0 ≤ t → μ {ω | t < ⨆ i ∈ s, |Y i ω|}
      ≤ ENNReal.ofReal (2 * (s.card : ℝ) * Real.exp (-t ^ 2 / (L : ℝ) ^ 2)) :=
    fun t ht => tail_abs_max_le hs hL hm hY ht
  -- integrability of the Gaussian majorant on `(a₀, ∞)`
  have hInt : MeasureTheory.IntegrableOn
      (fun t => 2 * (s.card : ℝ) * Real.exp (-t ^ 2 / (L : ℝ) ^ 2)) (Set.Ioi a₀) := by
    have heqfun : (fun t : ℝ => 2 * (s.card : ℝ) * Real.exp (-t ^ 2 / (L : ℝ) ^ 2))
        = fun t => 2 * (s.card : ℝ) * Real.exp (-(1 / (L : ℝ) ^ 2) * t ^ 2) := by
      funext t; rw [show -t ^ 2 / (L : ℝ) ^ 2 = -(1 / (L : ℝ) ^ 2) * t ^ 2 by ring]
    rw [heqfun]
    exact ((integrable_exp_neg_mul_sq hβ).const_mul _).integrableOn
  -- the value bound on the tail integral: `L/(2S)`
  have hval : (∫ t in Set.Ioi a₀, 2 * (s.card : ℝ) * Real.exp (-t ^ 2 / (L : ℝ) ^ 2))
      ≤ (L : ℝ) / (2 * S) := by
    have hcongr : (∫ t in Set.Ioi a₀, 2 * (s.card : ℝ) * Real.exp (-t ^ 2 / (L : ℝ) ^ 2))
        = 2 * (s.card : ℝ) * ∫ t in Set.Ioi a₀, Real.exp (-(1 / (L : ℝ) ^ 2) * t ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [show -t ^ 2 / (L : ℝ) ^ 2 = -(1 / (L : ℝ) ^ 2) * t ^ 2 by ring]
    rw [hcongr]
    have hb := integral_exp_neg_mul_sq_Ioi_le ha₀pos hβ
    have hexp : Real.exp (-(1 / (L : ℝ) ^ 2) * a₀ ^ 2) = 1 / (2 * (s.card : ℝ)) := by
      rw [ha₀def, show -(1 / (L : ℝ) ^ 2) * ((L : ℝ) * S) ^ 2 = -(S ^ 2) by field_simp,
        hS2, Real.exp_neg, Real.exp_log (by positivity), one_div]
    calc 2 * (s.card : ℝ) * ∫ t in Set.Ioi a₀, Real.exp (-(1 / (L : ℝ) ^ 2) * t ^ 2)
        ≤ 2 * (s.card : ℝ)
            * (Real.exp (-(1 / (L : ℝ) ^ 2) * a₀ ^ 2) / (2 * (1 / (L : ℝ) ^ 2) * a₀)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (L : ℝ) / (2 * S) := by
          rw [hexp, ha₀def]; field_simp
  -- assemble via the layer cake
  have hlint : ∫⁻ ω, ENNReal.ofReal ((⨆ i ∈ s, |Y i ω|)) ∂μ
      ≤ ENNReal.ofReal (a₀ + (L : ℝ) / (2 * S)) := by
    rw [MeasureTheory.lintegral_eq_lintegral_meas_lt μ hZnn hZm,
        ← Set.Ioc_union_Ioi_eq_Ioi ha₀pos.le,
        MeasureTheory.lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl),
        ENNReal.ofReal_add ha₀pos.le (by positivity)]
    refine add_le_add ?_ ?_
    · calc ∫⁻ t in Set.Ioc 0 a₀, μ {ω | t < ⨆ i ∈ s, |Y i ω|}
          ≤ ∫⁻ _ in Set.Ioc 0 a₀, 1 :=
            lintegral_mono fun t => (measure_mono (Set.subset_univ _)).trans_eq measure_univ
        _ = volume (Set.Ioc 0 a₀) := MeasureTheory.setLIntegral_one _
        _ = ENNReal.ofReal a₀ := by rw [Real.volume_Ioc, sub_zero]
    · calc ∫⁻ t in Set.Ioi a₀, μ {ω | t < ⨆ i ∈ s, |Y i ω|}
          ≤ ∫⁻ t in Set.Ioi a₀,
              ENNReal.ofReal (2 * (s.card : ℝ) * Real.exp (-t ^ 2 / (L : ℝ) ^ 2)) := by
            refine lintegral_mono_ae ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
              (Filter.Eventually.of_forall fun t ht => htail t (le_of_lt (lt_trans ha₀pos ht))))
        _ = ENNReal.ofReal
              (∫ t in Set.Ioi a₀, 2 * (s.card : ℝ) * Real.exp (-t ^ 2 / (L : ℝ) ^ 2)) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
              (Filter.Eventually.of_forall fun t => by positivity)).symm
        _ ≤ ENNReal.ofReal ((L : ℝ) / (2 * S)) := ENNReal.ofReal_le_ofReal hval
  -- convert to the Bochner integral and finish the arithmetic
  rw [integral_eq_lintegral_of_nonneg_ae hZnn hZm.aestronglyMeasurable]
  have harith : a₀ + (L : ℝ) / (2 * S) ≤ 2 * (L : ℝ) * S := by
    have hSsq : (1 : ℝ) / 2 ≤ S ^ 2 := by rw [hS2]; exact hlog2N
    have hLS : (L : ℝ) / (2 * S) ≤ (L : ℝ) * S := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * S)]
      nlinarith [mul_le_mul_of_nonneg_left hSsq hLR.le]
    rw [ha₀def]; linarith [hLS]
  calc (∫⁻ ω, ENNReal.ofReal ((⨆ i ∈ s, |Y i ω|)) ∂μ).toReal
      ≤ (ENNReal.ofReal (a₀ + (L : ℝ) / (2 * S))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = a₀ + (L : ℝ) / (2 * S) := ENNReal.toReal_ofReal (by positivity)
    _ ≤ 2 * (L : ℝ) * S := harith

-- Raised limit: the finite `⨆ i ∈ s` carrier forces expensive `whnf` unfolding of the
-- `Finset`-to-`Set` coercion when discharging the `AEMeasurable.biSup` measurability side goal.
set_option maxHeartbeats 1000000 in
/-- Integrability of the finite maximum of ψ₂-bounded variables, derived from
the tail bound (never hypothesized downstream). -/
lemma integrable_biSup_abs {ι : Type*}
    -- USER-INPUT: probability-space context; HDP §2.5
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hs : s.Nonempty) {Y : ι → Ω → ℝ} {L : ℝ≥0}
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hm : ∀ i ∈ s, AEMeasurable (Y i) μ)
    -- USER-INPUT: uniform ψ₂-norm bound ‖Y_i‖_{ψ₂} ≤ L; HDP §2.5
    (hY : ∀ i ∈ s, subGaussianNorm (Y i) μ ≤ (L : ℝ≥0∞)) :
    MeasureTheory.Integrable (fun ω => ⨆ i ∈ s, |Y i ω|) μ := by
  -- Each `|Y i|` is integrable (a strictly-positive scale gives a finite `∫⁻`).
  have hYint : ∀ i ∈ s, MeasureTheory.Integrable (fun ω => |Y i ω|) μ := by
    intro i hi
    have hKpos : (0 : ℝ≥0) < L + 1 := by positivity
    have hKne : ((L + 1 : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
    have hYK : subGaussianNorm (Y i) μ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) :=
      (hY i hi).trans (by exact_mod_cast le_add_of_nonneg_right zero_le_one)
    have htail : ∀ u : ℝ, 0 ≤ u →
        μ {ω | 0 + ((L + 1 : ℝ≥0) : ℝ) * u < |Y i ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
      intro u hu
      have ht0 : (0 : ℝ) ≤ ((L + 1 : ℝ≥0) : ℝ) * u := mul_nonneg (L + 1).coe_nonneg hu
      have hbr := measure_abs_ge_le_of_subGaussianNorm_le (hm i hi) hKpos hYK ht0
      have heq : -(((L + 1 : ℝ≥0) : ℝ) * u) ^ 2 / ((L + 1 : ℝ≥0) : ℝ) ^ 2 = -u ^ 2 := by
        field_simp
      calc μ {ω | 0 + ((L + 1 : ℝ≥0) : ℝ) * u < |Y i ω|}
          ≤ μ {ω | ((L + 1 : ℝ≥0) : ℝ) * u ≤ |Y i ω|} :=
            measure_mono fun ω hω => le_of_lt (by simpa using hω)
        _ ≤ ENNReal.ofReal
              (2 * Real.exp (-(((L + 1 : ℝ≥0) : ℝ) * u) ^ 2 / ((L + 1 : ℝ≥0) : ℝ) ^ 2)) := hbr
        _ = ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by rw [heq]
    have hlint := lintegral_ofReal_le_of_tail_le (hm i hi).abs
      (Filter.Eventually.of_forall fun ω => abs_nonneg _) le_rfl (L + 1).coe_nonneg htail
    refine ⟨(hm i hi).abs.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => abs_nonneg _)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  -- The finite max is dominated by the (integrable) sum of the `|Y i|`.
  have hsum : MeasureTheory.Integrable (fun ω => ∑ i ∈ s, |Y i ω|) μ :=
    MeasureTheory.integrable_finset_sum s hYint
  have hmeas : AEMeasurable (fun ω => ⨆ i ∈ s, |Y i ω|) μ :=
    AEMeasurable.biSup (↑s) s.finite_toSet.countable
      fun i hi => (hm i (Finset.mem_coe.mp hi)).abs
  refine hsum.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hnn : (0 : ℝ) ≤ ⨆ i ∈ s, |Y i ω| :=
    Real.iSup_nonneg fun i => Real.iSup_nonneg fun _ => abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact Real.iSup_le
    (fun i => Real.iSup_le
      (fun hi => Finset.single_le_sum (f := fun j => |Y j ω|) (fun j _ => abs_nonneg _) hi)
      (Finset.sum_nonneg fun j _ => abs_nonneg _))
    (Finset.sum_nonneg fun j _ => abs_nonneg _)

end StatLean.ConcentrationInequalities
