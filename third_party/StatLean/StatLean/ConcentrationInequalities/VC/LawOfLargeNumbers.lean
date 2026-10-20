module
public import StatLean.ConcentrationInequalities.VC.CoveringByVC
public import StatLean.ConcentrationInequalities.VC.EntropyIntegral
public import StatLean.ConcentrationInequalities.Symmetrization.Rademacher
public import StatLean.ConcentrationInequalities.Symmetrization.Empirical
public import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
public import StatLean.ConcentrationInequalities.Chaining.DudleyConsumers
public import StatLean.ConcentrationInequalities.Orlicz.TailToNorm
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Order.Lattice

@[expose] public section

/-!
# VC law of large numbers (Theorem 8.3.15) — finite-class core

For an i.i.d. sample $X_1, \dots, X_n \sim \mu$ and a finite class
$\mathcal{F}$ of measurable sets with $\mathrm{vc}(\mathcal{F}) \le d$
($d \ge 1$),
$$ \mathbb{E}\,\max_{S \in \mathcal{F}}
   \bigl|\mu_n(S) - \mu(S)\bigr|
   \;\le\; 5400\,\sqrt{\frac{d}{n}}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.6, Theorem 8.3.15 (the book's unnamed
absolute constant `C`).

**Proof formalization notes.** This is the ONLY VC file touching other
Batch-10 clusters; all contact is confined to the adapter lemmas here.
Pipeline: (1) `symmetrization_adapter` cites the symmetrization cluster's
Exercise 8.11 (`empirical_symmetrization`, instantiated at `ι := ↥F` via
`Set.indicator`, `Fin n ↔ ℕ` by precomposition, and
`∫ 𝟙_S dμ = μ.real S` via `integral_indicator_one_real`) — factor `2`.
(2) Per fixed sample `x`, the Rademacher linear process `Z_v(e) = ⟨e, v⟩`
on the symmetrized empirical projection
`T' := empProj x '' F ∪ (−(empProj x '' F)) ⊆ closedBall 0 1` has
sub-Gaussian increments with `K = √6` (`subGaussianIncrements_inner_signVec`:
coordinate Rademachers via `iIndepFun_eval_signVec`, each `e i · c` bounded
in `[−|c|, |c|]` so `HasSubgaussianMGF` with proxy `c²` via
`hasSubgaussianMGF_of_mem_Icc`, summed by
`HasSubgaussianMGF.sum_of_iIndepFun` to proxy `‖v − w‖²`, then bridged to
`subGaussianNorm ≤ √6 · dist` by the orlicz bridge B3
`subGaussianNorm_le_of_isSubGaussian`). (3) The chaining cluster's
`dudley_inequality_abs_of_finite` (frozen constant `40`) with the SAMPLE-INDEPENDENT
entropy bound `N(T', ε) ≤ (4/ε)^{22d}` from `coveringNumber_empProj_le` —
valid pointwise in the sample because Theorem 8.3.13 holds for *every*
probability measure, in particular the random empirical measure; the
unconditioning is `integral_mono` against a constant plus Fubini
(`MeasureTheory.integral_integral_swap` / `Measure.prod`). (4) The entropy
integral `≤ 27√d` is `entropyIntegral_le` (`VC/EntropyIntegral.lean`).

**Constants (frozen numerals, recomputed from the batch's frozen
interfaces — DEVIATION from the design's provisional 500/1000).**
Conditional Rademacher step: `40 · √6 · 27 = 1080·√6 ≈ 2645.5 ≤ 2700`
(frozen `2700` in `rademacher_process_expectation_le`). Headline:
`2 × 2700 = 5400` (frozen `5400` in `vc_lln_finset`; formula
`2 (symmetrization, Ex 8.11) × 40 (dudley_inequality_abs_of_finite) × √6 (B3 bridge)
× 27 (entropy integral) = 2160·√6 ≈ 5290.9 ≤ 5400`). Downstream consumers
scale linearly: `5400/√n` (Glivenko–Cantelli), `2·5400 = 10800`
(generalization). Named-sorry fallback of this work item:
`rademacher_process_expectation_le` (the conditional Dudley glue over the
three cross-cluster stubs); `symmetrization_adapter` and the Fubini
assembly must close.

**Bibliographic comments.** The uniform LLN over VC classes is the
Vapnik–Chervonenkis theorem (*Theory Probab. Appl.* 16 (1971), 264–280);
the `√(d/n)` rate through Dudley's entropy integral and Haussler-type
covering bounds follows R. M. Dudley (*Ann. Probab.* 6 (1978), 899–929)
and D. Haussler (*J. Combin. Theory Ser. A* 69 (1995), 217–232).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `∫ 𝟙_S dμ = μ.real S` in the `(fun _ => (1 : ℝ))` indicator form used by
`empFrac` (LEAN-ONLY adapter for instantiating Exercise 8.11 at indicator
classes; no book content). -/
lemma integral_indicator_one_real {μ : Measure Ω} {S : Set Ω}
    -- LEAN-ONLY: measurability so the indicator integral evaluates.
    (hS : MeasurableSet S) :
    ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real S := by
  rw [integral_indicator_const (1 : ℝ) hS, measureReal_def, smul_eq_mul, mul_one]

/-- `Finset.sup'` equals the subtype-indexed `ciSup` (LEAN-ONLY adapter
between the sup policy's finite core and Exercise 8.11's `⨆ k : ι` shape;
no book content). -/
lemma finset_sup'_eq_iSup_subtype {α : Type*} {F : Finset α}
    (hFne : F.Nonempty) (f : α → ℝ) :
    F.sup' hFne f = ⨆ k : {S // S ∈ F}, f (k : α) := by
  rw [Finset.sup'_eq_csSup_image, Set.image_eq_range]
  rfl

/-- **The Rademacher linear process has sub-Gaussian increments** (R6 named
lemma; HDP §8.3.6, Theorem 8.3.15 proof step): on any index set
`T ⊆ ℝⁿ`, the process `Z_v(e) = ∑ᵢ eᵢ vᵢ` under the Rademacher sign vector
`signVec n` satisfies `‖Z_v − Z_w‖_{ψ₂} ≤ √6 · dist v w` — coordinate
independence (`iIndepFun_eval_signVec`) + bounded-increment MGF
(`hasSubgaussianMGF_of_mem_Icc`, `HasSubgaussianMGF.sum_of_iIndepFun`,
proxy `‖v − w‖²`) + the orlicz bridge B3
(`subGaussianNorm_le_of_isSubGaussian`, factor `√6`). -/
lemma subGaussianIncrements_inner_signVec {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    SubGaussianIncrements
      (fun (v : EuclideanSpace ℝ (Fin n)) (e : Fin n → ℝ) => ∑ i, e i * v i)
      (NNReal.sqrt 6) T (signVec n) := by
  intro v _hv w _hw
  have hev : ∀ i, Measurable (fun e : Fin n → ℝ => e i) := fun i => measurable_pi_apply i
  set c : Fin n → ℝ := fun i => w i - v i with hc
  -- the increment `Z_w − Z_v` is `e ↦ ∑ i, e i · (w i − v i)`
  have hfun : (fun e : Fin n → ℝ => (∑ i, e i * w i) - ∑ i, e i * v i)
      = fun e => ∑ i, e i * c i := by
    funext e
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hc]; ring
  set σ2 : ℝ≥0 := ∑ i, ‖c i‖₊ ^ 2 with hσ2
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun i e => e i * c i with hY
  -- coordinatewise independence
  have hY_indep : ProbabilityTheory.iIndepFun Y (signVec n) :=
    (iIndepFun_eval_signVec n).comp (fun i (x : ℝ) => x * c i)
      (fun i => measurable_id.mul_const (c i))
  -- coordinate means vanish
  have hmean_i : ∀ i, ∫ e, Y i e ∂(signVec n) = 0 := by
    intro i
    have h0 : ∫ e, e i ∂(signVec n) = 0 := by
      have hmap := (measurePreserving_eval_signVec n i).map_eq
      have hrw : ∫ e, e i ∂(signVec n) = ∫ x, x ∂radLaw := by
        rw [← hmap]
        exact (integral_map (hev i).aemeasurable
          measurable_id.aestronglyMeasurable).symm
      rw [hrw]; exact radLaw_integral_id
    calc ∫ e, Y i e ∂(signVec n)
        = (∫ e, e i ∂(signVec n)) * c i := by simp only [hY]; rw [integral_mul_const]
      _ = 0 := by rw [h0, zero_mul]
  -- coordinate integrability
  have hY_int : ∀ i, MeasureTheory.Integrable (Y i) (signVec n) := by
    intro i
    refine MeasureTheory.Integrable.of_bound ?_ |c i| ?_
    · simp only [hY]
      exact ((hev i).mul_const (c i)).aestronglyMeasurable
    · filter_upwards [signVec_ae_pm n] with e he
      rcases he i with h | h <;> simp [hY, h, Real.norm_eq_abs]
  -- coordinate sub-Gaussian MGF with proxy `(w i − v i)²`
  have hY_mgf : ∀ i,
      ProbabilityTheory.HasSubgaussianMGF (Y i) (‖c i‖₊ ^ 2) (signVec n) := by
    intro i
    have hb : ∀ᵐ e ∂(signVec n), Y i e ∈ Set.Icc (-|c i|) (|c i|) := by
      filter_upwards [signVec_ae_pm n] with e he
      rw [Set.mem_Icc, ← abs_le]
      rcases he i with h | h <;> simp [hY, h, abs_neg]
    have hmeas : AEMeasurable (Y i) (signVec n) := by
      simp only [hY]
      exact ((hev i).mul_const (c i)).aemeasurable
    have hzero : (signVec n)[Y i] = 0 := hmean_i i
    have hmgf := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hmeas hb hzero
    have hpx : (‖(|c i|) - (-|c i|)‖₊ / 2) ^ 2 = ‖c i‖₊ ^ 2 := by
      have h2 : (|c i|) - (-|c i|) = 2 * |c i| := by ring
      rw [h2]
      apply NNReal.coe_injective
      push_cast
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |c i|)]
      ring
    rwa [hpx] at hmgf
  -- sum over coordinates: proxy `‖w − v‖²`
  have hsum_mgf : ProbabilityTheory.HasSubgaussianMGF
      (fun e => ∑ i, Y i e) σ2 (signVec n) := by
    have h := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun hY_indep
      (s := (Finset.univ : Finset (Fin n))) (fun i _ => hY_mgf i)
    simpa [hσ2] using h
  -- the increment is mean-zero
  have hmean : ∫ e, (∑ i, Y i e) ∂(signVec n) = 0 := by
    rw [MeasureTheory.integral_finset_sum _ (fun i _ => hY_int i)]
    simp [hmean_i]
  -- package as `IsSubGaussian`
  have hSG : IsSubGaussian (fun e => ∑ i, Y i e) σ2 (signVec n) := by
    rw [isSubGaussian_iff]
    simpa only [hmean, sub_zero] using hsum_mgf
  have hmeas_sum : AEMeasurable (fun e => ∑ i, Y i e) (signVec n) := by
    refine Measurable.aemeasurable (Finset.measurable_sum _ fun i _ => ?_)
    simp only [hY]; exact (hev i).mul_const (c i)
  have hbridge := subGaussianNorm_le_of_isSubGaussian hmeas_sum hSG hmean
  -- rewrite the goal's increment and conclude
  rw [hfun]
  refine le_trans hbridge (le_of_eq ?_)
  -- `√(6 σ²) = √6 · edist v w`
  rw [NNReal.sqrt_mul, ENNReal.coe_mul]
  congr 1
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [Real.coe_sqrt, EuclideanSpace.dist_eq, hσ2]
  congr 1
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, Real.dist_eq]
  simp only [hc]
  rw [sq_abs]
  ring

/-- A single value is dominated by a finite `⨆ t ∈ T` (honest conditional
`le_ciSup`, avoiding the FROZEN-FALSE `biSup_finset_eq_sup'`): the range of
`fun t => ⨆ (_ : t ∈ T), g t` is bounded above (junk `sSup ∅ = 0` off `T`),
so `le_ciSup_of_le` applies. -/
private lemma le_biSup_mem {E : Type*} {T : Set E} (hfin : T.Finite)
    (g : E → ℝ) {v : E} (hv : v ∈ T) : g v ≤ ⨆ t ∈ T, g t := by
  classical
  have hbdd : BddAbove (Set.range (fun t => ⨆ (_ : t ∈ T), g t)) := by
    obtain ⟨M, hM⟩ := (hfin.image g).bddAbove
    refine ⟨max M 0, ?_⟩
    rintro y ⟨t, rfl⟩
    change (⨆ (_ : t ∈ T), g t) ≤ max M 0
    by_cases ht : t ∈ T
    · rw [ciSup_pos ht]
      exact le_trans (hM (Set.mem_image_of_mem g ht)) (le_max_left _ _)
    · haveI : IsEmpty (t ∈ T) := ⟨ht⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  exact le_ciSup_of_le hbdd v (le_of_eq (ciSup_pos (f := fun _ : v ∈ T => g v) hv).symm)

-- The conditional Dudley glue assembles the whole §8.3.6 pipeline (covering
-- construction, entropy integral, sub-Gaussian bridge) in one term, whose
-- `Finset.sup'`/`⨆` defeq checks over `EuclideanSpace` need a raised limit.
set_option maxHeartbeats 1600000 in
/-- **Conditional Rademacher complexity bound** (HDP §8.3.6, Theorem 8.3.15
conditional step): for a fixed sample `x`, the expected Rademacher supremum
over a finite class of VC dimension `≤ d` is at most `2700·√d/√n`.
Frozen numeral: `40 (dudley_inequality_abs_of_finite) × √6 (B3) × 27 (entropy
integral) = 1080·√6 ≈ 2645.5 ≤ 2700` — DEVIATION from the design's
provisional `500`, recomputed from the batch's frozen constants. Applied
over `T' = empProj x '' F ∪ (−(empProj x '' F))` with the
sample-independent entropy bound `N(T', ε) ≤ (4/ε)^{22d}` from
`coveringNumber_empProj_le`. -/
lemma rademacher_process_expectation_le {n : ℕ} [NeZero n] (x : Fin n → Ω)
    (F : Finset (Set Ω)) (hFne : F.Nonempty)
    -- LEAN-ONLY: measurability of the class members; needed for the
    -- empirical-measure covering bound, no scope change.
    (hFmeas : ∀ S ∈ F, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.6, Theorem 8.3.15.
    (hd : vcDim (↑F : Set (Set Ω)) ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.6 (regime of Theorem 8.3.13).
    (hd1 : 1 ≤ d) :
    ∫ e, F.sup' hFne (fun S =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i)|)
      ∂(signVec n)
      ≤ 2700 * Real.sqrt d / Real.sqrt n := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  -- The Rademacher linear process and the symmetrized empirical projection.
  set Z : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) → ℝ :=
    fun v e => ∑ i, e i * v i with hZ
  set s : ℝ := Real.sqrt (n : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hn0
  have hsn : s⁻¹ * s⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, hs, Real.mul_self_sqrt hn0.le]
  set T : Set (EuclideanSpace ℝ (Fin n)) := empProj x '' (↑F : Set (Set Ω)) ∪ {0} with hT
  have hTfin : T.Finite :=
    (F.finite_toSet.image (empProj x)).union (Set.finite_singleton _)
  have h0T : (0 : EuclideanSpace ℝ (Fin n)) ∈ T := Or.inr rfl
  have hTne : T.Nonempty := ⟨0, h0T⟩
  -- Every point of `T` has norm `≤ 1`, so `diam T ≤ 2`.
  have h_empzero : empProj x (∅ : Set Ω) = 0 := by
    ext i; rw [empProj_apply]; simp
  have hnorm1 : ∀ v ∈ T, dist v (0 : EuclideanSpace ℝ (Fin n)) ≤ 1 := by
    intro v hv
    rw [hT] at hv
    rcases hv with hv | hv
    · obtain ⟨S, _hS, rfl⟩ := hv
      have hsq : dist (empProj x S) (0 : EuclideanSpace ℝ (Fin n)) ^ 2 = empFrac x S := by
        rw [← h_empzero, dist_empProj_sq]; congr 1; simp
      nlinarith [empFrac_le_one x S, empFrac_nonneg x S,
        dist_nonneg (x := empProj x S) (y := (0 : EuclideanSpace ℝ (Fin n)))]
    · rw [Set.mem_singleton_iff] at hv; subst hv; simp
  have hdiam2 : Metric.diam T ≤ 2 := by
    refine Metric.diam_le_of_forall_dist_le (by norm_num) (fun p hp q hq => ?_)
    calc dist p q ≤ dist p 0 + dist 0 q := dist_triangle p 0 q
      _ = dist p 0 + dist q 0 := by rw [dist_comm 0 q]
      _ ≤ 1 + 1 := add_le_add (hnorm1 p hp) (hnorm1 q hq)
      _ = 2 := by norm_num
  -- Sub-Gaussian increments, measurability of the process.
  have hinc : SubGaussianIncrements Z (NNReal.sqrt 6) T (signVec n) := by
    rw [hZ]; exact subGaussianIncrements_inner_signVec T
  have hmeas : ∀ t ∈ T, AEMeasurable (Z t) (signVec n) := by
    intro t _
    simp only [hZ]
    exact (Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).mul_const _)).aemeasurable
  have hK6 : ((NNReal.sqrt 6 : ℝ≥0) : ℝ) = Real.sqrt 6 := by rw [Real.coe_sqrt]; norm_num
  -- Dudley's inequality on the projected class.
  have hdud : (∫ e, ⨆ t ∈ T, |Z t e - Z 0 e| ∂(signVec n))
      ≤ 40 * Real.sqrt 6 * dudleyIntegral T 2 := by
    have h := dudley_inequality_abs_of_finite hTfin hTne hmeas hinc h0T hdiam2 (by norm_num)
    rwa [hK6] at h
  -- The entropy integral is `≤ 27√d` (sample-independent covering bound).
  have hint27 : dudleyIntegral T 2 ≤ 27 * Real.sqrt d := by
    have hcov_bound : ∀ ε ∈ Set.Ioc (0 : ℝ) 2,
        sqrtLogCov T ε ≤ Real.sqrt (22 * (d : ℝ) * Real.log (4 / ε)) := by
      intro ε hε
      obtain ⟨hε0, hε2⟩ := hε
      have h4e : (1 : ℝ) ≤ 4 / ε := by rw [le_div_iff₀ hε0]; linarith
      have hb1 : (1 : ℝ) ≤ (4 / ε) ^ (22 * d) := one_le_pow₀ h4e
      have htop : coveringNumber T ε ≠ ⊤ :=
        ne_top_of_le_ne_top hTfin.encard_lt_top.ne (Metric.coveringNumber_le_encard_self T)
      have hcount : ((coveringNumber T ε).toNat : ℝ) ≤ (4 / ε) ^ (22 * d) := by
        rcases lt_or_ge ε 1 with hε1lt | hεge1
        · -- `ε < 1`: image net (Theorem 8.3.13) plus the anchor `0`.
          have htop_img : coveringNumber (empProj x '' (↑F : Set (Set Ω))) ε ≠ ⊤ :=
            ne_top_of_le_ne_top (F.finite_toSet.image (empProj x)).encard_lt_top.ne
              (Metric.coveringNumber_le_encard_self _)
          obtain ⟨Cc, hCsub, _hCfin, hCcov, hCenc⟩ :=
            Metric.exists_set_encard_eq_coveringNumber htop_img
          have hcover_union : Metric.IsCover (Real.toNNReal ε) T (Cc ∪ {0}) := by
            rw [hT]
            exact SetRel.IsCover.union hCcov
              ((isEpsilonNet_self ({0} : Set (EuclideanSpace ℝ (Fin n))) hε0.le).isCover hε0.le)
          have hsubU : Cc ∪ {0} ⊆ T := by
            rw [hT]; exact Set.union_subset_union hCsub subset_rfl
          have hle1 : coveringNumber T ε ≤ (Cc ∪ {0}).encard :=
            hcover_union.coveringNumber_le_encard hsubU
          have hle2 : (Cc ∪ {0}).encard ≤ (⌊(2 / ε) ^ (21 * d)⌋₊ : ℕ∞) + 1 := by
            calc (Cc ∪ {0}).encard
                ≤ Cc.encard + ({0} : Set (EuclideanSpace ℝ (Fin n))).encard :=
                  Set.encard_union_le _ _
              _ = Cc.encard + 1 := by rw [Set.encard_singleton]
              _ ≤ (⌊(2 / ε) ^ (21 * d)⌋₊ : ℕ∞) + 1 := by
                  gcongr
                  rw [hCenc]
                  exact coveringNumber_empProj_le x hFmeas hd hd1 hε0 hε1lt
          have hcovU : coveringNumber T ε ≤ (⌊(2 / ε) ^ (21 * d)⌋₊ : ℕ∞) + 1 :=
            le_trans hle1 hle2
          have hcovU' : coveringNumber T ε ≤ ((⌊(2 / ε) ^ (21 * d)⌋₊ + 1 : ℕ) : ℕ∞) := by
            rw [Nat.cast_add, Nat.cast_one]; exact hcovU
          have htoNat : (coveringNumber T ε).toNat ≤ ⌊(2 / ε) ^ (21 * d)⌋₊ + 1 := by
            have h := ENat.toNat_le_toNat hcovU' (ENat.coe_ne_top _)
            rwa [ENat.toNat_coe] at h
          have hreal : ((coveringNumber T ε).toNat : ℝ) ≤ (2 / ε) ^ (21 * d) + 1 := by
            calc ((coveringNumber T ε).toNat : ℝ)
                ≤ ((⌊(2 / ε) ^ (21 * d)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast htoNat
              _ = (⌊(2 / ε) ^ (21 * d)⌋₊ : ℝ) + 1 := by push_cast; ring
              _ ≤ (2 / ε) ^ (21 * d) + 1 := by
                  have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (2 / ε) ^ (21 * d))
                  linarith
          refine le_trans hreal ?_
          -- `(2/ε)^{21d} + 1 ≤ (4/ε)^{22d}`.
          have hbase2 : (2 : ℝ) ≤ 2 / ε := by rw [le_div_iff₀ hε0]; nlinarith [hε1lt]
          have hone_le : (1 : ℝ) ≤ 2 / ε := le_trans one_le_two hbase2
          have hA1 : (1 : ℝ) ≤ (2 / ε) ^ (21 * d) := one_le_pow₀ hone_le
          have hd1' : 1 ≤ 21 * d := by omega
          have h4eq : (4 : ℝ) / ε = 2 * (2 / ε) := by field_simp; ring
          have step1 : (2 * (2 / ε)) ^ (21 * d) ≤ (2 * (2 / ε)) ^ (22 * d) := by
            apply pow_le_pow_right₀ (by nlinarith [hbase2]) (by omega)
          have step3 : (2 : ℝ) ≤ 2 ^ (21 * d) := by
            calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ (21 * d) := pow_le_pow_right₀ one_le_two hd1'
          have step4 : (2 : ℝ) * (2 / ε) ^ (21 * d) ≤ 2 ^ (21 * d) * (2 / ε) ^ (21 * d) :=
            mul_le_mul_of_nonneg_right step3 (by positivity)
          calc (2 / ε) ^ (21 * d) + 1
              ≤ (2 / ε) ^ (21 * d) + (2 / ε) ^ (21 * d) := by linarith [hA1]
            _ = 2 * (2 / ε) ^ (21 * d) := by ring
            _ ≤ 2 ^ (21 * d) * (2 / ε) ^ (21 * d) := step4
            _ = (2 * (2 / ε)) ^ (21 * d) := (mul_pow 2 (2 / ε) (21 * d)).symm
            _ ≤ (2 * (2 / ε)) ^ (22 * d) := step1
            _ = (4 / ε) ^ (22 * d) := by rw [← h4eq]
        · -- `ε ≥ 1`: the single ball centred at `0` covers `T`.
          have hnet : IsEpsilonNet ({0} : Set (EuclideanSpace ℝ (Fin n))) T ε := by
            refine ⟨fun y hy => ?_, fun v hv => ⟨0, rfl, ?_⟩⟩
            · rw [Set.mem_singleton_iff] at hy; subst hy; exact h0T
            · exact le_trans (hnorm1 v hv) hεge1
          have hcov1 : coveringNumber T ε ≤ 1 := by
            have hc := (hnet.isCover hε0.le).coveringNumber_le_encard
              (by intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact h0T)
            rwa [Set.encard_singleton] at hc
          calc ((coveringNumber T ε).toNat : ℝ)
              ≤ ((1 : ℕ∞).toNat : ℝ) := by exact_mod_cast ENat.toNat_le_toNat hcov1 (by simp)
            _ = 1 := by simp
            _ ≤ (4 / ε) ^ (22 * d) := hb1
      have hle := sqrtLogCov_le_sqrt_log_of_le hTne htop hcount hb1
      have hlogpow : Real.log ((4 / ε) ^ (22 * d)) = 22 * (d : ℝ) * Real.log (4 / ε) := by
        rw [Real.log_pow]; push_cast; ring
      rwa [hlogpow] at hle
    have hRHSint : MeasureTheory.IntegrableOn
        (fun ε => Real.sqrt (22 * (d : ℝ) * Real.log (4 / ε))) (Set.Ioc (0 : ℝ) 2)
        MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
        (intervalIntegrable_sqrt_log_mul (by positivity : (0 : ℝ) ≤ 22 * (d : ℝ)))
    calc dudleyIntegral T 2
        = ∫ ε in Set.Ioc (0 : ℝ) 2, sqrtLogCov T ε := rfl
      _ ≤ ∫ ε in Set.Ioc (0 : ℝ) 2, Real.sqrt (22 * (d : ℝ) * Real.log (4 / ε)) :=
          setIntegral_mono_on (integrableOn_sqrtLogCov_Ioc hTfin) hRHSint measurableSet_Ioc
            hcov_bound
      _ = ∫ ε in (0 : ℝ)..2, Real.sqrt (22 * (d : ℝ) * Real.log (4 / ε)) :=
          (intervalIntegral.integral_of_le (by norm_num)).symm
      _ ≤ 27 * Real.sqrt d := entropyIntegral_le hd1
  -- The LHS integrand is dominated by `s⁻¹` times the Dudley integrand.
  set fI : (Fin n → ℝ) → ℝ := fun e => F.sup' hFne (fun S =>
      |(n : ℝ)⁻¹ * ∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i)|) with hfI
  have hpt : ∀ e, fI e ≤ s⁻¹ * ⨆ t ∈ T, |Z t e - Z 0 e| := by
    intro e
    rw [hfI]
    refine Finset.sup'_le hFne _ (fun S hS => ?_)
    have hZ0 : Z (0 : EuclideanSpace ℝ (Fin n)) e = 0 := by simp only [hZ]; simp
    have hZeq : Z (empProj x S) e
        = s⁻¹ * ∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i) := by
      simp only [hZ]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [empProj_apply, ← hs]; ring
    have hvT : empProj x S ∈ T := by
      rw [hT]; exact Or.inl (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hS))
    have hbnd : |Z (empProj x S) e - Z 0 e| ≤ ⨆ t ∈ T, |Z t e - Z 0 e| :=
      le_biSup_mem hTfin (fun t => |Z t e - Z 0 e|) hvT
    calc |(n : ℝ)⁻¹ * ∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i)|
        = (n : ℝ)⁻¹ * |∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i)| := by
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hn0.le)]
      _ = s⁻¹ * |Z (empProj x S) e| := by
          rw [hZeq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hs0.le), ← mul_assoc, hsn]
      _ = s⁻¹ * |Z (empProj x S) e - Z 0 e| := by rw [hZ0, sub_zero]
      _ ≤ s⁻¹ * ⨆ t ∈ T, |Z t e - Z 0 e| :=
          mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr hs0.le)
  have hg_bisup_int : Integrable (fun e => ⨆ t ∈ T, |Z t e - Z 0 e|) (signVec n) :=
    integrable_biSup_sub hTfin hTne hmeas hinc h0T
  have hsg_int : Integrable (fun e => s⁻¹ * ⨆ t ∈ T, |Z t e - Z 0 e|) (signVec n) :=
    hg_bisup_int.const_mul s⁻¹
  have hf_nonneg : ∀ e, 0 ≤ fI e := by
    intro e
    obtain ⟨S, hS⟩ := id hFne
    have h0 : (0 : ℝ) ≤ F.sup' hFne (fun S =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i)|) :=
      le_trans (abs_nonneg _) (Finset.le_sup' (fun S =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i)|) hS)
    exact h0
  have hf_meas : Measurable fI := by
    have hgeq : fI = F.sup' hFne (fun S => fun e : Fin n → ℝ =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i)|) := by
      rw [hfI]; funext e; rw [Finset.sup'_apply]
    rw [hgeq]
    refine Finset.measurable_sup' hFne fun S hS => ?_
    refine Measurable.abs (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _
  have hf_int : Integrable fI (signVec n) := by
    refine Integrable.mono' hsg_int hf_meas.aestronglyMeasurable (ae_of_all _ (fun e => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg e)]
    exact hpt e
  -- Assemble the numeral: `40·√6·27 = 1080·√6 ≤ 2700`.
  have hsqrt6 : Real.sqrt 6 ≤ 5 / 2 := by
    have h : (5 / 2 : ℝ) = Real.sqrt ((5 / 2) ^ 2) := by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 2)]
    rw [h]; exact Real.sqrt_le_sqrt (by norm_num)
  have hnumeral : 40 * Real.sqrt 6 * (27 * Real.sqrt d) ≤ 2700 * Real.sqrt d := by
    have hrw : 40 * Real.sqrt 6 * (27 * Real.sqrt d) = 1080 * Real.sqrt 6 * Real.sqrt d := by ring
    rw [hrw]
    calc 1080 * Real.sqrt 6 * Real.sqrt d
        ≤ 1080 * (5 / 2) * Real.sqrt d := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg d)
          exact mul_le_mul_of_nonneg_left hsqrt6 (by norm_num)
      _ = 2700 * Real.sqrt d := by ring
  have hfinal : s⁻¹ * (40 * Real.sqrt 6 * (27 * Real.sqrt d)) ≤ 2700 * Real.sqrt d / s := by
    calc s⁻¹ * (40 * Real.sqrt 6 * (27 * Real.sqrt d))
        ≤ s⁻¹ * (2700 * Real.sqrt d) :=
          mul_le_mul_of_nonneg_left hnumeral (inv_nonneg.mpr hs0.le)
      _ = 2700 * Real.sqrt d / s := by rw [div_eq_mul_inv]; ring
  calc ∫ e, fI e ∂(signVec n)
      ≤ ∫ e, s⁻¹ * ⨆ t ∈ T, |Z t e - Z 0 e| ∂(signVec n) :=
        integral_mono hf_int hsg_int hpt
    _ = s⁻¹ * ∫ e, ⨆ t ∈ T, |Z t e - Z 0 e| ∂(signVec n) := integral_const_mul _ _
    _ ≤ s⁻¹ * (40 * Real.sqrt 6 * dudleyIntegral T 2) :=
        mul_le_mul_of_nonneg_left hdud (inv_nonneg.mpr hs0.le)
    _ ≤ s⁻¹ * (40 * Real.sqrt 6 * (27 * Real.sqrt d)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs0.le)
        exact mul_le_mul_of_nonneg_left hint27 (by positivity)
    _ ≤ 2700 * Real.sqrt d / s := hfinal

/-- **Symmetrization adapter** (HDP §8.3.6 via Exercise 8.11): the expected
uniform deviation is at most twice the expected Rademacher supremum, jointly
over sample and signs. Cites the symmetrization cluster's
`empirical_symmetrization` instantiated at `ι := ↥F` (indicators, bounded
by 1), `Fin n` by precomposition, and `integral_indicator_one_real`; this
adapter isolates any statement-shape mismatch. -/
lemma symmetrization_adapter {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity, no scope
    -- change.
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent; HDP §8.3.6,
    -- Theorem 8.3.15.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP §8.3.6 (map form;
    -- `ProbabilityTheory.HasLaw` not used per batch interface).
    (hlaw : ∀ i, P.map (X i) = μ)
    (F : Finset (Set Ω)) (hFne : F.Nonempty)
    -- LEAN-ONLY: measurability of the class members; Exercise 8.11 input.
    (hFmeas : ∀ S ∈ F, MeasurableSet S)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.6 (implicit).
    (hn : 1 ≤ n) :
    ∫ ξ, F.sup' hFne (fun S =>
        |empFrac (fun i : Fin n => X i ξ) S - μ.real S|) ∂P
      ≤ 2 * ∫ p, F.sup' hFne (fun S =>
          |(n : ℝ)⁻¹ * ∑ i : Fin n,
            p.2 i * S.indicator (fun _ => (1 : ℝ)) (X i p.1)|)
        ∂(P.prod (signVec n)) := by
  haveI : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  haveI : Nonempty {S // S ∈ F} := ⟨⟨hFne.choose, hFne.choose_spec⟩⟩
  have key := empirical_symmetrization (α := Ω) (ι := {S // S ∈ F})
      (μ := P) (P := μ) (n := n)
      (X := fun (i : Fin n) (ξ : Ξ) => X i ξ)
      (F := fun k : {S // S ∈ F} => (↑k : Set Ω).indicator (fun _ => (1 : ℝ)))
      (hX_meas := fun i => hXmeas i)
      (hX_indep := hindep.precomp Fin.val_injective)
      (hX_law := fun i => hlaw i)
      (hF_meas := fun k => measurable_const.indicator (hFmeas k.1 k.2))
      (hF_bdd := fun k x => by
        classical
        have hb : |(↑k : Set Ω).indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
          rw [Set.indicator_apply]; split_ifs <;> norm_num
        exact hb)
  -- convert the LHS: `Finset.sup'` → `⨆`, `empFrac` unfolds, `∫ 𝟙 = μ.real`
  have hL : (∫ ξ, F.sup' hFne (fun S =>
        |empFrac (fun i : Fin n => X i ξ) S - μ.real S|) ∂P)
      = ∫ ξ, ⨆ k : {S // S ∈ F},
          |(n : ℝ)⁻¹ * (∑ i : Fin n, (↑k : Set Ω).indicator (fun _ => (1 : ℝ)) (X i ξ))
            - ∫ x, (↑k : Set Ω).indicator (fun _ => (1 : ℝ)) x ∂μ| ∂P := by
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    dsimp only
    rw [finset_sup'_eq_iSup_subtype]
    refine iSup_congr fun k => ?_
    rw [integral_indicator_one_real (hFmeas k.1 k.2)]
    rfl
  -- convert the RHS: `Finset.sup'` → `⨆`
  have hR : (∫ p, F.sup' hFne (fun S =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n,
          p.2 i * S.indicator (fun _ => (1 : ℝ)) (X i p.1)|)
        ∂(P.prod (signVec n)))
      = ∫ p, ⨆ k : {S // S ∈ F},
          |(n : ℝ)⁻¹ * ∑ i : Fin n,
            p.2 i * (↑k : Set Ω).indicator (fun _ => (1 : ℝ)) (X i p.1)|
        ∂(P.prod (signVec n)) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    dsimp only
    exact finset_sup'_eq_iSup_subtype hFne _
  rw [hL, hR]
  exact key

/-- Absolute value of a `Finset.sup'` of nonnegative, `≤ 1`-bounded reals is
`≤ 1` (LEAN-ONLY: isolates the finite-sup bound of the joint Rademacher
integrand, keeping the bounded function abstract to avoid heavy defeq). -/
private lemma abs_finset_sup'_le {α : Type*} {F : Finset α} (hFne : F.Nonempty)
    (h : α → ℝ) (h1 : ∀ a ∈ F, h a ≤ 1) (h0 : ∀ a ∈ F, 0 ≤ h a) :
    ‖F.sup' hFne h‖ ≤ 1 := by
  have hnn : 0 ≤ F.sup' hFne h := by
    obtain ⟨a, ha⟩ := hFne
    exact le_trans (h0 a ha) (Finset.le_sup' h ha)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact Finset.sup'_le hFne h h1

/-- **VC law of large numbers, finite core** (HDP §8.3.6, Theorem 8.3.15):
`E max_{S ∈ F} |μ_n(S) − μ(S)| ≤ 5400·√d/√n` for a finite class of VC
dimension `≤ d`. Frozen numeral: `2 (symmetrization) × 40
(dudley_inequality_abs_of_finite) × √6 (B3) × 27 (entropy integral) = 2160·√6
≈ 5290.9 ≤ 5400` — DEVIATION from the design's provisional `1000`,
recomputed from the batch's frozen constants. Proof: symmetrize
(`symmetrization_adapter`) → Fubini → conditional Dudley with
sample-independent RHS (`rademacher_process_expectation_le`). -/
theorem vc_lln_finset {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity, no scope
    -- change.
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent; HDP §8.3.6,
    -- Theorem 8.3.15.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP §8.3.6 (map form).
    (hlaw : ∀ i, P.map (X i) = μ)
    (F : Finset (Set Ω)) (hFne : F.Nonempty)
    -- LEAN-ONLY: measurability of the class members (implicit in the book's
    -- Boolean functions on a probability space).
    (hFmeas : ∀ S ∈ F, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.6, Theorem 8.3.15.
    (hd : vcDim (↑F : Set (Set Ω)) ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.6.
    (hd1 : 1 ≤ d)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.6 (implicit).
    (hn : 1 ≤ n) :
    ∫ ξ, F.sup' hFne (fun S =>
        |empFrac (fun i : Fin n => X i ξ) S - μ.real S|) ∂P
      ≤ 5400 * Real.sqrt d / Real.sqrt n := by
  haveI : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  refine (symmetrization_adapter hXmeas hindep hlaw F hFne hFmeas hn).trans ?_
  set g : Ξ × (Fin n → ℝ) → ℝ := fun p => F.sup' hFne (fun S =>
      |(n : ℝ)⁻¹ * ∑ i : Fin n,
        p.2 i * S.indicator (fun _ => (1 : ℝ)) (X i p.1)|) with hg_def
  rw [show (5400 : ℝ) * Real.sqrt d / Real.sqrt n
        = 2 * (2700 * Real.sqrt d / Real.sqrt n) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  -- measurability of the joint integrand
  have hg_meas : Measurable g := by
    have hgeq : g = F.sup' hFne (fun S => fun p : Ξ × (Fin n → ℝ) =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n,
          p.2 i * S.indicator (fun _ => (1 : ℝ)) (X i p.1)|) := by
      funext p; rw [Finset.sup'_apply]
    rw [hgeq]
    refine Finset.measurable_sup' hFne fun S hS => ?_
    refine Measurable.abs (Measurable.const_mul ?_ _)
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((measurable_pi_apply i).comp measurable_snd).mul
      ((measurable_const.indicator (hFmeas S hS)).comp ((hXmeas i).comp measurable_fst))
  -- a.e. bound: the joint integrand is `≤ 1`
  have hae : ∀ᵐ p ∂(P.prod (signVec n)),
      ∀ i, p.2 i = 1 ∨ p.2 i = -1 := by
    rw [ae_iff]
    have hset : {p : Ξ × (Fin n → ℝ) | ¬ ∀ i, p.2 i = 1 ∨ p.2 i = -1}
        = Set.univ ×ˢ {s | ¬ ∀ i, s i = 1 ∨ s i = -1} := by
      ext p; simp
    rw [hset, Measure.prod_prod, ae_iff.mp (signVec_ae_pm n), mul_zero]
  have hbnd : ∀ᵐ p ∂(P.prod (signVec n)), ‖g p‖ ≤ 1 := by
    filter_upwards [hae] with p hp
    classical
    rw [hg_def]
    refine abs_finset_sup'_le hFne _ (fun S _ => ?_) (fun S _ => abs_nonneg _)
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    rw [abs_mul, abs_inv, abs_of_nonneg hn'.le, inv_mul_le_iff₀ hn', mul_one]
    calc |∑ i : Fin n, p.2 i * S.indicator (fun _ => (1 : ℝ)) (X i p.1)|
        ≤ ∑ i : Fin n, |p.2 i * S.indicator (fun _ => (1 : ℝ)) (X i p.1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have h1 : |p.2 i| = 1 := by rcases hp i with h | h <;> simp [h]
          have h2 : |S.indicator (fun _ => (1 : ℝ)) (X i p.1)| ≤ 1 := by
            rw [Set.indicator_apply]; split_ifs <;> norm_num
          rw [h1, one_mul]; exact h2
      _ = (n : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_one]
  have hg_int : Integrable g (P.prod (signVec n)) :=
    Integrable.of_bound hg_meas.aestronglyMeasurable 1 hbnd
  rw [integral_prod g hg_int]
  -- conditional Dudley bound, fibrewise
  have hbound : ∀ ξ, (∫ e, g (ξ, e) ∂(signVec n))
      ≤ 2700 * Real.sqrt d / Real.sqrt n := by
    intro ξ
    simp only [hg_def]
    exact rademacher_process_expectation_le (fun i => X i ξ) F hFne hFmeas hd hd1
  calc ∫ ξ, (∫ e, g (ξ, e) ∂(signVec n)) ∂P
      ≤ ∫ _ξ, (2700 * Real.sqrt d / Real.sqrt n) ∂P :=
        integral_mono hg_int.integral_prod_left (integrable_const _) hbound
    _ = 2700 * Real.sqrt d / Real.sqrt n := by rw [integral_const]; simp

end StatLean.ConcentrationInequalities
