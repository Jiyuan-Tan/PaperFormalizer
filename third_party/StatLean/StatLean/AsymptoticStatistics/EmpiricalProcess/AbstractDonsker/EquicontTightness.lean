module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.NecessityTightness
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterTightness

@[expose] public section

/-!
# Theorem 18.12 empirical-tightness — the coordinate-bound half

The gate-independent half of the van der Vaart, *Asymptotic Statistics* §18.12
empirical-tightness lemma: for any FINITE subset `S ⊆ ↥F` of the index and any
`ε > 0`, there is a uniform threshold `M` controlling the outer probability that
the empirical process `𝔾ₙ` exceeds `M` somewhere on `S`, in the `limsupₙ` sense.

This is the marginal (finite-net) tightness that every tightness scenario needs:
each single coordinate `f ∈ S` is uniformly tight because the empirical process
`𝔾ₙ f` converges in distribution to a (tight, finite-variance) Gaussian
(`IsMarginalCLT`), and a finite union is controlled by the union bound. The
oscillation / asymptotic-equicontinuity half (which depends on the chosen
discretization gate) lives elsewhere.

## Main results

* `marginal_coord_tight` — single-coordinate uniform tightness: for each
  `f ∈ ↥F` and `δ > 0`, there is `M` with
  `limsupₙ μ {ξ | M < |𝔾ₙ f|} ≤ ofReal δ`.
* `marginal_sup_bound_of_clt` — the finite-net sup bound: union over `S`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §18.12
(book p.260), Theorem 18.14(a) marginal CLT.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology AsymptoticStatistics ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

section Discretization

variable {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
variable {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
  (hF_meas : ∀ f ∈ F, Measurable f)
  (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)

/-- **Two-term `limsup` subadditivity on `ℝ≥0∞`/`atTop`.** `limsup (u + v) ≤
limsup u + limsup v`. The generic `ENNReal.limsup_add_le` needs
`CountableInterFilter`, which `atTop` lacks; this is the `limsup_le_iff`-pattern
specialization (cf. `limsup_add_tendsto_zero_le` in `NecessityTightness.lean`). -/
theorem limsup_add_le_atTop (u v : ℕ → ℝ≥0∞) :
    limsup (fun n => u n + v n) atTop ≤ limsup u atTop + limsup v atTop := by
  -- If either limsup is `⊤`, the bound is trivial.
  rcases eq_or_ne (limsup u atTop) ⊤ with hu | hu
  · rw [hu]; exact le_top
  rcases eq_or_ne (limsup v atTop) ⊤ with hv | hv
  · rw [hv, add_top]; exact le_top
  -- Both finite: the `limsup_le_iff` `b`-characterization.
  rw [limsup_le_iff isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)]
  intro b hb
  -- `limsup u < b − limsup v` (equivalent to `limsup u + limsup v < b`, both finite).
  have hub : limsup u atTop < b - limsup v atTop := by
    rw [lt_tsub_iff_right]; exact hb
  -- Pick `c` strictly between `limsup u` and `b − limsup v`.
  obtain ⟨c, huc, hcb⟩ := exists_between hub
  -- Then `limsup v < b − c`, so eventually `v n < b − c`.
  have hvbc : limsup v atTop < b - c := by
    rw [lt_tsub_iff_left]
    calc c + limsup v atTop < (b - limsup v atTop) + limsup v atTop :=
          (ENNReal.add_lt_add_iff_right hv).2 hcb
      _ = b := by rw [tsub_add_cancel_of_le (le_of_lt (lt_of_le_of_lt le_add_self hb))]
  have hUev : ∀ᶠ n in atTop, u n < c := eventually_lt_of_limsup_lt huc
  have hVev : ∀ᶠ n in atTop, v n < b - c := eventually_lt_of_limsup_lt hvbc
  have hcb' : c ≤ b := le_of_lt (lt_of_lt_of_le hcb tsub_le_self)
  filter_upwards [hUev, hVev] with n hUn hVn
  calc u n + v n < c + (b - c) := ENNReal.add_lt_add hUn hVn
    _ = b := add_tsub_cancel_of_le hcb'

/-- **`limsup` of a finite `ENNReal`-sum is bounded by the sum of `limsup`s.**
Finite-`Finset` iteration of `limsup_add_le_atTop`, used for the union bound in
`marginal_sup_bound_of_clt`. -/
theorem limsup_finset_sum_le {ι : Type*} (I : Finset ι) (u : ι → ℕ → ℝ≥0∞) :
    limsup (fun n => ∑ i ∈ I, u i n) atTop ≤ ∑ i ∈ I, limsup (u i) atTop := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | insert a I ha ih =>
    have hfun : (fun n => ∑ i ∈ insert a I, u i n)
        = (fun n => u a n + ∑ i ∈ I, u i n) := by
      funext n; rw [Finset.sum_insert ha]
    rw [hfun, Finset.sum_insert ha]
    refine le_trans (limsup_add_le_atTop (u a) (fun n => ∑ i ∈ I, u i n)) ?_
    gcongr

omit [MeasurableSpace Ω] in
/-- **Coordinate-0 of `tupleVec ![g]` is `g`.** The `0`-th coordinate of the
`EuclideanSpace ℝ (Fin 1)` packaging of the singleton tuple `![g]` at `ω` is
`g ω`. -/
theorem proj_tupleVec_singleton (g : Ω → ℝ) (ω : Ω) :
    EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) (tupleVec ![g] ω) = g ω := by
  rfl

/-- **Coordinate-0 reconciliation: the standardised `k = 1` CLT vector is the
empirical process.** For a measurable `g : Ω → ℝ` with `MemLp g 2 P` and an iid
sample `X` with law `P`, the `0`-th coordinate of the `IsMarginalCLT`-standardised
vector at the singleton tuple `![g]`,
`(√n)⁻¹ • (∑_{i<n} tupleVec ![g] (Xᵢξ) − n • E[tupleVec ![g] (X₀)])`, equals the
empirical process `empiricalProcess P n (X·ξ) g = √n·(Pₙ − P)g`.

Both sides distribute the continuous-linear coordinate map `EuclideanSpace.proj 0`
through the `•`, the `∑`, and the Bochner expectation
(`ContinuousLinearMap.integral_comp_comm`), reducing to the scalar identity
`(√n)⁻¹·(∑ g(Xᵢξ) − n·∫g dP) = √n·(n⁻¹∑ g(Xᵢξ) − ∫g dP)`. This is the
`Fin 1` packaging bridge between the multivariate-CLT encoding and the scalar
empirical process. -/
theorem proj_std_eq_empiricalProcess {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i)) (hX_law : μ.map (X 0) = P)
    (g : Ω → ℝ) (hg_meas : Measurable g) (hg : MemLp g 2 P) (n : ℕ) (ξ : Ξ) :
    EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)
        ((Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec ![g] (X i ξ)
          - n • μ[fun ξ => tupleVec ![g] (X 0 ξ)]))
      = empiricalProcess P n (fun i : Fin n => X i.val ξ) g := by
  classical
  have hg_int : Integrable g P := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- `g (X 0 ·)` is integrable under `μ` (pullback of L¹ `g` along the law map),
  -- and `∫ g(X 0 ·) dμ = ∫ g dP`.
  have hm : AEStronglyMeasurable g (μ.map (X 0)) := by
    rw [hX_law]; exact hg_int.aestronglyMeasurable
  have hgX_int : Integrable (fun ξ => g (X 0 ξ)) μ :=
    (integrable_map_measure hm (hX_meas 0).aemeasurable).mp (by rw [hX_law]; exact hg_int)
  have hint_eq : ∫ ξ, g (X 0 ξ) ∂μ = ∫ x, g x ∂P := by
    rw [← hX_law, integral_map (hX_meas 0).aemeasurable hm]
  -- `tupleVec ![g] (X 0 ·)` is integrable: its single coordinate is `g(X 0 ·)`,
  -- and the 1-dim Euclidean norm is `|g(X 0 ·)|`.
  have htv_meas : Measurable (tupleVec ![g]) := by
    have hpi : Measurable (fun ω => (fun i => (![g] : Fin 1 → (Ω → ℝ)) i ω) : Ω → (Fin 1 → ℝ)) :=
      measurable_pi_iff.mpr (fun i => by fin_cases i; exact hg_meas)
    exact (EuclideanSpace.equiv (Fin 1) ℝ).symm.continuous.measurable.comp hpi
  have htup_meas : Measurable (fun ξ => tupleVec ![g] (X 0 ξ)) := htv_meas.comp (hX_meas 0)
  -- `‖tupleVec ![g] (X 0 ξ)‖ = |g (X 0 ξ)|`.
  have hnorm : (fun ξ => ‖tupleVec ![g] (X 0 ξ)‖) = (fun ξ => |g (X 0 ξ)|) := by
    funext ξ
    rw [EuclideanSpace.norm_eq]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
    rw [show (tupleVec ![g] (X 0 ξ)) 0 = g (X 0 ξ) from rfl]
  have htup_int : Integrable (fun ξ => tupleVec ![g] (X 0 ξ)) μ := by
    refine ⟨htup_meas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have henorm : ∀ ξ, ‖tupleVec ![g] (X 0 ξ)‖ₑ = ‖g (X 0 ξ)‖ₑ := by
      intro ξ
      rw [← enorm_norm, congrFun hnorm ξ]
      simp [Real.enorm_eq_ofReal_abs, abs_abs]
    calc ∫⁻ ξ, ‖tupleVec ![g] (X 0 ξ)‖ₑ ∂μ
        = ∫⁻ ξ, ‖g (X 0 ξ)‖ₑ ∂μ := lintegral_congr fun ξ => henorm ξ
      _ < ⊤ := hgX_int.hasFiniteIntegral
  set L := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) with hL
  -- Distribute `L` (a CLM: linear, continuous) through `•`, `-`, `∑`, and `∫`.
  rw [hL, map_smul, map_sub, map_sum, map_nsmul]
  -- The summed coordinates are `g (X i ξ)`; the expectation coordinate is `∫ g dP`.
  have hsum : ∀ i, L (tupleVec ![g] (X i ξ)) = g (X i ξ) := fun i =>
    proj_tupleVec_singleton g (X i ξ)
  have hexp : L (μ[fun ξ => tupleVec ![g] (X 0 ξ)]) = ∫ x, g x ∂P := by
    rw [hL, ← ContinuousLinearMap.integral_comp_comm _ htup_int]
    simp only [proj_tupleVec_singleton]
    exact hint_eq
  rw [hL] at hsum hexp
  simp only [hsum, hexp]
  -- Scalar identity: `(√n)⁻¹·(∑ g(Xᵢξ) − n·∫g(X₀) dμ) = √n·(n⁻¹∑ g(Xᵢξ) − ∫g dP)`.
  unfold empiricalProcess empiricalAvg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hsqrt_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
    have hsum_eq : ∑ i ∈ Finset.range n, g (X i ξ)
        = ∑ i : Fin n, g (X i.val ξ) := by
      rw [Finset.sum_range fun i => g (X i ξ)]
    have hsqrt_ne : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)
    rw [smul_eq_mul, hsum_eq, nsmul_eq_mul]
    field_simp
    rw [hsqrt_sq]

set_option maxHeartbeats 1000000 in
-- reason: the closed-set outer-portmanteau step unfolds the `ProbabilityMeasure ℝ`
-- subtype coes against the continuous-mapping CLT term, which is `whnf`-heavy.
include hF_meas in
/-- **Single-coordinate uniform tightness.** For each `f : ↥F` and `δ > 0` there
is a threshold `M` such that the `limsupₙ` of the `μ`-probability that the
empirical process `𝔾ₙ f = empiricalProcess P n (X· ξ) f` exceeds `M` in absolute
value is at most `ofReal δ`.

The empirical process `𝔾ₙ f` converges in distribution to the Gaussian
`multivariateGaussian 0 (marginalCovMatrix P ![f])` (the `k = 1` case of the
marginal CLT clause `IsMarginalCLT.fdd`); convergence in distribution to a tight
finite-variance limit gives uniform tightness of the tails via the closed-set
portmanteau inequality (`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`)
plus continuity-from-above of the Gaussian tail (decreasing closed balls to `∅`).

vdV §18.12 (book p.260): the finite-dimensional marginals of the empirical
process are uniformly tight. -/
theorem marginal_coord_tight (h_clt : IsMarginalCLT F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f : ↥F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, limsup (fun n => μ
        {ξ | M < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|}) atTop
      ≤ ENNReal.ofReal δ := by
  classical
  have hf_meas : Measurable (f : Ω → ℝ) := hF_meas f.1 f.2
  have hf_memLp : MemLp (f : Ω → ℝ) 2 P := h_clt.1 f.1 f.2
  -- The `k = 1` marginal CLT for the singleton tuple `![f]`.
  obtain ⟨Y, hY_law, hY_tend⟩ := h_clt.2 μ X hX_meas hX_indep hX_id hX_law
    (k := 1) ![(f : Ω → ℝ)] (fun i => by fin_cases i; exact f.2)
  -- The standardised `k = 1` empirical vector (folded as `stdSeq` to keep later
  -- `ProbabilityMeasure`-coe unification cheap).
  set stdSeq : ℕ → Ξ → EuclideanSpace ℝ (Fin 1) := fun n ξ =>
    (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec ![(f : Ω → ℝ)] (X i ξ)
      - n • μ[fun ξ => tupleVec ![(f : Ω → ℝ)] (X 0 ξ)]) with hstdSeq
  -- The coordinate-0 continuous-linear readout `proj0 : EuclideanSpace ℝ (Fin 1) → ℝ`.
  set L := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) with hL
  -- Push the `k = 1` CLT through `proj0` (continuous mapping theorem).
  have hL_cont : Continuous (L : EuclideanSpace ℝ (Fin 1) → ℝ) := L.continuous
  have hcomp := hY_tend.continuous_comp hL_cont
  -- `proj0 ∘ stdSeq n = empiricalProcess P n (X·ξ) f` pointwise.
  have hpt : ∀ (n : ℕ) (ξ : Ξ),
      (L : EuclideanSpace ℝ (Fin 1) → ℝ) (stdSeq n ξ)
      = empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ) := fun n ξ =>
    proj_std_eq_empiricalProcess μ X hX_meas hX_law (f : Ω → ℝ) hf_meas hf_memLp n ξ
  -- The limit law `ν := (mvg).map (proj0 ∘ Y)` on `ℝ`.
  set ν : Measure ℝ :=
    (multivariateGaussian 0 (marginalCovMatrix P ![(f : Ω → ℝ)])).map (L ∘ Y) with hν
  -- `ν` is a probability measure (pushforward of a Gaussian under an a.e.-measurable map).
  have hLY_aem : AEMeasurable (L ∘ Y)
      (multivariateGaussian 0 (marginalCovMatrix P ![(f : Ω → ℝ)])) :=
    hcomp.aemeasurable_limit
  have hν_prob : IsProbabilityMeasure ν := by
    rw [hν]; exact Measure.isProbabilityMeasure_map hLY_aem
  -- Tail of `ν` vanishes: the closed tails `{x | (m:ℝ) ≤ |x|}` decrease to `∅`.
  set C : ℕ → Set ℝ := fun m => {x : ℝ | (m : ℝ) ≤ |x|} with hC
  have hC_closed : ∀ m, IsClosed (C m) := fun m =>
    isClosed_le continuous_const continuous_abs
  have hC_meas : ∀ m, MeasurableSet (C m) := fun m => (hC_closed m).measurableSet
  have hC_anti : Antitone C := by
    intro a b hab x hx
    simp only [hC, Set.mem_setOf_eq] at hx ⊢
    exact le_trans (by exact_mod_cast hab) hx
  have hC_iInter : ⋂ m, C m = (∅ : Set ℝ) := by
    ext x
    simp only [hC, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_le]
    obtain ⟨m, hm⟩ := exists_nat_gt |x|
    exact ⟨m, hm⟩
  have hν_tail : Tendsto (fun m => ν (C m)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν)
      (fun m => (hC_meas m).nullMeasurableSet) hC_anti ⟨0, measure_ne_top ν _⟩
    rw [hC_iInter, measure_empty] at h
    exact h
  -- Pick `M : ℕ` with `ν (C M) ≤ ofReal δ`.
  have hδ_pos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := by positivity
  obtain ⟨M, hM⟩ := (hν_tail.eventually (gt_mem_nhds hδ_pos)).exists
  refine ⟨(M : ℝ), ?_⟩
  -- `L ∘ stdSeq n = 𝔾ₙ f` as functions `Ξ → ℝ`.
  have hLstd : ∀ n : ℕ, (L : EuclideanSpace ℝ (Fin 1) → ℝ) ∘ (stdSeq n)
      = fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ) := by
    intro n; funext ξ; exact hpt n ξ
  -- Each empirical-process readout is measurable.
  have hgmeas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)) := by
    intro n
    unfold empiricalProcess empiricalAvg
    have hsum : Measurable (fun ξ : Ξ => ∑ i : Fin n, (f : Ω → ℝ) (X i.val ξ)) :=
      Finset.measurable_sum _ (fun i _ => hf_meas.comp (hX_meas i.val))
    exact measurable_const.mul ((measurable_const.mul hsum).sub measurable_const)
  -- Apply portmanteau directly to `hcomp.tendsto` (terms stay folded via `stdSeq`/`Y`).
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hcomp.tendsto
    (hC_closed M)
  -- The portmanteau sequence/limit coes equal `μ.map (𝔾ₙf)` / `ν` (the limit coe is
  -- defeq to `ν := (mvg).map (L∘Y)`). Bridge into the wanted `≤ ν (C M)` form.
  have hbridge : limsup (fun n => (μ.map (fun ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ))) (C M)) atTop
      ≤ ν (C M) := by
    refine le_trans (le_of_eq ?_) hport
    refine limsup_congr (Eventually.of_forall fun n => ?_)
    -- `μ.map (𝔾ₙf) = μ.map (L∘stdSeq n)` (by `hLstd`), and the ProbMeas coe is defeq.
    change (μ.map (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ))) (C M)
        = (μ.map ((L : EuclideanSpace ℝ (Fin 1) → ℝ) ∘ stdSeq n)) (C M)
    rw [hLstd n]
  -- Conclude.
  calc limsup (fun n => μ {ξ | (M : ℝ) < |empiricalProcess P n
          (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|}) atTop
      ≤ limsup (fun n => (μ.map (fun ξ =>
          empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ))) (C M)) atTop := by
        refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
        change μ {ξ | (M : ℝ) < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|}
          ≤ (μ.map (fun ξ => empiricalProcess P n
              (fun i : Fin n => X i.val ξ) (f : Ω → ℝ))) (C M)
        rw [Measure.map_apply (hgmeas n) (hC_meas M)]
        refine measure_mono (fun ξ hξ => ?_)
        simp only [Set.mem_setOf_eq] at hξ
        simp only [hC, Set.mem_preimage, Set.mem_setOf_eq]
        exact le_of_lt hξ
    _ ≤ ν (C M) := hbridge
    _ ≤ ENNReal.ofReal δ := le_of_lt hM

include hF_meas in
/-- **Finite-net sup bound (the coordinate-bound half of empirical tightness).**
For any finite subset `S ⊆ ↥F` and `ε > 0` there is a uniform threshold `M`
controlling the outer probability that the empirical process exceeds `M`
somewhere on `S`, in the `limsupₙ` sense:
`limsupₙ μ* {ξ | ∃ f ∈ S, M < |𝔾ₙ f|} ≤ ofReal ε`.

The event is a FINITE union of measurable coordinate events
(`measurable_empiricalProcess_coord`), so the outer measure `μ*` collapses to `μ`
on it (`outerMeasureStar_eq_measure`); the bound then follows from
single-coordinate tightness (`marginal_coord_tight` with `δ = ε / |S|`) and the
union / finite-sum-`limsup` inequality.

vdV §18.12 (book p.260): the finite-net marginal tightness of the empirical
process. -/
theorem marginal_sup_bound_of_clt (h_clt : IsMarginalCLT F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (S : Finset ↥F) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, limsup (fun n => μ.outerMeasureStar
        {ξ | ∃ f ∈ S, M < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|}) atTop
      ≤ ENNReal.ofReal ε := by
  classical
  -- Empty `S`: the union event is empty, so its outer mass is `0 ≤ ofReal ε`.
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨0, ?_⟩
    have hempty : ∀ n,
        {ξ | ∃ f ∈ S, (0:ℝ) < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|}
          = (∅ : Set Ξ) := by
      intro n; rw [hSe]; ext ξ; simp
    calc limsup (fun n => μ.outerMeasureStar
          {ξ | ∃ f ∈ S, (0:ℝ) < |empiricalProcess P n
            (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|}) atTop
        = limsup (fun _ : ℕ => (0 : ℝ≥0∞)) atTop := by
          simp only [hempty]
          rw [outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
      _ = 0 := limsup_const 0
      _ ≤ ENNReal.ofReal ε := zero_le
  -- Per-coordinate threshold for `δ := ε / |S|`.
  set δ : ℝ := ε / (S.card + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  -- For each `f : ↥F`, a threshold `Mf` with `limsupₙ μ {Mf < |𝔾ₙ f|} ≤ ofReal δ`.
  have hcoord : ∀ f : ↥F, ∃ Mf : ℝ, limsup (fun n => μ
      {ξ | Mf < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|}) atTop
        ≤ ENNReal.ofReal δ := fun f =>
    marginal_coord_tight hF_meas h_clt μ X hX_meas hX_indep hX_id hX_law f hδ
  choose Mfun hMfun using hcoord
  -- The uniform threshold `M = max over S of Mf` (`≥ Mfun f` for all `f ∈ S`).
  set M : ℝ := S.sup' hSne (fun f => Mfun f) with hM_def
  refine ⟨M, ?_⟩
  -- Abbreviation for the per-`f` tail event at the per-`f` threshold `Mfun f`.
  set E : ↥F → ℕ → Set Ξ := fun f n =>
    {ξ | Mfun f < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|} with hE_def
  -- The union event, and its measurability (finite union of coordinate events).
  set U : ℕ → Set Ξ := fun n =>
    {ξ | ∃ f ∈ S, M < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|} with hU_def
  -- Each coordinate event `{c < |𝔾ₙ f|}` is measurable.
  have hcoord_meas : ∀ (c : ℝ) (f : ↥F) (n : ℕ), MeasurableSet
      {ξ | c < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|} := by
    intro c f n
    -- `empiricalProcess P n X g = √n · (n⁻¹ ∑ᵢ g(Xᵢ) − ∫ g dP)`: an affine
    -- combination of the measurable finite sum `ξ ↦ ∑ᵢ g(Xᵢ ξ)`.
    have hgmeas : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)) := by
      unfold empiricalProcess empiricalAvg
      have hg : Measurable (f : Ω → ℝ) := hF_meas f.1 f.2
      have hsum : Measurable (fun ξ : Ξ => ∑ i : Fin n, (f : Ω → ℝ) (X i.val ξ)) :=
        Finset.measurable_sum _ (fun i _ => hg.comp (hX_meas i.val))
      exact measurable_const.mul ((measurable_const.mul hsum).sub measurable_const)
    exact measurableSet_lt measurable_const hgmeas.abs
  -- `U n` is measurable: finite union over `S` of coordinate events.
  have hU_meas : ∀ n, MeasurableSet (U n) := by
    intro n
    have : U n = ⋃ f ∈ S,
        {ξ | M < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)|} := by
      ext ξ; simp only [hU_def, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [this]
    exact MeasurableSet.biUnion S.countable_toSet (fun f _ => hcoord_meas M f n)
  -- Step 0: the outer measure of the measurable `U n` collapses to `μ (U n)`.
  have hstar : ∀ n, μ.outerMeasureStar (U n) = μ (U n) := fun n =>
    outerMeasureStar_eq_measure (hU_meas n)
  -- Step 1: `U n ⊆ ⋃_{f∈S} E f n` (since `M ≥ Mfun f` for `f ∈ S`).
  have hMge : ∀ f ∈ S, Mfun f ≤ M := fun f hf => Finset.le_sup' (fun g => Mfun g) hf
  have hsubset : ∀ n, U n ⊆ ⋃ f ∈ S, E f n := by
    intro n ξ hξ
    simp only [hU_def, Set.mem_setOf_eq] at hξ
    obtain ⟨f, hfS, hfgt⟩ := hξ
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨f, hfS, lt_of_le_of_lt (hMge f hfS) hfgt⟩
  -- Step 2: `μ (U n) ≤ ∑_{f∈S} μ (E f n)` (union bound).
  have hunion : ∀ n, μ (U n) ≤ ∑ f ∈ S, μ (E f n) := fun n =>
    le_trans (measure_mono (hsubset n)) (measure_biUnion_finset_le S (fun f => E f n))
  -- Step 3: `limsupₙ μ (U n) ≤ ∑_{f∈S} limsupₙ μ (E f n) ≤ |S| • ofReal δ`.
  calc limsup (fun n => μ.outerMeasureStar (U n)) atTop
      = limsup (fun n => μ (U n)) atTop := by simp only [hstar]
    _ ≤ limsup (fun n => ∑ f ∈ S, μ (E f n)) atTop :=
        limsup_le_limsup (Eventually.of_forall hunion)
    _ ≤ ∑ f ∈ S, limsup (fun n => μ (E f n)) atTop :=
        limsup_finset_sum_le S (fun f n => μ (E f n))
    _ ≤ ∑ _f ∈ S, ENNReal.ofReal δ :=
        Finset.sum_le_sum (fun f _ => hMfun f)
    _ ≤ ENNReal.ofReal ε := by
        rw [Finset.sum_const, nsmul_eq_mul]
        -- `|S| • ofReal δ = ofReal (|S| · δ)` and `|S| · δ = |S|·ε/(|S|+1) ≤ ε`.
        rw [show ((S.card : ℝ≥0∞)) = ENNReal.ofReal (S.card : ℝ) by
              rw [ENNReal.ofReal_natCast]]
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hδ_def, mul_div_assoc', div_le_iff₀ (by positivity)]
        -- `|S| · ε ≤ ε · (|S| + 1)`.
        have hcard0 : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
        nlinarith [hε.le, hcard0]

end Discretization

end AsymptoticStatistics.EmpiricalProcess
