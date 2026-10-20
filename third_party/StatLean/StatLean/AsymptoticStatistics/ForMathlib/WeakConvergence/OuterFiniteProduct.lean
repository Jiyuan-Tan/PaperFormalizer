module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterTightness
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

@[expose] public section

/-!
# Finite products for outer weak convergence

The mixed readouts retain arbitrary dependence between the two coordinates;
separate marginal convergence would not suffice.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics

private theorem outerMeasureStar_mono' {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A B : Set Ω} (hAB : A ⊆ B) :
    μ.outerMeasureStar A ≤ μ.outerMeasureStar B := by
  refine outerExpectation_mono fun ω => ?_
  by_cases hω : ω ∈ A
  · simp [hω, hAB hω]
  · simp [hω]

private theorem outerMeasureStar_union_le' {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) :
    μ.outerMeasureStar (A ∪ B) ≤ μ.outerMeasureStar A + μ.outerMeasureStar B := by
  refine le_trans (outerExpectation_mono (μ := μ) (X := (A ∪ B).indicator 1)
    (Y := A.indicator 1 + B.indicator 1) (fun ω => ?_)) (outerExpectation_add_le _ _)
  refine Set.indicator_apply_le (fun hω => ?_)
  rcases hω with hA | hB
  · simp [hA]
  · simp [hB]

private theorem limsup_add_le_atTop' (u v : ℕ → ℝ≥0∞) :
    limsup (fun n => u n + v n) atTop ≤ limsup u atTop + limsup v atTop := by
  rcases eq_or_ne (limsup u atTop) ⊤ with hu | hu
  · rw [hu]
    exact le_top
  rcases eq_or_ne (limsup v atTop) ⊤ with hv | hv
  · rw [hv, add_top]
    exact le_top
  rw [limsup_le_iff isCobounded_le_of_bot
    (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)]
  intro b hb
  have hub : limsup u atTop < b - limsup v atTop := by
    rw [lt_tsub_iff_right]
    exact hb
  obtain ⟨c, huc, hcb⟩ := exists_between hub
  have hvbc : limsup v atTop < b - c := by
    rw [lt_tsub_iff_left]
    calc
      c + limsup v atTop < (b - limsup v atTop) + limsup v atTop :=
        (ENNReal.add_lt_add_iff_right hv).2 hcb
      _ = b := by
        rw [tsub_add_cancel_of_le (le_of_lt (lt_of_le_of_lt le_add_self hb))]
  have hUev : ∀ᶠ n in atTop, u n < c := eventually_lt_of_limsup_lt huc
  have hVev : ∀ᶠ n in atTop, v n < b - c := eventually_lt_of_limsup_lt hvbc
  have hcb' : c ≤ b := le_of_lt (lt_of_lt_of_le hcb tsub_le_self)
  filter_upwards [hUev, hVev] with n hUn hVn
  calc
    u n + v n < c + (b - c) := ENNReal.add_lt_add hUn hVn
    _ = b := add_tsub_cancel_of_le hcb'

/-- A finite vector of arbitrary coordinates drawn from a separating family on
`D` and the standard coordinates on `EuclideanSpace ℝ (Fin k)`.

Edge behavior: `m = 0` gives the unique map into the zero-dimensional
Euclidean space; `k = 0` leaves only the `D` coordinates. -/
noncomputable def mixedEvalCLM
    {D ι : Type*} [SeminormedAddCommGroup D] [NormedSpace ℝ D]
    {k m : ℕ} (evalD : ι → D →L[ℝ] ℝ)
    (a : Fin m → Sum ι (Fin k)) :
    (D × EuclideanSpace ℝ (Fin k)) →L[ℝ] EuclideanSpace ℝ (Fin m) := by
  let c : Fin m → (D × EuclideanSpace ℝ (Fin k)) →L[ℝ] ℝ := fun r =>
    match a r with
    | Sum.inl i =>
        (evalD i).comp (ContinuousLinearMap.fst ℝ D (EuclideanSpace ℝ (Fin k)))
    | Sum.inr j =>
        (PiLp.proj 2 (fun _ : Fin k => ℝ) j).comp
          (ContinuousLinearMap.snd ℝ D (EuclideanSpace ℝ (Fin k)))
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c)

private noncomputable def euclideanTakeLeft {m n : ℕ} :
    EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      PiLp.proj 2 (fun _ : Fin (m + n) => ℝ) (Fin.castAdd n i)))

private noncomputable def euclideanTakeRight {m n : ℕ} :
    EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      PiLp.proj 2 (fun _ : Fin (m + n) => ℝ) (Fin.natAdd m i)))

private theorem euclideanTakeLeft_mixedEvalCLM_append
    {D ι : Type*} [SeminormedAddCommGroup D] [NormedSpace ℝ D]
    {k m n : ℕ} (evalD : ι → D →L[ℝ] ℝ)
    (a : Fin m → Sum ι (Fin k)) (b : Fin n → Sum ι (Fin k))
    (x : D × EuclideanSpace ℝ (Fin k)) :
    euclideanTakeLeft (mixedEvalCLM evalD (Fin.append a b) x) = mixedEvalCLM evalD a x := by
  apply PiLp.ext
  intro i
  simp [euclideanTakeLeft, mixedEvalCLM, Fin.append_left]

private theorem euclideanTakeRight_mixedEvalCLM_append
    {D ι : Type*} [SeminormedAddCommGroup D] [NormedSpace ℝ D]
    {k m n : ℕ} (evalD : ι → D →L[ℝ] ℝ)
    (a : Fin m → Sum ι (Fin k)) (b : Fin n → Sum ι (Fin k))
    (x : D × EuclideanSpace ℝ (Fin k)) :
    euclideanTakeRight (mixedEvalCLM evalD (Fin.append a b) x) = mixedEvalCLM evalD b x := by
  apply PiLp.ext
  intro i
  simp [euclideanTakeRight, mixedEvalCLM, Fin.append_right]

private noncomputable def mixedCylinderSubalgebra
    {D ι : Type*} [SeminormedAddCommGroup D] [NormedSpace ℝ D]
    {k : ℕ} (evalD : ι → D →L[ℝ] ℝ) :
    Subalgebra ℝ ((D × EuclideanSpace ℝ (Fin k)) →ᵇ ℝ) where
  carrier := {f | ∃ (m : ℕ) (a : Fin m → Sum ι (Fin k))
      (q : EuclideanSpace ℝ (Fin m) →ᵇ ℝ),
      f = q.compContinuous ⟨mixedEvalCLM evalD a, (mixedEvalCLM evalD a).continuous⟩}
  algebraMap_mem' := by
    intro r
    refine ⟨0, Fin.elim0, BoundedContinuousFunction.const _ r, ?_⟩
    ext x
    simp
  add_mem' := by
    rintro f g ⟨m, a, q, rfl⟩ ⟨n, b, r, rfl⟩
    let left : C(EuclideanSpace ℝ (Fin (m + n)), EuclideanSpace ℝ (Fin m)) :=
      ⟨euclideanTakeLeft, euclideanTakeLeft.continuous⟩
    let right : C(EuclideanSpace ℝ (Fin (m + n)), EuclideanSpace ℝ (Fin n)) :=
      ⟨euclideanTakeRight, euclideanTakeRight.continuous⟩
    refine ⟨m + n, Fin.append a b, q.compContinuous left + r.compContinuous right, ?_⟩
    ext x
    simp only [BoundedContinuousFunction.compContinuous_apply,
      BoundedContinuousFunction.coe_add, Pi.add_apply]
    change q (mixedEvalCLM evalD a x) + r (mixedEvalCLM evalD b x) =
      q (euclideanTakeLeft (mixedEvalCLM evalD (Fin.append a b) x)) +
        r (euclideanTakeRight (mixedEvalCLM evalD (Fin.append a b) x))
    rw [euclideanTakeLeft_mixedEvalCLM_append evalD a b,
      euclideanTakeRight_mixedEvalCLM_append evalD a b]

  mul_mem' := by
    rintro f g ⟨m, a, q, rfl⟩ ⟨n, b, r, rfl⟩
    let left : C(EuclideanSpace ℝ (Fin (m + n)), EuclideanSpace ℝ (Fin m)) :=
      ⟨euclideanTakeLeft, euclideanTakeLeft.continuous⟩
    let right : C(EuclideanSpace ℝ (Fin (m + n)), EuclideanSpace ℝ (Fin n)) :=
      ⟨euclideanTakeRight, euclideanTakeRight.continuous⟩
    refine ⟨m + n, Fin.append a b, q.compContinuous left * r.compContinuous right, ?_⟩
    ext x
    simp only [BoundedContinuousFunction.compContinuous_apply,
      BoundedContinuousFunction.coe_mul, Pi.mul_apply]
    change q (mixedEvalCLM evalD a x) * r (mixedEvalCLM evalD b x) =
      q (euclideanTakeLeft (mixedEvalCLM evalD (Fin.append a b) x)) *
        r (euclideanTakeRight (mixedEvalCLM evalD (Fin.append a b) x))
    rw [euclideanTakeLeft_mixedEvalCLM_append evalD a b,
      euclideanTakeRight_mixedEvalCLM_append evalD a b]

private noncomputable def boundedArctan : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨Real.arctan, Real.continuous_arctan⟩ Real.pi (by
    intro x y
    change |Real.arctan x - Real.arctan y| ≤ Real.pi
    rw [abs_le]
    constructor <;> linarith [Real.neg_pi_div_two_lt_arctan x,
      Real.arctan_lt_pi_div_two x, Real.neg_pi_div_two_lt_arctan y,
      Real.arctan_lt_pi_div_two y])

private theorem mixedCylinderSubalgebra_separates
    {D ι : Type*} [SeminormedAddCommGroup D] [NormedSpace ℝ D]
    {k : ℕ} (evalD : ι → D →L[ℝ] ℝ)
    (hsep : ∀ x y : D, (∀ i, evalD i x = evalD i y) → x = y) :
    ((mixedCylinderSubalgebra (k := k) evalD).map (toContinuousMapₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  have hc : ∃ c : Sum ι (Fin k),
      (mixedEvalCLM evalD (fun _ : Fin 1 => c) x).ofLp 0 ≠
        (mixedEvalCLM evalD (fun _ : Fin 1 => c) y).ofLp 0 := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    have hD : x.1 = y.1 := hsep x.1 y.1 (fun i => by
      simpa [mixedEvalCLM] using hn (Sum.inl i))
    have hE : x.2 = y.2 := by
      apply PiLp.ext
      intro j
      simpa [mixedEvalCLM] using hn (Sum.inr j)
    exact hxy (Prod.ext hD hE)
  obtain ⟨c, hc⟩ := hc
  let coord : C(EuclideanSpace ℝ (Fin 1), ℝ) :=
    ⟨PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0,
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).continuous⟩
  let q : EuclideanSpace ℝ (Fin 1) →ᵇ ℝ := boundedArctan.compContinuous coord
  let a : Fin 1 → Sum ι (Fin k) := fun _ => c
  let z : (D × EuclideanSpace ℝ (Fin k)) →ᵇ ℝ :=
    q.compContinuous ⟨mixedEvalCLM evalD a, (mixedEvalCLM evalD a).continuous⟩
  refine ⟨(z : (D × EuclideanSpace ℝ (Fin k)) → ℝ), ?_, ?_⟩
  · refine ⟨(toContinuousMapₐ ℝ) z, ?_, rfl⟩
    exact ⟨z, ⟨1, a, q, rfl⟩, rfl⟩
  · change Real.arctan ((mixedEvalCLM evalD a x).ofLp 0) ≠
      Real.arctan ((mixedEvalCLM evalD a y).ofLp 0)
    exact fun h => hc (Real.arctan_injective h)

private noncomputable def boundedClamp (B : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => max (-|B|) (min x |B|),
      continuous_const.max (continuous_id.min continuous_const)⟩
    (2 * |B|) (by
      intro x y
      rw [Real.dist_eq]
      change |max (-|B|) (min x |B|) - max (-|B|) (min y |B|)| ≤ 2 * |B|
      rw [abs_le]
      have hxlo : -|B| ≤ max (-|B|) (min x |B|) := le_max_left _ _
      have hxhi : max (-|B|) (min x |B|) ≤ |B| :=
        max_le (neg_le_self (abs_nonneg B)) (min_le_right _ _)
      have hylo : -|B| ≤ max (-|B|) (min y |B|) := le_max_left _ _
      have hyhi : max (-|B|) (min y |B|) ≤ |B| :=
        max_le (neg_le_self (abs_nonneg B)) (min_le_right _ _)
      constructor <;> linarith)

private theorem boundedClamp_apply_of_mem
    {B x : ℝ} (hB : 0 ≤ B) (hlo : -B ≤ x) (hhi : x ≤ B) :
    boundedClamp B x = x := by
  change max (-|B|) (min x |B|) = x
  rw [abs_of_nonneg hB, min_eq_left hhi, max_eq_right hlo]

private theorem boundedClamp_norm_le {B : ℝ} (hB : 0 ≤ B) :
    ‖boundedClamp B‖ ≤ B := by
  rw [BoundedContinuousFunction.norm_le hB]
  intro x
  rw [Real.norm_eq_abs]
  change |max (-|B|) (min x |B|)| ≤ B
  rw [abs_le, abs_of_nonneg hB]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

namespace IsAsymptoticallyTight

/-- Coordinatewise asymptotic tightness implies asymptotic tightness of the
paired process. This is the finite-product tightness step. -/
theorem prodMk
    {Ω D E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace D] [PseudoMetricSpace E]
    {μ : ℕ → Measure Ω} {Xn : ℕ → Ω → D} {Yn : ℕ → Ω → E}
    (hX : IsAsymptoticallyTight μ Xn)
    (hY : IsAsymptoticallyTight μ Yn) :
    IsAsymptoticallyTight μ (fun n ω => (Xn n ω, Yn n ω)) := by
  intro ε hε
  obtain ⟨K, hK, hXK⟩ := hX (ε / 2) (by linarith)
  obtain ⟨L, hL, hYL⟩ := hY (ε / 2) (by linarith)
  refine ⟨K ×ˢ L, hK.prod hL, ?_⟩
  intro δ hδ
  let A : ℕ → Set Ω := fun n => Xn n ⁻¹' (Metric.thickening δ K)ᶜ
  let B : ℕ → Set Ω := fun n => Yn n ⁻¹' (Metric.thickening δ L)ᶜ
  have hsub : ∀ n,
      (fun ω => (Xn n ω, Yn n ω)) ⁻¹' (Metric.thickening δ (K ×ˢ L))ᶜ
        ⊆ A n ∪ B n := by
    intro n ω hω
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hXmem : Xn n ω ∈ Metric.thickening δ K := by
      simpa [A] using hnot.1
    have hYmem : Yn n ω ∈ Metric.thickening δ L := by
      simpa [B] using hnot.2
    rw [Metric.mem_thickening_iff] at hXmem hYmem
    obtain ⟨x, hxK, hx⟩ := hXmem
    obtain ⟨y, hyL, hy⟩ := hYmem
    apply hω
    rw [Metric.mem_thickening_iff]
    exact ⟨(x, y), ⟨hxK, hyL⟩, by simpa [Prod.dist_eq] using max_lt hx hy⟩
  let U : ℕ → ℝ≥0∞ := fun n => (μ n).outerMeasureStar (A n)
  let V : ℕ → ℝ≥0∞ := fun n => (μ n).outerMeasureStar (B n)
  have hpoint : ∀ n,
      (μ n).outerMeasureStar
          ((fun ω => (Xn n ω, Yn n ω)) ⁻¹' (Metric.thickening δ (K ×ˢ L))ᶜ)
        ≤ U n + V n := by
    intro n
    exact (outerMeasureStar_mono' (μ n) (hsub n)).trans
      (outerMeasureStar_union_le' (μ n) (A n) (B n))
  have hlim_mono : limsup (fun n => (μ n).outerMeasureStar
        ((fun ω => (Xn n ω, Yn n ω)) ⁻¹' (Metric.thickening δ (K ×ˢ L))ᶜ)) atTop
      ≤ limsup (fun n => U n + V n) atTop :=
    limsup_le_limsup (Eventually.of_forall hpoint)
      isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
  calc
    limsup (fun n => (μ n).outerMeasureStar
        ((fun ω => (Xn n ω, Yn n ω)) ⁻¹' (Metric.thickening δ (K ×ˢ L))ᶜ)) atTop
        ≤ limsup (fun n => U n + V n) atTop := hlim_mono
    _ ≤ limsup U atTop + limsup V atTop := limsup_add_le_atTop' U V
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hXK δ hδ) (hYL δ hδ)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

end IsAsymptoticallyTight

/-- Continuous mapping for weak convergence in outer expectation.

The target law is the pushforward `ν.map g`. `OpensMeasurableSpace E` and
`hg_meas` ensure that continuous target readouts and the pushforward integral
are measurable. Finiteness of each source measure is needed when the exact
constant re-shift is passed through `ENNReal.toReal`. -/
theorem WeakConvergesOuter.map
    {Ω D E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] [MeasurableSpace E]
    [PseudoMetricSpace D] [PseudoMetricSpace E]
    {μ : ℕ → Measure Ω} {Xn : ℕ → Ω → D} {ν : Measure D}
    [OpensMeasurableSpace E] [∀ n, IsFiniteMeasure (μ n)]
    (h : WeakConvergesOuter μ Xn ν) (g : D → E)
    (hg : Continuous g)
    (hg_meas : AEMeasurable g ν) :
    WeakConvergesOuter μ (fun n ω => g (Xn n ω)) (ν.map g) := by
  intro f
  let gc : C(D, E) := ⟨g, hg⟩
  let fg : D →ᵇ ℝ := f.compContinuous gc
  have hnorm : ‖fg‖ ≤ ‖f‖ := f.norm_compContinuous_le gc
  have hbase_nonneg : ∀ x : D, 0 ≤ fg x + ‖fg‖ := by
    intro x
    have hx := (abs_le.1 (fg.norm_coe_le_norm x)).1
    linarith
  have hshift : ∀ n,
      (outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f (g (Xn n ω)) + ‖f‖))).toReal
          - ‖f‖ * (μ n Set.univ).toReal
        = (outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (fg (Xn n ω) + ‖fg‖))).toReal
          - ‖fg‖ * (μ n Set.univ).toReal := by
    intro n
    have hfun : (fun ω => ENNReal.ofReal (f (g (Xn n ω)) + ‖f‖)) =
        fun ω => ENNReal.ofReal (fg (Xn n ω) + ‖fg‖) + ENNReal.ofReal (‖f‖ - ‖fg‖) := by
      funext ω
      rw [← ENNReal.ofReal_add (hbase_nonneg _) (sub_nonneg.2 hnorm)]
      congr 1
      change f (g (Xn n ω)) + ‖f‖ =
        (f (g (Xn n ω)) + ‖fg‖) + (‖f‖ - ‖fg‖)
      ring
    have hbound : outerExpectation (μ n)
        (fun ω => ENNReal.ofReal (fg (Xn n ω) + ‖fg‖))
        ≤ ENNReal.ofReal (2 * ‖fg‖) * μ n Set.univ := by
      calc
        outerExpectation (μ n)
            (fun ω => ENNReal.ofReal (fg (Xn n ω) + ‖fg‖))
            ≤ outerExpectation (μ n) (fun _ => ENNReal.ofReal (2 * ‖fg‖)) :=
          outerExpectation_mono (fun ω => ENNReal.ofReal_le_ofReal (by
            have hx := (abs_le.1 (fg.norm_coe_le_norm (Xn n ω))).2
            linarith))
        _ = ENNReal.ofReal (2 * ‖fg‖) * μ n Set.univ :=
          outerExpectation_const _
    have hfinite : outerExpectation (μ n)
        (fun ω => ENNReal.ofReal (fg (Xn n ω) + ‖fg‖)) ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hbound
    rw [hfun, outerExpectation_add_const _ _ ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hfinite
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hnorm)]
    ring
  have ht := h fg
  rw [show (∫ y, f y ∂ν.map g) = ∫ x, fg x ∂ν by
    rw [MeasureTheory.integral_map hg_meas f.continuous.aestronglyMeasurable]
    rfl]
  simpa only [hshift] using ht

private theorem outerReadout_eq_commonShift
    {Ω D : Type*} [MeasurableSpace Ω] [PseudoMetricSpace D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → D)
    (f : D →ᵇ ℝ) {M : ℝ} (hfM : ‖f‖ ≤ M) :
    (outerExpectation μ
        (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))).toReal - ‖f‖ =
      (outerExpectation μ
        (fun ω => ENNReal.ofReal (f (X ω) + M))).toReal - M := by
  have hsplit : (fun ω => ENNReal.ofReal (f (X ω) + M)) =
      fun ω => ENNReal.ofReal (f (X ω) + ‖f‖) + ENNReal.ofReal (M - ‖f‖) := by
    funext ω
    rw [← ENNReal.ofReal_add (by
      have hx := (abs_le.1 (f.norm_coe_le_norm (X ω))).1
      linarith) (sub_nonneg.2 hfM)]
    congr 1
    ring
  have hbound : outerExpectation μ
      (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖)) ≤ ENNReal.ofReal (2 * ‖f‖) := by
    calc
      outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))
          ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) :=
        outerExpectation_mono (fun ω => ENNReal.ofReal_le_ofReal (by
          have hx := (abs_le.1 (f.norm_coe_le_norm (X ω))).2
          linarith))
      _ = ENNReal.ofReal (2 * ‖f‖) := by rw [outerExpectation_const]; simp
  have hfinite : outerExpectation μ
      (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  rw [hsplit, outerExpectation_add_const _ _ ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hfinite
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hfM)]
  simp only [measure_univ, ENNReal.toReal_one, mul_one]
  ring

private theorem abs_outerReadout_diff_le_of_close_off
    {Ω D : Type*} [MeasurableSpace Ω] [PseudoMetricSpace D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → D)
    (f g : D →ᵇ ℝ) (A : Set Ω) {η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ ω, ω ∉ A → |f (X ω) - g (X ω)| ≤ η) :
    |((outerExpectation μ
          (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))).toReal - ‖f‖) -
        ((outerExpectation μ
          (fun ω => ENNReal.ofReal (g (X ω) + ‖g‖))).toReal - ‖g‖)|
      ≤ η + (‖f‖ + ‖g‖) * (μ.outerMeasureStar A).toReal := by
  classical
  set M : ℝ := ‖f‖ + ‖g‖ with hM
  set ind : Ω → ℝ≥0∞ := A.indicator (fun _ => 1)
  set EF := outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + M))
  set EG := outerExpectation μ (fun ω => ENNReal.ofReal (g (X ω) + M))
  set I := outerExpectation μ ind
  have hfM : ‖f‖ ≤ M := by rw [hM]; linarith [norm_nonneg g]
  have hgM : ‖g‖ ≤ M := by rw [hM]; linarith [norm_nonneg f]
  have hI : I = μ.outerMeasureStar A := by rfl
  have hI_le : I ≤ 1 := by
    calc
      I ≤ outerExpectation μ (fun _ => 1) :=
        outerExpectation_mono fun ω => Set.indicator_le_self _ _ ω
      _ = 1 := by rw [outerExpectation_const]; simp
  have hI_top : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hI_le
  have hbound : ∀ (u : D →ᵇ ℝ), ‖u‖ ≤ M →
      outerExpectation μ (fun ω => ENNReal.ofReal (u (X ω) + M))
        ≤ ENNReal.ofReal (2 * M) := by
    intro u hu
    calc
      outerExpectation μ (fun ω => ENNReal.ofReal (u (X ω) + M))
          ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * M)) :=
        outerExpectation_mono (fun ω => ENNReal.ofReal_le_ofReal (by
          have hx := (abs_le.1 (u.norm_coe_le_norm (X ω))).2
          linarith))
      _ = ENNReal.ofReal (2 * M) := by rw [outerExpectation_const]; simp
  have hEF_top : EF ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound f hfM)
  have hEG_top : EG ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound g hgM)
  have hone (u v : D →ᵇ ℝ) (huM : ‖u‖ ≤ M) (hvM : ‖v‖ ≤ M)
      (hfar : ∀ ω, u (X ω) ≤ v (X ω) + M)
      (huv : ∀ ω, ω ∉ A → u (X ω) ≤ v (X ω) + η) :
      outerExpectation μ (fun ω => ENNReal.ofReal (u (X ω) + M)) ≤
        outerExpectation μ (fun ω => ENNReal.ofReal (v (X ω) + M)) +
          ENNReal.ofReal η + ENNReal.ofReal M * I := by
    have hpoint : ∀ ω, ENNReal.ofReal (u (X ω) + M) ≤
        ENNReal.ofReal (v (X ω) + M) +
          (ENNReal.ofReal η + ENNReal.ofReal M * ind ω) := by
      intro ω
      have hv_nonneg : 0 ≤ v (X ω) + M := by
        have hx := (abs_le.1 (v.norm_coe_le_norm (X ω))).1
        linarith
      by_cases hω : ω ∈ A
      · have hind : ind ω = 1 := by simp [ind, hω]
        rw [hind, mul_one]
        calc
          ENNReal.ofReal (u (X ω) + M) ≤
              ENNReal.ofReal ((v (X ω) + M) + (η + M)) :=
            ENNReal.ofReal_le_ofReal (by linarith [hfar ω])
          _ = ENNReal.ofReal (v (X ω) + M) +
                (ENNReal.ofReal η + ENNReal.ofReal M) := by
            rw [ENNReal.ofReal_add hv_nonneg (by positivity),
              ENNReal.ofReal_add hη (by positivity)]
      · have hind : ind ω = 0 := by simp [ind, hω]
        rw [hind, mul_zero, add_zero]
        rw [← ENNReal.ofReal_add hv_nonneg hη]
        exact ENNReal.ofReal_le_ofReal (by linarith [huv ω hω])
    have hs := outerExpectation_add_le (μ := μ)
      (fun ω => ENNReal.ofReal (v (X ω) + M))
      (fun ω => ENNReal.ofReal η + ENNReal.ofReal M * ind ω)
    have herr := outerExpectation_add_le (μ := μ) (fun _ => ENNReal.ofReal η)
      (fun ω => ENNReal.ofReal M * ind ω)
    have hconst : outerExpectation μ (fun _ => ENNReal.ofReal η) = ENNReal.ofReal η := by
      rw [outerExpectation_const]
      simp
    have hmul : outerExpectation μ (fun ω => ENNReal.ofReal M * ind ω) =
        ENNReal.ofReal M * I := by
      have heq : (fun ω => ENNReal.ofReal M * ind ω) = ENNReal.ofReal M • ind := by
        ext ω
        simp [smul_eq_mul]
      change outerExpectation μ (fun ω => ENNReal.ofReal M * ind ω) =
        ENNReal.ofReal M * outerExpectation μ ind
      rw [heq, outerExpectation_const_smul _ ENNReal.ofReal_ne_top, smul_eq_mul]
    calc
      outerExpectation μ (fun ω => ENNReal.ofReal (u (X ω) + M))
          ≤ outerExpectation μ (fun ω => ENNReal.ofReal (v (X ω) + M) +
              (ENNReal.ofReal η + ENNReal.ofReal M * ind ω)) :=
        outerExpectation_mono hpoint
      _ ≤ outerExpectation μ (fun ω => ENNReal.ofReal (v (X ω) + M)) +
            outerExpectation μ (fun ω => ENNReal.ofReal η + ENNReal.ofReal M * ind ω) := hs
      _ ≤ outerExpectation μ (fun ω => ENNReal.ofReal (v (X ω) + M)) +
            (outerExpectation μ (fun _ => ENNReal.ofReal η) +
              outerExpectation μ (fun ω => ENNReal.ofReal M * ind ω)) :=
        add_le_add le_rfl herr
      _ = outerExpectation μ (fun ω => ENNReal.ofReal (v (X ω) + M)) +
            ENNReal.ofReal η + ENNReal.ofReal M * I := by rw [hconst, hmul]; ac_rfl
  have hfg : EF ≤ EG + ENNReal.ofReal η + ENNReal.ofReal M * I := by
    apply hone f g hfM hgM
    · intro ω
      have hf := (abs_le.1 (f.norm_coe_le_norm (X ω))).2
      have hg := (abs_le.1 (g.norm_coe_le_norm (X ω))).1
      rw [hM]
      linarith
    intro ω hω
    linarith [le_trans (le_abs_self (f (X ω) - g (X ω))) (hclose ω hω)]
  have hgf : EG ≤ EF + ENNReal.ofReal η + ENNReal.ofReal M * I := by
    apply hone g f hgM hfM
    · intro ω
      have hg := (abs_le.1 (g.norm_coe_le_norm (X ω))).2
      have hf := (abs_le.1 (f.norm_coe_le_norm (X ω))).1
      rw [hM]
      linarith
    intro ω hω
    have hc := hclose ω hω
    rw [abs_sub_comm] at hc
    linarith [le_trans (le_abs_self (g (X ω) - f (X ω))) hc]
  have herr_top : ENNReal.ofReal η + ENNReal.ofReal M * I ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top⟩
  have hfg' : EF ≤ EG + (ENNReal.ofReal η + ENNReal.ofReal M * I) := by
    simpa [add_assoc] using hfg
  have hgf' : EG ≤ EF + (ENNReal.ofReal η + ENNReal.ofReal M * I) := by
    simpa [add_assoc] using hgf
  have hfg_real := (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hEG_top, herr_top⟩) hfg')
    (ENNReal.add_ne_top.2 ⟨hEG_top, herr_top⟩)).2 hfg'
  have hgf_real := (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hEF_top, herr_top⟩) hgf')
    (ENNReal.add_ne_top.2 ⟨hEF_top, herr_top⟩)).2 hgf'
  rw [ENNReal.toReal_add hEG_top herr_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hη,
    ENNReal.toReal_ofReal (by positivity)] at hfg_real
  rw [ENNReal.toReal_add hEF_top herr_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hη,
    ENNReal.toReal_ofReal (by positivity)] at hgf_real
  simp only [EF, EG, hI] at hfg_real hgf_real
  rw [outerReadout_eq_commonShift μ X f hfM,
    outerReadout_eq_commonShift μ X g hgM, abs_sub_le_iff]
  constructor <;> linarith

private theorem abs_integral_sub_le_of_close_on
    {D : Type*} [MeasurableSpace D] [PseudoMetricSpace D] [OpensMeasurableSpace D]
    (κ : Measure D) [IsProbabilityMeasure κ] (f g : D →ᵇ ℝ)
    (U : Set D) (hU : MeasurableSet U) {η B : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ x ∈ U, |f x - g x| ≤ η)
    (hglobal : ∀ x, |f x - g x| ≤ B) :
    |(∫ x, f x ∂κ) - ∫ x, g x ∂κ| ≤ η + B * (κ Uᶜ).toReal := by
  let ind : D → ℝ := Uᶜ.indicator (fun _ => 1)
  have hind_int : Integrable ind κ := (integrable_const (1 : ℝ)).indicator hU.compl
  have herr_int : Integrable (fun x => η + B * ind x) κ :=
    (integrable_const η).add (hind_int.const_mul B)
  have hdiff_int : Integrable (fun x => f x - g x) κ :=
    (f.integrable κ).sub (g.integrable κ)
  have hpoint : ∀ x, |f x - g x| ≤ η + B * ind x := by
    intro x
    by_cases hx : x ∈ U
    · simp only [ind, Set.indicator_of_notMem (show x ∉ Uᶜ by simpa), mul_zero, add_zero]
      exact hclose x hx
    · simp only [ind, Set.indicator_of_mem (show x ∈ Uᶜ by simpa), mul_one]
      linarith [hglobal x]
  rw [← integral_sub (f.integrable κ) (g.integrable κ), ← Real.norm_eq_abs]
  calc
    ‖∫ x, f x - g x ∂κ‖ ≤ ∫ x, ‖f x - g x‖ ∂κ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, |f x - g x| ∂κ := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ x, η + B * ind x ∂κ :=
      integral_mono hdiff_int.abs herr_int hpoint
    _ = η + B * (κ Uᶜ).toReal := by
      rw [integral_add, integral_const, integral_const_mul]
      · change κ.real Set.univ • η +
            B * (∫ x, Uᶜ.indicator (fun _ => (1 : ℝ)) x ∂κ) =
          η + B * (κ Uᶜ).toReal
        have hindicator : (∫ x, Uᶜ.indicator (fun _ => (1 : ℝ)) x ∂κ) =
            κ.real Uᶜ := by
          simpa only [Pi.one_apply] using! (integral_indicator_one (μ := κ) hU.compl)
        rw [hindicator]
        change (κ Set.univ).toReal * η + B * (κ Uᶜ).toReal =
          η + B * (κ Uᶜ).toReal
        simp
      · exact integrable_const η
      · exact hind_int.const_mul B

/-- Mixed finite-dimensional distributions plus tightness determine outer weak
convergence of a process in `D × ℝᵏ`.

The hypothesis quantifies over every finite tuple
`a : Fin m → Sum ι (Fin k)`, so it records the full mixed dependence between
the process coordinates and the finite-dimensional coordinate. -/
theorem weakConvergesOuter_prod_of_tight_mixedEval
    {Ω D ι : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasurableSpace D] [BorelSpace D]
    {k : ℕ} {μ : ℕ → Measure Ω}
    {Wn : ℕ → Ω → D × EuclideanSpace ℝ (Fin k)}
    {κ : Measure (D × EuclideanSpace ℝ (Fin k))}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure κ]
    (evalD : ι → D →L[ℝ] ℝ)
    (hsep : ∀ x y : D, (∀ i, evalD i x = evalD i y) → x = y)
    (htight : IsAsymptoticallyTight μ Wn)
    (hκtight : IsTightMeasureSet
      ({κ} : Set (Measure (D × EuclideanSpace ℝ (Fin k)))))
    (hmixed : ∀ (m : ℕ) (a : Fin m → Sum ι (Fin k)),
      WeakConvergesOuter μ
        (fun n ω => mixedEvalCLM evalD a (Wn n ω))
        (κ.map (mixedEvalCLM evalD a))) :
    WeakConvergesOuter μ Wn κ := by
  classical
  intro f
  simp_rw [show ∀ n, (μ n Set.univ).toReal = 1 from fun n => by simp, mul_one]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set α : ℝ := ε / 8 with hαdef
  set Q : ℝ := 2 * ‖f‖ + α with hQdef
  set ρ : ℝ := ε / (16 * (Q + 1)) with hρdef
  have hα : 0 < α := by rw [hαdef]; positivity
  have hQ : 0 ≤ Q := by rw [hQdef]; positivity
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  obtain ⟨K, hKcompact, hKtail⟩ := htight ρ hρ
  obtain ⟨L, hLcompact, hLmass_all⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hκtight)
      (ENNReal.ofReal ρ) (by simp [hρ])
  have hLmass : κ Lᶜ ≤ ENNReal.ofReal ρ := hLmass_all κ rfl
  let C : Set (D × EuclideanSpace ℝ (Fin k)) := K ∪ L
  have hCcompact : IsCompact C := hKcompact.union hLcompact
  obtain ⟨g0, hg0A, hg0close⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (mixedCylinderSubalgebra_separates evalD hsep) f.toContinuousMap hCcompact hα
  obtain ⟨g0b, hg0bA, hg0eq⟩ := Subalgebra.mem_map.1 hg0A
  obtain ⟨m, a, q0, hg0repr⟩ := hg0bA
  have hg0apply : ∀ x, g0 x = g0b x := by
    intro x
    rw [← hg0eq]
    rfl
  let B : ℝ := ‖f‖ + α
  have hB : 0 ≤ B := by simp only [B]; positivity
  let q : EuclideanSpace ℝ (Fin m) →ᵇ ℝ :=
    (boundedClamp B).compContinuous q0.toContinuousMap
  let T : (D × EuclideanSpace ℝ (Fin k)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    mixedEvalCLM evalD a
  let g : (D × EuclideanSpace ℝ (Fin k)) →ᵇ ℝ :=
    q.compContinuous ⟨T, T.continuous⟩
  have hg_apply : ∀ x, g x = boundedClamp B (g0b x) := by
    intro x
    simp only [g, q, BoundedContinuousFunction.compContinuous_apply]
    rw [hg0repr]
    rfl
  have hg_close_C : ∀ x ∈ C, |g x - f x| < α := by
    intro x hx
    have h0 : |g0b x - f x| < α := by
      simpa [Real.norm_eq_abs, hg0apply x] using hg0close x hx
    have hfbd := f.norm_coe_le_norm x
    have hlo : -B ≤ g0b x := by
      change -(‖f‖ + α) ≤ g0b x
      have := (abs_lt.1 h0).1
      have := (abs_le.1 hfbd).1
      linarith
    have hhi : g0b x ≤ B := by
      change g0b x ≤ ‖f‖ + α
      have := (abs_lt.1 h0).2
      have := (abs_le.1 hfbd).2
      linarith
    rw [hg_apply, boundedClamp_apply_of_mem hB hlo hhi]
    exact h0
  have hg_norm : ‖g‖ ≤ B := by
    rw [BoundedContinuousFunction.norm_le hB]
    intro x
    rw [hg_apply]
    exact le_trans (BoundedContinuousFunction.norm_coe_le_norm (boundedClamp B) (g0b x))
      (boundedClamp_norm_le hB)
  let U : Set (D × EuclideanSpace ℝ (Fin k)) := {x | |g x - f x| < α}
  have hUopen : IsOpen U := by
    exact isOpen_lt (continuous_abs.comp (g.continuous.sub f.continuous)) continuous_const
  have hCU : C ⊆ U := fun x hx => hg_close_C x hx
  obtain ⟨δ, hδ, hthick⟩ := hCcompact.exists_thickening_subset_open hUopen hCU
  let V : Set (D × EuclideanSpace ℝ (Fin k)) := Metric.thickening δ C
  let A : ℕ → Set Ω := fun n => Wn n ⁻¹' Vᶜ
  let tail : ℕ → ℝ≥0∞ := fun n => (μ n).outerMeasureStar (A n)
  have hA_sub : ∀ n,
      A n ⊆ Wn n ⁻¹' (Metric.thickening δ K)ᶜ := by
    intro n ω hω hmem
    apply hω
    simpa only [V] using
      (Metric.thickening_subset_of_subset δ
        (show K ⊆ C from Set.subset_union_left) hmem)
  have htail_point : ∀ n, tail n ≤
      (μ n).outerMeasureStar (Wn n ⁻¹' (Metric.thickening δ K)ᶜ) := by
    intro n
    exact outerMeasureStar_mono' (μ n) (hA_sub n)
  have htail_limsup : limsup tail atTop ≤ ENNReal.ofReal ρ := by
    calc
      limsup tail atTop ≤ limsup (fun n =>
          (μ n).outerMeasureStar (Wn n ⁻¹' (Metric.thickening δ K)ᶜ)) atTop :=
        limsup_le_limsup (Eventually.of_forall htail_point) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      _ ≤ ENNReal.ofReal ρ := hKtail δ hδ
  have htail_limsup_lt : limsup tail atTop < ENNReal.ofReal (2 * ρ) :=
    htail_limsup.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  have htail_ev_enn : ∀ᶠ n in atTop, tail n < ENNReal.ofReal (2 * ρ) :=
    eventually_lt_of_limsup_lt htail_limsup_lt
  have htail_ev : ∀ᶠ n in atTop, (tail n).toReal < 2 * ρ := by
    filter_upwards [htail_ev_enn] with n hn
    have hr := (ENNReal.toReal_lt_toReal hn.ne_top ENNReal.ofReal_ne_top).2 hn
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ρ)] at hr
    exact hr
  let R : ((D × EuclideanSpace ℝ (Fin k)) →ᵇ ℝ) → ℕ → ℝ := fun u n =>
    (outerExpectation (μ n)
      (fun ω => ENNReal.ofReal (u (Wn n ω) + ‖u‖))).toReal - ‖u‖
  have hreadout_eq : ∀ n,
      (outerExpectation (μ n) (fun ω =>
          ENNReal.ofReal (q (T (Wn n ω)) + ‖q‖))).toReal - ‖q‖ = R g n := by
    intro n
    let S : ℝ := ‖q‖ + ‖g‖
    have hqS : ‖q‖ ≤ S := by simp only [S]; linarith [norm_nonneg g]
    have hgS : ‖g‖ ≤ S := by simp only [S]; linarith [norm_nonneg q]
    simp only [R]
    rw [outerReadout_eq_commonShift (μ n) (fun ω => T (Wn n ω)) q hqS,
      outerReadout_eq_commonShift (μ n) (Wn n) g hgS]
    congr 2
  have hint_map : (∫ y, q y ∂κ.map T) = ∫ x, g x ∂κ := by
    rw [MeasureTheory.integral_map T.continuous.aemeasurable
      q.continuous.aestronglyMeasurable]
    rfl
  have hgconv : Tendsto (R g) atTop (𝓝 (∫ x, g x ∂κ)) := by
    have h := hmixed m a q
    rw [hint_map] at h
    simp_rw [show ∀ n, (μ n Set.univ).toReal = 1 from fun n => by simp, mul_one] at h
    have hreadout_eq' : ∀ n,
        (outerExpectation (μ n) (fun ω => ENNReal.ofReal
          (q (mixedEvalCLM evalD a (Wn n ω)) + ‖q‖))).toReal - ‖q‖ = R g n := by
      intro n
      simpa only [T] using hreadout_eq n
    simpa only [hreadout_eq'] using h
  have hg_ev : ∀ᶠ n in atTop, |R g n - ∫ x, g x ∂κ| < ε / 4 := by
    rw [Metric.tendsto_atTop] at hgconv
    simpa [Real.dist_eq] using hgconv (ε / 4) (by positivity)
  have hnorm_sum : ‖f‖ + ‖g‖ ≤ Q := by
    rw [hQdef]
    have := hg_norm
    change ‖g‖ ≤ ‖f‖ + α at this
    linarith
  have hclose_V : ∀ x ∈ V, |f x - g x| ≤ α := by
    intro x hx
    have hu : x ∈ U := hthick (by simpa only [V] using hx)
    change |g x - f x| < α at hu
    simpa only [abs_sub_comm] using le_of_lt hu
  have hglobal : ∀ x, |f x - g x| ≤ Q := by
    intro x
    calc
      |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
      _ ≤ ‖f‖ + ‖g‖ := add_le_add (by
          simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (by
          simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x)
      _ ≤ Q := hnorm_sum
  have hκV : κ Vᶜ ≤ ENNReal.ofReal ρ := by
    exact (measure_mono (Set.compl_subset_compl.2 <|
      Set.subset_union_right.trans (Metric.self_subset_thickening hδ C))).trans hLmass
  have hκV_real : (κ Vᶜ).toReal ≤ ρ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hκV
    simpa only [ENNReal.toReal_ofReal hρ.le] using h
  have hint_close : |(∫ x, f x ∂κ) - ∫ x, g x ∂κ| ≤
      α + Q * (κ Vᶜ).toReal :=
    abs_integral_sub_le_of_close_on κ f g V
      Metric.isOpen_thickening.measurableSet hα.le hclose_V hglobal
  have hRclose : ∀ n, |R f n - R g n| ≤ α + Q * (tail n).toReal := by
    intro n
    have hloc := abs_outerReadout_diff_le_of_close_off
      (μ n) (Wn n) f g (A n) hα.le (fun ω hω => by
        have hWV : Wn n ω ∈ V := by
          by_contra hnV
          exact hω (by simpa only [A, Set.mem_preimage, Set.mem_compl_iff] using hnV)
        exact hclose_V _ hWV)
    calc
      |R f n - R g n| ≤ α + (‖f‖ + ‖g‖) * (tail n).toReal := by
        simpa only [R, tail, A] using hloc
      _ ≤ α + Q * (tail n).toReal := by gcongr
  have hQρ : Q * ρ ≤ ε / 16 := by
    rw [hρdef]
    have hden : 0 < 16 * (Q + 1) := by positivity
    calc
      Q * (ε / (16 * (Q + 1))) = (ε * Q) / (16 * (Q + 1)) := by ring
      _ ≤ ε / 16 := by
        rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 16)]
        nlinarith
  have hint_bound : |(∫ x, f x ∂κ) - ∫ x, g x ∂κ| ≤ 3 * ε / 16 := by
    calc
      |(∫ x, f x ∂κ) - ∫ x, g x ∂κ| ≤ α + Q * (κ Vᶜ).toReal := hint_close
      _ ≤ α + Q * ρ := by gcongr
      _ ≤ 3 * ε / 16 := by rw [hαdef]; linarith
  rw [eventually_atTop] at htail_ev hg_ev
  obtain ⟨Ntail, hNtail⟩ := htail_ev
  obtain ⟨Ng, hNg⟩ := hg_ev
  refine ⟨max Ntail Ng, fun n hn => ?_⟩
  have hntail : (tail n).toReal < 2 * ρ := hNtail n (le_trans (le_max_left _ _) hn)
  have hng : |R g n - ∫ x, g x ∂κ| < ε / 4 :=
    hNg n (le_trans (le_max_right _ _) hn)
  have hRbound : |R f n - R g n| ≤ ε / 4 := by
    calc
      |R f n - R g n| ≤ α + Q * (tail n).toReal := hRclose n
      _ ≤ α + Q * (2 * ρ) := by gcongr
      _ ≤ ε / 4 := by rw [hαdef]; nlinarith
  change dist (R f n) (∫ x, f x ∂κ) < ε
  rw [Real.dist_eq]
  calc
    |R f n - ∫ x, f x ∂κ| ≤
        |R f n - R g n| +
          (|R g n - ∫ x, g x ∂κ| +
            |(∫ x, g x ∂κ) - ∫ x, f x ∂κ|) :=
      (abs_sub_le (R f n) (R g n) (∫ x, f x ∂κ)).trans
        (add_le_add le_rfl (abs_sub_le (R g n) (∫ x, g x ∂κ) (∫ x, f x ∂κ)))
    _ < ε := by
      rw [abs_sub_comm (∫ x, g x ∂κ) (∫ x, f x ∂κ)]
      linarith

end AsymptoticStatistics
