module
public import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Topology.MetricSpace.ThickenedIndicator
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-! # Bounded uniformly-continuous bowl approximation -/
open Filter Topology
open scoped ENNReal NNReal
namespace AsymptoticStatistics.LowerBounds.BowlShapedUCApprox
open AsymptoticStatistics

private noncomputable def softSublevelStep {E : Type*}
    [PseudoEMetricSpace E] (L : E → ℝ≥0∞) (q : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    E → ℝ≥0∞ := fun x =>
  ((q * (1 - thickenedIndicator hδ {y | L y ≤ (q : ℝ≥0∞)} x) : ℝ≥0) : ℝ≥0∞)

private theorem softSublevelStep_bowl {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : E → ℝ≥0∞) (hL : BowlShaped L) (_hL_lsc : LowerSemicontinuous L)
    (q : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    BowlShaped (softSublevelStep L q δ hδ) := by
  let S : Set E := {y | L y ≤ (q : ℝ≥0∞)}
  have hSconv : Convex ℝ S := hL.convex_sublevel (q : ℝ≥0∞)
  have hSneg : -S = S := by
    ext x
    rw [Set.mem_neg]
    change L (-x) ≤ (q : ℝ≥0∞) ↔ L x ≤ (q : ℝ≥0∞)
    rw [hL.symm]
  refine ⟨?_, ?_, ?_⟩
  · have : Continuous (softSublevelStep L q δ hδ) := by
      unfold softSublevelStep
      fun_prop
    exact this.measurable
  · intro x
    have hd : Metric.infEDist (-x) S = Metric.infEDist x S := by
      rw [infEDist_neg, hSneg]
    unfold softSublevelStep
    norm_cast
    change q * (1 - (thickenedIndicatorAux δ S (-x)).toNNReal) =
      q * (1 - (thickenedIndicatorAux δ S x).toNNReal)
    rw [show thickenedIndicatorAux δ S (-x) = thickenedIndicatorAux δ S x by
      unfold thickenedIndicatorAux
      rw [hd]]
  · intro c x hx y hy a b ha hb hab
    change softSublevelStep L q δ hδ (a • x + b • y) ≤ c
    change softSublevelStep L q δ hδ x ≤ c at hx
    change softSublevelStep L q δ hδ y ≤ c at hy
    by_cases hS : S = ∅
    · simpa [softSublevelStep, thickenedIndicator, thickenedIndicatorAux,
        S, hS] using hx
    · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
      rcases le_total (Metric.infEDist x S) (Metric.infEDist y S) with hxy | hyx
      · have hxmem : x ∈ Metric.cthickening (Metric.infDist y S) S := by
          change Metric.infEDist x S ≤ ENNReal.ofReal (Metric.infDist y S)
          rw [Metric.infDist, ENNReal.ofReal_toReal (Metric.infEDist_ne_top hSne)]
          exact hxy
        have hymem : y ∈ Metric.cthickening (Metric.infDist y S) S := by
          change Metric.infEDist y S ≤ ENNReal.ofReal (Metric.infDist y S)
          rw [Metric.infDist, ENNReal.ofReal_toReal (Metric.infEDist_ne_top hSne)]
        have hzmem := (hSconv.cthickening (Metric.infDist y S)) hxmem hymem ha hb hab
        have hzdist : Metric.infEDist (a • x + b • y) S ≤ Metric.infEDist y S := by
          change Metric.infEDist (a • x + b • y) S ≤
            ENNReal.ofReal (Metric.infDist y S) at hzmem
          rwa [Metric.infDist,
            ENNReal.ofReal_toReal (Metric.infEDist_ne_top hSne)] at hzmem
        have hind : thickenedIndicator hδ S y ≤
            thickenedIndicator hδ S (a • x + b • y) :=
          thickenedIndicator_mono_infEDist hδ hzdist
        apply (show softSublevelStep L q δ hδ (a • x + b • y) ≤
            softSublevelStep L q δ hδ y by
          simp only [softSublevelStep]
          gcongr).trans hy
      · have hymem : y ∈ Metric.cthickening (Metric.infDist x S) S := by
          change Metric.infEDist y S ≤ ENNReal.ofReal (Metric.infDist x S)
          rw [Metric.infDist, ENNReal.ofReal_toReal (Metric.infEDist_ne_top hSne)]
          exact hyx
        have hxmem : x ∈ Metric.cthickening (Metric.infDist x S) S := by
          change Metric.infEDist x S ≤ ENNReal.ofReal (Metric.infDist x S)
          rw [Metric.infDist, ENNReal.ofReal_toReal (Metric.infEDist_ne_top hSne)]
        have hzmem := (hSconv.cthickening (Metric.infDist x S)) hxmem hymem ha hb hab
        have hzdist : Metric.infEDist (a • x + b • y) S ≤ Metric.infEDist x S := by
          change Metric.infEDist (a • x + b • y) S ≤
            ENNReal.ofReal (Metric.infDist x S) at hzmem
          rwa [Metric.infDist,
            ENNReal.ofReal_toReal (Metric.infEDist_ne_top hSne)] at hzmem
        have hind : thickenedIndicator hδ S x ≤
            thickenedIndicator hδ S (a • x + b • y) :=
          thickenedIndicator_mono_infEDist hδ hzdist
        apply (show softSublevelStep L q δ hδ (a • x + b • y) ≤
            softSublevelStep L q δ hδ x by
          simp only [softSublevelStep]
          gcongr).trans hx

private theorem softSublevelStep_toReal {E : Type*} [PseudoMetricSpace E]
    (L : E → ℝ≥0∞) (q : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (x : E) :
    (softSublevelStep L q δ hδ x).toReal =
      (q : ℝ) * (1 - (thickenedIndicator hδ {y | L y ≤ (q : ℝ≥0∞)} x : ℝ)) := by
  rw [softSublevelStep]
  rw [ENNReal.coe_toReal]
  simp only [NNReal.coe_mul]
  rw [NNReal.coe_sub (thickenedIndicator_le_one hδ _ x)]
  norm_num

private theorem softSublevelStep_lipschitz {E : Type*} [PseudoMetricSpace E]
    (L : E → ℝ≥0∞) (q : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    LipschitzWith (q * δ.toNNReal⁻¹)
      (fun x => (softSublevelStep L q δ hδ x).toReal) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [softSublevelStep_toReal, softSublevelStep_toReal, Real.dist_eq]
  have hi := (lipschitzWith_thickenedIndicator hδ
    {z | L z ≤ (q : ℝ≥0∞)}).dist_le_mul x y
  rw [show (q : ℝ) * (1 - (thickenedIndicator hδ
        {z | L z ≤ (q : ℝ≥0∞)} x : ℝ)) -
      (q : ℝ) * (1 - (thickenedIndicator hδ
        {z | L z ≤ (q : ℝ≥0∞)} y : ℝ)) =
      (q : ℝ) * ((thickenedIndicator hδ
        {z | L z ≤ (q : ℝ≥0∞)} y : ℝ) -
        (thickenedIndicator hδ
          {z | L z ≤ (q : ℝ≥0∞)} x : ℝ)) by ring,
    abs_mul, abs_sub_comm]
  norm_cast at hi
  calc
    |(q : ℝ)| *
        |↑((thickenedIndicator hδ {z | L z ≤ ↑q}) x) -
          ↑((thickenedIndicator hδ {z | L z ≤ ↑q}) y)|
        = (q : ℝ) *
          |↑((thickenedIndicator hδ {z | L z ≤ ↑q}) x) -
            ↑((thickenedIndicator hδ {z | L z ≤ ↑q}) y)| := by
            congr 1
            exact abs_of_nonneg q.2
    _ ≤ (q : ℝ) * (↑δ.toNNReal⁻¹ * dist x y) :=
      mul_le_mul_of_nonneg_left (by simpa [NNReal.dist_eq, Real.dist_eq,
        abs_sub_comm] using hi) q.2
    _ = ↑(q * δ.toNNReal⁻¹) * dist x y := by
      rw [NNReal.coe_mul]
      ring

private noncomputable def rationalThreshold (i : ℕ) : ℝ≥0 :=
  match Encodable.decode (α := ℚ) i with
  | some q => Real.toNNReal (q : ℝ)
  | none => 0

private noncomputable def smoothingRadius (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private theorem smoothingRadius_pos (n : ℕ) : 0 < smoothingRadius n := by
  exact one_div_pos.mpr (by positivity)

private theorem smoothingRadius_antitone : Antitone smoothingRadius := by
  intro n m hnm
  simp only [smoothingRadius, one_div]
  gcongr

private theorem smoothingRadius_tendsto :
    Tendsto smoothingRadius atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private noncomputable def bowlApprox {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (n : ℕ) : E → ℝ≥0∞ := fun x =>
  (Finset.range (n + 1)).sup fun i =>
    softSublevelStep L (rationalThreshold i) (smoothingRadius n)
      (smoothingRadius_pos n) x

private theorem softSublevelStep_mono_radius {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (q : ℝ≥0) {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (h : d₁ ≤ d₂) (x : E) :
    softSublevelStep L q d₂ hd₂ x ≤ softSublevelStep L q d₁ hd₁ x := by
  simp only [softSublevelStep]
  have hi := thickenedIndicator_mono hd₁ hd₂ h
    {y | L y ≤ (q : ℝ≥0∞)} x
  gcongr

private theorem softSublevelStep_le_loss {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (q : ℝ≥0) (d : ℝ) (hd : 0 < d) (x : E) :
    softSublevelStep L q d hd x ≤ L x := by
  by_cases hx : L x ≤ (q : ℝ≥0∞)
  · have hi : thickenedIndicator hd {y | L y ≤ (q : ℝ≥0∞)} x = 1 :=
      thickenedIndicator_one hd _ hx
    rw [softSublevelStep, hi]
    simp
  · have hstep : softSublevelStep L q d hd x ≤ (q : ℝ≥0∞) := by
      simp only [softSublevelStep, ENNReal.coe_le_coe]
      simpa using (mul_le_mul_right (tsub_le_self : 1 -
        thickenedIndicator hd {y | L y ≤ (q : ℝ≥0∞)} x ≤ 1) q)
    exact hstep.trans (le_of_lt (lt_of_not_ge hx))

private theorem bowlShaped_max {E : Type*} [MeasurableSpace E]
    [AddCommGroup E] [Module ℝ E]
    {f g : E → ℝ≥0∞} (hf : BowlShaped f) (hg : BowlShaped g) :
    BowlShaped (fun x => max (f x) (g x)) := by
  refine ⟨hf.measurable.sup hg.measurable, ?_, ?_⟩
  · intro x
    simp [hf.symm, hg.symm]
  · intro c x hx y hy a b ha hb hab
    change max (f x) (g x) ≤ c at hx
    change max (f y) (g y) ≤ c at hy
    change max (f (a • x + b • y)) (g (a • x + b • y)) ≤ c
    rw [max_le_iff] at hx hy ⊢
    exact ⟨hf.convex_sublevel c hx.1 hy.1 ha hb hab,
      hg.convex_sublevel c hx.2 hy.2 ha hb hab⟩

private theorem bowlShaped_finset_sup {E ι : Type*} [MeasurableSpace E]
    [AddCommGroup E] [Module ℝ E] (s : Finset ι) (f : ι → E → ℝ≥0∞)
    (hf : ∀ i ∈ s, BowlShaped (f i)) :
    BowlShaped (fun x => s.sup fun i => f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change BowlShaped (fun _ => 0)
      exact ⟨measurable_const, by simp, by
        intro c x hx y hy a b ha hb hab
        exact hx⟩
  | @insert i s hi ih =>
      simpa only [Finset.sup_insert] using
        (bowlShaped_max (hf i (Finset.mem_insert_self i s))
          (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem finset_sup_ne_top {E ι : Type*} [PseudoEMetricSpace E]
    (s : Finset ι) (f : ι → E → ℝ≥0∞)
    (hf : ∀ i ∈ s, ∀ x, f i x ≠ ∞) (x : E) :
    s.sup (fun i => f i x) ≠ ∞ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sup_insert]
      exact max_ne_top (hf i (Finset.mem_insert_self i s) x)
        (ih fun j hj y => hf j (Finset.mem_insert_of_mem hj) y)

private theorem finset_sup_lipschitz {E ι : Type*} [PseudoMetricSpace E]
    (s : Finset ι) (f : ι → E → ℝ≥0∞)
    (hfinite : ∀ i ∈ s, ∀ x, f i x ≠ ∞)
    (hlip : ∀ i ∈ s, ∃ K : ℝ≥0, LipschitzWith K (fun x => (f i x).toReal)) :
    ∃ K : ℝ≥0, LipschitzWith K
      (fun x => (s.sup fun i => f i x).toReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      change LipschitzWith 0 (fun _ : E => (0 : ℝ))
      exact LipschitzWith.const 0
  | @insert i s hi ih =>
      rcases hlip i (Finset.mem_insert_self i s) with ⟨Ki, hKi⟩
      rcases ih (fun j hj x => hfinite j (Finset.mem_insert_of_mem hj) x)
          (fun j hj => hlip j (Finset.mem_insert_of_mem hj)) with ⟨Ks, hKs⟩
      refine ⟨max Ki Ks, ?_⟩
      convert hKi.max hKs using 1
      funext x
      simp only [Finset.sup_insert]
      rw [ENNReal.toReal_sup (hfinite i (Finset.mem_insert_self i s) x)
        (finset_sup_ne_top s f
          (fun j hj y => hfinite j (Finset.mem_insert_of_mem hj) y) x)]

private theorem bowlApprox_bowl {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : E → ℝ≥0∞) (hL : BowlShaped L) (hL_lsc : LowerSemicontinuous L) (n : ℕ) :
    BowlShaped (bowlApprox L n) := by
  unfold bowlApprox
  exact bowlShaped_finset_sup _ _ fun i _ =>
    softSublevelStep_bowl L hL hL_lsc _ _ _

private theorem bowlApprox_ne_top {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (n : ℕ) (x : E) : bowlApprox L n x ≠ ∞ := by
  unfold bowlApprox
  apply finset_sup_ne_top
  intro i hi y
  unfold softSublevelStep
  exact ENNReal.coe_ne_top

private theorem bowlApprox_bounded {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (n : ℕ) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, bowlApprox L n x ≤ B := by
  let B : ℝ≥0∞ := ∑ i ∈ Finset.range (n + 1), (rationalThreshold i : ℝ≥0∞)
  refine ⟨B, ?_, ?_⟩
  · rw [ENNReal.sum_lt_top]
    intro i hi
    exact ENNReal.coe_lt_top
  · intro x
    unfold bowlApprox
    apply Finset.sup_le
    intro i hi
    have hstep : softSublevelStep L (rationalThreshold i) (smoothingRadius n)
        (smoothingRadius_pos n) x ≤ (rationalThreshold i : ℝ≥0∞) := by
      simp only [softSublevelStep, ENNReal.coe_le_coe]
      simpa using (mul_le_mul_right (tsub_le_self : 1 - thickenedIndicator
        (smoothingRadius_pos n) {y | L y ≤ (rationalThreshold i : ℝ≥0∞)} x ≤ 1)
        (rationalThreshold i))
    refine hstep.trans ?_
    change (rationalThreshold i : ℝ≥0∞) ≤
      ∑ j ∈ Finset.range (n + 1), (rationalThreshold j : ℝ≥0∞)
    exact Finset.single_le_sum
      (f := fun j => (rationalThreshold j : ℝ≥0∞)) (fun _ _ => zero_le) hi

private theorem bowlApprox_uniformContinuous {E : Type*} [PseudoMetricSpace E]
    (L : E → ℝ≥0∞) (n : ℕ) :
    UniformContinuous fun x => (bowlApprox L n x).toReal := by
  unfold bowlApprox
  rcases finset_sup_lipschitz (Finset.range (n + 1))
      (fun i => softSublevelStep L (rationalThreshold i) (smoothingRadius n)
        (smoothingRadius_pos n))
      (fun i hi x => by
        unfold softSublevelStep
        exact ENNReal.coe_ne_top)
      (fun i hi => ⟨_, softSublevelStep_lipschitz L _ _ _⟩) with ⟨K, hK⟩
  exact hK.uniformContinuous

private theorem bowlApprox_mono {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (x : E) : Monotone fun n => bowlApprox L n x := by
  intro n m hnm
  unfold bowlApprox
  apply Finset.sup_le
  intro i hi
  refine (softSublevelStep_mono_radius L (rationalThreshold i)
    (smoothingRadius_pos m) (smoothingRadius_pos n)
    (smoothingRadius_antitone hnm) x).trans ?_
  apply Finset.le_sup (s := Finset.range (m + 1))
    (f := fun j => softSublevelStep L (rationalThreshold j) (smoothingRadius m)
      (smoothingRadius_pos m) x)
  simp only [Finset.mem_range] at hi ⊢
  omega

private theorem bowlApprox_le_loss {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (n : ℕ) (x : E) : bowlApprox L n x ≤ L x := by
  unfold bowlApprox
  exact Finset.sup_le fun i hi => softSublevelStep_le_loss L _ _ _ x

private theorem rationalThreshold_encode (q : ℚ) :
    rationalThreshold (Encodable.encode q) = Real.toNNReal (q : ℝ) := by
  simp [rationalThreshold]

private theorem softSublevelStep_tendsto_threshold {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (q : ℝ≥0) (x : E)
    (hx : ¬ L x ≤ (q : ℝ≥0∞))
    (hclosed : IsClosed {y | L y ≤ (q : ℝ≥0∞)}) :
    Tendsto (fun n => softSublevelStep L q (smoothingRadius n)
      (smoothingRadius_pos n) x) atTop (nhds (q : ℝ≥0∞)) := by
  let S : Set E := {y | L y ≤ (q : ℝ≥0∞)}
  have hxS : x ∉ S := hx
  have hi := thickenedIndicator_tendsto_indicator_closure
    smoothingRadius_pos smoothingRadius_tendsto S
  rw [tendsto_pi_nhds] at hi
  have hi0 : Tendsto (fun n => thickenedIndicator (smoothingRadius_pos n) S x)
      atTop (nhds 0) := by
    simpa [hclosed.closure_eq, Set.indicator_of_notMem hxS] using hi x
  have hc : Continuous (fun t : ℝ≥0 => ((q * (1 - t) : ℝ≥0) : ℝ≥0∞)) := by
    fun_prop
  convert hc.continuousAt.tendsto.comp hi0 using 1
  · rfl
  · simp

private theorem iSup_bowlApprox_eq {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (hL_lsc : LowerSemicontinuous L) (x : E) :
    (⨆ n, bowlApprox L n x) = L x := by
  apply le_antisymm
  · exact iSup_le fun n => bowlApprox_le_loss L n x
  · apply le_of_forall_lt
    intro a ha
    rcases ENNReal.lt_iff_exists_rat_btwn.mp ha with ⟨q, hq0, haq, hqL⟩
    let q₀ : ℝ≥0 := Real.toNNReal (q : ℝ)
    have hxq : ¬ L x ≤ (q₀ : ℝ≥0∞) := not_le_of_gt hqL
    have hclosed : IsClosed {y | L y ≤ (q₀ : ℝ≥0∞)} :=
      hL_lsc.isClosed_preimage (q₀ : ℝ≥0∞)
    have ht := softSublevelStep_tendsto_threshold L q₀ x hxq hclosed
    have hev : ∀ᶠ n in atTop,
        a < softSublevelStep L q₀ (smoothingRadius n) (smoothingRadius_pos n) x :=
      ht.eventually (Ioi_mem_nhds haq)
    rcases (hev.and (eventually_ge_atTop (Encodable.encode q))).exists with ⟨n, han, hni⟩
    refine han.trans_le (le_iSup_of_le n ?_)
    unfold bowlApprox
    have hmem : Encodable.encode q ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      omega
    have hsup := Finset.le_sup
      (f := fun i => softSublevelStep L (rationalThreshold i) (smoothingRadius n)
        (smoothingRadius_pos n) x) hmem
    simpa [q₀, rationalThreshold_encode] using hsup

private theorem bowlApprox_tendsto {E : Type*} [PseudoEMetricSpace E]
    (L : E → ℝ≥0∞) (hL_lsc : LowerSemicontinuous L) (x : E) :
    Tendsto (fun n => bowlApprox L n x) atTop (nhds (L x)) := by
  rw [← iSup_bowlApprox_eq L hL_lsc x]
  exact tendsto_atTop_iSup (bowlApprox_mono L x)

private theorem bowlShaped_uc_approx_general {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : E → ℝ≥0∞) (hL : BowlShaped L) (hL_lsc : LowerSemicontinuous L) :
    ∃ Ln : ℕ → E → ℝ≥0∞,
      (∀ n, BowlShaped (Ln n)) ∧
      (∀ n x, Ln n x ≠ ∞) ∧
      (∀ n, ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, Ln n x ≤ B) ∧
      (∀ n, UniformContinuous fun x => (Ln n x).toReal) ∧
      (∀ x, Monotone fun n => Ln n x) ∧
      (∀ x, Tendsto (fun n => Ln n x) atTop (nhds (L x))) := by
  refine ⟨bowlApprox L, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bowlApprox_bowl L hL hL_lsc
  · exact bowlApprox_ne_top L
  · exact bowlApprox_bounded L
  · exact bowlApprox_uniformContinuous L
  · exact bowlApprox_mono L
  · exact bowlApprox_tendsto L hL_lsc

/-- Every lsc bowl-shaped scalar loss has an increasing bounded, finite,
uniformly-continuous bowl-shaped approximation. -/
theorem bowlShaped_uc_approx
    (ℓ : ℝ → ℝ≥0∞) (hbowl : BowlShaped ℓ)
    (hlsc : LowerSemicontinuous ℓ) :
    ∃ ℓn : ℕ → ℝ → ℝ≥0∞,
      (∀ n, BowlShaped (ℓn n)) ∧
      (∀ n x, ℓn n x ≠ ∞) ∧
      (∀ n, ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓn n x ≤ B) ∧
      (∀ n, UniformContinuous fun x => (ℓn n x).toReal) ∧
      (∀ x, Monotone fun n => ℓn n x) ∧
      (∀ x, Tendsto (fun n => ℓn n x) atTop (𝓝 (ℓ x))) :=
  bowlShaped_uc_approx_general ℓ hbowl hlsc

/-- Vector-valued version of the bounded uniformly-continuous bowl
approximation.  It includes the empty space (`d = 0`) and makes no
finite-valuedness assumption on the original loss.

Proof idea: truncate the lsc bowl by bounded sublevel gauges and regularize
radially; monotone convergence removes the approximation after the bounded-UC
Gaussian-cone argument. -/
theorem bowlShaped_uc_approx_vec {d : ℕ}
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (_hbowl : BowlShaped ℓ)
    (_hlsc : LowerSemicontinuous ℓ) :
    ∃ ℓn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      (∀ n, BowlShaped (ℓn n)) ∧
      (∀ n x, ℓn n x ≠ ∞) ∧
      (∀ n, ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓn n x ≤ B) ∧
      (∀ n, UniformContinuous fun x => (ℓn n x).toReal) ∧
      (∀ x, Monotone fun n => ℓn n x) ∧
      (∀ x, Tendsto (fun n => ℓn n x) atTop (𝓝 (ℓ x))) :=
  bowlShaped_uc_approx_general ℓ _hbowl _hlsc

end AsymptoticStatistics.LowerBounds.BowlShapedUCApprox
