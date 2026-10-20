module
public import StatLean.AsymptoticStatistics.ForMathlib.VaryingSetSupremum
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterTightness
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-!
# Outer weak convergence under argmax supremum mappings

Specialized portmanteau theorems for vdV Theorem 5.56 and Corollary 5.58.
These are not advertised as a general extended continuous-mapping theorem.
Comparisons are written additively in `EReal`, never as `∞ - ∞`.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- Binary subadditivity of the outer measure induced by outer expectation. -/
theorem outerMeasureStar_union_le_processMapping {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) :
    μ.outerMeasureStar (A ∪ B) ≤ μ.outerMeasureStar A + μ.outerMeasureStar B := by
  refine (outerExpectation_mono (μ := μ) fun ω => ?_).trans
    (outerExpectation_add_le (A.indicator 1) (B.indicator 1))
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

/-- Monotonicity of the outer measure induced by outer expectation. -/
theorem outerMeasureStar_mono_processMapping {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A B : Set Ω} (hAB : A ⊆ B) :
    μ.outerMeasureStar A ≤ μ.outerMeasureStar B := by
  exact outerExpectation_mono fun ω => by
    by_cases hA : ω ∈ A
    · simp [hA, hAB hA]
    · simp [hA]

/-- Finite upper-tail sums approximate a bounded nonnegative number from above. -/
private theorem tailStep_bounds (m : ℕ) {η x : ℝ} (hη : 0 < η)
    (hx : 0 ≤ x) (hxm : x ≤ m * η) :
    x ≤ (∑ k ∈ Finset.range (m + 1), if (k : ℝ) * η ≤ x then η else 0) ∧
      (∑ k ∈ Finset.range (m + 1), if (k : ℝ) * η ≤ x then η else 0) ≤ x + η := by
  let q := ⌊x / η⌋₊
  have hq : q ≤ m := by
    dsimp [q]
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hη]
    simpa [mul_comm] using hxm
  have hp (k : ℕ) : (k : ℝ) * η ≤ x ↔ k ≤ q := by
    rw [Nat.le_floor_iff (div_nonneg hx hη.le), le_div_iff₀ hη]
  have hfilt : (Finset.range (m + 1)).filter (fun k : ℕ => (k : ℝ) * η ≤ x) =
      Finset.range (q + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, hp]
    omega
  have hsum : (∑ k ∈ Finset.range (m + 1), if (k : ℝ) * η ≤ x then η else 0) =
      (q + 1 : ℕ) * η := by
    rw [← Finset.sum_filter, hfilt,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  constructor
  · have := Nat.lt_floor_add_one (x / η)
    rw [div_lt_iff₀ hη] at this
    simpa [mul_comm] using this.le
  · have hqx : (q : ℝ) ≤ x / η := by
      dsimp [q]
      exact Nat.floor_le (div_nonneg hx hη.le)
    have hqmul : (q : ℝ) * η ≤ x := (le_div_iff₀ hη).mp hqx
    push_cast
    linarith

private theorem outerExpectation_finset_sum_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (u : ι → Ω → ℝ≥0∞) :
    outerExpectation μ (∑ i ∈ s, u i) ≤ ∑ i ∈ s, outerExpectation μ (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change outerExpectation μ (fun _ => 0) ≤ 0
      rw [outerExpectation_const]
      simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (outerExpectation_add_le _ _).trans (add_le_add le_rfl ih)

/-- A real error tends to zero in outer probability on a fixed sample space.

Edge behavior: the exceedance event is read by `outerMeasureStar`, so neither
the error nor the event needs to be measurable. -/
def TendstoInOuterProbabilityZero {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (r : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => (μ n).outerMeasureStar {ω | ε ≤ |r n ω|}) atTop (𝓝 0)

/-- Outer weak convergence for an `EReal × EReal`-valued sequence, using a
metric that induces `EReal`'s existing order topology.

The local instance is transparent and changes no topology.  Consequently
finite values tending to either infinity converge to the appropriate endpoint;
empty (`⊥`) and unbounded (`⊤`) suprema retain their genuine semantics. -/
def WeakConvergesOuterERealPair
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (Xn : ℕ → Ω → EReal × EReal)
    (ν : Measure (EReal × EReal)) : Prop :=
  letI : MetricSpace EReal := TopologicalSpace.metrizableSpaceMetric EReal
  WeakConvergesOuter μ Xn ν

/-- The unconditional extended-real pair-supremum outer weak convergence
premise of vdV Theorem 5.56.  It packages only the book's process-convergence
assumption, never an argmax or closed-event conclusion.

Edge behavior: all closed `F` and all `K ∈ 𝒦` are covered, including empty and
unbounded intersections through `setSupEReal`. -/
def PairSupConvergesOuter
    {Ω Ωlim D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
    [TopologicalSpace D]
    (μ : ℕ → Measure Ω) (μlim : Measure Ωlim)
    (Mn : ℕ → Ω → D → ℝ) (M : Ωlim → D → ℝ)
    (Hn : ℕ → Set D) (H : Set D) (𝒦 : Set (Set D)) : Prop :=
  ∀ (F K : Set D), IsClosed F → K ∈ 𝒦 →
    WeakConvergesOuterERealPair μ (fun n ω =>
      (ForMathlib.setSupEReal (Mn n ω) (F ∩ K ∩ Hn n),
        ForMathlib.setSupEReal (Mn n ω) (K ∩ Hn n)))
      (μlim.map (fun ω =>
        (ForMathlib.setSupEReal (M ω) (F ∩ K ∩ H),
          ForMathlib.setSupEReal (M ω) (K ∩ H))))

/-- Measurability of the extended-real limit pair in `PairSupConvergesOuter`.
It asserts measurability only, with no convergence or argmax conclusion. -/
def PairSupLimitMeasurable
    {Ωlim D : Type*} [MeasurableSpace Ωlim] [TopologicalSpace D]
    (M : Ωlim → D → ℝ) (H : Set D) (𝒦 : Set (Set D)) : Prop :=
  ∀ (F K : Set D), IsClosed F → K ∈ 𝒦 →
    Measurable (fun ω =>
      (ForMathlib.setSupEReal (M ω) (F ∩ K ∩ H),
        ForMathlib.setSupEReal (M ω) (K ∩ H)))

/-- Closed-set outer portmanteau sufficiency for a probability limit.

The closed-event limsup inequality implies outer weak convergence. -/
theorem weakConvergesOuter_of_closedSet_limsup {Ω D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace D] [PseudoMetricSpace D]
    [OpensMeasurableSpace D]
    {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)]
    {Xn : ℕ → Ω → D} {ν : Measure D} [IsProbabilityMeasure ν]
    (hclosed : ∀ F : Set D, IsClosed F →
      limsup (fun n => (μ n).outerMeasureStar (Xn n ⁻¹' F)) atTop ≤ ν F) :
    WeakConvergesOuter μ Xn ν := by
  classical
  intro f
  let R : BoundedContinuousFunction D ℝ → ℕ → ℝ := fun q n =>
    (outerExpectation (μ n) (fun ω => ENNReal.ofReal (q (Xn n ω) + ‖q‖))).toReal - ‖q‖
  have hupper (q : BoundedContinuousFunction D ℝ) : ∀ ε > 0,
      ∀ᶠ n in atTop, R q n ≤ (∫ x, q x ∂ν) + ε := by
    intro ε hε
    let η := min (ε / 8) 1
    have hη : 0 < η := lt_min (by linarith) zero_lt_one
    have hη1 : η ≤ 1 := min_le_right _ _
    have hηε : 2 * η < ε := by
      have := min_le_left (ε / 8) 1
      linarith
    let m := ⌈(2 * ‖q‖) / η⌉₊
    let g : D → ℝ := fun x => q x + ‖q‖
    let C : ℕ → Set D := fun k => {x | (k : ℝ) * η ≤ g x}
    have hg0 (x : D) : 0 ≤ g x := by
      have := (abs_le.1 (q.norm_coe_le_norm x)).1
      dsimp [g]
      linarith
    have hg2 (x : D) : g x ≤ 2 * ‖q‖ := by
      have := (abs_le.1 (q.norm_coe_le_norm x)).2
      dsimp [g]
      linarith
    have hm : 2 * ‖q‖ ≤ m * η := by
      have := Nat.le_ceil ((2 * ‖q‖) / η)
      rw [div_le_iff₀ hη] at this
      simpa [m, mul_comm] using this
    have hC (k : ℕ) : IsClosed (C k) := by
      exact isClosed_le continuous_const (q.continuous.add continuous_const)
    let c : ℝ≥0∞ := ENNReal.ofReal η
    let ζ : ℝ := η / (m + 1)
    have hζ : 0 < ζ := by positivity
    have hev : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (m + 1),
        (μ n).outerMeasureStar (Xn n ⁻¹' C k) ≤ ν (C k) + ENNReal.ofReal ζ := by
      rw [Finset.eventually_all]
      intro k _
      exact (eventually_lt_of_limsup_lt <| (hclosed (C k) (hC k)).trans_lt <|
        ENNReal.lt_add_right (measure_ne_top ν _) (ENNReal.ofReal_pos.2 hζ).ne').mono
          fun _ hn => hn.le
    filter_upwards [hev] with n hn
    let u : ℕ → Ω → ℝ≥0∞ := fun k => (Xn n ⁻¹' C k).indicator (fun _ => c)
    have hmaj : (fun ω => ENNReal.ofReal (g (Xn n ω))) ≤
        ∑ k ∈ Finset.range (m + 1), u k := by
      intro ω
      have hs := (tailStep_bounds m (x := g (Xn n ω)) hη (hg0 _) ((hg2 _).trans hm)).1
      refine (ENNReal.ofReal_le_ofReal hs).trans_eq ?_
      rw [ENNReal.ofReal_sum_of_nonneg]
      · simp only [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkx : (k : ℝ) * η ≤ g (Xn n ω) <;>
          simp [u, C, c, hkx]
      · intro k hk
        split_ifs <;> positivity
    have hterm (k : ℕ) : outerExpectation (μ n) (u k) =
        c * (μ n).outerMeasureStar (Xn n ⁻¹' C k) := by
      have hu : u k = c • (Xn n ⁻¹' C k).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        by_cases hω : ω ∈ Xn n ⁻¹' C k <;> simp [u, hω]
      rw [hu, outerExpectation_const_smul c ENNReal.ofReal_ne_top, smul_eq_mul]
      rfl
    have houter : outerExpectation (μ n) (fun ω => ENNReal.ofReal (g (Xn n ω))) ≤
        ∑ k ∈ Finset.range (m + 1), c * (ν (C k) + ENNReal.ofReal ζ) := by
      exact (outerExpectation_mono hmaj).trans <|
        (outerExpectation_finset_sum_le (μ n) _ u).trans <| by
          gcongr with k hk
          rw [hterm]
          simpa only [mul_comm] using mul_le_mul_left (hn k hk) c
    let v : ℕ → D → ℝ≥0∞ := fun k => (C k).indicator (fun _ => c)
    have hlimstep : (∑ k ∈ Finset.range (m + 1), c * ν (C k)) ≤
        ∫⁻ x, ENNReal.ofReal (g x + η) ∂ν := by
      have heqint : (∫⁻ x, ∑ k ∈ Finset.range (m + 1), v k x ∂ν) =
          ∑ k ∈ Finset.range (m + 1), c * ν (C k) := by
        rw [lintegral_finset_sum (Finset.range (m + 1))]
        · apply Finset.sum_congr rfl
          intro k hk
          simp [v, lintegral_indicator, (hC k).measurableSet, c]
        · intro k hk
          exact measurable_const.indicator (hC k).measurableSet
      rw [← heqint]
      apply lintegral_mono
      intro x
      have hs := (tailStep_bounds m (x := g x) hη (hg0 x) ((hg2 x).trans hm)).2
      calc
        (∑ k ∈ Finset.range (m + 1), v k x) =
            ENNReal.ofReal
              (∑ k ∈ Finset.range (m + 1), if (k : ℝ) * η ≤ g x then η else 0) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro k hk
            by_cases hkx : (k : ℝ) * η ≤ g x <;>
              simp [v, C, c, hkx]
          · intro k hk
            split_ifs <;> positivity
        _ ≤ ENNReal.ofReal (g x + η) := ENNReal.ofReal_le_ofReal hs
    have herr : (∑ _k ∈ Finset.range (m + 1), c * ENNReal.ofReal ζ) ≤
        ENNReal.ofReal η := by
      have hrealerr : ((m + 1 : ℕ) : ℝ) * (η * ζ) ≤ η := by
        dsimp [ζ]
        push_cast
        field_simp
        nlinarith [hη1]
      calc
        (∑ _k ∈ Finset.range (m + 1), c * ENNReal.ofReal ζ) =
            ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * (η * ζ)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, c]
          rw [← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hrealerr
    have hE : outerExpectation (μ n) (fun ω => ENNReal.ofReal (g (Xn n ω))) ≤
        (∫⁻ x, ENNReal.ofReal (g x + η) ∂ν) + ENNReal.ofReal η := by
      exact houter.trans <| by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        exact add_le_add hlimstep herr
    have hgηint : Integrable (fun x => g x + η) ν := by
      simpa [g, add_assoc] using (q.integrable ν).add (integrable_const (‖q‖ + η))
    have hlin : (∫⁻ x, ENNReal.ofReal (g x + η) ∂ν) =
        ENNReal.ofReal (∫ x, g x + η ∂ν) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hgηint]
      exact Eventually.of_forall fun x => add_nonneg (hg0 x) hη.le
    have htop : (∫⁻ x, ENNReal.ofReal (g x + η) ∂ν) + ENNReal.ofReal η ≠ ⊤ := by
      rw [hlin]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    have hreal := ENNReal.toReal_mono htop hE
    rw [ENNReal.toReal_add (by rw [hlin]; exact ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top,
      hlin, ENNReal.toReal_ofReal (integral_nonneg (fun x =>
        add_nonneg (hg0 x) hη.le)), ENNReal.toReal_ofReal hη.le] at hreal
    have hconstint : (∫ x, g x + η ∂ν) = (∫ x, q x ∂ν) + ‖q‖ + η := by
      rw [show (fun x => g x + η) = fun x => q x + (‖q‖ + η) by
        funext x; simp [g, add_assoc]]
      rw [integral_add (q.integrable ν) (integrable_const _), integral_const]
      simp
      ring
    rw [hconstint] at hreal
    dsimp [g] at hreal
    dsimp [R, g]
    linarith
  have hsum_nonneg (n : ℕ) : 0 ≤ R f n + R (-f) n := by
    dsimp [R]
    have hs := outerExpectation_add_le (μ := μ n)
      (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))
      (fun ω => ENNReal.ofReal ((-f) (Xn n ω) + ‖-f‖))
    have heq : (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖) +
        ENNReal.ofReal ((-f) (Xn n ω) + ‖-f‖)) = fun _ => ENNReal.ofReal (2 * ‖f‖) := by
      funext ω
      rw [← ENNReal.ofReal_add (by
        have := (abs_le.1 (f.norm_coe_le_norm (Xn n ω))).1; linarith) (by
        have := (abs_le.1 ((-f).norm_coe_le_norm (Xn n ω))).1; linarith)]
      congr 1
      simp
      ring
    change outerExpectation (μ n) (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖) +
      ENNReal.ofReal ((-f) (Xn n ω) + ‖-f‖)) ≤ _ at hs
    rw [heq, outerExpectation_const] at hs
    simp only [measure_univ, mul_one] at hs
    have hAtop : outerExpectation (μ n)
        (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * ‖f‖)) ENNReal.ofReal_ne_top ?_
      calc
        outerExpectation (μ n) (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖)) ≤
            outerExpectation (μ n) (fun _ => ENNReal.ofReal (2 * ‖f‖)) :=
          outerExpectation_mono fun ω => ENNReal.ofReal_le_ofReal (by
            have := (abs_le.1 (f.norm_coe_le_norm (Xn n ω))).2; linarith)
        _ = ENNReal.ofReal (2 * ‖f‖) := by rw [outerExpectation_const]; simp
    have hBtop : outerExpectation (μ n)
        (fun ω => ENNReal.ofReal ((-f) (Xn n ω) + ‖-f‖)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * ‖-f‖)) ENNReal.ofReal_ne_top ?_
      calc
        outerExpectation (μ n) (fun ω => ENNReal.ofReal ((-f) (Xn n ω) + ‖-f‖)) ≤
            outerExpectation (μ n) (fun _ => ENNReal.ofReal (2 * ‖-f‖)) :=
          outerExpectation_mono fun ω => ENNReal.ofReal_le_ofReal (by
            have := (abs_le.1 ((-f).norm_coe_le_norm (Xn n ω))).2; linarith)
        _ = ENNReal.ofReal (2 * ‖-f‖) := by rw [outerExpectation_const]; simp
    have htop := ENNReal.add_ne_top.2 ⟨hAtop, hBtop⟩
    have htoreal := ENNReal.toReal_mono htop hs
    rw [ENNReal.toReal_add hAtop hBtop,
      ENNReal.toReal_ofReal (by positivity)] at htoreal
    rw [norm_neg]
    have hlower : 2 * ‖f‖ ≤
        (outerExpectation (μ n) (fun ω => ENNReal.ofReal (f (Xn n ω) + ‖f‖))).toReal +
        (outerExpectation (μ n) (fun ω => ENNReal.ofReal (-f (Xn n ω) + ‖f‖))).toReal := by
      simpa only [norm_neg] using! htoreal
    linarith
  have hRtend : Tendsto (R f) atTop (𝓝 (∫ x, f x ∂ν)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    apply eventually_atTop.1
    filter_upwards [hupper f (ε / 2) (half_pos hε), hupper (-f) (ε / 2) (half_pos hε)]
      with n hfp hfm
    rw [Real.dist_eq, abs_lt]
    have hintneg : (∫ x, (-f) x ∂ν) = -(∫ x, f x ∂ν) := integral_neg _
    rw [hintneg] at hfm
    constructor <;> linarith [hsum_nonneg n]
  simpa [R] using hRtend

/-- Specialized varying-closed-event comparison used in Theorem 5.56.

If the pair `(sup_F Mₙ, sup_K Mₙ)` converges outer weakly and the nonnegative
near-maximizer error tends to zero in outer probability, then the limsup of
`sup_K Mₙ ≤ error + sup_F Mₙ` is bounded by the corresponding zero-error limit
event.  The additive `EReal` relation remains meaningful for empty (`⊥`) and
unbounded (`⊤`) suprema and avoids `∞ - ∞`.

`hpairLimMeas` makes the displayed limit law a legal pushforward;
vdV's limit pair is a random element, so this adds no mathematical regularity. -/
theorem outer_supComparison_limsup_of_pair_weakConvergence
    {Ω Ωlim : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
    {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)]
    {μlim : Measure Ωlim} [IsProbabilityMeasure μlim]
    (pairn : ℕ → Ω → EReal × EReal) (pairLim : Ωlim → EReal × EReal)
    (hpairLimMeas : Measurable pairLim)
    (hpair : WeakConvergesOuterERealPair μ pairn (μlim.map pairLim))
    (r : ℕ → Ω → ℝ) (hrnonneg : ∀ n ω, 0 ≤ r n ω)
    (hr : TendstoInOuterProbabilityZero μ r) :
    limsup (fun n => (μ n).outerMeasureStar
        {ω | (pairn n ω).2 ≤ (r n ω : EReal) + (pairn n ω).1}) atTop
      ≤ μlim {ω | (pairLim ω).2 ≤ (pairLim ω).1} := by
  letI : MetricSpace EReal := TopologicalSpace.metrizableSpaceMetric EReal
  change WeakConvergesOuter μ pairn (μlim.map pairLim) at hpair
  have hshift_mono {a b : ℝ} (hab : a ≤ b) (x : EReal) :
      (a : EReal) + x ≤ (b : EReal) + x := by
    induction x with
    | bot => simp
    | coe x => norm_cast; linarith
    | top => simp
  let d : ℕ → ℝ := fun k => 1 / (k + 1)
  let C : ℝ → Set (EReal × EReal) := fun δ => {p | p.2 ≤ (δ : EReal) + p.1}
  have hCclosed (δ : ℝ) : IsClosed (C δ) := by
    apply isClosed_le continuous_snd
    rw [continuous_iff_continuousAt]
    intro p
    exact (EReal.continuousAt_add (.inl (EReal.coe_ne_top δ))
      (.inl (EReal.coe_ne_bot δ))).comp
      (continuous_const.prodMk continuous_fst).continuousAt
  have hfixed (δ : ℝ) (hδ : 0 < δ) :
      limsup (fun n => (μ n).outerMeasureStar
          {ω | (pairn n ω).2 ≤ (r n ω : EReal) + (pairn n ω).1}) atTop
        ≤ μlim (pairLim ⁻¹' C δ) := by
    have hsub : ∀ n, {ω | (pairn n ω).2 ≤ (r n ω : EReal) + (pairn n ω).1} ⊆
        {ω | δ ≤ |r n ω|} ∪ pairn n ⁻¹' C δ := by
      intro n ω hω
      by_cases hbad : δ ≤ |r n ω|
      · exact Or.inl hbad
      · right
        have hrδ : r n ω ≤ δ := by
          rw [abs_of_nonneg (hrnonneg n ω)] at hbad
          exact (le_of_lt (lt_of_not_ge hbad))
        exact hω.trans (hshift_mono hrδ _)
    have hbad0 := hr δ hδ
    have hgood := limsup_outerMeasureStar_preimage_isClosed_le hpair (hCclosed δ)
    calc
      limsup (fun n => (μ n).outerMeasureStar
          {ω | (pairn n ω).2 ≤ (r n ω : EReal) + (pairn n ω).1}) atTop
          ≤ limsup (fun n => (μ n).outerMeasureStar {ω | δ ≤ |r n ω|} +
              (μ n).outerMeasureStar (pairn n ⁻¹' C δ)) atTop :=
        limsup_le_limsup (Eventually.of_forall fun n =>
          (outerMeasureStar_mono_processMapping (μ n) (hsub n)).trans
            (outerMeasureStar_union_le_processMapping (μ n) _ _))
      _ = limsup (fun n => (μ n).outerMeasureStar (pairn n ⁻¹' C δ)) atTop :=
        ENNReal.limsup_add_of_left_tendsto_zero hbad0 _
      _ ≤ (μlim.map pairLim) (C δ) := hgood
      _ = μlim (pairLim ⁻¹' C δ) := by
        rw [Measure.map_apply hpairLimMeas (hCclosed δ).measurableSet]
  have hdpos : ∀ k, 0 < d k := fun k => by
    dsimp [d]
    positivity
  let S : ℕ → Set Ωlim := fun k => pairLim ⁻¹' C (d k)
  have hSmeas : ∀ k, MeasurableSet (S k) := fun k =>
    hpairLimMeas (hCclosed (d k)).measurableSet
  have hSanti : Antitone S := by
    apply antitone_nat_of_succ_le
    intro k ω hω
    have hdk : d (k + 1) ≤ d k := by
      dsimp [d]
      gcongr
      omega
    exact hω.trans (hshift_mono hdk _)
  have hSint : (⋂ k, S k) = {ω | (pairLim ω).2 ≤ (pairLim ω).1} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h
      have hdlim : Tendsto d atTop (𝓝 0) := by
        simpa [d] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have haddlim : Tendsto (fun k => (d k : EReal) + (pairLim ω).1) atTop
          (𝓝 (pairLim ω).1) := by
        have hcoe : Tendsto (fun k => (d k : EReal)) atTop (𝓝 (0 : EReal)) :=
          EReal.tendsto_coe.mpr hdlim
        simpa using! (EReal.continuousAt_add (.inl (EReal.coe_ne_top 0))
          (.inl (EReal.coe_ne_bot 0))).tendsto.comp
            (hcoe.prodMk_nhds tendsto_const_nhds)
      exact ge_of_tendsto haddlim (Eventually.of_forall h)
    · intro h k
      exact h.trans (by
        simpa only [EReal.coe_zero, zero_add] using hshift_mono (hdpos k).le (pairLim ω).1)
  have hSmeasure : Tendsto (fun k => μlim (S k)) atTop
      (𝓝 (μlim {ω | (pairLim ω).2 ≤ (pairLim ω).1})) := by
    rw [← hSint]
    exact tendsto_measure_iInter_atTop (fun k => (hSmeas k).nullMeasurableSet)
      hSanti ⟨0, measure_ne_top _ _⟩
  exact ge_of_tendsto hSmeasure (Eventually.of_forall fun k => hfixed (d k) (hdpos k))

/-- The varying-map comparison in Corollary 5.58.

Local outer weak convergence in `ℓ∞(K)`, convergence `Hₙ → H`, and the
deterministic varying-set sandwich imply the one-sided outer comparison. `F`
is compact and `K` is a compact localization
set; the limit comparison uses `interior K`, exactly as in the refined proof on
vdV p.81.  No joint-pair convergence is assumed (and it may fail when `Hₙ`
changes).

`hZmeas` gives the displayed pushforward law, while `hZcontinuous` states that
the limit law is concentrated on the continuous paths required by the
varying-set sandwich. -/
theorem outer_supComparison_limsup_of_local_linf
    {Ω Ωlim D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
    [MetricSpace D]
    {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)]
    {μlim : Measure Ωlim} [IsProbabilityMeasure μlim]
    {Hn : ℕ → Set D} {H F K : Set D}
    (hset : ForMathlib.SetConverges Hn H)
    (hFcompact : IsCompact F) (hKcompact : IsCompact K) (hFK : F ⊆ K)
    (Zn : ℕ → Ω → ForMathlib.LinfOn K)
    (Z : Ωlim → ForMathlib.LinfOn K) (hZmeas : Measurable Z)
    (hZ : WeakConvergesOuter μ Zn (μlim.map Z))
    (hZcontinuous : ∀ᵐ ω ∂μlim, Continuous (Z ω))
    (r : ℕ → Ω → ℝ) (hrnonneg : ∀ n ω, 0 ≤ r n ω)
    (hr : TendstoInOuterProbabilityZero μ r) :
    limsup (fun n => (μ n).outerMeasureStar {ω |
        ForMathlib.linfSetSup (Zn n ω) (K ∩ Hn n)
          ≤ (r n ω : EReal) +
            ForMathlib.linfSetSup (Zn n ω) (F ∩ Hn n)}) atTop
      ≤ μlim {ω |
        ForMathlib.linfSetSup (Z ω) (interior K ∩ H)
          ≤ ForMathlib.linfSetSup (Z ω) (F ∩ H)} := by
  classical
  let d : ℕ → ℝ := fun k => 1 / (k + 1)
  let A : ℕ → ℝ → Set (ForMathlib.LinfOn K) := fun n δ => {z |
    ForMathlib.linfSetSup z (K ∩ Hn n) ≤
      (δ : EReal) + ForMathlib.linfSetSup z (F ∩ Hn n)}
  let U : ℕ → Set (ForMathlib.LinfOn K) := fun k =>
    ⋃ n : ℕ, ⋃ (_h : k ≤ n), A n (d k)
  let W : ℕ → Set (ForMathlib.LinfOn K) := fun k => closure (U k)
  have hdpos (k : ℕ) : 0 < d k := by
    dsimp [d]
    positivity
  have hdanti : Antitone d := by
    apply antitone_nat_of_succ_le
    intro k
    dsimp [d]
    gcongr
    omega
  have hshift_mono {a b : ℝ} (hab : a ≤ b) (x : EReal) :
      (a : EReal) + x ≤ (b : EReal) + x := by
    induction x with
    | bot => simp
    | coe x => norm_cast; linarith
    | top => simp
  have hWanti : Antitone W := by
    apply antitone_nat_of_succ_le
    intro k
    apply closure_mono
    intro z hz
    change z ∈ ⋃ n : ℕ, ⋃ (_h : k + 1 ≤ n), A n (d (k + 1)) at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨n, hkn, hzn⟩ := hz
    change z ∈ ⋃ n : ℕ, ⋃ (_h : k ≤ n), A n (d k)
    simp only [Set.mem_iUnion]
    refine ⟨n, hkn.trans' (Nat.le_succ k), ?_⟩
    exact hzn.trans (hshift_mono (hdanti (Nat.le_succ k)) _)
  have hWclosed (k : ℕ) : IsClosed (W k) := isClosed_closure
  have hA_subset_W {k n : ℕ} (hkn : k ≤ n) : A n (d k) ⊆ W k := by
    intro z hz
    apply subset_closure
    change z ∈ ⋃ n : ℕ, ⋃ (_h : k ≤ n), A n (d k)
    simp only [Set.mem_iUnion]
    exact ⟨n, hkn, hz⟩
  have htail (k : ℕ) :
      limsup (fun n => (μ n).outerMeasureStar {ω |
          ForMathlib.linfSetSup (Zn n ω) (K ∩ Hn n) ≤
            (r n ω : EReal) + ForMathlib.linfSetSup (Zn n ω) (F ∩ Hn n)}) atTop
        ≤ (μlim.map Z) (W k) := by
    have hsub : ∀ᶠ n in atTop, {ω |
        ForMathlib.linfSetSup (Zn n ω) (K ∩ Hn n) ≤
          (r n ω : EReal) + ForMathlib.linfSetSup (Zn n ω) (F ∩ Hn n)} ⊆
        {ω | d k ≤ |r n ω|} ∪ Zn n ⁻¹' W k := by
      filter_upwards [eventually_ge_atTop k] with n hkn
      intro ω hω
      by_cases hbad : d k ≤ |r n ω|
      · exact Or.inl hbad
      · right
        apply hA_subset_W hkn
        have hrδ : r n ω ≤ d k := by
          rw [abs_of_nonneg (hrnonneg n ω)] at hbad
          exact le_of_lt (lt_of_not_ge hbad)
        exact hω.trans (hshift_mono hrδ _)
    have hbad0 := hr (d k) (hdpos k)
    have hgood := limsup_outerMeasureStar_preimage_isClosed_le hZ (hWclosed k)
    calc
      limsup (fun n => (μ n).outerMeasureStar {ω |
          ForMathlib.linfSetSup (Zn n ω) (K ∩ Hn n) ≤
            (r n ω : EReal) + ForMathlib.linfSetSup (Zn n ω) (F ∩ Hn n)}) atTop
          ≤ limsup (fun n => (μ n).outerMeasureStar {ω | d k ≤ |r n ω|} +
              (μ n).outerMeasureStar (Zn n ⁻¹' W k)) atTop :=
        limsup_le_limsup (hsub.mono fun n hn =>
          (outerMeasureStar_mono_processMapping (μ n) hn).trans
            (outerMeasureStar_union_le_processMapping (μ n) _ _))
      _ = limsup (fun n => (μ n).outerMeasureStar (Zn n ⁻¹' W k)) atTop :=
        ENNReal.limsup_add_of_left_tendsto_zero hbad0 _
      _ ≤ (μlim.map Z) (W k) := hgood
  let S : ℕ → Set Ωlim := fun k => Z ⁻¹' W k
  have hSmeas (k : ℕ) : MeasurableSet (S k) :=
    hZmeas (hWclosed k).measurableSet
  have hSanti : Antitone S := fun _ _ hkl => preimage_mono (hWanti hkl)
  have hSmeasure : Tendsto (fun k => μlim (S k)) atTop (𝓝 (μlim (⋂ k, S k))) :=
    tendsto_measure_iInter_atTop (fun k => (hSmeas k).nullMeasurableSet)
      hSanti ⟨0, measure_ne_top _ _⟩
  have hprob_inter :
      limsup (fun n => (μ n).outerMeasureStar {ω |
          ForMathlib.linfSetSup (Zn n ω) (K ∩ Hn n) ≤
            (r n ω : EReal) + ForMathlib.linfSetSup (Zn n ω) (F ∩ Hn n)}) atTop
        ≤ μlim (⋂ k, S k) := by
    apply ge_of_tendsto hSmeasure
    filter_upwards with k
    rw [show μlim (S k) = (μlim.map Z) (W k) by
      rw [Measure.map_apply hZmeas (hWclosed k).measurableSet]]
    exact htail k
  have hd0 : Tendsto d atTop (𝓝 0) := by
    simpa [d] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdet (z : ForMathlib.LinfOn K) (hzcont : Continuous z)
      (hzW : z ∈ ⋂ k, W k) :
      ForMathlib.linfSetSup z (interior K ∩ H) ≤
        ForMathlib.linfSetSup z (F ∩ H) := by
    have hex (k : ℕ) : ∃ n : ℕ, ∃ hkn : k ≤ n,
        ∃ w : ForMathlib.LinfOn K, w ∈ A n (d k) ∧ dist w z < d k := by
      have hzclos : z ∈ closure (U k) := by
        simpa [W] using Set.mem_iInter.mp hzW k
      obtain ⟨w, hwU, hdist⟩ := Metric.mem_closure_iff.mp hzclos (d k) (hdpos k)
      change w ∈ ⋃ n : ℕ, ⋃ (_h : k ≤ n), A n (d k) at hwU
      simp only [Set.mem_iUnion] at hwU
      obtain ⟨n, hkn, hwn⟩ := hwU
      exact ⟨n, hkn, w, hwn, by simpa [dist_comm] using hdist⟩
    choose φ hφge w hwA hdist using hex
    obtain ⟨θ, hθmono, hφθmono⟩ := Filter.strictMono_subseq_of_id_le hφge
    have hwlim : Tendsto w atTop (𝓝 z) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      apply eventually_atTop.1
      filter_upwards [hd0 (eventually_lt_nhds hε)] with k hk
      exact (hdist k).trans hk
    have hwθlim : Tendsto (fun j => w (θ j)) atTop (𝓝 z) :=
      hwlim.comp hθmono.tendsto_atTop
    have hsetsub : ForMathlib.SetConverges (fun j => Hn ((φ ∘ θ) j)) H :=
      hset.subsequence hφθmono
    have hKclosure : closure K = K := hKcompact.isClosed.closure_eq
    have hFclosure : closure F = F := hFcompact.isClosed.closure_eq
    have hden := ForMathlib.varyingSetSupremum_sandwich
      (Hn := fun j => Hn ((φ ∘ θ) j)) (H := H) (B := K) (K := K)
      hsetsub (by simpa [hKclosure] using hKcompact)
      (by simp [hKclosure]) hwθlim hzcont
    have hnum := ForMathlib.varyingSetSupremum_sandwich
      (Hn := fun j => Hn ((φ ∘ θ) j)) (H := H) (B := F) (K := K)
      hsetsub (by simpa [hFclosure] using hFcompact)
      (by simpa [hFclosure] using hFK) hwθlim hzcont
    let a : ℕ → EReal := fun j =>
      ForMathlib.linfSetSup (w (θ j)) (K ∩ Hn ((φ ∘ θ) j))
    let b : ℕ → EReal := fun j =>
      ForMathlib.linfSetSup (w (θ j)) (F ∩ Hn ((φ ∘ θ) j))
    have hab (j : ℕ) : a j ≤ (d (θ j) : EReal) + b j := by
      simpa [a, b, Function.comp_def, A] using hwA (θ j)
    have hdθE : Tendsto (fun j => (d (θ j) : EReal)) atTop (𝓝 (0 : EReal)) :=
      EReal.tendsto_coe.mpr (hd0.comp hθmono.tendsto_atTop)
    have haddlimsup :
        limsup (fun j => (d (θ j) : EReal) + b j) atTop ≤ limsup b atTop := by
      have hadd := EReal.limsup_add_le
        (u := fun j => (d (θ j) : EReal)) (v := b) (f := atTop)
        (.inl (by rw [hdθE.limsup_eq]; exact EReal.coe_ne_bot 0))
        (.inl (by rw [hdθE.limsup_eq]; exact EReal.coe_ne_top 0))
      rw [hdθE.limsup_eq, zero_add] at hadd
      simpa only [Pi.add_apply] using! hadd
    calc
      ForMathlib.linfSetSup z (interior K ∩ H) ≤ liminf a atTop := hden.1
      _ ≤ limsup a atTop := hden.2.1
      _ ≤ limsup (fun j => (d (θ j) : EReal) + b j) atTop :=
        limsup_le_limsup (Eventually.of_forall hab)
      _ ≤ limsup b atTop := haddlimsup
      _ ≤ ForMathlib.linfSetSup z (F ∩ H) := by
        simpa [b, hFclosure] using hnum.2.2
  refine hprob_inter.trans (measure_mono_ae ?_)
  filter_upwards [hZcontinuous] with ω hωcont hω
  apply hdet (Z ω) hωcont
  apply Set.mem_iInter.mpr
  intro k
  simpa [S] using Set.mem_iInter.mp hω k

end AsymptoticStatistics
