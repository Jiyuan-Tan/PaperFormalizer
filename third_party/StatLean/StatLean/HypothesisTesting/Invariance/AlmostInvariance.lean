module
public import StatLean.HypothesisTesting.Invariance.Defs
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

@[expose] public section

/-!
# Almost invariance and its equivalence with invariance

A test is **almost invariant** when, for each group element separately, it is unchanged
along the action off a null set — the exceptional set being allowed to depend on the group
element. This is strictly weaker than invariance in general, and it is the class that
naturally appears when invariance is compared with unbiasedness or reached through a
sufficiency reduction.

The central result says that under two structural conditions the two notions coincide up
to a null set:

* **joint measurability** of the action, i.e. for every measurable `A` the set of pairs
  `(x, g)` with `g·x ∈ A` is product-measurable;
* the existence of a **σ-finite measure `ν` on the group whose null sets are stable under
  right translation**, `ν(B) = 0 ⟹ ν(Bg) = 0`.

Then every measurable almost-invariant function agrees, off a null set for the σ-finite
reference measure to which "almost" refers, with a genuinely invariant function. The
mechanism is a Fubini argument on the product of sample space and group followed by
averaging over the group: the average `ψ(x) = ∫ φ(g·x) dν(g)` is invariant on the
(invariant) set where it is defined, and equals `φ` off a null set.

The right-translation condition holds in particular for a **right-invariant** measure,
whose existence is guaranteed for a large class of groups by Haar theory, but the weaker
null-set form is what the proof needs and is often easy to check directly.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.5
(Almost Invariance), Theorem 6.5.1 (conditions under which an almost invariant test is
equivalent to an invariant one) and Corollary 6.5.1. (`TSH4 §6.5 Thm 6.5.1, Cor 6.5.1`.)

**Main results.**
* `exists_invariant_ae_eq_of_almostInvariant` — almost invariant ⟹ equal a.e. to invariant;
* `IsUMPAlmostInvariant` — UMP within the class of almost-invariant tests;
* `isUMPAlmostInvariant_of_isUMPInvariant` — a UMP invariant test is UMP among almost
  invariant tests.

**Proof formalization notes.**
* The joint-measurability condition is carried by `[MeasurableSMul₂ G 𝓧]`, which asserts
  measurability of `(g, x) ↦ g·x` on the product. This is the same content as the
  product-measurability of `{(x, g) : g·x ∈ A}` for every measurable `A`, up to the swap
  of factors.
* The right-translation null condition is written with preimages, `B·g = (· * g⁻¹) ⁻¹' B`,
  so that measurability of the translate is automatic; `MeasurableMul G` makes the
  translation map measurable.
* The conclusion is an a.e. statement **for the σ-finite measure `μ` to which almost
  invariance refers**, matching the source: the exceptional set is `μ`-null. The reading
  "null for the whole family `P`" is recovered by taking `μ` equivalent to the family,
  which is how the corollary below is set up.
* Non-degeneracy `ν ≠ 0` is stated explicitly. The averaging step normalizes `ν` to a
  probability measure, which is impossible for the zero measure; the source leaves this
  implicit in "there exists a σ-finite measure `ν` over `G`".
* The normalization is carried out inside the proof: a σ-finite `ν` carries an
  everywhere-positive integrable density (`exists_pos_lintegral_lt_of_sigmaFinite`), so it is
  equivalent to a *finite* measure `ν'`. Only null sets of `ν` enter the hypotheses `hν0`,
  `hν`, so nothing is lost by working with `ν'`.
* `φ` is an arbitrary measurable real function, not necessarily `ν'`-integrable, so the
  averaging is performed in the bounded chart `arctan` and read back through `tan`. The
  invariant representative is the *essential value* of `g ↦ arctan (φ (g • x))`: writing
  `A x` for its `ν'`-average and `D x` for its `L¹` deviation from that average,
  `ψ x = if D x = 0 then tan (A x) else 0`. This is genuinely invariant — not merely
  invariant a.e. — because the hypothesis `hν` says exactly that right translation preserves
  `ν'`-null sets, hence preserves the property "the orbit function is essentially constant"
  together with the value of that constant. Quasi-invariance is therefore enough; no
  invariant mean or amenability device is needed.
* Almost invariance in `IsUMPAlmostInvariant` is taken with respect to **every** member of
  the family (the classical "a.e. `P`" reading), rather than with respect to a single
  dominating measure.

**Bibliographic comments.** The equivalence of almost invariance and invariance under a
group carrying a measure with right-translation-invariant null sets belongs to the circle
of ideas of G. A. Hunt and C. Stein ("Most stringent tests of statistical hypotheses,"
unpublished manuscript, 1946) and C. Stein ("Some problems in multivariate analysis, Part
I," Technical Report 6, Department of Statistics, Stanford University, 1956); it is used
throughout E. L. Lehmann's development of invariance in the 1950s to compare invariance
with unbiasedness. Counterexamples delimiting the structural hypotheses, and further
results on the relation between the two notions, are due to R. H. Berk and P. J. Bickel
("On invariance and almost invariance," *Ann. Math. Statist.* **39** (1968), 1573–1576)
and R. H. Berk ("A remark on almost invariance," *Ann. Math. Statist.* **41** (1970),
733–735).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

variable {G Θ 𝓧 : Type*} [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧]

/-! ## Almost invariant functions are equivalent to invariant ones -/

/-- **Almost invariant ⟹ equivalent to invariant.** Under joint measurability of the
action and the existence of a nonzero σ-finite measure on the group whose null sets are
stable under right translation, every measurable almost-invariant function coincides, off
a `μ`-null set, with a measurable invariant function. -/
theorem exists_invariant_ae_eq_of_almostInvariant [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSMul₂ G 𝓧] {μ : Measure 𝓧} [SigmaFinite μ] {ν : Measure G} [SigmaFinite ν]
    {φ : 𝓧 → ℝ}
    -- USER-INPUT: the group carries a nonzero σ-finite measure
    (hν0 : ν ≠ 0)
    -- USER-INPUT: null sets of `ν` are stable under right translation, `ν B = 0 → ν (B·g) = 0`
    (hν : ∀ (g : G) (B : Set G), MeasurableSet B → ν B = 0 →
      ν ((fun y => y * g⁻¹) ⁻¹' B) = 0)
    -- USER-INPUT: `φ` is measurable
    (hφmeas : Measurable φ)
    -- USER-INPUT: `φ` is almost invariant with respect to `μ`
    (hφ : IsAlmostInvariant G μ φ) :
    ∃ ψ : 𝓧 → ℝ, Measurable ψ ∧ IsInvariantTest G ψ ∧ φ =ᵐ[μ] ψ := by
  classical
  -- `Real.tan` is measurable and inverts `Real.arctan`; `arctan` is the bounded chart used
  -- to average an arbitrary (not necessarily integrable) real function.
  have htan : Measurable Real.tan := by
    have h : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
    rw [h]; exact Real.measurable_sin.div Real.measurable_cos
  have harctan_b : ∀ y : ℝ, |Real.arctan y| ≤ Real.pi / 2 := fun y =>
    abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan y).le, (Real.arctan_lt_pi_div_two y).le⟩
  -- **Step 1: normalize.** A σ-finite `ν` carries an everywhere-positive density making it
  -- equivalent to a *finite* measure `ν'`; equivalence is all the hypotheses `hν0`/`hν` see,
  -- since both are statements about null sets.
  obtain ⟨w, hwpos, hwmeas, hwint⟩ :=
    exists_pos_lintegral_lt_of_sigmaFinite ν (ε := 1) one_ne_zero
  have hwm : Measurable fun y : G => ((w y : ℝ≥0) : ℝ≥0∞) := hwmeas.coe_nnreal_ennreal
  set ν' : Measure G := ν.withDensity (fun y => (w y : ℝ≥0∞)) with hν'def
  have hsupp : {y : G | ((w y : ℝ≥0) : ℝ≥0∞) ≠ 0} = Set.univ := by
    ext y; simp [(hwpos y).ne']
  have hnull : ∀ B : Set G, ν' B = 0 ↔ ν B = 0 := fun B => by
    rw [hν'def, withDensity_apply_eq_zero hwm, hsupp, Set.univ_inter]
  have hν'univ : ν' Set.univ < 1 := by
    rw [hν'def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hwint
  haveI : IsFiniteMeasure ν' := ⟨hν'univ.trans ENNReal.one_lt_top⟩
  have hν'ne : ν' Set.univ ≠ 0 := fun h =>
    hν0 (Measure.measure_univ_eq_zero.mp ((hnull _).mp h))
  set c : ℝ := (ν' Set.univ).toReal with hcdef
  have hc0 : 0 < c := ENNReal.toReal_pos hν'ne (measure_ne_top _ _)
  -- **Step 2: the averaged chart.** `F` is jointly measurable and bounded.
  set F : 𝓧 × G → ℝ := fun p => Real.arctan (φ (p.2 • p.1)) with hFdef
  have hFmeas : Measurable F :=
    (hφmeas.comp (measurable_snd.smul measurable_fst)).arctan
  have hFb : ∀ p : 𝓧 × G, |F p| ≤ Real.pi / 2 := fun p => harctan_b _
  have hFx : ∀ x : 𝓧, Measurable fun g => F (x, g) := fun x =>
    hFmeas.comp measurable_prodMk_left
  have hFint : ∀ x : 𝓧, Integrable (fun g => F (x, g)) ν' := fun x =>
    (integrable_const (Real.pi / 2)).mono' (hFx x).aestronglyMeasurable
      (ae_of_all _ fun g => by rw [Real.norm_eq_abs]; exact hFb _)
  set A : 𝓧 → ℝ := fun x => (∫ g, F (x, g) ∂ν') / c with hAdef
  have hAmeas : Measurable A :=
    (hFmeas.stronglyMeasurable.integral_prod_right').measurable.div_const c
  set D : 𝓧 → ℝ := fun x => ∫ g, ‖F (x, g) - A x‖ ∂ν' with hDdef
  have hDmeas : Measurable D := by
    have h : Measurable fun p : 𝓧 × G => ‖F p - A p.1‖ :=
      (hFmeas.sub (hAmeas.comp measurable_fst)).norm
    exact (h.stronglyMeasurable.integral_prod_right').measurable
  have hDint : ∀ x : 𝓧, Integrable (fun g => ‖F (x, g) - A x‖) ν' := fun x =>
    (integrable_const (Real.pi / 2 + |A x|)).mono'
      (((hFx x).sub measurable_const).norm).aestronglyMeasurable
      (ae_of_all _ fun g => by
        rw [norm_norm, Real.norm_eq_abs]
        exact (abs_sub _ _).trans (by linarith [hFb (x, g)]))
  -- `L1`: an essentially constant orbit function pins down `A` and kills `D`.
  have hL1 : ∀ (x : 𝓧) (r : ℝ), (∀ᵐ g ∂ν', F (x, g) = r) → A x = r ∧ D x = 0 := by
    intro x r hr
    have hA : A x = r := by
      have h1 : ∫ g, F (x, g) ∂ν' = ∫ _g : G, r ∂ν' := integral_congr_ae hr
      have h2 : ∫ _g : G, r ∂ν' = c * r := by
        rw [integral_const, smul_eq_mul, measureReal_def, ← hcdef]
      simp only [hAdef, h1, h2]
      field_simp
    refine ⟨hA, ?_⟩
    have hz : (fun g => ‖F (x, g) - A x‖) =ᵐ[ν'] fun _ => 0 := by
      filter_upwards [hr] with g hg
      rw [hg, hA, sub_self, norm_zero]
    simp only [hDdef]
    rw [integral_congr_ae hz, integral_zero]
  -- `L2`: conversely, `D x = 0` says the orbit function is essentially the constant `A x`.
  have hL2 : ∀ x : 𝓧, D x = 0 → ∀ᵐ g ∂ν', F (x, g) = A x := by
    intro x hx
    have h := (integral_eq_zero_iff_of_nonneg (fun g => norm_nonneg _) (hDint x)).mp hx
    filter_upwards [h] with g hg
    have := norm_eq_zero.mp hg
    linarith [sub_eq_zero.mp this]
  -- **Step 3: quasi-invariance.** Right translation preserves `ν'`-null sets, so it preserves
  -- "the orbit function is essentially the constant `r`".
  have hshift : ∀ (x : 𝓧) (h : G) (r : ℝ), (∀ᵐ g ∂ν', F (x, g) = r) →
      ∀ᵐ g ∂ν', F (h • x, g) = r := by
    intro x h r hr
    have hFeq : ∀ g : G, F (h • x, g) = F (x, g * h) := by
      intro g; simp only [hFdef, smul_smul]
    have hNmeas : MeasurableSet {g : G | F (x, g) ≠ r} :=
      ((hFx x) (measurableSet_singleton r)).compl
    have hkey := hν h⁻¹ _ hNmeas ((hnull _).mp (ae_iff.mp hr))
    rw [inv_inv] at hkey
    have hset : (fun y : G => y * h) ⁻¹' {g : G | F (x, g) ≠ r}
        = {g : G | F (h • x, g) ≠ r} := by
      ext g; simp only [Set.mem_preimage, Set.mem_setOf_eq, hFeq g]
    rw [hset] at hkey
    exact ae_iff.mpr ((hnull _).mpr hkey)
  have hstep : ∀ (h : G) (x : 𝓧), D x = 0 → A (h • x) = A x ∧ D (h • x) = 0 := fun h x hx =>
    hL1 (h • x) (A x) (hshift x h (A x) (hL2 x hx))
  -- The invariant representative: the essential value of `g ↦ arctan (φ (g • x))`, read back
  -- through `tan`, whenever that function is `ν'`-essentially constant.
  refine ⟨fun x => if D x = 0 then Real.tan (A x) else 0, ?_, ?_, ?_⟩
  · exact Measurable.ite (hDmeas (measurableSet_singleton 0)) (htan.comp hAmeas)
      measurable_const
  · -- Genuine invariance of the representative.
    intro h x
    by_cases hx : D x = 0
    · obtain ⟨hA', hD'⟩ := hstep h x hx
      simp only [if_pos hx, if_pos hD', hA']
    · have hD' : D (h • x) ≠ 0 := fun hcon => by
        obtain ⟨-, hD2⟩ := hstep h⁻¹ (h • x) hcon
        rw [inv_smul_smul] at hD2; exact hx hD2
      simp only [if_neg hx, if_neg hD']
  · -- **Step 4: Fubini.** The per-`g` a.e. identity becomes a per-`x` a.e.-in-`g` identity.
    have hPmeas : MeasurableSet {q : G × 𝓧 | φ (q.1 • q.2) = φ q.2} :=
      measurableSet_eq_fun (hφmeas.comp (measurable_fst.smul measurable_snd))
        (hφmeas.comp measurable_snd)
    have hcomm : ∀ᵐ x ∂μ, ∀ᵐ g ∂ν', φ (g • x) = φ x :=
      (Measure.ae_ae_comm (μ := ν') (ν := μ) hPmeas).mp (ae_of_all _ fun g => hφ g)
    filter_upwards [hcomm] with x hx
    have hr : ∀ᵐ g ∂ν', F (x, g) = Real.arctan (φ x) := by
      filter_upwards [hx] with g hg
      simp only [hFdef, hg]
    obtain ⟨hA', hD'⟩ := hL1 x _ hr
    simp only [if_pos hD', hA', Real.tan_arctan]

/-! ## UMP almost invariant tests -/

/-- **UMP almost invariant level-`α` test**: a critical function that is almost invariant
under every member of the family, has level `α`, and dominates on the alternative every
almost-invariant level-`α` competitor. -/
def IsUMPAlmostInvariant (G : Type*) [Group G] [MulAction G 𝓧] (P : Θ → Measure 𝓧)
    (Θ₀ Θ₁ : Set Θ) (α : ℝ) (φ : 𝓧 → ℝ) : Prop :=
  IsCriticalFn φ ∧ (∀ θ, IsAlmostInvariant G (P θ) φ) ∧ IsLevel P Θ₀ φ α ∧
    ∀ ψ, IsCriticalFn ψ → (∀ θ, IsAlmostInvariant G (P θ) ψ) → IsLevel P Θ₀ ψ α →
      ∀ θ ∈ Θ₁, power P ψ θ ≤ power P φ θ

/-- **A UMP invariant test is UMP among almost invariant tests.** Under the structural
assumptions above, together with a σ-finite dominating measure equivalent to the family,
every almost-invariant competitor has the power function of an invariant test, so it
cannot beat a UMP invariant one. -/
theorem isUMPAlmostInvariant_of_isUMPInvariant [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSMul₂ G 𝓧] [MulAction G Θ] {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} [SigmaFinite μ] {ν : Measure G}
    [SigmaFinite ν] {Θ₀ Θ₁ : Set Θ} {α : ℝ} {φ₀ : 𝓧 → ℝ}
    -- USER-INPUT: the group carries a nonzero σ-finite measure with right-translation
    -- stable null sets
    (hν0 : ν ≠ 0)
    (hν : ∀ (g : G) (B : Set G), MeasurableSet B → ν B = 0 →
      ν ((fun y => y * g⁻¹) ⁻¹' B) = 0)
    -- USER-INPUT: `μ` is equivalent to the family: every member is `μ`-absolutely
    -- continuous, and a set null under every member is `μ`-null
    (hdom : ∀ θ, P θ ≪ μ)
    (hequiv : ∀ A : Set 𝓧, MeasurableSet A → (∀ θ, P θ A = 0) → μ A = 0)
    -- USER-INPUT: `φ₀` is UMP among invariant level-`α` tests
    (hφ₀ : IsUMPInvariant G P Θ₀ Θ₁ α φ₀) :
    IsUMPAlmostInvariant G P Θ₀ Θ₁ α φ₀ := by
  refine ⟨hφ₀.1, fun θ g => ae_of_all _ (fun x => hφ₀.2.1 g x), hφ₀.2.2.1, ?_⟩
  intro ψ hψcrit hψai hψlevel θ hθ
  -- Family-wise almost invariance transfers to the equivalent dominating measure `μ`.
  have hμai : IsAlmostInvariant G μ ψ := by
    intro g
    have hgs : Measurable fun x : 𝓧 => g • x := measurable_const.smul measurable_id
    have hNmeas : MeasurableSet {x : 𝓧 | ψ (g • x) = ψ x}ᶜ := by
      have hset : {x : 𝓧 | ψ (g • x) = ψ x} = (fun x => ψ (g • x) - ψ x) ⁻¹' {0} := by
        ext x; simp [sub_eq_zero]
      rw [hset]
      exact (((hψcrit.1.comp hgs).sub hψcrit.1) (measurableSet_singleton 0)).compl
    rw [ae_iff]
    refine hequiv _ hNmeas (fun θ' => ?_)
    have h := hψai θ' g
    rwa [ae_iff] at h
  -- Averaging produces a genuinely invariant version; clamping keeps it a critical function.
  obtain ⟨ψ', hψ'meas, hψ'inv, hψ'ae⟩ :=
    exists_invariant_ae_eq_of_almostInvariant hν0 hν hψcrit.1 hμai
  have hclampcrit : IsCriticalFn (fun x => max 0 (min 1 (ψ' x))) :=
    ⟨measurable_const.max (measurable_const.min hψ'meas),
      fun x => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩
  have hclampinv : IsInvariantTest G (fun x => max 0 (min 1 (ψ' x))) := fun g x => by
    simp only [hψ'inv g x]
  have hψeq : ψ =ᵐ[μ] fun x => max 0 (min 1 (ψ' x)) := by
    filter_upwards [hψ'ae] with x hx
    have hb := hψcrit.2 x
    rw [← hx, min_eq_right hb.2, max_eq_right hb.1]
  have hpow : ∀ θ', power P (fun x => max 0 (min 1 (ψ' x))) θ' = power P ψ θ' := by
    intro θ'
    simp only [power]
    exact integral_congr_ae (hψeq.filter_mono (hdom θ').ae_le).symm
  have hclamplevel : IsLevel P Θ₀ (fun x => max 0 (min 1 (ψ' x))) α := by
    intro θ' hθ'; rw [hpow θ']; exact hψlevel θ' hθ'
  have hdomin := hφ₀.2.2.2 _ hclampcrit hclampinv hclamplevel θ hθ
  rwa [hpow θ] at hdomin

end StatLean.HypothesisTesting
