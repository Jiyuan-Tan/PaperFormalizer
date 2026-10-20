module
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Total variation distance between probability measures

Mathlib has the *signed-measure* (Jordan) total variation, but no total-variation **distance
between two probability measures**. For two probability measures $\mathbb{P}, \mathbb{Q}$ on a
measurable space, the **total variation distance** is defined in supremum form as
$$\|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}}
  = \sup_{A \text{ measurable}} \bigl(\mathbb{P}(A) - \mathbb{Q}(A)\bigr),$$
which equals $\sup_A |\mathbb{P}(A) - \mathbb{Q}(A)|$ since taking the complement flips the sign.
This file establishes the three standard equivalent characterizations and the basic metric
properties:

* `tvDist_le_one` — for probability measures, $\|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}} \le 1$;
* `tvDist_comm` — symmetry, $\|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}}
  = \|\mathbb{Q} - \mathbb{P}\|_{\mathrm{TV}}$;
* `tvDist_eq_half_lintegral` — the half-$L^1$ density form
  $\|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}} = \tfrac12 \int |p - q|\,d\nu$, with common
  dominating measure $\xi = \mathbb{P} + \mathbb{Q}$ and densities $p = d\mathbb{P}/d\xi$,
  $q = d\mathbb{Q}/d\xi$;
* `one_sub_tvDist_eq_iInf` — the variational representation
  $1 - \|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}}
    = \inf \bigl\{ \int f_0\,d\mathbb{P} + \int f_1\,d\mathbb{Q}
    : f_0, f_1 \ge 0 \text{ measurable},\ f_0 + f_1 \ge 1 \text{ pointwise} \bigr\}$,
  used in the proof of Le Cam's convex-hull bound.

Implementation note: the supremum and integral forms are stated with truncated subtraction in
$\mathbb{R}_{\ge 0}^\infty$ (so $\mathbb{P}(A) - \mathbb{Q}(A)$ means the positive part); this
matches the standard real-valued statement on probability measures, where the supremum is always
attained on the set $\{q \le p\}$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax lower bounds), §15.1.3 and §15.6,
Eq. (15.5)–(15.6), Exercise 15.1.

**Proof formalization notes.**
* `tvDist_comm` uses the "flip by complement" identity `tsub_eq_one_tsub_tsub` together with
  `measure_tsub_eq_compl` ($\mathbb{P}(A) - \mathbb{Q}(A) = \mathbb{Q}(A^c) - \mathbb{P}(A^c)$
  for probability measures), reindexing the supremum by complements.
* `tvDist_eq_half_lintegral` goes through the positive-part identity
  `tvDist_eq_lintegral_tsub`: the defining supremum is attained on $A = \{q \le p\}$ (with
  $p = d\mathbb{P}/d\xi$, $q = d\mathbb{Q}/d\xi$, $\xi = \mathbb{P} + \mathbb{Q}$), where
  $\mathbb{P}(A) - \mathbb{Q}(A) = \int_A (p - q)\,d\xi$ and the truncated $(p - q)$ vanishes off
  $A$, so the supremum equals $\int (p - q)\,d\xi$. The pointwise bridge
  $\mathrm{ofReal}\,|p - q| = (p - q) + (q - p)$ (lemma `ofReal_abs_toReal_sub`, valid where both
  densities are finite) plus the symmetry $\int (p - q)\,d\xi = \int (q - p)\,d\xi$ then yields the
  half-$L^1$ form.
* `one_sub_tvDist_eq_iInf` first proves $1 - \|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}}
  = \int \min(p, q)\,d\xi$ (lemma `one_sub_tvDist_eq_lintegral_min`, via
  $\min(p,q) + (p - q) = p$ and $\int p\,d\xi = 1$), then matches the infimum: the lower bound
  $\ge$ holds for any feasible $(f_0, f_1)$ from $\min(p,q)(f_0 + f_1) \ge \min(p,q)$, and the
  upper bound $\le$ is attained by the indicator choice $f_0 = \mathbf{1}_{\{p \le q\}}$,
  $f_1 = \mathbf{1}_{\{q < p\}}$, which evaluates to $\int \min(p,q)\,d\xi$.

**Bibliographic comments.** The total variation distance and its three equivalent forms
(supremum over events, one-half of the $L^1$ distance between densities, and the
$\min(p,q)$ / coupling-type variational representation) are classical folklore of statistical
distances with no single seminal origin; they appear in standard references on the comparison of
experiments and minimax theory. The variational form and its use to bound testing error trace to
L. Le Cam's theory of statistical experiments — see L. Le Cam, *Asymptotic Methods in Statistical
Decision Theory*, Springer, 1986 — but the elementary identities formalized here predate any
specific attribution and are reproduced in the Wainwright reference above.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Total variation distance** between two measures (Wainwright Eq. (15.5)):
`‖ℙ − ℚ‖_TV = sup_{A} (ℙ(A) − ℚ(A))` with truncated subtraction in `ℝ≥0∞`. For probability
measures this equals `sup_A |ℙ(A) − ℚ(A)|` and lies in `[0,1]`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.5). -/
noncomputable def tvDist (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ (s : Set α) (_ : MeasurableSet s), μ s - ν s

/-- For `a, b ≤ 1` in `ℝ≥0∞` (truncated subtraction), `a − b = (1 − b) − (1 − a)`. This is the
"flip by complement" identity used to show symmetry of the total variation distance. -/
private lemma tsub_eq_one_tsub_tsub {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    a - b = (1 - b) - (1 - a) := by
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (tsub_le_tsub_left h 1)]
  · have e : (1 : ℝ≥0∞) - a + (a - b) = 1 - b := tsub_add_tsub_cancel ha h
    rw [← e, (ENNReal.cancel_of_ne (ENNReal.sub_ne_top ENNReal.one_ne_top)).add_tsub_cancel_left]

/-- For probability measures and measurable `s`, `μ s − ν s = ν sᶜ − μ sᶜ`. -/
private lemma measure_tsub_eq_compl (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {s : Set α} (hs : MeasurableSet s) :
    μ s - ν s = ν sᶜ - μ sᶜ := by
  rw [prob_compl_eq_one_sub hs, prob_compl_eq_one_sub hs]
  exact tsub_eq_one_tsub_tsub prob_le_one prob_le_one

/-- One inequality of the symmetry of total variation: reindexing the supremum by complements. -/
private lemma tvDist_le_swap (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ tvDist ν μ := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [measure_tsub_eq_compl μ ν hs]
  exact le_iSup₂ (f := fun t (_ : MeasurableSet t) => ν t - μ t) sᶜ hs.compl

/-- Total variation distance is symmetric. -/
theorem tvDist_comm (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = tvDist ν μ :=
  le_antisymm (tvDist_le_swap μ ν) (tvDist_le_swap ν μ)

/-- For probability measures, `tvDist ℙ ℚ ≤ 1`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3. -/
theorem tvDist_le_one (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := by
  refine iSup_le fun s => iSup_le fun _ => ?_
  calc μ s - ν s ≤ μ s := tsub_le_self
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ s)
    _ = 1 := measure_univ

-- Pointwise bridge between the real `|p − q|` integrand and the two truncated `ℝ≥0∞`
-- differences `(p − q) + (q − p)`, valid wherever both densities are finite.
private lemma ofReal_abs_toReal_sub {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.ofReal |a.toReal - b.toReal| = (a - b) + (b - a) := by
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, zero_add,
        abs_of_nonpos (sub_nonpos.mpr (ENNReal.toReal_mono hb h)), neg_sub,
        ← ENNReal.toReal_sub_of_le h hb, ENNReal.ofReal_toReal (ENNReal.sub_ne_top hb)]
  · rw [tsub_eq_zero_of_le h, add_zero,
        abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono ha h)),
        ← ENNReal.toReal_sub_of_le h ha, ENNReal.ofReal_toReal (ENNReal.sub_ne_top ha)]

-- Eq. (15.6), positive-part form: the supremum defining `tvDist` is attained on the set
-- `A = {q ≤ p}` (densities `p = dμ/dξ`, `q = dν/dξ`, `ξ = μ + ν`), where `μ A − ν A =
-- ∫_A (p − q) dξ`. Since `(p − q)` (truncated in `ℝ≥0∞`) vanishes off `A`, the supremum
-- equals `∫ (p − q) dξ`.
private lemma tvDist_eq_lintegral_tsub (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν
      = ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
  have hμξ : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hνξ : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  have hpm : Measurable (μ.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hqm : Measurable (ν.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  set A : Set α := {x | ν.rnDeriv (μ + ν) x ≤ μ.rnDeriv (μ + ν) x} with hA
  have hAm : MeasurableSet A := measurableSet_le hqm hpm
  refine le_antisymm ?_ ?_
  · refine iSup_le fun s => iSup_le fun _ => ?_
    calc μ s - ν s
        = ∫⁻ x in s, μ.rnDeriv (μ + ν) x ∂(μ + ν)
            - ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν) := by
          rw [Measure.setLIntegral_rnDeriv hμξ s, Measure.setLIntegral_rnDeriv hνξ s]
      _ ≤ ∫⁻ x in s, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) :=
          lintegral_sub_le _ _ hqm
      _ ≤ ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
  · have hle : ν.rnDeriv (μ + ν) ≤ᵐ[(μ + ν).restrict A] μ.rnDeriv (μ + ν) :=
      ae_restrict_of_forall_mem hAm (fun x hx => hx)
    have hfin : ∫⁻ x in A, ν.rnDeriv (μ + ν) x ∂(μ + ν) ≠ ∞ := by
      rw [Measure.setLIntegral_rnDeriv hνξ A]; exact measure_ne_top ν A
    have hcompl : ∫⁻ x in Aᶜ, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) = 0 := by
      refine setLIntegral_eq_zero hAm.compl (fun x hx => ?_)
      rw [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      exact tsub_eq_zero_of_le hx.le
    have hDA : ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν)
        = ∫⁻ x in A, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
      rw [← lintegral_add_compl _ hAm, hcompl, add_zero]
    have hAsub : ∫⁻ x in A, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν)
        = μ A - ν A := by
      rw [lintegral_sub hqm hfin hle, Measure.setLIntegral_rnDeriv hμξ A,
          Measure.setLIntegral_rnDeriv hνξ A]
    rw [hDA, hAsub]
    exact le_iSup₂ (f := fun s (_ : MeasurableSet s) => μ s - ν s) A hAm

private lemma tvDist_eq_half_lintegral_aux (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν
      = 2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν) := by
  have hμξ : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hνξ : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  have hpm : Measurable (μ.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hqm : Measurable (ν.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hp1 : ∫⁻ x, μ.rnDeriv (μ + ν) x ∂(μ + ν) = 1 := by
    rw [Measure.lintegral_rnDeriv hμξ]; exact measure_univ
  have hq1 : ∫⁻ x, ν.rnDeriv (μ + ν) x ∂(μ + ν) = 1 := by
    rw [Measure.lintegral_rnDeriv hνξ]; exact measure_univ
  have habs : ∫⁻ x, ENNReal.ofReal
        |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν)
      = ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν)
        + ∫⁻ x, (ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x) ∂(μ + ν) := by
    rw [← lintegral_add_left (hpm.fun_sub hqm)]
    refine lintegral_congr_ae ?_
    filter_upwards [μ.rnDeriv_lt_top (μ + ν), ν.rnDeriv_lt_top (μ + ν)] with x hpx hqx
    exact ofReal_abs_toReal_sub hpx.ne hqx.ne
  have hDD : ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν)
      = ∫⁻ x, (ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x) ∂(μ + ν) := by
    have e1 : ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν)
          + ∫⁻ x, ν.rnDeriv (μ + ν) x ∂(μ + ν)
        = ∫⁻ x, (ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x) ∂(μ + ν)
          + ∫⁻ x, μ.rnDeriv (μ + ν) x ∂(μ + ν) := by
      rw [← lintegral_add_left (hpm.fun_sub hqm), ← lintegral_add_left (hqm.fun_sub hpm)]
      refine lintegral_congr fun x => ?_
      rw [tsub_add_eq_max, tsub_add_eq_max, max_comm]
    rw [hp1, hq1] at e1
    exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp e1
  rw [tvDist_eq_lintegral_tsub μ ν, habs, ← hDD, ← two_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top, one_mul]

/-- **Density (one-half `L¹`) form of total variation** (Wainwright Eq. (15.6)):
`‖ℙ − ℚ‖_TV = ½ ∫ |p − q| dν`, here with the common dominating measure `ξ = ℙ + ℚ` and
densities `p = dℙ/dξ`, `q = dℚ/dξ`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.6). -/
theorem tvDist_eq_half_lintegral (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν
      = 2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν) :=
  tvDist_eq_half_lintegral_aux μ ν

-- `1 − tvDist = ∫ min(p,q) dξ`: the complement of the positive-part form, using
-- `min(p,q) + (p − q) = p` pointwise and `∫ p dξ = μ univ = 1`.
private lemma one_sub_tvDist_eq_lintegral_min (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    1 - tvDist μ ν
      = ∫⁻ x, min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
  have hμξ : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hpm : Measurable (μ.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hqm : Measurable (ν.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hp1 : ∫⁻ x, μ.rnDeriv (μ + ν) x ∂(μ + ν) = 1 := by
    rw [Measure.lintegral_rnDeriv hμξ]; exact measure_univ
  have hDfin : ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hp1]; exact ENNReal.one_ne_top)
      (lintegral_mono fun _ => tsub_le_self)
  have hsum : ∫⁻ x, min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) ∂(μ + ν)
        + ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) = 1 := by
    rw [← lintegral_add_left (hpm.min hqm), ← hp1]
    refine lintegral_congr fun x => ?_
    rw [add_comm, tsub_add_min]
  rw [tvDist_eq_lintegral_tsub μ ν]
  exact (ENNReal.eq_sub_of_add_eq hDfin hsum).symm

-- Exercise 15.1: the variational/indicator-optimum representation of `1 − tvDist`.
-- `≥` from any feasible `(f₀, f₁)` (pointwise `f₀ p + f₁ q ≥ min(p,q)`); `≤` by the
-- indicator choice `f₀ = 𝟙_{p ≤ q}`, `f₁ = 𝟙_{q < p}`, which attains `∫ min(p,q) dξ`.
private lemma one_sub_tvDist_eq_iInf_aux (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    1 - tvDist μ ν
      = ⨅ (f₀ : α → ℝ≥0∞) (f₁ : α → ℝ≥0∞) (_ : Measurable f₀) (_ : Measurable f₁)
          (_ : ∀ x, 1 ≤ f₀ x + f₁ x),
          (∫⁻ x, f₀ x ∂μ + ∫⁻ x, f₁ x ∂ν) := by
  have hμξ : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hνξ : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  have hpm : Measurable (μ.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hqm : Measurable (ν.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  rw [one_sub_tvDist_eq_lintegral_min μ ν]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun f₀ => le_iInf fun f₁ => le_iInf fun hf0 => le_iInf fun hf1 =>
      le_iInf fun hfeas => ?_
    rw [← lintegral_rnDeriv_mul hμξ hf0.aemeasurable,
        ← lintegral_rnDeriv_mul hνξ hf1.aemeasurable,
        ← lintegral_add_left (hpm.fun_mul hf0)]
    refine lintegral_mono fun x => ?_
    calc min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x)
        = min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) * 1 := (mul_one _).symm
      _ ≤ min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) * (f₀ x + f₁ x) := by
          gcongr; exact hfeas x
      _ = min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) * f₀ x
            + min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) * f₁ x := mul_add _ _ _
      _ ≤ μ.rnDeriv (μ + ν) x * f₀ x + ν.rnDeriv (μ + ν) x * f₁ x := by
          gcongr <;> [exact min_le_left _ _; exact min_le_right _ _]
  · set B : Set α := {x | μ.rnDeriv (μ + ν) x ≤ ν.rnDeriv (μ + ν) x} with hB
    have hBm : MeasurableSet B := measurableSet_le hpm hqm
    have hfeas : ∀ x, 1 ≤ B.indicator 1 x + Bᶜ.indicator (1 : α → ℝ≥0∞) x := by
      intro x
      by_cases hx : x ∈ B
      · simp [Set.indicator_of_mem hx, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx)]
      · simp [Set.indicator_of_notMem hx, Set.indicator_of_mem (Set.mem_compl_iff B x |>.mpr hx)]
    refine iInf_le_of_le (B.indicator 1) (iInf_le_of_le (Bᶜ.indicator 1)
      (iInf_le_of_le (measurable_one.indicator hBm) (iInf_le_of_le
        (measurable_one.indicator hBm.compl) (iInf_le_of_le hfeas ?_))))
    rw [lintegral_indicator_one hBm, lintegral_indicator_one hBm.compl]
    have hμB : μ B = ∫⁻ x in B, min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
      rw [← Measure.setLIntegral_rnDeriv hμξ B]
      exact setLIntegral_congr_fun hBm (fun x hx => (min_eq_left hx).symm)
    have hνB : ν Bᶜ = ∫⁻ x in Bᶜ, min (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
      rw [← Measure.setLIntegral_rnDeriv hνξ Bᶜ]
      refine setLIntegral_congr_fun hBm.compl (fun x hx => ?_)
      rw [hB, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      exact (min_eq_right hx.le).symm
    rw [hμB, hνB]
    exact le_of_eq (lintegral_add_compl _ hBm)

/-- **Variational representation of total variation** (Wainwright Exercise 15.1):
`1 − ‖ℙ − ℚ‖_TV = inf { ∫ f₀ dℙ + ∫ f₁ dℚ : f₀, f₁ ≥ 0 measurable, f₀ + f₁ ≥ 1 pointwise }`.
This is the form used in the proof of Le Cam's convex-hull bound (Lemma 15.9).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.1. -/
theorem one_sub_tvDist_eq_iInf (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    1 - tvDist μ ν
      = ⨅ (f₀ : α → ℝ≥0∞) (f₁ : α → ℝ≥0∞) (_ : Measurable f₀) (_ : Measurable f₁)
          (_ : ∀ x, 1 ≤ f₀ x + f₁ x),
          (∫⁻ x, f₀ x ∂μ + ∫⁻ x, f₁ x ∂ν) :=
  one_sub_tvDist_eq_iInf_aux μ ν

end StatLean.Minimaxity
