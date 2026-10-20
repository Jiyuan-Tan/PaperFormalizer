module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
# The Huber loss and score

The Huber family (`MMY §2.3.2`, eq. (2.28)–(2.29); Huber 1964) is the canonical bridge
between least squares and bounded-influence estimation: quadratic in a central region
`|u| ≤ c`, linear outside, with score clamped at `±c`:

$$\rho_c(u) = \begin{cases} u^2/2, & |u| \le c\\ c|u| - c^2/2, & |u| > c\end{cases},
\qquad
\psi_c(u) = \max(-c, \min(c, u)).$$

The bounded score `|ψ_c| ≤ c` is the mathematical reason the Huber location estimator has
bounded influence (`MEstimation/Influence.lean`) and positive asymptotic breakdown
(`MEstimation/AsymptoticBreakdown.lean`), while the unbounded score `ψ(u) = u` of squared
loss makes the mean fragile.

**Deviation from the book statement.** `MMY` eq. (2.28) normalizes `ρ_k(u) = u²` on the
central region, so that `ρ_k' = 2ψ_k`. We use Huber's original normalization `u²/2`, giving
the cleaner identity `ρ_c' = ψ_c`; the two objectives differ by the constant factor `2`, so
they have the same minimizers and the same estimating equation.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.3.2 (eq.
(2.28)–(2.29)), Definitions 2.1–2.2 (ρ- and ψ-functions).

**Bibliographic comments.** P. J. Huber, "Robust estimation of a location parameter,"
*The Annals of Mathematical Statistics* **35**(1), 1964, pp. 73–101.
-/

open Filter Topology

namespace StatLean.RobustStatistics

/-- The **Huber loss** with clipping constant `c` (`MMY` eq. (2.28), in the `u²/2`
normalization): quadratic on `|u| ≤ c`, linear with slope `c` outside. Junk behaviour for
`c < 0` (the `|u| ≤ c` branch is empty). -/
noncomputable def huberRho (c u : ℝ) : ℝ :=
  if |u| ≤ c then u ^ 2 / 2 else c * |u| - c ^ 2 / 2

/-- The **Huber score** with clipping constant `c` (`MMY` eq. (2.29)): the identity
clamped to `[-c, c]`. -/
noncomputable def huberPsi (c u : ℝ) : ℝ :=
  max (-c) (min c u)

/-- On the central region the Huber loss is the (half) squared loss. -/
theorem huberRho_of_abs_le {c u : ℝ} (h : |u| ≤ c) : huberRho c u = u ^ 2 / 2 := by
  unfold huberRho
  rw [if_pos h]

/-- Outside the central region the Huber loss is linear in `|u|`. -/
theorem huberRho_of_lt_abs {c u : ℝ} (h : c < |u|) : huberRho c u = c * |u| - c ^ 2 / 2 := by
  unfold huberRho
  rw [if_neg (not_le.mpr h)]

/-- On the central region the Huber score is the identity. -/
theorem huberPsi_of_abs_le {c u : ℝ} (hc : 0 ≤ c) (h : |u| ≤ c) : huberPsi c u = u := by
  rw [abs_le] at h
  unfold huberPsi
  rw [min_eq_right h.2, max_eq_right h.1]

@[simp] theorem huberRho_zero {c : ℝ} (hc : 0 ≤ c) : huberRho c 0 = 0 := by
  rw [huberRho_of_abs_le (by simpa using hc)]
  ring

@[simp] theorem huberPsi_zero {c : ℝ} (hc : 0 ≤ c) : huberPsi c 0 = 0 :=
  huberPsi_of_abs_le hc (by simpa using hc)

/-- The Huber loss is nonnegative (`MMY` Definition 2.1, R1–R2 context). -/
theorem huberRho_nonneg {c : ℝ} (hc : 0 ≤ c) (u : ℝ) : 0 ≤ huberRho c u := by
  unfold huberRho
  split_ifs with h
  · positivity
  · rw [not_le] at h
    nlinarith [mul_le_mul_of_nonneg_left h.le hc]

/-- The Huber loss is even (`MMY` Definition 2.1: a function of `|u|`). -/
theorem huberRho_even (c u : ℝ) : huberRho c (-u) = huberRho c u := by
  unfold huberRho
  rw [abs_neg]
  split_ifs <;> ring

/-- The Huber score is odd (`MMY` Definition 2.2, Ψ1). -/
theorem huberPsi_odd {c : ℝ} (hc : 0 ≤ c) (u : ℝ) : huberPsi c (-u) = -huberPsi c u := by
  unfold huberPsi
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- **The Huber score is bounded by the clipping constant** (`MMY §2.3.2`): `|ψ_c| ≤ c`.
This is the property that transfers to a bounded influence function. -/
theorem abs_huberPsi_le {c : ℝ} (hc : 0 ≤ c) (u : ℝ) : |huberPsi c u| ≤ c := by
  rw [abs_le]
  refine ⟨le_max_left _ _, max_le (by linarith) ((min_le_left c u).trans le_rfl)⟩

/-- The Huber score is monotone (`MMY §2.3.1`: monotone ψ gives a well-posed estimating
equation). -/
theorem huberPsi_monotone (c : ℝ) : Monotone (huberPsi c) := fun _ _ hab =>
  max_le_max le_rfl (min_le_min le_rfl hab)

/-- The Huber score is `1`-Lipschitz. -/
theorem huberPsi_lipschitz (c : ℝ) : LipschitzWith 1 (huberPsi c) :=
  (LipschitzWith.id.const_min c).const_max (-c)

/-- The Huber score is continuous. -/
theorem huberPsi_continuous (c : ℝ) : Continuous (huberPsi c) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- The Huber score tends to `-c` at `-∞` (the lower clamp; `MMY §3.2.1`,
`k₁ = -ψ(-∞)`). -/
theorem huberPsi_tendsto_atBot (c : ℝ) : Tendsto (huberPsi c) atBot (𝓝 (-c)) := by
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := -c) (f := atBot))
  filter_upwards [eventually_le_atBot (-c)] with u hu
  unfold huberPsi
  rw [max_eq_left ((min_le_right c u).trans hu)]

/-- The Huber score tends to `c` at `+∞` (the upper clamp; `MMY §3.2.1`, `k₂ = ψ(∞)`).

**Statement repair (2026-08-15).** The hypothesis `0 ≤ c` is *not* optional: the original
stub asserted the limit for every real `c`, which is false for `c < 0`. There
`min c u ≤ c < 0 < -c`, so `huberPsi c` is the *constant* `-c` and tends to `-c ≠ c`; the
refutation at `c = -1` is machine-checked immediately below. Since `MMY §2.2` only ever
uses a positive clipping constant, adding `0 ≤ c` restores the book's statement rather
than weakening it. The companion limit `huberPsi_tendsto_atBot` needs no such repair: for
`c < 0` the constant value `-c` *is* the claimed limit there. -/
theorem huberPsi_tendsto_atTop {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (huberPsi c) atTop (𝓝 c) := by
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := c) (f := atTop))
  filter_upwards [eventually_ge_atTop c] with u hu
  unfold huberPsi
  rw [min_eq_left hu, max_eq_right (by linarith)]

/-- Machine-checked refutation of the *unrepaired* form of the statement above at
`c = -1`: the score is the constant `1` there, so it does not tend to `-1`. This is the
witness that forced the `0 ≤ c` hypothesis. -/
example : ¬ Tendsto (huberPsi (-1 : ℝ)) atTop (𝓝 (-1)) := by
  intro h
  have hconst : huberPsi (-1 : ℝ) = fun _ => (1 : ℝ) := by
    funext u
    unfold huberPsi
    rw [max_eq_left ((min_le_left (-1 : ℝ) u).trans (by norm_num))]
    norm_num
  rw [hconst] at h
  have := tendsto_nhds_unique h (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
  norm_num at this

/-- **The Huber loss is differentiable with derivative the Huber score**
(`MMY` eq. (2.29)): `ρ_c' = ψ_c`, including at the knots `u = ±c`. -/
theorem hasDerivAt_huberRho {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    HasDerivAt (huberRho c) (huberPsi c u) u := by
  rcases hc.eq_or_lt with rfl | hcpos
  · -- Degenerate clipping constant: `ρ_0 ≡ 0` and `ψ_0 ≡ 0`.
    have h0 : huberRho (0 : ℝ) = fun _ : ℝ => (0 : ℝ) := by
      funext v
      unfold huberRho
      split_ifs with h
      · rw [abs_eq_zero.mp (le_antisymm h (abs_nonneg v))]; ring
      · ring
    have h1 : huberPsi (0 : ℝ) u = 0 := by
      unfold huberPsi
      rw [neg_zero, max_eq_left (min_le_left (0 : ℝ) u)]
    rw [h0, h1]
    exact hasDerivAt_const _ _
  · -- Global branch formulas, valid at the knots as well.
    have hIci : ∀ v : ℝ, c ≤ v → huberRho c v = c * v - c ^ 2 / 2 := by
      intro v hv
      rcases eq_or_lt_of_le hv with heq | hlt
      · rw [← heq, huberRho_of_abs_le (abs_of_nonneg hcpos.le).le]; ring
      · have hv0 : (0 : ℝ) ≤ v := hcpos.le.trans hv
        rw [huberRho_of_lt_abs (by rwa [abs_of_nonneg hv0]), abs_of_nonneg hv0]
    have hIic : ∀ v : ℝ, v ≤ -c → huberRho c v = -(c * v) - c ^ 2 / 2 := by
      intro v hv
      rcases eq_or_lt_of_le hv with heq | hlt
      · rw [heq, huberRho_of_abs_le (by rw [abs_neg, abs_of_nonneg hcpos.le])]; ring
      · have hv0 : v < 0 := hlt.trans_le (by linarith)
        rw [huberRho_of_lt_abs (by rw [abs_of_neg hv0]; linarith), abs_of_neg hv0]; ring
    -- Derivatives of the three branch formulas.
    have hlin : ∀ w : ℝ, HasDerivAt (fun v : ℝ => c * v - c ^ 2 / 2) c w := by
      intro w
      simpa using ((hasDerivAt_id w).const_mul c).sub_const (c ^ 2 / 2)
    have hlin' : ∀ w : ℝ, HasDerivAt (fun v : ℝ => -(c * v) - c ^ 2 / 2) (-c) w := by
      intro w
      simpa using (((hasDerivAt_id w).const_mul c).neg).sub_const (c ^ 2 / 2)
    have hsq : ∀ w : ℝ, HasDerivAt (fun v : ℝ => v ^ 2 / 2) w w := by
      intro w
      have h : HasDerivAt (fun v : ℝ => v * v / 2) w w := by
        simpa using ((hasDerivAt_id w).mul (hasDerivAt_id w)).div_const 2
      simpa only [pow_two] using h
    rcases lt_trichotomy u (-c) with hu | hu | hu
    · -- Left linear region.
      have hpsi : huberPsi c u = -c := by
        unfold huberPsi
        rw [min_eq_right (by linarith), max_eq_left hu.le]
      rw [hpsi]
      exact (hlin' u).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (Iio_mem_nhds hu) fun v hv => hIic v (le_of_lt hv))
    · -- Left knot `u = -c`: glue the two one-sided derivatives.
      subst hu
      have hpsi : huberPsi c (-c) = -c := by
        unfold huberPsi
        rw [min_eq_right (by linarith), max_eq_left le_rfl]
      rw [hpsi]
      have hleft : HasDerivWithinAt (huberRho c) (-c) (Set.Iic (-c)) (-c) :=
        (hlin' (-c)).hasDerivWithinAt.congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun v hv => hIic v hv)
          (hIic (-c) le_rfl)
      have hright : HasDerivWithinAt (huberRho c) (-c) (Set.Ici (-c)) (-c) := by
        refine ((hsq (-c)).hasDerivWithinAt).congr_of_eventuallyEq ?_
          (huberRho_of_abs_le (by rw [abs_neg, abs_of_nonneg hcpos.le]))
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : -c < c))] with v hv1 hv2
        exact huberRho_of_abs_le (abs_le.2 ⟨hv1, hv2.le⟩)
      have := hleft.union hright
      rw [Set.Iic_union_Ici] at this
      exact hasDerivWithinAt_univ.mp this
    · rcases lt_trichotomy u c with hu2 | hu2 | hu2
      · -- Central quadratic region.
        rw [huberPsi_of_abs_le hcpos.le (abs_le.2 ⟨hu.le, hu2.le⟩)]
        exact (hsq u).congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem (Ioo_mem_nhds hu hu2) fun v hv =>
            huberRho_of_abs_le (abs_le.2 ⟨hv.1.le, hv.2.le⟩))
      · -- Right knot `u = c`.
        rw [hu2]
        have hpsi : huberPsi c c = c := by
          unfold huberPsi
          rw [min_eq_left le_rfl, max_eq_right (by linarith)]
        rw [hpsi]
        have hright : HasDerivWithinAt (huberRho c) c (Set.Ici c) c :=
          (hlin c).hasDerivWithinAt.congr_of_eventuallyEq
            (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun v hv => hIci v hv)
            (hIci c le_rfl)
        have hleft : HasDerivWithinAt (huberRho c) c (Set.Iic c) c := by
          refine ((hsq c).hasDerivWithinAt).congr_of_eventuallyEq ?_
            (huberRho_of_abs_le (abs_of_nonneg hcpos.le).le)
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : -c < c))] with v hv1 hv2
          exact huberRho_of_abs_le (abs_le.2 ⟨hv2.le, hv1⟩)
        have := hleft.union hright
        rw [Set.Iic_union_Ici] at this
        exact hasDerivWithinAt_univ.mp this
      · -- Right linear region.
        have hpsi : huberPsi c u = c := by
          unfold huberPsi
          rw [min_eq_left hu2.le, max_eq_right (by linarith)]
        rw [hpsi]
        exact (hlin u).congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hu2) fun v hv => hIci v (le_of_lt hv))

theorem deriv_huberRho {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    deriv (huberRho c) u = huberPsi c u :=
  (hasDerivAt_huberRho hc u).deriv

/-- The Huber loss is continuous. -/
theorem huberRho_continuous {c : ℝ} (hc : 0 ≤ c) : Continuous (huberRho c) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_huberRho hc u).continuousAt

/-- **The Huber loss is convex** (`MMY §2.4`, eq. (2.40) context: ρ with nondecreasing
derivative). -/
theorem huberRho_convex {c : ℝ} (hc : 0 ≤ c) : ConvexOn ℝ Set.univ (huberRho c) := by
  refine MonotoneOn.convexOn_of_deriv convex_univ (huberRho_continuous hc).continuousOn
    ?_ ?_
  · rw [interior_univ]
    exact fun v _ => ((hasDerivAt_huberRho hc v).differentiableAt).differentiableWithinAt
  · rw [interior_univ]
    intro a _ b _ hab
    rw [deriv_huberRho hc, deriv_huberRho hc]
    exact huberPsi_monotone c hab

/-- The Huber loss is coercive for `c > 0`: it grows without bound as `|u| → ∞` (used for
the existence of Huber M-estimates). -/
theorem huberRho_tendsto_cocompact {c : ℝ} (hc : 0 < c) :
    Tendsto (huberRho c) (cocompact ℝ) atTop := by
  have habs : Tendsto (fun u : ℝ => |u|) (cocompact ℝ) atTop := by
    simpa only [Real.norm_eq_abs] using! (tendsto_norm_cocompact_atTop (E := ℝ))
  have h1 : Tendsto (fun u : ℝ => c * |u| + -(c ^ 2 / 2)) (cocompact ℝ) atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_const_mul_atTop_of_pos hc).2 habs)
  refine tendsto_atTop_mono (fun u => ?_) h1
  unfold huberRho
  split_ifs with h
  · nlinarith [sq_nonneg (|u| - c), sq_abs u]
  · linarith

end StatLean.RobustStatistics
