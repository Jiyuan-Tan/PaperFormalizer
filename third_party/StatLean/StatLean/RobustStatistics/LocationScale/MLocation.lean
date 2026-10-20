module
public import StatLean.RobustStatistics.LocationScale.Huber
public import StatLean.RobustStatistics.LocationScale.Mean
public import StatLean.RobustStatistics.LocationScale.Median

@[expose] public section

/-!
# Location M-estimates — the finite-sample objective and estimating equation

A location M-estimate for the loss `ρ` is a global minimizer of
`θ ↦ ∑ᵢ ρ(xᵢ - θ)` (`MMY §2.3.1`, eq. (2.13)). This family contains the mean
(`ρ(u) = u²`), the median (`ρ(u) = |u|`) and the Huber estimates, and — for
differentiable `ρ` with score `ψ = ρ'` — is characterized by the estimating equation
`∑ᵢ ψ(xᵢ - θ̂) = 0` (`MMY` eq. (2.19)):

* `IsMLocationEstimate ρ x θ` — `θ` globally minimizes the M-objective.
* `exists_isMLocationEstimate` — existence for continuous coercive losses.
* `IsMLocationEstimate.score_eq_zero` — minimizer ⟹ estimating equation (eq. (2.19)).
* `isMLocationEstimate_of_score_eq_zero` — the converse for convex `ρ`.
* `isMLocationEstimate_comp_add` — the M-estimate correspondence is shift equivariant.
* `isMLocationEstimate_sq_iff` — squared loss ⟺ the sample mean (eq. (2.16)).
* `isMLocationEstimate_abs_sampleMedian` — the median minimizes the L¹ objective
  (eq. (2.18)).
* Huber instances: existence, and the clipped estimating equation.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.3.1 (eq.
(2.13), (2.16), (2.18)–(2.19)), Theorem 10.1 (existence/uniqueness of solutions).

**Bibliographic comments.** Location M-estimators — maximum-likelihood-type estimators for
a free loss `ρ` — are P. J. Huber, "Robust estimation of a location parameter," *Ann. Math.
Statist.* **35** (1964), 73–101; existence, uniqueness and computation are treated in Huber
and Ronchetti, *Robust Statistics*, 2nd ed., Wiley, 2009, chs. 3 and 6.
-/

open Filter Topology

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- **Location M-estimate** (`MMY §2.3.1`, eq. (2.13)): `θ` is a global minimizer of the
M-objective `t ↦ ∑ᵢ ρ(xᵢ - t)`. For non-convex (redescending) `ρ` this is the absolute
minimum, not a mere estimating-equation root (`MMY §2.4` discussion). -/
def IsMLocationEstimate (ρ : ℝ → ℝ) (x : Fin n → ℝ) (θ : ℝ) : Prop :=
  ∀ t : ℝ, ∑ i, ρ (x i - θ) ≤ ∑ i, ρ (x i - t)

/-- **Existence of location M-estimates** for continuous, bounded-below, coercive losses
(`MMY` Theorem 10.1 context). -/
theorem exists_isMLocationEstimate {ρ : ℝ → ℝ}
    -- USER-INPUT: continuous loss; MMY Thm 10.1 context
    (hρc : Continuous ρ)
    -- USER-INPUT: coercive loss (ρ → ∞ as |u| → ∞); MMY §2.3.1 (ρ-function, R3)
    (hρ_coer : Tendsto ρ (cocompact ℝ) atTop)
    -- LEAN-ONLY: bounded below, so that one escaping term cannot be cancelled; free for
    -- ρ-functions, which are nonnegative (MMY Def 2.1 R1–R2)
    (hρ_bdd : BddBelow (Set.range ρ))
    (x : Fin n → ℝ) :
    ∃ θ : ℝ, IsMLocationEstimate ρ x θ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun t => by simp⟩
  · obtain ⟨b, hb⟩ := hρ_bdd
    have hb' : ∀ u, b ≤ ρ u := fun u => hb ⟨u, rfl⟩
    set i₀ : Fin n := ⟨0, hn⟩ with hi₀
    have hfc : Continuous (fun t : ℝ => ∑ i, ρ (x i - t)) :=
      continuous_finset_sum _ fun i _ => hρc.comp (continuous_const.sub continuous_id)
    -- `t ↦ a - t` is proper: it swaps the two ends of the line.
    have hmap : ∀ a : ℝ, Tendsto (fun t : ℝ => a - t) (cocompact ℝ) (cocompact ℝ) := by
      intro a
      have h1 : Tendsto (fun t : ℝ => a - t) atBot atTop := by
        refine tendsto_atTop.2 fun c => ?_
        filter_upwards [eventually_le_atBot (a - c)] with t ht
        linarith
      have h2 : Tendsto (fun t : ℝ => a - t) atTop atBot := by
        refine tendsto_atBot.2 fun c => ?_
        filter_upwards [eventually_ge_atTop (a - c)] with t ht
        linarith
      rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
      exact ⟨h1.mono_right le_sup_right, h2.mono_right le_sup_left⟩
    have hterm : Tendsto (fun t : ℝ => ρ (x i₀ - t)) (cocompact ℝ) atTop :=
      hρ_coer.comp (hmap (x i₀))
    -- One escaping term drives the whole sum, the others being bounded below.
    have hlow : ∀ t : ℝ, ρ (x i₀ - t) + ((n - 1 : ℕ) : ℝ) * b ≤ ∑ i, ρ (x i - t) := by
      intro t
      have hsplit : ∑ i, ρ (x i - t)
          = ρ (x i₀ - t) + ∑ i ∈ Finset.univ.erase i₀, ρ (x i - t) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
      have hrest : ((n - 1 : ℕ) : ℝ) * b ≤ ∑ i ∈ Finset.univ.erase i₀, ρ (x i - t) := by
        calc ((n - 1 : ℕ) : ℝ) * b = ∑ _i ∈ Finset.univ.erase i₀, b := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
                Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum fun i _ => hb' _
      rw [hsplit]
      linarith
    have hcoer : Tendsto (fun t : ℝ => ∑ i, ρ (x i - t)) (cocompact ℝ) atTop :=
      tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ _ hterm)
    obtain ⟨θ, hθ⟩ := hfc.exists_forall_le hcoer
    exact ⟨θ, fun t => hθ t⟩

/-- Auxiliary: the M-objective `t ↦ ∑ᵢ ρ(xᵢ - t)` is differentiable with derivative
`∑ᵢ -ψ(xᵢ - t)`, by the chain rule through the affine reparametrization `t ↦ xᵢ - t`.
(`HasDerivAt.sum` is stated for a `Pi`-valued sum of functions, so the sum has to be
pushed through the evaluation.) -/
private theorem hasDerivAt_mObjective {ρ ψ : ℝ → ℝ} (hρ : ∀ u, HasDerivAt ρ (ψ u) u)
    (x : Fin n → ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ i, ρ (x i - t)) (∑ i, -ψ (x i - θ)) θ := by
  have h : HasDerivAt (∑ i ∈ (Finset.univ : Finset (Fin n)), fun t : ℝ => ρ (x i - t))
      (∑ i, -ψ (x i - θ)) θ := by
    refine HasDerivAt.sum fun i _ => ?_
    have hinner : HasDerivAt (fun t : ℝ => x i - t) (-1 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_sub (x i)
    simpa [Function.comp_def] using (hρ (x i - θ)).comp θ hinner
  have hfun : (∑ i ∈ (Finset.univ : Finset (Fin n)), fun t : ℝ => ρ (x i - t))
      = fun t : ℝ => ∑ i, ρ (x i - t) := by
    funext t
    simp
  rwa [hfun] at h

/-- **The estimating equation** (`MMY §2.3.1`, eq. (2.19)): at an M-estimate for a
differentiable loss, the score sum vanishes, `∑ᵢ ψ(xᵢ - θ̂) = 0`. -/
theorem IsMLocationEstimate.score_eq_zero {ρ ψ : ℝ → ℝ} {x : Fin n → ℝ} {θ : ℝ}
    -- USER-INPUT: differentiable loss with score ψ = ρ'; MMY eq. (2.19)
    (hρ : ∀ u, HasDerivAt ρ (ψ u) u)
    (hθ : IsMLocationEstimate ρ x θ) :
    ∑ i, ψ (x i - θ) = 0 := by
  have hderiv : HasDerivAt (fun t : ℝ => ∑ i, ρ (x i - t)) (∑ i, -ψ (x i - θ)) θ :=
    hasDerivAt_mObjective hρ x θ
  have hmin : IsLocalMin (fun t : ℝ => ∑ i, ρ (x i - t)) θ :=
    Filter.Eventually.of_forall hθ
  simpa using hmin.hasDerivAt_eq_zero hderiv

/-- **The convex converse** (`MMY §2.4`, eq. (2.40) discussion): for convex differentiable
`ρ`, any root of the estimating equation is a global M-estimate. -/
theorem isMLocationEstimate_of_score_eq_zero {ρ ψ : ℝ → ℝ} {x : Fin n → ℝ} {θ : ℝ}
    -- USER-INPUT: convex loss; MMY §2.4 eq. (2.40)
    (hρ_conv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: differentiable loss with score ψ = ρ'; MMY eq. (2.19)
    (hρ : ∀ u, HasDerivAt ρ (ψ u) u)
    (hscore : ∑ i, ψ (x i - θ) = 0) :
    IsMLocationEstimate ρ x θ := by
  -- The objective is convex, being a sum of convex functions precomposed with `t ↦ xᵢ - t`.
  have hgconv : ConvexOn ℝ Set.univ (fun t : ℝ => ∑ i, ρ (x i - t)) := by
    refine ⟨convex_univ, ?_⟩
    intro p _ q _ a b ha hb hab
    simp only [smul_eq_mul]
    have hle : ∀ i : Fin n,
        ρ (x i - (a * p + b * q)) ≤ a * ρ (x i - p) + b * ρ (x i - q) := by
      intro i
      have hxe : x i - (a * p + b * q) = a * (x i - p) + b * (x i - q) := by
        linear_combination (-(x i)) * hab
      rw [hxe]
      simpa using hρ_conv.2 (Set.mem_univ (x i - p)) (Set.mem_univ (x i - q)) ha hb hab
    calc ∑ i, ρ (x i - (a * p + b * q))
        ≤ ∑ i, (a * ρ (x i - p) + b * ρ (x i - q)) := Finset.sum_le_sum fun i _ => hle i
      _ = a * (∑ i, ρ (x i - p)) + b * (∑ i, ρ (x i - q)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- The estimating equation says the derivative of the objective vanishes at `θ`.
  have hgderiv : HasDerivAt (fun t : ℝ => ∑ i, ρ (x i - t)) 0 θ := by
    have h : HasDerivAt (fun t : ℝ => ∑ i, ρ (x i - t)) (∑ i, -ψ (x i - θ)) θ :=
      hasDerivAt_mObjective hρ x θ
    have hz : (∑ i, -ψ (x i - θ)) = 0 := by simpa using hscore
    rwa [hz] at h
  -- A convex function with vanishing derivative at `θ` is minimized there.
  intro t
  rcases lt_trichotomy θ t with h | h | h
  · have hs := hgconv.le_slope_of_hasDerivAt (Set.mem_univ θ) (Set.mem_univ t) h hgderiv
    simp only [slope_def_field] at hs
    have hd : (0 : ℝ) < t - θ := by linarith
    have h2 := mul_nonneg hs hd.le
    rw [div_mul_cancel₀ _ (ne_of_gt hd)] at h2
    linarith
  · rw [h]
  · have hs := hgconv.slope_le_of_hasDerivAt (Set.mem_univ t) (Set.mem_univ θ) h hgderiv
    simp only [slope_def_field] at hs
    have hd : (0 : ℝ) < θ - t := by linarith
    have h2 := mul_le_mul_of_nonneg_right hs hd.le
    rw [div_mul_cancel₀ _ (ne_of_gt hd), zero_mul] at h2
    linarith

/-- **Shift equivariance of the M-estimate correspondence** (`MMY §2.3.1`, Problem 2.5):
`θ + a` is an M-estimate for the shifted sample `x + a·𝟙` iff `θ` is one for `x`. -/
theorem isMLocationEstimate_comp_add {ρ : ℝ → ℝ} {x : Fin n → ℝ} {θ a : ℝ} :
    IsMLocationEstimate ρ (x + a • (1 : Fin n → ℝ)) (θ + a) ↔ IsMLocationEstimate ρ x θ := by
  have key : ∀ t : ℝ,
      ∑ i, ρ ((x + a • (1 : Fin n → ℝ)) i - t) = ∑ i, ρ (x i - (t - a)) := by
    intro t
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    ring
  constructor
  · intro h t
    have h2 := h (t + a)
    rw [key (θ + a), key (t + a)] at h2
    simpa using h2
  · intro h t
    have h2 := h (t - a)
    rw [key (θ + a), key t]
    simpa using h2

/-- **Squared loss recovers the sample mean** (`MMY §2.3.1`, eq. (2.16)): for `n ≥ 1`,
`θ` minimizes `∑ (xᵢ - θ)²` iff `θ = x̄`. -/
theorem isMLocationEstimate_sq_iff {x : Fin n → ℝ} {θ : ℝ} (hn : 0 < n) :
    IsMLocationEstimate (fun u => u ^ 2) x θ ↔ θ = sampleMean x := by
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum0 : ∑ i, (x i - sampleMean x) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    simp only [sampleMean]
    field_simp
    ring
  -- The bias–variance split of the least-squares objective.
  have key : ∀ t : ℝ, ∑ i, (x i - t) ^ 2
      = (∑ i, (x i - sampleMean x) ^ 2) + (n : ℝ) * (sampleMean x - t) ^ 2 := by
    intro t
    calc ∑ i, (x i - t) ^ 2
        = ∑ i, ((x i - sampleMean x) ^ 2 + (2 * (sampleMean x - t)) * (x i - sampleMean x)
            + (sampleMean x - t) ^ 2) := Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, (x i - sampleMean x) ^ 2)
            + (2 * (sampleMean x - t)) * (∑ i, (x i - sampleMean x))
            + (n : ℝ) * (sampleMean x - t) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := by rw [hsum0]; ring
  constructor
  · intro h
    have h1 : (∑ i, (x i - θ) ^ 2) ≤ ∑ i, (x i - sampleMean x) ^ 2 := h (sampleMean x)
    rw [key θ] at h1
    have h2 : (sampleMean x - θ) ^ 2 ≤ 0 := by nlinarith
    have h3 : sampleMean x - θ = 0 := by nlinarith [sq_nonneg (sampleMean x - θ)]
    linarith
  · rintro rfl
    intro t
    change (∑ i, (x i - sampleMean x) ^ 2) ≤ ∑ i, (x i - t) ^ 2
    rw [key t]
    nlinarith [sq_nonneg (sampleMean x - t)]

/-- Auxiliary counting step for the L¹ objective: moving the location from `m` to a larger
`t` cannot decrease the objective as soon as at least half the observations are `≤ m`.

Each observation `≤ m` pays exactly `t - m` for the move, while every observation pays at
most `t - m` in the other direction (the reverse triangle inequality), so the net change is
at least `(t - m)·(#{yⱼ ≤ m} - #{yⱼ > m}) ≥ 0`. -/
private theorem sum_abs_le_of_card_le (y : Fin n → ℝ) {m t : ℝ} (hmt : m < t)
    (hcnt : n ≤ 2 * (Finset.univ.filter fun j => y j ≤ m).card) :
    ∑ i, |y i - m| ≤ ∑ i, |y i - t| := by
  have hterm : ∀ i : Fin n,
      |y i - m| - |y i - t| ≤ (if y i ≤ m then -(t - m) else t - m) := by
    intro i
    by_cases hi : y i ≤ m
    · rw [if_pos hi, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [if_neg hi]
      have h1 := abs_sub_abs_le_abs_sub (y i - m) (y i - t)
      have h2 : |y i - m - (y i - t)| = t - m := by
        rw [show y i - m - (y i - t) = t - m by ring, abs_of_pos (by linarith)]
      linarith
  have hsum : ∑ i, (|y i - m| - |y i - t|)
      ≤ ∑ i, (if y i ≤ m then -(t - m) else t - m) :=
    Finset.sum_le_sum fun i _ => hterm i
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul] at hsum
  have hcard : (Finset.univ.filter fun j : Fin n => y j ≤ m).card
      + (Finset.univ.filter fun j : Fin n => ¬ y j ≤ m).card = n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hle : ((Finset.univ.filter fun j : Fin n => ¬ y j ≤ m).card : ℝ)
      ≤ ((Finset.univ.filter fun j : Fin n => y j ≤ m).card : ℝ) := by
    have : (Finset.univ.filter fun j : Fin n => ¬ y j ≤ m).card
        ≤ (Finset.univ.filter fun j : Fin n => y j ≤ m).card := by omega
    exact_mod_cast this
  nlinarith [hsum, hle, sub_pos.2 hmt]

/-- **The median minimizes the L¹ objective** (`MMY §2.3.1`, eq. (2.18), (2.21)): the
sample median is an M-estimate for the absolute-value loss. (For even `n` the low median
is one of the minimizers.) -/
theorem isMLocationEstimate_abs_sampleMedian (x : Fin n → ℝ) :
    IsMLocationEstimate (fun u => |u|) x (sampleMedian x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro t; simp
  intro t
  change (∑ i, |x i - sampleMedian x|) ≤ ∑ i, |x i - t|
  rcases lt_trichotomy t (sampleMedian x) with ht | ht | ht
  · -- Below the median: reflect and use the count of observations `≥ m`.
    have hset : (Finset.univ.filter fun j : Fin n => -x j ≤ -sampleMedian x)
        = (Finset.univ.filter fun j : Fin n => sampleMedian x ≤ x j) := by
      ext j
      simp [neg_le_neg_iff]
    have hcnt : n ≤ 2 * (Finset.univ.filter fun j : Fin n => -x j ≤ -sampleMedian x).card := by
      rw [hset]
      have h := card_sampleMedian_le hn.ne' x
      omega
    have hmain := sum_abs_le_of_card_le (fun i => -x i)
      (m := -sampleMedian x) (t := -t) (by linarith) hcnt
    calc ∑ i, |x i - sampleMedian x| = ∑ i, |(-x i) - (-sampleMedian x)| :=
          Finset.sum_congr rfl fun i _ => by
            rw [show -x i - -sampleMedian x = -(x i - sampleMedian x) by ring, abs_neg]
      _ ≤ ∑ i, |(-x i) - (-t)| := hmain
      _ = ∑ i, |x i - t| :=
          Finset.sum_congr rfl fun i _ => by
            rw [show -x i - -t = -(x i - t) by ring, abs_neg]
  · rw [ht]
  · -- Above the median: the count of observations `≤ m` is at least half.
    have hcnt : n ≤ 2 * (Finset.univ.filter fun j : Fin n => x j ≤ sampleMedian x).card := by
      have h := card_le_sampleMedian hn.ne' x
      omega
    exact sum_abs_le_of_card_le x ht hcnt

/-! ### Huber location estimates (`MMY §2.3.2`) -/

/-- Huber location estimates exist for every sample. -/
theorem exists_isMLocationEstimate_huber {c : ℝ} (hc : 0 < c) (x : Fin n → ℝ) :
    ∃ θ : ℝ, IsMLocationEstimate (huberRho c) x θ :=
  exists_isMLocationEstimate (huberRho_continuous hc.le) (huberRho_tendsto_cocompact hc)
    ⟨0, by rintro y ⟨u, rfl⟩; exact huberRho_nonneg hc.le u⟩ x

/-- **The Huber estimating equation** (`MMY` eq. (2.19) with eq. (2.29)): at a Huber
M-estimate, the clipped residuals sum to zero. -/
theorem IsMLocationEstimate.huber_score_eq_zero {c : ℝ} (hc : 0 ≤ c) {x : Fin n → ℝ}
    {θ : ℝ} (hθ : IsMLocationEstimate (huberRho c) x θ) :
    ∑ i, huberPsi c (x i - θ) = 0 :=
  hθ.score_eq_zero (hasDerivAt_huberRho hc)

/-- **A Huber score root is a Huber M-estimate** (convexity of `ρ_c`). -/
theorem isMLocationEstimate_huber_of_score_eq_zero {c : ℝ} (hc : 0 ≤ c) {x : Fin n → ℝ}
    {θ : ℝ} (hscore : ∑ i, huberPsi c (x i - θ) = 0) :
    IsMLocationEstimate (huberRho c) x θ :=
  isMLocationEstimate_of_score_eq_zero (huberRho_convex hc) (hasDerivAt_huberRho hc) hscore

end StatLean.RobustStatistics
