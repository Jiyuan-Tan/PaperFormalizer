module
public import StatLean.Bayesian.BernsteinVonMises.Defs
public import StatLean.Bayesian.BernsteinVonMises.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-!
# Prior small-ball bounds and the exponential tail split

Quantitative consequences of the prior condition of the Bernstein–von Mises theorem
(`HasLocalDensity`):

* `prior_ball_inv_sqrt_lower` — the small-ball lower bound
  `π(B(θ₀, u/√n)) ≳ n^{-k/2}` (continuity and positivity of the density at `θ₀`);
* `prior_smallBall_upper` / `prior_smallBall_lower` — two-sided volume comparison of `π`
  with Lebesgue measure on a small ball around `θ₀`;
* `prior_tail_split` — the Step-A tail estimate (vdV p. 142, last display):
  `√nᵏ · ∫_{‖θ−θ₀‖ ≥ Mₙ/√n} exp(−c n (‖θ−θ₀‖² ∧ 1)) dπ(θ) → 0` for every `Mₙ → ∞`,
  by splitting at a fixed radius `D` where the density is bounded (moderate zone: Gaussian
  integral; far zone: `√nᵏ e^{−cn} → 0`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, p. 142 (the displays following "Combining the preceding displays").

**Proof formalization notes.** All statements are about the prior alone — no sampling model
appears. The `n^{-k/2}` normalizations are kept explicit (no rescaled-prior object is
introduced); `volume` is Lebesgue measure on `EuclideanSpace ℝ (Fin k)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Pointwise

namespace StatLean.Bayesian

variable {k : ℕ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- Continuity and positivity of `f` at `θ₀` give a radius `D ≤ r₀` on which the density is
squeezed between `f θ₀ / 2` and `2 f θ₀`. -/
private lemma exists_density_envelope (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧
      (∀ θ ∈ Metric.ball θ₀ D, f θ ≤ 2 * f θ₀) ∧
      (∀ θ ∈ Metric.ball θ₀ D, f θ₀ / 2 ≤ f θ) := by
  have hpos := hπ.pos
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.continuousAt_iff.1 hπ.continuousAt (f θ₀ / 2) (by linarith)
  refine ⟨min δ r₀, lt_min hδ hπ.rad_pos, min_le_right _ _, ?_, ?_⟩ <;>
    intro θ hθ
  · have h1 : dist θ θ₀ < δ := lt_of_lt_of_le (Metric.mem_ball.1 hθ) (min_le_left _ _)
    have := hδf h1
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).2
    linarith
  · have h1 : dist θ θ₀ < δ := lt_of_lt_of_le (Metric.mem_ball.1 hθ) (min_le_left _ _)
    have := hδf h1
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).1
    linarith

/-- The prior integral over a small measurable subset of `B(θ₀, r₀)` unfolds to a Lebesgue
integral of the density. -/
private lemma prior_setLIntegral_eq (hπ : HasLocalDensity π θ₀ r₀ f)
    {s : Set (EuclideanSpace ℝ (Fin k))} (hs : s ⊆ Metric.ball θ₀ r₀) (hsm : MeasurableSet s) :
    π s = ∫⁻ θ in s, ENNReal.ofReal (f θ) ∂volume := by
  have h1 : π s = π.restrict (Metric.ball θ₀ r₀) s := by
    rw [Measure.restrict_apply hsm, Set.inter_eq_self_of_subset_left hs]
  rw [h1, hπ.restrict_eq, withDensity_apply _ hsm, Measure.restrict_restrict hsm,
    Set.inter_eq_self_of_subset_left hs]

/-- Volume of a ball in `ℝᵏ` in terms of the unit ball (stated without `[Nontrivial]`, so that
the degenerate case `k = 0` is covered). -/
private lemma volume_ball_eq_ofReal_pow (x : EuclideanSpace ℝ (Fin k)) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x r)
      = ENNReal.ofReal (r ^ k) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r
      = r • Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    rw [smul_ball hr.ne' (0 : EuclideanSpace ℝ (Fin k)) 1, smul_zero,
      Real.norm_eq_abs, abs_of_pos hr, mul_one]
  rw [Measure.addHaar_ball_center, hball,
    Measure.addHaar_smul_of_nonneg (volume : Measure (EuclideanSpace ℝ (Fin k))) hr.le,
    finrank_euclideanSpace_fin]

/-- The lower volume comparison, extracted so that both `prior_ball_inv_sqrt_lower` and
`prior_smallBall_lower` can use it. -/
private lemma prior_smallBall_lower_aux (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧ ∃ cb : ℝ≥0∞, 0 < cb ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
        cb * volume s ≤ π s := by
  obtain ⟨D, hD, hDr, _, hlow⟩ := exists_density_envelope hπ
  refine ⟨D, hD, hDr, ENNReal.ofReal (f θ₀ / 2), ?_, ?_⟩
  · exact ENNReal.ofReal_pos.2 (by linarith [hπ.pos])
  intro s hs hsm
  have hsr : s ⊆ Metric.ball θ₀ r₀ := hs.trans (Metric.ball_subset_ball hDr)
  rw [prior_setLIntegral_eq hπ hsr hsm, ← setLIntegral_const s (ENNReal.ofReal (f θ₀ / 2))]
  exact setLIntegral_mono hπ.measurable.ennreal_ofReal fun θ hθ =>
    ENNReal.ofReal_le_ofReal (hlow θ (hs hθ))

/-- **Prior small-ball lower bound** (vdV p. 142: `Π_n(U) ≳ (1/√n)ᵏ`): under the prior
condition, for every fixed `u > 0` there is `c > 0` with
`c · (√n)⁻ᵏ ≤ π(B(θ₀, u/√n))` for all large `n`. -/
theorem prior_ball_inv_sqrt_lower
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {u : ℝ}
    -- LEAN-ONLY: nontrivial ball radius
    (hu : 0 < u) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) ≤ π (Metric.ball θ₀ (u / Real.sqrt n)) := by
  obtain ⟨D, hD, _, cb, hcb, hbound⟩ := prior_smallBall_lower_aux hπ
  set V₁ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) with hV₁
  have hV₁pos : 0 < V₁ := Metric.measure_ball_pos _ _ one_pos
  refine ⟨cb * ENNReal.ofReal (u ^ k) * V₁, ?_, ?_⟩
  · exact ENNReal.mul_pos
      (ENNReal.mul_pos hcb.ne' (ENNReal.ofReal_pos.2 (by positivity)).ne').ne' hV₁pos.ne'
  -- eventually `u / √n ≤ D` and `n ≥ 1`
  have hsq : Tendsto (fun n : ℕ => u / Real.sqrt n) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa using h.const_div_atTop u
  filter_upwards [hsq.eventually (eventually_le_nhds hD), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hrpos : 0 < u / Real.sqrt n := div_pos hu hsqrt
  have hsub : Metric.ball θ₀ (u / Real.sqrt n) ⊆ Metric.ball θ₀ D := Metric.ball_subset_ball hn
  have hvol := volume_ball_eq_ofReal_pow θ₀ hrpos
  have hkey : ENNReal.ofReal ((u / Real.sqrt n) ^ k)
      = ENNReal.ofReal (u ^ k) * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow, inv_pow]
    ring
  calc cb * ENNReal.ofReal (u ^ k) * V₁ * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
      = cb * (ENNReal.ofReal ((u / Real.sqrt n) ^ k) * V₁) := by rw [hkey]; ring
    _ = cb * volume (Metric.ball θ₀ (u / Real.sqrt n)) := by rw [hvol]
    _ ≤ π (Metric.ball θ₀ (u / Real.sqrt n)) :=
        hbound _ hsub Metric.isOpen_ball.measurableSet

/-- **Local volume upper comparison**: near `θ₀` the prior is dominated by a multiple of
Lebesgue measure (density bounded by continuity at `θ₀`). Returns a radius `D ≤ r₀` on which
the comparison holds. -/
theorem prior_smallBall_upper
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧ ∃ Cb : ℝ≥0∞, Cb ≠ ∞ ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
        π s ≤ Cb * volume s := by
  obtain ⟨D, hD, hDr, hup, _⟩ := exists_density_envelope hπ
  refine ⟨D, hD, hDr, ENNReal.ofReal (2 * f θ₀), ENNReal.ofReal_ne_top, ?_⟩
  intro s hs hsm
  have hsr : s ⊆ Metric.ball θ₀ r₀ := hs.trans (Metric.ball_subset_ball hDr)
  rw [prior_setLIntegral_eq hπ hsr hsm, ← setLIntegral_const s (ENNReal.ofReal (2 * f θ₀))]
  exact setLIntegral_mono measurable_const fun θ hθ =>
    ENNReal.ofReal_le_ofReal (hup θ (hs hθ))

/-- **Local volume lower comparison**: near `θ₀` the prior dominates a positive multiple of
Lebesgue measure (density positive by continuity at `θ₀`). -/
theorem prior_smallBall_lower
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧ ∃ cb : ℝ≥0∞, 0 < cb ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
        cb * volume s ≤ π s :=
  prior_smallBall_lower_aux hπ

/-- The multivariate Gaussian kernel is integrable on `ℝᵏ` (real part of the complex Gaussian
integrability lemma). -/
private lemma integrable_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : EuclideanSpace ℝ (Fin k) => Real.exp (-c * ‖v‖ ^ 2)) := by
  have hb : 0 < ((c : ℂ)).re := by simpa using hc
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin k)) hb 0 (0 : EuclideanSpace ℝ (Fin k))).norm
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  have hre : (-(c : ℂ) * ((‖v‖ : ℝ) : ℂ) ^ 2) = ((-c * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hre, Complex.ofReal_re]

/-- The total mass of the Gaussian kernel is finite. -/
private lemma lintegral_exp_neg_mul_sq_norm_ne_top {c : ℝ} (hc : 0 < c) :
    ∫⁻ v : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp (-c * ‖v‖ ^ 2)) ≠ ∞ := by
  have h := (integrable_exp_neg_mul_sq_norm (k := k) hc).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm,
    lintegral_enorm_of_nonneg (fun v => (Real.exp_pos _).le)] at h
  exact h.ne

/-- **The Gaussian tail vanishes**: `∫_{‖h‖ ≥ Mₙ} e^{−c‖h‖²} dh → 0` whenever `Mₙ → ∞`. -/
private lemma gaussian_tail_tendsto {c : ℝ} (hc : 0 < c) {Mseq : ℕ → ℝ}
    (hM : Tendsto Mseq atTop atTop) :
    Tendsto (fun n : ℕ => ∫⁻ v in {v : EuclideanSpace ℝ (Fin k) | Mseq n ≤ ‖v‖},
        ENNReal.ofReal (Real.exp (-c * ‖v‖ ^ 2))) atTop (𝓝 0) := by
  set ν : Measure (EuclideanSpace ℝ (Fin k)) :=
    volume.withDensity (fun v => ENNReal.ofReal (Real.exp (-c * ‖v‖ ^ 2))) with hνdef
  have hνapply : ∀ s : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet s →
      ν s = ∫⁻ v in s, ENNReal.ofReal (Real.exp (-c * ‖v‖ ^ 2)) :=
    fun s hs => withDensity_apply _ hs
  set T : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun j => {v | (j : ℝ) ≤ ‖v‖} with hTdef
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    measurableSet_le measurable_const (by fun_prop)
  have hTanti : Antitone T := by
    intro i j hij v hv
    simp only [hTdef, Set.mem_setOf_eq] at hv ⊢
    exact le_trans (by exact_mod_cast hij) hv
  have hTinter : (⋂ j, T j) = (∅ : Set (EuclideanSpace ℝ (Fin k))) := by
    ext v
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨j, hj⟩ := exists_nat_gt ‖v‖
    exact ⟨j, by simpa [hTdef] using hj⟩
  have hfin : ν (T 0) ≠ ∞ := by
    rw [hνapply _ (hTm 0)]
    exact ne_top_of_le_ne_top (lintegral_exp_neg_mul_sq_norm_ne_top hc)
      (setLIntegral_le_lintegral _ _)
  have hlim : Tendsto (fun j => ν (T j)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := ν) (fun j => (hTm j).nullMeasurableSet)
      hTanti ⟨0, hfin⟩
    rwa [hTinter, measure_empty] at this
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨j, hj⟩ := (ENNReal.tendsto_nhds_zero.1 hlim ε hε).exists
  filter_upwards [hM.eventually_ge_atTop (j : ℝ)] with n hn
  rw [← hνapply _ (measurableSet_le measurable_const (by fun_prop))]
  exact le_trans (measure_mono fun v hv => le_trans hn hv) hj

/-- `√nᵏ · e^{−c n D²} → 0`. -/
private lemma poly_mul_exp_neg_tendsto {k : ℕ} {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    Tendsto (fun n : ℕ => Real.sqrt n ^ k * Real.exp (-c * n * D ^ 2)) atTop (𝓝 0) := by
  set b : ℝ := c * D ^ 2 with hbdef
  have hb : 0 < b := by positivity
  have hbk : (b : ℝ) ^ k ≠ 0 := pow_ne_zero k hb.ne'
  have hmaj : Tendsto (fun n : ℕ => (b ^ k)⁻¹ * ((b * Real.sqrt n) ^ k *
      Real.exp (-(b * Real.sqrt n)))) atTop (𝓝 0) := by
    have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun n : ℕ => b * Real.sqrt n) atTop atTop :=
      hsqrtTop.const_mul_atTop hb
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp h0
    simpa [Function.comp_def] using
      (tendsto_const_nhds (x := (b ^ k)⁻¹) (f := atTop (α := ℕ))).mul h1
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hnR
  have hn2 : Real.sqrt n ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n : ℝ) by positivity)]
  have hexp : Real.exp (-c * n * D ^ 2) ≤ Real.exp (-(b * Real.sqrt n)) := by
    refine Real.exp_le_exp.2 ?_
    have : b * Real.sqrt n ≤ b * n := by gcongr
    nlinarith
  calc Real.sqrt n ^ k * Real.exp (-c * n * D ^ 2)
      ≤ Real.sqrt n ^ k * Real.exp (-(b * Real.sqrt n)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (b ^ k)⁻¹ * ((b * Real.sqrt n) ^ k * Real.exp (-(b * Real.sqrt n))) := by
        rw [mul_pow b (Real.sqrt n) k, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hbk,
          one_mul]

/-- Set-level domination of measures upgrades to a domination of `lintegral`s. -/
private lemma lintegral_le_of_setMeasure_le {α : Type*} [MeasurableSpace α]
    {μ' ν' : Measure α} {Cb : ℝ≥0∞} {s : Set α}
    (h : ∀ t, t ⊆ s → MeasurableSet t → μ' t ≤ Cb * ν' t) (hs : MeasurableSet s)
    (G : α → ℝ≥0∞) :
    ∫⁻ a in s, G a ∂μ' ≤ Cb * ∫⁻ a in s, G a ∂ν' := by
  have hle : μ'.restrict s ≤ Cb • ν'.restrict s := by
    refine Measure.le_iff.2 fun t htm => ?_
    rw [Measure.restrict_apply htm, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply htm]
    exact h _ Set.inter_subset_right (htm.inter hs)
  calc ∫⁻ a in s, G a ∂μ' ≤ ∫⁻ a, G a ∂(Cb • ν'.restrict s) := lintegral_mono' hle le_rfl
    _ = Cb * ∫⁻ a in s, G a ∂ν' := lintegral_smul_measure _ _

/-- **Change of variables `h = √n(θ − θ₀)` on the moderate zone**. -/
private lemma moderate_zone_bound {c : ℝ} {n : ℕ}
    -- LEAN-ONLY: `√n ≠ 0`
    (hn : 1 ≤ n) (R : ℝ) (θ₀ : EuclideanSpace ℝ (Fin k))
    {s : Set (EuclideanSpace ℝ (Fin k))} (hsm : MeasurableSet s)
    (hsR : ∀ θ ∈ s, R / Real.sqrt n ≤ ‖θ - θ₀‖) :
    ∫⁻ θ in s, ENNReal.ofReal (Real.exp (-c * n * ‖θ - θ₀‖ ^ 2)) ∂volume
      ≤ ENNReal.ofReal ((Real.sqrt n ^ k)⁻¹) *
          ∫⁻ v in {v : EuclideanSpace ℝ (Fin k) | R ≤ ‖v‖},
            ENNReal.ofReal (Real.exp (-c * ‖v‖ ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsqsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  set T : Set (EuclideanSpace ℝ (Fin k)) := {v | R ≤ ‖v‖} with hTdef
  have hTm : MeasurableSet T := measurableSet_le measurable_const (by fun_prop)
  set G : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (-c * ‖v‖ ^ 2)) with hGdef
  have hGm : Measurable G := by rw [hGdef]; fun_prop
  have hmapL : Measure.map (fun θ : EuclideanSpace ℝ (Fin k) => Real.sqrt n • (θ - θ₀))
      (volume : Measure (EuclideanSpace ℝ (Fin k)))
      = ENNReal.ofReal ((Real.sqrt n ^ k)⁻¹) • volume := by
    have h1 : Measure.map (fun θ : EuclideanSpace ℝ (Fin k) => θ - θ₀) volume = volume :=
      (measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin k))) θ₀).map_eq
    have h2 : (fun θ : EuclideanSpace ℝ (Fin k) => Real.sqrt n • (θ - θ₀))
        = (fun x : EuclideanSpace ℝ (Fin k) => Real.sqrt n • x)
          ∘ (fun θ : EuclideanSpace ℝ (Fin k) => θ - θ₀) := rfl
    rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), h1,
      Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin k))) hsq.ne',
      finrank_euclideanSpace_fin,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt n ^ k)⁻¹)]
  have key : ENNReal.ofReal ((Real.sqrt n ^ k)⁻¹) * ∫⁻ v in T, G v
      = ∫⁻ θ, T.indicator G (Real.sqrt n • (θ - θ₀)) ∂volume := by
    have := lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin k))))
      (f := T.indicator G) (g := fun θ : EuclideanSpace ℝ (Fin k) => Real.sqrt n • (θ - θ₀))
      (hGm.indicator hTm) (by fun_prop)
    rw [hmapL, lintegral_smul_measure, lintegral_indicator hTm] at this
    exact this
  rw [key]
  rw [← lintegral_indicator hsm]
  refine lintegral_mono fun θ => ?_
  by_cases hθ : θ ∈ s
  · rw [Set.indicator_of_mem hθ]
    have hnorm : ‖Real.sqrt n • (θ - θ₀)‖ = Real.sqrt n * ‖θ - θ₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq.le]
    have hmem : Real.sqrt n • (θ - θ₀) ∈ T := by
      rw [hTdef, Set.mem_setOf_eq, hnorm]
      have := hsR θ hθ
      rw [div_le_iff₀ hsq] at this
      linarith [this]
    rw [Set.indicator_of_mem hmem, hGdef]
    simp only
    rw [hnorm, mul_pow, hsqsq]
    ring_nf
    exact le_rfl
  · rw [Set.indicator_of_notMem hθ]
    exact zero_le

/-- **The Step-A tail split** (vdV p. 142, final display of the concentration step): for every
exponent `c > 0` and every `Mₙ → ∞`,
`(√n)ᵏ · ∫_{‖θ−θ₀‖ ≥ Mₙ/√n} exp(−c n (‖θ−θ₀‖² ∧ 1)) dπ(θ) → 0`.
Split at a radius `D` from `prior_smallBall_upper`: on the moderate zone substitute the
density bound and compare with the Gaussian integral `∫_{‖h‖ ≥ Mₙ} e^{−c‖h‖²} dh → 0`; on
the far zone bound by `(√n)ᵏ e^{−c n D²} · π(univ) → 0`. -/
theorem prior_tail_split
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {c : ℝ}
    -- LEAN-ONLY: positive exponential rate (supplied by the exponential-tests lemma)
    (hc : 0 < c) {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV §10.2, p. 141 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop) :
    Tendsto (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt n ^ k) *
          ∫⁻ θ in {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
            ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
      atTop (𝓝 0) := by
  classical
  -- the density-comparison radius, shrunk to `≤ 1`
  obtain ⟨D₀, hD₀, _, Cb, hCbtop, hCb⟩ := prior_smallBall_upper hπ
  set D : ℝ := min D₀ 1 with hDdef
  have hD : 0 < D := lt_min hD₀ one_pos
  have hD1 : D ≤ 1 := min_le_right _ _
  have hCb' : ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
      π s ≤ Cb * volume s := fun s hs hsm =>
    hCb s (hs.trans (Metric.ball_subset_ball (min_le_left _ _))) hsm
  set g : ℕ → EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := fun n θ =>
    ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) with hgdef
  set S : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖}
    with hSdef
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le measurable_const (by fun_prop)
  set tail : ℕ → ℝ≥0∞ := fun n => ∫⁻ v in {v : EuclideanSpace ℝ (Fin k) | Mseq n ≤ ‖v‖},
    ENNReal.ofReal (Real.exp (-c * ‖v‖ ^ 2)) with htaildef
  -- the dominating sequence
  set bound : ℕ → ℝ≥0∞ := fun n =>
    Cb * tail n + ENNReal.ofReal (Real.sqrt n ^ k * Real.exp (-c * n * D ^ 2)) with hbdef
  have hbound0 : Tendsto bound atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => Cb * tail n) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := Cb) (gaussian_tail_tendsto (k := k) hc hM)
        (Or.inr hCbtop)
      rw [mul_zero] at h
      exact h
    have h2 : Tendsto (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt n ^ k * Real.exp (-c * n * D ^ 2))) atTop (𝓝 0) := by
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp
        (poly_mul_exp_neg_tendsto (k := k) hc hD)
      rw [ENNReal.ofReal_zero] at h
      exact h
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound0
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsk : (0 : ℝ) < Real.sqrt n ^ k := pow_pos hs k
  set A : Set (EuclideanSpace ℝ (Fin k)) := S n ∩ Metric.ball θ₀ D with hAdef
  set B : Set (EuclideanSpace ℝ (Fin k)) := S n \ Metric.ball θ₀ D with hBdef
  have hAm : MeasurableSet A := (hSm n).inter Metric.isOpen_ball.measurableSet
  have hBm : MeasurableSet B := (hSm n).diff Metric.isOpen_ball.measurableSet
  -- split the integral
  have hsplit : ∫⁻ θ in S n, g n θ ∂π ≤ ∫⁻ θ in A, g n θ ∂π + ∫⁻ θ in B, g n θ ∂π := by
    have hSAB : S n = A ∪ B := by rw [hAdef, hBdef, Set.inter_union_diff]
    rw [hSAB]
    exact lintegral_union_le _ _ _
  -- moderate zone
  have hmod : ENNReal.ofReal (Real.sqrt n ^ k) * ∫⁻ θ in A, g n θ ∂π ≤ Cb * tail n := by
    have hstep1 : ∫⁻ θ in A, g n θ ∂π ≤ Cb * ∫⁻ θ in A, g n θ ∂volume :=
      lintegral_le_of_setMeasure_le (fun t ht htm => hCb' t (ht.trans Set.inter_subset_right) htm)
        hAm _
    have hcongr : ∫⁻ θ in A, g n θ ∂volume
        = ∫⁻ θ in A, ENNReal.ofReal (Real.exp (-c * n * ‖θ - θ₀‖ ^ 2)) ∂volume := by
      refine setLIntegral_congr_fun hAm fun θ hθ => ?_
      have h1 : ‖θ - θ₀‖ < D := by
        have := hθ.2
        rwa [Metric.mem_ball, dist_eq_norm] at this
      have h2 : ‖θ - θ₀‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg (θ - θ₀)]
      rw [hgdef]
      simp only [min_eq_left h2]
    have hstep2 : ∫⁻ θ in A, ENNReal.ofReal (Real.exp (-c * n * ‖θ - θ₀‖ ^ 2)) ∂volume
        ≤ ENNReal.ofReal ((Real.sqrt n ^ k)⁻¹) * tail n :=
      moderate_zone_bound hn (Mseq n) θ₀ hAm (fun θ hθ => hθ.1)
    have hstep3 : ∫⁻ θ in A, g n θ ∂π
        ≤ Cb * (ENNReal.ofReal ((Real.sqrt n ^ k)⁻¹) * tail n) := by
      refine hstep1.trans ?_
      gcongr
      exact hcongr.trans_le hstep2
    calc ENNReal.ofReal (Real.sqrt n ^ k) * ∫⁻ θ in A, g n θ ∂π
        ≤ ENNReal.ofReal (Real.sqrt n ^ k) *
            (Cb * (ENNReal.ofReal ((Real.sqrt n ^ k)⁻¹) * tail n)) := by
          gcongr
      _ = (ENNReal.ofReal (Real.sqrt n ^ k) * ENNReal.ofReal ((Real.sqrt n ^ k)⁻¹)) *
            (Cb * tail n) := by ring
      _ = Cb * tail n := by
          rw [← ENNReal.ofReal_mul hsk.le, mul_inv_cancel₀ hsk.ne', ENNReal.ofReal_one, one_mul]
  -- far zone
  have hfar : ENNReal.ofReal (Real.sqrt n ^ k) * ∫⁻ θ in B, g n θ ∂π
      ≤ ENNReal.ofReal (Real.sqrt n ^ k * Real.exp (-c * n * D ^ 2)) := by
    have hpt : ∀ θ ∈ B, g n θ ≤ ENNReal.ofReal (Real.exp (-c * n * D ^ 2)) := by
      intro θ hθ
      have h1 : D ≤ ‖θ - θ₀‖ := by
        have := hθ.2
        simp only [Metric.mem_ball, dist_eq_norm, not_lt] at this
        exact this
      have h2 : D ^ 2 ≤ min (‖θ - θ₀‖ ^ 2) 1 := by
        refine le_min ?_ (by nlinarith)
        nlinarith
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have hcn : 0 ≤ c * n := by positivity
      nlinarith
    have h3 : ∫⁻ θ in B, g n θ ∂π ≤ ENNReal.ofReal (Real.exp (-c * n * D ^ 2)) := by
      calc ∫⁻ θ in B, g n θ ∂π
          ≤ ∫⁻ _ in B, ENNReal.ofReal (Real.exp (-c * n * D ^ 2)) ∂π :=
            setLIntegral_mono measurable_const hpt
        _ = ENNReal.ofReal (Real.exp (-c * n * D ^ 2)) * π B := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (Real.exp (-c * n * D ^ 2)) * 1 := by
            gcongr
            simpa using prob_le_one
        _ = ENNReal.ofReal (Real.exp (-c * n * D ^ 2)) := mul_one _
    calc ENNReal.ofReal (Real.sqrt n ^ k) * ∫⁻ θ in B, g n θ ∂π
        ≤ ENNReal.ofReal (Real.sqrt n ^ k) * ENNReal.ofReal (Real.exp (-c * n * D ^ 2)) := by
          gcongr
      _ = ENNReal.ofReal (Real.sqrt n ^ k * Real.exp (-c * n * D ^ 2)) :=
          (ENNReal.ofReal_mul hsk.le).symm
  calc ENNReal.ofReal (Real.sqrt n ^ k) * ∫⁻ θ in S n, g n θ ∂π
      ≤ ENNReal.ofReal (Real.sqrt n ^ k) *
          (∫⁻ θ in A, g n θ ∂π + ∫⁻ θ in B, g n θ ∂π) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt n ^ k) * ∫⁻ θ in A, g n θ ∂π
          + ENNReal.ofReal (Real.sqrt n ^ k) * ∫⁻ θ in B, g n θ ∂π := mul_add _ _ _
    _ ≤ bound n := add_le_add hmod hfar

end StatLean.Bayesian
