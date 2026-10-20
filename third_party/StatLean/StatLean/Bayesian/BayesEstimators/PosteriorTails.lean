module
public import StatLean.Bayesian.BayesEstimators.Defs
public import StatLean.Bayesian.BernsteinVonMises.PosteriorConcentration
public import StatLean.Bayesian.BernsteinVonMises.PriorSmallBall

@[expose] public section

/-!
# Negligibility of the posterior tails with polynomial weights

The first part of the proof of the Bayes-point-estimator theorem: for every `Mₙ → ∞`, the local
posterior
integral of the polynomial envelope `1 + ‖h‖ᵖ` outside the radius-`Mₙ` balls tends to zero
in `P^n_{θ₀}`-probability, provided the prior has a finite `p`-th moment. This strengthens
Step A of the Bernstein–von Mises theorem from posterior *masses* to *weighted* masses.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.3, proof of
Theorem 10.8, p. 148, display (10.9) and the paragraph deriving it.

**Proof formalization notes.** Identical architecture to `posterior_mass_compl_ball_tendsto`
(the tests kill the `{φₙ ≈ 1}` side; the mixture/Fubini bound handles the `(1 − φₙ)` side),
with the weight `1 + ‖h‖ᵖ` inserted in the Fubini bound and the prior `p`-moment
condition absorbing the polynomial factor in the tail split (vdV: "and use the fact that
`∫ ‖θ‖ᵖ dΠ(θ) < ∞`"). The envelope form suffices for every measurable `f` with
`|f| ≤ 1 + ‖·‖ᵖ` by monotonicity of the lintegral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-! ### Step 0: bookkeeping bricks -/

/-- The parameter-side tail set corresponding to the local ball `‖h‖ ≥ R`. -/
private def tailSet (θ₀ : EuclideanSpace ℝ (Fin k)) (R : ℝ) (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {θ | R / Real.sqrt n ≤ ‖θ - θ₀‖}

private theorem measurableSet_tailSet (θ₀ : EuclideanSpace ℝ (Fin k)) (R : ℝ) (n : ℕ) :
    MeasurableSet (tailSet θ₀ R n) :=
  measurableSet_le measurable_const (by fun_prop)

/-- **Weighted pushforward bookkeeping**: the weighted local-posterior integral over
`‖h‖ ≥ R` is the θ-posterior integral of the unscaled weight over `‖θ − θ₀‖ ≥ R/√n`. -/
private theorem lintegral_tail_bvmLocalPosterior {n : ℕ} (hn : 1 ≤ n) (ω : Fin n → 𝓧) (R : ℝ)
    {W : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hW : Measurable W) :
    ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ, W h
        ∂(bvmLocalPosterior κ π θ₀ n ω)
      = ∫⁻ θ, (tailSet θ₀ R n).indicator (fun θ => W (Real.sqrt n • (θ - θ₀))) θ
          ∂(((iidKernel κ n)†π) ω) := by
  have hpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hg : Measurable (bvmLocalScale θ₀ n) := measurable_bvmLocalScale θ₀ n
  have hSc : MeasurableSet ((Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ) :=
    Metric.isOpen_ball.measurableSet.compl
  have hpre : bvmLocalScale θ₀ n ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ
      = tailSet θ₀ R n := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt,
      bvmLocalScale, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos.le, tailSet,
      Set.mem_setOf_eq, div_le_iff₀ hpos]
    constructor <;> intro h <;> linarith
  rw [lintegral_indicator (measurableSet_tailSet θ₀ R n)]
  simp only [bvmLocalPosterior, Kernel.map_apply _ hg]
  rw [Measure.restrict_map hg hSc, lintegral_map hW hg, hpre]
  rfl

/-- Measurability in the sample of the weighted local-posterior tail integral. -/
private theorem measurable_lintegral_tail (n : ℕ) (R : ℝ)
    {W : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hW : Measurable W) :
    Measurable fun ω => ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ, W h
      ∂(bvmLocalPosterior κ π θ₀ n ω) := by
  have hSc : MeasurableSet ((Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ) :=
    Metric.isOpen_ball.measurableSet.compl
  simp_rw [← lintegral_indicator hSc]
  exact Measurable.lintegral_kernel_prod_right (κ := bvmLocalPosterior κ π θ₀ n)
    (f := fun _ h => (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ.indicator W h)
    ((hW.indicator hSc).comp measurable_snd)

/-- **The weighted disintegration identity** (the Fubini step of Step A, with a weight in
place of the set indicator): the predictive mean of `(posterior-integral of `w`) · G` is the
prior integral of `w · (P^n_θ-mean of G)`. -/
private theorem weighted_posterior_predictive_eq (n : ℕ)
    {w : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hw : Measurable w)
    {G : (Fin n → 𝓧) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, (∫⁻ θ, w θ ∂(((iidKernel κ n)†π) ω)) * G ω ∂(iidKernel κ n ∘ₘ π)
      = ∫⁻ θ, w θ * ∫⁻ ω, G ω ∂(iidKernel κ n θ) ∂π := by
  have hF : Measurable fun z : (Fin n → 𝓧) × EuclideanSpace ℝ (Fin k) => w z.2 * G z.1 :=
    (hw.comp measurable_snd).mul (hG.comp measurable_fst)
  have hF' : Measurable fun z : EuclideanSpace ℝ (Fin k) × (Fin n → 𝓧) => w z.1 * G z.2 :=
    (hw.comp measurable_fst).mul (hG.comp measurable_snd)
  calc ∫⁻ ω, (∫⁻ θ, w θ ∂(((iidKernel κ n)†π) ω)) * G ω ∂(iidKernel κ n ∘ₘ π)
      = ∫⁻ ω, ∫⁻ θ, w θ * G ω ∂(((iidKernel κ n)†π) ω) ∂(iidKernel κ n ∘ₘ π) :=
        lintegral_congr fun ω => (lintegral_mul_const _ hw).symm
    _ = ∫⁻ z, w z.2 * G z.1 ∂((iidKernel κ n ∘ₘ π) ⊗ₘ ((iidKernel κ n)†π)) :=
        (Measure.lintegral_compProd hF).symm
    _ = ∫⁻ z, w z.2 * G z.1 ∂((π ⊗ₘ iidKernel κ n).map Prod.swap) := by
        rw [compProd_posterior_eq_map_swap]
    _ = ∫⁻ y, w y.1 * G y.2 ∂(π ⊗ₘ iidKernel κ n) := by
        rw [lintegral_map hF measurable_swap]
        simp
    _ = ∫⁻ θ, ∫⁻ ω, w θ * G ω ∂(iidKernel κ n θ) ∂π := Measure.lintegral_compProd hF'
    _ = ∫⁻ θ, w θ * ∫⁻ ω, G ω ∂(iidKernel κ n θ) ∂π :=
        lintegral_congr fun θ => lintegral_const_mul _ hG

/-- The localized mixture is dominated by the predictive with constant `π(B)⁻¹`. -/
private theorem lintegral_bvmMixture_le (u : ℝ) (n : ℕ) {G : (Fin n → 𝓧) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ ω, G ω ∂(bvmMixture κ π θ₀ u n)
      ≤ (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹ * ∫⁻ ω, G ω ∂(iidKernel κ n ∘ₘ π) := by
  simp only [bvmMixture, ProbabilityTheory.cond]
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hG.aemeasurable,
    Measure.lintegral_bind (Kernel.aemeasurable _) hG.aemeasurable, lintegral_smul_measure]
  exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-! ### Step 1: the weighted prior tail estimate -/

/-- `t ↦ t ^ p` is continuous for `0 ≤ p` (`rpow`). -/
private lemma continuous_rpow_const_of_nonneg {p : ℝ} (hp : 0 ≤ p) :
    Continuous fun t : ℝ => t ^ p :=
  continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x p (Or.inr hp)

private lemma tendsto_exp_neg_half_mul :
    Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (-(1 / 2) : ℝ) * x) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0)).2 tendsto_id
  exact Real.tendsto_exp_atBot.comp h

/-- A polynomial times a Gaussian is bounded on `[0, ∞)`. -/
private theorem exists_poly_exp_bound {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t → (1 + t ^ p) * Real.exp (-c * t ^ 2) ≤ K := by
  have hcont : Continuous fun t : ℝ => (1 + t ^ p) * Real.exp (-c * t ^ 2) :=
    (continuous_const.add (continuous_rpow_const_of_nonneg hp)).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2)))
  have h1 : Tendsto (fun t : ℝ => Real.exp (-c * t ^ 2)) atTop (𝓝 0) :=
    (exp_neg_mul_sq_isLittleO_exp_neg hc).trans_tendsto Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun t : ℝ => t ^ p * Real.exp (-c * t ^ 2)) atTop (𝓝 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hc p).trans_tendsto tendsto_exp_neg_half_mul
  have hlim : Tendsto (fun t : ℝ => (1 + t ^ p) * Real.exp (-c * t ^ 2)) atTop (𝓝 0) := by
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3.congr fun t => by ring
  obtain ⟨T, hT⟩ :=
    eventually_atTop.1 (hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  have hcpt : IsCompact (Set.Icc (0 : ℝ) (max T 0)) := isCompact_Icc
  obtain ⟨t₀, -, ht₀⟩ := hcpt.exists_isMaxOn ⟨0, by simp⟩ hcont.continuousOn
  refine ⟨max 1 ((1 + t₀ ^ p) * Real.exp (-c * t₀ ^ 2)),
    lt_of_lt_of_le one_pos (le_max_left _ _), fun t ht => ?_⟩
  rcases le_or_gt t (max T 0) with h | h
  · exact le_trans (ht₀ (Set.mem_Icc.2 ⟨ht, h⟩)) (le_max_right _ _)
  · exact le_trans (hT t ((le_max_left T 0).trans h.le)) (le_max_left _ _)


/-- **The pointwise weight-absorption inequality**: the polynomially weighted exponential
bound splits into a half-rate exponential (handled by the unweighted tail split) plus a
prior-moment term (handled by `∫ ‖θ‖ᵖ dΠ < ∞`). -/
private theorem weighted_exp_split {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
      (1 + (Real.sqrt n * r) ^ p) * Real.exp (-c * n * min (r ^ 2) 1)
        ≤ K * Real.exp (-(c / 2) * n * min (r ^ 2) 1)
          + K * (1 + r ^ p) * Real.exp (-(c / 2) * n) := by
  obtain ⟨K, hK, hKb⟩ := exists_poly_exp_bound hp (half_pos hc)
  refine ⟨K, hK, fun n r hr => ?_⟩
  have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hrp : (0 : ℝ) ≤ r ^ p := Real.rpow_nonneg hr p
  rcases le_or_gt r 1 with hr1 | hr1
  · have hmin : min (r ^ 2) 1 = r ^ 2 := min_eq_left (by nlinarith)
    simp only [hmin]
    have h1 := hKb (Real.sqrt n * r) (mul_nonneg hs hr)
    rw [show (Real.sqrt n * r) ^ 2 = (n : ℝ) * r ^ 2 by rw [mul_pow, hsq]] at h1
    have key : (1 + (Real.sqrt n * r) ^ p) * Real.exp (-c * (n : ℝ) * r ^ 2)
        ≤ K * Real.exp (-(c / 2) * (n : ℝ) * r ^ 2) := by
      have e : Real.exp (-c * (n : ℝ) * r ^ 2)
          = Real.exp (-(c / 2) * ((n : ℝ) * r ^ 2)) * Real.exp (-(c / 2) * (n : ℝ) * r ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    refine key.trans (le_add_of_nonneg_right ?_)
    exact mul_nonneg (mul_nonneg hK.le (by linarith)) (Real.exp_pos _).le
  · have hmin : min (r ^ 2) 1 = 1 := min_eq_right (by nlinarith)
    simp only [hmin, mul_one]
    set E := Real.exp (-(c / 2) * (n : ℝ)) with hEdef
    have hEpos : 0 < E := Real.exp_pos _
    set S := Real.sqrt n ^ p with hSdef
    have hSnn : 0 ≤ S := Real.rpow_nonneg hs p
    have h1 : (1 + S) * E ≤ K := by
      have h := hKb (Real.sqrt n) hs
      rw [hsq] at h
      exact h
    have hEK : E ≤ K := by nlinarith
    have hSEK : S * E ≤ K := by nlinarith
    have hmain : (1 + (Real.sqrt n * r) ^ p) * Real.exp (-c * (n : ℝ))
        ≤ K * (1 + r ^ p) * E := by
      have hmr : (Real.sqrt n * r) ^ p = S * r ^ p := Real.mul_rpow hs hr
      have he : Real.exp (-c * (n : ℝ)) = E * E := by
        rw [hEdef, ← Real.exp_add]; congr 1; ring
      rw [hmr, he, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hEpos.le
      nlinarith [mul_nonneg (sub_nonneg.2 hSEK) hrp]
    have : (0 : ℝ) ≤ K * E := mul_nonneg hK.le hEpos.le
    linarith


/-- Auxiliary: `n^{kk/2} e^{-a n} → 0`. -/
private theorem sqrt_pow_mul_exp_neg_tendsto (kk : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.sqrt n ^ kk * Real.exp (-a * n)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hKb⟩ :=
    exists_poly_exp_bound (p := (kk : ℝ)) (Nat.cast_nonneg kk) (half_pos ha)
  have key : ∀ n : ℕ, Real.sqrt n ^ kk * Real.exp (-a * (n : ℝ))
      ≤ K * Real.exp (-(a / 2) * (n : ℝ)) := by
    intro n
    have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have h1 := hKb (Real.sqrt n) hs
    rw [hsq] at h1
    have hnat : Real.sqrt n ^ kk = Real.sqrt n ^ (kk : ℝ) := (Real.rpow_natCast _ kk).symm
    have hnn : (0 : ℝ) ≤ Real.sqrt n ^ (kk : ℝ) := Real.rpow_nonneg hs _
    have hEpos : (0 : ℝ) < Real.exp (-(a / 2) * (n : ℝ)) := Real.exp_pos _
    have h3 : Real.sqrt n ^ kk * Real.exp (-(a / 2) * (n : ℝ)) ≤ K := by
      rw [hnat]
      nlinarith
    have he : Real.exp (-a * (n : ℝ))
        = Real.exp (-(a / 2) * (n : ℝ)) * Real.exp (-(a / 2) * (n : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h3 hEpos.le
  have hg : Tendsto (fun n : ℕ => K * Real.exp (-(a / 2) * (n : ℝ))) atTop (𝓝 0) := by
    have hb : Real.exp (-(a / 2)) < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by simp]
      exact Real.exp_lt_exp.2 (by linarith)
    have h0 : (0 : ℝ) ≤ Real.exp (-(a / 2)) := (Real.exp_pos _).le
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hb).const_mul K
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [mul_comm (-(a / 2) : ℝ) (n : ℝ), Real.exp_nat_mul]
  refine squeeze_zero (fun n => ?_) key hg
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.exp_pos _).le

/-- Elementary `rpow` subadditivity up to the factor `2 ^ p`. -/
private lemma rpow_add_le_two_rpow {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  have hmax : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h1 : (a + b) ^ p ≤ (2 * max a b) ^ p := Real.rpow_le_rpow (by linarith) hmax hp
  have h2 : (2 * max a b) ^ p = 2 ^ p * max a b ^ p :=
    Real.mul_rpow (by norm_num) (le_trans ha (le_max_left a b))
  have h3 : max a b ^ p ≤ a ^ p + b ^ p := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; have := Real.rpow_nonneg ha p; linarith
    · rw [max_eq_left h]; have := Real.rpow_nonneg hb p; linarith
  have h4 : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) p
  calc (a + b) ^ p ≤ (2 * max a b) ^ p := h1
    _ = 2 ^ p * max a b ^ p := h2
    _ ≤ 2 ^ p * (a ^ p + b ^ p) := by nlinarith

/-- Measurability of `θ ↦ ‖θ - θ₀‖ ^ p` (`rpow`, `0 ≤ p`). -/
private lemma measurable_norm_sub_rpow (θ₀ : EuclideanSpace ℝ (Fin k)) {p : ℝ} (hp : 0 ≤ p) :
    Measurable fun θ : EuclideanSpace ℝ (Fin k) => ‖θ - θ₀‖ ^ p :=
  ((Real.continuous_rpow_const hp).comp
    (by fun_prop : Continuous fun θ : EuclideanSpace ℝ (Fin k) => ‖θ - θ₀‖)).measurable

/-- **The weighted Step-A tail split** (vdV p. 148): the polynomially weighted prior tail
integral against the exponential type-II bound is negligible after the `(√n)ᵏ`
normalization. -/
private theorem weighted_prior_tail_tendsto
    (hπ : HasLocalDensity π θ₀ r₀ f) {p : ℝ} (hp : 0 ≤ p)
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞) {c : ℝ} (hc : 0 < c)
    {Mseq : ℕ → ℝ} (hM : Tendsto Mseq atTop atTop) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n ^ k) *
        ∫⁻ θ in tailSet θ₀ (Mseq n) n,
          ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
            Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hsplit⟩ := weighted_exp_split hp hc
  have hc2 : (0 : ℝ) < c / 2 := half_pos hc
  -- measurability of the two auxiliary integrands
  have hmG1 : ∀ n : ℕ, Measurable fun θ : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) := by
    intro n; fun_prop
  have hmG2 : Measurable fun θ : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) :=
    (measurable_const.add (measurable_norm_sub_rpow θ₀ hp)).ennreal_ofReal
  have hmMom : Measurable fun θ : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal (‖θ‖ ^ p) :=
    (((Real.continuous_rpow_const hp).comp continuous_norm).measurable).ennreal_ofReal
  -- Step 4: the `p`-moment integral of `‖θ - θ₀‖` is finite
  have hbd : ∀ θ : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ≤
      1 + ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal (‖θ‖ ^ p) + ENNReal.ofReal (‖θ₀‖ ^ p)) := by
    intro θ
    have hn0 : (0 : ℝ) ≤ ‖θ‖ ^ p := Real.rpow_nonneg (norm_nonneg _) p
    have hn1 : (0 : ℝ) ≤ ‖θ₀‖ ^ p := Real.rpow_nonneg (norm_nonneg _) p
    have h2p : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) p
    have h1 : ‖θ - θ₀‖ ≤ ‖θ‖ + ‖θ₀‖ := norm_sub_le θ θ₀
    have h2 : ‖θ - θ₀‖ ^ p ≤ (‖θ‖ + ‖θ₀‖) ^ p := Real.rpow_le_rpow (norm_nonneg _) h1 hp
    have h3 : (‖θ‖ + ‖θ₀‖) ^ p ≤ 2 ^ p * (‖θ‖ ^ p + ‖θ₀‖ ^ p) :=
      rpow_add_le_two_rpow (norm_nonneg _) (norm_nonneg _) hp
    calc ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p)
        ≤ ENNReal.ofReal (1 + 2 ^ p * (‖θ‖ ^ p + ‖θ₀‖ ^ p)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = 1 + ENNReal.ofReal (2 ^ p) *
            (ENNReal.ofReal (‖θ‖ ^ p) + ENNReal.ofReal (‖θ₀‖ ^ p)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul h2p, ENNReal.ofReal_add hn0 hn1]
  have hCfin : (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) ≠ ∞ := by
    have hle : (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) ≤
        1 + ENNReal.ofReal (2 ^ p) *
          ((∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π) + ENNReal.ofReal (‖θ₀‖ ^ p)) := by
      refine le_trans (lintegral_mono hbd) (le_of_eq ?_)
      rw [lintegral_add_left measurable_const,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left hmMom]
      simp
    refine ne_top_of_le_ne_top ?_ hle
    refine (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ?_⟩).ne
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨hmom, ENNReal.ofReal_lt_top⟩)
  -- Step 1: the pointwise `ℝ≥0∞` bound
  have key : ∀ (n : ℕ) (θ : EuclideanSpace ℝ (Fin k)),
      ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
          Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1))
          + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
              * ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) := by
    intro n θ
    refine le_trans (ENNReal.ofReal_le_ofReal (hsplit n ‖θ - θ₀‖ (norm_nonneg _))) (le_of_eq ?_)
    have hp1 : (0 : ℝ) ≤ K * Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1) :=
      mul_nonneg hK.le (Real.exp_pos _).le
    have hrp : (0 : ℝ) ≤ 1 + ‖θ - θ₀‖ ^ p := by
      have := Real.rpow_nonneg (norm_nonneg (θ - θ₀)) p; linarith
    have hp2 : (0 : ℝ) ≤ K * (1 + ‖θ - θ₀‖ ^ p) * Real.exp (-(c / 2) * n) :=
      mul_nonneg (mul_nonneg hK.le hrp) (Real.exp_pos _).le
    have hp3 : (0 : ℝ) ≤ K * Real.exp (-(c / 2) * n) :=
      mul_nonneg hK.le (Real.exp_pos _).le
    rw [ENNReal.ofReal_add hp1 hp2, ENNReal.ofReal_mul hK.le]
    congr 1
    rw [show K * (1 + ‖θ - θ₀‖ ^ p) * Real.exp (-(c / 2) * n)
        = K * Real.exp (-(c / 2) * n) * (1 + ‖θ - θ₀‖ ^ p) from by ring,
      ENNReal.ofReal_mul hp3, ENNReal.ofReal_mul hK.le]
  -- Step 2: integrate the pointwise bound over the tail set
  have hint : ∀ n : ℕ,
      (∫⁻ θ in tailSet θ₀ (Mseq n) n, ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
          Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π) ≤
        ENNReal.ofReal K * (∫⁻ θ in tailSet θ₀ (Mseq n) n,
            ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
          + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
              * (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) := by
    intro n
    have hne : ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n)) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    calc (∫⁻ θ in tailSet θ₀ (Mseq n) n, ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
            Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
        ≤ ∫⁻ θ in tailSet θ₀ (Mseq n) n,
            (ENNReal.ofReal K *
                ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1))
              + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
                  * ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p)) ∂π := lintegral_mono (key n)
      _ = ENNReal.ofReal K * (∫⁻ θ in tailSet θ₀ (Mseq n) n,
              ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
            + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
                * (∫⁻ θ in tailSet θ₀ (Mseq n) n,
                    ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) := by
          rw [lintegral_add_left (measurable_const.fun_mul (hmG1 n)),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ hne]
      _ ≤ ENNReal.ofReal K * (∫⁻ θ in tailSet θ₀ (Mseq n) n,
              ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
            + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
                * (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) :=
          add_le_add le_rfl (mul_le_mul_right (setLIntegral_le_lintegral _ _) _)
  -- Step 3 / 5: the two limits
  have hA : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n ^ k) *
      ∫⁻ θ in tailSet θ₀ (Mseq n) n,
        ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π) atTop (𝓝 0) :=
    prior_tail_split hπ hc2 hM
  have hB : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (Real.sqrt n ^ k * Real.exp (-(c / 2) * n))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (sqrt_pow_mul_exp_neg_tendsto k hc2)
    simpa using this
  -- Step 6: squeeze
  have hU : Tendsto (fun n : ℕ =>
      ENNReal.ofReal K * (ENNReal.ofReal (Real.sqrt n ^ k) *
          ∫⁻ θ in tailSet θ₀ (Mseq n) n,
            ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
        + ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt n ^ k * Real.exp (-(c / 2) * n))
            * (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hA
      (Or.inr ENNReal.ofReal_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hB
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h1 h2
    have h3 := ENNReal.Tendsto.mul_const (b := ∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π)
      h2 (Or.inr hCfin)
    rw [zero_mul] at h3
    simpa using h1.add h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  have h := mul_le_mul_right (hint n) (ENNReal.ofReal (Real.sqrt n ^ k))
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.sqrt n ^ k)]
  ring


/-! ### Step 2: the per-sample-size mixture bound -/

/-- **The weighted Step-A bound at a fixed sample size**: on the event where the polynomially
weighted posterior tail exceeds `δ` and the test does not fire, the localized mixture mass is
controlled by the prior-side weighted tail integral. -/
private theorem tail_mixture_bound
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) {R : ℝ}
    {φn : (Fin n → 𝓧) → ℝ} (hφmeas : Measurable φn)
    (hφ01 : ∀ ω, φn ω ∈ Set.Icc (0 : ℝ) 1) {c : ℝ}
    (hφII : ∀ θ, R / Real.sqrt n ≤ ‖θ - θ₀‖ →
      ∫ ω, (1 - φn ω) ∂(productMeasure M μ θ n)
        ≤ Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1))
    {δ : ℝ≥0∞} (hδ : 0 < δ) (hδtop : δ ≠ ∞) {c₁ : ℝ≥0∞} (hc₁ : 0 < c₁)
    (hballn : c₁ * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
      ≤ π (Metric.ball θ₀ (1 / Real.sqrt n))) :
    bvmMixture κ π θ₀ 1 n
        ({ω | δ ≤ ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ,
            ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω)}
          ∩ {ω | φn ω < (2 : ℝ)⁻¹})
      ≤ (ENNReal.ofReal ((2 : ℝ)⁻¹))⁻¹ * δ⁻¹ * c₁⁻¹ *
        (ENNReal.ofReal (Real.sqrt n ^ k) *
          ∫⁻ θ in tailSet θ₀ R n,
            ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
              Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π) := by
  have hpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hrpow : Continuous fun t : ℝ => t ^ p :=
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x p (Or.inr hp)
  have hWmeas : Measurable fun h : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal (1 + ‖h‖ ^ p) :=
    (continuous_const.add (hrpow.comp continuous_norm)).measurable.ennreal_ofReal
  set T : (Fin n → 𝓧) → ℝ≥0∞ := fun ω =>
    ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ,
      ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω) with hTdef
  have hTmeas : Measurable T := measurable_lintegral_tail n R hWmeas
  set g : (Fin n → 𝓧) → ℝ≥0∞ := fun ω => ENNReal.ofReal (1 - φn ω) with hgdef
  have hgmeas : Measurable g := (measurable_const.sub hφmeas).ennreal_ofReal
  have hφint : ∀ θ' : EuclideanSpace ℝ (Fin k), Integrable φn (productMeasure M μ θ' n) := by
    intro θ'
    haveI : IsProbabilityMeasure (productMeasure M μ θ' n) := by
      rw [productMeasure_eq_iidKernel_apply hκ θ' n]; infer_instance
    refine (integrable_const (1 : ℝ)).mono' hφmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    have h := hφ01 ω
    change ‖φn ω‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  set a : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ)⁻¹) with hadef
  have ha0 : a ≠ 0 := by simp [hadef]
  set S : Set (Fin n → 𝓧) := {ω | δ ≤ T ω} ∩ {ω | φn ω < (2 : ℝ)⁻¹} with hSdef
  set I : ℝ≥0∞ := ∫⁻ θ in tailSet θ₀ R n,
    ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
      Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π with hIdef
  -- (i) the untriggered test gives back a factor `1/2`
  have h1 : a * bvmMixture κ π θ₀ 1 n S ≤ ∫⁻ ω in S, g ω ∂(bvmMixture κ π θ₀ 1 n) := by
    rw [← setLIntegral_const S a]
    refine setLIntegral_mono hgmeas fun ω hω => ?_
    have hlt : φn ω < (2 : ℝ)⁻¹ := hω.2
    have hle : (2 : ℝ)⁻¹ ≤ 1 - φn ω := by linarith
    simpa [hadef, hgdef] using ENNReal.ofReal_le_ofReal hle
  -- (ii) Markov in the weighted posterior tail
  have h2 : ∫⁻ ω in S, g ω ∂(bvmMixture κ π θ₀ 1 n)
      ≤ δ⁻¹ * ∫⁻ ω, T ω * g ω ∂(bvmMixture κ π θ₀ 1 n) := by
    calc ∫⁻ ω in S, g ω ∂(bvmMixture κ π θ₀ 1 n)
        ≤ ∫⁻ ω in S, δ⁻¹ * (T ω * g ω) ∂(bvmMixture κ π θ₀ 1 n) := by
          refine setLIntegral_mono (by fun_prop) fun ω hω => ?_
          calc g ω = δ⁻¹ * δ * g ω := by
                rw [ENNReal.inv_mul_cancel hδ.ne' hδtop, one_mul]
            _ ≤ δ⁻¹ * T ω * g ω := by gcongr; exact hω.1
            _ = δ⁻¹ * (T ω * g ω) := by ring
      _ ≤ ∫⁻ ω, δ⁻¹ * (T ω * g ω) ∂(bvmMixture κ π θ₀ 1 n) := setLIntegral_le_lintegral _ _
      _ = δ⁻¹ * ∫⁻ ω, T ω * g ω ∂(bvmMixture κ π θ₀ 1 n) :=
          lintegral_const_mul _ (hTmeas.mul hgmeas)
  -- (iii) mixture ≤ predictive
  have h3 : ∫⁻ ω, T ω * g ω ∂(bvmMixture κ π θ₀ 1 n)
      ≤ (π (Metric.ball θ₀ (1 / Real.sqrt n)))⁻¹
        * ∫⁻ ω, T ω * g ω ∂(iidKernel κ n ∘ₘ π) :=
    lintegral_bvmMixture_le 1 n (hTmeas.mul hgmeas)
  -- (iv) the weighted disintegration identity
  set wn : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := (tailSet θ₀ R n).indicator
    (fun θ => ENNReal.ofReal (1 + ‖Real.sqrt n • (θ - θ₀)‖ ^ p)) with hwndef
  have hwn : Measurable wn := by
    refine Measurable.indicator ?_ (measurableSet_tailSet θ₀ R n)
    exact hWmeas.comp (by fun_prop)
  have h4 : ∫⁻ ω, T ω * g ω ∂(iidKernel κ n ∘ₘ π)
      = ∫⁻ θ, wn θ * ∫⁻ ω, g ω ∂(iidKernel κ n θ) ∂π := by
    rw [← weighted_posterior_predictive_eq n hwn hgmeas]
    exact lintegral_congr fun ω => by
      rw [hTdef, hwndef]
      exact congrArg (· * g ω) (lintegral_tail_bvmLocalPosterior hn ω R hWmeas)
  -- (v) the type-II bound on the tail
  have h5 : ∫⁻ θ, wn θ * ∫⁻ ω, g ω ∂(iidKernel κ n θ) ∂π ≤ I := by
    rw [hIdef, ← lintegral_indicator (measurableSet_tailSet θ₀ R n)]
    refine lintegral_mono fun θ => ?_
    by_cases hθ : θ ∈ tailSet θ₀ R n
    · rw [hwndef, Set.indicator_of_mem hθ, Set.indicator_of_mem hθ]
      have hnorm : ‖Real.sqrt n • (θ - θ₀)‖ = Real.sqrt n * ‖θ - θ₀‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      have hgi : ∫⁻ ω, g ω ∂(iidKernel κ n θ)
          ≤ ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) := by
        have hpm : productMeasure M μ θ n = iidKernel κ n θ :=
          productMeasure_eq_iidKernel_apply hκ θ n
        haveI : IsProbabilityMeasure (productMeasure M μ θ n) := by
          rw [hpm]; infer_instance
        have hnn : 0 ≤ᵐ[productMeasure M μ θ n] fun ω => 1 - φn ω := by
          filter_upwards with ω
          change (0 : ℝ) ≤ 1 - φn ω
          linarith [(hφ01 ω).2]
        have hint : Integrable (fun ω => 1 - φn ω) (productMeasure M μ θ n) :=
          (integrable_const (1 : ℝ)).sub (hφint θ)
        calc ∫⁻ ω, g ω ∂(iidKernel κ n θ)
            = ∫⁻ ω, ENNReal.ofReal (1 - φn ω) ∂(productMeasure M μ θ n) := by rw [hpm, hgdef]
          _ = ENNReal.ofReal (∫ ω, (1 - φn ω) ∂(productMeasure M μ θ n)) :=
              (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (hφII θ hθ)
      calc ENNReal.ofReal (1 + ‖Real.sqrt n • (θ - θ₀)‖ ^ p) * ∫⁻ ω, g ω ∂(iidKernel κ n θ)
          ≤ ENNReal.ofReal (1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p)
              * ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) := by
            rw [hnorm]; gcongr
        _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
    · rw [hwndef, Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ, zero_mul]
  -- (vi) the prior small-ball lower bound
  have h6 : (π (Metric.ball θ₀ (1 / Real.sqrt n)))⁻¹
      ≤ c₁⁻¹ * ENNReal.ofReal (Real.sqrt n ^ k) := by
    have hx0 : ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    calc (π (Metric.ball θ₀ (1 / Real.sqrt n)))⁻¹
        ≤ (c₁ * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k))⁻¹ := ENNReal.inv_le_inv.2 hballn
      _ = c₁⁻¹ * (ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k))⁻¹ :=
          ENNReal.mul_inv (Or.inl hc₁.ne') (Or.inr hx0)
      _ = c₁⁻¹ * ENNReal.ofReal (Real.sqrt n ^ k) := by
          rw [inv_pow, ENNReal.ofReal_inv_of_pos (by positivity), inv_inv]
  -- assemble
  have hstep : a * bvmMixture κ π θ₀ 1 n S
      ≤ δ⁻¹ * (c₁⁻¹ * ENNReal.ofReal (Real.sqrt n ^ k) * I) :=
    calc a * bvmMixture κ π θ₀ 1 n S
        ≤ ∫⁻ ω in S, g ω ∂(bvmMixture κ π θ₀ 1 n) := h1
      _ ≤ δ⁻¹ * ∫⁻ ω, T ω * g ω ∂(bvmMixture κ π θ₀ 1 n) := h2
      _ ≤ δ⁻¹ * ((π (Metric.ball θ₀ (1 / Real.sqrt n)))⁻¹
            * ∫⁻ ω, T ω * g ω ∂(iidKernel κ n ∘ₘ π)) := by gcongr
      _ ≤ δ⁻¹ * (c₁⁻¹ * ENNReal.ofReal (Real.sqrt n ^ k) * I) := by
          gcongr
          exact h4.le.trans h5
  calc bvmMixture κ π θ₀ 1 n S
      = a⁻¹ * (a * bvmMixture κ π θ₀ 1 n S) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ a⁻¹ * (δ⁻¹ * (c₁⁻¹ * ENNReal.ofReal (Real.sqrt n ^ k) * I)) := by gcongr
    _ = a⁻¹ * δ⁻¹ * c₁⁻¹ * (ENNReal.ofReal (Real.sqrt n ^ k) * I) := by ring

/-- **The polynomial-weighted posterior-tail bound** (vdV p. 148): the polynomial-weighted posterior
tails are negligible.
For every `Mₙ → ∞` and `δ > 0`,
`P^n_{θ₀} { ∫_{‖h‖ ≥ Mₙ} (1 + ‖h‖ᵖ) d(local posterior) ≥ δ } → 0`,
given the model/Fisher/prior conditions of the Bernstein–von Mises theorem, exponentially powerful
tests
(the exponential-tests lemma shape), and the prior moment `∫ ‖θ‖ᵖ dπ < ∞`. -/
theorem posterior_tail_lintegral_tendsto
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {p : ℝ}
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: finite prior `p`-moment, `∫ ‖θ‖ᵖ dΠ < ∞`; vdV §10.3
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV §10.3 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop)
    {φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ} {c : ℝ}
    -- LEAN-ONLY: positive exponential rate (supplied by the exponential-tests lemma)
    (hc : 0 < c)
    -- USER-INPUT: exponentially powerful tests; vdV §10.2 (discharged at assembly)
    (hφ : IsExpConsistentTestSeq M μ θ₀ Mseq c φ) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
            ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω)})
        atTop (𝓝 0) := by
  classical
  -- the polynomial envelope
  have hrpow : Continuous fun t : ℝ => t ^ p :=
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x p (Or.inr hp)
  have hWmeas : Measurable fun h : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal (1 + ‖h‖ ^ p) :=
    (continuous_const.add (hrpow.comp continuous_norm)).measurable.ennreal_ofReal
  -- the sampling experiments are probability measures
  have hprob : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ n) := by
    intro θ n
    rw [productMeasure_eq_iidKernel_apply hκ θ n]
    infer_instance
  have hφint : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      Integrable (φ n) (productMeasure M μ θ n) := by
    intro θ n
    haveI := hprob θ n
    refine (integrable_const (1 : ℝ)).mono' (hφ.measurable n).aestronglyMeasurable ?_
    filter_upwards with ω
    have h := hφ.mem_Icc n ω
    change ‖φ n ω‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  -- the ℝ≥0∞ form of the test errors
  have hlint : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      ∫⁻ ω, ENNReal.ofReal (1 - φ n ω) ∂(productMeasure M μ θ n)
        = ENNReal.ofReal (∫ ω, (1 - φ n ω) ∂(productMeasure M μ θ n)) := by
    intro θ n
    haveI := hprob θ n
    refine (ofReal_integral_eq_lintegral_ofReal
      ((integrable_const (1 : ℝ)).sub (hφint θ n)) ?_).symm
    filter_upwards with ω
    change (0 : ℝ) ≤ 1 - φ n ω
    linarith [(hφ.mem_Icc n ω).2]
  have hlintφ : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (φ n ω) ∂(productMeasure M μ θ₀ n)
      = ENNReal.ofReal (∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) := by
    intro n
    haveI := hprob θ₀ n
    refine (ofReal_integral_eq_lintegral_ofReal (hφint θ₀ n) ?_).symm
    filter_upwards with ω
    exact (hφ.mem_Icc n ω).1
  -- Part I: the test kills the `{φₙ ≥ 1/2}` side under the base law
  have hhalf : ENNReal.ofReal ((2 : ℝ)⁻¹) ≠ 0 := by
    simp
  have hI : Tendsto (fun n : ℕ => productMeasure M μ θ₀ n {ω | (2 : ℝ)⁻¹ ≤ φ n ω})
      atTop (𝓝 0) := by
    have hbd : ∀ n : ℕ, productMeasure M μ θ₀ n {ω | (2 : ℝ)⁻¹ ≤ φ n ω}
        ≤ (ENNReal.ofReal ((2 : ℝ)⁻¹))⁻¹
          * ENNReal.ofReal (∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) := by
      intro n
      have hmk := mul_meas_ge_le_lintegral₀
        (μ := productMeasure M μ θ₀ n)
        ((hφ.measurable n).ennreal_ofReal.aemeasurable) (ENNReal.ofReal ((2 : ℝ)⁻¹))
      have hsub : productMeasure M μ θ₀ n {ω | (2 : ℝ)⁻¹ ≤ φ n ω}
          ≤ productMeasure M μ θ₀ n
            {ω | ENNReal.ofReal ((2 : ℝ)⁻¹) ≤ ENNReal.ofReal (φ n ω)} :=
        measure_mono fun _ hω => ENNReal.ofReal_le_ofReal hω
      have hstep : ENNReal.ofReal ((2 : ℝ)⁻¹)
          * productMeasure M μ θ₀ n {ω | (2 : ℝ)⁻¹ ≤ φ n ω}
          ≤ ENNReal.ofReal (∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) := by
        calc ENNReal.ofReal ((2 : ℝ)⁻¹)
              * productMeasure M μ θ₀ n {ω | (2 : ℝ)⁻¹ ≤ φ n ω}
            ≤ ENNReal.ofReal ((2 : ℝ)⁻¹) * productMeasure M μ θ₀ n
                {ω | ENNReal.ofReal ((2 : ℝ)⁻¹) ≤ ENNReal.ofReal (φ n ω)} := by gcongr
          _ ≤ ∫⁻ ω, ENNReal.ofReal (φ n ω) ∂(productMeasure M μ θ₀ n) := hmk
          _ = _ := hlintφ n
      calc productMeasure M μ θ₀ n {ω | (2 : ℝ)⁻¹ ≤ φ n ω}
          = (ENNReal.ofReal ((2 : ℝ)⁻¹))⁻¹ * (ENNReal.ofReal ((2 : ℝ)⁻¹)
              * productMeasure M μ θ₀ n {ω | (2 : ℝ)⁻¹ ≤ φ n ω}) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hhalf ENNReal.ofReal_ne_top, one_mul]
        _ ≤ _ := by gcongr
    have hlim : Tendsto (fun n : ℕ => (ENNReal.ofReal ((2 : ℝ)⁻¹))⁻¹
        * ENNReal.ofReal (∫ ω, φ n ω ∂(productMeasure M μ θ₀ n))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ =>
          ENNReal.ofReal (∫ ω, φ n ω ∂(productMeasure M μ θ₀ n))) atTop (𝓝 0) := by
        simpa using (ENNReal.tendsto_ofReal hφ.typeI)
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (by simp))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le) hbd
  -- the main statement, for finite thresholds
  have main : ∀ δ : ℝ≥0∞, 0 < δ → δ ≠ ∞ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
            ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω)})
        atTop (𝓝 0) := by
    intro δ hδ hδtop
    obtain ⟨Tn, hTn⟩ : ∃ Tn : ∀ n : ℕ, (Fin n → 𝓧) → ℝ≥0∞, ∀ n ω, Tn n ω =
        ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
          ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω) := ⟨_, fun _ _ => rfl⟩
    simp only [← hTn]
    have hTmeas : ∀ n, Measurable (Tn n) := by
      intro n
      have he : Tn n = fun ω => ∫⁻ h in
          (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
            ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω) := funext (hTn n)
      rw [he]
      exact measurable_lintegral_tail (κ := κ) (π := π) (θ₀ := θ₀) n (Mseq n) hWmeas
    obtain ⟨A, hA⟩ : ∃ A : ∀ n : ℕ, Set (Fin n → 𝓧), ∀ n,
        A n = {ω | δ ≤ Tn n ω} ∩ {ω | φ n ω < (2 : ℝ)⁻¹} := ⟨_, fun _ => rfl⟩
    have hAmeas : ∀ n, MeasurableSet (A n) := by
      intro n
      rw [hA]
      exact (measurableSet_le measurable_const (hTmeas n)).inter
        (measurableSet_lt (hφ.measurable n) measurable_const)
    -- Part II: the mixture bound on the damped side
    obtain ⟨c₁, hc₁, hball⟩ := prior_ball_inv_sqrt_lower hπ (u := 1) one_pos
    obtain ⟨N₀, hN₀⟩ := hφ.typeII
    have hII : Tendsto (fun n => bvmMixture κ π θ₀ 1 n (A n)) atTop (𝓝 0) := by
      have hbd : ∀ᶠ n : ℕ in atTop, bvmMixture κ π θ₀ 1 n (A n)
          ≤ (ENNReal.ofReal ((2 : ℝ)⁻¹))⁻¹ * δ⁻¹ * c₁⁻¹ *
            (ENNReal.ofReal (Real.sqrt n ^ k) *
              ∫⁻ θ in tailSet θ₀ (Mseq n) n,
                ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
                  Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π) := by
        filter_upwards [hball, eventually_ge_atTop N₀, eventually_ge_atTop 1] with
          n hballn hnN hn1
        rw [hA n]
        simp only [hTn]
        exact tail_mixture_bound hκ hp hn1 (hφ.measurable n) (hφ.mem_Icc n)
          (hN₀ n hnN) hδ hδtop hc₁ hballn
      have hlim : Tendsto (fun n : ℕ => (ENNReal.ofReal ((2 : ℝ)⁻¹))⁻¹ * δ⁻¹ * c₁⁻¹ *
          (ENNReal.ofReal (Real.sqrt n ^ k) *
            ∫⁻ θ in tailSet θ₀ (Mseq n) n,
              ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
                Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)) atTop (𝓝 0) := by
        have hC : (ENNReal.ofReal ((2 : ℝ)⁻¹))⁻¹ * δ⁻¹ * c₁⁻¹ ≠ ∞ := by
          refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_
          · simpa [ENNReal.inv_ne_top] using hhalf
          · simpa [ENNReal.inv_ne_top] using hδ.ne'
          · simpa [ENNReal.inv_ne_top] using hc₁.ne'
        simpa using ENNReal.Tendsto.const_mul
          (weighted_prior_tail_tendsto hπ hp hmom hc hM) (Or.inr hC)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun n => zero_le) hbd
    -- Part III: transfer to the base law by contiguity
    have hIII : Tendsto (fun n => productMeasure M μ θ₀ n (A n)) atTop (𝓝 0) :=
      (mutuallyContiguous_mixture_base hPDF hsc hDQM hJ_pd hJ hκ hπ (u := 1) one_pos).2
        A hAmeas hII
    -- Part IV: assemble
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hI.add hIII) (fun n => zero_le) (fun n => ?_)
    calc productMeasure M μ θ₀ n {ω | δ ≤ Tn n ω}
        ≤ productMeasure M μ θ₀ n ({ω | (2 : ℝ)⁻¹ ≤ φ n ω} ∪ A n) := by
          refine measure_mono fun ω hω => ?_
          rcases le_or_gt ((2 : ℝ)⁻¹) (φ n ω) with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hA]; exact ⟨hω, h⟩)
      _ ≤ _ := measure_union_le _ _
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (main (min δ 1) (lt_min hδ zero_lt_one)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)))
    (fun n => zero_le) (fun _ => measure_mono fun _ hω => (min_le_left δ 1).trans hω)

end StatLean.Bayesian

