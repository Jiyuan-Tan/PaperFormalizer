module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasResidualExplicit
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.ForMathlib.IntegrableTail
public import StatLean.AsymptoticStatistics.ForMathlib.MatrixInProbability

@[expose] public section

/-!
# QMD transport of a random score under a moving model

This file proves the model-shift term in vdV (25.52) and
Theorem 25.59.  The scalar statements expose the sign before any information
inverse is applied:

`√n (P scoreHat - P_{thetaHat,eta} scoreHat)
  + √n (thetaHat-theta0) <score0, path.score> = o_P(1)`.

Consequently the Z-estimating-equation algebra produces the covariant
`+ I^{-1} B_n` correction.  The literal `+ B_n` display in vdV is recovered
only in information-normalized coordinates (`I = 1`).

The native finite-dimensional statements use one QMD model, one cross-moment
matrix, and one continuous linear map.  They do not invert coordinates
separately.

Reference: vdV §25.8, equation (25.52), pp. 391--392, and Theorem 25.59,
p. 395. The displayed correction is written in covariant coordinates.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Matrix.Norms.L2Operator

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Extend a punctured limit by the prescribed value at zero. -/
private lemma tendsto_zeroExtension {E F : Type*}
    [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]
    (f extension : E → F) (hf : Tendsto f (𝓝[≠] 0) (𝓝 0))
    (hzero : extension 0 = 0) (hne : ∀ x ≠ 0, extension x = f x) :
    Tendsto extension (𝓝 0) (𝓝 0) := by
  classical
  intro s hs
  change extension ⁻¹' s ∈ 𝓝 0
  obtain ⟨t, ht, hts⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hf hs)
  refine mem_of_superset ht fun x hx => ?_
  by_cases h0 : x = 0
  · simpa [h0, hzero] using mem_of_mem_nhds hs
  · simpa [hne x h0] using hts ⟨hx, h0⟩

/-- Continuous-at-zero maps preserve convergence in probability when the
underlying probability spaces vary with `n`. -/
private lemma tendstoInProbZero_comp_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, Omega' n → E} {f : E → F}
    (hZ : TendstoInProbZero P Z) (hf : Tendsto f (𝓝 0) (𝓝 0)) :
    TendstoInProbZero P (fun n omega => f (Z n omega)) := by
  intro epsilon hepsilon
  have hev : {x | dist (f x) 0 < epsilon} ∈ 𝓝 (0 : E) :=
    Metric.tendsto_nhds.mp hf epsilon hepsilon
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hsub : ∀ n, {omega | epsilon ≤ ‖f (Z n omega)‖} ⊆
      {omega | delta ≤ ‖Z n omega‖} := by
    intro n omega homega
    by_contra hnot
    have hsmall := hball (by simpa [Metric.mem_ball, dist_zero_right] using not_le.mp hnot)
    simp only [Set.mem_setOf_eq, dist_zero_right] at hsmall homega
    exact (not_lt_of_ge homega) hsmall
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hZ delta hdelta) (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n => measureReal_mono (hsub n))

/-- The sum of two sequences converging to zero in probability also converges
to zero in probability. -/
private lemma tendstoInProbZero_add
    {G : Type*} [NormedAddCommGroup G]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z W : ∀ n, Omega' n → G}
    (hZ : TendstoInProbZero P Z) (hW : TendstoInProbZero P W) :
    TendstoInProbZero P (fun n omega => Z n omega + W n omega) := by
  intro epsilon hepsilon
  have hsub : ∀ n, {omega | epsilon ≤ ‖Z n omega + W n omega‖} ⊆
      {omega | epsilon / 2 ≤ ‖Z n omega‖} ∪
        {omega | epsilon / 2 ≤ ‖W n omega‖} := by
    intro n omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
    simp only [Set.mem_setOf_eq] at homega
    exact (not_lt_of_ge homega) <|
      lt_of_le_of_lt (norm_add_le (Z n omega) (W n omega)) (by linarith)
  have hsum := (hZ (epsilon / 2) (half_pos hepsilon)).add
    (hW (epsilon / 2) (half_pos hepsilon))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_add] using hsum)
    (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n =>
      (measureReal_mono (hsub n)).trans (measureReal_union_le _ _))

/-- Pointwise norm domination preserves varying-base convergence in probability. -/
private lemma tendstoInProbZero_mono
    {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, Omega' n → G} {W : ∀ n, Omega' n → H}
    (hle : ∀ n omega, ‖Z n omega‖ ≤ ‖W n omega‖)
    (hW : TendstoInProbZero P W) : TendstoInProbZero P Z := by
  intro epsilon hepsilon
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hW epsilon hepsilon) (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n => measureReal_mono fun _ homega => homega.trans (hle _ _))

/-- Pointwise norm domination preserves boundedness in probability. -/
private lemma isBoundedInProb_mono
    {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, Omega' n → G} {W : ∀ n, Omega' n → H}
    (hle : ∀ n omega, ‖Z n omega‖ ≤ ‖W n omega‖)
    (hW : IsBoundedInProb P W) : IsBoundedInProb P Z := by
  intro epsilon hepsilon
  obtain ⟨M, hM⟩ := hW epsilon hepsilon
  exact ⟨M, fun n => (measureReal_mono fun _ homega =>
    homega.trans_le (hle _ _)).trans (hM n)⟩

/-- Sums of two bounded-in-probability families are bounded in probability. -/
private lemma isBoundedInProb_add
    {G : Type*} [NormedAddCommGroup G]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z W : ∀ n, Omega' n → G}
    (hZ : IsBoundedInProb P Z) (hW : IsBoundedInProb P W) :
    IsBoundedInProb P (fun n omega => Z n omega + W n omega) := by
  intro epsilon hepsilon
  obtain ⟨MZ, hMZ⟩ := hZ (epsilon / 2) (half_pos hepsilon)
  obtain ⟨MW, hMW⟩ := hW (epsilon / 2) (half_pos hepsilon)
  refine ⟨max MZ 0 + max MW 0, fun n => ?_⟩
  have hsub : {omega | max MZ 0 + max MW 0 < ‖Z n omega + W n omega‖} ⊆
      {omega | MZ < ‖Z n omega‖} ∪ {omega | MW < ‖W n omega‖} := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hnot
    have hZle : ‖Z n omega‖ ≤ max MZ 0 := hnot.1.trans (le_max_left _ _)
    have hWle : ‖W n omega‖ ≤ max MW 0 := hnot.2.trans (le_max_left _ _)
    exact (not_lt_of_ge ((norm_add_le _ _).trans (add_le_add hZle hWle))) homega
  exact (measureReal_mono hsub).trans <|
    (measureReal_union_le _ _).trans (by linarith [hMZ n, hMW n])

/-- A deterministic family is bounded in probability. -/
private lemma isBoundedInProb_const
    {G : Type*} [NormedAddCommGroup G]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)}
    (c : G) : IsBoundedInProb P (fun _ _ => c) := by
  intro epsilon hepsilon
  refine ⟨‖c‖, fun n => ?_⟩
  simpa using hepsilon.le

/-- Deterministic scalar multiplication preserves boundedness in probability. -/
private lemma isBoundedInProb_const_smul
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, Omega' n → G} (c : ℝ) (hZ : IsBoundedInProb P Z) :
    IsBoundedInProb P (fun n omega => c • Z n omega) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using (isBoundedInProb_const (P := P) (0 : G))
  · intro epsilon hepsilon
    obtain ⟨M, hM⟩ := hZ epsilon hepsilon
    refine ⟨|c| * M, fun n => ?_⟩
    refine (measureReal_mono fun omega homega => ?_).trans (hM n)
    simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs] at homega ⊢
    nlinarith [abs_pos.mpr hc]

/-- An `o_P(1)` approximation plus an arbitrarily small deterministic multiple
of an `O_P(1)` envelope is `o_P(1)`. -/
private lemma tendstoInProbZero_of_fixed_truncation
    {G A B C : Type*}
    [NormedAddCommGroup G] [NormedAddCommGroup A]
    [NormedAddCommGroup B] [NormedAddCommGroup C]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, Omega' n → G} {Am : ℕ → ∀ n, Omega' n → A}
    {Bf : ∀ n, Omega' n → B} {Cf : ∀ n, Omega' n → C}
    {c : ℕ → ℝ}
    (hA : ∀ m, TendstoInProbZero P (Am m))
    (hB : IsBoundedInProb P Bf)
    (hc : Tendsto c atTop (nhds 0))
    (hC : TendstoInProbZero P Cf)
    (hbound : ∀ m n omega, ‖Z n omega‖ ≤
      ‖Am m n omega‖ + |c m| * ‖Bf n omega‖ + ‖Cf n omega‖) :
    TendstoInProbZero P Z := by
  intro epsilon hepsilon
  refine Metric.tendsto_atTop.mpr fun eta heta => ?_
  obtain ⟨M, hM⟩ := hB (eta / 3) (by positivity)
  let M' : ℝ := max M 1
  have hM' : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcsmall : ∀ᶠ m in atTop, |c m| < epsilon / (3 * M') := by
    have hnhds : {x : ℝ | |x| < epsilon / (3 * M')} ∈ nhds 0 := by
      convert Metric.ball_mem_nhds (0 : ℝ)
        (by positivity : 0 < epsilon / (3 * M')) using 1
      ext x
      simp [Metric.mem_ball]
    exact hc hnhds
  obtain ⟨m, hm⟩ := hcsmall.exists
  have htail : |c m| * M' < epsilon / 3 := by
    have hm' : |c m| * (3 * M') < epsilon :=
      (lt_div_iff₀ (mul_pos (by norm_num) hM')).mp hm
    calc
      |c m| * M' = (|c m| * (3 * M')) / 3 := by ring
      _ < epsilon / 3 := div_lt_div_of_pos_right hm' (by norm_num)
  have hAsmall : ∀ᶠ n in atTop,
      (P n).real {omega | epsilon / 3 ≤ ‖Am m n omega‖} < eta / 3 :=
    (hA m (epsilon / 3) (by positivity)).eventually
      (Iio_mem_nhds (by positivity : 0 < eta / 3))
  have hCsmall : ∀ᶠ n in atTop,
      (P n).real {omega | epsilon / 3 ≤ ‖Cf n omega‖} < eta / 3 :=
    (hC (epsilon / 3) (by positivity)).eventually
      (Iio_mem_nhds (by positivity : 0 < eta / 3))
  apply eventually_atTop.mp
  filter_upwards [hAsmall, hCsmall] with n hAn hCn
  have hsub : {omega | epsilon ≤ ‖Z n omega‖} ⊆
      {omega | epsilon / 3 ≤ ‖Am m n omega‖} ∪
        {omega | M < ‖Bf n omega‖} ∪
          {omega | epsilon / 3 ≤ ‖Cf n omega‖} := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
    have hBle : ‖Bf n omega‖ ≤ M' :=
      (not_lt.mp hnot.1.2).trans (le_max_left _ _)
    have htail' : |c m| * ‖Bf n omega‖ < epsilon / 3 :=
      (mul_le_mul_of_nonneg_left hBle (abs_nonneg _)).trans_lt htail
    exact (not_lt_of_ge homega) <|
      lt_of_le_of_lt (hbound m n omega) (by linarith [hnot.1.1, hnot.2, htail'])
  have hunion : (P n).real
      ({omega | epsilon / 3 ≤ ‖Am m n omega‖} ∪
        {omega | M < ‖Bf n omega‖} ∪
          {omega | epsilon / 3 ≤ ‖Cf n omega‖}) ≤
      (P n).real {omega | epsilon / 3 ≤ ‖Am m n omega‖} +
        (P n).real {omega | M < ‖Bf n omega‖} +
          (P n).real {omega | epsilon / 3 ≤ ‖Cf n omega‖} := by
    exact (measureReal_union_le _ _).trans <|
      add_le_add_left (measureReal_union_le _ _) _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact (measureReal_mono hsub).trans_lt <|
    hunion.trans_lt (by linarith [hM n, hAn, hCn])

/-- A deterministic scalar multiple of an `o_P(1)` family is `o_P(1)`. -/
private lemma tendstoInProbZero_const_smul
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} {Z : ∀ n, Omega' n → G}
    (c : ℝ) (hZ : TendstoInProbZero P Z) :
    TendstoInProbZero P (fun n omega => c • Z n omega) := by
  intro epsilon hepsilon
  rcases eq_or_ne c 0 with rfl | hc
  · have hset : ∀ n, {omega | epsilon ≤ ‖(0 : ℝ) • Z n omega‖} =
        (∅ : Set (Omega' n)) := by
      intro n
      ext omega
      simp [not_le.mpr hepsilon]
    simp only [hset, measureReal_empty]
    exact tendsto_const_nhds
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    simpa only [norm_smul, Real.norm_eq_abs, div_le_iff₀ hcpos, mul_comm] using
      hZ (epsilon / |c|) (div_pos hepsilon hcpos)

/-- Pull an `L²(P)` function back to the common dominator using `sqrt (dP/dmu)`. -/
private lemma memLp_sqrt_rnDeriv_smul_of_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P mu : Measure Omega} [IsFiniteMeasure P] [SigmaFinite mu]
    (hPmu : P ≪ mu) {f : Omega → E} (hf : MemLp f 2 P) :
    MemLp (fun omega => Real.sqrt ((P.rnDeriv mu omega).toReal) • f omega) 2 mu := by
  have hP : P = mu.withDensity (P.rnDeriv mu) :=
    (Measure.withDensity_rnDeriv_eq P mu hPmu).symm
  let F : Lp E 2 P := hf.toLp f
  have hF_eq : (F : Omega → E) =ᵐ[P] f := MemLp.coeFn_toLp hf
  have hF_eq_density : (F : Omega → E) =ᵐ[mu.withDensity (P.rnDeriv mu)] f := by
    have hae : ae (mu.withDensity (P.rnDeriv mu)) = ae P := congrArg ae hP.symm
    rw [hae]
    exact hF_eq
  have hF_eq_mu :=
    (ae_withDensity_iff (Measure.measurable_rnDeriv P mu)).mp hF_eq_density
  have hweighted_meas : AEStronglyMeasurable
      (fun omega => Real.sqrt ((P.rnDeriv mu omega).toReal) • f omega) mu := by
    have hF_meas : StronglyMeasurable (F : Omega → E) := Lp.stronglyMeasurable F
    have hmeas : AEStronglyMeasurable
        (fun omega => Real.sqrt ((P.rnDeriv mu omega).toReal) • (F : Omega → E) omega) mu :=
      ((Measure.measurable_rnDeriv P mu).ennreal_toReal.sqrt.aestronglyMeasurable).smul
        hF_meas.aestronglyMeasurable
    refine hmeas.congr ?_
    filter_upwards [hF_eq_mu] with omega homega
    by_cases hrn : P.rnDeriv mu omega = 0
    · simp [hrn]
    · rw [homega hrn]
  have hi : Integrable (fun omega => ‖f omega‖ ^ 2 * (P.rnDeriv mu omega).toReal) mu := by
    rw [← MeasureTheory.integrable_withDensity_iff
      (Measure.measurable_rnDeriv P mu) (Measure.rnDeriv_lt_top P mu), ← hP]
    exact hf.integrable_norm_pow (by norm_num)
  rw [memLp_two_iff_integrable_sq_norm hweighted_meas]
  convert hi using 1
  funext omega
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt ENNReal.toReal_nonneg]
  ring

/-- Bochner-valued L2 Cauchy--Schwarz, in the exact square-integral form used below. -/
private lemma norm_integral_smul_le_sqrt_integral_sq
    {d : ℕ} {mu : Measure Omega} {f : Omega → ℝ}
    {g : Omega → EuclideanSpace ℝ (Fin d)}
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    ‖∫ omega, f omega • g omega ∂mu‖ ≤
      Real.sqrt (∫ omega, f omega ^ 2 ∂mu) *
        Real.sqrt (∫ omega, ‖g omega‖ ^ 2 ∂mu) := by
  calc
    _ ≤ ∫ omega, ‖f omega • g omega‖ ∂mu := norm_integral_le_integral_norm _
    _ = ∫ omega, |f omega| * ‖g omega‖ ∂mu := by
      apply integral_congr_ae
      exact Eventually.of_forall fun omega => by
        change ‖f omega • g omega‖ = |f omega| * ‖g omega‖
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |∫ omega, |f omega| * ‖g omega‖ ∂mu| := le_abs_self _
    _ ≤ _ := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
          mu hf.norm hg.norm

/-- Minkowski's inequality in the real square-integral form used by the QMD
and score-energy estimates below. -/
private lemma sqrt_integral_sq_add_le
    {mu : Measure Omega} {f g : Omega → ℝ}
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    Real.sqrt (∫ omega, (f omega + g omega) ^ 2 ∂mu) ≤
      Real.sqrt (∫ omega, f omega ^ 2 ∂mu) +
        Real.sqrt (∫ omega, g omega ^ 2 ∂mu) := by
  change Real.sqrt (∫ omega, (f + g) omega ^ 2 ∂mu) ≤
    Real.sqrt (∫ omega, f omega ^ 2 ∂mu) +
      Real.sqrt (∫ omega, g omega ^ 2 ∂mu)
  rw [AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
      (hf.add hg),
    AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal hf,
    AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal hg]
  have hle := eLpNorm_add_le hf.1 hg.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htop : eLpNorm f 2 mu + eLpNorm g 2 mu ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hf.2.ne, hg.2.ne⟩
  have hreal := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_add hf.2.ne hg.2.ne] at hreal
  exact hreal

/-- Minkowski's inequality for square integrals of normed-valued functions. -/
private lemma sqrt_integral_norm_sq_add_le
    {E : Type*} [NormedAddCommGroup E]
    {mu : Measure Omega} {f g : Omega → E}
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    Real.sqrt (∫ omega, ‖f omega + g omega‖ ^ 2 ∂mu) ≤
      Real.sqrt (∫ omega, ‖f omega‖ ^ 2 ∂mu) +
        Real.sqrt (∫ omega, ‖g omega‖ ^ 2 ∂mu) := by
  have hpoint : ∀ omega, ‖f omega + g omega‖ ^ 2 ≤
      (‖f omega‖ + ‖g omega‖) ^ 2 := fun omega =>
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
      (norm_add_le _ _)
  have hint : (∫ omega, ‖f omega + g omega‖ ^ 2 ∂mu) ≤
      ∫ omega, (‖f omega‖ + ‖g omega‖) ^ 2 ∂mu :=
    integral_mono ((hf.add hg).norm.integrable_sq)
      ((hf.norm.add hg.norm).integrable_sq) hpoint
  exact (Real.sqrt_le_sqrt hint).trans (sqrt_integral_sq_add_le hf.norm hg.norm)

/-- A square-root Radon--Nikodym pullback preserves the `L²` energy. -/
private lemma integral_norm_sqrt_rnDeriv_smul_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P mu : Measure Omega} [IsFiniteMeasure P] [SigmaFinite mu]
    (hPmu : P ≪ mu) {f : Omega → E} (hf : MemLp f 2 P) :
    (∫ omega,
        ‖Real.sqrt ((P.rnDeriv mu omega).toReal) • f omega‖ ^ 2 ∂mu) =
      ∫ omega, ‖f omega‖ ^ 2 ∂P := by
  have hi : Integrable (fun omega => ‖f omega‖ ^ 2) P :=
    hf.integrable_norm_pow (by norm_num)
  rw [← integral_rnDeriv_smul hPmu]
  apply integral_congr_ae
  exact Eventually.of_forall fun omega => by
    change ‖Real.sqrt ((P.rnDeriv mu omega).toReal) • f omega‖ ^ 2 =
      (P.rnDeriv mu omega).toReal * ‖f omega‖ ^ 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]

/-- The `L²(P)` energy of the score above a diverging norm threshold vanishes. -/
private lemma score_tail_energy_tendsto
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {g : Omega → EuclideanSpace ℝ (Fin d)}
    (hgmeas : Measurable g) (hg : MemLp g 2 P) :
    Tendsto (fun m : ℕ => Real.sqrt (∫ omega,
        ‖{x | (m : ℝ) < ‖g x‖}.indicator g omega‖ ^ 2 ∂P))
      atTop (nhds 0) := by
  have hnormmeas : Measurable (fun omega => ‖g omega‖) := hgmeas.norm
  have htail := AsymptoticStatistics.ForMathlib.tendsto_setIntegral_tail_of_integrable
    (hg.integrable_norm_pow (by norm_num)) hnormmeas tendsto_natCast_atTop_atTop
  have heq : ∀ m : ℕ,
      (∫ omega, ‖{x | (m : ℝ) < ‖g x‖}.indicator g omega‖ ^ 2 ∂P) =
        ∫ omega in {x | (m : ℝ) < ‖g x‖}, ‖g omega‖ ^ 2 ∂P := by
    intro m
    rw [← integral_indicator (measurableSet_lt measurable_const hnormmeas)]
    apply integral_congr_ae
    exact Eventually.of_forall fun omega => by
      change ‖{x | (m : ℝ) < ‖g x‖}.indicator g omega‖ ^ 2 =
        {x | (m : ℝ) < ‖g x‖}.indicator (fun x => ‖g x‖ ^ 2) omega
      by_cases homega : (m : ℝ) < ‖g omega‖
      · have homega' : omega ∈ {x : Omega | (m : ℝ) < ‖g x‖} := homega
        rw [Set.indicator_of_mem homega', Set.indicator_of_mem homega']
      · have homega' : omega ∉ {x : Omega | (m : ℝ) < ‖g x‖} := homega
        rw [Set.indicator_of_notMem homega', Set.indicator_of_notMem homega']
        simp
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp htail
  simp only [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr' (Eventually.of_forall fun m => ?_)
  change Real.sqrt (∫ omega in {x | (m : ℝ) < ‖g x‖}, ‖g omega‖ ^ 2 ∂P) =
    Real.sqrt (∫ omega,
      ‖{x | (m : ℝ) < ‖g x‖}.indicator g omega‖ ^ 2 ∂P)
  rw [heq m]

set_option maxHeartbeats 1500000 in
-- This is the deterministic bounded-score/tail split on pp. 392--393.
private lemma native_modelShift_truncation_bound
    {d : ℕ} {mu : Measure Omega}
    {u : EuclideanSpace ℝ (Fin d)} {m : ℝ}
    {s t : Omega → ℝ}
    {g gSmall gTail z z0 : Omega → EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ ≤ 1) (hm : 0 ≤ m)
    (hgSplit : ∀ omega, g omega = gSmall omega + gTail omega)
    (hgSmall : ∀ omega, ‖gSmall omega‖ ≤ m)
    (hst : MemLp (s - t) 2 mu)
    (htz : MemLp (fun omega => t omega • z omega) 2 mu)
    (hsz : MemLp (fun omega => s omega • z omega) 2 mu)
    (htg : MemLp (fun omega => t omega • g omega) 2 mu)
    (htgTail : MemLp (fun omega => t omega • gTail omega) 2 mu)
    (htdiff : MemLp (fun omega => t omega • (z omega - z0 omega)) 2 mu)
    (hsmallZ : MemLp
      (fun omega => ⟪u, gSmall omega⟫_ℝ • (t omega • z omega)) 2 mu)
    (htailCoef : MemLp (fun omega => ⟪u, gTail omega⟫_ℝ * t omega) 2 mu)
    (htailZ : MemLp (fun omega => (s omega - t omega) • z omega) 2 mu)
    (hfullCoef : MemLp (fun omega => ⟪u, g omega⟫_ℝ * t omega) 2 mu) :
    ‖∫ omega, (⟪u, g omega⟫_ℝ * t omega) •
        ((s omega + t omega) • z omega -
          (2 : ℝ) • (t omega • z0 omega)) ∂mu‖ ≤
      m * Real.sqrt (∫ omega, (s omega - t omega) ^ 2 ∂mu) *
          Real.sqrt (∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu) +
        Real.sqrt (∫ omega, ‖t omega • gTail omega‖ ^ 2 ∂mu) *
          Real.sqrt (2 * ((∫ omega, ‖s omega • z omega‖ ^ 2 ∂mu) +
            ∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu)) +
        2 * Real.sqrt (∫ omega, ‖t omega • g omega‖ ^ 2 ∂mu) *
          Real.sqrt (∫ omega, ‖t omega • (z omega - z0 omega)‖ ^ 2 ∂mu) := by
  let I1 : EuclideanSpace ℝ (Fin d) :=
    ∫ omega, (s omega - t omega) •
      (⟪u, gSmall omega⟫_ℝ • (t omega • z omega)) ∂mu
  let I2 : EuclideanSpace ℝ (Fin d) :=
    ∫ omega, (⟪u, gTail omega⟫_ℝ * t omega) •
      ((s omega - t omega) • z omega) ∂mu
  let I3 : EuclideanSpace ℝ (Fin d) :=
    ∫ omega, (⟪u, g omega⟫_ℝ * t omega) •
      (t omega • (z omega - z0 omega)) ∂mu
  have hi1 : Integrable (fun omega => (s omega - t omega) •
      (⟪u, gSmall omega⟫_ℝ • (t omega • z omega))) mu :=
    memLp_one_iff_integrable.mp
      (hsmallZ.smul hst : MemLp _ 1 mu)
  have hi2 : Integrable (fun omega => (⟪u, gTail omega⟫_ℝ * t omega) •
      ((s omega - t omega) • z omega)) mu :=
    memLp_one_iff_integrable.mp
      (htailZ.smul htailCoef : MemLp _ 1 mu)
  have hi3 : Integrable (fun omega => (⟪u, g omega⟫_ℝ * t omega) •
      (t omega • (z omega - z0 omega))) mu :=
    memLp_one_iff_integrable.mp
      (htdiff.smul hfullCoef : MemLp _ 1 mu)
  have hi3c : Integrable (fun omega => (2 : ℝ) •
      ((⟪u, g omega⟫_ℝ * t omega) •
        (t omega • (z omega - z0 omega)))) mu :=
    memLp_one_iff_integrable.mp
      ((htdiff.smul hfullCoef : MemLp _ 1 mu).const_smul (2 : ℝ))
  have hdecomp :
      (∫ omega, (⟪u, g omega⟫_ℝ * t omega) •
          ((s omega + t omega) • z omega -
            (2 : ℝ) • (t omega • z0 omega)) ∂mu) =
        I1 + I2 + (2 : ℝ) • I3 := by
    calc
      _ = ∫ omega,
          ((s omega - t omega) •
              (⟪u, gSmall omega⟫_ℝ • (t omega • z omega)) +
            (⟪u, gTail omega⟫_ℝ * t omega) •
              ((s omega - t omega) • z omega)) +
            (2 : ℝ) • ((⟪u, g omega⟫_ℝ * t omega) •
              (t omega • (z omega - z0 omega))) ∂mu := by
        apply integral_congr_ae
        exact Eventually.of_forall fun omega => by
          change (⟪u, g omega⟫_ℝ * t omega) •
              ((s omega + t omega) • z omega -
                (2 : ℝ) • (t omega • z0 omega)) =
            ((s omega - t omega) •
                (⟪u, gSmall omega⟫_ℝ • (t omega • z omega)) +
              (⟪u, gTail omega⟫_ℝ * t omega) •
                ((s omega - t omega) • z omega)) +
              (2 : ℝ) • ((⟪u, g omega⟫_ℝ * t omega) •
                (t omega • (z omega - z0 omega)))
          rw [hgSplit omega, inner_add_right]
          module
      _ = (∫ omega,
            (s omega - t omega) •
                (⟪u, gSmall omega⟫_ℝ • (t omega • z omega)) +
              (⟪u, gTail omega⟫_ℝ * t omega) •
                ((s omega - t omega) • z omega) ∂mu) +
          ∫ omega, (2 : ℝ) • ((⟪u, g omega⟫_ℝ * t omega) •
            (t omega • (z omega - z0 omega))) ∂mu :=
        integral_add (hi1.add hi2) hi3c
      _ = I1 + I2 + (2 : ℝ) • I3 := by
        rw [integral_add hi1 hi2, integral_smul]
  have hsmallPoint : ∀ omega,
      ‖⟪u, gSmall omega⟫_ℝ • (t omega • z omega)‖ ^ 2 ≤
        m ^ 2 * ‖t omega • z omega‖ ^ 2 := by
    intro omega
    have hi : |⟪u, gSmall omega⟫_ℝ| ≤ m := calc
      _ ≤ ‖u‖ * ‖gSmall omega‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * m := mul_le_mul hu (hgSmall omega) (norm_nonneg _) (by norm_num)
      _ = m := one_mul _
    have hisq : |⟪u, gSmall omega⟫_ℝ| ^ 2 ≤ m ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hm).2 hi
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_right hisq (sq_nonneg _)
  have hsmallInt :
      (∫ omega, ‖⟪u, gSmall omega⟫_ℝ •
          (t omega • z omega)‖ ^ 2 ∂mu) ≤
        m ^ 2 * ∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu := by
    calc
      _ ≤ ∫ omega, m ^ 2 * ‖t omega • z omega‖ ^ 2 ∂mu :=
        integral_mono (hsmallZ.integrable_norm_pow (by norm_num))
          (htz.integrable_norm_pow (by norm_num) |>.const_mul _) hsmallPoint
      _ = _ := by rw [integral_const_mul]
  have hsmallSqrt :
      Real.sqrt (∫ omega, ‖⟪u, gSmall omega⟫_ℝ •
          (t omega • z omega)‖ ^ 2 ∂mu) ≤
        m * Real.sqrt (∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu) := by
    have hsqrt := Real.sqrt_le_sqrt hsmallInt
    rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hm] at hsqrt
    exact hsqrt
  have htailCoefPoint : ∀ omega,
      (⟪u, gTail omega⟫_ℝ * t omega) ^ 2 ≤
        ‖t omega • gTail omega‖ ^ 2 := by
    intro omega
    have hi : |⟪u, gTail omega⟫_ℝ| ≤ ‖gTail omega‖ := calc
      _ ≤ ‖u‖ * ‖gTail omega‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖gTail omega‖ :=
        mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      _ = _ := one_mul _
    have hisq : ⟪u, gTail omega⟫_ℝ ^ 2 ≤ ‖gTail omega‖ ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hi
    calc
      (⟪u, gTail omega⟫_ℝ * t omega) ^ 2 =
          ⟪u, gTail omega⟫_ℝ ^ 2 * t omega ^ 2 := by ring
      _ ≤ ‖gTail omega‖ ^ 2 * t omega ^ 2 :=
        mul_le_mul_of_nonneg_right hisq (sq_nonneg _)
      _ = ‖t omega • gTail omega‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
  have htailCoefInt :
      (∫ omega, (⟪u, gTail omega⟫_ℝ * t omega) ^ 2 ∂mu) ≤
        ∫ omega, ‖t omega • gTail omega‖ ^ 2 ∂mu :=
    integral_mono htailCoef.integrable_sq
      (htgTail.integrable_norm_pow (by norm_num)) htailCoefPoint
  have htailCoefSqrt :
      Real.sqrt (∫ omega, (⟪u, gTail omega⟫_ℝ * t omega) ^ 2 ∂mu) ≤
        Real.sqrt (∫ omega, ‖t omega • gTail omega‖ ^ 2 ∂mu) :=
    Real.sqrt_le_sqrt htailCoefInt
  have htailZPoint : ∀ omega,
      ‖(s omega - t omega) • z omega‖ ^ 2 ≤
        2 * (‖s omega • z omega‖ ^ 2 + ‖t omega • z omega‖ ^ 2) := by
    intro omega
    have hn : ‖(s omega - t omega) • z omega‖ ≤
        ‖s omega • z omega‖ + ‖t omega • z omega‖ := by
      rw [sub_smul]
      exact norm_sub_le _ _
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hn
    nlinarith [sq_nonneg (‖s omega • z omega‖ - ‖t omega • z omega‖)]
  have htailZInt :
      (∫ omega, ‖(s omega - t omega) • z omega‖ ^ 2 ∂mu) ≤
        2 * ((∫ omega, ‖s omega • z omega‖ ^ 2 ∂mu) +
          ∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu) := by
    calc
      _ ≤ ∫ omega, 2 *
          (‖s omega • z omega‖ ^ 2 + ‖t omega • z omega‖ ^ 2) ∂mu :=
        integral_mono (htailZ.integrable_norm_pow (by norm_num))
          (((hsz.integrable_norm_pow (by norm_num)).add
            (htz.integrable_norm_pow (by norm_num))).const_mul 2) htailZPoint
      _ = _ := by rw [integral_const_mul, integral_add
        (hsz.integrable_norm_pow (by norm_num)) (htz.integrable_norm_pow (by norm_num))]
  have htailZSqrt :
      Real.sqrt (∫ omega, ‖(s omega - t omega) • z omega‖ ^ 2 ∂mu) ≤
        Real.sqrt (2 * ((∫ omega, ‖s omega • z omega‖ ^ 2 ∂mu) +
          ∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu)) :=
    Real.sqrt_le_sqrt htailZInt
  have hfullCoefPoint : ∀ omega,
      (⟪u, g omega⟫_ℝ * t omega) ^ 2 ≤ ‖t omega • g omega‖ ^ 2 := by
    intro omega
    have hi : |⟪u, g omega⟫_ℝ| ≤ ‖g omega‖ := calc
      _ ≤ ‖u‖ * ‖g omega‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖g omega‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      _ = _ := one_mul _
    have hisq : ⟪u, g omega⟫_ℝ ^ 2 ≤ ‖g omega‖ ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hi
    calc
      (⟪u, g omega⟫_ℝ * t omega) ^ 2 =
          ⟪u, g omega⟫_ℝ ^ 2 * t omega ^ 2 := by ring
      _ ≤ ‖g omega‖ ^ 2 * t omega ^ 2 :=
        mul_le_mul_of_nonneg_right hisq (sq_nonneg _)
      _ = ‖t omega • g omega‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
  have hfullCoefInt :
      (∫ omega, (⟪u, g omega⟫_ℝ * t omega) ^ 2 ∂mu) ≤
        ∫ omega, ‖t omega • g omega‖ ^ 2 ∂mu :=
    integral_mono hfullCoef.integrable_sq
      (htg.integrable_norm_pow (by norm_num)) hfullCoefPoint
  have hfullCoefSqrt :
      Real.sqrt (∫ omega, (⟪u, g omega⟫_ℝ * t omega) ^ 2 ∂mu) ≤
        Real.sqrt (∫ omega, ‖t omega • g omega‖ ^ 2 ∂mu) :=
    Real.sqrt_le_sqrt hfullCoefInt
  have hcs1 := norm_integral_smul_le_sqrt_integral_sq hst hsmallZ
  have hcs2 := norm_integral_smul_le_sqrt_integral_sq htailCoef htailZ
  have hcs3 := norm_integral_smul_le_sqrt_integral_sq hfullCoef htdiff
  have hI1 : ‖I1‖ ≤
      m * Real.sqrt (∫ omega, (s omega - t omega) ^ 2 ∂mu) *
        Real.sqrt (∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu) := by
    calc
      _ ≤ Real.sqrt (∫ omega, (s omega - t omega) ^ 2 ∂mu) *
          Real.sqrt (∫ omega, ‖⟪u, gSmall omega⟫_ℝ •
            (t omega • z omega)‖ ^ 2 ∂mu) := hcs1
      _ ≤ Real.sqrt (∫ omega, (s omega - t omega) ^ 2 ∂mu) *
          (m * Real.sqrt (∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu)) :=
        mul_le_mul_of_nonneg_left hsmallSqrt (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hI2 : ‖I2‖ ≤
      Real.sqrt (∫ omega, ‖t omega • gTail omega‖ ^ 2 ∂mu) *
        Real.sqrt (2 * ((∫ omega, ‖s omega • z omega‖ ^ 2 ∂mu) +
          ∫ omega, ‖t omega • z omega‖ ^ 2 ∂mu)) := by
    calc
      _ ≤ Real.sqrt (∫ omega, (⟪u, gTail omega⟫_ℝ * t omega) ^ 2 ∂mu) *
          Real.sqrt (∫ omega, ‖(s omega - t omega) • z omega‖ ^ 2 ∂mu) := hcs2
      _ ≤ Real.sqrt (∫ omega, ‖t omega • gTail omega‖ ^ 2 ∂mu) *
          Real.sqrt (∫ omega, ‖(s omega - t omega) • z omega‖ ^ 2 ∂mu) :=
        mul_le_mul_of_nonneg_right htailCoefSqrt (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left htailZSqrt (Real.sqrt_nonneg _)
  have hI3 : ‖I3‖ ≤
      Real.sqrt (∫ omega, ‖t omega • g omega‖ ^ 2 ∂mu) *
        Real.sqrt (∫ omega, ‖t omega • (z omega - z0 omega)‖ ^ 2 ∂mu) := by
    calc
      _ ≤ Real.sqrt (∫ omega, (⟪u, g omega⟫_ℝ * t omega) ^ 2 ∂mu) *
          Real.sqrt (∫ omega, ‖t omega • (z omega - z0 omega)‖ ^ 2 ∂mu) := hcs3
      _ ≤ _ := mul_le_mul_of_nonneg_right hfullCoefSqrt (Real.sqrt_nonneg _)
  rw [hdecomp]
  calc
    ‖I1 + I2 + (2 : ℝ) • I3‖ ≤ ‖I1‖ + ‖I2‖ + 2 * ‖I3‖ := by
      calc
        _ ≤ ‖I1 + I2‖ + ‖(2 : ℝ) • I3‖ := norm_add_le _ _
        _ ≤ (‖I1‖ + ‖I2‖) + 2 * ‖I3‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          gcongr
          exact norm_add_le _ _
    _ ≤ _ := add_le_add (add_le_add hI1 hI2)
      (mul_le_mul_of_nonneg_left hI3 (by norm_num))
    _ = _ := by ring

/-- The pointwise square-root-density transport identity. -/
private lemma scalar_sqrt_transport_identity (a b z e c ell : ℝ) :
    z * a ^ 2 - z * b ^ 2 - e * (c * ell * b ^ 2) =
      z * (a + b) * (a - b - e / 2 * ell * b) +
        e / 2 * ((z * (a + b) - 2 * c * b) * (ell * b)) := by
  ring

/-- Vector version of the same square-root-density transport identity. -/
private lemma vector_sqrt_transport_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a b ell : ℝ) (z v : E) :
    a ^ 2 • z - b ^ 2 • z - (ell * b ^ 2) • v =
      (a - b - (1 / 2 : ℝ) * ell * b) • ((a + b) • z) +
        (1 / 2 : ℝ) • ((ell * b) • ((a + b) • z - (2 * b) • v)) := by
  module

/-- The raw moving-model bias from vdV (25.52):
`sqrt n * P_{thetaHat,eta} scoreHat`.

The path parameter is the estimator displacement from `theta0`; hence the
nuisance component of the integrating law is fixed at truth.  At `n = 0`,
`Real.sqrt 0 = 0`, so the definition is zero regardless of the integral. -/
noncomputable def rawMovingBias
    {P : Measure Omega} [IsProbabilityMeasure P] (gamma : QMDPath P)
    (estimator : ∀ n, (Fin n → Omega) → ℝ) (theta0 : ℝ)
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → ℝ)
    (n : ℕ) (X : Fin n → Omega) : ℝ :=
  Real.sqrt n * ∫ omega, scoreHat n X omega
    ∂(gamma.curve (estimator n X - theta0))

/-- Honest analytic hypotheses for transporting a random scalar score along a
dominated QMD path.

The bundle contains only integrability, consistency, and the three robust
Hellinger-weighted L2 conditions (membership, tightness, and transport).  In
particular, it contains neither an integral-shift expansion nor an
asymptotic-linearity conclusion. -/
structure HellingerScoreTransportHyp
    (P : Measure Omega) [IsProbabilityMeasure P]
    (gamma : QMDPath P)
    (estimator : ∀ n, (Fin n → Omega) → ℝ) (theta0 : ℝ)
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → ℝ)
    (score0 : Omega → ℝ) : Prop where
  /-- the random score is integrable under the true law. -/
  scoreHat_integrable_truth : ∀ n X, Integrable (scoreHat n X) P
  /-- the random score is integrable under the moving law. -/
  scoreHat_integrable_moving : ∀ n X,
    Integrable (scoreHat n X) (gamma.curve (estimator n X - theta0))
  /-- the limiting score belongs to L2 of the true law. -/
  score0_memLp : MemLp score0 2 P
  /-- the Hellinger-weighted random score is genuinely in
  `L2(gamma.dominating)`.  This prevents the Bochner-integral convention for
  non-integrable functions from making the transport condition vacuous. -/
  weightedScore_memLp : ∀ n X, MemLp (fun omega =>
    scoreHat n X omega *
      (Real.sqrt (((gamma.curve (estimator n X - theta0)).rnDeriv
          gamma.dominating omega).toReal)
        + Real.sqrt (((gamma.curve 0).rnDeriv
            gamma.dominating omega).toReal))) 2 gamma.dominating
  /-- the L2 norms of the Hellinger-weighted random scores are
  bounded in probability.  This is the `O_P(1)` factor paired with the
  normalized QMD square-root-density remainder. -/
  weightedScore_tight : IsBoundedInProb
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega,
      |scoreHat n X omega *
        (Real.sqrt (((gamma.curve (estimator n X - theta0)).rnDeriv
            gamma.dominating omega).toReal)
          + Real.sqrt (((gamma.curve 0).rnDeriv
              gamma.dominating omega).toReal))| ^ 2
      ∂gamma.dominating))
  /-- Hellinger-weighted L2 transport of the random score.
  The expression is the genuine square-root-density tangent transport
  `scoreHat * (sqrt p_delta + sqrt p_0) - 2 * score0 * sqrt p_0`.
  This is an analytic norm condition, not the desired integral-shift result. -/
  weightedScore_transport : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X =>
      Real.sqrt (∫ omega,
        |scoreHat n X omega *
            (Real.sqrt (((gamma.curve (estimator n X - theta0)).rnDeriv
              gamma.dominating omega).toReal)
              + Real.sqrt (((gamma.curve 0).rnDeriv
                  gamma.dominating omega).toReal))
          - 2 * score0 omega *
              Real.sqrt (((gamma.curve 0).rnDeriv
                gamma.dominating omega).toReal)| ^ 2
        ∂gamma.dominating))
  /-- consistency of the estimator along the QMD path. -/
  consistency : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => estimator n X - theta0)

set_option maxHeartbeats 1200000 in
-- The RN/Bochner normalization proof elaborates several large dependent integrals.
/-- QMD model shift normalized by the nonzero parameter displacement.

This is the rate-free transport statement: consistency selects the local QMD
regime.  The value at zero is set explicitly to zero, avoiding a false demand
that an arbitrary `0/0` representation converge.

The proof uses `h.consistency` to localize the punctured-neighborhood QMD limit;
`weightedScore_memLp` excludes Bochner fallback; `weightedScore_tight` pairs
with the normalized QMD remainder; and `weightedScore_transport` identifies
the limiting cross moment. -/
theorem qmdPath_modelShift_normalized_oP
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : ∀ n, (Fin n → Omega) → ℝ} {theta0 : ℝ}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → ℝ}
    {score0 : Omega → ℝ}
    (h : HellingerScoreTransportHyp P gamma estimator theta0 scoreHat score0) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let delta := estimator n X - theta0
        if delta = 0 then 0 else
          (((∫ omega, scoreHat n X omega ∂(gamma.curve delta)) -
              ∫ omega, scoreHat n X omega ∂P)
            - delta *
                ∫ omega, score0 omega * (gamma.score : Omega → ℝ) omega ∂P)
            / |delta|) := by
  let s : ℝ → Omega → ℝ := fun delta omega =>
    Real.sqrt (((gamma.curve delta).rnDeriv gamma.dominating omega).toReal)
  let g : Omega → ℝ := gamma.score
  let r : ℝ → Omega → ℝ := fun delta omega =>
    s delta omega - s 0 omega - (delta / 2) * g omega * s 0 omega
  let W : ∀ n, (Fin n → Omega) → Omega → ℝ := fun n X omega =>
    scoreHat n X omega * (s (estimator n X - theta0) omega + s 0 omega)
  let K : ∀ n, (Fin n → Omega) → Omega → ℝ := fun n X omega =>
    W n X omega - 2 * score0 omega * s 0 omega
  let K0 : Omega → ℝ := fun omega => g omega * s 0 omega
  have hs : ∀ delta, MemLp (s delta) 2 gamma.dominating := by
    intro delta
    letI := gamma.curve_isProbability delta
    exact AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
      (gamma.curve_absContinuous delta)
  have hPac : P ≪ gamma.dominating := by
    simpa only [gamma.curve_at_zero] using gamma.curve_absContinuous 0
  have hscore0s0 : MemLp (fun omega => s 0 omega * score0 omega) 2 gamma.dominating := by
    rw [show s 0 = fun omega =>
      Real.sqrt ((P.rnDeriv gamma.dominating omega).toReal) from by
        funext omega; simp [s, gamma.curve_at_zero]]
    exact memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := gamma.dominating)
      hPac h.score0_memLp
  have hgP : MemLp g 2 P := by
    simpa [g] using Lp.memLp (gamma.score : Lp ℝ 2 P)
  have hK0 : MemLp K0 2 gamma.dominating := by
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := gamma.dominating) hPac hgP
    simpa [K0, s, g, gamma.curve_at_zero, mul_comm] using hm
  have hr : ∀ delta, MemLp (r delta) 2 gamma.dominating := fun delta => by
    simpa [r, K0, mul_assoc] using!
      ((hs delta).sub (hs 0)).sub (hK0.const_mul (delta / 2))
  let qraw : ℝ → ℝ := fun delta =>
    Real.sqrt (∫ omega, r delta omega ^ 2 ∂gamma.dominating) / |delta|
  let q : ℝ → ℝ := fun delta => if delta = 0 then 0 else qraw delta
  have hqraw : Tendsto qraw (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp
      gamma.qmd_limit
    simp only [Function.comp_def, ENNReal.toReal_zero] at ht
    refine ht.congr' (Eventually.of_forall fun delta => ?_)
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (abs_nonneg delta),
      ← AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
        (hr delta)]
  have hq : Tendsto q (𝓝 (0 : ℝ)) (𝓝 0) :=
    tendsto_zeroExtension qraw q hqraw (by simp [q]) (by intro x hx; simp [q, hx])
  have hq_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => q (estimator n X - theta0)) :=
    tendstoInProbZero_comp_zero h.consistency hq
  have hW_tight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, W n X omega ^ 2 ∂gamma.dominating)) := by
    simpa only [W, s, sq_abs] using h.weightedScore_tight
  have hterm1 := tendstoInProbZero_of_isBoundedInProb_mul hW_tight hq_prob
  have hK_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, K n X omega ^ 2 ∂gamma.dominating)) := by
    simpa only [K, W, s, sq_abs] using h.weightedScore_transport
  have hterm2 := tendstoInProbZero_const_smul
    (Real.sqrt (∫ omega, K0 omega ^ 2 ∂gamma.dominating) / 2) hK_prob
  have henv := tendstoInProbZero_add hterm1 hterm2
  refine tendstoInProbZero_mono (fun n X => ?_) henv
  simp only [q, qraw, smul_eq_mul]
  by_cases hdelta : estimator n X - theta0 = 0
  · simp only [hdelta, ↓reduceIte, norm_zero, mul_zero, zero_add]
    exact norm_nonneg _
  · simp only [hdelta, ↓reduceIte]
    have hWmem : MemLp (W n X) 2 gamma.dominating := h.weightedScore_memLp n X
    have hKmem : MemLp (K n X) 2 gamma.dominating := by
      have hm : MemLp (fun omega => 2 * score0 omega * s 0 omega) 2
          gamma.dominating := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscore0s0.const_mul 2
      exact hWmem.sub hm
    have hshift :
        ((∫ omega, scoreHat n X omega ∂(gamma.curve (estimator n X - theta0))) -
            ∫ omega, scoreHat n X omega ∂P) -
          (estimator n X - theta0) * ∫ omega, score0 omega * g omega ∂P =
        ∫ omega, W n X omega * r (estimator n X - theta0) omega ∂gamma.dominating +
          ((estimator n X - theta0) / 2) *
            ∫ omega, K n X omega * K0 omega ∂gamma.dominating := by
      letI := gamma.curve_isProbability (estimator n X - theta0)
      have hi_delta := (integrable_toReal_rnDeriv_mul_iff
        (gamma.curve_absContinuous (estimator n X - theta0))).2
          (h.scoreHat_integrable_moving n X)
      have hi_zero := (integrable_toReal_rnDeriv_mul_iff hPac).2
        (h.scoreHat_integrable_truth n X)
      have hi_cross : Integrable (fun omega => score0 omega * g omega) P :=
        h.score0_memLp.integrable_mul hgP
      have hi_cross_mu := (integrable_toReal_rnDeriv_mul_iff hPac).2
        (by simpa [mul_comm] using hi_cross)
      rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          (gamma.curve_absContinuous (estimator n X - theta0)) (scoreHat n X),
        AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          hPac (scoreHat n X),
        AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          hPac (fun omega => score0 omega * g omega),
        ← integral_sub (by simpa [s, mul_comm, Real.sq_sqrt ENNReal.toReal_nonneg] using hi_delta)
          (by simpa [s, mul_comm, Real.sq_sqrt ENNReal.toReal_nonneg] using hi_zero),
        ← integral_const_mul,
        ← integral_sub,
        ← integral_const_mul,
        ← integral_add]
      · refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
        simp only [W, K, K0, r, s]
        rw [gamma.curve_at_zero]
        have hd := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ ((gamma.curve (estimator n X - theta0)).rnDeriv
            gamma.dominating omega).toReal)
        have h0 := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ (P.rnDeriv gamma.dominating omega).toReal)
        simpa only [hd, h0] using scalar_sqrt_transport_identity
          (Real.sqrt (((gamma.curve (estimator n X - theta0)).rnDeriv
            gamma.dominating omega).toReal))
          (Real.sqrt ((P.rnDeriv gamma.dominating omega).toReal))
          (scoreHat n X omega) (estimator n X - theta0) (score0 omega) (g omega)
      · exact hWmem.integrable_mul (hr _)
      · exact (hKmem.integrable_mul hK0).const_mul _
      · simpa [Pi.sub_apply, mul_comm] using! hi_delta.sub hi_zero
      · simpa [mul_assoc, mul_comm, mul_left_comm] using hi_cross_mu.const_mul
          (estimator n X - theta0)
    rw [hshift]
    have hcs1 := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
      gamma.dominating hWmem (hr (estimator n X - theta0))
    have hcs2 := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
      gamma.dominating hKmem hK0
    simp only [Real.norm_eq_abs]
    rw [abs_div]
    simp only [abs_abs]
    have henv_nonneg : 0 ≤
        Real.sqrt (∫ omega, W n X omega ^ 2 ∂gamma.dominating) *
            (Real.sqrt (∫ omega, r (estimator n X - theta0) omega ^ 2
              ∂gamma.dominating) / |estimator n X - theta0|) +
          Real.sqrt (∫ omega, K0 omega ^ 2 ∂gamma.dominating) / 2 *
            Real.sqrt (∫ omega, K n X omega ^ 2 ∂gamma.dominating) := by positivity
    rw [abs_of_nonneg henv_nonneg]
    calc
      _ ≤ (|∫ omega, W n X omega * r (estimator n X - theta0) omega
                ∂gamma.dominating| +
            |(estimator n X - theta0) / 2| *
              |∫ omega, K n X omega * K0 omega ∂gamma.dominating|) /
            |estimator n X - theta0| := by
        apply div_le_div_of_nonneg_right _ (abs_nonneg _)
        simpa only [abs_mul] using abs_add_le
          (∫ omega, W n X omega * r (estimator n X - theta0) omega
            ∂gamma.dominating)
          (((estimator n X - theta0) / 2) *
            ∫ omega, K n X omega * K0 omega ∂gamma.dominating)
      _ ≤ (Real.sqrt (∫ omega, W n X omega ^ 2 ∂gamma.dominating) *
              Real.sqrt (∫ omega, r (estimator n X - theta0) omega ^ 2
                ∂gamma.dominating) +
            (|estimator n X - theta0| / 2) *
              (Real.sqrt (∫ omega, K n X omega ^ 2 ∂gamma.dominating) *
                Real.sqrt (∫ omega, K0 omega ^ 2 ∂gamma.dominating))) /
            |estimator n X - theta0| := by
        apply div_le_div_of_nonneg_right _ (abs_nonneg _)
        apply add_le_add hcs1
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left hcs2 (by positivity)
      _ = _ := by field_simp [abs_ne_zero.mpr hdelta]

/-- The ordinary scalar model-shift expansion from root-`n` tightness.

The displayed sign is deliberately `P scoreHat - P_{thetaHat,eta} scoreHat`
plus the QMD cross moment.  Thus solving the estimating equation yields the
corrected `+ I^{-1} B_n` term.

The proof applies `qmdPath_modelShift_normalized_oP`; `hTight` controls
`sqrt n * |delta|`, while the shared bundle's consistency is the independent
localization input needed by the normalized theorem. -/
theorem qmdPath_modelShift_oP_of_sqrtN_tight
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : ∀ n, (Fin n → Omega) → ℝ} {theta0 : ℝ}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → ℝ}
    {score0 : Omega → ℝ}
    (h : HellingerScoreTransportHyp P gamma estimator theta0 scoreHat score0)
    -- the local parameter `sqrt n (thetaHat-theta0)` is `O_P(1)`.
    (hTight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * (estimator n X - theta0))) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        Real.sqrt n *
            ((∫ omega, scoreHat n X omega ∂P) -
              ∫ omega, scoreHat n X omega
                ∂(gamma.curve (estimator n X - theta0)))
          + Real.sqrt n * (estimator n X - theta0) *
              ∫ omega, score0 omega * (gamma.score : Omega → ℝ) omega ∂P) := by
  have hnorm := qmdPath_modelShift_normalized_oP h
  have hscale : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * |estimator n X - theta0|) := by
    simpa only [IsBoundedInProb, Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hTight
  have hprod := tendstoInProbZero_of_isBoundedInProb_mul hscale hnorm
  have hneg := tendstoInProbZero_const_smul (-1) hprod
  convert hneg using 1
  funext n X
  let delta := estimator n X - theta0
  by_cases hdelta : delta = 0
  · simp [delta, hdelta, gamma.curve_at_zero]
  · simp only [delta, hdelta, ↓reduceIte, smul_eq_mul]
    have habs : |estimator n X - theta0| ≠ 0 := by
      simpa [delta] using abs_ne_zero.mpr hdelta
    field_simp [habs]
    ring

/-! ## Finite-dimensional formulation -/

/-- A dominated QMD model with a native Euclidean parameter and score.

This is not a family of scalar paths: its QMD remainder is stated once for an
arbitrary vector displacement and uses the single linear form
`h |-> <h, score>`. -/
structure QMDModel (P : Measure Omega) [IsProbabilityMeasure P] (d : ℕ) where
  /-- Constitutive (vdV §7.2 and §25.3): the local parameter curve of laws. -/
  curve : EuclideanSpace ℝ (Fin d) → Measure Omega
  /-- Constitutive (vdV §7.2): the model passes through truth at zero. -/
  curve_at_zero : curve 0 = P
  /-- Constitutive (vdV §7.2): every member of the local model is a probability law. -/
  curve_isProbability : ∀ h, IsProbabilityMeasure (curve h)
  /-- Constitutive (dominated specialization of vdV §7.2): one common dominating measure. -/
  dominating : Measure Omega
  /-- Constitutive (dominated specialization): every local law is dominated. -/
  curve_absContinuous : ∀ h, curve h ≪ dominating
  /-- Mathlib's Radon--Nikodym API requires sigma-finiteness. -/
  dominating_sigmaFinite : SigmaFinite dominating
  /-- Constitutive (vdV §7.2): the native vector score. -/
  score : Omega → EuclideanSpace ℝ (Fin d)
  /-- measurable representative for the native score. -/
  score_measurable : Measurable score
  /-- Constitutive (vdV Lemma 7.6): the score is square-integrable. -/
  score_memLp : MemLp score 2 P
  /-- Constitutive (vdV Lemma 7.6): the score has mean zero. -/
  score_mean_zero : ∫ omega, score omega ∂P = 0
  /-- Constitutive (vdV §7.2, equation (7.2)): native square-root-density
  remainder, with one Euclidean linear form and no coordinatewise paths. -/
  qmd_limit : Tendsto
    (fun h : EuclideanSpace ℝ (Fin d) =>
      eLpNorm (fun omega : Omega =>
        Real.sqrt (((curve h).rnDeriv dominating omega).toReal)
          - Real.sqrt (((curve 0).rnDeriv dominating omega).toReal)
          - (1 / 2 : ℝ) * ⟪h, score omega⟫_ℝ *
              Real.sqrt (((curve 0).rnDeriv dominating omega).toReal))
        2 dominating / ENNReal.ofReal ‖h‖)
      (nhdsWithin 0 {0}ᶜ) (𝓝 (0 : ℝ≥0∞))

instance {P : Measure Omega} [IsProbabilityMeasure P] {d : ℕ}
    (M : QMDModel P d) : SigmaFinite M.dominating := M.dominating_sigmaFinite

set_option maxHeartbeats 1800000 in
-- The proof keeps the vector QMD remainder and tangent in one common L² space.
/-- Native QMD implies Hellinger continuity of the local vector model at
truth.  This is the first-order continuity used in the truncation proof of
vdV (25.76). -/
theorem qmdModel_hellinger_continuous
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d) :
    Tendsto (fun delta : EuclideanSpace ℝ (Fin d) =>
      Real.sqrt (∫ omega,
        (Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal) -
          Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) ^ 2
        ∂M.dominating)) (nhds 0) (nhds 0) := by
  let s : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal)
  let g : Omega → EuclideanSpace ℝ (Fin d) := M.score
  let r : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    s delta omega - s 0 omega - (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega
  have hs : ∀ delta, MemLp (s delta) 2 M.dominating := fun delta => by
    letI := M.curve_isProbability delta
    simpa [s] using
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
        (M.curve_absContinuous delta)
  have hPac : P ≪ M.dominating := by
    simpa only [← M.curve_at_zero] using M.curve_absContinuous 0
  have hgP : MemLp g 2 P := by simpa [g] using M.score_memLp
  have hr : ∀ delta, MemLp (r delta) 2 M.dominating := fun delta => by
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
      hPac (MemLp.const_inner (𝕜 := ℝ) delta hgP)
    have ht : MemLp (fun omega =>
        (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) 2 M.dominating := by
      simpa [s, g, M.curve_at_zero, smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm] using hm.const_mul (1 / 2 : ℝ)
    exact (hs delta).sub (hs 0) |>.sub (by simpa [r] using ht)
  let qraw : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) / ‖delta‖
  let q : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    if delta = 0 then 0 else qraw delta
  have hqraw : Tendsto qraw (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp
      M.qmd_limit
    simp only [Function.comp_def, ENNReal.toReal_zero] at ht
    refine ht.congr' (Eventually.of_forall fun delta => ?_)
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (norm_nonneg delta),
      ← AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
        (hr delta)]
  have hq : Tendsto q (nhds (0 : EuclideanSpace ℝ (Fin d))) (nhds 0) :=
    tendsto_zeroExtension qraw q hqraw (by simp [q]) (by intro x hx; simp [q, hx])
  let G2 : ℝ := ∫ omega, ‖g omega‖ ^ 2 ∂P
  have hG2nonneg : 0 ≤ G2 := integral_nonneg fun _ => sq_nonneg _
  have htangent : ∀ delta, MemLp (fun omega =>
      (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) 2 M.dominating := by
    intro delta
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
      hPac (MemLp.const_inner (𝕜 := ℝ) delta hgP)
    simpa [s, g, M.curve_at_zero, smul_eq_mul, mul_assoc, mul_comm,
      mul_left_comm] using hm.const_mul (1 / 2 : ℝ)
  have hinnerInt : ∀ delta,
      (∫ omega, (⟪delta, g omega⟫_ℝ * s 0 omega) ^ 2
        ∂M.dominating) = ∫ omega, ⟪delta, g omega⟫_ℝ ^ 2 ∂P := by
    intro delta
    have hi : Integrable (fun omega => ⟪delta, g omega⟫_ℝ ^ 2) P :=
      (MemLp.const_inner (𝕜 := ℝ) delta hgP).integrable_sq
    rw [← integral_rnDeriv_smul hPac]
    apply integral_congr_ae
    exact Eventually.of_forall fun omega => by
      simp only [s, M.curve_at_zero, smul_eq_mul]
      rw [mul_pow]
      rw [Real.sq_sqrt ENNReal.toReal_nonneg]
      ring
  have hinnerBound : ∀ delta,
      (∫ omega, ⟪delta, g omega⟫_ℝ ^ 2 ∂P) ≤ ‖delta‖ ^ 2 * G2 := by
    intro delta
    calc
      _ ≤ ∫ omega, ‖delta‖ ^ 2 * ‖g omega‖ ^ 2 ∂P := by
        apply integral_mono
        · exact (MemLp.const_inner (𝕜 := ℝ) delta hgP).integrable_sq
        · exact (hgP.integrable_norm_pow (by norm_num)).const_mul _
        · intro omega
          have hi := abs_real_inner_le_norm delta (g omega)
          have hisq : ⟪delta, g omega⟫_ℝ ^ 2 ≤
              (‖delta‖ * ‖g omega‖) ^ 2 := by
            rw [← sq_abs]
            exact (sq_le_sq₀ (abs_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hi
          nlinarith
      _ = _ := by rw [integral_const_mul]
  have htangentBound : ∀ delta,
      Real.sqrt (∫ omega,
          ((1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) ^ 2
          ∂M.dominating) ≤
        (‖delta‖ / 2) * Real.sqrt G2 := by
    intro delta
    have hint : (∫ omega,
        ((1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) ^ 2
          ∂M.dominating) ≤ (1 / 2 : ℝ) ^ 2 * (‖delta‖ ^ 2 * G2) := by
      calc
        _ = (1 / 2 : ℝ) ^ 2 *
            ∫ omega, (⟪delta, g omega⟫_ℝ * s 0 omega) ^ 2
              ∂M.dominating := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Eventually.of_forall fun omega => by ring
        _ = (1 / 2 : ℝ) ^ 2 *
            ∫ omega, ⟪delta, g omega⟫_ℝ ^ 2 ∂P := by
          rw [hinnerInt]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hinnerBound delta) (sq_nonneg _)
    have hsqrt := Real.sqrt_le_sqrt hint
    rw [Real.sqrt_mul (sq_nonneg (1 / 2 : ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Real.sqrt_mul (sq_nonneg ‖delta‖), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg delta)] at hsqrt
    convert hsqrt using 1; ring
  let H : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    Real.sqrt (∫ omega, (s delta omega - s 0 omega) ^ 2 ∂M.dominating)
  have hHbound : ∀ delta, H delta ≤
      q delta * ‖delta‖ + (‖delta‖ / 2) * Real.sqrt G2 := by
    intro delta
    by_cases hdelta : delta = 0
    · subst delta
      simp [H, q]
    · have hfun : (fun omega => s delta omega - s 0 omega) =
          fun omega => r delta omega +
            (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega := by
        funext omega
        simp only [r]
        ring
      simp only [H]
      have hsquare : (fun omega => (s delta omega - s 0 omega) ^ 2) =
          fun omega => (r delta omega +
            (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) ^ 2 := by
        funext omega
        rw [congrFun hfun omega]
      rw [hsquare]
      calc
        _ ≤ Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) +
            Real.sqrt (∫ omega,
              ((1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) ^ 2
                ∂M.dominating) :=
          sqrt_integral_sq_add_le (hr delta) (htangent delta)
        _ ≤ Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) +
            (‖delta‖ / 2) * Real.sqrt G2 :=
          add_le_add (le_refl _) (htangentBound delta)
        _ = q delta * ‖delta‖ + (‖delta‖ / 2) * Real.sqrt G2 := by
          simp only [q, hdelta, ↓reduceIte, qraw]
          field_simp [norm_ne_zero_iff.mpr hdelta]
  have hupper : Tendsto (fun delta =>
      q delta * ‖delta‖ + (‖delta‖ / 2) * Real.sqrt G2)
      (nhds (0 : EuclideanSpace ℝ (Fin d))) (nhds 0) := by
    have hnorm : Tendsto (fun delta : EuclideanSpace ℝ (Fin d) => ‖delta‖)
        (nhds 0) (nhds 0) := by
      simpa using (continuous_norm (E := EuclideanSpace ℝ (Fin d))).tendsto 0
    have hfirst := hq.mul hnorm
    have hsecond := (hnorm.div_const 2).mul_const (Real.sqrt G2)
    simpa using hfirst.add hsecond
  have hH : Tendsto H (nhds (0 : EuclideanSpace ℝ (Fin d))) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
      (Eventually.of_forall hHbound)
  simpa only [H, s] using hH

/-- Native raw moving bias `sqrt n * P_{thetaHat,eta} scoreHat`.

At dimension zero this is the unique vector in the zero-dimensional Euclidean
space; at `n = 0` it is also killed by the scalar factor `Real.sqrt 0`. -/
noncomputable def rawMovingBias_vec {d : ℕ} {P : Measure Omega}
    [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d))
    (theta0 : EuclideanSpace ℝ (Fin d))
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Omega) : EuclideanSpace ℝ (Fin d) :=
  Real.sqrt n • ∫ omega, scoreHat n X omega
    ∂(M.curve (estimator n X - theta0))

/-- Native cross moment between a vector estimating score and the QMD score.

Entry `(j,k)` is `P[score0_j * qmdScore_k]`; its action is always taken through
the single map `Matrix.toEuclideanCLM`, including when `d = 1`. -/
noncomputable def qmdCrossMoment {d : ℕ} (P : Measure Omega)
    [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (score0 : Omega → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => ∫ omega, score0 omega j * M.score omega k ∂P

/-- The cross-moment matrix acts as the integral of the score rank-one action. -/
private lemma qmdCrossMoment_apply {d : ℕ} {P : Measure Omega}
    [IsProbabilityMeasure P] (M : QMDModel (Omega := Omega) P d)
    (score0 : Omega → EuclideanSpace ℝ (Fin d))
    (hscore0 : MemLp score0 2 P)
    (delta : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (qmdCrossMoment P M score0) delta =
      ∫ omega, ⟪delta, M.score omega⟫_ℝ • score0 omega ∂P := by
  have hinner : MemLp (fun omega => ⟪delta, M.score omega⟫_ℝ) 2 P :=
    M.score_memLp.const_inner delta
  have hint : Integrable (fun omega => ⟪delta, M.score omega⟫_ℝ • score0 omega) P :=
    ((hscore0.smul hinner : MemLp _ 1 P).integrable (by norm_num))
  ext j
  change ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
      (qmdCrossMoment P M score0)) delta).ofLp j =
    (EuclideanSpace.proj j) (∫ omega, ⟪delta, M.score omega⟫_ℝ • score0 omega ∂P)
  rw [← (EuclideanSpace.proj j).integral_comp_comm hint]
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    qmdCrossMoment, PiLp.inner_apply, EuclideanSpace.coe_proj,
    PiLp.smul_apply, smul_eq_mul]
  have heq :
      (fun x => (∑ i, ⟪delta.ofLp i, (M.score x).ofLp i⟫_ℝ) *
        (score0 x).ofLp j) =
        fun x => ∑ i, delta.ofLp i *
          ((score0 x).ofLp j * (M.score x).ofLp i) := by
    funext x
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
    simp only [conj_trivial]
    change (M.score x).ofLp i * delta.ofLp i * (score0 x).ofLp j =
      delta.ofLp i * ((score0 x).ofLp j * (M.score x).ofLp i)
    ring
  rw [heq]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i hi
    have h0j := hscore0.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
    have hgi := M.score_memLp.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
    exact (h0j.integrable_mul hgi).const_mul _

set_option maxHeartbeats 1200000 in
-- This deterministic estimate is separated from the probabilistic localization
-- so that Lean elaborates the two analytic layers independently.
private lemma native_modelShift_normalized_bound
    {d : ℕ} {μ : Measure Omega}
    {delta : EuclideanSpace ℝ (Fin d)} (hdelta : delta ≠ 0)
    {r f G : Omega → ℝ}
    {W K : Omega → EuclideanSpace ℝ (Fin d)}
    (hr : MemLp r 2 μ) (hf : MemLp f 2 μ) (hG : MemLp G 2 μ)
    (hW : MemLp W 2 μ) (hK : MemLp K 2 μ)
    (hpoint : ∀ omega, f omega ^ 2 ≤ ‖delta‖ ^ 2 * G omega ^ 2) :
    ‖delta‖⁻¹ * ‖(∫ omega, r omega • W omega ∂μ) +
          (1 / 2 : ℝ) • ∫ omega, f omega • K omega ∂μ‖ ≤
      Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) *
          (Real.sqrt (∫ omega, r omega ^ 2 ∂μ) / ‖delta‖) +
        Real.sqrt (∫ omega, G omega ^ 2 ∂μ) / 2 *
          Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ) := by
  have hcs1 := norm_integral_smul_le_sqrt_integral_sq hr hW
  have hcs2 := norm_integral_smul_le_sqrt_integral_sq hf hK
  have hint :
      ∫ omega, f omega ^ 2 ∂μ ≤
        ‖delta‖ ^ 2 * ∫ omega, G omega ^ 2 ∂μ := by
    calc
      _ ≤ ∫ omega, ‖delta‖ ^ 2 * G omega ^ 2 ∂μ :=
        integral_mono hf.integrable_sq
          (hG.integrable_sq.const_mul (‖delta‖ ^ 2)) hpoint
      _ = _ := by rw [integral_const_mul]
  have hsqrt :
      Real.sqrt (∫ omega, f omega ^ 2 ∂μ) ≤
        ‖delta‖ * Real.sqrt (∫ omega, G omega ^ 2 ∂μ) := by
    have hs := Real.sqrt_le_sqrt hint
    rw [Real.sqrt_mul (sq_nonneg ‖delta‖), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg delta)] at hs
    exact hs
  have hnorm_ne : ‖delta‖ ≠ 0 := norm_ne_zero_iff.mpr hdelta
  have hfactor :
      ‖delta‖⁻¹ * Real.sqrt (∫ omega, f omega ^ 2 ∂μ) ≤
        Real.sqrt (∫ omega, G omega ^ 2 ∂μ) := by
    calc
      _ ≤ ‖delta‖⁻¹ *
          (‖delta‖ * Real.sqrt (∫ omega, G omega ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hsqrt (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by field_simp [hnorm_ne]
  have htri :
      ‖(∫ omega, r omega • W omega ∂μ) +
            (1 / 2 : ℝ) • ∫ omega, f omega • K omega ∂μ‖ ≤
        ‖∫ omega, r omega • W omega ∂μ‖ +
          (1 / 2 : ℝ) * ‖∫ omega, f omega • K omega ∂μ‖ := by
    calc
      _ ≤ ‖∫ omega, r omega • W omega ∂μ‖ +
          ‖(1 / 2 : ℝ) • ∫ omega, f omega • K omega ∂μ‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      ‖∫ omega, r omega • W omega ∂μ‖ +
            (1 / 2 : ℝ) * ‖∫ omega, f omega • K omega ∂μ‖ ≤
        Real.sqrt (∫ omega, r omega ^ 2 ∂μ) *
              Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) +
          (1 / 2 : ℝ) * (Real.sqrt (∫ omega, f omega ^ 2 ∂μ) *
            Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ)) :=
    add_le_add hcs1 (mul_le_mul_of_nonneg_left hcs2 (by norm_num))
  calc
    _ ≤ ‖delta‖⁻¹ *
        (‖∫ omega, r omega • W omega ∂μ‖ +
          (1 / 2 : ℝ) * ‖∫ omega, f omega • K omega ∂μ‖) :=
      mul_le_mul_of_nonneg_left htri (inv_nonneg.mpr (norm_nonneg delta))
    _ ≤ ‖delta‖⁻¹ *
        (Real.sqrt (∫ omega, r omega ^ 2 ∂μ) *
            Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) +
          (1 / 2 : ℝ) * (Real.sqrt (∫ omega, f omega ^ 2 ∂μ) *
            Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ))) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (norm_nonneg delta))
    _ = Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) *
          (Real.sqrt (∫ omega, r omega ^ 2 ∂μ) / ‖delta‖) +
        (1 / 2 : ℝ) * Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ) *
          (‖delta‖⁻¹ * Real.sqrt (∫ omega, f omega ^ 2 ∂μ)) := by
      field_simp [hnorm_ne]
    _ ≤ Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) *
          (Real.sqrt (∫ omega, r omega ^ 2 ∂μ) / ‖delta‖) +
        (1 / 2 : ℝ) * Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ) *
          Real.sqrt (∫ omega, G omega ^ 2 ∂μ) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (Real.sqrt_nonneg _)))
    _ = _ := by ring

/-- Honest native analogue of `HellingerScoreTransportHyp`, with the same
membership/tightness/transport split and no integral-shift conclusion. -/
structure HellingerScoreTransportHypVec
    {d : ℕ} (P : Measure Omega) [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d))
    (theta0 : EuclideanSpace ℝ (Fin d))
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d))
    (score0 : Omega → EuclideanSpace ℝ (Fin d)) : Prop where
  /-- integrability under the true law. -/
  scoreHat_integrable_truth : ∀ n X, Integrable (scoreHat n X) P
  /-- integrability under the moving law. -/
  scoreHat_integrable_moving : ∀ n X,
    Integrable (scoreHat n X) (M.curve (estimator n X - theta0))
  /-- the limiting vector score belongs to L2 of truth. -/
  score0_memLp : MemLp score0 2 P
  /-- the native Hellinger-weighted random score genuinely belongs
  to `L2(M.dominating)`, excluding the non-integrable Bochner fallback. -/
  weightedScore_memLp : ∀ n X, MemLp (fun omega =>
    (Real.sqrt (((M.curve (estimator n X - theta0)).rnDeriv
        M.dominating omega).toReal)
      + Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
        scoreHat n X omega) 2 M.dominating
  /-- the native weighted-score L2 norms are `O_P(1)`, to pair
  with the single native QMD remainder. -/
  weightedScore_tight : IsBoundedInProb
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega,
      ‖(Real.sqrt (((M.curve (estimator n X - theta0)).rnDeriv
            M.dominating omega).toReal)
          + Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
          scoreHat n X omega‖ ^ 2
      ∂M.dominating))
  /-- native Hellinger-weighted L2 score transport through the
  single vector square-root-density tangent expression. -/
  weightedScore_transport : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X =>
      Real.sqrt (∫ omega,
        ‖(Real.sqrt (((M.curve (estimator n X - theta0)).rnDeriv
              M.dominating omega).toReal)
              + Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
              scoreHat n X omega
          - (2 * Real.sqrt (((M.curve 0).rnDeriv
              M.dominating omega).toReal)) • score0 omega‖ ^ 2
        ∂M.dominating))
  /-- consistency in the native Euclidean parameter. -/
  consistency : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => estimator n X - theta0)

/-- First-order score hypotheses matching vdV (25.76a,b).  Unlike
`HellingerScoreTransportHypVec`, this bundle does not assume a weighted-score
transport conclusion.  The per-sample `MemLp` fields select honest Bochner
representatives for the two displayed square expectations. -/
structure FirstOrder2576ScoreTransportHypVec
    {d : ℕ} (P : Measure Omega) [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d))
    (theta0 : EuclideanSpace ℝ (Fin d))
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d))
    (score0 : Omega → EuclideanSpace ℝ (Fin d)) : Prop where
  /-- jointly measurable representative of the fitted score. -/
  scoreHat_measurable : ∀ n,
    Measurable (fun p : (Fin n → Omega) × Omega => scoreHat n p.1 p.2)
  /-- The fitted score has a genuine `L²(P₀)` representative. -/
  scoreHat_memLp_truth : ∀ n X, MemLp (scoreHat n X) 2 P
  /-- The fitted score has a genuine `L²(P_{θhat,η0})` representative. -/
  scoreHat_memLp_moving : ∀ n X,
    MemLp (scoreHat n X) 2 (M.curve (estimator n X - theta0))
  /-- The limiting score is square-integrable under truth. -/
  score0_memLp : MemLp score0 2 P
  /-- Equation (25.76a): `P₀‖scoreHat-score0‖² = o_P(1)`. -/
  score_l2_truth : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega, ‖scoreHat n X omega - score0 omega‖ ^ 2 ∂P))
  /-- measurability of the random `L²(P₀)` distance. -/
  score_l2_truth_measurable : ∀ n, Measurable (fun X =>
    Real.sqrt (∫ omega, ‖scoreHat n X omega - score0 omega‖ ^ 2 ∂P))
  /-- Equation (25.76b): the moving-law score-square expectation is `O_P(1)`. -/
  score_energy_moving_tight : IsBoundedInProb
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega, ‖scoreHat n X omega‖ ^ 2
      ∂(M.curve (estimator n X - theta0))))
  /-- Consistency of the Euclidean parameter estimator. -/
  consistency : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => estimator n X - theta0)

/-- Equation (25.76a) and the fixed limiting score imply `O_P(1)` truth-law
score energy. -/
private lemma firstOrder2576_scoreEnergy_truth_tight
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : FirstOrder2576ScoreTransportHypVec P M estimator theta0 scoreHat score0) :
    IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂P)) := by
  let c0 : ℝ := Real.sqrt (∫ omega, ‖score0 omega‖ ^ 2 ∂P)
  have hdiffOP := h.score_l2_truth.isBoundedInProb h.score_l2_truth_measurable
  have hc0OP : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun _ _ => c0) := isBoundedInProb_const c0
  have hsum := isBoundedInProb_add hdiffOP hc0OP
  refine isBoundedInProb_mono (fun n X => ?_) hsum
  have hdiff : MemLp (fun omega => scoreHat n X omega - score0 omega) 2 P :=
    (h.scoreHat_memLp_truth n X).sub h.score0_memLp
  have hle := sqrt_integral_norm_sq_add_le hdiff h.score0_memLp
  have hc0nonneg : 0 ≤ c0 := Real.sqrt_nonneg _
  have hdiffnonneg : 0 ≤ Real.sqrt
      (∫ omega, ‖scoreHat n X omega - score0 omega‖ ^ 2 ∂P) := Real.sqrt_nonneg _
  simpa only [sub_add_cancel, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (add_nonneg hdiffnonneg hc0nonneg), c0] using hle

/-- Equations (25.76a,b) bound the square-root-density score envelope used in
the truncation argument on pp. 392--393. -/
private lemma firstOrder2576_scoreEnvelope_tight
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : FirstOrder2576ScoreTransportHypVec P M estimator theta0 scoreHat score0) :
    IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (2 *
        ((∫ omega, ‖scoreHat n X omega‖ ^ 2
            ∂(M.curve (estimator n X - theta0))) +
          ∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂P))) := by
  have hsum := isBoundedInProb_add h.score_energy_moving_tight
    (firstOrder2576_scoreEnergy_truth_tight h)
  have hscaled := isBoundedInProb_const_smul (Real.sqrt 2) hsum
  refine isBoundedInProb_mono (fun n X => ?_) hscaled
  let A : ℝ := ∫ omega, ‖scoreHat n X omega‖ ^ 2
    ∂(M.curve (estimator n X - theta0))
  let B : ℝ := ∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂P
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hroot : Real.sqrt (2 * (A + B)) ≤
      Real.sqrt 2 * (Real.sqrt A + Real.sqrt B) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)))).1
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (add_nonneg hA hB)), mul_pow,
      hs2]
    nlinarith [hsA, hsB, mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]
  have hright : 0 ≤ Real.sqrt 2 * (Real.sqrt A + Real.sqrt B) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))
  change ‖Real.sqrt (2 * (A + B))‖ ≤
    ‖Real.sqrt 2 • (Real.sqrt A + Real.sqrt B)‖
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    show Real.sqrt 2 • (Real.sqrt A + Real.sqrt B) =
      Real.sqrt 2 * (Real.sqrt A + Real.sqrt B) by rfl,
    Real.norm_eq_abs, abs_of_nonneg hright]
  exact hroot

set_option maxHeartbeats 2500000 in
-- This is the probabilistic truncation argument on pp. 392--393.
/-- Equations (25.76a,b), consistency, and first-order QMD imply the native
score cross-transport needed in the moving-law expansion. -/
theorem qmdModel_scoreCrossTransport_oP_of_2576
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : FirstOrder2576ScoreTransportHypVec P M estimator theta0 scoreHat score0) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let delta := estimator n X - theta0
        let u := if delta = 0 then 0 else ‖delta‖⁻¹ • delta
        ∫ omega,
          (⟪u, M.score omega⟫_ℝ *
              Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
            ((Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal) +
                Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
                scoreHat n X omega -
              (2 : ℝ) •
                (Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal) •
                  score0 omega)) ∂M.dominating) := by
  let s : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal)
  let g : Omega → EuclideanSpace ℝ (Fin d) := M.score
  let delta : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d) :=
    fun n X => estimator n X - theta0
  let u : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d) := fun n X =>
    if delta n X = 0 then 0 else ‖delta n X‖⁻¹ • delta n X
  let K : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d) :=
    fun n X omega =>
      (s (delta n X) omega + s 0 omega) • scoreHat n X omega -
        (2 : ℝ) • (s 0 omega • score0 omega)
  let Z : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d) := fun n X =>
    ∫ omega, (⟪u n X, g omega⟫_ℝ * s 0 omega) • K n X omega ∂M.dominating
  let H : ∀ n, (Fin n → Omega) → ℝ := fun n X =>
    Real.sqrt (∫ omega, (s (delta n X) omega - s 0 omega) ^ 2 ∂M.dominating)
  let Et : ∀ n, (Fin n → Omega) → ℝ := fun n X =>
    Real.sqrt (∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂P)
  let B : ∀ n, (Fin n → Omega) → ℝ := fun n X =>
    Real.sqrt (2 * ((∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂(M.curve (delta n X))) +
      ∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂P))
  let D : ∀ n, (Fin n → Omega) → ℝ := fun n X =>
    Real.sqrt (∫ omega, ‖scoreHat n X omega - score0 omega‖ ^ 2 ∂P)
  let c : ℕ → ℝ := fun m => Real.sqrt (∫ omega,
    ‖{x | (m : ℝ) < ‖g x‖}.indicator g omega‖ ^ 2 ∂P)
  let Am : ℕ → ∀ n, (Fin n → Omega) → ℝ := fun m n X => (m : ℝ) * H n X * Et n X
  let G : ℝ := Real.sqrt (∫ omega, ‖g omega‖ ^ 2 ∂P)
  let C : ∀ n, (Fin n → Omega) → ℝ := fun n X => 2 * G * D n X
  have hPac : P ≪ M.dominating := by
    simpa only [← M.curve_at_zero] using M.curve_absContinuous 0
  have hs : ∀ dlt, MemLp (s dlt) 2 M.dominating := fun dlt => by
    letI := M.curve_isProbability dlt
    simpa [s] using
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
        (M.curve_absContinuous dlt)
  have hgP : MemLp g 2 P := by simpa [g] using M.score_memLp
  have hH : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P)) H := by
    simpa only [H, delta, s] using
      tendstoInProbZero_comp_zero h.consistency (qmdModel_hellinger_continuous M)
  have hEt : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P)) Et := by
    simpa only [Et] using firstOrder2576_scoreEnergy_truth_tight h
  have hB : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P)) B := by
    simpa only [B, delta] using firstOrder2576_scoreEnvelope_tight h
  have hc : Tendsto c atTop (nhds 0) := by
    simpa only [c, g] using score_tail_energy_tendsto M.score_measurable M.score_memLp
  have hC : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P)) C := by
    have hscaled := tendstoInProbZero_const_smul (2 * G) h.score_l2_truth
    simpa only [C, D, smul_eq_mul, mul_assoc] using hscaled
  have hA : ∀ m, TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P)) (Am m) := by
    intro m
    have hprod := tendstoInProbZero_of_isBoundedInProb_mul hEt hH
    have hscaled := tendstoInProbZero_const_smul (m : ℝ) hprod
    simpa only [Am, H, Et, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hbound : ∀ m n X, ‖Z n X‖ ≤
      ‖Am m n X‖ + |c m| * ‖B n X‖ + ‖C n X‖ := by
    intro m n X
    let S : Set Omega := {omega | (m : ℝ) < ‖g omega‖}
    let gTail : Omega → EuclideanSpace ℝ (Fin d) := S.indicator g
    let gSmall : Omega → EuclideanSpace ℝ (Fin d) := g - gTail
    have hS : MeasurableSet S := by
      exact measurableSet_lt measurable_const (M.score_measurable.norm)
    have hgTailP : MemLp gTail 2 P := by
      simpa only [gTail, g] using M.score_memLp.indicator hS
    have hgTailMeas : Measurable gTail := by
      exact M.score_measurable.indicator hS
    have hgSmallMeas : Measurable gSmall := by
      exact M.score_measurable.sub hgTailMeas
    have hgSplit : ∀ omega, g omega = gSmall omega + gTail omega := by
      intro omega
      simp only [gSmall, Pi.sub_apply]
      abel
    have hgSmall : ∀ omega, ‖gSmall omega‖ ≤ (m : ℝ) := by
      intro omega
      by_cases homega : omega ∈ S
      · simp [gSmall, gTail, Set.indicator_of_mem homega]
      · have hle : ‖g omega‖ ≤ (m : ℝ) := by
          simpa only [S, Set.mem_setOf_eq, not_lt] using homega
        simpa [gSmall, gTail, Set.indicator_of_notMem homega] using hle
    have hu : ‖u n X‖ ≤ 1 := by
      by_cases hdelta : delta n X = 0
      · simp [u, hdelta]
      · simp only [u, hdelta, ↓reduceIte, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hdelta)]
    have hst : MemLp (s (delta n X) - s 0) 2 M.dominating :=
      (hs (delta n X)).sub (hs 0)
    have htz : MemLp (fun omega => s 0 omega • scoreHat n X omega) 2 M.dominating := by
      simpa [s, M.curve_at_zero] using
        memLp_sqrt_rnDeriv_smul_of_memLp hPac (h.scoreHat_memLp_truth n X)
    have hsz : MemLp (fun omega => s (delta n X) omega • scoreHat n X omega)
        2 M.dominating := by
      letI := M.curve_isProbability (delta n X)
      simpa [s] using memLp_sqrt_rnDeriv_smul_of_memLp
        (M.curve_absContinuous (delta n X)) (h.scoreHat_memLp_moving n X)
    have htg : MemLp (fun omega => s 0 omega • g omega) 2 M.dominating := by
      simpa [s, g, M.curve_at_zero] using
        memLp_sqrt_rnDeriv_smul_of_memLp hPac M.score_memLp
    have htgTail : MemLp (fun omega => s 0 omega • gTail omega) 2 M.dominating := by
      simpa [s, M.curve_at_zero] using
        memLp_sqrt_rnDeriv_smul_of_memLp hPac hgTailP
    have htdiff : MemLp (fun omega =>
        s 0 omega • (scoreHat n X omega - score0 omega)) 2 M.dominating := by
      simpa [s, M.curve_at_zero] using memLp_sqrt_rnDeriv_smul_of_memLp hPac
        ((h.scoreHat_memLp_truth n X).sub h.score0_memLp)
    let coefSmall : Omega → ℝ := fun omega => ⟪u n X, gSmall omega⟫_ℝ
    have hcoefSmallMeas : Measurable coefSmall := by
      exact ((continuous_const (y := u n X)).inner continuous_id).measurable.comp hgSmallMeas
    have hcoefSmallTop : MemLp coefSmall ∞ M.dominating := by
      apply memLp_top_of_bound hcoefSmallMeas.aestronglyMeasurable (m : ℝ)
      exact Eventually.of_forall fun omega => by
        change |⟪u n X, gSmall omega⟫_ℝ| ≤ (m : ℝ)
        calc
          _ ≤ ‖u n X‖ * ‖gSmall omega‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * (m : ℝ) := mul_le_mul hu (hgSmall omega)
            (norm_nonneg _) (by positivity)
          _ = _ := one_mul _
    have hsmallZ : MemLp (fun omega =>
        ⟪u n X, gSmall omega⟫_ℝ • (s 0 omega • scoreHat n X omega))
        2 M.dominating := by
      simpa only [coefSmall] using! htz.smul hcoefSmallTop
    have htailCoef : MemLp (fun omega =>
        ⟪u n X, gTail omega⟫_ℝ * s 0 omega) 2 M.dominating := by
      have hi := MemLp.const_inner (𝕜 := ℝ) (u n X) htgTail
      simpa only [real_inner_smul_right, smul_eq_mul, mul_comm] using hi
    have htailZ : MemLp (fun omega =>
        (s (delta n X) omega - s 0 omega) • scoreHat n X omega)
        2 M.dominating := by
      simpa only [sub_smul] using! hsz.sub htz
    have hfullCoef : MemLp (fun omega =>
        ⟪u n X, g omega⟫_ℝ * s 0 omega) 2 M.dominating := by
      have hi := MemLp.const_inner (𝕜 := ℝ) (u n X) htg
      simpa only [real_inner_smul_right, smul_eq_mul, mul_comm] using hi
    have htEnergy : (∫ omega, ‖s 0 omega • scoreHat n X omega‖ ^ 2
        ∂M.dominating) = ∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂P := by
      simpa [s, M.curve_at_zero] using
        integral_norm_sqrt_rnDeriv_smul_sq hPac (h.scoreHat_memLp_truth n X)
    have hsEnergy : (∫ omega,
        ‖s (delta n X) omega • scoreHat n X omega‖ ^ 2 ∂M.dominating) =
        ∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂(M.curve (delta n X)) := by
      letI := M.curve_isProbability (delta n X)
      simpa [s] using integral_norm_sqrt_rnDeriv_smul_sq
        (M.curve_absContinuous (delta n X)) (h.scoreHat_memLp_moving n X)
    have htailEnergy : (∫ omega, ‖s 0 omega • gTail omega‖ ^ 2
        ∂M.dominating) = ∫ omega, ‖gTail omega‖ ^ 2 ∂P := by
      simpa [s, M.curve_at_zero] using
        integral_norm_sqrt_rnDeriv_smul_sq hPac hgTailP
    have hgEnergy : (∫ omega, ‖s 0 omega • g omega‖ ^ 2 ∂M.dominating) =
        ∫ omega, ‖g omega‖ ^ 2 ∂P := by
      simpa [s, M.curve_at_zero] using
        integral_norm_sqrt_rnDeriv_smul_sq hPac hgP
    have hdiffEnergy : (∫ omega,
        ‖s 0 omega • (scoreHat n X omega - score0 omega)‖ ^ 2 ∂M.dominating) =
        ∫ omega, ‖scoreHat n X omega - score0 omega‖ ^ 2 ∂P := by
      simpa [s, M.curve_at_zero] using integral_norm_sqrt_rnDeriv_smul_sq hPac
        ((h.scoreHat_memLp_truth n X).sub h.score0_memLp)
    have hdet := native_modelShift_truncation_bound (mu := M.dominating)
      (u := u n X) (m := (m : ℝ)) (s := s (delta n X)) (t := s 0)
      (g := g) (gSmall := gSmall) (gTail := gTail)
      (z := scoreHat n X) (z0 := score0) hu (by positivity) hgSplit hgSmall hst htz
      hsz htg htgTail htdiff hsmallZ htailCoef htailZ hfullCoef
    have hc_nonneg : 0 ≤ c m := Real.sqrt_nonneg _
    have hA_nonneg : 0 ≤ Am m n X := by
      simp only [Am]
      positivity
    have hB_nonneg : 0 ≤ B n X := by simp [B]
    have hC_nonneg : 0 ≤ C n X := by
      simp only [C, G, D]
      positivity
    have htail_as_c : Real.sqrt (∫ omega, ‖s 0 omega • gTail omega‖ ^ 2
        ∂M.dominating) = c m := by
      rw [htailEnergy]
    simpa only [Z, K, H, Et, B, C, D, G, c, delta, u, g, s,
      htEnergy, hsEnergy, htail_as_c, hgEnergy, hdiffEnergy,
      Real.norm_eq_abs, abs_of_nonneg hA_nonneg, abs_of_nonneg hc_nonneg,
      abs_of_nonneg hB_nonneg, abs_of_nonneg hC_nonneg] using hdet
  have hZ := tendstoInProbZero_of_fixed_truncation hA hB hc hC hbound
  simpa only [Z, K, u, delta, s, g] using hZ

/-- Equations (25.76a,b) also bound the Hellinger-weighted fitted score. -/
private lemma firstOrder2576_weightedScore_tight
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : FirstOrder2576ScoreTransportHypVec P M estimator theta0 scoreHat score0) :
    IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega,
        ‖(Real.sqrt (((M.curve (estimator n X - theta0)).rnDeriv
              M.dominating omega).toReal) +
            Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
            scoreHat n X omega‖ ^ 2 ∂M.dominating)) := by
  have hsum := isBoundedInProb_add h.score_energy_moving_tight
    (firstOrder2576_scoreEnergy_truth_tight h)
  refine isBoundedInProb_mono (fun n X => ?_) hsum
  let s : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal)
  have hPac : P ≪ M.dominating := by
    simpa only [← M.curve_at_zero] using M.curve_absContinuous 0
  have ht : MemLp (fun omega => s 0 omega • scoreHat n X omega) 2 M.dominating := by
    simpa [s, M.curve_at_zero] using
      memLp_sqrt_rnDeriv_smul_of_memLp hPac (h.scoreHat_memLp_truth n X)
  have hs : MemLp (fun omega =>
      s (estimator n X - theta0) omega • scoreHat n X omega) 2 M.dominating := by
    letI := M.curve_isProbability (estimator n X - theta0)
    simpa [s] using memLp_sqrt_rnDeriv_smul_of_memLp
      (M.curve_absContinuous (estimator n X - theta0))
      (h.scoreHat_memLp_moving n X)
  have hle := sqrt_integral_norm_sq_add_le hs ht
  have hsEnergy : (∫ omega,
      ‖s (estimator n X - theta0) omega • scoreHat n X omega‖ ^ 2
        ∂M.dominating) =
      ∫ omega, ‖scoreHat n X omega‖ ^ 2
        ∂(M.curve (estimator n X - theta0)) := by
    letI := M.curve_isProbability (estimator n X - theta0)
    simpa [s] using integral_norm_sqrt_rnDeriv_smul_sq
      (M.curve_absContinuous (estimator n X - theta0))
      (h.scoreHat_memLp_moving n X)
  have htEnergy : (∫ omega, ‖s 0 omega • scoreHat n X omega‖ ^ 2
      ∂M.dominating) = ∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂P := by
    simpa [s, M.curve_at_zero] using
      integral_norm_sqrt_rnDeriv_smul_sq hPac (h.scoreHat_memLp_truth n X)
  have hright : 0 ≤
      Real.sqrt (∫ omega, ‖scoreHat n X omega‖ ^ 2
        ∂(M.curve (estimator n X - theta0))) +
      Real.sqrt (∫ omega, ‖scoreHat n X omega‖ ^ 2 ∂P) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  simpa only [s, add_smul, hsEnergy, htEnergy, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hright] using hle

set_option maxHeartbeats 4000000 in
-- The RN/Bochner identity and unit-direction cross transport are elaboration-heavy.
/-- Native first-order model-shift expansion derived directly from equations
(25.76a,b), rather than a supplied Hellinger-score transport conclusion. -/
theorem qmdModel_modelShift_normalized_oP_of_2576
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : FirstOrder2576ScoreTransportHypVec P M estimator theta0 scoreHat score0) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let delta := estimator n X - theta0
        if delta = 0 then 0 else
          ‖delta‖⁻¹ •
            (((∫ omega, scoreHat n X omega ∂(M.curve delta)) -
                ∫ omega, scoreHat n X omega ∂P) -
              Matrix.toEuclideanCLM (𝕜 := ℝ)
                (qmdCrossMoment P M score0) delta)) := by
  let s : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal)
  let g : Omega → EuclideanSpace ℝ (Fin d) := M.score
  let r : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    s delta omega - s 0 omega - (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega
  let W : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d) :=
    fun n X omega => (s (estimator n X - theta0) omega + s 0 omega) •
      scoreHat n X omega
  let K : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d) :=
    fun n X omega => W n X omega - (2 : ℝ) • (s 0 omega • score0 omega)
  let u : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d) := fun n X =>
    let delta := estimator n X - theta0
    if delta = 0 then 0 else ‖delta‖⁻¹ • delta
  let Cross : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d) := fun n X =>
    ∫ omega, (⟪u n X, g omega⟫_ℝ * s 0 omega) • K n X omega ∂M.dominating
  have hs : ∀ delta, MemLp (s delta) 2 M.dominating := fun delta => by
    letI := M.curve_isProbability delta
    simpa [s] using
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
        (M.curve_absContinuous delta)
  have hPac : P ≪ M.dominating := by
    simpa only [← M.curve_at_zero] using M.curve_absContinuous 0
  have hgP : MemLp g 2 P := by simpa [g] using M.score_memLp
  have hscore0s0 : MemLp (fun omega => s 0 omega • score0 omega) 2 M.dominating := by
    simpa [s, M.curve_at_zero] using
      memLp_sqrt_rnDeriv_smul_of_memLp hPac h.score0_memLp
  have hr : ∀ delta, MemLp (r delta) 2 M.dominating := fun delta => by
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp hPac
      (MemLp.const_inner (𝕜 := ℝ) delta hgP)
    have ht : MemLp (fun omega =>
        (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) 2 M.dominating := by
      simpa [s, g, M.curve_at_zero, smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm] using hm.const_mul (1 / 2 : ℝ)
    exact (hs delta).sub (hs 0) |>.sub (by simpa [r] using ht)
  let qraw : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) / ‖delta‖
  let q : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    if delta = 0 then 0 else qraw delta
  have hqraw : Tendsto qraw (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp
      M.qmd_limit
    simp only [Function.comp_def, ENNReal.toReal_zero] at ht
    refine ht.congr' (Eventually.of_forall fun delta => ?_)
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (norm_nonneg delta),
      ← AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
        (hr delta)]
  have hq : Tendsto q (nhds (0 : EuclideanSpace ℝ (Fin d))) (nhds 0) :=
    tendsto_zeroExtension qraw q hqraw (by simp [q]) (by intro x hx; simp [q, hx])
  have hq_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => q (estimator n X - theta0)) :=
    tendstoInProbZero_comp_zero h.consistency hq
  have hW_tight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, ‖W n X omega‖ ^ 2 ∂M.dominating)) := by
    simpa only [W, s] using firstOrder2576_weightedScore_tight h
  have hterm1 := tendstoInProbZero_of_isBoundedInProb_mul hW_tight hq_prob
  have hCross : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P)) Cross := by
    simpa only [Cross, K, W, u, s, g, smul_smul] using
      qmdModel_scoreCrossTransport_oP_of_2576 h
  have hCrossNorm : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => ‖Cross n X‖) := by
    simpa only [TendstoInProbZero, Real.norm_eq_abs, abs_norm] using hCross
  have hterm2 := tendstoInProbZero_const_smul (1 / 2 : ℝ) hCrossNorm
  have henv := tendstoInProbZero_add hterm1 hterm2
  refine tendstoInProbZero_mono (fun n X => ?_) henv
  simp only [q, qraw, smul_eq_mul]
  by_cases hdelta : estimator n X - theta0 = 0
  · simp only [hdelta, ↓reduceIte, norm_zero, mul_zero, zero_add]
    exact norm_nonneg _
  · simp only [hdelta, ↓reduceIte]
    let delta := estimator n X - theta0
    have hdelta' : delta ≠ 0 := hdelta
    have htHat : MemLp (fun omega => s 0 omega • scoreHat n X omega)
        2 M.dominating := by
      simpa [s, M.curve_at_zero] using
        memLp_sqrt_rnDeriv_smul_of_memLp hPac (h.scoreHat_memLp_truth n X)
    have hsHat : MemLp (fun omega => s delta omega • scoreHat n X omega)
        2 M.dominating := by
      letI := M.curve_isProbability delta
      simpa [s] using memLp_sqrt_rnDeriv_smul_of_memLp
        (M.curve_absContinuous delta) (h.scoreHat_memLp_moving n X)
    have hWmem : MemLp (W n X) 2 M.dominating := by
      simpa [W, delta, add_smul] using! hsHat.add htHat
    have hKmem : MemLp (K n X) 2 M.dominating :=
      hWmem.sub (hscore0s0.const_smul (2 : ℝ))
    let fdelta : Omega → ℝ := fun omega => ⟪delta, g omega⟫_ℝ * s 0 omega
    have hfdelta : MemLp fdelta 2 M.dominating := by
      have hm := memLp_sqrt_rnDeriv_smul_of_memLp hPac
        (MemLp.const_inner (𝕜 := ℝ) delta hgP)
      simpa [fdelta, s, g, M.curve_at_zero, smul_eq_mul, mul_comm] using hm
    have hshift :
        ((∫ omega, scoreHat n X omega ∂(M.curve delta)) -
            ∫ omega, scoreHat n X omega ∂P) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (qmdCrossMoment P M score0) delta =
        ∫ omega, r delta omega • W n X omega ∂M.dominating +
          (1 / 2 : ℝ) • ∫ omega, fdelta omega • K n X omega ∂M.dominating := by
      rw [qmdCrossMoment_apply M score0 h.score0_memLp delta]
      letI := M.curve_isProbability delta
      have hi_delta := (integrable_rnDeriv_smul_iff
        (M.curve_absContinuous delta)).2 ((h.scoreHat_memLp_moving n X).integrable one_le_two)
      have hi_zero := (integrable_rnDeriv_smul_iff hPac).2
        ((h.scoreHat_memLp_truth n X).integrable one_le_two)
      have hi_cross : Integrable (fun omega => ⟪delta, g omega⟫_ℝ • score0 omega) P :=
        memLp_one_iff_integrable.mp
          (h.score0_memLp.smul (MemLp.const_inner (𝕜 := ℝ) delta hgP) :
            MemLp _ 1 P)
      have hi_cross' : Integrable
          (fun omega => ⟪delta, M.score omega⟫_ℝ • score0 omega) P := by
        simpa only [g] using hi_cross
      have hi_cross_mu := (integrable_rnDeriv_smul_iff hPac).2 hi_cross'
      have hi1 : Integrable (fun omega => r delta omega • W n X omega)
          M.dominating := memLp_one_iff_integrable.mp
        (hWmem.smul (hr delta) : MemLp _ 1 M.dominating)
      have hi2 : Integrable (fun omega => fdelta omega • K n X omega)
          M.dominating := memLp_one_iff_integrable.mp
        (hKmem.smul hfdelta : MemLp _ 1 M.dominating)
      have hi2c : Integrable (fun omega =>
          (1 / 2 : ℝ) • (fdelta omega • K n X omega)) M.dominating :=
        memLp_one_iff_integrable.mp
          ((hKmem.smul hfdelta : MemLp _ 1 M.dominating).const_smul (1 / 2 : ℝ))
      rw [← integral_rnDeriv_smul (M.curve_absContinuous delta),
        ← integral_rnDeriv_smul hPac, ← integral_rnDeriv_smul hPac,
        ← integral_sub hi_delta hi_zero]
      rw [← integral_sub]
      · rw [← integral_smul, ← integral_add hi1 hi2c]
        refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
        simp only [r, W, K, fdelta, s, g]
        rw [M.curve_at_zero]
        have hd := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ ((M.curve delta).rnDeriv M.dominating omega).toReal)
        have h0 := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ (P.rnDeriv M.dominating omega).toReal)
        simpa only [hd, h0, smul_smul, delta, mul_comm] using
          vector_sqrt_transport_identity
            (Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal))
            (Real.sqrt ((P.rnDeriv M.dominating omega).toReal))
            ⟪delta, M.score omega⟫_ℝ (scoreHat n X omega) (score0 omega)
      · simpa [Pi.sub_apply] using! hi_delta.sub hi_zero
      · exact hi_cross_mu
    have hcs1 := norm_integral_smul_le_sqrt_integral_sq (hr delta) hWmem
    have hcross_eq : Cross n X = ‖delta‖⁻¹ •
        ∫ omega, fdelta omega • K n X omega ∂M.dominating := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Eventually.of_forall fun omega => by
        simp only [u, delta, hdelta, ↓reduceIte, fdelta,
          real_inner_smul_left, smul_smul]
        module
    have hcross_norm : ‖delta‖⁻¹ *
        ‖∫ omega, fdelta omega • K n X omega ∂M.dominating‖ = ‖Cross n X‖ := by
      rw [hcross_eq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg delta))]
    rw [hshift, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg delta))]
    have hinv : 0 ≤ ‖delta‖⁻¹ := inv_nonneg.mpr (norm_nonneg delta)
    have hsum : ‖(∫ omega, r delta omega • W n X omega ∂M.dominating) +
          (1 / 2 : ℝ) • ∫ omega, fdelta omega • K n X omega ∂M.dominating‖ ≤
        ‖∫ omega, r delta omega • W n X omega ∂M.dominating‖ +
          (1 / 2 : ℝ) * ‖∫ omega, fdelta omega • K n X omega ∂M.dominating‖ := by
      calc
        _ ≤ ‖∫ omega, r delta omega • W n X omega ∂M.dominating‖ +
            ‖(1 / 2 : ℝ) • ∫ omega, fdelta omega • K n X omega
              ∂M.dominating‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have henv_nonneg : 0 ≤
        Real.sqrt (∫ omega, ‖W n X omega‖ ^ 2 ∂M.dominating) *
            (Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) / ‖delta‖) +
          (1 / 2 : ℝ) * ‖Cross n X‖ :=
      add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _)
          (div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
        (mul_nonneg (by norm_num) (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg henv_nonneg]
    calc
      _ ≤ ‖delta‖⁻¹ *
          (‖∫ omega, r delta omega • W n X omega ∂M.dominating‖ +
            (1 / 2 : ℝ) *
              ‖∫ omega, fdelta omega • K n X omega ∂M.dominating‖) :=
        mul_le_mul_of_nonneg_left hsum hinv
      _ ≤ ‖delta‖⁻¹ *
          (Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) *
              Real.sqrt (∫ omega, ‖W n X omega‖ ^ 2 ∂M.dominating) +
            (1 / 2 : ℝ) *
              ‖∫ omega, fdelta omega • K n X omega ∂M.dominating‖) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hcs1 le_rfl) hinv
      _ = Real.sqrt (∫ omega, ‖W n X omega‖ ^ 2 ∂M.dominating) *
            (Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) / ‖delta‖) +
          (1 / 2 : ℝ) * ‖Cross n X‖ := by
        rw [← hcross_norm, mul_add]
        simp only [div_eq_mul_inv]
        ring

set_option maxHeartbeats 4000000 in
-- The RN/Bochner normalization proof elaborates several dependent Euclidean integrals.
/-- Native model-shift expansion normalized by the nonzero local-parameter norm.
The value at zero is explicitly defined to be zero.

The proof uses the native consistency field to localize `M.qmd_limit`; the three
weighted-score fields respectively guarantee a genuine L2 object, supply the
`O_P(1)` factor, and identify the matrix cross moment through one CLM. -/
theorem qmdModel_modelShift_normalized_oP
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : HellingerScoreTransportHypVec P M estimator theta0 scoreHat score0) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let delta := estimator n X - theta0
        if delta = 0 then 0 else
          ‖delta‖⁻¹ •
            (((∫ omega, scoreHat n X omega ∂(M.curve delta)) -
                ∫ omega, scoreHat n X omega ∂P)
              - Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (qmdCrossMoment P M score0) delta)) := by
  let s : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal)
  let g : Omega → EuclideanSpace ℝ (Fin d) := M.score
  let r : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    s delta omega - s 0 omega - (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega
  let W : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d) :=
    fun n X omega => (s (estimator n X - theta0) omega + s 0 omega) • scoreHat n X omega
  let K : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d) :=
    fun n X omega => W n X omega - (2 : ℝ) • (s 0 omega • score0 omega)
  let G0 : Omega → ℝ := fun omega => ‖g omega‖ * s 0 omega
  have hs : ∀ delta, MemLp (s delta) 2 M.dominating := fun delta => by
    letI := M.curve_isProbability delta
    simpa [s] using
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
        (M.curve_absContinuous delta)
  have hPac : P ≪ M.dominating := by
    simpa only [← M.curve_at_zero] using M.curve_absContinuous 0
  have hgP : MemLp g 2 P := by simpa [g] using M.score_memLp
  have hG0 : MemLp G0 2 M.dominating := by
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
      hPac hgP.norm
    simpa [G0, s, g, M.curve_at_zero, smul_eq_mul, mul_comm] using hm
  have hscore0s0 : MemLp (fun omega => s 0 omega • score0 omega) 2 M.dominating := by
    simpa [s, M.curve_at_zero] using
      memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
        hPac h.score0_memLp
  have hr : ∀ delta, MemLp (r delta) 2 M.dominating := fun delta => by
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
      hPac (MemLp.const_inner (𝕜 := ℝ) delta hgP)
    have ht : MemLp (fun omega =>
        (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) 2 M.dominating := by
      simpa [s, g, M.curve_at_zero, smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm] using hm.const_mul (1 / 2 : ℝ)
    exact (hs delta).sub (hs 0) |>.sub (by simpa [r] using ht)
  let qraw : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) / ‖delta‖
  let q : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    if delta = 0 then 0 else qraw delta
  have hqraw : Tendsto qraw (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp
      M.qmd_limit
    simp only [Function.comp_def, ENNReal.toReal_zero] at ht
    refine ht.congr' (Eventually.of_forall fun delta => ?_)
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (norm_nonneg delta),
      ← AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
        (hr delta)]
  have hq : Tendsto q (𝓝 (0 : EuclideanSpace ℝ (Fin d))) (𝓝 0) :=
    tendsto_zeroExtension qraw q hqraw (by simp [q]) (by intro x hx; simp [q, hx])
  have hq_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => q (estimator n X - theta0)) :=
    tendstoInProbZero_comp_zero h.consistency hq
  have hW_tight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, ‖W n X omega‖ ^ 2 ∂M.dominating)) := by
    simpa only [W, s] using h.weightedScore_tight
  have hterm1 := tendstoInProbZero_of_isBoundedInProb_mul hW_tight hq_prob
  have hK_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, ‖K n X omega‖ ^ 2 ∂M.dominating)) := by
    simpa only [K, W, s, smul_smul] using h.weightedScore_transport
  have hterm2 := tendstoInProbZero_const_smul
    (Real.sqrt (∫ omega, G0 omega ^ 2 ∂M.dominating) / 2) hK_prob
  have henv := tendstoInProbZero_add hterm1 hterm2
  refine tendstoInProbZero_mono (fun n X => ?_) henv
  simp only [q, qraw, smul_eq_mul]
  by_cases hdelta : estimator n X - theta0 = 0
  · simp only [hdelta, ↓reduceIte, norm_zero, mul_zero, zero_add]
    exact norm_nonneg _
  · simp only [hdelta, ↓reduceIte]
    let delta := estimator n X - theta0
    have hdelta' : delta ≠ 0 := hdelta
    have hWmem : MemLp (W n X) 2 M.dominating := h.weightedScore_memLp n X
    have hKmem : MemLp (K n X) 2 M.dominating := by
      exact hWmem.sub (hscore0s0.const_smul (2 : ℝ))
    let fdelta : Omega → ℝ := fun omega => ⟪delta, g omega⟫_ℝ * s 0 omega
    have hfdelta : MemLp fdelta 2 M.dominating := by
      have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
        hPac (MemLp.const_inner (𝕜 := ℝ) delta hgP)
      simpa [fdelta, s, g, M.curve_at_zero, smul_eq_mul, mul_comm] using hm
    have hshift :
        ((∫ omega, scoreHat n X omega ∂(M.curve delta)) -
            ∫ omega, scoreHat n X omega ∂P) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (qmdCrossMoment P M score0) delta =
        ∫ omega, r delta omega • W n X omega ∂M.dominating +
          (1 / 2 : ℝ) • ∫ omega, fdelta omega • K n X omega ∂M.dominating := by
      rw [qmdCrossMoment_apply M score0 h.score0_memLp delta]
      letI := M.curve_isProbability delta
      have hi_delta := (integrable_rnDeriv_smul_iff
        (M.curve_absContinuous delta)).2 (h.scoreHat_integrable_moving n X)
      have hi_zero := (integrable_rnDeriv_smul_iff hPac).2
        (h.scoreHat_integrable_truth n X)
      have hi_cross : Integrable (fun omega => ⟪delta, g omega⟫_ℝ • score0 omega) P :=
        memLp_one_iff_integrable.mp
          (h.score0_memLp.smul (MemLp.const_inner (𝕜 := ℝ) delta hgP) :
            MemLp _ 1 P)
      have hi_cross' : Integrable
          (fun omega => ⟪delta, M.score omega⟫_ℝ • score0 omega) P := by
        simpa only [g] using hi_cross
      have hi_cross_mu := (integrable_rnDeriv_smul_iff hPac).2 hi_cross'
      have hi1 : Integrable (fun omega => r delta omega • W n X omega)
          M.dominating :=
        memLp_one_iff_integrable.mp
          (hWmem.smul (hr delta) : MemLp _ 1 M.dominating)
      have hi2 : Integrable (fun omega => fdelta omega • K n X omega)
          M.dominating :=
        memLp_one_iff_integrable.mp
          (hKmem.smul hfdelta : MemLp _ 1 M.dominating)
      have hi2c : Integrable
          (fun omega => (1 / 2 : ℝ) • (fdelta omega • K n X omega)) M.dominating :=
        memLp_one_iff_integrable.mp
          ((hKmem.smul hfdelta : MemLp _ 1 M.dominating).const_smul (1 / 2 : ℝ))
      rw [← integral_rnDeriv_smul (M.curve_absContinuous delta),
        ← integral_rnDeriv_smul hPac, ← integral_rnDeriv_smul hPac,
        ← integral_sub hi_delta hi_zero]
      rw [← integral_sub]
      · rw [← integral_smul, ← integral_add hi1 hi2c]
        refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
        simp only [r, W, K, fdelta, s, g]
        rw [M.curve_at_zero]
        have hd := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ ((M.curve delta).rnDeriv M.dominating omega).toReal)
        have h0 := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ (P.rnDeriv M.dominating omega).toReal)
        simpa only [hd, h0, smul_smul, delta, mul_comm] using
          vector_sqrt_transport_identity
          (Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal))
          (Real.sqrt ((P.rnDeriv M.dominating omega).toReal))
          ⟪delta, M.score omega⟫_ℝ (scoreHat n X omega) (score0 omega)
      · simpa [Pi.sub_apply] using! hi_delta.sub hi_zero
      · exact hi_cross_mu
    have hpoint : ∀ omega, fdelta omega ^ 2 ≤ ‖delta‖ ^ 2 * G0 omega ^ 2 := by
      intro omega
      have hinner := abs_real_inner_le_norm delta (g omega)
      have hsquare : ⟪delta, g omega⟫_ℝ ^ 2 ≤ (‖delta‖ * ‖g omega‖) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg ⟪delta, g omega⟫_ℝ)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
      simp only [fdelta, G0]
      calc
        (⟪delta, g omega⟫_ℝ * s 0 omega) ^ 2 =
            ⟪delta, g omega⟫_ℝ ^ 2 * s 0 omega ^ 2 := by ring
        _ ≤ (‖delta‖ * ‖g omega‖) ^ 2 * s 0 omega ^ 2 :=
          mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
        _ = ‖delta‖ ^ 2 * (‖g omega‖ * s 0 omega) ^ 2 := by ring
    rw [hshift, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg delta))]
    have henv_nonneg : 0 ≤
        Real.sqrt (∫ omega, ‖W n X omega‖ ^ 2 ∂M.dominating) *
            (Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) / ‖delta‖) +
          Real.sqrt (∫ omega, G0 omega ^ 2 ∂M.dominating) / 2 *
            Real.sqrt (∫ omega, ‖K n X omega‖ ^ 2 ∂M.dominating) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg henv_nonneg]
    exact native_modelShift_normalized_bound (μ := M.dominating) (delta := delta)
      hdelta' (hr delta) hfdelta hG0 hWmem hKmem hpoint

/-- Ordinary native model-shift expansion from root-`n` tightness.

The cross moment acts through one matrix/continuous-linear-map expression; no
coordinatewise inverse or scalar discharge appears in the statement.

The proof applies `qmdModel_modelShift_normalized_oP` and multiplies its native
remainder by the `O_P(1)` root-`n` local parameter supplied by `hTight`. -/
theorem qmdModel_modelShift_oP_of_sqrtN_tight
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : HellingerScoreTransportHypVec P M estimator theta0 scoreHat score0)
    -- root-`n` tightness of the native local parameter.
    (hTight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n • (estimator n X - theta0))) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        Real.sqrt n •
            ((∫ omega, scoreHat n X omega ∂P) -
              ∫ omega, scoreHat n X omega
                ∂(M.curve (estimator n X - theta0)))
          + Real.sqrt n •
              (Matrix.toEuclideanCLM (𝕜 := ℝ)
                (qmdCrossMoment P M score0) (estimator n X - theta0))) := by
  have hnorm := qmdModel_modelShift_normalized_oP h
  have hscale : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * ‖estimator n X - theta0‖) := by
    simpa only [IsBoundedInProb, norm_smul, Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _)] using hTight
  have hprod := tendstoInProbZero_of_isBoundedInProb_mul hscale hnorm
  have hneg := tendstoInProbZero_const_smul (-1) hprod
  convert hneg using 1
  funext n X
  let delta := estimator n X - theta0
  by_cases hdelta : delta = 0
  · simp [delta, hdelta, M.curve_at_zero]
  · simp only [delta, hdelta, ↓reduceIte]
    have hnorm : ‖estimator n X - theta0‖ ≠ 0 := by
      simpa only [delta] using norm_ne_zero_iff.mpr hdelta
    have hcancel :
        Real.sqrt n * ‖estimator n X - theta0‖ *
            ‖estimator n X - theta0‖⁻¹ = Real.sqrt n := by
      field_simp [hnorm]
    simp only [smul_smul, hcancel]
    module

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
