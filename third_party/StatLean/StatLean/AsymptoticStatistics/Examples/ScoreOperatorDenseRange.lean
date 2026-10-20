module
public import StatLean.AsymptoticStatistics.Operators.ScoreOperator
public import StatLean.AsymptoticStatistics.LowerBounds.ScoreOperatorRegularityObstruction
public import StatLean.AsymptoticStatistics.Core.MassMethod
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.AsymptoticStatistics.Operators.InformationLoss
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! # Concrete dense nonclosed score-range witnesses for vdV 25.32 -/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal
namespace AsymptoticStatistics.Examples.ScoreOperatorDenseRange
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Operators.ScoreOperator
open AsymptoticStatistics.LowerBounds.ScoreOperatorRegularityObstruction
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.MassMethod
open Asymptotics

/-- Full-support half-geometric law used by the compressed multiplier model. -/
def IsHalfGeometricFullSupport (P : Measure ℕ) : Prop :=
  (∀ n : ℕ, 0 < P {n}) ∧
    ∀ n : ℕ, P {n + 1} = (2 : ℝ≥0∞)⁻¹ * P {n}

-- Port note (Mathlib db584cd): `geometricMeasure` now takes `p : unitInterval` (same law
-- `n ↦ (1 - p) ^ n * p`); its probability-measure instance is inferred.
private noncomputable def halfGeometricP : Measure ℕ :=
  geometricMeasure ⟨1 / 2, by constructor <;> norm_num⟩

private noncomputable instance halfGeometricP_isProbability :
    IsProbabilityMeasure halfGeometricP := by
  unfold halfGeometricP; infer_instance

private instance halfGeometricL2ZeroMean_closed :
    IsClosed (L2ZeroMean halfGeometricP : Set (Lp ℝ 2 halfGeometricP)) :=
  L2ZeroMean_isClosed halfGeometricP

private noncomputable instance halfGeometricL2ZeroMean_complete :
    CompleteSpace ↥(L2ZeroMean halfGeometricP) :=
  inferInstance

private lemma halfGeometricP_singleton (n : ℕ) :
    halfGeometricP {n} = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  unfold halfGeometricP
  rw [geometricMeasure_singleton (by simp [← Subtype.coe_inj])]
  congr 1
  show (1 - 1 / 2 : ℝ) ^ n * (1 / 2) = _
  ring

private lemma halfGeometricP_fullSupport :
    IsHalfGeometricFullSupport halfGeometricP := by
  constructor
  · intro n
    rw [halfGeometricP_singleton]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  · intro n
    rw [halfGeometricP_singleton, halfGeometricP_singleton]
    rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

private noncomputable def denseMultiplier (n : ℕ) : ℝ :=
  Real.sqrt (1 / 2 : ℝ) ^ n

private lemma denseMultiplier_nonneg (n : ℕ) : 0 ≤ denseMultiplier n := by
  exact pow_nonneg (Real.sqrt_nonneg _) _

private lemma denseMultiplier_pos (n : ℕ) : 0 < denseMultiplier n := by
  exact pow_pos (Real.sqrt_pos.2 (by norm_num)) _

private lemma denseMultiplier_le_one (n : ℕ) : denseMultiplier n ≤ 1 := by
  apply pow_le_one₀ (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_one]
  norm_num

private noncomputable def multiplyDenseRaw
    (f : Lp ℝ 2 halfGeometricP) (n : ℕ) : ℝ :=
  denseMultiplier n * f n

private lemma multiplyDenseRaw_memLp (f : Lp ℝ 2 halfGeometricP) :
    MemLp (multiplyDenseRaw f) 2 halfGeometricP := by
  apply MemLp.of_le (Lp.memLp f)
  · unfold multiplyDenseRaw
    exact (measurable_of_countable _).aestronglyMeasurable
  · filter_upwards with n
    unfold multiplyDenseRaw
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (denseMultiplier_nonneg n)]
    exact mul_le_of_le_one_left (abs_nonneg _) (denseMultiplier_le_one n)

private noncomputable def multiplyDenseLp :
    Lp ℝ 2 halfGeometricP →ₗ[ℝ] Lp ℝ 2 halfGeometricP where
  toFun f := (multiplyDenseRaw_memLp f).toLp (multiplyDenseRaw f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(multiplyDenseRaw_memLp (f + g)).coeFn_toLp,
      (multiplyDenseRaw_memLp f).coeFn_toLp,
      (multiplyDenseRaw_memLp g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add ((multiplyDenseRaw_memLp f).toLp (multiplyDenseRaw f))
        ((multiplyDenseRaw_memLp g).toLp (multiplyDenseRaw g))]
      with n hfg hf hg hadd hadd_out
    rw [hfg, hadd_out, Pi.add_apply, hf, hg]
    unfold multiplyDenseRaw
    rw [hadd, Pi.add_apply]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(multiplyDenseRaw_memLp (c • f)).coeFn_toLp,
      (multiplyDenseRaw_memLp f).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((multiplyDenseRaw_memLp f).toLp (multiplyDenseRaw f))]
      with n hcf hf hsmul hsmul_out
    rw [hcf]
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul] at hsmul_out ⊢
    rw [hsmul_out, hf]
    unfold multiplyDenseRaw
    rw [hsmul, Pi.smul_apply, smul_eq_mul]
    change denseMultiplier n * (c * f n) = c * (denseMultiplier n * f n)
    ring

private lemma multiplyDenseLp_coe (f : Lp ℝ 2 halfGeometricP) :
    ((multiplyDenseLp f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ)
      =ᵐ[halfGeometricP] multiplyDenseRaw f :=
  (multiplyDenseRaw_memLp f).coeFn_toLp

private lemma multiplyDenseLp_norm_le (f : Lp ℝ 2 halfGeometricP) :
    ‖multiplyDenseLp f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [multiplyDenseLp_coe f] with n hn
  rw [hn]
  unfold multiplyDenseRaw
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (denseMultiplier_nonneg n)]
  exact mul_le_of_le_one_left (abs_nonneg _) (denseMultiplier_le_one n)

private noncomputable def multiplyDenseCLM :
    Lp ℝ 2 halfGeometricP →L[ℝ] Lp ℝ 2 halfGeometricP :=
  multiplyDenseLp.mkContinuous 1 (by simpa using multiplyDenseLp_norm_le)

private lemma integralL2_one_halfGeometric :
    integralL2 halfGeometricP (oneL2 halfGeometricP) = 1 := by
  rw [AsymptoticStatistics.Operators.InformationLoss.integralL2_apply]
  unfold oneL2
  rw [integral_congr_ae (memLp_const (1 : ℝ)).coeFn_toLp]
  simp

private noncomputable def centerHalfGeometricCLM :
    Lp ℝ 2 halfGeometricP →L[ℝ] Lp ℝ 2 halfGeometricP :=
  ContinuousLinearMap.id ℝ _ -
    (ContinuousLinearMap.toSpanSingleton ℝ (oneL2 halfGeometricP)).comp
      (integralL2 halfGeometricP)

private lemma centerHalfGeometricCLM_apply (f : Lp ℝ 2 halfGeometricP) :
    centerHalfGeometricCLM f =
      f - (integralL2 halfGeometricP f) • oneL2 halfGeometricP := by
  simp [centerHalfGeometricCLM, ContinuousLinearMap.toSpanSingleton_apply]

private lemma centerHalfGeometricCLM_mem (_f : Lp ℝ 2 halfGeometricP) :
    centerHalfGeometricCLM _f ∈ L2ZeroMean halfGeometricP := by
  rw [L2ZeroMean, LinearMap.mem_ker]
  change integralL2 halfGeometricP (centerHalfGeometricCLM _f) = 0
  rw [centerHalfGeometricCLM_apply, map_sub, map_smul,
    integralL2_one_halfGeometric]
  simp

private noncomputable def compressedDenseMap :
    ↥(L2ZeroMean halfGeometricP) →L[ℝ]
      ↥(L2ZeroMean halfGeometricP) :=
  (centerHalfGeometricCLM.comp
      (multiplyDenseCLM.comp (L2ZeroMean halfGeometricP).subtypeL)).codRestrict
    (L2ZeroMean halfGeometricP) (fun _ => centerHalfGeometricCLM_mem _)

private lemma compressedDenseMap_coe (f : ↥(L2ZeroMean halfGeometricP)) :
    (compressedDenseMap f : Lp ℝ 2 halfGeometricP) =
      multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP) -
        (integralL2 halfGeometricP
          (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP))) •
            oneL2 halfGeometricP := by
  exact centerHalfGeometricCLM_apply _

private lemma centerHalfGeometricCLM_eq_starProjection
    (f : Lp ℝ 2 halfGeometricP) :
    centerHalfGeometricCLM f =
      (L2ZeroMean halfGeometricP).starProjection f := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (centerHalfGeometricCLM_mem f)
  intro w hw
  have hw0 : integralL2 halfGeometricP w = 0 := by
    exact hw
  rw [centerHalfGeometricCLM_apply]
  have hone : ⟪oneL2 halfGeometricP, w⟫_ℝ = 0 := by
    simpa [integralL2] using hw0
  rw [show f - (f - (integralL2 halfGeometricP f) • oneL2 halfGeometricP) =
      (integralL2 halfGeometricP f) • oneL2 halfGeometricP by abel,
    inner_smul_left, hone, mul_zero]

private lemma compressedDenseMap_eq_projection
    (f : ↥(L2ZeroMean halfGeometricP)) :
    compressedDenseMap f =
      (L2ZeroMean halfGeometricP).orthogonalProjection
        (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP)) := by
  apply Subtype.ext
  exact centerHalfGeometricCLM_eq_starProjection _

private lemma multiplyDenseCLM_symmetric
    (f g : Lp ℝ 2 halfGeometricP) :
    ⟪multiplyDenseCLM f, g⟫_ℝ = ⟪f, multiplyDenseCLM g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplyDenseLp_coe f, multiplyDenseLp_coe g]
    with n hf hg
  change ⟪((multiplyDenseLp f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n,
      (g : ℕ → ℝ) n⟫_ℝ =
    ⟪(f : ℕ → ℝ) n,
      ((multiplyDenseLp g : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n⟫_ℝ
  rw [hf, hg]
  unfold multiplyDenseRaw
  change (g : ℕ → ℝ) n * (denseMultiplier n * (f : ℕ → ℝ) n) =
    (denseMultiplier n * (g : ℕ → ℝ) n) * (f : ℕ → ℝ) n
  ring

private lemma compressedDenseMap_symmetric
    (f g : ↥(L2ZeroMean halfGeometricP)) :
    ⟪compressedDenseMap f, g⟫_ℝ = ⟪f, compressedDenseMap g⟫_ℝ := by
  rw [compressedDenseMap_eq_projection, compressedDenseMap_eq_projection,
    Submodule.inner_orthogonalProjection_eq_of_mem_right,
    Submodule.inner_orthogonalProjection_eq_of_mem_left]
  exact multiplyDenseCLM_symmetric _ _

private lemma denseMultiplier_sq (n : ℕ) :
    denseMultiplier n ^ 2 = (1 / 2 : ℝ) ^ n := by
  rw [denseMultiplier, pow_two, ← mul_pow,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private lemma compressedDenseMap_apply_ae
    (f : ↥(L2ZeroMean halfGeometricP)) :
    (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) =ᵐ[halfGeometricP]
      fun n => denseMultiplier n *
          ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n -
        integralL2 halfGeometricP
          (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP)) := by
  have hmain :
      (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
        Lp ℝ 2 halfGeometricP) : ℕ → ℝ) =ᵐ[halfGeometricP]
        (((multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP) -
          (integralL2 halfGeometricP
            (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP))) •
              oneL2 halfGeometricP : Lp ℝ 2 halfGeometricP) : ℕ → ℝ)) := by
    rw [compressedDenseMap_coe]
  filter_upwards [hmain,
      Lp.coeFn_sub (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP))
        ((integralL2 halfGeometricP
          (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP))) •
            oneL2 halfGeometricP),
      Lp.coeFn_smul
        (integralL2 halfGeometricP
          (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP)))
        (oneL2 halfGeometricP),
      multiplyDenseLp_coe (f : Lp ℝ 2 halfGeometricP),
      (memLp_const (1 : ℝ)).coeFn_toLp]
    with n hn hsub hsmul hmul hone
  rw [hn, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul]
  change ((multiplyDenseLp (f : Lp ℝ 2 halfGeometricP) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n - _ = _
  rw [hmul]
  change denseMultiplier n *
        ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n -
      (integralL2 halfGeometricP
        (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP))) *
          ((oneL2 halfGeometricP : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n = _
  unfold oneL2
  rw [hone]
  ring

private lemma compressedDenseMap_apply_everywhere
    (f : ↥(L2ZeroMean halfGeometricP)) (n : ℕ) :
    (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n =
      denseMultiplier n *
          ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n -
        integralL2 halfGeometricP
          (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP)) := by
  exact (ae_iff_of_countable.mp (compressedDenseMap_apply_ae f) n
    (halfGeometricP_fullSupport.1 n).ne')

private lemma summable_singleton_norm_of_integrable
    {u : ℕ → ℝ} (hu : Integrable u halfGeometricP) :
    Summable (fun n : ℕ => (halfGeometricP {n}).toReal * ‖u n‖) := by
  have htop : (∑' n : ℕ, ‖u n‖ₑ * halfGeometricP {n}) ≠ ∞ := by
    rw [← lintegral_countable' (μ := halfGeometricP)
      (fun n : ℕ => ‖u n‖ₑ)]
    exact hu.hasFiniteIntegral.ne
  have hs := ENNReal.summable_toReal htop
  convert hs using 1
  ext n
  rw [ENNReal.toReal_mul]
  simp [mul_comm]

private lemma zeroL2_coe_everywhere (n : ℕ) :
    (((0 : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) = 0 := by
  exact ae_iff_of_countable.mp
    (Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := halfGeometricP)) n
    (halfGeometricP_fullSupport.1 n).ne'

private lemma compressedDenseMap_eq_zero
    {f : ↥(L2ZeroMean halfGeometricP)} (hf : compressedDenseMap f = 0) :
    f = 0 := by
  let c : ℝ := integralL2 halfGeometricP
    (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP))
  have hpoint : ∀ n : ℕ,
      denseMultiplier n *
          ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n = c := by
    intro n
    have hn := compressedDenseMap_apply_everywhere f n
    rw [hf] at hn
    rw [show ((((0 : ↥(L2ZeroMean halfGeometricP)) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) = 0 by
        exact zeroL2_coe_everywhere n] at hn
    change 0 = denseMultiplier n *
        ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n - c at hn
    linarith
  have hfint : Integrable
      (fun n : ℕ => (((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2)
      halfGeometricP := by
    exact (Lp.memLp (f : Lp ℝ 2 halfGeometricP)).integrable_sq
  have hsum : Summable (fun n : ℕ =>
      (halfGeometricP {n}).toReal *
        ‖(((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2‖) := by
    exact summable_singleton_norm_of_integrable hfint
  have hterm : ∀ n : ℕ,
      (halfGeometricP {n}).toReal *
          ‖(((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2‖ =
        c ^ 2 / 2 := by
    intro n
    rw [halfGeometricP_singleton,
      ENNReal.toReal_ofReal (by positivity),
      Real.norm_of_nonneg (sq_nonneg _), pow_succ,
      ← denseMultiplier_sq]
    have hs := congrArg (fun x : ℝ => x ^ 2) (hpoint n)
    nlinarith
  have hc_sum : Summable (fun _ : ℕ => c ^ 2 / 2) :=
    hsum.congr hterm
  have hc_sq : c ^ 2 / 2 = 0 := by
    simpa only [summable_const_iff] using hc_sum
  have hc : c = 0 := by nlinarith [sq_nonneg c]
  apply Subtype.ext
  apply Lp.ext
  filter_upwards with n
  rw [show ((((0 : ↥(L2ZeroMean halfGeometricP)) :
    Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) = 0 by
      exact zeroL2_coe_everywhere n]
  have hn := hpoint n
  rw [hc] at hn
  exact (mul_eq_zero.mp hn).resolve_left (denseMultiplier_pos n).ne'

private lemma compressedDenseMap_injective :
    Function.Injective compressedDenseMap := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply compressedDenseMap_eq_zero
  rw [map_sub, hfg, sub_self]

private lemma compressedDenseMap_denseRange :
    DenseRange compressedDenseMap := by
  have hsym : (compressedDenseMap :
      ↥(L2ZeroMean halfGeometricP) →ₗ[ℝ]
        ↥(L2ZeroMean halfGeometricP)).IsSymmetric :=
    compressedDenseMap_symmetric
  have hker : compressedDenseMap.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr compressedDenseMap_injective
  have hclosure : compressedDenseMap.range.topologicalClosure = ⊤ := by
    refine (@Submodule.topologicalClosure_eq_top_iff
      ℝ ↥(L2ZeroMean halfGeometricP) inferInstance inferInstance inferInstance
      compressedDenseMap.range
      ((L2ZeroMean_isClosed halfGeometricP).isComplete.completeSpace_coe)).2 ?_
    change (LinearMap.range (compressedDenseMap :
      ↥(L2ZeroMean halfGeometricP) →ₗ[ℝ]
        ↥(L2ZeroMean halfGeometricP)))ᗮ = ⊥
    rw [hsym.orthogonal_range]
    exact hker
  rw [denseRange_iff_closure_range]
  change closure (compressedDenseMap.range :
      Set ↥(L2ZeroMean halfGeometricP)) = Set.univ
  simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe]
    using congrArg SetLike.coe hclosure

private noncomputable def denseQRaw (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n - 1 / 3

private lemma denseQRaw_memLp : MemLp denseQRaw 2 halfGeometricP := by
  apply MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 2
  filter_upwards with n
  rw [Real.norm_eq_abs]
  calc
    |denseQRaw n| ≤ |(-1 : ℝ) ^ n| + |(1 / 3 : ℝ)| := by
      simpa [denseQRaw] using abs_sub ((-1 : ℝ) ^ n) (1 / 3 : ℝ)
    _ = 4 / 3 := by norm_num [div_eq_mul_inv]
    _ ≤ 2 := by norm_num

private noncomputable def denseQLp : Lp ℝ 2 halfGeometricP :=
  denseQRaw_memLp.toLp denseQRaw

private lemma denseQLp_coe :
    ((denseQLp : Lp ℝ 2 halfGeometricP) : ℕ → ℝ)
      =ᵐ[halfGeometricP] denseQRaw :=
  denseQRaw_memLp.coeFn_toLp

private lemma denseQRaw_integrable : Integrable denseQRaw halfGeometricP :=
  denseQRaw_memLp.integrable (by norm_num)

private lemma hasSum_halfGeometric_alternating :
    HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n)
      (1 / 3 : ℝ) := by
  have h := (hasSum_geometric_of_norm_lt_one
    (ξ := (-1 / 2 : ℝ)) (by norm_num)).mul_left (1 / 2 : ℝ)
  convert! h using 1
  · ext n
    rw [pow_succ]
    rw [show (-1 / 2 : ℝ) = (1 / 2) * (-1) by ring, mul_pow]
    ring
  · norm_num

private lemma hasSum_halfGeometric_third :
    HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * (1 / 3 : ℝ))
      (1 / 3 : ℝ) := by
  have h := (hasSum_geometric_of_norm_lt_one
    (ξ := (1 / 2 : ℝ)) (by norm_num)).mul_left (1 / 6 : ℝ)
  convert! h using 1
  · ext n
    rw [pow_succ]
    ring
  · norm_num

private lemma integral_denseQRaw :
    ∫ n, denseQRaw n ∂halfGeometricP = 0 := by
  rw [integral_countable denseQRaw_integrable]
  have hsum := hasSum_halfGeometric_alternating.sub hasSum_halfGeometric_third
  calc
    (∑' n, halfGeometricP.real {n} • denseQRaw n) =
        ∑' n, ((1 / 2 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n -
          (1 / 2 : ℝ) ^ (n + 1) * (1 / 3 : ℝ)) := by
      apply tsum_congr
      intro n
      rw [Measure.real, halfGeometricP_singleton,
        ENNReal.toReal_ofReal (by positivity)]
      change (1 / 2 : ℝ) ^ (n + 1) * denseQRaw n = _
      simp only [denseQRaw]
      ring
    _ = (1 / 3 : ℝ) - 1 / 3 := hsum.tsum_eq
    _ = 0 := by ring

private noncomputable def denseQ : ↥(L2ZeroMean halfGeometricP) :=
  ⟨denseQLp, by
    rw [AsymptoticStatistics.Operators.InformationLoss.mem_L2ZeroMean_iff]
    rw [integral_congr_ae denseQLp_coe]
    exact integral_denseQRaw⟩

private lemma denseQ_coe_everywhere (n : ℕ) :
    (((denseQ : ↥(L2ZeroMean halfGeometricP)) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n = denseQRaw n := by
  exact ae_iff_of_countable.mp denseQLp_coe n
    (halfGeometricP_fullSupport.1 n).ne'

private lemma denseQ_not_mem_compressedDenseMap_range :
    denseQ ∉ compressedDenseMap.range := by
  rintro ⟨f, hf⟩
  change compressedDenseMap f = denseQ at hf
  let c : ℝ := integralL2 halfGeometricP
    (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP))
  have hpoint : ∀ n : ℕ,
      denseMultiplier n *
          ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n =
        denseQRaw n + c := by
    intro n
    have hn := compressedDenseMap_apply_everywhere f n
    have hfn := congrArg (fun z : ↥(L2ZeroMean halfGeometricP) =>
      (((z : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n)) hf
    change (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n =
      (((denseQ : ↥(L2ZeroMean halfGeometricP)) :
        Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n at hfn
    rw [denseQ_coe_everywhere] at hfn
    rw [hfn] at hn
    dsimp only [c]
    linarith
  have hfint : Integrable
      (fun n : ℕ => (((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2)
      halfGeometricP := by
    exact (Lp.memLp (f : Lp ℝ 2 halfGeometricP)).integrable_sq
  have hsum : Summable (fun n : ℕ =>
      (halfGeometricP {n}).toReal *
        ‖(((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2‖) := by
    exact summable_singleton_norm_of_integrable hfint
  have hterm : ∀ n : ℕ,
      (halfGeometricP {n}).toReal *
          ‖(((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2‖ =
        (denseQRaw n + c) ^ 2 / 2 := by
    intro n
    rw [halfGeometricP_singleton,
      ENNReal.toReal_ofReal (by positivity),
      Real.norm_of_nonneg (sq_nonneg _), pow_succ,
      ← denseMultiplier_sq]
    have hs := congrArg (fun x : ℝ => x ^ 2) (hpoint n)
    nlinarith
  have halt : Summable (fun n : ℕ => (denseQRaw n + c) ^ 2 / 2) :=
    hsum.congr hterm
  have hzero := halt.tendsto_atTop_zero
  have hevenMap : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hoddMap : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have heven := hzero.comp hevenMap
  have hodd := hzero.comp hoddMap
  have heven_eq :
      (fun n : ℕ => (denseQRaw (2 * n) + c) ^ 2 / 2) =
        fun _ => ((2 / 3 : ℝ) + c) ^ 2 / 2 := by
    funext n
    simp [denseQRaw, pow_mul]
    ring
  have hodd_eq :
      (fun n : ℕ => (denseQRaw (2 * n + 1) + c) ^ 2 / 2) =
        fun _ => ((-4 / 3 : ℝ) + c) ^ 2 / 2 := by
    funext n
    simp [denseQRaw, pow_succ, pow_mul]
    ring
  change Tendsto (fun n : ℕ => (denseQRaw (2 * n) + c) ^ 2 / 2)
      atTop (𝓝 0) at heven
  change Tendsto (fun n : ℕ => (denseQRaw (2 * n + 1) + c) ^ 2 / 2)
      atTop (𝓝 0) at hodd
  rw [heven_eq] at heven
  rw [hodd_eq] at hodd
  have hc_even : ((2 / 3 : ℝ) + c) ^ 2 / 2 = 0 :=
    (tendsto_nhds_unique heven tendsto_const_nhds).symm
  have hc_odd : ((-4 / 3 : ℝ) + c) ^ 2 / 2 = 0 :=
    (tendsto_nhds_unique hodd tendsto_const_nhds).symm
  nlinarith

private lemma compressedDenseMap_range_not_closed :
    ¬ IsClosed (compressedDenseMap.range :
      Set ↥(L2ZeroMean halfGeometricP)) := by
  intro hclosed
  have hdense : closure (Set.range compressedDenseMap) = Set.univ :=
    compressedDenseMap_denseRange.closure_range
  have hrange : (compressedDenseMap.range :
      Set ↥(L2ZeroMean halfGeometricP)) = Set.univ := by
    calc
      (compressedDenseMap.range : Set ↥(L2ZeroMean halfGeometricP)) =
          closure (compressedDenseMap.range :
            Set ↥(L2ZeroMean halfGeometricP)) := hclosed.closure_eq.symm
      _ = closure (Set.range compressedDenseMap) := rfl
      _ = Set.univ := hdense
  apply denseQ_not_mem_compressedDenseMap_range
  have hq : denseQ ∈ (Set.univ :
      Set ↥(L2ZeroMean halfGeometricP)) := trivial
  rw [← hrange] at hq
  exact hq

private lemma compressedDenseMap_isEssBounded
    (f : ↥(L2ZeroMean halfGeometricP)) :
    IsEssBoundedMixtureScore (compressedDenseMap f) := by
  let a : ℕ → ℝ := fun n =>
    (halfGeometricP {n}).toReal *
      ‖(((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2‖
  let S : ℝ := ∑' n, a n
  let c : ℝ := integralL2 halfGeometricP
    (multiplyDenseCLM (f : Lp ℝ 2 halfGeometricP))
  have hfint : Integrable
      (fun n : ℕ => (((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2)
      halfGeometricP := by
    exact (Lp.memLp (f : Lp ℝ 2 halfGeometricP)).integrable_sq
  have hsum : Summable a := by
    exact summable_singleton_norm_of_integrable hfint
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n =>
    mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  have hterm : ∀ n : ℕ,
      a n = (denseMultiplier n *
        ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2 / 2 := by
    intro n
    dsimp only [a]
    rw [halfGeometricP_singleton,
      ENNReal.toReal_ofReal (by positivity),
      Real.norm_of_nonneg (sq_nonneg _), pow_succ,
      ← denseMultiplier_sq]
    ring
  refine ⟨Real.sqrt (2 * S) + |c|, Filter.Eventually.of_forall (fun n => ?_)⟩
  rw [compressedDenseMap_apply_everywhere]
  change |denseMultiplier n *
      ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n - c| ≤ _
  have hle : a n ≤ S := hsum.le_tsum n (fun i _ => ha_nonneg i)
  have hsq : (denseMultiplier n *
      ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) ^ 2 ≤ 2 * S := by
    rw [hterm n] at hle
    linarith
  calc
    |denseMultiplier n *
        ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n - c| ≤
        |denseMultiplier n *
          ((f : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n| + |c| := abs_sub _ _
    _ ≤ Real.sqrt (2 * S) + |c| :=
      by simpa [add_comm] using add_le_add_right (Real.abs_le_sqrt hsq) |c|

private noncomputable def denseChart
    (f : ↥(L2ZeroMean halfGeometricP)) : Measure ℕ :=
  halfGeometricP.withDensity (fun n => ENNReal.ofReal
    (1 + (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n))

private def DenseChartGood (f : ↥(L2ZeroMean halfGeometricP)) : Prop :=
  ∀ᵐ n ∂halfGeometricP,
    0 < 1 + (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n

private lemma denseChart_injective_on_good
    {f g : ↥(L2ZeroMean halfGeometricP)}
    (hf : DenseChartGood f) (hg : DenseChartGood g)
    (hfg : denseChart f = denseChart g) : f = g := by
  have hmeas (z : ↥(L2ZeroMean halfGeometricP)) :
      AEMeasurable (fun n => ENNReal.ofReal
        (1 + (((compressedDenseMap z : ↥(L2ZeroMean halfGeometricP)) :
          Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n)) halfGeometricP := by
    exact ((aemeasurable_const.add
      (Lp.aestronglyMeasurable
        (compressedDenseMap z : Lp ℝ 2 halfGeometricP)).aemeasurable)).ennreal_ofReal
  have hfrn := Measure.rnDeriv_withDensity₀ halfGeometricP (hmeas f)
  have hgrn := Measure.rnDeriv_withDensity₀ halfGeometricP (hmeas g)
  change (denseChart f).rnDeriv halfGeometricP =ᵐ[halfGeometricP] _ at hfrn
  change (denseChart g).rnDeriv halfGeometricP =ᵐ[halfGeometricP] _ at hgrn
  rw [hfg] at hfrn
  have hdensity := hfrn.symm.trans hgrn
  apply compressedDenseMap_injective
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hdensity, hf, hg] with n hn hfn hgn
  have := ENNReal.ofReal_eq_ofReal_iff hfn.le hgn.le |>.mp hn
  linarith

private noncomputable def densePsi (Q : Measure ℕ) : ℝ := by
  classical
  exact
  if h : ∃ f : ↥(L2ZeroMean halfGeometricP),
      DenseChartGood f ∧ Q = denseChart f then
    ⟪denseQ, Classical.choose h⟫_ℝ
  else 0

private lemma densePsi_denseChart
    (f : ↥(L2ZeroMean halfGeometricP)) (hf : DenseChartGood f) :
    densePsi (denseChart f) = ⟪denseQ, f⟫_ℝ := by
  let hrep : ∃ g : ↥(L2ZeroMean halfGeometricP),
      DenseChartGood g ∧ denseChart f = denseChart g := ⟨f, hf, rfl⟩
  rw [densePsi, dif_pos hrep]
  have hchosen := Classical.choose_spec hrep
  have huniq : Classical.choose hrep = f :=
    (denseChart_injective_on_good hchosen.1 hf hchosen.2.symm)
  exact congrArg (fun z => ⟪denseQ, z⟫_ℝ) huniq

private lemma denseChartGood_smul
    (f : ↥(L2ZeroMean halfGeometricP))
    (hf : IsEssBoundedMixtureScore (compressedDenseMap f))
    {t : ℝ} (ht : |t| < boundedDensityPath_truncRadius hf) :
    DenseChartGood (t • f) := by
  have hbound := hf.essBound_spec
  have hcoe := Lp.coeFn_smul t
    (compressedDenseMap f : Lp ℝ 2 halfGeometricP)
  have hmap : compressedDenseMap (t • f) = t • compressedDenseMap f :=
    map_smul compressedDenseMap t f
  filter_upwards [hbound, hcoe] with n hn hsmul
  rw [hmap]
  change 0 < 1 +
    (((t • (compressedDenseMap f : Lp ℝ 2 halfGeometricP) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n)
  rw [hsmul, Pi.smul_apply, smul_eq_mul]
  have hM_nn : 0 ≤ hf.essBound := hf.essBound_nonneg
  have h_abs_le : |t *
      (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
        Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n| ≤ |t| * hf.essBound := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)
  have h_tM_le : |t| * hf.essBound ≤
      boundedDensityPath_truncRadius hf * hf.essBound :=
    mul_le_mul_of_nonneg_right ht.le hM_nn
  have h_delta : boundedDensityPath_truncRadius hf * hf.essBound < 1 := by
    unfold boundedDensityPath_truncRadius
    rw [show (1 : ℝ) / (hf.essBound + 1) * hf.essBound =
      hf.essBound / (hf.essBound + 1) by ring]
    rw [div_lt_one (by linarith : (0 : ℝ) < hf.essBound + 1)]
    linarith
  have habs : |t *
      (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
        Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n| < 1 :=
    lt_of_le_of_lt (h_abs_le.trans h_tM_le) h_delta
  linarith [neg_abs_le (t *
    (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
      Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n)]

private lemma boundedDensityPath_curve_eq_denseChart
    (f : ↥(L2ZeroMean halfGeometricP))
    (hf : IsEssBoundedMixtureScore (compressedDenseMap f))
    {t : ℝ} (ht : |t| < boundedDensityPath_truncRadius hf) :
    (boundedDensityPath (compressedDenseMap f) hf).curve t =
      denseChart (t • f) := by
  rw [boundedDensityPath_curve_eq_withDensity _ hf ht]
  unfold denseChart
  apply MeasureTheory.withDensity_congr_ae
  have hmap : compressedDenseMap (t • f) = t • compressedDenseMap f :=
    map_smul compressedDenseMap t f
  rw [hmap]
  filter_upwards [Lp.coeFn_smul t
    (compressedDenseMap f : Lp ℝ 2 halfGeometricP)] with n hn
  change ENNReal.ofReal (1 + t *
      (((compressedDenseMap f : ↥(L2ZeroMean halfGeometricP)) :
        Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n) =
    ENNReal.ofReal (1 +
      (((t • (compressedDenseMap f : Lp ℝ 2 halfGeometricP) :
        Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n))
  rw [hn, Pi.smul_apply, smul_eq_mul]

private lemma denseChart_zero : denseChart 0 = halfGeometricP := by
  unfold denseChart
  have hden : (fun n : ℕ => ENNReal.ofReal
      (1 + (((compressedDenseMap (0 : ↥(L2ZeroMean halfGeometricP)) :
        ↥(L2ZeroMean halfGeometricP)) : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n))
      =ᵐ[halfGeometricP] fun _ => (1 : ℝ≥0∞) := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞))
      (μ := halfGeometricP)] with n hn
    rw [map_zero]
    change ENNReal.ofReal (1 +
      (((0 : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n)) = 1
    rw [hn, Pi.zero_apply, add_zero, ENNReal.ofReal_one]
  rw [MeasureTheory.withDensity_congr_ae hden]
  exact MeasureTheory.withDensity_one

private lemma denseChartGood_zero :
    DenseChartGood (0 : ↥(L2ZeroMean halfGeometricP)) := by
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞))
    (μ := halfGeometricP)] with n hn
  rw [map_zero]
  change 0 < 1 + (((0 : Lp ℝ 2 halfGeometricP) : ℕ → ℝ) n)
  rw [hn]
  norm_num

private lemma densePsi_halfGeometricP : densePsi halfGeometricP = 0 := by
  rw [← denseChart_zero, densePsi_denseChart 0 denseChartGood_zero]
  simp

/-- One dependent witness bundles the concrete probability law, its actual
`L2ZeroMean P` score operator, the dense nonclosed adjoint obstruction, and
the normalized-square-tilt derivative paths for the same `A`, `q`, and `ψ`.

The construction uses the half-geometric law on `ℕ`, compressed multiplier
`m(n)=2^{-n/2}`, bounded mean-zero `q` outside the multiplier range, and
normalized square tilts. -/
structure DenseRangeScoreWitness where
  P : Measure ℕ
  hP : IsProbabilityMeasure P
  geometric_fullSupport : IsHalfGeometricFullSupport P
  hcomplete : CompleteSpace ↥(L2ZeroMean P)
  A : @ScoreOperator ℕ inferInstance ↥(L2ZeroMean P) inferInstance
    inferInstance hcomplete P hP
  Amap : ↥(L2ZeroMean P) →L[ℝ] ↥(L2ZeroMean P)
  Amap_eq : Amap = @ScoreOperator.toCLM ℕ inferInstance ↥(L2ZeroMean P)
    inferInstance inferInstance hcomplete P hP A
  Astar : ↥(L2ZeroMean P) →L[ℝ] ↥(L2ZeroMean P)
  q : ↥(L2ZeroMean P)
  adjoint_identity : ∀ v y, ⟪Astar y, v⟫_ℝ = ⟪y, Amap v⟫_ℝ
  dense_range : DenseRange Amap
  range_not_closed : ¬ IsClosed (Amap.range : Set ↥(L2ZeroMean P))
  q_not_mem_adjoint_range : q ∉ Astar.range
  ψ : Measure ℕ → ℝ
  paths : @ScorePathDerivativeData ℕ inferInstance P hP
    ↥(L2ZeroMean P) inferInstance inferInstance hcomplete A q ψ

/-- The half-geometric compressed-multiplier construction
jointly satisfies every field of `DenseRangeScoreWitness`. -/
theorem exists_denseRangeScoreWitness :
    Nonempty DenseRangeScoreWitness := by
  let Amap : ↥(L2ZeroMean halfGeometricP) →L[ℝ]
      ↥(L2ZeroMean halfGeometricP) := compressedDenseMap
  let A : @ScoreOperator ℕ inferInstance ↥(L2ZeroMean halfGeometricP)
      inferInstance inferInstance halfGeometricL2ZeroMean_complete
      halfGeometricP halfGeometricP_isProbability :=
    @ScoreOperator.mk ℕ inferInstance ↥(L2ZeroMean halfGeometricP)
      inferInstance inferInstance halfGeometricL2ZeroMean_complete
      halfGeometricP halfGeometricP_isProbability Amap
  letI : CompleteSpace ↥(L2ZeroMean halfGeometricP) :=
    (L2ZeroMean_isClosed halfGeometricP).isComplete.completeSpace_coe
  let hg : ∀ f : ↥(L2ZeroMean halfGeometricP),
      IsEssBoundedMixtureScore (Amap f) :=
    fun f => compressedDenseMap_isEssBounded f
  let hpaths : ∀ f : ↥(L2ZeroMean halfGeometricP),
      QMDPath halfGeometricP :=
    fun f => boundedDensityPath (Amap f) (hg f)
  have hscore : ∀ f : ↥(L2ZeroMean halfGeometricP),
      (hpaths f).score = Amap f := fun f => by
    exact boundedDensityPath_score (Amap f) (hg f)
  have hderiv : ∀ f : ↥(L2ZeroMean halfGeometricP),
      Tendsto (fun t : ℝ =>
        (densePsi ((hpaths f).curve t) - densePsi halfGeometricP) / t)
        (𝓝[≠] 0) (𝓝 ⟪denseQ, f⟫_ℝ) := fun f => by
    have hevent : ∀ᶠ t : ℝ in 𝓝[≠] 0,
        |t| < boundedDensityPath_truncRadius (hg f) := by
      have hpos := boundedDensityPath_truncRadius_pos (hg f)
      have hnhds : Set.Ioo
          (-boundedDensityPath_truncRadius (hg f))
          (boundedDensityPath_truncRadius (hg f)) ∈ 𝓝 (0 : ℝ) :=
        Ioo_mem_nhds (by linarith) hpos
      have hwithin : Set.Ioo
          (-boundedDensityPath_truncRadius (hg f))
          (boundedDensityPath_truncRadius (hg f)) ∈ 𝓝[≠] (0 : ℝ) :=
        Filter.mem_inf_iff.mpr
          ⟨Set.Ioo (-boundedDensityPath_truncRadius (hg f))
              (boundedDensityPath_truncRadius (hg f)), hnhds,
            Set.univ, Filter.univ_mem, by simp⟩
      filter_upwards [hwithin] with t ht
      exact abs_lt.mpr ht
    have heq : (fun t : ℝ =>
        (densePsi ((hpaths f).curve t) - densePsi halfGeometricP) / t)
        =ᶠ[𝓝[≠] 0] fun _ => ⟪denseQ, f⟫_ℝ := by
      filter_upwards [hevent, self_mem_nhdsWithin] with t ht ht0
      change (densePsi ((boundedDensityPath (Amap f) (hg f)).curve t) -
        densePsi halfGeometricP) / t = ⟪denseQ, f⟫_ℝ
      rw [boundedDensityPath_curve_eq_denseChart f (hg f) ht,
        densePsi_denseChart (t • f) (denseChartGood_smul f (hg f) ht),
        densePsi_halfGeometricP, sub_zero]
      have hinter : ⟪denseQ, t • f⟫_ℝ = t * ⟪denseQ, f⟫_ℝ := by
        simpa using (inner_smul_right (𝕜 := ℝ) denseQ f t)
      rw [hinter]
      change (t * ⟪denseQ, f⟫_ℝ) / t = ⟪denseQ, f⟫_ℝ
      exact mul_div_cancel_left₀ _ ht0
    exact tendsto_congr' heq |>.mpr tendsto_const_nhds
  let paths : @ScorePathDerivativeData ℕ inferInstance halfGeometricP
      halfGeometricP_isProbability ↥(L2ZeroMean halfGeometricP)
      inferInstance inferInstance this
      A denseQ densePsi :=
    @ScorePathDerivativeData.mk ℕ inferInstance halfGeometricP
      halfGeometricP_isProbability ↥(L2ZeroMean halfGeometricP)
      inferInstance inferInstance this A denseQ densePsi
      hpaths (fun f => by change (hpaths f).score = Amap f; exact hscore f) hderiv
  exact ⟨
    { P := halfGeometricP
      hP := halfGeometricP_isProbability
      geometric_fullSupport := halfGeometricP_fullSupport
      hcomplete := halfGeometricL2ZeroMean_complete
      A := A
      Amap := Amap
      Amap_eq := by rfl
      Astar := Amap
      q := denseQ
      adjoint_identity := fun v y => by
        change ⟪compressedDenseMap y, v⟫_ℝ =
          ⟪y, compressedDenseMap v⟫_ℝ
        exact compressedDenseMap_symmetric y v
      dense_range := compressedDenseMap_denseRange
      range_not_closed := compressedDenseMap_range_not_closed
      q_not_mem_adjoint_range := denseQ_not_mem_compressedDenseMap_range
      ψ := densePsi
      paths := paths }⟩

/-- The concrete baseline law for the separate raw-regularity witness. -/
noncomputable def standardGaussian : Measure ℝ :=
  gaussianReal 0 1

private noncomputable instance standardGaussian_isProbability :
    IsProbabilityMeasure standardGaussian := by
  unfold standardGaussian
  infer_instance

private noncomputable def gaussianLocationScore : ↥(L2ZeroMean standardGaussian) :=
  CandidateIF.toL2ZeroMean
    { raw := id
      memLp2 := by
        unfold standardGaussian
        exact ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num)
      mean_zero := by
        unfold standardGaussian
        simp }

private lemma gaussianLocationScore_coe :
    (((gaussianLocationScore : ↥(L2ZeroMean standardGaussian)) :
      Lp ℝ 2 standardGaussian) : ℝ → ℝ) =ᵐ[standardGaussian] id := by
  exact CandidateIF.coeFn_toL2ZeroMean _

private lemma gaussianLocationScore_smul_coe (b : ℝ) :
    ((((b • gaussianLocationScore : ↥(L2ZeroMean standardGaussian)) :
      Lp ℝ 2 standardGaussian) : ℝ → ℝ)) =ᵐ[standardGaussian]
      fun x => b * x := by
  have hsmul := Lp.coeFn_smul b
    (gaussianLocationScore : Lp ℝ 2 standardGaussian)
  filter_upwards [hsmul, gaussianLocationScore_coe] with x hx hs
  change (((b • (gaussianLocationScore : Lp ℝ 2 standardGaussian) :
    Lp ℝ 2 standardGaussian) : ℝ → ℝ) x) = b * x
  rw [hx, Pi.smul_apply, smul_eq_mul, hs]
  rfl

private lemma integral_gaussian_exp_tilt (a : ℝ) :
    ∫ x, Real.exp (a * x - a ^ 2 / 2) ∂standardGaussian = 1 := by
  unfold standardGaussian
  rw [show (fun x : ℝ => Real.exp (a * x - a ^ 2 / 2)) =
      fun x => Real.exp (-a ^ 2 / 2) * Real.exp (a * x) by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [integral_const_mul,
    ProbabilityTheory.integral_exp_mul_gaussianReal 0 1 a]
  simp only [NNReal.coe_one, zero_mul, one_mul, zero_add]
  rw [← Real.exp_add]
  ring_nf
  exact Real.exp_zero

private lemma integral_id_mul_gaussian_exp_tilt (a : ℝ) :
    ∫ x, x * Real.exp (a * x - a ^ 2 / 2) ∂standardGaussian = a := by
  let w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp (a * x - a ^ 2 / 2))
  have hw_meas : Measurable w := by fun_prop
  have hw_top : ∀ᵐ x ∂standardGaussian, w x < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  calc
    (∫ x, x * Real.exp (a * x - a ^ 2 / 2) ∂standardGaussian) =
        ∫ x, x ∂standardGaussian.withDensity w := by
      rw [integral_withDensity_eq_integral_toReal_smul hw_meas hw_top]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp only [w]
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
      ring
    _ = ∫ x, x ∂gaussianReal a ⟨1, zero_le_one⟩ := by
      rw [show standardGaussian.withDensity w =
          gaussianReal a ⟨1, zero_le_one⟩ by
        simpa [standardGaussian, w] using!
          ProbabilityTheory.gaussianReal_withDensity_exp_shift a]
    _ = a := ProbabilityTheory.integral_id_gaussianReal

private noncomputable def gaussianSqrtDensity (a x : ℝ) : ℝ :=
  Real.exp (a * x / 2 - a ^ 2 / 4)

private lemma integral_gaussianSqrtDensity (a : ℝ) :
    ∫ x, gaussianSqrtDensity a x ∂standardGaussian =
      Real.exp (-a ^ 2 / 8) := by
  unfold gaussianSqrtDensity standardGaussian
  rw [show (fun x : ℝ => Real.exp (a * x / 2 - a ^ 2 / 4)) =
      fun x => Real.exp (-a ^ 2 / 4) * Real.exp ((a / 2) * x) by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [integral_const_mul,
    ProbabilityTheory.integral_exp_mul_gaussianReal 0 1 (a / 2)]
  simp only [NNReal.coe_one, zero_mul, one_mul, zero_add]
  rw [← Real.exp_add]
  congr 1
  ring

private lemma integral_gaussianSqrtDensity_sq (a : ℝ) :
    ∫ x, gaussianSqrtDensity a x ^ 2 ∂standardGaussian = 1 := by
  rw [show (fun x : ℝ => gaussianSqrtDensity a x ^ 2) =
      fun x => Real.exp (a * x - a ^ 2 / 2) by
    funext x
    unfold gaussianSqrtDensity
    rw [← Real.exp_nat_mul]
    norm_num
    ring]
  exact integral_gaussian_exp_tilt a

private lemma integral_id_mul_gaussianSqrtDensity (a : ℝ) :
    ∫ x, x * gaussianSqrtDensity a x ∂standardGaussian =
      (a / 2) * Real.exp (-a ^ 2 / 8) := by
  rw [show (fun x : ℝ => x * gaussianSqrtDensity a x) =
      fun x => Real.exp (-a ^ 2 / 8) *
        (x * Real.exp ((a / 2) * x - (a / 2) ^ 2 / 2)) by
    funext x
    unfold gaussianSqrtDensity
    have hexp : a * x / 2 - a ^ 2 / 4 =
        -a ^ 2 / 8 + ((a / 2) * x - (a / 2) ^ 2 / 2) := by ring
    rw [hexp, Real.exp_add]
    ring]
  rw [integral_const_mul, integral_id_mul_gaussian_exp_tilt]
  ring

private noncomputable def gaussianQmdResidual (a x : ℝ) : ℝ :=
  gaussianSqrtDensity a x - 1 - (a / 2) * x

private lemma gaussianSqrtDensity_memLp (a : ℝ) :
    MemLp (gaussianSqrtDensity a) 2 standardGaussian := by
  rw [memLp_two_iff_integrable_sq (by
    unfold gaussianSqrtDensity
    fun_prop)]
  rw [show (fun x : ℝ => gaussianSqrtDensity a x ^ 2) =
      fun x => Real.exp (-a ^ 2 / 2) * Real.exp (a * x) by
    funext x
    unfold gaussianSqrtDensity
    rw [← Real.exp_nat_mul]
    have he : 2 * (a * x / 2 - a ^ 2 / 4) = -a ^ 2 / 2 + a * x := by ring
    norm_num
    rw [he, Real.exp_add]]
  unfold standardGaussian
  exact (ProbabilityTheory.integrable_exp_mul_gaussianReal a).const_mul _

private lemma gaussianQmdResidual_memLp (a : ℝ) :
    MemLp (gaussianQmdResidual a) 2 standardGaussian := by
  have hs := gaussianSqrtDensity_memLp a
  have hx : MemLp (id : ℝ → ℝ) 2 standardGaussian := by
    unfold standardGaussian
    exact ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num)
  have h := (hs.sub (memLp_const (1 : ℝ))).sub (hx.const_mul (a / 2))
  apply MemLp.ae_eq _ h
  filter_upwards with x
  rfl

private lemma integral_sq_id_standardGaussian :
    ∫ x : ℝ, x ^ 2 ∂standardGaussian = 1 := by
  have h := ProbabilityTheory.variance_fun_id_gaussianReal
    (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable] at h
  simpa [standardGaussian] using h

private lemma integral_gaussianQmdResidual_sq (a : ℝ) :
    ∫ x, gaussianQmdResidual a x ^ 2 ∂standardGaussian =
      2 + a ^ 2 / 4 - (2 + a ^ 2 / 2) * Real.exp (-a ^ 2 / 8) := by
  have hs2 := (gaussianSqrtDensity_memLp a).integrable_sq
  have hs := (gaussianSqrtDensity_memLp a).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hx2 : Integrable (fun x : ℝ => x ^ 2) standardGaussian := by
    have hx : MemLp (id : ℝ → ℝ) 2 standardGaussian := by
      unfold standardGaussian
      exact ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num)
    simpa only [id_eq] using hx.integrable_sq
  have hx : Integrable (id : ℝ → ℝ) standardGaussian := by
    unfold standardGaussian
    exact (ProbabilityTheory.memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl
  change Integrable (fun x : ℝ => x) standardGaussian at hx
  have hxs : Integrable (fun x => x * gaussianSqrtDensity a x) standardGaussian := by
    exact (by
      simpa only [id_eq] using!
        (ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num) :
          MemLp (id : ℝ → ℝ) 2 standardGaussian).integrable_mul
            (gaussianSqrtDensity_memLp a))
  have hsum1 : Integrable (fun x : ℝ => gaussianSqrtDensity a x ^ 2 + 1)
      standardGaussian := by
    simpa only [Pi.add_apply] using! hs2.add (integrable_const (1 : ℝ))
  have hsum2 : Integrable (fun x : ℝ =>
      gaussianSqrtDensity a x ^ 2 + 1 + (a ^ 2 / 4) * x ^ 2)
      standardGaussian := by
    simpa only [Pi.add_apply] using! hsum1.add (hx2.const_mul (a ^ 2 / 4))
  have hsub1 : Integrable (fun x : ℝ =>
      gaussianSqrtDensity a x ^ 2 + 1 + (a ^ 2 / 4) * x ^ 2 -
        2 * gaussianSqrtDensity a x) standardGaussian := by
    simpa only [Pi.sub_apply] using! hsum2.sub (hs.const_mul 2)
  have hsub2 : Integrable (fun x : ℝ =>
      gaussianSqrtDensity a x ^ 2 + 1 + (a ^ 2 / 4) * x ^ 2 -
        2 * gaussianSqrtDensity a x - a * (x * gaussianSqrtDensity a x))
      standardGaussian := by
    simpa only [Pi.sub_apply] using! hsub1.sub (hxs.const_mul a)
  rw [show (fun x : ℝ => gaussianQmdResidual a x ^ 2) = fun x =>
      gaussianSqrtDensity a x ^ 2 + 1 + (a ^ 2 / 4) * x ^ 2
        - 2 * gaussianSqrtDensity a x
        - a * (x * gaussianSqrtDensity a x) + a * x by
    funext x
    unfold gaussianQmdResidual
    ring]
  change ∫ x,
      (((((fun y : ℝ => gaussianSqrtDensity a y ^ 2) + fun _ => 1) +
          fun y => (a ^ 2 / 4) * y ^ 2) -
        fun y => 2 * gaussianSqrtDensity a y) -
        fun y => a * (y * gaussianSqrtDensity a y) : ℝ → ℝ) x +
        (fun y : ℝ => a * y) x ∂standardGaussian = _
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [integral_add
      hsub2
      (hx.const_mul a)]
  rw [integral_sub
      hsub1 (hxs.const_mul a)]
  rw [integral_sub
      hsum2 (hs.const_mul 2)]
  rw [integral_add hsum1
      (hx2.const_mul (a ^ 2 / 4))]
  rw [integral_add hs2 (integrable_const (1 : ℝ))]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul,
    integral_gaussianSqrtDensity_sq,
    integral_sq_id_standardGaussian, integral_gaussianSqrtDensity,
    integral_id_mul_gaussianSqrtDensity]
  rw [integral_const]
  rw [show standardGaussian.real Set.univ = 1 by
    rw [Measure.real, measure_univ]
    rfl]
  simp only [one_smul]
  rw [show (∫ x : ℝ, x ∂standardGaussian) = 0 by
    unfold standardGaussian
    exact ProbabilityTheory.integral_id_gaussianReal]
  ring

private lemma gaussianQmdIntegral_isLittleO :
    (fun a : ℝ =>
      2 + a ^ 2 / 4 - (2 + a ^ 2 / 2) * Real.exp (-a ^ 2 / 8))
      =o[𝓝 0] fun a : ℝ => a ^ 2 := by
  let u : ℝ → ℝ := fun a => -a ^ 2 / 8
  let R : ℝ → ℝ := fun a => Real.exp (u a) - 1 - u a
  have hu : Tendsto u (𝓝 0) (𝓝 0) := by
    have hcont : Continuous u := by
      dsimp only [u]
      fun_prop
    simpa [u] using hcont.tendsto 0
  have hR0 : (fun a => Real.exp (u a) - 1 - u a) =o[𝓝 0] u := by
    have hbase := (Real.exp_sub_sum_range_succ_isLittleO_pow 1).comp_tendsto hu
    apply hbase.congr (fun a => ?_) (fun _ => by simp)
    simp only [Function.comp_apply]
    have hsum : ∑ i ∈ Finset.range 2, u a ^ i / (i.factorial : ℝ) = 1 + u a := by
      norm_num [Finset.sum_range_succ]
    rw [hsum]
    ring
  have hR : R =o[𝓝 0] (fun a : ℝ => a ^ 2) := by
    have huO : u =O[𝓝 0] (fun a : ℝ => a ^ 2) := by
      apply (isBigO_const_mul_self (-(8 : ℝ)⁻¹)
        (fun a : ℝ => a ^ 2) (𝓝 0)).congr <;> intro a
      · dsimp only [u]
        ring
      · rfl
    exact (hR0.trans_isBigO huO).congr (fun a => by simp [R]) (fun _ => rfl)
  have hcoef : (fun a : ℝ => 2 + a ^ 2 / 2) =O[𝓝 0] (fun _ => (1 : ℝ)) := by
    have hc : ContinuousAt (fun a : ℝ => 2 + a ^ 2 / 2) 0 := by fun_prop
    exact hc.tendsto.isBigO_one ℝ
  have hcoefR : (fun a : ℝ => (2 + a ^ 2 / 2) * R a)
      =o[𝓝 0] (fun a : ℝ => a ^ 2) := by
    simpa only [one_mul] using hcoef.mul_isLittleO hR
  have hfour : (fun a : ℝ => a ^ 4 / 16) =o[𝓝 0] (fun a : ℝ => a ^ 2) := by
    exact (isLittleO_pow_pow (by norm_num : 2 < 4)).const_mul_left (16 : ℝ)⁻¹
      |>.congr' (by filter_upwards with a; simp [div_eq_mul_inv]; ring) EventuallyEq.rfl
  have hmain := hfour.sub hcoefR
  apply hmain.congr'
  · filter_upwards with a
    simp [R, u]
    ring
  · filter_upwards with a
    rfl

private lemma gaussianQmdNorm_rate :
    Tendsto (fun a : ℝ =>
      (eLpNorm (gaussianQmdResidual a) 2 standardGaussian).toReal / |a|)
      (𝓝[≠] 0) (𝓝 0) := by
  let I : ℝ → ℝ := fun a =>
    2 + a ^ 2 / 4 - (2 + a ^ 2 / 2) * Real.exp (-a ^ 2 / 8)
  have hratio : Tendsto (fun a : ℝ => I a / a ^ 2) (𝓝 0) (𝓝 0) := by
    exact gaussianQmdIntegral_isLittleO.tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun a : ℝ => Real.sqrt (I a / a ^ 2))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using (hratio.mono_left nhdsWithin_le_nhds).sqrt
  apply hsqrt.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hI : 0 ≤ I a := by
    dsimp only [I]
    rw [← integral_gaussianQmdResidual_sq]
    exact integral_nonneg (fun _ => sq_nonneg _)
  rw [Real.sqrt_div hI, Real.sqrt_sq_eq_abs]
  dsimp only [I]
  rw [← integral_gaussianQmdResidual_sq,
    AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
      (gaussianQmdResidual_memLp a)]

private lemma gaussianQmdENNReal_rate :
    Tendsto (fun a : ℝ =>
      eLpNorm (gaussianQmdResidual a) 2 standardGaussian / ENNReal.ofReal |a|)
      (𝓝[≠] 0) (𝓝 0) := by
  have hlift : Tendsto (fun a : ℝ => ENNReal.ofReal
      ((eLpNorm (gaussianQmdResidual a) 2 standardGaussian).toReal / |a|))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal gaussianQmdNorm_rate
  apply hlift.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [ENNReal.ofReal_div_of_pos (abs_pos.mpr ha),
    ENNReal.ofReal_toReal (gaussianQmdResidual_memLp a).2.ne]

private lemma gaussianLocationResidual_ae (b t : ℝ) :
    (fun x : ℝ =>
      Real.sqrt ((gaussianReal (t * b) 1).rnDeriv standardGaussian x).toReal -
        Real.sqrt (standardGaussian.rnDeriv standardGaussian x).toReal -
        (t / 2) *
          ((((b • gaussianLocationScore : ↥(L2ZeroMean standardGaussian)) :
            Lp ℝ 2 standardGaussian) : ℝ → ℝ) x) *
          Real.sqrt (standardGaussian.rnDeriv standardGaussian x).toReal)
      =ᵐ[standardGaussian] gaussianQmdResidual (t * b) := by
  have hrn : (gaussianReal (t * b) 1).rnDeriv standardGaussian
      =ᵐ[standardGaussian] fun x =>
        ENNReal.ofReal (Real.exp ((t * b) * x - (t * b) ^ 2 / 2)) := by
    rw [show gaussianReal (t * b) 1 = standardGaussian.withDensity
        (fun x => ENNReal.ofReal
          (Real.exp ((t * b) * x - (t * b) ^ 2 / 2))) by
      simpa [standardGaussian] using
        (ProbabilityTheory.gaussianReal_withDensity_exp_shift (t * b)).symm]
    exact Measure.rnDeriv_withDensity standardGaussian (by fun_prop)
  have hrn0 := standardGaussian.rnDeriv_self
  have hscore := gaussianLocationScore_smul_coe b
  filter_upwards [hrn, hrn0, hscore] with x hx hx0 hs
  rw [hx, hx0, ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ENNReal.toReal_one, Real.sqrt_one, hs]
  rw [← Real.exp_half]
  unfold gaussianQmdResidual gaussianSqrtDensity
  congr 1 <;> ring_nf

private noncomputable def gaussianLocationPath (b : ℝ) : QMDPath standardGaussian where
  curve t := gaussianReal (t * b) 1
  curve_at_zero := by simp [standardGaussian]
  curve_isProbability := fun _ => inferInstance
  dominating := standardGaussian
  curve_absContinuous t := by
    rw [show gaussianReal (t * b) 1 =
      standardGaussian.withDensity
        (fun x => ENNReal.ofReal (Real.exp ((t * b) * x - (t * b) ^ 2 / 2))) by
      simpa [standardGaussian] using
        (ProbabilityTheory.gaussianReal_withDensity_exp_shift (t * b)).symm]
    exact withDensity_absolutelyContinuous _ _
  dominating_sigmaFinite := inferInstance
  score := b • gaussianLocationScore
  qmd_limit := by
    have hnorm : ∀ t : ℝ,
        eLpNorm (fun x : ℝ =>
          Real.sqrt ((gaussianReal (t * b) 1).rnDeriv standardGaussian x).toReal -
            Real.sqrt (standardGaussian.rnDeriv standardGaussian x).toReal -
            (t / 2) *
              ((((b • gaussianLocationScore : ↥(L2ZeroMean standardGaussian)) :
                Lp ℝ 2 standardGaussian) : ℝ → ℝ) x) *
              Real.sqrt (standardGaussian.rnDeriv standardGaussian x).toReal)
          2 standardGaussian =
        eLpNorm (gaussianQmdResidual (t * b)) 2 standardGaussian := fun t =>
      eLpNorm_congr_ae (gaussianLocationResidual_ae b t)
    have hnorm' : ∀ t : ℝ,
        eLpNorm (fun x : ℝ =>
          Real.sqrt ((gaussianReal (t * b) 1).rnDeriv standardGaussian x).toReal -
            Real.sqrt ((gaussianReal (0 * b) 1).rnDeriv standardGaussian x).toReal -
            (t / 2) *
              ((((b • gaussianLocationScore : ↥(L2ZeroMean standardGaussian)) :
                Lp ℝ 2 standardGaussian) : ℝ → ℝ) x) *
              Real.sqrt ((gaussianReal (0 * b) 1).rnDeriv standardGaussian x).toReal)
          2 standardGaussian =
        eLpNorm (gaussianQmdResidual (t * b)) 2 standardGaussian := by
      intro t
      simpa [standardGaussian] using hnorm t
    by_cases hb : b = 0
    · subst b
      simp_rw [hnorm']
      have hres : gaussianQmdResidual 0 = 0 := by
        funext x
        simp [gaussianQmdResidual, gaussianSqrtDensity]
      simp only [mul_zero]
      rw [hres]
      simpa only [eLpNorm_zero, ENNReal.zero_div] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞))
            (𝓝[≠] 0) (𝓝 0))
    · have hmap : Tendsto (fun t : ℝ => t * b) (𝓝[≠] 0) (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have hc : Tendsto (fun t : ℝ => t * b) (𝓝 0) (𝓝 0) := by
            have hcont : Continuous (fun t : ℝ => t * b) := by fun_prop
            simpa using hcont.tendsto 0
          exact hc.mono_left inf_le_left
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact mul_ne_zero ht hb
      have hbase := gaussianQmdENNReal_rate.comp hmap
      have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |b|) hbase
        (Or.inr ENNReal.ofReal_ne_top)
      have hmul0 : Tendsto (fun t : ℝ => ENNReal.ofReal |b| *
          (eLpNorm (gaussianQmdResidual (t * b)) 2 standardGaussian /
            ENNReal.ofReal |t * b|)) (𝓝[≠] 0) (𝓝 0) := by
        simpa only [Function.comp_apply, mul_zero] using hmul
      apply hmul0.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hnorm', abs_mul, ENNReal.ofReal_mul (abs_nonneg t),
        ← mul_div_assoc]
      rw [mul_comm (ENNReal.ofReal |t|) (ENNReal.ofReal |b|)]
      exact ENNReal.mul_div_mul_left _ _
        (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hb)) ENNReal.ofReal_ne_top

private lemma gaussian_sum_law (n : ℕ) (μ : ℝ) :
    (Measure.pi (fun _ : Fin n => gaussianReal μ 1)).map
        (fun X => ∑ i, X i) = gaussianReal (n * μ) n := by
  letI : IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin n => gaussianReal μ 1)).map
        (fun X => ∑ i, X i)) :=
    Measure.isProbabilityMeasure_map (by fun_prop :
      AEMeasurable (fun X : Fin n → ℝ => ∑ i, X i)
        (Measure.pi (fun _ : Fin n => gaussianReal μ 1)))
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_sum_pi_eq_prod]
  rw [Finset.prod_apply]
  change (∏ _ : Fin n, charFun (gaussianReal μ 1) t) = _
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, charFun_gaussianReal,
    ← Complex.exp_nat_mul]
  rw [charFun_gaussianReal]
  congr 1
  push_cast
  ring

private lemma gaussian_standardized_sample_mean_law
    (n : ℕ) (μ : ℝ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => gaussianReal μ 1)).map
        (fun X => Real.sqrt n * ((∑ i, X i) / n - μ)) = standardGaussian := by
  have hsum := gaussian_sum_law n μ
  have hsum_meas : Measurable (fun X : Fin n → ℝ => ∑ i, X i) := by fun_prop
  have haff_meas : Measurable (fun s : ℝ => Real.sqrt n * (s / n - μ)) := by fun_prop
  rw [show (Measure.pi (fun _ : Fin n => gaussianReal μ 1)).map
      (fun X => Real.sqrt n * ((∑ i, X i) / n - μ)) =
      ((Measure.pi (fun _ : Fin n => gaussianReal μ 1)).map
        (fun X => ∑ i, X i)).map
          (fun s => Real.sqrt n * (s / n - μ)) by
    rw [Measure.map_map haff_meas hsum_meas]
    rfl, hsum]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsqrt : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  rw [show (fun s : ℝ => Real.sqrt n * (s / n - μ)) =
      fun s => (Real.sqrt n / n) * (s - n * μ) by
    funext s
    field_simp]
  rw [show (gaussianReal (n * μ) n).map
      (fun s => (Real.sqrt n / n) * (s - n * μ)) =
      ((gaussianReal (n * μ) n).map (fun s => s - n * μ)).map
        (fun x => (Real.sqrt n / n) * x) by
    rw [Measure.map_map
      (by fun_prop : Measurable fun x : ℝ => (Real.sqrt n / n) * x)
      (by fun_prop : Measurable fun s : ℝ => s - n * μ)]
    rfl,
    gaussianReal_map_sub_const, sub_self,
    gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  change (Real.sqrt n / n) ^ 2 * n = 1
  field_simp [hnR]
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Formal satisfiability bundle for raw regularity: the standard Gaussian
location family, its location score, the identity parameter, and the sample
mean have common local limit `N(0,1)`.  This is deliberately separate from
the dense-range obstruction witness. -/
structure RawRegularityWitness where
  hP : IsProbabilityMeasure standardGaussian
  hcomplete : CompleteSpace ↥(L2ZeroMean standardGaussian)
  A : @ScoreOperator ℝ inferInstance ℝ inferInstance inferInstance
    inferInstance standardGaussian hP
  chi : ℝ
  psi : Measure ℝ → ℝ
  paths : @ScorePathDerivativeData ℝ inferInstance standardGaussian hP ℝ
    inferInstance inferInstance inferInstance A chi psi
  gaussian_location_path : ∀ b t,
    (paths.selectedPath b).curve t = gaussianReal (t * b) ⟨1, zero_le_one⟩
  psi_on_location : ∀ θ : ℝ, psi (gaussianReal θ ⟨1, zero_le_one⟩) = θ
  T_n : ∀ n, (Fin n → ℝ) → ℝ
  sample_mean : ∀ n X, T_n n X =
    if n = 0 then 0 else (∑ i, X i) / n
  raw : @RawRegularity ℝ inferInstance standardGaussian hP ℝ
    inferInstance inferInstance inferInstance A chi psi paths T_n
  limit_is_standardGaussian : raw.limitLaw = standardGaussian

/-- The one-dimensional Gaussian location/sample-mean model formally
discharges satisfiability of the raw regularity predicate. -/
theorem exists_rawRegularityWitness :
    Nonempty RawRegularityWitness := by
  letI : IsClosed (L2ZeroMean standardGaussian : Set (Lp ℝ 2 standardGaussian)) :=
    L2ZeroMean_isClosed standardGaussian
  letI : CompleteSpace ↥(L2ZeroMean standardGaussian) := inferInstance
  let Amap : ℝ →L[ℝ] ↥(L2ZeroMean standardGaussian) :=
    ContinuousLinearMap.toSpanSingleton ℝ gaussianLocationScore
  let A : ScoreOperator ℝ standardGaussian := ⟨Amap⟩
  let ψ : Measure ℝ → ℝ := fun Q => ∫ x, x ∂Q
  let paths : ScorePathDerivativeData A (1 : ℝ) ψ :=
    { selectedPath := gaussianLocationPath
      score_eq := fun b => by
        change b • gaussianLocationScore = Amap b
        simp [Amap, ContinuousLinearMap.toSpanSingleton_apply]
      derivative_quotient := fun b => by
        have hloc : ∀ t : ℝ,
            ψ ((gaussianLocationPath b).curve t) = t * b := by
          intro t
          change (∫ x, x ∂gaussianReal (t * b) 1) = t * b
          exact ProbabilityTheory.integral_id_gaussianReal
        have hzero : ψ standardGaussian = 0 := by
          change (∫ x, x ∂standardGaussian) = 0
          unfold standardGaussian
          exact ProbabilityTheory.integral_id_gaussianReal
        have heq : (fun t : ℝ =>
            (ψ ((gaussianLocationPath b).curve t) - ψ standardGaussian) / t) =ᶠ[𝓝[≠] 0]
            fun _ => b := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          rw [hloc, hzero, sub_zero]
          exact mul_div_cancel_left₀ b ht
        have hb : ⟪(1 : ℝ), b⟫_ℝ = b := by
          change b * 1 = b
          ring
        rw [hb]
        apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => b) (𝓝[≠] 0) (𝓝 b)).congr'
        filter_upwards [heq] with t ht
        simpa using ht.symm }
  let T_n : ∀ n, (Fin n → ℝ) → ℝ := fun n X =>
    if n = 0 then 0 else (∑ i, X i) / n
  have hψloc : ∀ θ : ℝ, ψ (gaussianReal θ 1) = θ := fun θ => by
    change (∫ x, x ∂gaussianReal θ 1) = θ
    exact ProbabilityTheory.integral_id_gaussianReal
  have hmap (b : ℝ) (n : ℕ) (hn : 0 < n) :
      (Measure.pi (fun _ : Fin n =>
        (paths.selectedPath b).curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → ℝ => Real.sqrt n *
            (T_n n X - ψ ((paths.selectedPath b).curve ((Real.sqrt n)⁻¹)))) =
        standardGaussian := by
    have hlaw := gaussian_standardized_sample_mean_law n
      ((Real.sqrt n)⁻¹ * b) hn
    rw [show (fun _ : Fin n =>
        (paths.selectedPath b).curve ((Real.sqrt n)⁻¹)) =
        fun _ => gaussianReal ((Real.sqrt n)⁻¹ * b) 1 by
      funext i
      rfl]
    rw [show (fun X : Fin n → ℝ => Real.sqrt n *
          (T_n n X - ψ ((paths.selectedPath b).curve ((Real.sqrt n)⁻¹)))) =
        (fun X : Fin n → ℝ => Real.sqrt n *
          ((∑ i, X i) / n - (Real.sqrt n)⁻¹ * b)) by
      funext X
      rw [show T_n n X = (∑ i, X i) / n by simp [T_n, hn.ne']]
      rw [show ψ ((paths.selectedPath b).curve ((Real.sqrt n)⁻¹)) =
          (Real.sqrt n)⁻¹ * b by
        change ψ (gaussianReal ((Real.sqrt n)⁻¹ * b) 1) = _
        exact hψloc _]]
    exact hlaw
  let raw : RawRegularity A (1 : ℝ) ψ paths T_n :=
    { estimator_meas := fun n => by
        by_cases hn : n = 0
        · simp [T_n, hn]
        · simp only [T_n, hn, ↓reduceIte]
          fun_prop
      limitLaw := standardGaussian
      limit_isProbability := inferInstance
      weak_limit := fun b f => by
        have hev : ∀ᶠ n : ℕ in atTop, 0 < n :=
          (eventually_ge_atTop 1).mono (fun n hn => lt_of_lt_of_le Nat.zero_lt_one hn)
        apply tendsto_congr' ?_ |>.mpr tendsto_const_nhds
        filter_upwards [hev] with n hn
        rw [hmap b n hn] }
  exact ⟨
    { hP := standardGaussian_isProbability
      hcomplete := inferInstance
      A := A
      chi := 1
      psi := ψ
      paths := paths
      gaussian_location_path := fun _ _ => rfl
      psi_on_location := fun θ => by simpa using! hψloc θ
      T_n := T_n
      sample_mean := fun _ _ => rfl
      raw := raw
      limit_is_standardGaussian := rfl }⟩

end AsymptoticStatistics.Examples.ScoreOperatorDenseRange
