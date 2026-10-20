module
public import StatLean.TimeSeries.ForMathlib.Fourier.HerglotzBochner
public import StatLean.TimeSeries.Process.Autocovariance
public import StatLean.TimeSeries.Models.WhiteNoise

@[expose] public section

/-!
# The spectral distribution of a stationary process (FY §2.3.1–§2.3.2, Theorem 2.10)

**FY Theorem 2.10 (Wiener–Khintchine), process form**: every weakly stationary process
has a unique spectral measure — a negation-invariant finite measure `F` on
`AddCircle (2π)` whose Fourier coefficients are the autocovariances,
`γ(k) = ∫ e^{ikλ} dF(λ)` (FY eq. (2.35), unnormalized form eq. (2.37)). Existence
combines the batch-A Herglotz theorem with the ACVF's evenness and positive
semidefiniteness (FY Theorem 2.7, necessity); uniqueness is
`ext_of_measureFourierCoeff`. The book's `[−π, π]`-with-endpoint conventions are the
circle picture (batch-A design decision D7); `F(π) = γ(0)` is the mass identity.

(FY §2.3.1's periodic-process examples are instances of the correspondence — the
random-phase process of `Stationarity/Gaussian.lean` realizes an arbitrary spectral
measure — and are not separately formalized.)

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.1
(pp. 49–51, eqs. (2.30)–(2.34)) and §2.3.2 Theorem 2.10 (p. 51) with §2.7.4.
(`FY §2.3.2 Thm 2.10`.)

**Proof formalization notes.** Uniqueness is not claimed in FY (inventory flag); it is
supplied here so "the spectral measure" is meaningful. The mass identity is the `k = 0`
coefficient (`measureFourierCoeff_zero`).

**Bibliographic comments.** N. Wiener, *Generalized harmonic analysis* (1930);
A. Ya. Khinchin (1934); H. Wold (1938); G. Herglotz (1911) for the underlying moment
theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `F` is **a spectral measure** of the process `X` (FY eqs. (2.35)/(2.37)): a
negation-invariant finite measure on the circle whose Fourier coefficients are the
autocovariances. -/
def IsSpectralMeasure (X : ℤ → Ω → ℝ) (μ : Measure Ω)
    (F : Measure (AddCircle (2 * π))) : Prop :=
  IsFiniteMeasure F ∧ NegInvariant F ∧
    ∀ k : ℤ, measureFourierCoeff F k = (acvf X μ k : ℂ)

/-- **FY Theorem 2.10, existence (process form)**: every weakly stationary process has a
spectral measure. -/
theorem exists_isSpectralMeasure [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) :
    ∃ F : Measure (AddCircle (2 * π)), IsSpectralMeasure X μ F := by
  obtain ⟨F, hfin, hneg, hcoef⟩ :=
    exists_measure_of_isPosSemidefSeq (acvf X μ) hstat.acvf_even hstat.acvf_posSemidef
  exact ⟨F, hfin, hneg, hcoef⟩

/-- **Uniqueness of the spectral measure** (supplied on top of FY): two spectral
measures of the same process coincide. -/
theorem IsSpectralMeasure.unique {X : ℤ → Ω → ℝ}
    {F G : Measure (AddCircle (2 * π))}
    (hF : IsSpectralMeasure X μ F) (hG : IsSpectralMeasure X μ G) : F = G := by
  obtain ⟨hFfin, -, hFc⟩ := hF
  obtain ⟨hGfin, -, hGc⟩ := hG
  haveI := hFfin
  haveI := hGfin
  exact ext_of_measureFourierCoeff F G fun n => by rw [hFc n, hGc n]

/-- The **mass identity** `F(circle) = γ(0)` (FY: `G(π) = γ(0) = Var X_t`). -/
theorem IsSpectralMeasure.mass {X : ℤ → Ω → ℝ} {F : Measure (AddCircle (2 * π))}
    (hF : IsSpectralMeasure X μ F) :
    F Set.univ = ENNReal.ofReal (acvf X μ 0) := by
  obtain ⟨hFfin, -, hFc⟩ := hF
  haveI := hFfin
  have h := hFc 0
  rw [measureFourierCoeff_zero] at h
  have hre : (F Set.univ).toReal = acvf X μ 0 := by exact_mod_cast h
  rw [← hre, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- `measureFourierCoeff` is scalar-linear in the measure. -/
private lemma measureFourierCoeff_smul' (c : ENNReal) (F : Measure (AddCircle (2 * π)))
    (j : ℤ) :
    measureFourierCoeff (c • F) j = ((c.toReal : ℝ) : ℂ) * measureFourierCoeff F j := by
  rw [measureFourierCoeff, measureFourierCoeff, integral_smul_measure]
  exact Complex.real_smul

/-- Orthogonality against normalized Haar: `∫ e^{ikλ} d(haar) = δ_{k0}`. -/
private lemma measureFourierCoeff_haarAddCircle (k : ℤ) :
    measureFourierCoeff (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) k
      = if k = 0 then (1 : ℂ) else 0 := by
  rw [measureFourierCoeff]
  rcases eq_or_ne k 0 with rfl | hk
  · have h1 : ∀ z : AddCircle (2 * π), fourier (T := 2 * π) 0 z = (1 : ℂ) := fun _ =>
      fourier_zero
    rw [if_pos rfl, integral_congr_ae (Filter.Eventually.of_forall h1), integral_const]
    simp
  · rw [if_neg hk]
    exact MeasureTheory.integral_eq_zero_of_add_right_eq_neg
      (μ := (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))))
      (g := ((2 * π / 2 / k : ℝ) : AddCircle (2 * π)))
      fun x => fourier_add_half_inv_index hk (by positivity) x

/-- Coefficients of the pushforward under negation. -/
private lemma measureFourierCoeff_map_neg' (F : Measure (AddCircle (2 * π)))
    [IsFiniteMeasure F] (m : ℤ) :
    measureFourierCoeff (F.map (fun z => -z)) m = measureFourierCoeff F (-m) := by
  rw [measureFourierCoeff, measureFourierCoeff,
    integral_map measurable_neg.aemeasurable
      ((map_continuous (fourier (T := 2 * π) m)).aestronglyMeasurable)]
  have hpt : ∀ z : AddCircle (2 * π),
      fourier (T := 2 * π) (-m) z = fourier (T := 2 * π) m (-z) := by
    intro z
    rw [fourier_apply, fourier_apply, neg_zsmul, zsmul_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt z).symm)

/-- Normalized Haar measure on the circle is negation-invariant (its coefficients are
`δ_{k0}`, which is even). -/
private lemma negInvariant_haarAddCircle :
    NegInvariant (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) := by
  haveI : IsFiniteMeasure
      ((AddCircle.haarAddCircle : Measure (AddCircle (2 * π))).map (fun z => -z)) :=
    Measure.isFiniteMeasure_map _ _
  refine ext_of_measureFourierCoeff _ _ fun m => ?_
  rw [measureFourierCoeff_map_neg', measureFourierCoeff_haarAddCircle,
    measureFourierCoeff_haarAddCircle]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [if_neg (neg_ne_zero.mpr hm), if_neg hm]

/-- The spectral measure of white noise is the uniform measure of total mass `σ²`
(FY §2.3.2: constant spectral density `σ²/2π`): `F = σ² • (normalized Haar)`. -/
theorem isSpectralMeasure_whiteNoise [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hσ : 0 ≤ σ2) (hε : IsWhiteNoise ε σ2 μ) :
    IsSpectralMeasure ε μ (ENNReal.ofReal σ2 •
      (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) := by
  refine ⟨⟨?_⟩, ?_, fun k => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  · rw [NegInvariant, Measure.map_smul, negInvariant_haarAddCircle]
  · rw [measureFourierCoeff_smul', measureFourierCoeff_haarAddCircle,
      ENNReal.toReal_ofReal hσ, hε.acvf_eq k]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg hk, if_neg hk, mul_zero, Complex.ofReal_zero]

end StatLean.TimeSeries
