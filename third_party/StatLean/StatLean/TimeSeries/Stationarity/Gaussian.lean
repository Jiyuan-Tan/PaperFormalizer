module
public import StatLean.TimeSeries.ForMathlib.Fourier.HerglotzBochner
public import StatLean.TimeSeries.Process.LinearProcess
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-!
# Stationary Gaussian processes and the completion of FY Theorem 2.7 (FY §2.1.3, §2.2.1)

Two threads:

1. **FY Theorem 2.7, sufficiency** (`exists_stationary_of_isPosSemidefSeq`, the batch-A
   debt): every even positive semidefinite `γ : ℤ → ℝ` is the ACVF of some weakly
   stationary process. Proof by the **random-phase construction** over the Herglotz
   spectral measure — no Kolmogorov extension needed: on
   `Ω' = AddCircle (2π) × ℝ × ℝ` with `P = (γ(0)⁻¹ • F) ⊗ N(0,1) ⊗ N(0,1)` (where `F`
   is the measure from `exists_measure_of_isPosSemidefSeq`), the process
   `X_t(λ, α, β) = √γ(0) · (α · Re(e^{itλ}) + β · Im(e^{itλ}))`
   has mean `0` and covariance
   `E X_s X_t = γ(0)·E_Λ[Re(e^{i(s−t)Λ})] = Re(measureFourierCoeff F (s−t)) = γ(s−t)`.
2. **FY §2.1.3**: Gaussian processes — a weakly stationary Gaussian process is strictly
   stationary (finite-dimensional Gaussian laws are determined by mean vector and
   covariance matrix, both shift-invariant); a causal ARMA process driven by i.i.d.
   Gaussian noise is a Gaussian process (`L²`-limits of Gaussian vectors are Gaussian);
   the **Wold decomposition** (FY eq. (2.6)) as a named DEBT (batch F, conditional-
   expectation route) and **Proposition 2.1** standing on it.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003: §2.2.1
Theorem 2.7 (p. 40; sufficiency cited to Brockwell & Davis 1991, p. 27 — our
random-phase proof is a different, self-contained route, documented deviation);
§2.1.3 (pp. 32–33: Gaussian processes, Wold eq. (2.6), Proposition 2.1).
(`FY §2.2.1 Thm 2.7; §2.1.3 Prop 2.1`.)

**Proof formalization notes.**
* The random-phase process is *not* Gaussian and not strictly stationary — Theorem 2.7
  only demands weak stationarity, and the construction uses exclusively batch-A bricks
  (`exists_measure_of_isPosSemidefSeq`, `measureFourierCoeff_im/neg`, `NegInvariant`).
  The amplitudes only need mean `0`, variance `1`, uncorrelated; we take independent
  standard Gaussians (`gaussianReal 0 1`) for definiteness.
* `IsGaussianProcess` is Mathlib's (pinned) structure; the weak⇒strict argument pins the
  finite-dimensional laws down through their characteristic functions.
* Prop 2.1(iii) (conditional-independence ⇒ AR(p)) needs Gaussian conditioning; stated
  here with proof deferred (DEBT) pending the Gaussian-conditioning bricks.

**Bibliographic comments.** The spectral random-phase representation goes back to
Slutsky and to Cramér's spectral theory (H. Cramér, "On the theory of stationary random
processes", *Ann. of Math.* **41** (1940), 215–230). The Wold decomposition is H. Wold
(1938). Gaussian processes as determined by second-order structure: Kolmogorov's
*Grundbegriffe* (1933) plus classical multivariate normal theory.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real ENNReal Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The random-phase construction (private machinery for FY Theorem 2.7, sufficiency)

On `Ω' = AddCircle (2π) × (ℝ × ℝ)` carrying `P ⊗ N(0,1) ⊗ N(0,1)` the process
`X_t(λ, α, β) = c · (α · Re(e^{itλ}) + β · Im(e^{itλ}))` has mean `0` and covariance
`c² · Re ∫ e^{i(s−t)λ} dP(λ) = c² · Re (measureFourierCoeff P (s − t))`; feeding in the
Herglotz measure normalized to a probability measure and `c = √γ(0)` gives `γ`. -/

private instance factpi : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- Sample space of the random-phase construction: circle × (two amplitudes). -/
private abbrev RPS : Type := AddCircle (2 * π) × (ℝ × ℝ)

/-- Amplitude law: two independent standard Gaussians (any mean-`0`, variance-`1`,
uncorrelated pair would do). -/
private noncomputable def rpAmp : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

private instance rpAmp_isProb : IsProbabilityMeasure rpAmp := by
  rw [rpAmp]; infer_instance

private instance rpAmp_isFinite : IsFiniteMeasure rpAmp := inferInstance

private instance rpAmp_sfinite : SFinite rpAmp := inferInstance

/-- The random-phase process with amplitude scale `c`. -/
private noncomputable def rpProc (c : ℝ) (t : ℤ) : RPS → ℝ :=
  fun z => c * (z.2.1 * (fourier t z.1).re + z.2.2 * (fourier t z.1).im)

private lemma memLp_gauss (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun x : ℝ => x) p (gaussianReal 0 1) := memLp_id_gaussianReal' p hp

private lemma integrable_gauss : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
  (memLp_gauss 1 (by simp)).integrable le_rfl

private lemma gauss_sq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (μ := gaussianReal 0 1) (memLp_gauss 2 (by simp))
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  simpa using h.symm

private lemma integrable_gauss_sq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  have := (memLp_gauss 2 (by simp)).integrable_sq
  simpa using this

private lemma rpAmp_fst : ∫ p : ℝ × ℝ, p.1 ∂rpAmp = 0 := by
  rw [rpAmp]
  simpa using integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (fun x : ℝ => x)

private lemma rpAmp_snd : ∫ p : ℝ × ℝ, p.2 ∂rpAmp = 0 := by
  rw [rpAmp]
  simpa using integral_fun_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (fun x : ℝ => x)

private lemma rpAmp_fst_sq : ∫ p : ℝ × ℝ, p.1 * p.1 ∂rpAmp = 1 := by
  rw [rpAmp]
  have h := integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (fun x : ℝ => x ^ 2)
  simp only [probReal_univ, one_smul, gauss_sq] at h
  simpa [← pow_two] using h

private lemma rpAmp_snd_sq : ∫ p : ℝ × ℝ, p.2 * p.2 ∂rpAmp = 1 := by
  rw [rpAmp]
  have h := integral_fun_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (fun x : ℝ => x ^ 2)
  simp only [probReal_univ, one_smul, gauss_sq] at h
  simpa [← pow_two] using h

private lemma rpAmp_cross : ∫ p : ℝ × ℝ, p.1 * p.2 ∂rpAmp = 0 := by
  rw [rpAmp]
  simpa using integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x : ℝ => x) (fun x : ℝ => x)

private lemma rpAmp_int_fst : Integrable (fun p : ℝ × ℝ => p.1) rpAmp := by
  rw [rpAmp]; exact integrable_gauss.comp_fst _

private lemma rpAmp_int_snd : Integrable (fun p : ℝ × ℝ => p.2) rpAmp := by
  rw [rpAmp]; exact integrable_gauss.comp_snd _

private lemma rpAmp_int_fst_sq : Integrable (fun p : ℝ × ℝ => p.1 * p.1) rpAmp := by
  have h : (fun p : ℝ × ℝ => p.1 * p.1) = fun p : ℝ × ℝ => p.1 ^ 2 := by funext p; ring
  rw [h, rpAmp]; exact integrable_gauss_sq.comp_fst _

private lemma rpAmp_int_snd_sq : Integrable (fun p : ℝ × ℝ => p.2 * p.2) rpAmp := by
  have h : (fun p : ℝ × ℝ => p.2 * p.2) = fun p : ℝ × ℝ => p.2 ^ 2 := by funext p; ring
  rw [h, rpAmp]; exact integrable_gauss_sq.comp_snd _

private lemma rpAmp_int_cross : Integrable (fun p : ℝ × ℝ => p.1 * p.2) rpAmp := by
  rw [rpAmp]; exact integrable_gauss.mul_prod integrable_gauss

private lemma continuous_fourier_re (t : ℤ) :
    Continuous fun l : AddCircle (2 * π) => (fourier t l).re :=
  Complex.continuous_re.comp (map_continuous (fourier t))

private lemma continuous_fourier_im (t : ℤ) :
    Continuous fun l : AddCircle (2 * π) => (fourier t l).im :=
  Complex.continuous_im.comp (map_continuous (fourier t))

private lemma integrable_of_continuous (P : Measure (AddCircle (2 * π))) [IsFiniteMeasure P]
    {F : AddCircle (2 * π) → ℝ} (hF : Continuous F) : Integrable F P := by
  simpa using! (BoundedContinuousFunction.mkOfCompact
    (⟨F, hF⟩ : C(AddCircle (2 * π), ℝ))).integrable P

/-- `Re(e^{isλ} · conj e^{itλ}) = Re e^{i(s−t)λ}` in coordinates. -/
private lemma fourier_sub_re (s t : ℤ) (l : AddCircle (2 * π)) :
    (fourier s l).re * (fourier t l).re + (fourier s l).im * (fourier t l).im
      = (fourier (s - t) l).re := by
  have h : fourier (T := 2 * π) (s - t) l
      = fourier (T := 2 * π) s l * (starRingEnd ℂ) (fourier (T := 2 * π) t l) := by
    rw [sub_eq_add_neg, fourier_add, fourier_neg]
  rw [h]
  simp [Complex.mul_re]

private lemma rp_int_term {F : AddCircle (2 * π) → ℝ} (hF : Continuous F)
    {G : ℝ × ℝ → ℝ} (hG : Integrable G rpAmp)
    (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P] :
    Integrable (fun z : RPS => F z.1 * G z.2) (P.prod rpAmp) :=
  (integrable_of_continuous P hF).mul_prod hG

private lemma rp_integral (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (t : ℤ) : ∫ z, rpProc c t z ∂(P.prod rpAmp) = 0 := by
  have h1 : Integrable (fun z : RPS => (fourier t z.1).re * z.2.1) (P.prod rpAmp) :=
    rp_int_term (continuous_fourier_re t) rpAmp_int_fst P
  have h2 : Integrable (fun z : RPS => (fourier t z.1).im * z.2.2) (P.prod rpAmp) :=
    rp_int_term (continuous_fourier_im t) rpAmp_int_snd P
  have heq : ∀ z : RPS, rpProc c t z
      = c * ((fourier t z.1).re * z.2.1 + (fourier t z.1).im * z.2.2) := by
    intro z; simp only [rpProc]; ring
  calc ∫ z, rpProc c t z ∂(P.prod rpAmp)
      = ∫ z : RPS, c * ((fourier t z.1).re * z.2.1 + (fourier t z.1).im * z.2.2)
          ∂(P.prod rpAmp) := integral_congr_ae (Eventually.of_forall heq)
    _ = c * ∫ z : RPS, ((fourier t z.1).re * z.2.1 + (fourier t z.1).im * z.2.2)
          ∂(P.prod rpAmp) := integral_const_mul _ _
    _ = 0 := by
        rw [integral_add h1 h2,
          integral_prod_mul (μ := P) (ν := rpAmp)
            (fun l => (fourier (T := 2 * π) t l).re) (fun p : ℝ × ℝ => p.1),
          integral_prod_mul (μ := P) (ν := rpAmp)
            (fun l => (fourier (T := 2 * π) t l).im) (fun p : ℝ × ℝ => p.2),
          rpAmp_fst, rpAmp_snd]
        ring

/-- The three-term quadratic form in the amplitudes, integrated out: only the `α²` and
`β²` slots survive (`E α² = E β² = 1`, `E αβ = 0`). -/
private lemma rp_quad (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    {F₁ F₂ F₃ : AddCircle (2 * π) → ℝ} (h₁ : Continuous F₁) (h₂ : Continuous F₂)
    (h₃ : Continuous F₃) :
    ∫ z : RPS, (F₁ z.1 * (z.2.1 * z.2.1) + F₂ z.1 * (z.2.1 * z.2.2)
        + F₃ z.1 * (z.2.2 * z.2.2)) ∂(P.prod rpAmp)
      = ∫ l, (F₁ l + F₃ l) ∂P := by
  have i₁ : Integrable (fun z : RPS => F₁ z.1 * (z.2.1 * z.2.1)) (P.prod rpAmp) :=
    rp_int_term h₁ rpAmp_int_fst_sq P
  have i₂ : Integrable (fun z : RPS => F₂ z.1 * (z.2.1 * z.2.2)) (P.prod rpAmp) :=
    rp_int_term h₂ rpAmp_int_cross P
  have i₃ : Integrable (fun z : RPS => F₃ z.1 * (z.2.2 * z.2.2)) (P.prod rpAmp) :=
    rp_int_term h₃ rpAmp_int_snd_sq P
  have i₁₂ : Integrable
      (fun z : RPS => F₁ z.1 * (z.2.1 * z.2.1) + F₂ z.1 * (z.2.1 * z.2.2)) (P.prod rpAmp) :=
    i₁.add i₂
  rw [integral_add i₁₂ i₃, integral_add i₁ i₂,
    integral_prod_mul (μ := P) (ν := rpAmp) F₁ (fun p : ℝ × ℝ => p.1 * p.1),
    integral_prod_mul (μ := P) (ν := rpAmp) F₂ (fun p : ℝ × ℝ => p.1 * p.2),
    integral_prod_mul (μ := P) (ν := rpAmp) F₃ (fun p : ℝ × ℝ => p.2 * p.2),
    rpAmp_fst_sq, rpAmp_snd_sq, rpAmp_cross,
    integral_add (integrable_of_continuous P h₁) (integrable_of_continuous P h₃)]
  ring

private lemma rp_prod_eq (c : ℝ) (s t : ℤ) (z : RPS) :
    rpProc c s z * rpProc c t z
      = (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re)) z.1 * (z.2.1 * z.2.1)
        + (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
            + (fourier s l).im * (fourier t l).re)) z.1 * (z.2.1 * z.2.2)
        + (fun l => c ^ 2 * ((fourier s l).im * (fourier t l).im)) z.1 * (z.2.2 * z.2.2) := by
  simp only [rpProc]
  ring

private lemma rp_integrable_mul (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (s t : ℤ) :
    Integrable (fun z : RPS => rpProc c s z * rpProc c t z) (P.prod rpAmp) := by
  have i₁ : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re)) z.1 * (z.2.1 * z.2.1))
      (P.prod rpAmp) :=
    rp_int_term (((continuous_fourier_re s).mul (continuous_fourier_re t)).const_mul _)
      rpAmp_int_fst_sq P
  have i₂ : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
        + (fourier s l).im * (fourier t l).re)) z.1 * (z.2.1 * z.2.2)) (P.prod rpAmp) :=
    rp_int_term ((((continuous_fourier_re s).mul (continuous_fourier_im t)).add
      ((continuous_fourier_im s).mul (continuous_fourier_re t))).const_mul _) rpAmp_int_cross P
  have i₃ : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).im * (fourier t l).im)) z.1 * (z.2.2 * z.2.2))
      (P.prod rpAmp) :=
    rp_int_term (((continuous_fourier_im s).mul (continuous_fourier_im t)).const_mul _)
      rpAmp_int_snd_sq P
  have i₁₂ : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re)) z.1 * (z.2.1 * z.2.1)
        + (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
            + (fourier s l).im * (fourier t l).re)) z.1 * (z.2.1 * z.2.2)) (P.prod rpAmp) :=
    i₁.add i₂
  have i : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re)) z.1 * (z.2.1 * z.2.1)
        + (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
            + (fourier s l).im * (fourier t l).re)) z.1 * (z.2.1 * z.2.2)
        + (fun l => c ^ 2 * ((fourier s l).im * (fourier t l).im)) z.1 * (z.2.2 * z.2.2))
      (P.prod rpAmp) := i₁₂.add i₃
  exact i.congr (Eventually.of_forall fun z => (rp_prod_eq c s t z).symm)

private lemma rp_integral_mul (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (s t : ℤ) :
    ∫ z, rpProc c s z * rpProc c t z ∂(P.prod rpAmp)
      = c ^ 2 * (measureFourierCoeff P (s - t)).re := by
  have hfourier : Integrable (fun l : AddCircle (2 * π) => fourier (s - t) l) P :=
    (BoundedContinuousFunction.mkOfCompact (fourier (T := 2 * π) (s - t))).integrable P
  have hre : ∫ l : AddCircle (2 * π), (fourier (s - t) l).re ∂P
      = (measureFourierCoeff P (s - t)).re := by
    rw [measureFourierCoeff]
    simpa using integral_re (μ := P) (f := fun l : AddCircle (2 * π) => fourier (s - t) l) hfourier
  rw [integral_congr_ae (Eventually.of_forall (rp_prod_eq c s t)),
    rp_quad P (F₁ := fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re))
      (F₂ := fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
        + (fourier s l).im * (fourier t l).re))
      (F₃ := fun l => c ^ 2 * ((fourier s l).im * (fourier t l).im))
      (((continuous_fourier_re s).mul (continuous_fourier_re t)).const_mul _)
      ((((continuous_fourier_re s).mul (continuous_fourier_im t)).add
        ((continuous_fourier_im s).mul (continuous_fourier_re t))).const_mul _)
      (((continuous_fourier_im s).mul (continuous_fourier_im t)).const_mul _)]
  have hpt : ∀ l : AddCircle (2 * π),
      c ^ 2 * ((fourier s l).re * (fourier t l).re)
        + c ^ 2 * ((fourier s l).im * (fourier t l).im)
        = c ^ 2 * (fourier (s - t) l).re := by
    intro l
    rw [← fourier_sub_re s t l]; ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, hre]

private lemma rp_continuous (c : ℝ) (t : ℤ) : Continuous (rpProc c t) := by
  have hre : Continuous fun z : RPS => (fourier t z.1).re :=
    (continuous_fourier_re t).comp continuous_fst
  have him : Continuous fun z : RPS => (fourier t z.1).im :=
    (continuous_fourier_im t).comp continuous_fst
  have h1 : Continuous fun z : RPS => z.2.1 := continuous_fst.comp continuous_snd
  have h2 : Continuous fun z : RPS => z.2.2 := continuous_snd.comp continuous_snd
  exact ((h1.mul hre).add (h2.mul him)).const_mul c

private lemma rp_memLp (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (t : ℤ) : MemLp (rpProc c t) 2 (P.prod rpAmp) := by
  refine (memLp_two_iff_integrable_sq (rp_continuous c t).aestronglyMeasurable).mpr ?_
  refine (rp_integrable_mul P c t t).congr ?_
  filter_upwards with z
  rw [pow_two]

private lemma rp_cov (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (s t : ℤ) :
    cov[rpProc c s, rpProc c t; P.prod rpAmp] = c ^ 2 * (measureFourierCoeff P (s - t)).re := by
  rw [covariance_eq_sub (rp_memLp P c s) (rp_memLp P c t), rp_integral, rp_integral]
  simp only [mul_zero, sub_zero, Pi.mul_apply]
  exact rp_integral_mul P c s t

private theorem rp_isStationary (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) : IsStationary (rpProc c) (P.prod rpAmp) where
  memLp t := rp_memLp P c t
  integral_eq s t := by rw [rp_integral, rp_integral]
  cov_shift t k := by
    have h : t + k - t = k - 0 := by ring
    rw [rp_cov, rp_cov, h]

private theorem rp_acvf (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (k : ℤ) :
    acvf (rpProc c) (P.prod rpAmp) k = c ^ 2 * (measureFourierCoeff P k).re := by
  rw [acvf, rp_cov, sub_zero]

/-- `measureFourierCoeff` is scalar-linear in the measure (the normalization step). -/
private lemma mfc_smul (a : ENNReal) (F : Measure (AddCircle (2 * π))) (j : ℤ) :
    measureFourierCoeff (a • F) j = ((a.toReal : ℝ) : ℂ) * measureFourierCoeff F j := by
  rw [measureFourierCoeff, measureFourierCoeff, integral_smul_measure]
  exact Complex.real_smul

/-- **FY Theorem 2.7, sufficiency** (batch-A debt, relocated here; proof: random-phase
construction over the Herglotz measure — see the module docstring). Every even positive
semidefinite sequence is the autocovariance function of some weakly stationary process. -/
theorem exists_stationary_of_isPosSemidefSeq (γ : ℤ → ℝ)
    -- USER-INPUT: evenness; FY §2.2.1 Thm 2.7
    (heven : ∀ k, γ (-k) = γ k)
    -- USER-INPUT: positive semidefiniteness, eq. (2.17); FY §2.2.1 Thm 2.7
    (hpsd : IsPosSemidefSeq γ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsStationary X' μ' ∧
        acvf X' μ' = γ := by
  -- Produce a probability measure `P` on the circle and a scale `c` with
  -- `c² · Re (measureFourierCoeff P k) = γ k`; the random-phase process then has ACVF `γ`.
  obtain ⟨P, hP, c, hc⟩ : ∃ (P : Measure (AddCircle (2 * π))) (_ : IsProbabilityMeasure P) (c : ℝ),
      ∀ k, c ^ 2 * (measureFourierCoeff P k).re = γ k := by
    rcases eq_or_lt_of_le hpsd.nonneg_zero with h0 | h0
    · -- degenerate case `γ 0 = 0`: `|γ k| ≤ γ 0 = 0` forces `γ ≡ 0`, take `c = 0`
      have hzero : ∀ k, γ k = 0 := by
        intro k
        have h1 := hpsd.abs_le_of_even heven k
        rw [← h0] at h1
        exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
      exact ⟨Measure.dirac 0, inferInstance, 0, fun k => by simp [hzero k]⟩
    · -- main case: normalize the Herglotz measure to a probability measure, `c = √γ(0)`
      obtain ⟨F, hFfin, _hFneg, hFcoef⟩ := exists_measure_of_isPosSemidefSeq γ heven hpsd
      have hne : ENNReal.ofReal (γ 0) ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h0
      have htop : ENNReal.ofReal (γ 0) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hmass : F Set.univ = ENNReal.ofReal (γ 0) := by
        have h := (measureFourierCoeff_zero F).symm.trans (hFcoef 0)
        have h2 : (F Set.univ).toReal = γ 0 := by exact_mod_cast h
        rw [← h2, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      haveI hprob : IsProbabilityMeasure ((ENNReal.ofReal (γ 0))⁻¹ • F) :=
        ⟨by rw [Measure.smul_apply, smul_eq_mul, hmass, ENNReal.inv_mul_cancel hne htop]⟩
      refine ⟨(ENNReal.ofReal (γ 0))⁻¹ • F, hprob, Real.sqrt (γ 0), fun k => ?_⟩
      rw [mfc_smul, hFcoef k, ENNReal.toReal_inv, ENNReal.toReal_ofReal h0.le,
        Real.sq_sqrt h0.le, ← Complex.ofReal_mul, Complex.ofReal_re]
      field_simp
  haveI := hP
  exact ⟨AddCircle (2 * π) × (ℝ × ℝ), inferInstance, P.prod rpAmp, rpProc c, inferInstance,
    fun t => (rp_continuous c t).measurable, rp_isStationary P c,
    funext fun k => (rp_acvf P c k).trans (hc k)⟩

/-- **FY Theorem 2.7, both halves packaged**: a real sequence is the ACVF of some weakly
stationary process iff it is even and positive semidefinite. -/
theorem isPosSemidefSeq_and_even_iff_acvf (γ : ℤ → ℝ) :
    ((∀ k, γ (-k) = γ k) ∧ IsPosSemidefSeq γ) ↔
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' : ℤ → Ω' → ℝ),
        IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsStationary X' μ' ∧
          acvf X' μ' = γ := by
  constructor
  · rintro ⟨heven, hpsd⟩
    exact exists_stationary_of_isPosSemidefSeq γ heven hpsd
  · rintro ⟨Ω', _, μ', X', hprob, _hmeas, hstat, rfl⟩
    exact ⟨hstat.acvf_even, hstat.acvf_posSemidef⟩

/-! ### Gaussian finite-dimensional laws (private machinery for the weak ⇒ strict step) -/

/-- Every finite-dimensional tuple of a Gaussian process has a Gaussian law on `Fin n → ℝ`
(a continuous-linear image of the `Finset`-restricted process). -/
private lemma hasGaussianLaw_tuple {X : ℤ → Ω → ℝ} (hG : IsGaussianProcess X μ)
    {n : ℕ} (τ : Fin n → ℤ) :
    HasGaussianLaw (fun ω (i : Fin n) => X (τ i) ω) μ := by
  classical
  let I : Finset ℤ := Finset.image τ Finset.univ
  let L : (I → ℝ) →L[ℝ] (Fin n → ℝ) :=
    { toFun := fun x i => x ⟨τ i, Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp
      cont := by fun_prop }
  exact (hG.hasGaussianLaw I).map_fun L

/-- A continuous linear functional on a finite product of copies of `ℝ`, in coordinates. -/
private lemma dual_apply_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, x i * L (fun j => if i = j then (1 : ℝ) else 0) := by
  have h := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
  simpa [smul_eq_mul] using h

/-- The covariance of two linear functionals of a tuple, in terms of the ACVF. -/
private lemma cov_dual_tuple [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) {n : ℕ} (τ : Fin n → ℤ)
    (L₁ L₂ : StrongDual ℝ (Fin n → ℝ)) :
    cov[fun ω => L₁ fun i => X (τ i) ω, fun ω => L₂ fun i => X (τ i) ω; μ]
      = ∑ i, ∑ j, (L₁ (fun j' => if i = j' then (1 : ℝ) else 0)
          * L₂ (fun j' => if j = j' then (1 : ℝ) else 0)) * acvf X μ (τ i - τ j) := by
  have h1 : (fun ω => L₁ fun i => X (τ i) ω)
      = fun ω => ∑ i, X (τ i) ω * L₁ (fun j => if i = j then (1 : ℝ) else 0) := by
    funext ω; exact dual_apply_sum L₁ _
  have h2 : (fun ω => L₂ fun i => X (τ i) ω)
      = fun ω => ∑ i, X (τ i) ω * L₂ (fun j => if i = j then (1 : ℝ) else 0) := by
    funext ω; exact dual_apply_sum L₂ _
  rw [h1, h2, covariance_fun_sum_fun_sum (fun i => (hstat.memLp (τ i)).mul_const _)
    (fun j => (hstat.memLp (τ j)).mul_const _)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_mul_const_left, covariance_mul_const_right, hstat.cov_eq_acvf]
  ring

/-- Two finite-dimensional laws of a weakly stationary Gaussian process agree as soon as the
covariance patterns of the two time tuples agree: both laws are Gaussian, their mean vectors
are constant (weak stationarity) and their dual covariance forms are the ACVF pattern. -/
private theorem map_tuple_eq_of_acvf [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hG : IsGaussianProcess X μ) (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    {n : ℕ} (τ σ : Fin n → ℤ)
    (hacvf : ∀ i j, acvf X μ (τ i - τ j) = acvf X μ (σ i - σ j)) :
    (μ.map fun ω (i : Fin n) => X (τ i) ω) = μ.map fun ω (i : Fin n) => X (σ i) ω := by
  haveI hgτ : IsGaussian (μ.map fun ω (i : Fin n) => X (τ i) ω) :=
    (hasGaussianLaw_tuple hG τ).isGaussian_map
  haveI hgσ : IsGaussian (μ.map fun ω (i : Fin n) => X (σ i) ω) :=
    (hasGaussianLaw_tuple hG σ).isGaussian_map
  have hmτ : Measurable fun ω (i : Fin n) => X (τ i) ω :=
    measurable_pi_lambda _ fun i => hmeas _
  have hmσ : Measurable fun ω (i : Fin n) => X (σ i) ω :=
    measurable_pi_lambda _ fun i => hmeas _
  have hIτ : Integrable (fun ω (i : Fin n) => X (τ i) ω) μ := by
    have h := IsGaussian.integrable_id (μ := μ.map fun ω (i : Fin n) => X (τ i) ω)
    rw [integrable_map_measure aestronglyMeasurable_id hmτ.aemeasurable] at h
    simpa [Function.comp_def] using h
  have hIσ : Integrable (fun ω (i : Fin n) => X (σ i) ω) μ := by
    have h := IsGaussian.integrable_id (μ := μ.map fun ω (i : Fin n) => X (σ i) ω)
    rw [integrable_map_measure aestronglyMeasurable_id hmσ.aemeasurable] at h
    simpa [Function.comp_def] using h
  refine IsGaussian.ext_covarianceBilinDual ?_ ?_
  · -- mean vectors: coordinatewise, the constant mean of the process
    rw [integral_map hmτ.aemeasurable aestronglyMeasurable_id,
      integral_map hmσ.aemeasurable aestronglyMeasurable_id]
    funext i
    have f1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).integral_comp_comm
      hIτ
    have f2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).integral_comp_comm
      hIσ
    simp only [ContinuousLinearMap.proj_apply, id_eq] at f1 f2 ⊢
    rw [← f1, ← f2]
    exact hstat.integral_eq _ _
  · -- dual covariance forms: the ACVF pattern of the tuple
    ext L₁ L₂
    rw [covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covariance_map_fun L₁.continuous.aestronglyMeasurable L₂.continuous.aestronglyMeasurable
        hmτ.aemeasurable,
      covariance_map_fun L₁.continuous.aestronglyMeasurable L₂.continuous.aestronglyMeasurable
        hmσ.aemeasurable,
      cov_dual_tuple hstat τ L₁ L₂, cov_dual_tuple hstat σ L₁ L₂]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hacvf i j]

/-- **Weakly stationary Gaussian processes are strictly stationary** (FY §2.1.3): the
finite-dimensional laws of a Gaussian process are determined by the mean vector and
covariance matrix, and both are shift-invariant under weak stationarity. -/
theorem IsGaussianProcess.isStrictlyStationary [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ}
    -- USER-INPUT: the process is Gaussian; FY §2.1.3
    (hG : IsGaussianProcess X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: weak stationarity; FY §2.1.3
    (hstat : IsStationary X μ) :
    IsStrictlyStationary X μ := by
  intro n t k
  exact map_tuple_eq_of_acvf hG hmeas hstat (fun i => t i + k) t
    (fun i j => by rw [show t i + k - (t j + k) = t i - t j by ring])

/-! ### `L²`-limits of Gaussian laws (private machinery for the linear-process step) -/

private lemma real_inner_mul' (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

private lemma integral_sq_eq_norm_sq {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    ∫ ω, g ω ^ 2 ∂μ = ‖hg.toLp g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with ω hω
  rw [real_inner_mul', hω, ← pow_two]

/-- **`L²`-limits of real Gaussian random variables are Gaussian.** -/
private lemma isGaussian_map_of_tendsto_L2 [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} {Z : Ω → ℝ}
    (hYg : ∀ N, IsGaussian (μ.map (Y N)))
    (hYm : ∀ N, AEStronglyMeasurable (Y N) μ) (hZm : AEStronglyMeasurable Z μ)
    (hconv : Tendsto (fun N => eLpNorm (Y N - Z) 2 μ) atTop (𝓝 0)) :
    IsGaussian (μ.map Z) := by
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZm.aemeasurable
  -- `L²` membership
  have hYL2 : ∀ N, MemLp (Y N) 2 μ := by
    intro N
    haveI := hYg N
    have h := IsGaussian.memLp_two_id (μ := μ.map (Y N))
    rw [memLp_map_measure_iff aestronglyMeasurable_id (hYm N).aemeasurable] at h
    simpa [Function.comp_def] using h
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, eLpNorm (Y N₀ - Z) 2 μ < ⊤ := by
    obtain ⟨N₀, hN₀⟩ := (hconv.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1)).exists
    exact ⟨N₀, hN₀.trans_le le_top⟩
  have hdiff : MemLp (Y N₀ - Z) 2 μ := ⟨(hYm N₀).sub hZm, hN₀⟩
  have hZL2 : MemLp Z 2 μ := by
    have h := (hYL2 N₀).sub hdiff
    simpa using h
  -- means converge
  have hmean : Tendsto (fun N => ∫ ω, Y N ω ∂μ) atTop (𝓝 (∫ ω, Z ω ∂μ)) := by
    refine tendsto_integral_of_L1' Z (hZL2.integrable one_le_two).aestronglyMeasurable
      (Eventually.of_forall fun N => (hYL2 N).integrable one_le_two) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun N => zero_le) fun N => ?_
    exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two ((hYm N).sub hZm)
  -- second moments converge (continuity of the `L²` norm)
  have hLp : Tendsto (fun N => (hYL2 N).toLp (Y N)) atTop (𝓝 (hZL2.toLp Z)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hd : ∀ N, dist ((hYL2 N).toLp (Y N)) (hZL2.toLp Z)
        = (eLpNorm (Y N - Z) 2 μ).toReal := by
      intro N
      rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    simp only [hd]
    exact (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hconv
  have hsq : Tendsto (fun N => ∫ ω, Y N ω ^ 2 ∂μ) atTop (𝓝 (∫ ω, Z ω ^ 2 ∂μ)) := by
    simp only [integral_sq_eq_norm_sq (hYL2 _), integral_sq_eq_norm_sq hZL2]
    exact (hLp.norm).pow 2
  have hvar : Tendsto (fun N => Var[Y N; μ]) atTop (𝓝 Var[Z; μ]) := by
    simp only [variance_eq_sub (hYL2 _), variance_eq_sub hZL2]
    have h1 : ∀ N, (μ[(Y N) ^ 2] : ℝ) = ∫ ω, Y N ω ^ 2 ∂μ := fun N => by simp
    have h2 : (μ[Z ^ 2] : ℝ) = ∫ ω, Z ω ^ 2 ∂μ := by simp
    simp only [h1, h2]
    exact hsq.sub (hmean.pow 2)
  -- pass to a subsequence along which `Y` converges a.e.
  obtain ⟨ns, hmono, hns⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) (fun N => hYm N) hZm
      hconv).exists_seq_tendsto_ae
  -- the characteristic functions agree in the limit
  suffices h : μ.map Z = gaussianReal (∫ ω, Z ω ∂μ) Var[Z; μ].toNNReal by
    rw [h]; infer_instance
  refine Measure.ext_of_charFun ?_
  funext u
  have hchar : ∀ N, charFun (μ.map (Y N)) u
      = Complex.exp (u * (∫ ω, Y N ω ∂μ) * Complex.I - Var[Y N; μ] * u ^ 2 / 2) := by
    intro N
    haveI := hYg N
    rw [(hYg N).eq_gaussianReal, charFun_gaussianReal, integral_map (hYm N).aemeasurable
      aestronglyMeasurable_id, variance_map aemeasurable_id (hYm N).aemeasurable]
    simp [Real.coe_toNNReal _ (variance_nonneg _ _)]
  have hcv : ∀ N, charFun (μ.map (Y N)) u = ∫ ω, Complex.exp (u * Y N ω * Complex.I) ∂μ := by
    intro N
    rw [charFun_apply, integral_map (hYm N).aemeasurable]
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [real_inner_mul']
      congr 1
      push_cast
      ring
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hcz : charFun (μ.map Z) u = ∫ ω, Complex.exp (u * Z ω * Complex.I) ∂μ := by
    rw [charFun_apply, integral_map hZm.aemeasurable]
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [real_inner_mul']
      congr 1
      push_cast
      ring
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hlim1 : Tendsto (fun j => ∫ ω, Complex.exp (u * Y (ns j) ω * Complex.I) ∂μ) atTop
      (𝓝 (∫ ω, Complex.exp (u * Z ω * Complex.I) ∂μ)) := by
    have hcont : Continuous fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I) := by
      fun_prop
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun j => hcont.comp_aestronglyMeasurable (hYm (ns j))) (integrable_const _)
      (fun j => Eventually.of_forall fun ω => ?_) ?_
    · have hre : ((u : ℂ) * (Y (ns j) ω : ℂ) * Complex.I).re = 0 := by simp
      rw [Complex.norm_exp, hre]
      simp
    · filter_upwards [hns] with ω hω
      exact (hcont.tendsto _).comp hω
  rw [charFun_gaussianReal, Real.coe_toNNReal _ (variance_nonneg _ _), hcz]
  refine tendsto_nhds_unique hlim1 ?_
  have hrw : ∀ j, ∫ ω, Complex.exp (u * Y (ns j) ω * Complex.I) ∂μ
      = Complex.exp (u * (∫ ω, Y (ns j) ω ∂μ) * Complex.I
          - Var[Y (ns j); μ] * u ^ 2 / 2) := fun j => by rw [← hcv, hchar]
  simp only [hrw]
  have hm' : Tendsto (fun j => ∫ ω, Y (ns j) ω ∂μ) atTop (𝓝 (∫ ω, Z ω ∂μ)) :=
    hmean.comp hmono.tendsto_atTop
  have hv' : Tendsto (fun j => Var[Y (ns j); μ]) atTop (𝓝 Var[Z; μ]) :=
    hvar.comp hmono.tendsto_atTop
  have hA : Tendsto (fun j => ((u : ℂ) * ((∫ ω, Y (ns j) ω ∂μ : ℝ) : ℂ) * Complex.I
      - ((Var[Y (ns j); μ] : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2)) atTop
      (𝓝 ((u : ℂ) * ((∫ ω, Z ω ∂μ : ℝ) : ℂ) * Complex.I
        - ((Var[Z; μ] : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2)) := by
    refine Tendsto.sub ?_ ?_
    · exact (((Complex.continuous_ofReal.tendsto _).comp hm').const_mul _).mul_const _
    · exact ((((Complex.continuous_ofReal.tendsto _).comp hv').mul_const _)).div_const _
  exact (Complex.continuous_exp.tendsto _).comp hA



section LinearGaussian

variable {ψ : ℕ → ℝ} {X ε : ℤ → Ω → ℝ}

/-- Partial sums of the linear process (FY eq. (2.1)). -/
private noncomputable def gpsum (ψ : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (s : ℤ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω

/-- A finite linear combination of i.i.d. standard Gaussian innovations is Gaussian. -/
private lemma isGaussian_noise_comb [IsProbabilityMeasure μ] {σ2 : ℝ}
    (hε : IsIIDNoise ε σ2 μ) (hgauss : ∀ t, μ.map (ε t) = gaussianReal 0 1)
    {A : Type*} [Fintype A] (τ : A → ℤ) (c : A → ℝ) :
    IsGaussian (μ.map fun ω => ∑ a, c a * ε (τ a) ω) := by
  classical
  have hmem : ∀ a : A, τ a ∈ Finset.image τ Finset.univ := fun a =>
    Finset.mem_image_of_mem τ (Finset.mem_univ a)
  have hblock : HasGaussianLaw
      (fun ω (b : {x // x ∈ Finset.image τ Finset.univ}) => ε (b : ℤ) ω) μ := by
    refine iIndepFun.hasGaussianLaw (fun b => ⟨by rw [hgauss]; infer_instance⟩) ?_
    exact hε.iIndep.precomp Subtype.val_injective
  let G : ({x // x ∈ Finset.image τ Finset.univ} → ℝ) →L[ℝ] ℝ :=
    { toFun := fun v => ∑ a, c a * v ⟨τ a, hmem a⟩
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      cont := by fun_prop }
  have heq : (fun ω => ∑ a, c a * ε (τ a) ω)
      = fun ω => G (fun (b : {x // x ∈ Finset.image τ Finset.univ}) => ε (b : ℤ) ω) := rfl
  rw [heq]
  exact (hblock.map_fun G).isGaussian_map







/-- A window of partial sums, linearly combined, is Gaussian. -/
private lemma isGaussian_gpsum_comb [IsProbabilityMeasure μ] {σ2 : ℝ}
    (hε : IsIIDNoise ε σ2 μ) (hgauss : ∀ t, μ.map (ε t) = gaussianReal 0 1)
    (ψ : ℕ → ℝ) {A : Type*} [Fintype A] (τ : A → ℤ) (c : A → ℝ) (N : ℕ) :
    IsGaussian (μ.map fun ω => ∑ a, c a * gpsum ψ ε (τ a) N ω) := by
  have heq : (fun ω => ∑ a, c a * gpsum ψ ε (τ a) N ω)
      = fun ω => ∑ p : A × Fin N, (c p.1 * ψ (p.2 : ℕ)) * ε (τ p.1 - (p.2 : ℕ)) ω := by
    funext ω
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gpsum, ← Fin.sum_univ_eq_sum_range (fun j => ψ j * ε (τ a - (j : ℕ)) ω) N,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [heq]
  exact isGaussian_noise_comb hε hgauss _ _

/-- The linear combination of the partial sums converges to that of the process in `L²`. -/
private lemma tendsto_eLpNorm_comb [IsProbabilityMeasure μ]
    (hX : IsLinearProcessOf ψ X ε μ) (hmX : ∀ t, Measurable (X t)) (hmε : ∀ t, Measurable (ε t))
    {A : Type*} [Fintype A] (τ : A → ℤ) (c : A → ℝ) :
    Tendsto (fun N => eLpNorm
      ((fun ω => ∑ a, c a * gpsum ψ ε (τ a) N ω) - fun ω => ∑ a, c a * X (τ a) ω) 2 μ)
      atTop (𝓝 0) := by
  have hmg : ∀ (a : A) (N : ℕ), Measurable (gpsum ψ ε (τ a) N) := fun a N =>
    Finset.measurable_sum _ fun j _ => (hmε _).const_mul _
  have hterm : ∀ a : A, Tendsto (fun N => eLpNorm
      (fun ω => c a * (gpsum ψ ε (τ a) N ω - X (τ a) ω)) 2 μ) atTop (𝓝 0) := by
    intro a
    have h0 : Tendsto (fun N =>
        eLpNorm (fun ω => gpsum ψ ε (τ a) N ω - X (τ a) ω) 2 μ) atTop (𝓝 0) := by
      refine (hX (τ a)).congr fun N => ?_
      rw [← eLpNorm_neg]
      exact eLpNorm_congr_ae (Eventually.of_forall fun ω => by simp [gpsum])
    have hc : ∀ N, eLpNorm (fun ω => c a * (gpsum ψ ε (τ a) N ω - X (τ a) ω)) 2 μ
        = ‖c a‖ₑ * eLpNorm (fun ω => gpsum ψ ε (τ a) N ω - X (τ a) ω) 2 μ := fun N => by
      simpa using! eLpNorm_const_smul (c := c a)
        (f := fun ω => gpsum ψ ε (τ a) N ω - X (τ a) ω) (p := 2) (μ := μ)
    simp only [hc]
    simpa using (ENNReal.Tendsto.const_mul h0 (Or.inr (by simp)))
  have hsum : Tendsto (fun N => ∑ a : A, eLpNorm
      (fun ω => c a * (gpsum ψ ε (τ a) N ω - X (τ a) ω)) 2 μ) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.univ : Finset A) fun a _ => hterm a
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun N => zero_le) fun N => ?_
  have hcongr : ((fun ω => ∑ a, c a * gpsum ψ ε (τ a) N ω) - fun ω => ∑ a, c a * X (τ a) ω)
      = fun ω => ∑ a : A, c a * (gpsum ψ ε (τ a) N ω - X (τ a) ω) := by
    funext ω
    simp only [Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hcongr]
  have hfun : (fun ω => ∑ a : A, c a * (gpsum ψ ε (τ a) N ω - X (τ a) ω))
      = ∑ a : A, fun ω => c a * (gpsum ψ ε (τ a) N ω - X (τ a) ω) := by
    funext ω; simp
  rw [hfun]
  exact eLpNorm_sum_le (fun a _ => (((hmg a N).sub (hmX _)).const_mul _).aestronglyMeasurable)
    one_le_two



private lemma measurable_gpsum (hmε : ∀ t, Measurable (ε t)) (ψ : ℕ → ℝ) (s : ℤ) (N : ℕ) :
    Measurable (gpsum ψ ε s N) :=
  Finset.measurable_sum _ fun _ _ => (hmε _).const_mul _

/-- **Causal ARMA with i.i.d. Gaussian noise is a Gaussian process** (FY §2.1.3): the
finite-dimensional vectors are `L²`-limits of linear images of Gaussian vectors. -/
theorem isGaussianProcess_of_linearProcess [IsProbabilityMeasure μ]
    {ψ : ℕ → ℝ} {X ε : ℤ → Ω → ℝ}
    (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun n => |ψ n|)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the innovations form an i.i.d. Gaussian family; FY §2.1.3
    (hε : IsIIDNoise ε 1 μ)
    (hgauss : ∀ t, μ.map (ε t) = gaussianReal 0 1) :
    IsGaussianProcess X μ := by

  refine ⟨fun I => ⟨?_⟩⟩
  refine isGaussian_of_map_eq_gaussianReal fun L => ?_
  have hVm : Measurable fun ω => (I.restrict (X · ω) : {x // x ∈ I} → ℝ) :=
    measurable_pi_lambda _ fun b => hmeas _
  obtain ⟨c, hcdef⟩ : ∃ c : {x // x ∈ I} → ℝ,
      ∀ b, c b = L (fun j => if b = j then (1 : ℝ) else 0) := ⟨_, fun _ => rfl⟩
  have hZeq : (⇑L ∘ fun ω => (I.restrict (X · ω) : {x // x ∈ I} → ℝ))
      = fun ω => ∑ b : {x // x ∈ I}, c b * X (b : ℤ) ω := by
    funext ω
    simp only [Function.comp_apply]
    rw [dual_apply_sum L]
    exact Finset.sum_congr rfl fun b _ => by rw [hcdef, mul_comm]; rfl
  rw [Measure.map_map L.continuous.measurable hVm, hZeq]
  have hg : IsGaussian (μ.map fun ω => ∑ b : {x // x ∈ I}, c b * X (b : ℤ) ω) := by
    refine isGaussian_map_of_tendsto_L2
      (fun N => isGaussian_gpsum_comb hε hgauss ψ (fun b : {x // x ∈ I} => (b : ℤ)) c N)
      (fun N => ?_) ?_ (tendsto_eLpNorm_comb hX hmeas hε.measurable _ c)
    · exact (Finset.measurable_sum _ fun b _ =>
        (measurable_gpsum hε.measurable ψ _ N).const_mul _).aestronglyMeasurable
    · exact (Finset.measurable_sum _ fun b _ => (hmeas _).const_mul _).aestronglyMeasurable
  exact ⟨_, _, IsGaussian.eq_gaussianReal _ hg⟩

end LinearGaussian

/-! ### Private machinery for the Wold decomposition (FY eq. (2.6), batch F)

The Hilbert-space half runs in an abstract real Hilbert space `H` over a family `x : ℤ → H`
whose Gram matrix is shift invariant (`⟪x s, x t⟫ = γ (s − t)`): the closed linear spans
`wspan x m` of the past, the innovations `winn x t`, the shift invariance of the innovation
inner products, the Wold coefficients `wpsi`, the MA(∞) part `wsum` and the remote-past
remainder `wdet`. The probabilistic half instantiates `H = L²(μ)` and adds the Gaussian
input: every element of the closed linear span of the process has a Gaussian law, so
uncorrelated families in that span are independent. -/

section WoldHilbert

open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The closed linear span of the past `{x s : s ≤ m}`. -/
private noncomputable def wspan (x : ℤ → H) (m : ℤ) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range fun k : ℕ => x (m - k))).topologicalClosure

private instance instCompleteWspan (x : ℤ → H) (m : ℤ) : CompleteSpace (wspan x m) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

omit [CompleteSpace H] in
private lemma mem_wspan {x : ℤ → H} {m s : ℤ} (h : s ≤ m) : x s ∈ wspan x m := by
  refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(m - s).toNat, ?_⟩)
  simp [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ m - s)]

omit [CompleteSpace H] in
private lemma isClosed_wspan (x : ℤ → H) (m : ℤ) : IsClosed (wspan x m : Set H) :=
  Submodule.isClosed_topologicalClosure _

omit [CompleteSpace H] in
/-- Universal property: any closed submodule containing the past contains `wspan`. -/
private lemma wspan_le {x : ℤ → H} {m : ℤ} {K : Submodule ℝ H} (hK : IsClosed (K : Set H))
    (h : ∀ s ≤ m, x s ∈ K) : wspan x m ≤ K :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h _ (by omega))) hK

omit [CompleteSpace H] in
private lemma wspan_mono (x : ℤ → H) {m m' : ℤ} (h : m ≤ m') : wspan x m ≤ wspan x m' :=
  wspan_le (isClosed_wspan x m') fun _ hs => mem_wspan (by omega)

/-- The innovation at time `t`: `x t` minus its projection on the strict past. -/
private noncomputable def winn (x : ℤ → H) (t : ℤ) : H :=
  x t - (wspan x (t - 1)).starProjection (x t)

private lemma winn_mem_orthogonal (x : ℤ → H) (t : ℤ) : winn x t ∈ (wspan x (t - 1))ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

private lemma inner_winn_of_mem {x : ℤ → H} {t : ℤ} {v : H} (hv : v ∈ wspan x (t - 1)) :
    ⟪winn x t, v⟫ = 0 := by
  rw [real_inner_comm]; exact (winn_mem_orthogonal x t) v hv

private lemma winn_mem (x : ℤ → H) (t : ℤ) : winn x t ∈ wspan x t :=
  Submodule.sub_mem _ (mem_wspan le_rfl)
    (wspan_mono x (by omega) (Submodule.starProjection_apply_mem _ _))

private lemma inner_winn_winn {x : ℤ → H} {s t : ℤ} (h : s ≠ t) : ⟪winn x s, winn x t⟫ = 0 := by
  rcases lt_or_gt_of_ne h with hst | hst
  · rw [real_inner_comm]
    exact inner_winn_of_mem (wspan_mono x (by omega) (winn_mem x s))
  · exact inner_winn_of_mem (wspan_mono x (by omega) (winn_mem x t))

omit [CompleteSpace H] in
/-- Pythagoras for the orthogonal projection onto a subspace. -/
private lemma norm_sub_sq_starProjection (K : Submodule ℝ H) [K.HasOrthogonalProjection] (y : H)
    {w : H} (hw : w ∈ K) :
    ‖y - w‖ ^ 2 = ‖y - K.starProjection y‖ ^ 2 + ‖K.starProjection y - w‖ ^ 2 := by
  have hsum : y - w = (y - K.starProjection y) + (K.starProjection y - w) := by abel
  have hmem : K.starProjection y - w ∈ K :=
    Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ _) hw
  have hzero : ⟪y - K.starProjection y, K.starProjection y - w⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.sub_starProjection_mem_orthogonal (K := K) y) _ hmem
  rw [hsum, norm_add_sq_real, hzero]
  ring

omit [CompleteSpace H] in
private lemma norm_sub_starProjection_le (K : Submodule ℝ H) [K.HasOrthogonalProjection] (y : H)
    {w : H} (hw : w ∈ K) : ‖y - K.starProjection y‖ ≤ ‖y - w‖ := by
  have h := norm_sub_sq_starProjection K y hw
  nlinarith [norm_nonneg (y - w), norm_nonneg (y - K.starProjection y),
    norm_nonneg (K.starProjection y - w), sq_nonneg ‖K.starProjection y - w‖]


/-! ### Transfer of the Gram structure under time shifts -/

/-- A finite linear combination of the past `{x (a - k) : k : ℕ}` with coefficients `c`. -/
private noncomputable def lincomb (x : ℤ → H) (a : ℤ) (c : ℕ →₀ ℝ) : H :=
  ∑ k ∈ c.support, c k • x (a - k)

omit [CompleteSpace H] in
private lemma mem_span_past_iff (x : ℤ → H) (a : ℤ) (v : H) :
    v ∈ Submodule.span ℝ (Set.range fun k : ℕ => x (a - k)) ↔
      ∃ c : ℕ →₀ ℝ, lincomb x a c = v :=
  Finsupp.mem_span_range_iff_exists_finsupp

omit [CompleteSpace H] in
private lemma lincomb_mem_wspan (x : ℤ → H) (a : ℤ) (c : ℕ →₀ ℝ) : lincomb x a c ∈ wspan x a :=
  Submodule.le_topologicalClosure _ ((mem_span_past_iff x a _).2 ⟨c, rfl⟩)

variable {x : ℤ → H} {γ : ℤ → ℝ}

omit [CompleteSpace H] in
private lemma inner_x_lincomb (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (u a : ℤ) (c : ℕ →₀ ℝ) :
    ⟪x u, lincomb x a c⟫ = ∑ k ∈ c.support, c k * γ (u - a + k) := by
  rw [lincomb, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_right, hγ]
  have h : u - (a - (k : ℤ)) = u - a + k := by omega
  rw [h]

omit [CompleteSpace H] in
private lemma inner_lincomb_lincomb (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (a : ℤ)
    (c c' : ℕ →₀ ℝ) :
    ⟪lincomb x a c, lincomb x a c'⟫
      = ∑ k ∈ c.support, ∑ l ∈ c'.support, c k * c' l * γ ((l : ℤ) - k) := by
  rw [lincomb, lincomb, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [real_inner_smul_right, hγ]
  have h : a - (k : ℤ) - (a - (l : ℤ)) = (l : ℤ) - k := by omega
  rw [h]; ring

omit [CompleteSpace H] in
/-- Shift-transfer of the inner products against the innovation residual. -/
private lemma inner_res_transfer (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (a b v : ℤ) (c : ℕ →₀ ℝ) :
    ⟪x (a + v), x a - lincomb x (a - 1) c⟫ = ⟪x (b + v), x b - lincomb x (b - 1) c⟫ := by
  rw [inner_sub_right, inner_sub_right, hγ, hγ, inner_x_lincomb hγ, inner_x_lincomb hγ]
  have h1 : a + v - a = v := by omega
  have h2 : b + v - b = v := by omega
  have h3 : a + v - (a - 1) = v + 1 := by omega
  have h4 : b + v - (b - 1) = v + 1 := by omega
  rw [h1, h2, h3, h4]

omit [CompleteSpace H] in
/-- Shift-transfer of the norm of the innovation residual. -/
private lemma norm_res_transfer (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (a b : ℤ) (c : ℕ →₀ ℝ) :
    ‖x a - lincomb x (a - 1) c‖ = ‖x b - lincomb x (b - 1) c‖ := by
  have e : ∀ u : ℤ, ⟪x u - lincomb x (u - 1) c, x u - lincomb x (u - 1) c⟫
      = γ 0 - 2 * (∑ k ∈ c.support, c k * γ (1 + k))
        + ∑ k ∈ c.support, ∑ l ∈ c.support, c k * c l * γ ((l : ℤ) - k) := by
    intro u
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm (x u) (lincomb x (u - 1) c), hγ, inner_x_lincomb hγ,
      inner_lincomb_lincomb hγ]
    have h5 : u - u = (0 : ℤ) := by omega
    have h6 : u - (u - 1) = (1 : ℤ) := by omega
    rw [h5, h6]
    ring
  have h := (e a).trans (e b).symm
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (x a - lincomb x (a - 1) c), norm_nonneg (x b - lincomb x (b - 1) c)]

/-! ### Shift invariance of the innovations -/

omit [CompleteSpace H] in
private lemma coe_wspan (x : ℤ → H) (m : ℤ) :
    ((wspan x m : Submodule ℝ H) : Set H)
      = closure ((Submodule.span ℝ (Set.range fun k : ℕ => x (m - k)) : Submodule ℝ H) : Set H) :=
  Submodule.topologicalClosure_coe _

/-- Approximation of the projection onto the past by an explicit finite linear combination. -/
private lemma exists_lincomb_approx (b : ℤ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ →₀ ℝ, ‖(wspan x (b - 1)).starProjection (x b) - lincomb x (b - 1) c‖ < δ := by
  have hmem : (wspan x (b - 1)).starProjection (x b) ∈ wspan x (b - 1) :=
    Submodule.starProjection_apply_mem _ _
  rw [← SetLike.mem_coe, coe_wspan, Metric.mem_closure_iff] at hmem
  obtain ⟨w, hw, hwd⟩ := hmem δ hδ
  obtain ⟨c, rfl⟩ := (mem_span_past_iff x (b - 1) w).1 hw
  exact ⟨c, by rwa [dist_eq_norm] at hwd⟩

private lemma norm_winn_le (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (a b : ℤ) :
    ‖winn x a‖ ≤ ‖winn x b‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨c, hc⟩ := exists_lincomb_approx (x := x) b hε
  have hb : ‖x b - lincomb x (b - 1) c‖ ≤ ‖winn x b‖ + ε := by
    have hsplit : x b - lincomb x (b - 1) c
        = winn x b + ((wspan x (b - 1)).starProjection (x b) - lincomb x (b - 1) c) := by
      rw [winn]; abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (by linarith)
  have ha : ‖winn x a‖ ≤ ‖x a - lincomb x (a - 1) c‖ :=
    norm_sub_starProjection_le _ _ (lincomb_mem_wspan x (a - 1) c)
  rw [norm_res_transfer hγ a b c] at ha
  linarith

private lemma norm_winn_eq (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (a b : ℤ) :
    ‖winn x a‖ = ‖winn x b‖ :=
  le_antisymm (norm_winn_le hγ a b) (norm_winn_le hγ b a)

/-- **Shift invariance of the innovation inner products.** -/
private lemma inner_x_winn_transfer (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (a b v : ℤ) :
    ⟪x (a + v), winn x a⟫ = ⟪x (b + v), winn x b⟫ := by
  set M := ‖x (a + v)‖ + ‖x (b + v)‖ + 1 with hM
  have hMpos : (0 : ℝ) < M := by positivity
  have key : ∀ ε > 0, |⟪x (a + v), winn x a⟫ - ⟪x (b + v), winn x b⟫| ≤ ε := by
    intro ε hε
    have hδ : 0 < ε / M := by positivity
    set δ := ε / M with hδdef
    obtain ⟨c, hc⟩ := exists_lincomb_approx (x := x) b hδ
    have hpythb := norm_sub_sq_starProjection (wspan x (b - 1)) (x b)
      (lincomb_mem_wspan x (b - 1) c)
    have hpytha := norm_sub_sq_starProjection (wspan x (a - 1)) (x a)
      (lincomb_mem_wspan x (a - 1) c)
    have hnormeq : ‖x a - lincomb x (a - 1) c‖ ^ 2 = ‖x b - lincomb x (b - 1) c‖ ^ 2 := by
      rw [norm_res_transfer hγ a b c]
    have hW : ‖x a - (wspan x (a - 1)).starProjection (x a)‖ ^ 2
        = ‖x b - (wspan x (b - 1)).starProjection (x b)‖ ^ 2 := by
      have h := norm_winn_eq hγ a b
      simp only [winn] at h
      rw [h]
    have hb2 : ‖(wspan x (b - 1)).starProjection (x b) - lincomb x (b - 1) c‖ ^ 2 ≤ δ ^ 2 := by
      nlinarith [norm_nonneg ((wspan x (b - 1)).starProjection (x b) - lincomb x (b - 1) c)]
    have hda : ‖(wspan x (a - 1)).starProjection (x a) - lincomb x (a - 1) c‖ ≤ δ := by
      have h1 : ‖(wspan x (a - 1)).starProjection (x a) - lincomb x (a - 1) c‖ ^ 2 ≤ δ ^ 2 := by
        linarith
      nlinarith [norm_nonneg ((wspan x (a - 1)).starProjection (x a) - lincomb x (a - 1) c)]
    have ea : ⟪x (a + v), winn x a⟫ - ⟪x (a + v), x a - lincomb x (a - 1) c⟫
        = ⟪x (a + v), lincomb x (a - 1) c - (wspan x (a - 1)).starProjection (x a)⟫ := by
      rw [← inner_sub_right, winn]; congr 1; abel
    have eb : ⟪x (b + v), winn x b⟫ - ⟪x (b + v), x b - lincomb x (b - 1) c⟫
        = ⟪x (b + v), lincomb x (b - 1) c - (wspan x (b - 1)).starProjection (x b)⟫ := by
      rw [← inner_sub_right, winn]; congr 1; abel
    have ba : |⟪x (a + v), winn x a⟫ - ⟪x (a + v), x a - lincomb x (a - 1) c⟫|
        ≤ ‖x (a + v)‖ * δ := by
      rw [ea]
      refine (abs_real_inner_le_norm _ _).trans ?_
      gcongr
      rw [norm_sub_rev]; exact hda
    have bb : |⟪x (b + v), winn x b⟫ - ⟪x (b + v), x b - lincomb x (b - 1) c⟫|
        ≤ ‖x (b + v)‖ * δ := by
      rw [eb]
      refine (abs_real_inner_le_norm _ _).trans ?_
      gcongr
      rw [norm_sub_rev]; exact le_of_lt hc
    have hmid := inner_res_transfer hγ a b v c
    have ba' := abs_le.1 ba
    have bb' := abs_le.1 bb
    have hfin : ‖x (a + v)‖ * δ + ‖x (b + v)‖ * δ ≤ ε := by
      have h1 : ‖x (a + v)‖ + ‖x (b + v)‖ ≤ M := by rw [hM]; linarith
      have h2 : (‖x (a + v)‖ + ‖x (b + v)‖) * δ ≤ M * δ :=
        mul_le_mul_of_nonneg_right h1 hδ.le
      have h3 : M * δ = ε := by rw [hδdef]; field_simp
      nlinarith
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [ba'.1, ba'.2, bb'.1, bb'.2]
  have h0 : |⟪x (a + v), winn x a⟫ - ⟪x (b + v), winn x b⟫| ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using key ε hε
  have h1 := abs_nonpos_iff.1 h0
  linarith [h1]

/-! ### The Wold coefficients and the MA(∞) part -/

omit [CompleteSpace H] in
/-- Orthogonal Pythagoras for a finite sum. -/
private lemma norm_sum_sq_orthogonal {u : ℕ → H} (hu : ∀ i j, i ≠ j → ⟪u i, u j⟫ = 0)
    (s : Finset ℕ) :
    ‖∑ i ∈ s, u i‖ ^ 2 = ∑ i ∈ s, ‖u i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]
  · intro b _ hb; exact hu i b (Ne.symm hb)
  · intro h; exact absurd hi h

/-- The innovation variance. -/
private noncomputable def wsig (x : ℤ → H) : ℝ := ‖winn x 0‖ ^ 2

/-- The Wold coefficients. -/
private noncomputable def wpsi (x : ℤ → H) (j : ℕ) : ℝ := ⟪x 0, winn x (-(j : ℤ))⟫ / wsig x

private lemma wsig_nonneg (x : ℤ → H) : 0 ≤ wsig x := sq_nonneg _

private lemma norm_winn_sq (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) :
    ‖winn x t‖ ^ 2 = wsig x := by rw [wsig, norm_winn_eq hγ t 0]

private lemma winn_eq_zero (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (h : wsig x = 0) (t : ℤ) :
    winn x t = 0 := by
  have h2 : ‖winn x t‖ ^ 2 = 0 := by rw [norm_winn_sq hγ, h]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  exact norm_eq_zero.1 this

private lemma inner_x_winn (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) (j : ℕ) :
    ⟪x t, winn x (t - (j : ℤ))⟫ = wpsi x j * wsig x := by
  have h := inner_x_winn_transfer hγ (t - (j : ℤ)) (-(j : ℤ)) (j : ℤ)
  have e1 : t - (j : ℤ) + (j : ℤ) = t := by omega
  have e2 : -(j : ℤ) + (j : ℤ) = 0 := by omega
  rw [e1, e2] at h
  rw [h, wpsi]
  rcases eq_or_ne (wsig x) 0 with hz | hz
  · rw [hz, div_zero, zero_mul, winn_eq_zero hγ hz, inner_zero_right]
  · field_simp

/-- Bessel's inequality for the Wold coefficients. -/
private lemma sum_sq_wpsi_mul_le (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (N : ℕ) :
    (∑ j ∈ Finset.range N, wpsi x j ^ 2) * wsig x ≤ ‖x 0‖ ^ 2 := by
  set w : H := ∑ j ∈ Finset.range N, wpsi x j • winn x (0 - (j : ℤ)) with hw
  have horth : ∀ i j : ℕ, i ≠ j →
      ⟪wpsi x i • winn x (0 - (i : ℤ)), wpsi x j • winn x (0 - (j : ℤ))⟫ = 0 := by
    intro i j hij
    rw [real_inner_smul_left, real_inner_smul_right,
      inner_winn_winn (x := x) (by omega : (0 : ℤ) - i ≠ (0 : ℤ) - j)]
    ring
  have h1 : ⟪x 0, w⟫ = (∑ j ∈ Finset.range N, wpsi x j ^ 2) * wsig x := by
    rw [hw, inner_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, inner_x_winn hγ 0 j]
    ring
  have h2 : ‖w‖ ^ 2 = (∑ j ∈ Finset.range N, wpsi x j ^ 2) * wsig x := by
    rw [hw, norm_sum_sq_orthogonal horth, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_winn_sq hγ]
  have h3 : ⟪x 0, w⟫ ≤ ‖x 0‖ * ‖w‖ := real_inner_le_norm _ _
  nlinarith [norm_nonneg (x 0), norm_nonneg w, h1, h2, h3]

private lemma summable_wpsi_sq (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) :
    Summable fun j : ℕ => wpsi x j ^ 2 := by
  rcases eq_or_ne (wsig x) 0 with hz | hz
  · have : ∀ j : ℕ, wpsi x j ^ 2 = 0 := by
      intro j; rw [wpsi, hz, div_zero]; ring
    simp [this]
  · have hpos : 0 < wsig x := lt_of_le_of_ne (wsig_nonneg x) (Ne.symm hz)
    refine summable_of_sum_range_le (fun j => sq_nonneg _) (c := ‖x 0‖ ^ 2 / wsig x) fun N => ?_
    rw [le_div_iff₀ hpos]
    exact sum_sq_wpsi_mul_le hγ N

/-! ### The MA(∞) part and the deterministic remainder -/

/-- Partial sums of the Wold series. -/
private noncomputable def wpartial (x : ℤ → H) (t : ℤ) (n : ℕ) : H :=
  ∑ j ∈ Finset.range n, wpsi x j • winn x (t - (j : ℤ))

/-- The MA(∞) part of the Wold decomposition. -/
private noncomputable def wsum (x : ℤ → H) (t : ℤ) : H := limUnder atTop (wpartial x t)

/-- The deterministic remainder of the Wold decomposition. -/
private noncomputable def wdet (x : ℤ → H) (t : ℤ) : H := x t - wsum x t

private lemma horth_winn (x : ℤ → H) (t : ℤ) : ∀ i j : ℕ, i ≠ j →
    ⟪wpsi x i • winn x (t - (i : ℤ)), wpsi x j • winn x (t - (j : ℤ))⟫ = 0 := by
  intro i j hij
  rw [real_inner_smul_left, real_inner_smul_right,
    inner_winn_winn (x := x) (by omega : t - (i : ℤ) ≠ t - (j : ℤ))]
  ring

private lemma norm_wpartial_sub (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) {m n : ℕ}
    (h : n ≤ m) :
    ‖wpartial x t m - wpartial x t n‖ ^ 2
      = ((∑ j ∈ Finset.range m, wpsi x j ^ 2) - ∑ j ∈ Finset.range n, wpsi x j ^ 2) * wsig x := by
  have hsub : wpartial x t m - wpartial x t n
      = ∑ j ∈ Finset.Ico n m, wpsi x j • winn x (t - (j : ℤ)) := by
    rw [wpartial, wpartial, Finset.sum_Ico_eq_sub _ h]
  have hterm : ∀ k : ℕ, ‖wpsi x k • winn x (t - (k : ℤ))‖ ^ 2 = wpsi x k ^ 2 * wsig x := by
    intro k
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_winn_sq hγ]
  rw [hsub, norm_sum_sq_orthogonal (horth_winn x t), Finset.sum_Ico_eq_sub _ h]
  simp only [hterm]
  rw [sub_mul, Finset.sum_mul, Finset.sum_mul]

private lemma cauchySeq_wpartial (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) :
    CauchySeq (wpartial x t) := by
  have hσ : (0 : ℝ) < wsig x + 1 := by linarith [wsig_nonneg x]
  rw [NormedAddCommGroup.cauchySeq_iff]
  intro ε hε
  have hC : CauchySeq fun n => ∑ j ∈ Finset.range n, wpsi x j ^ 2 :=
    (summable_wpsi_sq hγ).hasSum.tendsto_sum_nat.cauchySeq
  rw [NormedAddCommGroup.cauchySeq_iff] at hC
  obtain ⟨N, hN⟩ := hC (ε ^ 2 / (wsig x + 1)) (by positivity)
  have key : ∀ p q : ℕ, N ≤ p → N ≤ q → q ≤ p → ‖wpartial x t p - wpartial x t q‖ < ε := by
    intro p q hp hq hqp
    have h1 := norm_wpartial_sub hγ t hqp
    have h2 := hN p hp q hq
    rw [Real.norm_eq_abs] at h2
    have h3 : ((∑ j ∈ Finset.range p, wpsi x j ^ 2)
        - ∑ j ∈ Finset.range q, wpsi x j ^ 2) * wsig x < ε ^ 2 := by
      have h4 : ((∑ j ∈ Finset.range p, wpsi x j ^ 2)
          - ∑ j ∈ Finset.range q, wpsi x j ^ 2) ≤ ε ^ 2 / (wsig x + 1) := by
        have h2' := abs_lt.1 h2
        linarith [h2'.1, h2'.2]
      have h5 : ε ^ 2 / (wsig x + 1) * wsig x < ε ^ 2 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hσ]
        nlinarith [wsig_nonneg x, sq_nonneg ε, hε]
      nlinarith [wsig_nonneg x]
    nlinarith [norm_nonneg (wpartial x t p - wpartial x t q), hε]
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [neg_add_eq_sub]
  rcases le_total n m with h | h
  · rw [norm_sub_rev]; exact key m n hm hn h
  · exact key n m hn hm h

private lemma tendsto_wpartial (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) :
    Tendsto (wpartial x t) atTop (𝓝 (wsum x t)) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_wpartial hγ t)
  rw [wsum, hL.limUnder_eq]
  exact hL

/-! ### Orthogonality and remote-past membership of the deterministic part -/

omit [CompleteSpace H] in
private lemma mem_orthogonal_wspan {u : H} {m : ℤ} (h : ∀ s ≤ m, ⟪x s, u⟫ = 0) :
    u ∈ (wspan x m)ᗮ := by
  have hle : wspan x m ≤ (ℝ ∙ u)ᗮ := by
    refine wspan_le (Submodule.isClosed_orthogonal _) fun s hs => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact h s hs
  intro v hv
  have hv' := hle hv
  rwa [Submodule.mem_orthogonal_singleton_iff_inner_left] at hv'

private lemma inner_winn_wpartial (x : ℤ → H) (t : ℤ) (n : ℕ) :
    ⟪winn x (t - (n : ℤ)), wpartial x t n⟫ = 0 := by
  rw [wpartial, inner_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  rw [real_inner_smul_right, inner_winn_winn (x := x) (by omega : t - (n : ℤ) ≠ t - (i : ℤ)),
    mul_zero]

private lemma wpartial_mem_orthogonal (x : ℤ → H) (t : ℤ) (n : ℕ) :
    wpartial x t n ∈ (wspan x (t - (n : ℤ) - 1))ᗮ := by
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  refine Submodule.smul_mem _ _ ?_
  intro v hv
  rw [← real_inner_comm]
  exact inner_winn_of_mem (wspan_mono x (by omega) hv)

/-- The projection of `x t` on the past `t - n` is the `n`-th Wold residual. -/
private lemma wpartial_mem (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) (n : ℕ) :
    x t - wpartial x t n ∈ wspan x (t - (n : ℤ)) := by
  induction n with
  | zero => simpa [wpartial] using mem_wspan (x := x) (m := t) le_rfl
  | succ n ih =>
    set z := x t - wpartial x t n with hz
    set Q := (wspan x (t - (n : ℤ) - 1)).starProjection z with hQ
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have hnext : x t - wpartial x t (n + 1) = z - wpsi x n • winn x (t - (n : ℤ)) := by
      rw [hz, wpartial, wpartial, Finset.sum_range_succ]; abel
    set u := z - Q - wpsi x n • winn x (t - (n : ℤ)) with hu
    -- `u` lies in the span of the past up to `t - n`
    have hQmem : Q ∈ wspan x (t - (n : ℤ) - 1) := Submodule.starProjection_apply_mem _ _
    have humem : u ∈ wspan x (t - (n : ℤ)) := by
      refine Submodule.sub_mem _ (Submodule.sub_mem _ ih ?_) (Submodule.smul_mem _ _ ?_)
      · exact wspan_mono x (by omega) hQmem
      · exact winn_mem x _
    -- `u` is orthogonal to the strict past
    have hperp1 : ∀ v ∈ wspan x (t - (n : ℤ) - 1), ⟪v, u⟫ = 0 := by
      intro v hv
      have h1 : ⟪v, z - Q⟫ = 0 := by
        have := Submodule.sub_starProjection_mem_orthogonal
          (K := wspan x (t - (n : ℤ) - 1)) z
        exact this v hv
      have h2 : ⟪v, winn x (t - (n : ℤ))⟫ = 0 := by
        rw [← real_inner_comm]
        exact inner_winn_of_mem (by simpa using hv)
      rw [hu, show z - Q - wpsi x n • winn x (t - (n : ℤ))
        = (z - Q) - wpsi x n • winn x (t - (n : ℤ)) from rfl, inner_sub_right,
        real_inner_smul_right, h1, h2]
      ring
    have hperp2 : ⟪winn x (t - (n : ℤ)), u⟫ = 0 := by
      have hzin : ⟪winn x (t - (n : ℤ)), z⟫ = wpsi x n * wsig x := by
        rw [hz, inner_sub_right, inner_winn_wpartial, ← real_inner_comm, inner_x_winn hγ]
        ring
      have hQin : ⟪winn x (t - (n : ℤ)), Q⟫ = 0 := inner_winn_of_mem (by simpa using hQmem)
      have hself : ⟪winn x (t - (n : ℤ)), winn x (t - (n : ℤ))⟫ = wsig x := by
        rw [real_inner_self_eq_norm_sq, norm_winn_sq hγ]
      rw [hu, inner_sub_right, inner_sub_right, real_inner_smul_right, hzin, hQin, hself]
      ring
    have huperp : u ∈ (wspan x (t - (n : ℤ)))ᗮ := by
      refine mem_orthogonal_wspan fun s hs => ?_
      rcases eq_or_lt_of_le hs with heq | hlt
      · have hsplit : x (t - (n : ℤ)) = winn x (t - (n : ℤ))
            + (wspan x (t - (n : ℤ) - 1)).starProjection (x (t - (n : ℤ))) := by
          rw [winn]; abel
        rw [heq, hsplit, inner_add_left, hperp2,
          hperp1 _ (Submodule.starProjection_apply_mem _ _)]
        ring
      · exact hperp1 _ (mem_wspan (by omega))
    have hu0 : u = 0 := by
      have := huperp u humem
      simpa using inner_self_eq_zero.1 this
    have hQeq : z - wpsi x n • winn x (t - (n : ℤ)) = Q := by
      rw [hu] at hu0
      have h' : z - wpsi x n • winn x (t - (n : ℤ)) - Q = 0 := by rw [← hu0]; abel
      exact sub_eq_zero.1 h'
    rw [hcast, ← sub_sub, hnext, hQeq]
    exact hQmem

private lemma wpartial_mem_wspan (x : ℤ → H) (t : ℤ) (n : ℕ) : wpartial x t n ∈ wspan x t :=
  Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (wspan_mono x (by omega) (winn_mem x (t - (i : ℤ))))

private lemma wsum_mem (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) : wsum x t ∈ wspan x t :=
  (isClosed_wspan x t).mem_of_tendsto (tendsto_wpartial hγ t)
    (Eventually.of_forall fun n => wpartial_mem_wspan x t n)

/-- The deterministic part lives in the remote past. -/
private lemma wdet_mem (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) (N : ℕ) :
    wdet x t ∈ wspan x (t - (N : ℤ)) := by
  have htend : Tendsto (fun n => x t - wpartial x t n) atTop (𝓝 (wdet x t)) :=
    (tendsto_wpartial hγ t).const_sub _
  refine (isClosed_wspan x (t - (N : ℤ))).mem_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact wspan_mono x (by omega) (wpartial_mem hγ t n)

private lemma inner_wsum_winn (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t : ℤ) (j : ℕ) :
    ⟪wsum x t, winn x (t - (j : ℤ))⟫ = wpsi x j * wsig x := by
  have h1 : Tendsto (fun n => ⟪wpartial x t n, winn x (t - (j : ℤ))⟫) atTop
      (𝓝 ⟪wsum x t, winn x (t - (j : ℤ))⟫) :=
    (tendsto_wpartial hγ t).inner tendsto_const_nhds
  have h2 : (fun n => ⟪wpartial x t n, winn x (t - (j : ℤ))⟫)
      =ᶠ[atTop] fun _ => wpsi x j * wsig x := by
    filter_upwards [eventually_gt_atTop j] with n hn
    rw [wpartial, sum_inner, Finset.sum_eq_single j]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_winn_sq hγ]
    · intro b _ hb
      rw [real_inner_smul_left, inner_winn_winn (x := x)
        (by omega : t - (b : ℤ) ≠ t - (j : ℤ)), mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 hn) h
  exact tendsto_nhds_unique h1 (Tendsto.congr' h2.symm tendsto_const_nhds)

/-- The deterministic part is orthogonal to every innovation. -/
private lemma inner_wdet_winn (hγ : ∀ s t : ℤ, ⟪x s, x t⟫ = γ (s - t)) (t s : ℤ) :
    ⟪wdet x t, winn x s⟫ = 0 := by
  rcases le_or_gt s t with hst | hst
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = t - (j : ℤ) := ⟨(t - s).toNat, by omega⟩
    rw [wdet, inner_sub_left, inner_x_winn hγ, inner_wsum_winn hγ, sub_self]
  · have h0 : wdet x t ∈ wspan x t := by simpa using wdet_mem hγ t 0
    have hmem : wdet x t ∈ wspan x (s - 1) := wspan_mono x (by omega) h0
    rw [← real_inner_comm]
    exact inner_winn_of_mem hmem

end WoldHilbert


/-! ## The probabilistic layer -/

section WoldProb

open scoped RealInnerProductSpace

/-- Real `L²` inner product in coordinates. -/
private lemma winner_mul (a b : ℝ) : inner ℝ a b = a * b := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

private lemma coeFn_lp_sum {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    ((∑ i ∈ s, f i : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] fun ω => ∑ i ∈ s, (f i : Ω → ℝ) ω := by
  classical
  induction s using Finset.induction with
  | empty => simpa using! Lp.coeFn_zero ℝ 2 μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with ω h1 h2
    rw [h1]
    simp only [Pi.add_apply, h2]
    rw [Finset.sum_insert ha]

/-- The `L²` inner product of two classes is the integral of the product of representatives. -/
private lemma inner_lp_eq_integral (f g : Lp ℝ 2 μ) {F G : Ω → ℝ}
    (hF : (f : Ω → ℝ) =ᵐ[μ] F) (hG : (g : Ω → ℝ) =ᵐ[μ] G) :
    ⟪f, g⟫ = ∫ ω, F ω * G ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF, hG] with ω h1 h2
  rw [winner_mul, h1, h2]

/-- The Gram identity: the `L²` classes of a centred stationary process have the ACVF as
Gram matrix. -/
private lemma inner_lpProc [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ} (hstat : IsStationary X μ)
    (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0) {x : ℤ → Lp ℝ 2 μ} (hx : ∀ t, (x t : Ω → ℝ) =ᵐ[μ] X t)
    (s t : ℤ) : ⟪x s, x t⟫ = acvf X μ (s - t) := by
  rw [inner_lp_eq_integral (x s) (x t) (hx s) (hx t)]
  have h2 : cov[X s, X t; μ] = ∫ ω, X s ω * X t ω ∂μ := by
    rw [covariance_eq_sub (hstat.memLp s) (hstat.memLp t), hmean s, hmean t]
    simp
  rw [← h2]
  have h3 := hstat.cov_shift t (s - t)
  rw [show t + (s - t) = s by ring] at h3
  rw [h3, acvf]

/-- The Gaussian space: the closed linear span of the whole process. -/
private noncomputable def gspan (x : ℤ → Lp ℝ 2 μ) : Submodule ℝ (Lp ℝ 2 μ) :=
  (Submodule.span ℝ (Set.range x)).topologicalClosure

private lemma wspan_le_gspan (x : ℤ → Lp ℝ 2 μ) (m : ℤ) : wspan x m ≤ gspan x :=
  wspan_le (Submodule.isClosed_topologicalClosure _)
    fun s _ => Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨s, rfl⟩)

private lemma isGaussian_finsum [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hG : IsGaussianProcess X μ) (s : Finset ℤ) (c : ℤ → ℝ) :
    IsGaussian (μ.map fun ω => ∑ i ∈ s, c i * X i ω) := by
  classical
  let L : ({i // i ∈ s} → ℝ) →L[ℝ] ℝ :=
    { toFun := fun v => ∑ i : {i // i ∈ s}, c i * v i
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      cont := by fun_prop }
  have heq : (fun ω => ∑ i ∈ s, c i * X i ω)
      = fun ω => L (s.restrict (X · ω)) := by
    funext ω
    exact (Finset.sum_coe_sort s fun i => c i * X i ω).symm
  rw [heq]
  exact ((hG.hasGaussianLaw s).map_fun L).isGaussian_map

/-- **Every element of the Gaussian space has a Gaussian law.** -/
private lemma isGaussian_of_mem_gspan [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hG : IsGaussianProcess X μ) {x : ℤ → Lp ℝ 2 μ} (hx : ∀ t, (x t : Ω → ℝ) =ᵐ[μ] X t)
    {g : Lp ℝ 2 μ} (hg : g ∈ gspan x) : IsGaussian (μ.map (g : Ω → ℝ)) := by
  classical
  have hspan : ∀ v ∈ Submodule.span ℝ (Set.range x), IsGaussian (μ.map (v : Ω → ℝ)) := by
    intro v hv
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
    have hae : ((c.sum fun i r => r • x i : Lp ℝ 2 μ) : Ω → ℝ)
        =ᵐ[μ] fun ω => ∑ i ∈ c.support, c i * X i ω := by
      have h1 := coeFn_lp_sum c.support fun i => c i • x i
      have h2 : ∀ᵐ ω ∂μ, ∀ i ∈ c.support, ((c i • x i : Lp ℝ 2 μ) : Ω → ℝ) ω = c i * X i ω := by
        rw [ae_all_iff]
        intro i
        rw [ae_all_iff]
        intro _
        filter_upwards [Lp.coeFn_smul (c i) (x i), hx i] with ω hω hω'
        rw [hω]
        simp [hω']
      filter_upwards [h1, h2] with ω hω hω'
      rw [Finsupp.sum]
      rw [hω]
      exact Finset.sum_congr rfl fun i hi => hω' i hi
    rw [Measure.map_congr hae]
    exact isGaussian_finsum hG c.support fun i => c i
  rw [← SetLike.mem_coe, gspan, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hg
  obtain ⟨u, hu, hulim⟩ := hg
  refine isGaussian_map_of_tendsto_L2 (Y := fun n => ((u n : Lp ℝ 2 μ) : Ω → ℝ))
    (fun n => hspan _ (hu n)) (fun n => (Lp.stronglyMeasurable _).aestronglyMeasurable)
    (Lp.stronglyMeasurable _).aestronglyMeasurable ?_
  have heq : ∀ n, eLpNorm (((u n : Lp ℝ 2 μ) : Ω → ℝ) - (g : Ω → ℝ)) 2 μ
      = ENNReal.ofReal ‖u n - g‖ := by
    intro n
    rw [eLpNorm_congr_ae (Lp.coeFn_sub (u n) g).symm, Lp.norm_def,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (u n - g))]
  have hreal : Tendsto (fun n => ‖u n - g‖) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => u n - g) atTop (𝓝 (g - g)) :=
      hulim.sub (tendsto_const_nhds (x := g))
    rw [sub_self] at h0
    simpa using h0.norm
  have hfin : Tendsto (fun N => ENNReal.ofReal ‖u N - g‖) atTop (𝓝 0) := by
    have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    rw [ENNReal.ofReal_zero] at h1
    exact h1
  exact Tendsto.congr (fun N => (heq N).symm) hfin

/-- A finite linear combination of `L²` classes, in coordinates. -/
private lemma coeFn_lp_lincomb {ι : Type*} (s : Finset ι) (c : ι → ℝ) (z : ι → Lp ℝ 2 μ)
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Z i =ᵐ[μ] (z i : Ω → ℝ)) :
    ((∑ i ∈ s, c i • z i : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] fun ω => ∑ i ∈ s, c i * Z i ω := by
  have h1 := coeFn_lp_sum s fun i => c i • z i
  have h2 : ∀ᵐ ω ∂μ, ∀ i ∈ s, ((c i • z i : Lp ℝ 2 μ) : Ω → ℝ) ω = c i * Z i ω := by
    rw [Filter.eventually_all_finset]
    intro i _
    filter_upwards [Lp.coeFn_smul (c i) (z i), hZ i] with ω hω hω'
    rw [hω]
    simp [hω']
  filter_upwards [h1, h2] with ω hω hω'
  rw [hω]
  exact Finset.sum_congr rfl fun i hi => hω' i hi

/-- **A family of elements of the Gaussian space is a Gaussian process.** -/
private lemma isGaussianProcess_of_mem_gspan [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hG : IsGaussianProcess X μ) {x : ℤ → Lp ℝ 2 μ} (hx : ∀ t, (x t : Ω → ℝ) =ᵐ[μ] X t)
    {ι : Type*} {Z : ι → Ω → ℝ} (z : ι → Lp ℝ 2 μ)
    (hz : ∀ i, z i ∈ gspan x) (hZ : ∀ i, Z i =ᵐ[μ] (z i : Ω → ℝ))
    (hZm : ∀ i, Measurable (Z i)) :
    IsGaussianProcess Z μ := by
  classical
  refine ⟨fun I => ⟨?_⟩⟩
  refine isGaussian_of_map_eq_gaussianReal fun L => ?_
  have hVm : Measurable fun ω => (I.restrict (Z · ω) : {i // i ∈ I} → ℝ) :=
    measurable_pi_lambda _ fun b => hZm _
  obtain ⟨c, hcdef⟩ : ∃ c : {i // i ∈ I} → ℝ,
      ∀ b, c b = L (fun j => if b = j then (1 : ℝ) else 0) := ⟨_, fun _ => rfl⟩
  have hZeq : (⇑L ∘ fun ω => (I.restrict (Z · ω) : {i // i ∈ I} → ℝ))
      = fun ω => ∑ b : {i // i ∈ I}, c b * Z (b : ι) ω := by
    funext ω
    simp only [Function.comp_apply]
    rw [dual_apply_sum L]
    exact Finset.sum_congr rfl fun b _ => by rw [hcdef, mul_comm]; rfl
  rw [Measure.map_map L.continuous.measurable hVm, hZeq]
  have hae : ((∑ b : {i // i ∈ I}, c b • z (b : ι) : Lp ℝ 2 μ) : Ω → ℝ)
      =ᵐ[μ] fun ω => ∑ b : {i // i ∈ I}, c b * Z (b : ι) ω :=
    coeFn_lp_lincomb Finset.univ c (fun b : {i // i ∈ I} => z (b : ι))
      (fun b : {i // i ∈ I} => Z (b : ι)) fun b => hZ _
  have hg : IsGaussian (μ.map fun ω => ∑ b : {i // i ∈ I}, c b * Z (b : ι) ω) := by
    rw [← Measure.map_congr hae]
    exact isGaussian_of_mem_gspan hG hx
      (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hz _))
  exact ⟨_, _, IsGaussian.eq_gaussianReal _ hg⟩

/-! ### Zero mean on the Gaussian space -/

/-- The constant class `1` in `L²`. -/
private noncomputable def oneLp (μ : Measure Ω) [IsFiniteMeasure μ] : Lp ℝ 2 μ :=
  (memLp_const (1 : ℝ)).toLp _

private lemma inner_oneLp [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    ⟪f, oneLp μ⟫ = ∫ ω, (f : Ω → ℝ) ω ∂μ := by
  rw [inner_lp_eq_integral f (oneLp μ) (Filter.EventuallyEq.refl _ _)
    (MemLp.coeFn_toLp (memLp_const (1 : ℝ)))]
  simp

private lemma integral_eq_zero_of_mem_gspan [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0) {x : ℤ → Lp ℝ 2 μ} (hx : ∀ t, (x t : Ω → ℝ) =ᵐ[μ] X t)
    {g : Lp ℝ 2 μ} (hg : g ∈ gspan x) : ∫ ω, (g : Ω → ℝ) ω ∂μ = 0 := by
  have hle : gspan x ≤ (ℝ ∙ oneLp μ)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_oneLp,
      integral_congr_ae (hx t)]
    exact hmean t
  have h := hle hg
  rwa [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_oneLp] at h

/-! ### Measurable representatives adapted to the past -/

omit [MeasurableSpace Ω] in
private lemma sigmaLE_mono (X : ℤ → Ω → ℝ) {m m' : ℤ} (h : m ≤ m') :
    sigmaLE X m ≤ sigmaLE X m' :=
  iSup₂_le fun s hs => le_iSup₂ (f := fun s' (_ : s' ∈ Set.Iic m')
    => MeasurableSpace.comap (X s') inferInstance) s (le_trans hs h)

private lemma sigmaLE_le {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (m : ℤ) :
    sigmaLE X m ≤ ‹MeasurableSpace Ω› := iSup₂_le fun s _ => (hmeas s).comap_le

omit [MeasurableSpace Ω] in
private lemma measurable_sigmaLE {X : ℤ → Ω → ℝ} {s m : ℤ} (hs : s ≤ m) :
    Measurable[sigmaLE X m] (X s) :=
  measurable_iff_comap_le.2 (le_iSup₂ (f := fun s' (_ : s' ∈ Set.Iic m)
    => MeasurableSpace.comap (X s') inferInstance) s hs)

private lemma exists_repr_of_mem_wspan {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    {x : ℤ → Lp ℝ 2 μ} (hx : ∀ t, (x t : Ω → ℝ) =ᵐ[μ] X t) (m : ℤ)
    {f : Lp ℝ 2 μ} (hf : f ∈ wspan x m) :
    ∃ g : Ω → ℝ, Measurable[sigmaLE X m] g ∧ (f : Ω → ℝ) =ᵐ[μ] g := by
  have hsub : wspan x m ≤ lpMeas ℝ ℝ (sigmaLE X m) 2 μ := by
    refine wspan_le (isClosed_aestronglyMeasurable (sigmaLE_le hmeas m)) fun s hs => ?_
    exact mem_lpMeas_iff_aestronglyMeasurable.2
      ((measurable_sigmaLE (X := X) hs).stronglyMeasurable.aestronglyMeasurable.congr (hx s).symm)
  obtain ⟨g, hg, hfg⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 (hsub hf)
  exact ⟨g, hg.measurable, hfg⟩

private lemma integral_sq_lp [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    ∫ ω, (f : Ω → ℝ) ω ^ 2 ∂μ = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    inner_lp_eq_integral f f (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)]
  simp only [pow_two]

omit [MeasurableSpace Ω] in
private lemma comap_pi_eq {ι : Type*} (Z : ι → Ω → ℝ) :
    MeasurableSpace.comap (fun ω i => Z i ω) inferInstance
      = ⨆ i, MeasurableSpace.comap (Z i) inferInstance := by
  rw [show (inferInstance : MeasurableSpace (ι → ℝ)) = MeasurableSpace.pi from rfl,
    MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  exact iSup_congr fun i => by rw [MeasurableSpace.comap_comp]; rfl

private lemma measure_inter_eq_right_of_measure_eq_one [IsProbabilityMeasure μ] {A B : Set Ω}
    (hA : MeasurableSet A) (h : μ A = 1) : μ (A ∩ B) = μ B := by
  have hc : μ Aᶜ = 0 := by rw [prob_compl_eq_one_sub hA, h, tsub_self]
  refine le_antisymm (measure_mono Set.inter_subset_right) ?_
  have h1 : B ⊆ (A ∩ B) ∪ Aᶜ := by
    intro ω hω
    by_cases hA' : ω ∈ A
    · exact Or.inl ⟨hA', hω⟩
    · exact Or.inr hA'
  calc μ B ≤ μ ((A ∩ B) ∪ Aᶜ) := measure_mono h1
    _ ≤ μ (A ∩ B) + μ Aᶜ := measure_union_le _ _
    _ = μ (A ∩ B) := by rw [hc, add_zero]

end WoldProb



/-- **Wold decomposition, Gaussian form — DEBT** (FY §2.1.3, eq. (2.6); cited to
Brockwell & Davis 1991, p. 187; closure scheduled for batch F via the conditional-
expectation route, see `notes/time_series/debt_assessment.md` §5): a zero-mean weakly
stationary Gaussian process splits as an MA(∞) over i.i.d. Gaussian innovations plus an
independent deterministic (remote-past-measurable) component. -/
theorem wold_gaussian_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hG : IsGaussianProcess X μ) (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStationary X μ)
    -- USER-INPUT: zero mean; FY eq. (2.6)
    (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0) :
    ∃ (ψ : ℕ → ℝ) (ε V : ℤ → Ω → ℝ) (σ2 : ℝ),
      (Summable fun j => ψ j ^ 2) ∧ IsIIDNoise ε σ2 μ ∧
      (∀ t : ℤ, Measurable (V t)) ∧
      (∀ t : ℤ, Measurable[⨅ n : ℕ, sigmaLE X (t - n)] (V t)) ∧
      Indep (⨆ t : ℤ, MeasurableSpace.comap (ε t) inferInstance)
        (⨆ t : ℤ, MeasurableSpace.comap (V t) inferInstance) μ ∧
      ∀ t : ℤ, Tendsto
        (fun N => eLpNorm
          (fun ω => X t ω - (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω + V t ω)) 2 μ)
        atTop (nhds 0) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : ℤ → Lp ℝ 2 μ, ∀ t, (x t : Ω → ℝ) =ᵐ[μ] X t :=
    ⟨fun t => (hstat.memLp t).toLp (X t), fun t => MemLp.coeFn_toLp _⟩
  have hγ : ∀ s t : ℤ, (inner ℝ (x s) (x t) : ℝ) = acvf X μ (s - t) := inner_lpProc hstat hmean hx
  -- innovations
  have hεm : ∀ t : ℤ, Measurable (((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) := fun t =>
    (Lp.stronglyMeasurable _).measurable
  have hεg : ∀ t : ℤ, winn x t ∈ gspan x := fun t => wspan_le_gspan x t (winn_mem x t)
  have hdg : ∀ t : ℤ, wdet x t ∈ gspan x := fun t =>
    wspan_le_gspan x t (by simpa using wdet_mem hγ t 0)
  -- adapted representatives of the deterministic part
  have hrepr : ∀ (t : ℤ) (n : ℕ), ∃ g : Ω → ℝ, Measurable[sigmaLE X (t - (n : ℤ))] g ∧
      ((wdet x t : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] g :=
    fun t n => exists_repr_of_mem_wspan hmeas hx _ (wdet_mem hγ t n)
  choose gr hgrm hgrae using hrepr
  set V : ℤ → Ω → ℝ := fun t ω => limsup (fun n => gr t n ω) atTop with hVdef
  have hVae : ∀ t : ℤ, V t =ᵐ[μ] ((wdet x t : Lp ℝ 2 μ) : Ω → ℝ) := by
    intro t
    have hall : ∀ᵐ ω ∂μ, ∀ n : ℕ, gr t n ω = ((wdet x t : Lp ℝ 2 μ) : Ω → ℝ) ω :=
      ae_all_iff.2 fun n => (hgrae t n).symm
    filter_upwards [hall] with ω hω
    simp only [hVdef, hω, limsup_const]
  have hVN : ∀ (t : ℤ) (N : ℕ), Measurable[sigmaLE X (t - (N : ℤ))] (V t) := by
    intro t N
    have h1 : Measurable[sigmaLE X (t - (N : ℤ))]
        fun ω => limsup (fun n => gr t (n + N) ω) atTop :=
      Measurable.limsup fun n =>
        (hgrm t (n + N)).mono (sigmaLE_mono X (by push_cast; omega)) le_rfl
    have h2 : (fun ω => limsup (fun n => gr t (n + N) ω) atTop) = V t := by
      funext ω; exact limsup_nat_add (fun n => gr t n ω) N
    rwa [h2] at h1
  have hVm : ∀ t : ℤ, Measurable (V t) := fun t => by
    have := hVN t 0
    simpa using this.mono (sigmaLE_le hmeas (t - ((0 : ℕ) : ℤ))) le_rfl
  -- means and second moments
  have hmean0 : ∀ g : Lp ℝ 2 μ, g ∈ gspan x → ∫ ω, (g : Ω → ℝ) ω ∂μ = 0 :=
    fun g hg => integral_eq_zero_of_mem_gspan hmean hx hg
  refine ⟨wpsi x, fun t => ((winn x t : Lp ℝ 2 μ) : Ω → ℝ), V, wsig x,
    summable_wpsi_sq hγ, ?_, hVm, ?_, ?_, ?_⟩
  · -- IsIIDNoise
    have hcovε : ∀ s t : ℤ, s ≠ t →
        cov[((winn x s : Lp ℝ 2 μ) : Ω → ℝ), ((winn x t : Lp ℝ 2 μ) : Ω → ℝ); μ] = 0 := by
      intro s t hst
      have h1 : ∫ ω, ((((winn x s : Lp ℝ 2 μ) : Ω → ℝ)
          * ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) ω) ∂μ = 0 := by
        rw [show (fun ω => ((((winn x s : Lp ℝ 2 μ) : Ω → ℝ)
              * ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) ω))
            = fun ω => ((winn x s : Lp ℝ 2 μ) : Ω → ℝ) ω
              * ((winn x t : Lp ℝ 2 μ) : Ω → ℝ) ω from rfl,
          ← inner_lp_eq_integral (winn x s) (winn x t) (Filter.EventuallyEq.refl _ _)
            (Filter.EventuallyEq.refl _ _), inner_winn_winn hst]
      rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), hmean0 _ (hεg s), hmean0 _ (hεg t), h1]
      ring
    have hlaw : ∀ t : ℤ, μ.map ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)
        = gaussianReal 0 (wsig x).toNNReal := by
      intro t
      haveI hgt : IsGaussian (μ.map ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) :=
        isGaussian_of_mem_gspan hG hx (hεg t)
      have hmm : (μ.map ((winn x t : Lp ℝ 2 μ) : Ω → ℝ))[id] = 0 := by
        rw [integral_map (hεm t).aemeasurable aestronglyMeasurable_id]
        exact hmean0 _ (hεg t)
      have hvv : Var[id; μ.map ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)] = wsig x := by
        rw [variance_map aemeasurable_id (hεm t).aemeasurable]
        have h2 : (fun ω => id (((winn x t : Lp ℝ 2 μ) : Ω → ℝ) ω))
            = ((winn x t : Lp ℝ 2 μ) : Ω → ℝ) := rfl
        rw [show (id ∘ ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) = ((winn x t : Lp ℝ 2 μ) : Ω → ℝ) from rfl,
          variance_eq_sub (Lp.memLp _), hmean0 _ (hεg t)]
        have h3 : (μ[((winn x t : Lp ℝ 2 μ) : Ω → ℝ) ^ 2] : ℝ)
            = ∫ ω, ((winn x t : Lp ℝ 2 μ) : Ω → ℝ) ω ^ 2 ∂μ := rfl
        rw [h3, integral_sq_lp, norm_winn_sq hγ]
        ring
      rw [hgt.eq_gaussianReal, hmm, hvv]
    refine ⟨hεm, ?_, ?_, Lp.memLp _, hmean0 _ (hεg 0), ?_⟩
    · have hgp : IsGaussianProcess
          (fun (p : (t : ℤ) × Unit) ω => ((winn x p.1 : Lp ℝ 2 μ) : Ω → ℝ) ω) μ :=
        isGaussianProcess_of_mem_gspan hG hx (fun p : (t : ℤ) × Unit => winn x p.1)
          (fun p => hεg p.1) (fun _ => Filter.EventuallyEq.refl _ _) (fun p => hεm p.1)
      have h0 := IsGaussianProcess.iIndepFun_of_covariance_eq_zero
        (X := fun (t : ℤ) (_ : Unit) => ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) hgp
        (fun t _ => (hεm t).aemeasurable) (fun t₁ t₂ h _ _ => hcovε t₁ t₂ h)
      exact h0.comp (fun (_ : ℤ) (v : Unit → ℝ) => v ()) fun _ => measurable_pi_apply ()
    · intro s t
      exact ⟨(hεm s).aemeasurable, (hεm t).aemeasurable, by rw [hlaw s, hlaw t]⟩
    · have h3 : (μ[((winn x 0 : Lp ℝ 2 μ) : Ω → ℝ) ^ 2] : ℝ)
          = ∫ ω, ((winn x 0 : Lp ℝ 2 μ) : Ω → ℝ) ω ^ 2 ∂μ := rfl
      rw [variance_eq_sub (Lp.memLp _), hmean0 _ (hεg 0), h3, integral_sq_lp, wsig]
      ring
  · intro t B hB
    exact MeasurableSpace.measurableSet_iInf.2 fun n => hVN t n hB
  · -- Indep
    have hcovεV : ∀ (s t : ℤ), cov[((winn x s : Lp ℝ 2 μ) : Ω → ℝ), V t; μ] = 0 := by
      intro s t
      have hmV : MemLp (V t) 2 μ := (Lp.memLp (wdet x t)).ae_eq (hVae t).symm
      have h1 : ∫ ω, ((((winn x s : Lp ℝ 2 μ) : Ω → ℝ) * V t) ω) ∂μ = 0 := by
        rw [show (fun ω => ((((winn x s : Lp ℝ 2 μ) : Ω → ℝ) * V t) ω))
            = fun ω => ((winn x s : Lp ℝ 2 μ) : Ω → ℝ) ω * V t ω from rfl,
          ← inner_lp_eq_integral (winn x s) (wdet x t) (Filter.EventuallyEq.refl _ _)
            (hVae t).symm, ← real_inner_comm (winn x s) (wdet x t), inner_wdet_winn hγ t s]
      have hV0 : ∫ ω, V t ω ∂μ = 0 := by
        rw [integral_congr_ae (hVae t)]
        exact hmean0 _ (hdg t)
      rw [covariance_eq_sub (Lp.memLp _) hmV, hmean0 _ (hεg s), hV0, h1]
      ring
    have hSum : IsGaussianProcess
        (Sum.elim (fun t : ℤ => ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) V) μ := by
      refine isGaussianProcess_of_mem_gspan hG hx (Sum.elim (winn x) (wdet x)) ?_ ?_ ?_
      · rintro (t | t)
        · exact hεg t
        · exact hdg t
      · rintro (t | t)
        · exact Filter.EventuallyEq.refl _ _
        · exact hVae t
      · rintro (t | t)
        · exact hεm t
        · exact hVm t
    have hIF := IsGaussianProcess.indepFun_of_covariance_eq_zero hSum
      (fun s => (hεm s).aemeasurable) (fun t => (hVm t).aemeasurable) hcovεV
    have hIndep : Indep (MeasurableSpace.comap
        (fun ω (s : ℤ) => ((winn x s : Lp ℝ 2 μ) : Ω → ℝ) ω) inferInstance)
        (MeasurableSpace.comap (fun ω (t : ℤ) => V t ω) inferInstance) μ := hIF
    rw [comap_pi_eq fun s : ℤ => ((winn x s : Lp ℝ 2 μ) : Ω → ℝ), comap_pi_eq V] at hIndep
    exact hIndep
  · -- L² convergence
    intro t
    have hwsum : ((wsum x t : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] fun ω => X t ω - V t ω := by
      have h1 : wsum x t = x t - wdet x t := by rw [wdet]; abel
      rw [h1]
      filter_upwards [Lp.coeFn_sub (x t) (wdet x t), hx t, hVae t] with ω h2 h3 h4
      rw [h2]
      simp only [Pi.sub_apply, h3, h4]
    have hcongr : ∀ N : ℕ,
        (fun ω => X t ω - ((∑ j ∈ Finset.range N, wpsi x j
            * ((winn x (t - (j : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ) ω) + V t ω))
          =ᵐ[μ] ((wsum x t - wpartial x t N : Lp ℝ 2 μ) : Ω → ℝ) := by
      intro N
      have hwp : ((wpartial x t N : Lp ℝ 2 μ) : Ω → ℝ)
          =ᵐ[μ] fun ω => ∑ j ∈ Finset.range N, wpsi x j
            * ((winn x (t - (j : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ) ω :=
        coeFn_lp_lincomb (Finset.range N) (wpsi x) (fun j => winn x (t - (j : ℤ)))
          (fun j => ((winn x (t - (j : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ))
          fun _ => Filter.EventuallyEq.refl _ _
      filter_upwards [Lp.coeFn_sub (wsum x t) (wpartial x t N), hwsum, hwp] with ω h1 h2 h3
      rw [h1]
      simp only [Pi.sub_apply, h2, h3]
      ring
    have hnorm : Tendsto (fun N => ‖wsum x t - wpartial x t N‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N => wsum x t - wpartial x t N) atTop (𝓝 (wsum x t - wsum x t)) :=
        tendsto_const_nhds.sub (tendsto_wpartial hγ t)
      rw [sub_self] at h0
      simpa using h0.norm
    have hfinal : Tendsto (fun N => ENNReal.ofReal ‖wsum x t - wpartial x t N‖) atTop (𝓝 0) := by
      have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
      rw [ENNReal.ofReal_zero] at h1
      exact h1
    refine Tendsto.congr (fun N => ?_) hfinal
    rw [eLpNorm_congr_ae (hcongr N), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

/-- **Proposition 2.1(ii)** (FY §2.1.3): a zero-mean weakly stationary Gaussian process
that is `q`-dependent (`Cov(X_s, X_t) = 0` for `|s − t| > q`) with trivial remote past
in its Wold decomposition is an MA(q). Statement conditional on `wold_gaussian_debt`;
DEBT until batch F. -/
theorem gaussian_q_dependent_isMA_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    {q : ℕ}
    (hG : IsGaussianProcess X μ) (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStationary X μ) (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: q-dependence; FY §2.1.3 Prop 2.1(ii)
    (hdep : ∀ s t : ℤ, (q : ℤ) < |s - t| → cov[X s, X t; μ] = 0)
    -- USER-INPUT: purely nondeterministic (trivial remote past); FY §2.1.3 Prop 2.1(i)
    (hpnd : ∀ A : Set Ω, MeasurableSet[⨅ n : ℕ, sigmaLE X (-(n : ℤ))] A →
      μ A = 0 ∨ μ A = 1) :
    ∃ (a : Fin q → ℝ) (σ2 : ℝ) (ε : ℤ → Ω → ℝ), IsMA a σ2 X ε μ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : ℤ → Lp ℝ 2 μ, ∀ t, (x t : Ω → ℝ) =ᵐ[μ] X t :=
    ⟨fun t => (hstat.memLp t).toLp (X t), fun t => MemLp.coeFn_toLp _⟩
  have hγ : ∀ s t : ℤ, (inner ℝ (x s) (x t) : ℝ) = acvf X μ (s - t) := inner_lpProc hstat hmean hx
  have hεm : ∀ t : ℤ, Measurable (((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) := fun t =>
    (Lp.stronglyMeasurable _).measurable
  have hεg : ∀ t : ℤ, winn x t ∈ gspan x := fun t => wspan_le_gspan x t (winn_mem x t)
  have hdg : ∀ t : ℤ, wdet x t ∈ gspan x := fun t =>
    wspan_le_gspan x t (by simpa using wdet_mem hγ t 0)
  have hmean0 : ∀ g : Lp ℝ 2 μ, g ∈ gspan x → ∫ ω, (g : Ω → ℝ) ω ∂μ = 0 :=
    fun g hg => integral_eq_zero_of_mem_gspan hmean hx hg
  -- **Step 1**: the deterministic component vanishes (trivial remote past).
  have hdet : ∀ t : ℤ, wdet x t = 0 := by
    intro t
    have hrepr : ∀ n : ℕ, ∃ g : Ω → ℝ, Measurable[sigmaLE X (t - (n : ℤ))] g ∧
        ((wdet x t : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] g :=
      fun n => exists_repr_of_mem_wspan hmeas hx _ (wdet_mem hγ t n)
    choose gr hgrm hgrae using hrepr
    set W : Ω → ℝ := fun ω => limsup (fun n => gr n ω) atTop with hWdef
    have hWae : W =ᵐ[μ] ((wdet x t : Lp ℝ 2 μ) : Ω → ℝ) := by
      have hall : ∀ᵐ ω ∂μ, ∀ n : ℕ, gr n ω = ((wdet x t : Lp ℝ 2 μ) : Ω → ℝ) ω :=
        ae_all_iff.2 fun n => (hgrae n).symm
      filter_upwards [hall] with ω hω
      simp only [hWdef, hω, limsup_const]
    have hWN : ∀ N : ℕ, Measurable[sigmaLE X (t - (N : ℤ))] W := by
      intro N
      have h1 : Measurable[sigmaLE X (t - (N : ℤ))]
          fun ω => limsup (fun n => gr (n + N) ω) atTop :=
        Measurable.limsup fun n =>
          (hgrm (n + N)).mono (sigmaLE_mono X (by push_cast; omega)) le_rfl
      have h2 : (fun ω => limsup (fun n => gr (n + N) ω) atTop) = W := by
        funext ω; exact limsup_nat_add (fun n => gr n ω) N
      rwa [h2] at h1
    have hWtail : ∀ m : ℕ, Measurable[sigmaLE X (-(m : ℤ))] W := fun m =>
      (hWN (t + (m : ℤ)).toNat).mono (sigmaLE_mono X (by omega)) le_rfl
    have hWm : Measurable W := (hWtail 0).mono (sigmaLE_le hmeas _) le_rfl
    have hWiInf : Measurable[⨅ n : ℕ, sigmaLE X (-(n : ℤ))] W := fun B hB =>
      MeasurableSpace.measurableSet_iInf.2 fun n => hWtail n hB
    have hle0 : (⨅ n : ℕ, sigmaLE X (-(n : ℤ))) ≤ (inferInstance : MeasurableSpace Ω) :=
      le_trans (iInf_le _ 0) (by simpa using sigmaLE_le hmeas (0 : ℤ))
    have hind : IndepFun W W μ := by
      rw [indepFun_iff_measure_inter_preimage_eq_mul]
      intro s s' hs hs'
      rcases hpnd _ (hWiInf hs) with h0 | h1
      · rw [h0, zero_mul]
        exact measure_mono_null Set.inter_subset_left h0
      · rw [h1, one_mul]
        exact measure_inter_eq_right_of_measure_eq_one (hle0 _ (hWiInf hs)) h1
    have hmW : MemLp W 2 μ := (Lp.memLp (wdet x t)).ae_eq hWae.symm
    have hvar : Var[W; μ] = 0 := by
      rw [← covariance_self hWm.aemeasurable]
      exact hind.covariance_eq_zero hmW hmW
    have hmeanW : ∫ ω, W ω ∂μ = 0 := by
      rw [integral_congr_ae hWae]
      exact hmean0 _ (hdg t)
    have hsq : (μ[W ^ 2] : ℝ) = ∫ ω, W ω ^ 2 ∂μ := rfl
    have hnorm : ‖wdet x t‖ ^ 2 = 0 := by
      rw [← integral_sq_lp (wdet x t)]
      have h1 : ∫ ω, ((wdet x t : Lp ℝ 2 μ) : Ω → ℝ) ω ^ 2 ∂μ = ∫ ω, W ω ^ 2 ∂μ :=
        integral_congr_ae (by filter_upwards [hWae] with ω hω; rw [hω])
      have h2 := variance_eq_sub hmW
      rw [hvar, hmeanW, hsq] at h2
      rw [h1]
      linarith [h2]
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hnorm)
  -- **Step 2**: the innovations are white noise `WN(0, σ²)`.
  have hcovε : ∀ s t : ℤ, s ≠ t →
      cov[((winn x s : Lp ℝ 2 μ) : Ω → ℝ), ((winn x t : Lp ℝ 2 μ) : Ω → ℝ); μ] = 0 := by
    intro s t hst
    have h1 : ∫ ω, ((((winn x s : Lp ℝ 2 μ) : Ω → ℝ)
        * ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) ω) ∂μ = 0 := by
      rw [show (fun ω => ((((winn x s : Lp ℝ 2 μ) : Ω → ℝ)
            * ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) ω))
          = fun ω => ((winn x s : Lp ℝ 2 μ) : Ω → ℝ) ω
            * ((winn x t : Lp ℝ 2 μ) : Ω → ℝ) ω from rfl,
        ← inner_lp_eq_integral (winn x s) (winn x t) (Filter.EventuallyEq.refl _ _)
          (Filter.EventuallyEq.refl _ _), inner_winn_winn hst]
    rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), hmean0 _ (hεg s), hmean0 _ (hεg t), h1]
    ring
  have hvarε : ∀ t : ℤ, Var[((winn x t : Lp ℝ 2 μ) : Ω → ℝ); μ] = wsig x := by
    intro t
    have h3 : (μ[((winn x t : Lp ℝ 2 μ) : Ω → ℝ) ^ 2] : ℝ)
        = ∫ ω, ((winn x t : Lp ℝ 2 μ) : Ω → ℝ) ω ^ 2 ∂μ := rfl
    rw [variance_eq_sub (Lp.memLp _), hmean0 _ (hεg t), h3, integral_sq_lp, norm_winn_sq hγ]
    ring
  have hwn : IsWhiteNoise (fun t => ((winn x t : Lp ℝ 2 μ) : Ω → ℝ)) (wsig x) μ :=
    ⟨hεm, fun t => Lp.memLp _, fun t => hmean0 _ (hεg t), hvarε, hcovε⟩
  -- **Step 3**: `q`-dependence kills the Wold coefficients beyond lag `q`.
  have hψhigh : ∀ j : ℕ, q < j → wpsi x j = 0 := by
    intro j hj
    have h1 := inner_x_winn hγ 0 j
    have hzero : (inner ℝ (x 0) (winn x (0 - (j : ℤ))) : ℝ) = 0 := by
      rw [show winn x (0 - (j : ℤ))
          = x (0 - (j : ℤ)) - (wspan x (0 - (j : ℤ) - 1)).starProjection (x (0 - (j : ℤ)))
          from rfl, inner_sub_right]
      have hA : (inner ℝ (x 0) (x (0 - (j : ℤ))) : ℝ) = 0 := by
        rw [hγ, acvf]
        have hq : ((q : ℤ)) < |(0 - (0 - (j : ℤ))) - 0| := by
          rcases abs_cases ((0 - (0 - (j : ℤ))) - 0) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
        simpa using hdep (0 - (0 - (j : ℤ))) 0 hq
      have hB : (inner ℝ (x 0)
          ((wspan x (0 - (j : ℤ) - 1)).starProjection (x (0 - (j : ℤ)))) : ℝ) = 0 := by
        have hperp : x 0 ∈ (wspan x (0 - (j : ℤ) - 1))ᗮ := by
          refine mem_orthogonal_wspan fun s hs => ?_
          rw [hγ, acvf]
          have hq : ((q : ℤ)) < |(s - 0) - 0| := by
            rcases abs_cases ((s - 0) - 0) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
          simpa using hdep (s - 0) 0 hq
        rw [← real_inner_comm]
        exact hperp ((wspan x (0 - (j : ℤ) - 1)).starProjection (x (0 - (j : ℤ))))
          (Submodule.starProjection_apply_mem _ _)
      rw [hA, hB, sub_zero]
    rw [hzero] at h1
    rcases eq_or_ne (wsig x) 0 with hz | hz
    · rw [wpsi, hz, div_zero]
    · exact (mul_eq_zero.1 h1.symm).resolve_right hz
  have hψ0 : wsig x ≠ 0 → wpsi x 0 = 1 := by
    intro hz
    have h1 := inner_x_winn hγ 0 0
    have hsplit : x 0 = winn x 0 + (wspan x ((0 : ℤ) - 1)).starProjection (x 0) := by
      rw [winn]; abel
    have hP : (inner ℝ ((wspan x ((0 : ℤ) - 1)).starProjection (x 0)) (winn x 0) : ℝ) = 0 := by
      rw [← real_inner_comm]
      exact inner_winn_of_mem (Submodule.starProjection_apply_mem _ _)
    have h2 : (inner ℝ (x 0) (winn x 0) : ℝ) = wsig x := by
      nth_rewrite 1 [hsplit]
      rw [inner_add_left, hP, add_zero, real_inner_self_eq_norm_sq, norm_winn_sq hγ]
    simp only [Nat.cast_zero, sub_zero] at h1
    rw [h2] at h1
    have h4 : wpsi x 0 * wsig x = 1 * wsig x := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel₀ hz h4
  -- **Step 4**: the Wold series terminates, so `X` is an MA(q).
  have hpart : ∀ (t : ℤ) (N : ℕ), q + 1 ≤ N → wpartial x t N = wpartial x t (q + 1) := by
    intro t N hN
    have hsub : Finset.range (q + 1) ⊆ Finset.range N := fun j hj =>
      Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) hN)
    refine (Finset.sum_subset hsub fun j _ hj => ?_).symm
    have hj' : q < j := by
      by_contra hcon
      exact hj (Finset.mem_range.2 (by omega))
    rw [hψhigh j hj', zero_smul]
  have hsum_eq : ∀ t : ℤ, wsum x t = wpartial x t (q + 1) := by
    intro t
    refine tendsto_nhds_unique (tendsto_wpartial hγ t) (Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop (q + 1)] with N hN
    exact (hpart t N hN).symm
  have hxeq : ∀ t : ℤ, x t = wpartial x t (q + 1) := by
    intro t
    have h := hdet t
    rw [wdet, hsum_eq t, sub_eq_zero] at h
    exact h
  have hrec : ∀ t : ℤ, X t =ᵐ[μ] fun ω => ∑ j ∈ Finset.range (q + 1), wpsi x j
      * ((winn x (t - (j : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ) ω := by
    intro t
    have h1 := coeFn_lp_lincomb (Finset.range (q + 1)) (wpsi x) (fun j => winn x (t - (j : ℤ)))
      (fun j => ((winn x (t - (j : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ))
      fun _ => Filter.EventuallyEq.refl _ _
    have h2 : ((x t : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] fun ω => ∑ j ∈ Finset.range (q + 1), wpsi x j
        * ((winn x (t - (j : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ) ω := by
      rw [hxeq t]; exact h1
    exact (hx t).symm.trans h2
  refine ⟨fun i : Fin q => wpsi x ((i : ℕ) + 1), wsig x,
    fun t => ((winn x t : Lp ℝ 2 μ) : Ω → ℝ), hmeas, hwn, ?_⟩
  intro t
  rcases eq_or_ne (wsig x) 0 with hz | hz
  · have hεz : ∀ᵐ ω ∂μ, ∀ s : ℤ, ((winn x s : Lp ℝ 2 μ) : Ω → ℝ) ω = 0 := by
      refine ae_all_iff.2 fun s => ?_
      have : ((winn x s : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] 0 := by
        rw [winn_eq_zero hγ hz s]; exact Lp.coeFn_zero ℝ 2 μ
      filter_upwards [this] with ω hω
      simpa using hω
    have hX0 : X t =ᵐ[μ] fun _ => (0 : ℝ) := by
      refine (hrec t).trans ?_
      filter_upwards [hεz] with ω hω
      exact Finset.sum_eq_zero fun j _ => by rw [hω (t - (j : ℤ)), mul_zero]
    filter_upwards [hX0, hεz] with ω h1 h2
    simp [h1, h2]
  · filter_upwards [hrec t] with ω hω
    have e1 : ∑ j ∈ Finset.range (q + 1), wpsi x j
        * ((winn x (t - (j : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ) ω
        = (∑ i ∈ Finset.range q, wpsi x (i + 1)
            * ((winn x (t - 1 - ((i : ℕ) : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ) ω)
          + wpsi x 0 * ((winn x t : Lp ℝ 2 μ) : Ω → ℝ) ω := by
      have hidx : ∀ i : ℕ, t - ((i + 1 : ℕ) : ℤ) = t - 1 - ((i : ℕ) : ℤ) := by
        intro i; push_cast; ring
      have hidx0 : t - ((0 : ℕ) : ℤ) = t := by simp
      rw [Finset.sum_range_succ']
      simp only [hidx, hidx0]
    rw [hω, e1, hψ0 hz, Fin.sum_univ_eq_sum_range (fun i => wpsi x (i + 1)
      * ((winn x (t - 1 - ((i : ℕ) : ℤ)) : Lp ℝ 2 μ) : Ω → ℝ) ω) q]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, one_mul, zero_add]
    ring

end StatLean.TimeSeries
