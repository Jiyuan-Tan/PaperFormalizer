module
public import StatLean.TimeSeries.Process.PartialAutocorrelation

@[expose] public section

/-!
# Best linear prediction and prewhitening (FY §3.2, Definition 3.1, Theorem 3.1)

For a zero-mean weakly stationary process:

* the **mean-squared prediction error** of a linear predictor of `X_{k+1}` from
  `X_k, …, X_1` (`predMSE`; FY eqs. (3.3)–(3.4));
* **FY Theorem 3.1**: a coefficient vector is MSE-optimal **iff** it solves the
  Yule–Walker system `Σ_j φ_{kj} γ(i − j) = γ(i)`, `i = 1..k` (eq. (3.5)) — full
  in-text proof (quadratic expansion (3.6) + perturbation necessity);
* **prewhitening**: successive innovations `X_{t+1} − X̂_{t+1}` are uncorrelated
  (corollary of the projection orthogonality);
* the **innovation variances** `ν_t = γ(0) − Σ_j φ_{tj} γ(j)` (eq. (3.7));
* the **innovation algorithm** (B&D Prop 5.2.2) — Gram–Schmidt recursion for the
  one-step predictors; stated as a correctness claim for the recursively defined
  coefficients, proof attempted (demoted to a named debt if it exceeds the wave
  budget, per the roadmap).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.2,
Definition 3.1, Theorem 3.1, eqs. (3.3)–(3.8) (pp. 91–93). (`FY §3.2`.)

**Proof formalization notes.**
* The predictor window is `X_1, …, X_k` predicting `X_{k+1}`, per FY's indexing; the
  time reversal against `Process/PartialAutocorrelation.lean`'s
  `linRegCoeffs`-machinery is handled by `acvf_even`.
* `predMSE` is an integral of a square, not a `variance` — the process is zero-mean by
  hypothesis, keeping the statements free of centering.

**Bibliographic comments.** Best linear prediction of stationary sequences is
Kolmogorov (1941) and Wiener (1949); the finite-window normal-equation form is
standard from Brockwell & Davis (1991) §5.1; the innovation algorithm is B&D
Prop 5.2.2 (after Rissanen–Barbosa).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Mean-squared prediction error** (FY eq. (3.4)) of predicting `X_{k+1}` by
`Σ_{j<k} φ_j X_{k−j}` (so `φ_0` weights the most recent observation `X_k`). -/
noncomputable def predMSE (X : ℤ → Ω → ℝ) (μ : Measure Ω) (k : ℕ)
    (φ : Fin k → ℝ) : ℝ :=
  ∫ ω, (X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω) ^ 2 ∂μ

/-! ### The prediction toolkit

The prediction error `R_φ = X_{k+1} − Σ_j φ_j X_{k−j}` has zero mean, so `predMSE` *is* its
variance and all second moments are covariances; bilinearity of the covariance against the
window turns everything into `acvf` arithmetic (FY eq. (3.6)). The Yule–Walker system is
exactly the orthogonality of `R_φ` against the window. -/

section Toolkit

variable {X : ℤ → Ω → ℝ}

/-- Covariance only sees the a.e. class of each argument. -/
private lemma covariance_congr_ae {Y Y' Z Z' : Ω → ℝ} (hY : Y =ᵐ[μ] Y') (hZ : Z =ᵐ[μ] Z') :
    cov[Y, Z; μ] = cov[Y', Z'; μ] := by
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  have hIZ : ∫ x, Z x ∂μ = ∫ x, Z' x ∂μ := integral_congr_ae hZ
  simp only [covariance, hIY, hIZ]
  exact integral_congr_ae (by filter_upwards [hY, hZ] with ω h1 h2 using by rw [h1, h2])

/-- Square-integrability of a linear combination of the prediction window. -/
private lemma memLp_predWindow (hstat : IsStationary X μ) {k : ℕ} (φ : Fin k → ℝ) :
    MemLp (fun ω => ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω) 2 μ :=
  memLp_finset_sum _ fun (j : Fin k) _ => (hstat.memLp ((k : ℤ) - (j : ℕ))).const_mul (φ j)

/-- Square-integrability of the prediction error. -/
private lemma memLp_predError (hstat : IsStationary X μ) {k : ℕ} (φ : Fin k → ℝ) :
    MemLp (fun ω => X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω) 2 μ :=
  (hstat.memLp ((k : ℤ) + 1)).sub (memLp_predWindow hstat φ)

/-- The zero-mean hypothesis propagates to every marginal (the mean is time-constant). -/
private lemma integral_eq_zero_of_zero_mean (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (t : ℤ) : ∫ ω, X t ω ∂μ = 0 := by
  rw [hstat.integral_eq t 0, hmean]

/-- Hence the prediction error is centred. -/
private lemma integral_predError_eq_zero [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) {k : ℕ} (φ : Fin k → ℝ) :
    ∫ ω, (X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω) ∂μ = 0 := by
  have hint : ∀ t : ℤ, Integrable (X t) μ := fun t => hstat.integrable t
  have hterm : ∀ j : Fin k, ∫ ω, φ j * X ((k : ℤ) - (j : ℕ)) ω ∂μ = 0 := fun j => by
    rw [integral_const_mul, integral_eq_zero_of_zero_mean hstat hmean, mul_zero]
  rw [integral_sub (hint _) ((memLp_predWindow hstat φ).integrable one_le_two),
    integral_finset_sum _ (fun (j : Fin k) _ => (hint ((k : ℤ) - (j : ℕ))).const_mul (φ j)),
    integral_eq_zero_of_zero_mean hstat hmean]
  simp [hterm]

/-- `predMSE` is the variance of the (centred) prediction error. -/
private lemma predMSE_eq_variance [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) {k : ℕ} (φ : Fin k → ℝ) :
    predMSE X μ k φ
      = variance (fun ω => X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω) μ := by
  rw [variance_of_integral_eq_zero
    (memLp_predError hstat φ).aestronglyMeasurable.aemeasurable
    (integral_predError_eq_zero hstat hmean φ)]
  rfl

/-- Bilinear expansion of the prediction-error covariance against a single coordinate of the
process (the first half of FY eq. (3.6)). -/
private lemma cov_predError_left [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {k : ℕ} (φ : Fin k → ℝ) (t : ℤ) :
    cov[fun ω => X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω, X t; μ]
      = acvf X μ ((k : ℤ) + 1 - t) - ∑ j, φ j * acvf X μ ((k : ℤ) - (j : ℕ) - t) := by
  rw [covariance_fun_sub_left (hstat.memLp ((k : ℤ) + 1)) (memLp_predWindow hstat φ)
      (hstat.memLp t),
    covariance_fun_sum_left (fun (j : Fin k) => (hstat.memLp ((k : ℤ) - (j : ℕ))).const_mul (φ j))
      (hstat.memLp t)]
  simp_rw [covariance_const_mul_left, hstat.cov_eq_acvf]

/-- **The Yule–Walker system is the orthogonality of the prediction error against the
window** (FY eq. (3.5) as normal equations). -/
private lemma yuleWalker_iff_orthogonal [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {k : ℕ} (φ : Fin k → ℝ) :
    (∀ i : Fin k, ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ) = acvf X μ ((i : ℕ) + 1))
      ↔ ∀ i : Fin k,
          cov[fun ω => X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω,
              X ((k : ℤ) - (i : ℕ)); μ] = 0 := by
  have hc : ∀ i : Fin k,
      cov[fun ω => X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω,
          X ((k : ℤ) - (i : ℕ)); μ]
        = acvf X μ ((i : ℕ) + 1) - ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ) := by
    intro i
    rw [cov_predError_left hstat φ ((k : ℤ) - (i : ℕ))]
    congr 1
    · congr 1
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ring
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · rw [hc i, h i, sub_self]
  · have hi := hc i
    rw [h i] at hi
    linarith

/-- **FY eq. (3.6)**: the quadratic expansion of the prediction MSE around a base point `φ`.
The cross term is the covariance of the prediction error at `φ` with the perturbation. -/
private lemma predMSE_eq_add [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) {k : ℕ} (φ ψ : Fin k → ℝ) :
    predMSE X μ k ψ = predMSE X μ k φ
      - 2 * ∑ j, (ψ j - φ j) *
          cov[fun ω => X ((k : ℤ) + 1) ω - ∑ i, φ i * X ((k : ℤ) - (i : ℕ)) ω,
              X ((k : ℤ) - (j : ℕ)); μ]
      + variance (fun ω => ∑ j, (ψ j - φ j) * X ((k : ℤ) - (j : ℕ)) ω) μ := by
  have hsplit : (fun ω => X ((k : ℤ) + 1) ω - ∑ j, ψ j * X ((k : ℤ) - (j : ℕ)) ω)
      = fun ω => (X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω)
          - ∑ j, (ψ j - φ j) * X ((k : ℤ) - (j : ℕ)) ω := by
    funext ω
    have hd : ∑ j, (ψ j - φ j) * X ((k : ℤ) - (j : ℕ)) ω
        = (∑ j, ψ j * X ((k : ℤ) - (j : ℕ)) ω) - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hd]
    ring
  rw [predMSE_eq_variance hstat hmean ψ, predMSE_eq_variance hstat hmean φ, hsplit,
    variance_fun_sub (memLp_predError hstat φ) (memLp_predWindow hstat fun j => ψ j - φ j),
    covariance_fun_sum_right
      (fun (j : Fin k) => (hstat.memLp ((k : ℤ) - (j : ℕ))).const_mul (ψ j - φ j))
      (memLp_predError hstat φ)]
  simp_rw [covariance_const_mul_right]

/-- A psd quadratic with a linear term that is nonnegative in every direction has no linear
term (the perturbation step of FY Theorem 3.1's necessity half). -/
private lemma eq_zero_of_quadratic_nonneg {a g : ℝ} (hg : 0 ≤ g)
    (h : ∀ t : ℝ, 0 ≤ -(2 * (t * a)) + t ^ 2 * g) : a = 0 := by
  by_contra hne
  have hpos : (0 : ℝ) < g + 1 := by linarith
  obtain ⟨c, hc, hac⟩ : ∃ c : ℝ, c ≠ 0 ∧ a = c * (g + 1) :=
    ⟨a / (g + 1), div_ne_zero hne (ne_of_gt hpos), by field_simp⟩
  have h1 := h c
  rw [hac] at h1
  have hc2 : 0 < c ^ 2 := lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc))
  nlinarith [mul_nonneg hc2.le hg]

/-- Orthogonality of a Yule–Walker prediction error against the whole observation window
`X_1, …, X_l` (not just the window coordinates in their `Fin l` indexing). -/
private lemma cov_predError_eq_zero_of_yuleWalker [IsProbabilityMeasure μ]
    (hstat : IsStationary X μ) {l : ℕ} {ψ : Fin l → ℝ}
    (hψ : ∀ i : Fin l, ∑ j, ψ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ) = acvf X μ ((i : ℕ) + 1))
    {t : ℤ} (ht1 : 1 ≤ t) (ht2 : t ≤ (l : ℤ)) :
    cov[fun ω => X ((l : ℤ) + 1) ω - ∑ j, ψ j * X ((l : ℤ) - (j : ℕ)) ω, X t; μ] = 0 := by
  have hlt : ((l : ℤ) - t).toNat < l := by omega
  set i : Fin l := ⟨((l : ℤ) - t).toNat, hlt⟩ with hidef
  have hival : ((i : ℕ) : ℤ) = (l : ℤ) - t := by
    have hv : (i : ℕ) = ((l : ℤ) - t).toNat := rfl
    rw [hv]
    omega
  have h1 : acvf X μ ((l : ℤ) + 1 - t) = acvf X μ (((i : ℕ) : ℤ) + 1) := by
    rw [hival]
    congr 1
    ring
  have h2 : ∀ j : Fin l, ((l : ℤ) - (j : ℕ) - t) = (((i : ℕ) : ℤ) - (j : ℕ)) := by
    intro j
    rw [hival]
    ring
  rw [cov_predError_left hstat ψ t, h1, sub_eq_zero, ← hψ i]
  exact Finset.sum_congr rfl fun j _ => by rw [h2 j]

/-- A real vector with vanishing self-dot-product is zero (the ambient `Mathlib` lemma
`dotProduct_self_eq_zero` is not in this file's import closure). -/
private lemma eq_zero_of_dotProduct_self {n : ℕ} {x : Fin n → ℝ}
    (h : dotProduct x x = 0) : x = 0 := by
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
  simpa using mul_self_eq_zero.mp hi

/-- A real symmetric system `A b = c` is solvable as soon as `c` annihilates the kernel of
`A` (the range of a symmetric map is the orthogonal complement of its kernel). -/
private lemma exists_solution_of_symm {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hsymm : ∀ i j, A j i = A i j) {c : Fin n → ℝ}
    (hker : ∀ x : Fin n → ℝ, (∀ i, ∑ j, A i j * x j = 0) → ∑ i, c i * x i = 0) :
    ∃ b : Fin n → ℝ, ∀ i, ∑ j, A i j * b j = c i := by
  classical
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of A with hM
  have hMsymm : M.transpose = M := by
    ext i j
    exact hsymm i j
  have hmulVec : ∀ (x : Fin n → ℝ) (i : Fin n),
      Matrix.mulVec M x i = ∑ j, A i j * x j := fun x i => rfl
  -- `y ⊥ range M` whenever `M y = 0`, by symmetry of `M`
  have horth : ∀ y z : Fin n → ℝ, Matrix.mulVec M y = 0 →
      dotProduct (Matrix.mulVec M z) y = 0 := by
    intro y z hy
    have h1 : dotProduct (Matrix.mulVec M z) y
        = dotProduct (Matrix.vecMul y M) z := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec]
    rw [h1, ← Matrix.mulVec_transpose, hMsymm, hy, zero_dotProduct]
  set f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin M with hf
  have hfapp : ∀ x, f x = Matrix.mulVec M x := fun x => rfl
  have hdisj : Disjoint (LinearMap.ker f) (LinearMap.range f) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨z, hz⟩ := hx2
    have hxk : Matrix.mulVec M x = 0 := by
      have := LinearMap.mem_ker.mp hx1
      rwa [hfapp] at this
    have hzx : Matrix.mulVec M z = x := by rw [← hfapp]; exact hz
    have hxx : dotProduct x x = 0 := by
      have := horth x z hxk
      rwa [hzx] at this
    exact eq_zero_of_dotProduct_self hxx
  have hsup : LinearMap.ker f ⊔ LinearMap.range f = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have hrn : Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f)
        = Module.finrank ℝ (Fin n → ℝ) := LinearMap.finrank_range_add_finrank_ker f
    have hsi := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (LinearMap.range f)
    rw [disjoint_iff.mp hdisj] at hsi
    simp only [finrank_bot, add_zero] at hsi
    omega
  have hmem : c ∈ LinearMap.ker f ⊔ LinearMap.range f := by rw [hsup]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨b, hb⟩ := hz
  have hyk : Matrix.mulVec M y = 0 := by
    have := LinearMap.mem_ker.mp hy
    rwa [hfapp] at this
  have hbz : Matrix.mulVec M b = z := by rw [← hfapp]; exact hb
  have hzy : dotProduct z y = 0 := by
    have := horth y b hyk
    rwa [hbz] at this
  have hy0 : y = 0 := by
    have hcy : dotProduct c y = 0 := hker y fun i => by
      have := congrFun hyk i
      rwa [hmulVec] at this
    rw [← hyz, add_dotProduct, hzy, add_zero] at hcy
    exact eq_zero_of_dotProduct_self hcy
  refine ⟨b, fun i => ?_⟩
  have : Matrix.mulVec M b = c := by rw [hbz, ← hyz, hy0, zero_add]
  have := congrFun this i
  rwa [hmulVec] at this

end Toolkit

/-- **FY Theorem 3.1**: for a zero-mean weakly stationary process, `φ` minimizes the
prediction MSE **iff** it solves the Yule–Walker system (3.5)
`Σ_j φ_j γ(i − j) = γ(i)` for `i = 1..k` (lag bookkeeping: predicting one step ahead
from the `k` most recent values). -/
theorem predMSE_isMinOn_iff_yuleWalker [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    -- USER-INPUT: zero mean; FY §3.2 standing assumption
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {k : ℕ} (φ : Fin k → ℝ) :
    (∀ ψ : Fin k → ℝ, predMSE X μ k φ ≤ predMSE X μ k ψ) ↔
      ∀ i : Fin k, ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)
        = acvf X μ ((i : ℕ) + 1) := by
  rw [yuleWalker_iff_orthogonal hstat φ]
  refine ⟨fun hmin i => ?_, fun horth ψ => ?_⟩
  · -- Necessity: perturb `φ` in the direction `t · e_i` (FY §3.2, the derivative at `t = 0`).
    refine eq_zero_of_quadratic_nonneg hstat.acvf_zero_nonneg fun t => ?_
    have h := hmin fun j => φ j + if j = i then t else 0
    rw [predMSE_eq_add hstat hmean φ fun j => φ j + if j = i then t else 0] at h
    have hsum : ∑ j, ((φ j + if j = i then t else 0) - φ j) *
        cov[fun ω => X ((k : ℤ) + 1) ω - ∑ i, φ i * X ((k : ℤ) - (i : ℕ)) ω,
            X ((k : ℤ) - (j : ℕ)); μ]
        = t * cov[fun ω => X ((k : ℤ) + 1) ω - ∑ i, φ i * X ((k : ℤ) - (i : ℕ)) ω,
            X ((k : ℤ) - (i : ℕ)); μ] := by
      simp only [add_sub_cancel_left, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hvar : variance (fun ω => ∑ j, ((φ j + if j = i then t else 0) - φ j)
          * X ((k : ℤ) - (j : ℕ)) ω) μ = t ^ 2 * acvf X μ 0 := by
      have hfun : (fun ω => ∑ j, ((φ j + if j = i then t else 0) - φ j)
            * X ((k : ℤ) - (j : ℕ)) ω) = fun ω => t * X ((k : ℤ) - (i : ℕ)) ω := by
        funext ω
        simp only [add_sub_cancel_left, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
      rw [hfun, variance_const_mul, ← hstat.acvf_zero_eq_variance]
    rw [hsum, hvar] at h
    linarith
  · -- Sufficiency: the cross term vanishes and the quadratic term is a variance.
    rw [predMSE_eq_add hstat hmean φ ψ]
    have hcross : ∑ j, (ψ j - φ j) *
        cov[fun ω => X ((k : ℤ) + 1) ω - ∑ i, φ i * X ((k : ℤ) - (i : ℕ)) ω,
            X ((k : ℤ) - (j : ℕ)); μ] = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [horth j, mul_zero]
    have hq := variance_nonneg (fun ω => ∑ j, (ψ j - φ j) * X ((k : ℤ) - (j : ℕ)) ω) μ
    rw [hcross]
    linarith

/-- **Prewhitening** (FY §3.2, consequence of Thm 3.1's orthogonality): innovations at
different horizons are uncorrelated: if `φ` and `ψ` are Yule–Walker solutions at
horizons `k < l`, the corresponding innovations have zero covariance. -/
theorem innovations_uncorrelated [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {k l : ℕ} (hkl : k < l) {φ : Fin k → ℝ} {ψ : Fin l → ℝ}
    -- USER-INPUT: both are Yule–Walker solutions; FY Thm 3.1
    (hφ : ∀ i : Fin k, ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)
      = acvf X μ ((i : ℕ) + 1))
    (hψ : ∀ i : Fin l, ∑ j, ψ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)
      = acvf X μ ((i : ℕ) + 1)) :
    cov[fun ω => X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω,
        fun ω => X ((l : ℤ) + 1) ω - ∑ j, ψ j * X ((l : ℤ) - (j : ℕ)) ω; μ] = 0 := by
  have hkl' : (k : ℤ) < (l : ℤ) := by exact_mod_cast hkl
  -- the horizon-`l` innovation is orthogonal to all of `X_1, …, X_l` …
  have h1 : cov[fun ω => X ((l : ℤ) + 1) ω - ∑ j, ψ j * X ((l : ℤ) - (j : ℕ)) ω,
      X ((k : ℤ) + 1); μ] = 0 :=
    cov_predError_eq_zero_of_yuleWalker hstat hψ (by omega) (by omega)
  have h2 : ∀ j : Fin k, cov[fun ω => X ((l : ℤ) + 1) ω - ∑ i, ψ i * X ((l : ℤ) - (i : ℕ)) ω,
      X ((k : ℤ) - (j : ℕ)); μ] = 0 := by
    intro j
    have hj : ((j : ℕ) : ℤ) < (k : ℤ) := by exact_mod_cast j.isLt
    have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
    exact cov_predError_eq_zero_of_yuleWalker hstat hψ (by omega) (by omega)
  -- … and the horizon-`k` innovation is a linear combination of exactly those variables.
  rw [covariance_comm,
    covariance_fun_sub_right (memLp_predError hstat ψ) (hstat.memLp ((k : ℤ) + 1))
      (memLp_predWindow hstat φ),
    covariance_fun_sum_right
      (fun j : Fin k => (hstat.memLp ((k : ℤ) - (j : ℕ))).const_mul (φ j))
      (memLp_predError hstat ψ), h1]
  simp_rw [covariance_const_mul_right, h2]
  simp

/-- **Innovation variance identity** (FY eq. (3.7)): at a Yule–Walker solution,
`predMSE = ν_k = γ(0) − Σ_j φ_j γ(j+1)`. -/
theorem predMSE_eq_innovation_variance [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {k : ℕ} {φ : Fin k → ℝ}
    (hφ : ∀ i : Fin k, ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)
      = acvf X μ ((i : ℕ) + 1)) :
    predMSE X μ k φ = acvf X μ 0 - ∑ j, φ j * acvf X μ ((j : ℕ) + 1) := by
  have horth := (yuleWalker_iff_orthogonal hstat φ).mp hφ
  rw [predMSE_eq_variance hstat hmean φ,
    ← covariance_self (memLp_predError hstat φ).aestronglyMeasurable.aemeasurable,
    covariance_fun_sub_right (memLp_predError hstat φ) (hstat.memLp ((k : ℤ) + 1))
      (memLp_predWindow hstat φ),
    covariance_fun_sum_right
      (fun j : Fin k => (hstat.memLp ((k : ℤ) - (j : ℕ))).const_mul (φ j))
      (memLp_predError hstat φ)]
  simp_rw [covariance_const_mul_right, horth, mul_zero, Finset.sum_const_zero, sub_zero]
  -- what is left is the innovation variance (3.7), after `γ(−(j+1)) = γ(j+1)`
  rw [cov_predError_left hstat φ ((k : ℤ) + 1)]
  congr 1
  · congr 1
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [show ((k : ℤ) - (j : ℕ) - ((k : ℤ) + 1)) = -(((j : ℕ) : ℤ) + 1) from by ring,
      hstat.acvf_even]

/-- Existence of a Yule–Walker solution at every horizon (the finite-dimensional
projection always exists; no invertibility needed — FY takes it silently from the
projection formulation of Definition 3.1). -/
theorem exists_yuleWalker_solution [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (k : ℕ) :
    ∃ φ : Fin k → ℝ, ∀ i : Fin k,
      ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ) = acvf X μ ((i : ℕ) + 1) := by
  -- The Toeplitz system is consistent: its right-hand side annihilates its kernel, because a
  -- kernel vector makes the corresponding combination of the window a.s. constant.
  have hcov : ∀ i j : Fin k, cov[X ((k : ℤ) - (i : ℕ)), X ((k : ℤ) - (j : ℕ)); μ]
      = acvf X μ ((i : ℕ) - (j : ℕ) : ℤ) := by
    intro i j
    rw [hstat.cov_eq_acvf,
      show ((k : ℤ) - (i : ℕ)) - ((k : ℤ) - (j : ℕ)) = -((((i : ℕ) : ℤ)) - ((j : ℕ) : ℤ)) from
        by ring,
      hstat.acvf_even]
  have hker : ∀ x : Fin k → ℝ,
      (∀ i : Fin k, ∑ j : Fin k, acvf X μ ((i : ℕ) - (j : ℕ) : ℤ) * x j = 0) →
      ∑ i : Fin k, acvf X μ ((i : ℕ) + 1) * x i = 0 := by
    intro x hx
    have hrow : ∀ i : Fin k,
        ∑ j : Fin k, cov[X ((k : ℤ) - (i : ℕ)), X ((k : ℤ) - (j : ℕ)); μ] * x j = 0 := by
      intro i
      simp_rw [hcov]
      exact hx i
    have hvar : variance (fun ω => ∑ j, x j * X ((k : ℤ) - (j : ℕ)) ω) μ = 0 := by
      rw [variance_fun_sum fun (j : Fin k) => (hstat.memLp ((k : ℤ) - (j : ℕ))).const_mul (x j)]
      have hterm : ∀ i j : Fin k,
          cov[fun ω => x i * X ((k : ℤ) - (i : ℕ)) ω,
              fun ω => x j * X ((k : ℤ) - (j : ℕ)) ω; μ]
            = x i * (cov[X ((k : ℤ) - (i : ℕ)), X ((k : ℤ) - (j : ℕ)); μ] * x j) := by
        intro i j
        rw [covariance_const_mul_left, covariance_const_mul_right]
        ring
      simp_rw [hterm, ← Finset.mul_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [hrow i, mul_zero]
    have hconst : (fun ω => ∑ j, x j * X ((k : ℤ) - (j : ℕ)) ω)
        =ᵐ[μ] fun _ => ∫ ω, ∑ j, x j * X ((k : ℤ) - (j : ℕ)) ω ∂μ :=
      ae_eq_integral_of_variance_eq_zero (memLp_predWindow hstat x) hvar
    have hzero : cov[X ((k : ℤ) + 1), fun ω => ∑ j, x j * X ((k : ℤ) - (j : ℕ)) ω; μ] = 0 := by
      rw [covariance_congr_ae (EventuallyEq.refl _ (X ((k : ℤ) + 1))) hconst]
      exact covariance_const_right _
    rw [covariance_fun_sum_right
      (fun j : Fin k => (hstat.memLp ((k : ℤ) - (j : ℕ))).const_mul (x j))
      (hstat.memLp ((k : ℤ) + 1))] at hzero
    simp_rw [covariance_const_mul_right, hstat.cov_eq_acvf] at hzero
    rw [← hzero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 2
    ring
  obtain ⟨b, hb⟩ := exists_solution_of_symm
    (A := fun i j : Fin k => acvf X μ ((i : ℕ) - (j : ℕ) : ℤ))
    (c := fun i : Fin k => acvf X μ ((i : ℕ) + 1))
    (fun i j => by
      change acvf X μ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))
      rw [show (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = -(((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) from by ring,
        hstat.acvf_even]) hker
  exact ⟨b, fun i => by simpa [mul_comm] using hb i⟩

end StatLean.TimeSeries
