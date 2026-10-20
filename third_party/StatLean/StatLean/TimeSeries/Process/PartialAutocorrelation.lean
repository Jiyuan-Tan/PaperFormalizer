module
public import StatLean.TimeSeries.Process.LinearProcess
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Partial autocorrelation (FY §2.2.3, Definition 2.6, Proposition 2.3, Theorem 2.9)

The PACF via linear-regression residuals: for `k ≥ 2`,
`π(k) = Corr(R_{1|2..k}, R_{k+1|2..k})` where `R_{j|2..k}` is the residual of the best
linear approximation of `X_j` by `(X_2, …, X_k)` (FY Definition 2.6, eq. (2.28));
`π(1) = ρ(1)`. We take the **normal-equation coefficient vector** `Σ⁻¹γ` (with Mathlib's
junk-total `Matrix.inv`) as the regression coefficients — under the invertibility
hypothesis this *is* the arg-min of eq. (2.28), which we record as a lemma rather than a
definition. Main results:

* **Proposition 2.3(i)** (proof §2.7.2): the closed matrix formula FY eq. (2.29);
* **Proposition 2.3(ii)**: the PACF of a causal AR(p) vanishes beyond lag `p`;
* **Theorem 2.9** (proof §2.7.3): `π(k) = b_{kk}`, the last coefficient of the best
  linear AR(k) predictor (partitioned-inverse computation).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.2.3
(pp. 43–45: Definition 2.6, eqs. (2.28)–(2.29), Proposition 2.3, Theorem 2.9) and
§2.7.2–§2.7.3 (pp. 79–80). (`FY §2.2.3; §2.7.2–2.7.3`.)

**Proof formalization notes.**
* All objects are junk-total: `Matrix.inv` is the adjugate-based inverse (zero matrix
  when singular) and correlations divide by standard deviations (junk `0`); theorems
  carry the invertibility/nondegeneracy hypotheses the book leaves implicit (inventory
  flags).
* By stationarity everything is expressed through `acvf`; the covariance matrix of the
  window `(X_2, …, X_k)` is the Toeplitz matrix `Γ(i,j) = γ(i − j)`.
* FY's `R_{1|2..k}` vs `R_{k+1|2..k}` variance equality ("two-moment time
  reversibility") is the evenness of `γ` at the matrix level.

**Bibliographic comments.** Partial autocorrelation enters time-series identification
through Box & Jenkins (1970); the matrix formulas are classical multivariate regression
(cf. C. R. Rao, *Linear Statistical Inference*, 1973, p. 33 for the partitioned
inverse FY cites).
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **Toeplitz autocovariance matrix** of a window of length `n`:
`(i, j) ↦ γ(i − j)`. -/
noncomputable def acvfToeplitz (X : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)

/-- The **normal-equation coefficients** for regressing `X_{t₀}` on the window
`(X_{w 0}, …, X_{w (n−1)})`: `Σ⁻¹ γ_vec`, junk-total via `Matrix.inv`. -/
noncomputable def linRegCoeffs (X : ℤ → Ω → ℝ) (μ : Measure Ω) {n : ℕ}
    (t0 : ℤ) (w : Fin n → ℤ) : Fin n → ℝ :=
  (Matrix.of fun i j => cov[X (w i), X (w j); μ])⁻¹ *ᵥ
    (fun i => cov[X t0, X (w i); μ])

/-- The **regression residual** of `X_{t₀}` on the window `w`. -/
noncomputable def linRegResidual (X : ℤ → Ω → ℝ) (μ : Measure Ω) {n : ℕ}
    (t0 : ℤ) (w : Fin n → ℤ) : Ω → ℝ :=
  fun ω => X t0 ω - ∑ i, linRegCoeffs X μ t0 w i * X (w i) ω

/-- The **partial autocorrelation function** (FY Definition 2.6): `π(1) = ρ(1)`, and for
`k ≥ 2` the correlation of the residuals of `X_1` and `X_{k+1}` regressed on
`(X_2, …, X_k)`. Junk-total (`Matrix.inv` + division conventions). -/
noncomputable def pacf (X : ℤ → Ω → ℝ) (μ : Measure Ω) (k : ℕ) : ℝ :=
  if k ≤ 1 then acf X μ 1
  else
    let w : Fin (k - 1) → ℤ := fun i => (i : ℕ) + 2
    let R1 := linRegResidual X μ 1 w
    let R2 := linRegResidual X μ ((k : ℤ) + 1) w
    cov[R1, R2; μ] / (Real.sqrt (variance R1 μ) * Real.sqrt (variance R2 μ))

/-! ### The regression toolkit

Bilinearity of the covariance against the window, the normal equations `Σα = c` supplied
by `Matrix.mul_nonsing_inv`, and the resulting orthogonality `R ⊥ X_{w l}` — the three
facts every result below runs on. -/

section Toolkit

variable {X : ℤ → Ω → ℝ}

/-- Covariance only sees the a.e. class of each argument. -/
private lemma covariance_congr_ae {Y Y' Z Z' : Ω → ℝ} (hY : Y =ᵐ[μ] Y') (hZ : Z =ᵐ[μ] Z') :
    cov[Y, Z; μ] = cov[Y', Z'; μ] := by
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  have hIZ : ∫ x, Z x ∂μ = ∫ x, Z' x ∂μ := integral_congr_ae hZ
  simp only [covariance, hIY, hIZ]
  exact integral_congr_ae (by filter_upwards [hY, hZ] with ω h1 h2 using by rw [h1, h2])

/-- Definitional unfolding of the residual. -/
private lemma linRegResidual_eq (X : ℤ → Ω → ℝ) (μ : Measure Ω) {n : ℕ} (t0 : ℤ)
    (w : Fin n → ℤ) :
    linRegResidual X μ t0 w
      = fun ω => X t0 ω - ∑ i, linRegCoeffs X μ t0 w i * X (w i) ω := rfl

/-- Entrywise form of the normal-equation coefficients. -/
private lemma linRegCoeffs_eq (X : ℤ → Ω → ℝ) (μ : Measure Ω) {n : ℕ} (t0 : ℤ)
    (w : Fin n → ℤ) (i : Fin n) :
    linRegCoeffs X μ t0 w i
      = ∑ j, (Matrix.of fun i j => cov[X (w i), X (w j); μ])⁻¹ i j
          * cov[X t0, X (w j); μ] := rfl

/-- Square-integrability of a linear combination of the window. -/
private lemma memLp_window (hstat : IsStationary X μ) {n : ℕ} (w : Fin n → ℤ)
    (c : Fin n → ℝ) : MemLp (fun ω => ∑ i, c i * X (w i) ω) 2 μ :=
  memLp_finset_sum _ fun i _ => (hstat.memLp (w i)).const_mul (c i)

/-- Square-integrability of the regression residual. -/
private lemma memLp_linRegResidual (hstat : IsStationary X μ) {n : ℕ} (t0 : ℤ)
    (w : Fin n → ℤ) : MemLp (linRegResidual X μ t0 w) 2 μ :=
  (hstat.memLp t0).sub (memLp_window hstat w _)

/-- Bilinear expansion of the residual covariance. -/
private lemma cov_linRegResidual_left [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ) {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    cov[linRegResidual X μ t0 w, Y; μ]
      = cov[X t0, Y; μ] - ∑ i, linRegCoeffs X μ t0 w i * cov[X (w i), Y; μ] := by
  rw [linRegResidual_eq,
    covariance_fun_sub_left (hstat.memLp t0) (memLp_window hstat w _) hY,
    covariance_fun_sum_left (fun i => (hstat.memLp (w i)).const_mul _) hY]
  simp_rw [covariance_const_mul_left]

/-- The **normal equations** `Σ α = c` (FY §2.7.2): the defining property of
`linRegCoeffs`, from `M * M⁻¹ = 1`. -/
private lemma linRegCoeffs_normalEq {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) (l : Fin n) :
    ∑ j, cov[X (w l), X (w j); μ] * linRegCoeffs X μ t0 w j = cov[X t0, X (w l); μ] := by
  have h : (Matrix.of fun i j => cov[X (w i), X (w j); μ]) *ᵥ linRegCoeffs X μ t0 w
      = fun i => cov[X t0, X (w i); μ] := by
    rw [linRegCoeffs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hinv, Matrix.one_mulVec]
  simpa [Matrix.mulVec, dotProduct] using congrFun h l

/-- **Uniqueness** of the normal-equation solution under invertibility. -/
private lemma linRegCoeffs_eq_of_normalEq {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) (b : Fin n → ℝ)
    (hb : ∀ l, ∑ j, cov[X (w l), X (w j); μ] * b j = cov[X t0, X (w l); μ]) :
    linRegCoeffs X μ t0 w = b := by
  have hM : (Matrix.of fun i j => cov[X (w i), X (w j); μ]) *ᵥ b
      = fun i => cov[X t0, X (w i); μ] := by
    funext l; simpa [Matrix.mulVec, dotProduct] using hb l
  rw [linRegCoeffs, ← hM, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv,
    Matrix.one_mulVec]

/-- **Orthogonality** (FY eq. (2.70)): the residual is uncorrelated with every window
coordinate. -/
private lemma cov_linRegResidual_window [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) (l : Fin n) :
    cov[linRegResidual X μ t0 w, X (w l); μ] = 0 := by
  rw [cov_linRegResidual_left hstat t0 w (hstat.memLp (w l))]
  have h2 : ∑ i, linRegCoeffs X μ t0 w i * cov[X (w i), X (w l); μ]
      = ∑ j, cov[X (w l), X (w j); μ] * linRegCoeffs X μ t0 w j :=
    Finset.sum_congr rfl fun i _ => by rw [covariance_comm]; ring
  rw [h2, linRegCoeffs_normalEq t0 w hinv l, sub_self]

/-- The residual is uncorrelated with every linear combination of the window. -/
private lemma cov_linRegResidual_windowSum [IsProbabilityMeasure μ]
    (hstat : IsStationary X μ) {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) (c : Fin n → ℝ) :
    cov[linRegResidual X μ t0 w, fun ω => ∑ i, c i * X (w i) ω; μ] = 0 := by
  rw [covariance_fun_sum_right (fun i => (hstat.memLp (w i)).const_mul (c i))
    (memLp_linRegResidual hstat t0 w)]
  simp_rw [covariance_const_mul_right, cov_linRegResidual_window hstat t0 w hinv]
  simp

/-- The covariance of two residuals on a common window collapses onto the raw variable
(FY eq. (2.70)). -/
private lemma cov_linRegResidual_residual [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 t1 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) :
    cov[linRegResidual X μ t0 w, linRegResidual X μ t1 w; μ]
      = cov[X t0, X t1; μ] - ∑ i, linRegCoeffs X μ t0 w i * cov[X (w i), X t1; μ] := by
  have h1 : cov[linRegResidual X μ t0 w, linRegResidual X μ t1 w; μ]
      = cov[linRegResidual X μ t0 w, X t1; μ] := by
    rw [linRegResidual_eq X μ t1 w,
      covariance_fun_sub_right (memLp_linRegResidual hstat t0 w) (hstat.memLp t1)
        (memLp_window hstat w _),
      cov_linRegResidual_windowSum hstat t0 w hinv, sub_zero]
  rw [h1, cov_linRegResidual_left hstat t0 w (hstat.memLp t1)]

/-- The residual covariance in autocovariance form. -/
private lemma cov_linRegResidual_residual_acvf [IsProbabilityMeasure μ]
    (hstat : IsStationary X μ) {n : ℕ} (t0 t1 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) :
    cov[linRegResidual X μ t0 w, linRegResidual X μ t1 w; μ]
      = acvf X μ (t0 - t1) - ∑ i, linRegCoeffs X μ t0 w i * acvf X μ (w i - t1) := by
  rw [cov_linRegResidual_residual hstat t0 t1 w hinv]
  simp_rw [hstat.cov_eq_acvf]

/-- The residual variance in autocovariance form. -/
private lemma variance_linRegResidual [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) :
    variance (linRegResidual X μ t0 w) μ
      = acvf X μ 0 - ∑ i, linRegCoeffs X μ t0 w i * acvf X μ (w i - t0) := by
  rw [← covariance_self
      (memLp_linRegResidual hstat t0 w).aestronglyMeasurable.aemeasurable,
    cov_linRegResidual_residual_acvf hstat t0 t0 w hinv, sub_self]

/-- The coefficients are equivariant under a joint time shift and a relabelling of the
window: both leave every covariance entry unchanged. -/
private lemma linRegCoeffs_reindex_shift [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 s : ℤ) (w : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) :
    linRegCoeffs X μ (t0 + s) (fun i => w (σ i) + s)
      = fun i => linRegCoeffs X μ t0 w (σ i) := by
  have hcov : ∀ i j : Fin n,
      cov[X (w (σ i) + s), X (w (σ j) + s); μ] = cov[X (w (σ i)), X (w (σ j)); μ] := by
    intro i j
    rw [hstat.cov_eq_acvf, hstat.cov_eq_acvf]
    congr 1
    ring
  have hsub : (Matrix.of fun i j => cov[X (w (σ i) + s), X (w (σ j) + s); μ])
      = (Matrix.of fun i j => cov[X (w i), X (w j); μ]).submatrix σ σ := by
    ext i j; simpa using hcov i j
  have hinv' : IsUnit (Matrix.of fun i j => cov[X (w (σ i) + s), X (w (σ j) + s); μ]).det := by
    rw [hsub, Matrix.det_submatrix_equiv_self]; exact hinv
  refine linRegCoeffs_eq_of_normalEq _ _ hinv' _ fun l => ?_
  have hR : cov[X (t0 + s), X (w (σ l) + s); μ] = cov[X t0, X (w (σ l)); μ] := by
    rw [hstat.cov_eq_acvf, hstat.cov_eq_acvf]; congr 1; ring
  calc ∑ j, cov[X (w (σ l) + s), X (w (σ j) + s); μ] * linRegCoeffs X μ t0 w (σ j)
      = ∑ j, cov[X (w (σ l)), X (w (σ j)); μ] * linRegCoeffs X μ t0 w (σ j) :=
        Finset.sum_congr rfl fun j _ => by rw [hcov]
    _ = ∑ j, cov[X (w (σ l)), X (w j); μ] * linRegCoeffs X μ t0 w j :=
        Equiv.sum_comp σ fun j => cov[X (w (σ l)), X (w j); μ] * linRegCoeffs X μ t0 w j
    _ = cov[X t0, X (w (σ l)); μ] := linRegCoeffs_normalEq t0 w hinv (σ l)
    _ = cov[X (t0 + s), X (w (σ l) + s); μ] := hR.symm

/-- **Leading principal submatrices inherit nonsingularity** for autocovariance Toeplitz
matrices: a kernel vector of `Γ_n` makes the corresponding linear combination of the
process a.s. constant, hence extends by zero to a kernel vector of `Γ_{n+1}`. -/
private lemma isUnit_det_acvfToeplitz_of_succ [IsProbabilityMeasure μ]
    (hstat : IsStationary X μ) {n : ℕ}
    (hinv : IsUnit (acvfToeplitz X μ (n + 1)).det) : IsUnit (acvfToeplitz X μ n).det := by
  classical
  rw [isUnit_iff_ne_zero] at hinv ⊢
  intro h0
  obtain ⟨x, hx, hxz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hrow : ∀ i : Fin n, ∑ j : Fin n, acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j = 0 := by
    intro i
    simpa [Matrix.mulVec, dotProduct, acvfToeplitz] using congrFun hxz i
  have hcovu : ∀ i j : Fin n,
      cov[X (((i : ℕ) : ℤ)), X (((j : ℕ) : ℤ)); μ]
        = acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := fun i j => hstat.cov_eq_acvf _ _
  -- the linear combination has zero variance, hence is a.s. constant
  have hvar : variance (fun ω => ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω) μ = 0 := by
    rw [variance_fun_sum (fun i : Fin n => (hstat.memLp (((i : ℕ) : ℤ))).const_mul (x i))]
    have hterm : ∀ i j : Fin n,
        cov[fun ω => x i * X (((i : ℕ) : ℤ)) ω, fun ω => x j * X (((j : ℕ) : ℤ)) ω; μ]
          = x i * (acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j) := by
      intro i j
      rw [covariance_const_mul_left, covariance_const_mul_right, hcovu]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show ∑ j : Fin n, acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j = 0 from hrow i, mul_zero]
  have hconst : (fun ω => ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω)
      =ᵐ[μ] fun _ => ∫ ω, ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω ∂μ :=
    ae_eq_integral_of_variance_eq_zero
      (memLp_window hstat (fun i : Fin n => ((i : ℕ) : ℤ)) x) hvar
  have hcovS : ∀ t : ℤ, cov[X t, fun ω => ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω; μ] = 0 := by
    intro t
    rw [covariance_congr_ae (EventuallyEq.refl _ (X t)) hconst]
    exact covariance_const_right _
  -- extend the kernel vector by zero
  refine hinv (Matrix.exists_mulVec_eq_zero_iff.1
    ⟨fun i : Fin (n + 1) => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0, ?_, ?_⟩)
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    exact Function.ne_iff.2 ⟨i.castSucc, by simpa using hi⟩
  · funext l
    have hexp : (acvfToeplitz X μ (n + 1) *ᵥ
          fun i : Fin (n + 1) => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0) l
        = ∑ j : Fin n, acvf X μ (((l : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j := by
      simp only [Matrix.mulVec, dotProduct, acvfToeplitz, Matrix.of_apply]
      rw [Fin.sum_univ_castSucc]
      simp
    have hcs : ∑ j : Fin n, acvf X μ (((l : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j
        = cov[X (((l : ℕ) : ℤ)), fun ω => ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω; μ] := by
      rw [covariance_fun_sum_right
        (fun j : Fin n => (hstat.memLp (((j : ℕ) : ℤ))).const_mul (x j))
        (hstat.memLp (((l : ℕ) : ℤ)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [covariance_const_mul_right, hstat.cov_eq_acvf]
      ring
    rw [hexp, hcs, hcovS]
    rfl

end Toolkit

/-- The normal-equation coefficients minimize the mean-squared prediction error
(FY eq. (2.28)) — the arg-min property, under invertibility of the window covariance
matrix (the book's implicit hypothesis, inventory flag). -/
theorem linRegCoeffs_isMinOn [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    -- USER-INPUT: nondegenerate window covariance; implicit in FY eq. (2.28)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det)
    (β : Fin n → ℝ) :
    variance (linRegResidual X μ t0 w) μ ≤
      variance (fun ω => X t0 ω - ∑ i, β i * X (w i) ω) μ := by
  -- FY eq. (2.69): `X_{t₀} − βᵀW = R − (β−α)ᵀW`, and the cross term vanishes.
  have hkey : (fun ω => X t0 ω - ∑ i, β i * X (w i) ω)
      = fun ω => linRegResidual X μ t0 w ω
          - ∑ i, (β i - linRegCoeffs X μ t0 w i) * X (w i) ω := by
    funext ω
    simp only [linRegResidual_eq, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hkey, variance_fun_sub (memLp_linRegResidual hstat t0 w)
      (memLp_window hstat w _),
    cov_linRegResidual_windowSum hstat t0 w hinv]
  have := variance_nonneg (fun ω => ∑ i, (β i - linRegCoeffs X μ t0 w i) * X (w i) ω) μ
  linarith

/-! ### The PACF in residual form

`pacf` divides by `√(Var R₁)·√(Var R₂)`; FY's "two-moment time reversibility" says the two
residual variances agree, so the denominator is just `Var R₁`. At the coefficient level the
reversibility is `β = α ∘ rev`, which we get from the uniqueness of the normal-equation
solution together with the evenness of `γ`. -/

section Reversibility

variable {X : ℤ → Ω → ℝ}

/-- The `k ≤ 1` branch of `pacf`. -/
private lemma pacf_of_le_one (X : ℤ → Ω → ℝ) (μ : Measure Ω) {k : ℕ} (hk : k ≤ 1) :
    pacf X μ k = acf X μ 1 := by
  rw [pacf, if_pos hk]

/-- The `k ≥ 2` branch of `pacf`, with the window spelled out. -/
private lemma pacf_of_two_le (X : ℤ → Ω → ℝ) (μ : Measure Ω) {k : ℕ} (hk : 2 ≤ k) :
    pacf X μ k =
      cov[linRegResidual X μ 1 (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2),
          linRegResidual X μ ((k : ℤ) + 1)
            (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2); μ] /
        (Real.sqrt (variance (linRegResidual X μ 1
            (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2)) μ) *
          Real.sqrt (variance (linRegResidual X μ ((k : ℤ) + 1)
            (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2)) μ)) := by
  rw [pacf, if_neg (by omega : ¬ (k ≤ 1))]

/-- **Two-moment time reversibility** at the coefficient level (FY §2.7.2): regressing
`X_{m+2}` on `(X_2, …, X_{m+1})` gives the *reversed* coefficient vector of the regression
of `X_1` on the same window. -/
private lemma linRegCoeffs_rev [IsProbabilityMeasure μ] (hstat : IsStationary X μ) {m : ℕ}
    (hinv : IsUnit (Matrix.of fun i j : Fin m =>
      cov[X (((i : ℕ) : ℤ) + 2), X (((j : ℕ) : ℤ) + 2); μ]).det) :
    linRegCoeffs X μ ((m : ℤ) + 2) (fun i : Fin m => ((i : ℕ) : ℤ) + 2)
      = fun i => linRegCoeffs X μ 1 (fun i : Fin m => ((i : ℕ) : ℤ) + 2) (Fin.rev i) := by
  set w : Fin m → ℤ := fun i => ((i : ℕ) : ℤ) + 2 with hw
  have hrv : ∀ i : Fin m, ((Fin.rev i : Fin m) : ℕ) = m - 1 - (i : ℕ) := by
    intro i; rw [Fin.val_rev]; omega
  refine linRegCoeffs_eq_of_normalEq _ _ hinv _ fun l => ?_
  have hc : ∀ i j : Fin m,
      cov[X (w i), X (w j); μ] = acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := by
    intro i j; rw [hstat.cov_eq_acvf]; congr 1; simp only [hw]; ring
  calc ∑ j, cov[X (w l), X (w j); μ] * linRegCoeffs X μ 1 w (Fin.rev j)
      = ∑ j, cov[X (w (Fin.rev l)), X (w (Fin.revPerm j)); μ]
          * linRegCoeffs X μ 1 w (Fin.revPerm j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [hc, hc]
        simp only [Fin.revPerm_apply]
        have hneg : ((l : ℕ) : ℤ) - ((j : ℕ) : ℤ)
            = -((((Fin.rev l : Fin m) : ℕ) : ℤ) - (((Fin.rev j : Fin m) : ℕ) : ℤ)) := by
          rw [hrv, hrv]
          have h1 := l.isLt; have h2 := j.isLt
          omega
        rw [hneg, hstat.acvf_even]
    _ = ∑ j, cov[X (w (Fin.rev l)), X (w j); μ] * linRegCoeffs X μ 1 w j :=
        Equiv.sum_comp Fin.revPerm
          fun j => cov[X (w (Fin.rev l)), X (w j); μ] * linRegCoeffs X μ 1 w j
    _ = cov[X 1, X (w (Fin.rev l)); μ] := linRegCoeffs_normalEq 1 w hinv (Fin.rev l)
    _ = cov[X ((m : ℤ) + 2), X (w l); μ] := by
        rw [hstat.cov_eq_acvf, hstat.cov_eq_acvf]
        have hneg : (1 : ℤ) - w (Fin.rev l) = -(((m : ℤ) + 2) - w l) := by
          simp only [hw]
          rw [hrv]
          have h1 := l.isLt
          omega
        rw [hneg, hstat.acvf_even]

/-- **FY Definition 2.6 in residual form**: the two residual variances coincide, so the
PACF is the residual covariance divided by the (single) residual variance. -/
private lemma pacf_eq_cov_div_variance [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {k : ℕ} (hk : 1 ≤ k)
    (hinv : IsUnit (Matrix.of fun i j : Fin (k - 1) =>
      cov[X (((i : ℕ) : ℤ) + 2), X (((j : ℕ) : ℤ) + 2); μ]).det)
    (hpos : 0 < variance (linRegResidual X μ 1
      (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2)) μ) :
    pacf X μ k =
      cov[linRegResidual X μ 1 (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2),
          linRegResidual X μ ((k : ℤ) + 1)
            (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2); μ] /
        variance (linRegResidual X μ 1
          (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2)) μ := by
  rcases eq_or_lt_of_le hk with h1 | h2
  · -- `k = 1`: the window is empty and both residuals are the raw variables
    haveI : IsEmpty (Fin (k - 1)) := by
      rw [show k - 1 = 0 by omega]; infer_instance
    have hres : ∀ t : ℤ,
        linRegResidual X μ t (fun i : Fin (k - 1) => ((i : ℕ) : ℤ) + 2) = X t := by
      intro t; funext ω; simp [linRegResidual_eq]
    have hzero : (1 : ℤ) - ((k : ℤ) + 1) = -1 := by omega
    rw [pacf_of_le_one X μ (by omega), hres, hres, acf, hstat.cov_eq_acvf, hzero,
      hstat.acvf_even 1, ← hstat.acvf_zero_eq_variance 1]
  · -- `k ≥ 2`: reversibility identifies the two residual variances
    set w : Fin (k - 1) → ℤ := fun i => ((i : ℕ) : ℤ) + 2 with hw
    have hkm : (k : ℤ) + 1 = ((k - 1 : ℕ) : ℤ) + 2 := by omega
    have hrev : linRegCoeffs X μ ((k : ℤ) + 1) w
        = fun i => linRegCoeffs X μ 1 w (Fin.rev i) := by
      rw [hkm]; exact linRegCoeffs_rev hstat hinv
    have hrv : ∀ i : Fin (k - 1), ((Fin.rev i : Fin (k - 1)) : ℕ) = (k - 1) - 1 - (i : ℕ) := by
      intro i; rw [Fin.val_rev]; omega
    have hvar : variance (linRegResidual X μ ((k : ℤ) + 1) w) μ
        = variance (linRegResidual X μ 1 w) μ := by
      rw [variance_linRegResidual hstat _ w hinv, variance_linRegResidual hstat _ w hinv, hrev]
      congr 1
      rw [← Equiv.sum_comp Fin.revPerm
        fun i => linRegCoeffs X μ 1 w i * acvf X μ (w i - 1)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have hneg : w i - ((k : ℤ) + 1) = -(w (Fin.revPerm i) - 1) := by
        simp only [hw, Fin.revPerm_apply]
        rw [hrv]
        have h1 := i.isLt
        omega
      rw [hneg, hstat.acvf_even]
    rw [pacf_of_two_le X μ (by omega), hvar, Real.mul_self_sqrt hpos.le]

end Reversibility

/-- **Proposition 2.3(i)** (FY eq. (2.29); proof §2.7.2): the closed formula
`π(k) = (γ(k) − cᵀΣ⁻¹c̃) / (γ(0) − c̃ᵀΣ⁻¹c̃)` in Toeplitz form, under invertibility of
the inner-window covariance matrix. -/
theorem pacf_eq_matrix_formula [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) {k : ℕ} (hk : 2 ≤ k)
    (hinv : IsUnit (Matrix.of fun i j : Fin (k - 1) =>
      cov[X (((i : ℕ) + 2 : ℕ) : ℤ), X (((j : ℕ) + 2 : ℕ) : ℤ); μ]).det)
    -- USER-INPUT: nondegenerate residual variances; implicit in FY Def 2.6
    (hpos : 0 < variance (linRegResidual X μ 1
      (fun i : Fin (k - 1) => ((i : ℕ) + 2 : ℤ))) μ) :
    pacf X μ k =
      (acvf X μ k - ∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        acvf X μ ((k : ℤ) + 1 - ((i : ℕ) + 2)) *
          (Matrix.of fun i j : Fin (k - 1) =>
            acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)))⁻¹ i j *
          acvf X μ (((j : ℕ) + 2 : ℤ) - 1)) /
      (acvf X μ 0 - ∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        acvf X μ (1 - ((i : ℕ) + 2)) *
          (Matrix.of fun i j : Fin (k - 1) =>
            acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)))⁻¹ i j *
          acvf X μ (((j : ℕ) + 2 : ℤ) - 1)) := by
  have hcast : ∀ i : Fin (k - 1), ((((i : ℕ) + 2 : ℕ)) : ℤ) = ((i : ℕ) : ℤ) + 2 :=
    fun i => by push_cast; ring
  simp only [hcast] at hinv
  set w : Fin (k - 1) → ℤ := fun i => ((i : ℕ) : ℤ) + 2 with hw
  -- the window covariance matrix is the Toeplitz matrix of the statement
  have hMΓ : (Matrix.of fun i j => cov[X (w i), X (w j); μ])
      = Matrix.of fun i j : Fin (k - 1) => acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [hstat.cov_eq_acvf]
    congr 1
    simp only [hw]
    ring
  -- the coefficient vector in Toeplitz form (FY's `Σ⁻¹c̃`)
  have hα : ∀ i, linRegCoeffs X μ 1 w i
      = ∑ j, (Matrix.of fun i j : Fin (k - 1) =>
          acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)))⁻¹ i j
            * acvf X μ (((j : ℕ) + 2 : ℤ) - 1) := by
    intro i
    rw [linRegCoeffs_eq, hMΓ]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [hstat.cov_eq_acvf]
    have hneg : (1 : ℤ) - w j = -(((j : ℕ) + 2 : ℤ) - 1) := by simp only [hw]; ring
    rw [hneg, hstat.acvf_even]
  rw [pacf_eq_cov_div_variance hstat (by omega) hinv hpos,
    cov_linRegResidual_residual_acvf hstat 1 ((k : ℤ) + 1) w hinv,
    variance_linRegResidual hstat 1 w hinv]
  congr 1
  · -- numerator (FY's `γ(k) − cᵀΣ⁻¹c̃`)
    have h1 : (1 : ℤ) - ((k : ℤ) + 1) = -(k : ℤ) := by ring
    rw [h1, hstat.acvf_even]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hα i, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 : w i - ((k : ℤ) + 1) = -(((k : ℤ) + 1) - (((i : ℕ) : ℤ) + 2)) := by
      simp only [hw]; ring
    rw [h2, hstat.acvf_even]
    ring
  · -- denominator (FY's `γ(0) − c̃ᵀΣ⁻¹c̃`)
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hα i, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h3 : (1 : ℤ) - (((i : ℕ) : ℤ) + 2) = -(w i - 1) := by simp only [hw]; ring
    rw [h3, hstat.acvf_even]
    ring

/-! ### Theorem 2.9

Instead of Rao's partitioned inverse we verify the partitioned solution directly: the
vector whose last entry is `π(k)` and whose remaining entries are the inner-window
coefficients corrected by the residual projection solves the `k × k` normal equations, and
under invertibility the solution is unique. This is the Frisch–Waugh–Lovell step of
FY §2.7.3, carried out in covariance language. -/

section LastCoeff

variable {X : ℤ → Ω → ℝ}

/-- Entrywise form of the Toeplitz autocovariance matrix. -/
private lemma acvfToeplitz_apply (X : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) (i j : Fin n) :
    acvfToeplitz X μ n i j = acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := rfl

/-- `pacf` in residual form, indexed so that the inner window has length `m`. -/
private lemma pacf_succ_eq_cov_div_variance [IsProbabilityMeasure μ]
    (hstat : IsStationary X μ) {m : ℕ}
    (hinv : IsUnit (Matrix.of fun i j : Fin m =>
      cov[X (((i : ℕ) : ℤ) + 2), X (((j : ℕ) : ℤ) + 2); μ]).det)
    (hpos : 0 < variance (linRegResidual X μ 1
      (fun i : Fin m => ((i : ℕ) : ℤ) + 2)) μ) :
    pacf X μ (m + 1) =
      cov[linRegResidual X μ 1 (fun i : Fin m => ((i : ℕ) : ℤ) + 2),
          linRegResidual X μ ((m : ℤ) + 2)
            (fun i : Fin m => ((i : ℕ) : ℤ) + 2); μ] /
        variance (linRegResidual X μ 1 (fun i : Fin m => ((i : ℕ) : ℤ) + 2)) μ := by
  have h := pacf_eq_cov_div_variance hstat (k := m + 1) (by omega) hinv hpos
  rw [show ((m + 1 : ℕ) : ℤ) + 1 = (m : ℤ) + 2 by push_cast; ring] at h
  exact h

end LastCoeff

/-- **Theorem 2.9** (FY §2.2.3; proof §2.7.3, partitioned inverse): `π(k)` equals the
last coefficient of the best linear AR(k) predictor of `X_t` from
`(X_{t−1}, …, X_{t−k})`. -/
theorem pacf_eq_last_arCoeff [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) {k : ℕ} (hk : 1 ≤ k)
    (hinv : IsUnit (acvfToeplitz X μ k).det)
    (hpos : 0 < variance (linRegResidual X μ 1
      (fun i : Fin (k - 1) => ((i : ℕ) + 2 : ℤ))) μ) :
    pacf X μ k = linRegCoeffs X μ (k : ℤ)
      (fun i : Fin k => (k : ℤ) - 1 - (i : ℕ)) ⟨k - 1, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [show (fun i : Fin (m + 1) => ((m + 1 : ℕ) : ℤ) - 1 - ((i : ℕ) : ℤ))
      = (fun i : Fin (m + 1) => (m : ℤ) - ((i : ℕ) : ℤ)) from by funext i; push_cast; ring,
    show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 from by push_cast; ring]
  -- the outer window `(X_m, …, X_0)`, its head `(X_m, …, X_1)`, and the PACF window
  set v : Fin (m + 1) → ℤ := fun i => (m : ℤ) - ((i : ℕ) : ℤ) with hv
  set q : Fin m → ℤ := fun i => (m : ℤ) - ((i : ℕ) : ℤ) with hq
  set w : Fin m → ℤ := fun i => ((i : ℕ) : ℤ) + 2 with hw
  -- nonsingularity of the three window covariance matrices
  have hinvT : IsUnit (acvfToeplitz X μ m).det := isUnit_det_acvfToeplitz_of_succ hstat hinv
  have hinvv : IsUnit (Matrix.of fun i j : Fin (m + 1) => cov[X (v i), X (v j); μ]).det := by
    have he : (Matrix.of fun i j : Fin (m + 1) => cov[X (v i), X (v j); μ])
        = (acvfToeplitz X μ (m + 1))ᵀ := by
      ext i j
      simp only [Matrix.of_apply, Matrix.transpose_apply, acvfToeplitz_apply]
      rw [hstat.cov_eq_acvf]
      congr 1
      simp only [hv]
      ring
    rw [he, Matrix.det_transpose]; exact hinv
  have hinvq : IsUnit (Matrix.of fun i j : Fin m => cov[X (q i), X (q j); μ]).det := by
    have he : (Matrix.of fun i j : Fin m => cov[X (q i), X (q j); μ])
        = (acvfToeplitz X μ m)ᵀ := by
      ext i j
      simp only [Matrix.of_apply, Matrix.transpose_apply, acvfToeplitz_apply]
      rw [hstat.cov_eq_acvf]
      congr 1
      simp only [hq]
      ring
    rw [he, Matrix.det_transpose]; exact hinvT
  have hinvw : IsUnit (Matrix.of fun i j : Fin m => cov[X (w i), X (w j); μ]).det := by
    have he : (Matrix.of fun i j : Fin m => cov[X (w i), X (w j); μ])
        = acvfToeplitz X μ m := by
      ext i j
      simp only [Matrix.of_apply, acvfToeplitz_apply]
      rw [hstat.cov_eq_acvf]
      congr 1
      simp only [hw]
      ring
    rw [he]; exact hinvT
  -- the PACF window is the reversed head window, shifted one step forward
  have hqw : (fun i : Fin m => q (Fin.revPerm i) + 1) = w := by
    funext i
    simp only [hq, hw, Fin.revPerm_apply, Fin.val_rev]
    have := i.isLt
    omega
  have hα : linRegCoeffs X μ 1 w
      = fun i => linRegCoeffs X μ 0 q (Fin.revPerm i) := by
    have h := linRegCoeffs_reindex_shift hstat 0 1 q Fin.revPerm hinvq
    rw [hqw, zero_add] at h
    exact h
  have hβ : linRegCoeffs X μ ((m : ℤ) + 2) w
      = fun i => linRegCoeffs X μ ((m : ℤ) + 1) q (Fin.revPerm i) := by
    have h := linRegCoeffs_reindex_shift hstat ((m : ℤ) + 1) 1 q Fin.revPerm hinvq
    rw [hqw] at h
    rw [show (m : ℤ) + 2 = ((m : ℤ) + 1) + 1 from by ring]
    exact h
  -- transfer of the two residual second moments to the head window
  have hcov12 : cov[linRegResidual X μ 1 w, linRegResidual X μ ((m : ℤ) + 2) w; μ]
      = cov[linRegResidual X μ 0 q, linRegResidual X μ ((m : ℤ) + 1) q; μ] := by
    rw [cov_linRegResidual_residual_acvf hstat 1 ((m : ℤ) + 2) w hinvw,
      cov_linRegResidual_residual_acvf hstat 0 ((m : ℤ) + 1) q hinvq]
    simp only [hα]
    have h1 : acvf X μ ((1 : ℤ) - ((m : ℤ) + 2)) = acvf X μ ((0 : ℤ) - ((m : ℤ) + 1)) := by
      rw [show (1 : ℤ) - ((m : ℤ) + 2) = (0 : ℤ) - ((m : ℤ) + 1) from by ring]
    have h2 : ∑ i, linRegCoeffs X μ 0 q (Fin.revPerm i) * acvf X μ (w i - ((m : ℤ) + 2))
        = ∑ i, linRegCoeffs X μ 0 q i * acvf X μ (q i - ((m : ℤ) + 1)) := by
      rw [show ∑ i, linRegCoeffs X μ 0 q i * acvf X μ (q i - ((m : ℤ) + 1))
          = ∑ i, linRegCoeffs X μ 0 q (Fin.revPerm i)
              * acvf X μ (q (Fin.revPerm i) - ((m : ℤ) + 1)) from
        (Equiv.sum_comp Fin.revPerm _).symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have harg : w i - ((m : ℤ) + 2) = q (Fin.revPerm i) - ((m : ℤ) + 1) := by
        simp only [hw, hq, Fin.revPerm_apply, Fin.val_rev]
        have := i.isLt
        omega
      rw [harg]
    rw [h1, h2]
  have hvar1 : variance (linRegResidual X μ 1 w) μ
      = variance (linRegResidual X μ 0 q) μ := by
    rw [variance_linRegResidual hstat 1 w hinvw, variance_linRegResidual hstat 0 q hinvq]
    simp only [hα]
    have h2 : ∑ i, linRegCoeffs X μ 0 q (Fin.revPerm i) * acvf X μ (w i - 1)
        = ∑ i, linRegCoeffs X μ 0 q i * acvf X μ (q i - 0) := by
      rw [show ∑ i, linRegCoeffs X μ 0 q i * acvf X μ (q i - 0)
          = ∑ i, linRegCoeffs X μ 0 q (Fin.revPerm i)
              * acvf X μ (q (Fin.revPerm i) - 0) from (Equiv.sum_comp Fin.revPerm _).symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have harg : w i - (1 : ℤ) = q (Fin.revPerm i) - 0 := by
        simp only [hw, hq, Fin.revPerm_apply, Fin.val_rev]
        have := i.isLt
        omega
      rw [harg]
    rw [h2]
  -- the last coefficient: FY's `π(k) = Cov(R_Y, R_W)/Var R_W`
  set θ : ℝ := cov[linRegResidual X μ ((m : ℤ) + 1) q, linRegResidual X μ 0 q; μ]
    / variance (linRegResidual X μ 0 q) μ with hθdef
  have hvarne : variance (linRegResidual X μ 0 q) μ ≠ 0 := by
    rw [← hvar1]; exact ne_of_gt hpos
  have hpacf : pacf X μ (m + 1) = θ := by
    rw [pacf_succ_eq_cov_div_variance hstat hinvw hpos, hcov12, hvar1, hθdef,
      covariance_comm (linRegResidual X μ 0 q)]
  -- the two identities that make the last normal equation hold
  have hRYX0 : cov[linRegResidual X μ ((m : ℤ) + 1) q, X 0; μ]
      = cov[linRegResidual X μ ((m : ℤ) + 1) q, linRegResidual X μ 0 q; μ] := by
    rw [cov_linRegResidual_left hstat ((m : ℤ) + 1) q (hstat.memLp 0),
      cov_linRegResidual_residual hstat ((m : ℤ) + 1) 0 q hinvq]
  have hRWX0 : cov[linRegResidual X μ 0 q, X 0; μ]
      = variance (linRegResidual X μ 0 q) μ := by
    rw [cov_linRegResidual_left hstat 0 q (hstat.memLp 0),
      ← covariance_self (memLp_linRegResidual hstat 0 q).aestronglyMeasurable.aemeasurable,
      cov_linRegResidual_residual hstat 0 0 q hinvq]
  -- the partitioned candidate solution
  set b : Fin (m + 1) → ℝ := fun j =>
    if h : (j : ℕ) < m then
      linRegCoeffs X μ ((m : ℤ) + 1) q ⟨j, h⟩ - θ * linRegCoeffs X μ 0 q ⟨j, h⟩
    else θ with hbdef
  have hbcast : ∀ i : Fin m, b i.castSucc
      = linRegCoeffs X μ ((m : ℤ) + 1) q i - θ * linRegCoeffs X μ 0 q i := by
    intro i
    simp [hbdef, i.isLt]
  have hblast : b (Fin.last m) = θ := by simp [hbdef]
  have hvcast : ∀ i : Fin m, v i.castSucc = q i := by
    intro i; simp only [hv, hq, Fin.val_castSucc]
  have hvlast : v (Fin.last m) = 0 := by simp [hv]
  -- the candidate's prediction error is `R_Y − θ R_W`
  have hT : (fun ω => X ((m : ℤ) + 1) ω - ∑ j, b j * X (v j) ω)
      = fun ω => linRegResidual X μ ((m : ℤ) + 1) q ω
          - θ * linRegResidual X μ 0 q ω := by
    funext ω
    have hsplit : ∑ j, b j * X (v j) ω
        = (∑ i : Fin m, (linRegCoeffs X μ ((m : ℤ) + 1) q i
              - θ * linRegCoeffs X μ 0 q i) * X (q i) ω) + θ * X 0 ω := by
      rw [Fin.sum_univ_castSucc, hblast, hvlast]
      exact congrArg (· + θ * X 0 ω)
        (Finset.sum_congr rfl fun i _ => by rw [hbcast, hvcast])
    have hd : ∑ i : Fin m, (linRegCoeffs X μ ((m : ℤ) + 1) q i
            - θ * linRegCoeffs X μ 0 q i) * X (q i) ω
        = (∑ i, linRegCoeffs X μ ((m : ℤ) + 1) q i * X (q i) ω)
          - ∑ i, θ * (linRegCoeffs X μ 0 q i * X (q i) ω) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have he : ∑ i : Fin m, θ * (linRegCoeffs X μ 0 q i * X (q i) ω)
        = θ * ∑ i, linRegCoeffs X μ 0 q i * X (q i) ω := by rw [Finset.mul_sum]
    rw [hsplit, hd, he, linRegResidual_eq, linRegResidual_eq]
    ring
  -- the candidate satisfies the `k × k` normal equations
  have hbeq : linRegCoeffs X μ ((m : ℤ) + 1) v = b := by
    refine linRegCoeffs_eq_of_normalEq _ _ hinvv b fun l => ?_
    have hsum : ∑ j, cov[X (v l), X (v j); μ] * b j
        = cov[X (v l), fun ω => ∑ j, b j * X (v j) ω; μ] := by
      rw [covariance_fun_sum_right (fun j => (hstat.memLp (v j)).const_mul (b j))
        (hstat.memLp (v l))]
      exact Finset.sum_congr rfl fun j _ => by rw [covariance_const_mul_right]; ring
    have hexp : cov[X (v l), fun ω => X ((m : ℤ) + 1) ω - ∑ j, b j * X (v j) ω; μ]
        = cov[X (v l), X ((m : ℤ) + 1); μ]
          - cov[X (v l), fun ω => ∑ j, b j * X (v j) ω; μ] :=
      covariance_fun_sub_right (hstat.memLp (v l)) (hstat.memLp _) (memLp_window hstat v b)
    have hkey : cov[X (v l), fun ω => X ((m : ℤ) + 1) ω - ∑ j, b j * X (v j) ω; μ] = 0 := by
      rw [hT, covariance_fun_sub_right (hstat.memLp (v l))
          (memLp_linRegResidual hstat ((m : ℤ) + 1) q)
          ((memLp_linRegResidual hstat 0 q).const_mul θ),
        covariance_const_mul_right]
      refine Fin.lastCases ?_ ?_ l
      · rw [hvlast, covariance_comm (X 0), covariance_comm (X 0), hRYX0, hRWX0, hθdef]
        field_simp
        ring
      · intro i
        rw [hvcast, covariance_comm (X (q i)), covariance_comm (X (q i)),
          cov_linRegResidual_window hstat ((m : ℤ) + 1) q hinvq i,
          cov_linRegResidual_window hstat 0 q hinvq i]
        ring
    rw [hsum, covariance_comm (X ((m : ℤ) + 1)) (X (v l))]
    linarith [hexp, hkey]
  rw [hpacf, hbeq]
  exact hblast.symm

/-! ### Causality and the Yule–Walker equations

For Proposition 2.3(ii) the only analytic input is that an innovation is uncorrelated with
the strict past of the process it drives; that is the `L²`-continuity argument applied to
the MA(∞) representation, and it turns the AR(p) recurrence into the Yule–Walker equations
at every lag. -/

section Causality

/-- `inner ℝ` on the reals is multiplication. -/
private lemma real_inner_mul' (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

/-- The `L²` inner product of two classes is the integral of the product. -/
private lemma inner_toLp' {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [real_inner_mul', h1, h2]

/-- **Causality**: an innovation is uncorrelated with the strict past of the linear process
it drives. The finite partial sums of the MA(∞) representation are exactly orthogonal to
`ε_t`, and they converge to `X_s` in `L²`. -/
private lemma cov_eq_zero_of_lt [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hlin : IsLinearProcessOf ψ X ε μ) (hε : IsWhiteNoise ε σ2 μ)
    {s t : ℤ} (hX : MemLp (X s) 2 μ) (hst : s < t) :
    cov[X s, ε t; μ] = 0 := by
  have hSm : ∀ N : ℕ,
      MemLp (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω) 2 μ := fun N =>
    memLp_finset_sum _ fun j _ => (hε.memLp (s - (j : ℕ))).const_mul (ψ j)
  -- the partial sums are exactly orthogonal to the future innovation
  have hSc : ∀ N : ℕ,
      cov[fun ω => ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω, ε t; μ] = 0 := by
    intro N
    rw [covariance_fun_sum_left'
      (fun j _ => (hε.memLp (s - (j : ℕ))).const_mul (ψ j)) (hε.memLp t)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [covariance_const_mul_left, hε.uncorrelated _ _ (by omega), mul_zero]
  -- so the covariance is that of the (vanishing) `L²` remainder
  have hbound : ∀ N : ℕ, |cov[X s, ε t; μ]|
      ≤ (eLpNorm (fun ω => X s ω - ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω) 2 μ).toReal
        * ‖(hε.memLp t).toLp (ε t)‖ := by
    intro N
    have hDm : MemLp
        (fun ω => X s ω - ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω) 2 μ :=
      hX.sub (hSm N)
    have hD : cov[X s, ε t; μ]
        = cov[fun ω => X s ω - ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω, ε t; μ] := by
      rw [covariance_fun_sub_left hX (hSm N) (hε.memLp t), hSc N, sub_zero]
    have hcv : cov[fun ω => X s ω - ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω, ε t; μ]
        = inner ℝ (hDm.toLp _) ((hε.memLp t).toLp (ε t)) := by
      rw [inner_toLp' hDm (hε.memLp t), covariance_eq_sub hDm (hε.memLp t),
        hε.integral_eq_zero t, mul_zero, sub_zero]
      simp [Pi.mul_apply]
    rw [hD, hcv, ← Lp.norm_toLp _ hDm]
    exact abs_real_inner_le_norm _ _
  have h0 : Tendsto (fun N : ℕ =>
      (eLpNorm (fun ω => X s ω - ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω) 2 μ).toReal)
      atTop (𝓝 0) := by
    simpa using! (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hlin s)
  have hlim : Tendsto (fun N : ℕ =>
      (eLpNorm (fun ω => X s ω - ∑ j ∈ Finset.range N, ψ j * ε (s - (j : ℕ)) ω) 2 μ).toReal
        * ‖(hε.memLp t).toLp (ε t)‖) atTop (𝓝 0) := by
    simpa using h0.mul_const ‖(hε.memLp t).toLp (ε t)‖
  exact abs_eq_zero.mp (le_antisymm
    (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound) (abs_nonneg _))

end Causality

/-- **Proposition 2.3(ii)**: the PACF of a causal AR(p) process vanishes beyond lag
`p` (from Theorem 2.9 and the Yule–Walker structure: the best AR(k) predictor for
`k > p` uses only the first `p` coefficients). -/
theorem pacf_eq_zero_of_isAR [IsProbabilityMeasure μ] {p : ℕ} {b : Fin p → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsAR b σ2 X ε μ) (hstat : IsStationary X μ)
    -- USER-INPUT: causality, as an explicit MA(∞) representation; FY Prop 2.3(ii)
    {ψ : ℕ → ℝ} (hψ : Summable fun n => |ψ n|) (hlin : IsLinearProcessOf ψ X ε μ)
    {k : ℕ}
    -- USER-INPUT: lag beyond the AR order; FY Prop 2.3(ii)
    (hk : p < k)
    (hinv : IsUnit (acvfToeplitz X μ k).det)
    (hpos : 0 < variance (linRegResidual X μ 1
      (fun i : Fin (k - 1) => ((i : ℕ) + 2 : ℤ))) μ) :
    pacf X μ k = 0 := by
  classical
  rw [pacf_eq_last_arCoeff hstat (by omega) hinv hpos]
  set v : Fin k → ℤ := fun i => (k : ℤ) - 1 - ((i : ℕ) : ℤ) with hv
  have hinvv : IsUnit (Matrix.of fun i j : Fin k => cov[X (v i), X (v j); μ]).det := by
    have he : (Matrix.of fun i j : Fin k => cov[X (v i), X (v j); μ])
        = (acvfToeplitz X μ k)ᵀ := by
      ext i j
      simp only [Matrix.of_apply, Matrix.transpose_apply, acvfToeplitz_apply]
      rw [hstat.cov_eq_acvf]
      congr 1
      simp only [hv]
      ring
    rw [he, Matrix.det_transpose]; exact hinv
  -- the AR coefficient vector padded with zeros
  set c : Fin k → ℝ := fun j => if hj : (j : ℕ) < p then b ⟨j, hj⟩ else 0 with hc
  have hpad : ∀ ω, ∑ j, c j * X (v j) ω
      = ∑ i : Fin p, b i * X ((k : ℤ) - 1 - ((i : ℕ) : ℤ)) ω := by
    intro ω
    have hg : ∑ j, c j * X (v j) ω
        = ∑ j ∈ Finset.range k,
            (if hj : j < p then b ⟨j, hj⟩ else 0) * X ((k : ℤ) - 1 - (j : ℤ)) ω :=
      Fin.sum_univ_eq_sum_range
        (fun j => (if hj : j < p then b ⟨j, hj⟩ else 0) * X ((k : ℤ) - 1 - (j : ℤ)) ω) k
    have hres : ∑ j ∈ Finset.range k,
          (if hj : j < p then b ⟨j, hj⟩ else 0) * X ((k : ℤ) - 1 - (j : ℤ)) ω
        = ∑ j ∈ Finset.range p,
            (if hj : j < p then b ⟨j, hj⟩ else 0) * X ((k : ℤ) - 1 - (j : ℤ)) ω := by
      refine (Finset.sum_subset
        (fun x hx => Finset.mem_range.2 ((Finset.mem_range.1 hx).trans hk))
        fun j hj hjn => ?_).symm
      rw [Finset.mem_range] at hjn
      rw [dif_neg hjn, zero_mul]
    rw [hg, hres, ← Fin.sum_univ_eq_sum_range
      (fun j => (if hj : j < p then b ⟨j, hj⟩ else 0) * X ((k : ℤ) - 1 - (j : ℤ)) ω) p]
    exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]
  -- the candidate's prediction error is the innovation
  have hresid : (fun ω => X (k : ℤ) ω - ∑ j, c j * X (v j) ω) =ᵐ[μ] ε (k : ℤ) := by
    filter_upwards [h.recurrence (k : ℤ)] with ω hω
    rw [hpad ω, hω]
    simp
  -- hence the Yule–Walker equations hold at every lag `1 ≤ i ≤ k`
  have hbeq : linRegCoeffs X μ (k : ℤ) v = c := by
    refine linRegCoeffs_eq_of_normalEq _ _ hinvv c fun l => ?_
    have hsum : ∑ j, cov[X (v l), X (v j); μ] * c j
        = cov[X (v l), fun ω => ∑ j, c j * X (v j) ω; μ] := by
      rw [covariance_fun_sum_right (fun j => (hstat.memLp (v j)).const_mul (c j))
        (hstat.memLp (v l))]
      exact Finset.sum_congr rfl fun j _ => by rw [covariance_const_mul_right]; ring
    have hexp : cov[X (v l), fun ω => X (k : ℤ) ω - ∑ j, c j * X (v j) ω; μ]
        = cov[X (v l), X (k : ℤ); μ]
          - cov[X (v l), fun ω => ∑ j, c j * X (v j) ω; μ] :=
      covariance_fun_sub_right (hstat.memLp (v l)) (hstat.memLp _) (memLp_window hstat v c)
    have hkey : cov[X (v l), fun ω => X (k : ℤ) ω - ∑ j, c j * X (v j) ω; μ] = 0 := by
      rw [covariance_congr_ae (EventuallyEq.refl _ (X (v l))) hresid]
      refine cov_eq_zero_of_lt hlin h.whiteNoise (hstat.memLp (v l)) ?_
      simp only [hv]
      omega
    rw [hsum, covariance_comm (X (k : ℤ)) (X (v l))]
    linarith [hexp, hkey]
  rw [hbeq]
  simp only [hc]
  exact dif_neg (by omega)

end StatLean.TimeSeries
