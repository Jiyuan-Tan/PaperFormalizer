module
public import StatLean.TimeSeries.Stationarity.ARMAExistence
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The Gaussian ARMA likelihood (FY §3.3.1, eqs. (3.9)–(3.13))

The parametric objects of ARMA maximum likelihood:

* the **model-implied ACVF** `armaACVF b a k = Σ_j ψ_j ψ_{j+|k|}` (unit noise
  variance; FY eq. (2.2) applied to the transfer coefficients `armaPsi`) and its
  Toeplitz matrices `armaToeplitz`;
* the **identifiability/invertibility constraint set** (FY eq. (3.11)):
  `b(z) a(z) ≠ 0` on `|z| ≤ 1` (`ARMAInvertibleParams`);
* the **Gaussian negative twice-log-likelihood** in covariance form
  (`armaNegTwoLogLik`; equivalent to FY's innovations form (3.9) through the LDLᵀ
  factorization, which FY uses only for computation);
* the **profiling identities** (FY eqs. (3.12)–(3.13)): `σ̂² = S/T` and the profiled
  criterion `log(S/T) + T⁻¹ log det Γ_T`;
* structural targets: summability of the model ACVF on the constraint set (geometric
  ψ-decay), the link `acvf X = σ² · armaACVF` for an actual stationary causal ARMA
  process, and positive-definiteness of `armaToeplitz` on the constraint set (via the
  spectral lower bound `g ≥ c > 0` on the circle).

**MLE (FY eq. (3.10)).** The book prints `arg min` — corrected to `arg max` of the
likelihood, i.e. minimization of `armaNegTwoLogLik`; estimator sequences are treated
as hypotheses ("a measurable sequence minimizing the criterion over the constraint
set"), consumed by `ARMA/MLEAsymptotics.lean`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.3.1,
eqs. (3.9)–(3.13) (pp. 93–95). (`FY §3.3.1`.)

**Bibliographic comments.** The innovations-form Gaussian likelihood is Schweppe
(1965) / Ansley (1979); the covariance form is classical multivariate normal theory.
Root-flipping identifiability is Brockwell & Davis (1991) Prop 4.4.2.
-/

open MeasureTheory ProbabilityTheory Filter Polynomial Matrix
open scoped ProbabilityTheory Topology Real

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **model-implied ACVF at unit noise variance** (FY eq. (2.2) for the transfer
coefficients): `γ_{b,a}(k) = Σ_{j≥0} ψ_j ψ_{j+|k|}`; junk (`tsum` = 0 convention)
outside the summable regime. -/
noncomputable def armaACVF {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (k : ℤ) : ℝ :=
  ∑' j : ℕ, armaPsi b a j * armaPsi b a (j + k.natAbs)

/-- The model-implied Toeplitz covariance matrix `Γ_T(b, a)` (unit noise variance). -/
noncomputable def armaToeplitz {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (T : ℕ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i j => armaACVF b a ((i : ℤ) - (j : ℤ))

/-- **FY eq. (3.11)**: the identifiability/invertibility parameter set
`𝓑 = {(b, a) : b(z) a(z) ≠ 0 for |z| ≤ 1}`. -/
def ARMAInvertibleParams {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) : Prop :=
  NoRootClosedDisc b ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z (maPoly a) ≠ 0

/-- The **Gaussian negative twice-log-likelihood** of data `x` under the ARMA
parameters `(b, a, σ²)`, covariance form:
`T log(2πσ²) + log det Γ_T + σ⁻² xᵀ Γ_T⁻¹ x` (junk when `Γ_T` is singular, by the
matrix-inverse convention). -/
noncomputable def armaNegTwoLogLik {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (σ2 : ℝ) {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  (T : ℝ) * Real.log (2 * π * σ2) + Real.log (armaToeplitz b a T).det
    + σ2⁻¹ * (x ⬝ᵥ ((armaToeplitz b a T)⁻¹ *ᵥ x))

/-- The **profiling sum of squares** `S(b, a) = xᵀ Γ_T⁻¹ x` (FY eq. (3.12)'s
numerator). -/
noncomputable def armaProfileS {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  x ⬝ᵥ ((armaToeplitz b a T)⁻¹ *ᵥ x)

/-- **FY eq. (3.13)**: the profiled (σ²-maximized) criterion
`ℓ*(b, a) = log(S(b, a)/T) + T⁻¹ log det Γ_T`. -/
noncomputable def armaProfileCriterion {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  Real.log (armaProfileS b a x / T) + (T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det

/-- On the constraint set the model ACVF is absolutely summable (geometric ψ-decay,
FY Thm 2.1 machinery). -/
theorem summable_abs_armaACVF {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    Summable fun k : ℤ => |armaACVF b a k| := by
  obtain ⟨C, hC, r, hr0, hr1, hbnd⟩ := exists_geometric_bound_armaPsi a hB.1
  have hr2nn : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hgeom : Summable fun j : ℕ => (r ^ 2) ^ j := summable_geometric_of_lt_one hr2nn hr2
  have hgeomval : ∑' j : ℕ, (r ^ 2) ^ j = (1 - r ^ 2)⁻¹ := tsum_geometric_of_lt_one hr2nn hr2
  -- the Cauchy-product estimate `|ψ_j ψ_{j+m}| ≤ C² r^m (r²)^j`
  have hterm : ∀ m j : ℕ,
      |armaPsi b a j * armaPsi b a (j + m)| ≤ C ^ 2 * r ^ m * (r ^ 2) ^ j := by
    intro m j
    rw [abs_mul]
    calc |armaPsi b a j| * |armaPsi b a (j + m)|
        ≤ (C * r ^ j) * (C * r ^ (j + m)) :=
          mul_le_mul (hbnd j) (hbnd (j + m)) (abs_nonneg _) (by positivity)
      _ = C ^ 2 * r ^ m * (r ^ 2) ^ j := by rw [pow_add, ← pow_mul]; ring
  have hsum : ∀ m : ℕ, Summable fun j : ℕ => |armaPsi b a j * armaPsi b a (j + m)| :=
    fun m => Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (hterm m) (hgeom.mul_left _)
  -- hence `|γ(k)| ≤ (C²/(1 − r²)) r^{|k|}`
  have hACVF : ∀ k : ℤ, |armaACVF b a k| ≤ C ^ 2 / (1 - r ^ 2) * r ^ k.natAbs := by
    intro k
    have h1 : |armaACVF b a k| ≤ ∑' j : ℕ, |armaPsi b a j * armaPsi b a (j + k.natAbs)| := by
      rw [armaACVF, ← Real.norm_eq_abs]
      simpa [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun j : ℕ => armaPsi b a j * armaPsi b a (j + k.natAbs))
          (by simpa [Real.norm_eq_abs] using hsum k.natAbs)
    have h2 : ∑' j : ℕ, |armaPsi b a j * armaPsi b a (j + k.natAbs)|
        ≤ ∑' j : ℕ, C ^ 2 * r ^ k.natAbs * (r ^ 2) ^ j :=
      (hsum _).tsum_le_tsum (hterm _) (hgeom.mul_left _)
    have h3 : ∑' j : ℕ, C ^ 2 * r ^ k.natAbs * (r ^ 2) ^ j
        = C ^ 2 / (1 - r ^ 2) * r ^ k.natAbs := by
      rw [tsum_mul_left, hgeomval]; ring
    linarith
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hACVF ?_
  refine Summable.of_nat_of_neg ?_ ?_ <;>
    simpa using (summable_geometric_of_lt_one hr0 hr1).mul_left (C ^ 2 / (1 - r ^ 2))

/-- **The model/process ACVF link**: a stationary causal ARMA(p, q) process with noise
variance `σ²` has `acvf X μ k = σ² · armaACVF b a k` (FY eq. (2.2); connects the
parametric likelihood objects to the process). -/
theorem acvf_eq_smul_armaACVF [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ)
    -- USER-INPUT: causal representation; FY §3.1 standing assumption
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    -- USER-INPUT: no roots on the closed disc; FY §3.1
    (hroot : NoRootClosedDisc b) (k : ℤ) :
    acvf X μ k = σ2 * armaACVF b a k := by
  exact (hcausal.isStationary (summable_abs_armaPsi a hroot) h.whiteNoise h.measurableX).2 k

/-- **FY eq. (3.12)**: at fixed `(b, a)` the Gaussian likelihood is maximized in `σ²`
at `σ̂² = S(b, a)/T`, and the minimized value is the profiled criterion up to the
additive constant `T(log(2π) + 1)`. Requires nondegenerate data (`S > 0`). -/
theorem armaNegTwoLogLik_profile {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    {T : ℕ} (hT : 0 < T) {x : Fin T → ℝ}
    -- LEAN-ONLY: nondegenerate profiling sum (a.s. under continuous data laws)
    (hS : 0 < armaProfileS b a x) :
    (∀ σ2 : ℝ, 0 < σ2 →
        armaNegTwoLogLik b a (armaProfileS b a x / T) x ≤ armaNegTwoLogLik b a σ2 x) ∧
      armaNegTwoLogLik b a (armaProfileS b a x / T) x
        = (T : ℝ) * armaProfileCriterion b a x + (T : ℝ) * (Real.log (2 * π) + 1) := by
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.2 hT
  have hT0 : (T : ℝ) ≠ 0 := hTpos.ne'
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  simp only [armaNegTwoLogLik, armaProfileCriterion, armaProfileS] at hS ⊢
  set S : ℝ := x ⬝ᵥ ((armaToeplitz b a T)⁻¹ *ᵥ x) with hSdef
  set L : ℝ := Real.log (armaToeplitz b a T).det with hLdef
  have hS0 : S ≠ 0 := hS.ne'
  have hST : (0 : ℝ) < S / T := div_pos hS hTpos
  -- `σ̂²⁻¹ S = T` and `T · T⁻¹ L = L`
  have hSTinv : (S / (T : ℝ))⁻¹ * S = T := by field_simp
  have hLT : (T : ℝ) * ((T : ℝ)⁻¹ * L) = L := by field_simp
  constructor
  · intro σ2 hσ
    -- the scale-free ratio `u = σ² T / S`
    have hu : (0 : ℝ) < σ2 * T / S := div_pos (mul_pos hσ hTpos) hS
    -- `log u + u⁻¹ ≥ 1`, i.e. `log y ≤ y - 1` at `y = u⁻¹`
    have hkey : 1 ≤ Real.log (σ2 * T / S) + (σ2 * T / S)⁻¹ := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.2 hu)
      rw [Real.log_inv] at h
      linarith
    have hlogσ : Real.log σ2 = Real.log (S / T) + Real.log (σ2 * T / S) := by
      rw [← Real.log_mul hST.ne' hu.ne']
      congr 1
      field_simp
    have hinv : σ2⁻¹ * S = (T : ℝ) * (σ2 * T / S)⁻¹ := by field_simp
    rw [Real.log_mul h2pi.ne' hST.ne', Real.log_mul h2pi.ne' hσ.ne', hSTinv, hlogσ, hinv]
    have hmul : (T : ℝ) * 1 ≤ (T : ℝ) * (Real.log (σ2 * T / S) + (σ2 * T / S)⁻¹) :=
      mul_le_mul_of_nonneg_left hkey hTpos.le
    linarith
  · rw [Real.log_mul h2pi.ne' hST.ne', hSTinv]
    linarith [hLT]

section Toeplitz

/-- The **one-sided transfer kernel** `ψ̃(m, s) = ψ_{m−s} · 1{s ≤ m}`. It is the
(lower-triangular, unit-diagonal) Cholesky-type factor of the model Toeplitz matrices:
`γ(s − t) = Σ_m ψ̃(m, s) ψ̃(m, t)` (`armaACVF_eq_tsum_psiKer`). -/
private noncomputable def psiKer {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (m s : ℕ) : ℝ :=
  if s ≤ m then armaPsi b a (m - s) else 0

private lemma psiKer_self {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (s : ℕ) :
    psiKer b a s s = 1 := by
  simp [psiKer, armaPsi_zero]

private lemma psiKer_eq_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) {m s : ℕ}
    (h : m < s) : psiKer b a m s = 0 := by
  simp [psiKer, Nat.not_le.2 h]

/-- Each kernel product is summable in `m` (geometric ψ-decay). -/
private lemma summable_psiKer_mul {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    (hb : NoRootClosedDisc b) (s t : ℕ) :
    Summable fun m : ℕ => psiKer b a m s * psiKer b a m t := by
  obtain ⟨C, hC, r₀, hr₀, hr₁, hbnd₀⟩ := exists_geometric_bound_armaPsi a hb
  -- enlarge the ratio so that it is strictly positive (needed to divide by `r^s`)
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = max r₀ (1 / 2) := ⟨_, rfl⟩
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) (hrdef ▸ le_max_right r₀ (1 / 2))
  have hrlt : r < 1 := hrdef ▸ max_lt hr₁ (by norm_num)
  have hbnd : ∀ n, |armaPsi b a n| ≤ C * r ^ n := fun n =>
    (hbnd₀ n).trans (by
      have h : r₀ ^ n ≤ r ^ n := pow_le_pow_left₀ hr₀ (hrdef ▸ le_max_left r₀ (1 / 2)) n
      nlinarith)
  have hCr : ∀ u : ℕ, 0 ≤ C / r ^ u := fun u => div_nonneg hC (by positivity)
  have hker : ∀ m u : ℕ, |psiKer b a m u| ≤ C / r ^ u * r ^ m := by
    intro m u
    unfold psiKer
    split_ifs with h
    · have hsplit : r ^ m = r ^ (m - u) * r ^ u := by rw [← pow_add]; congr 1; omega
      calc |armaPsi b a (m - u)| ≤ C * r ^ (m - u) := hbnd _
        _ = C / r ^ u * (r ^ (m - u) * r ^ u) := by field_simp
        _ = C / r ^ u * r ^ m := by rw [← hsplit]
    · rw [abs_zero]
      exact mul_nonneg (hCr u) (by positivity)
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_)
    ((summable_geometric_of_lt_one (sq_nonneg r) (by nlinarith)).mul_left
      (C / r ^ s * (C / r ^ t))))
  rw [abs_mul]
  calc |psiKer b a m s| * |psiKer b a m t|
      ≤ (C / r ^ s * r ^ m) * (C / r ^ t * r ^ m) :=
        mul_le_mul (hker m s) (hker m t) (abs_nonneg _) (mul_nonneg (hCr s) (by positivity))
    _ = C / r ^ s * (C / r ^ t) * (r ^ 2) ^ m := by rw [← pow_mul]; ring

/-- **The Cholesky-type factorization of the model ACVF**: `γ(s − t) = Σ_m ψ̃(m,s) ψ̃(m,t)`.
(Reindexing `Σ_j ψ_j ψ_{j+|s−t|}` by the absolute time `m = j + max(s,t)`.) -/
private lemma armaACVF_eq_tsum_psiKer {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    (hb : NoRootClosedDisc b) (s t : ℕ) :
    armaACVF b a ((s : ℤ) - (t : ℤ)) = ∑' m : ℕ, psiKer b a m s * psiKer b a m t := by
  have main : ∀ u v : ℕ, v ≤ u →
      armaACVF b a ((u : ℤ) - (v : ℤ)) = ∑' m : ℕ, psiKer b a m u * psiKer b a m v := by
    intro u v hvu
    have hs := summable_psiKer_mul a hb u v
    have hzero : ∑ i ∈ Finset.range u, psiKer b a i u * psiKer b a i v = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [psiKer_eq_zero b a (Finset.mem_range.1 hi), zero_mul]
    have hsplit := hs.sum_add_tsum_nat_add u
    rw [hzero, zero_add] at hsplit
    rw [← hsplit, armaACVF, show ((u : ℤ) - (v : ℤ)).natAbs = u - v by omega]
    refine tsum_congr fun j => ?_
    have h1 : psiKer b a (j + u) u = armaPsi b a j := by simp [psiKer]
    have h2 : psiKer b a (j + u) v = armaPsi b a (j + (u - v)) := by
      rw [psiKer, if_pos (by omega)]
      congr 1
      omega
    rw [h1, h2]
  rcases le_total t s with h | h
  · exact main s t h
  · have hsymm : armaACVF b a ((s : ℤ) - (t : ℤ)) = armaACVF b a ((t : ℤ) - (s : ℤ)) := by
      simp only [armaACVF, show ((s : ℤ) - (t : ℤ)).natAbs = ((t : ℤ) - (s : ℤ)).natAbs by omega]
    rw [hsymm, main t s h]
    exact tsum_congr fun m => mul_comm _ _

end Toeplitz

/-- **Positive-definiteness of the model Toeplitz matrices** on the constraint set:
the spectral density of the model is bounded below by a positive constant on the
circle (`|a|²/|b|²` continuous and root-free), so every `Γ_T(b, a)` is positive
definite; in particular invertible. (FY uses this silently in (3.9)–(3.13).) -/
theorem armaToeplitz_posDef {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) (T : ℕ) :
    (armaToeplitz b a T).PosDef := by
  classical
  have hb := hB.1
  have hsum : ∀ s t : ℕ, Summable fun m : ℕ => psiKer b a m s * psiKer b a m t :=
    fun s t => summable_psiKer_mul a hb s t
  have hentry : ∀ i j : Fin T, armaToeplitz b a T i j
      = ∑' m : ℕ, psiKer b a m (i : ℕ) * psiKer b a m (j : ℕ) := fun i j =>
    armaACVF_eq_tsum_psiKer a hb (i : ℕ) (j : ℕ)
  -- expanding the square of the filtered vector `(ψ̃ᵀ c)_m`
  have hexp : ∀ (c : Fin T → ℝ) (m : ℕ), (∑ s : Fin T, c s * psiKer b a m (s : ℕ)) ^ 2
      = ∑ s : Fin T, ∑ t : Fin T, c s * c t * (psiKer b a m s * psiKer b a m t) := by
    intro c m
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
  have hsumsq : ∀ c : Fin T → ℝ,
      Summable fun m : ℕ => (∑ s : Fin T, c s * psiKer b a m (s : ℕ)) ^ 2 := by
    intro c
    simp_rw [hexp c]
    exact summable_sum fun s _ => summable_sum fun t _ => (hsum s t).mul_left _
  -- **the quadratic form is the `ℓ²` norm of the filtered vector**
  have hquad : ∀ c : Fin T → ℝ, c ⬝ᵥ (armaToeplitz b a T *ᵥ c)
      = ∑' m : ℕ, (∑ s : Fin T, c s * psiKer b a m (s : ℕ)) ^ 2 := by
    intro c
    have hrow : ∀ s : Fin T,
        ∑' m : ℕ, ∑ t : Fin T, c s * c t * (psiKer b a m s * psiKer b a m t)
          = ∑ t : Fin T, c s * c t * armaToeplitz b a T s t := by
      intro s
      rw [Summable.tsum_finsetSum
        (f := fun (t : Fin T) (m : ℕ) => c s * c t * (psiKer b a m s * psiKer b a m t))
        (s := (Finset.univ : Finset (Fin T))) (fun t _ => (hsum s t).mul_left _)]
      exact Finset.sum_congr rfl fun t _ => by rw [tsum_mul_left, ← hentry s t]
    have hswap : ∑' m : ℕ, (∑ s : Fin T, c s * psiKer b a m (s : ℕ)) ^ 2
        = ∑ s : Fin T, ∑' m : ℕ, ∑ t : Fin T,
            c s * c t * (psiKer b a m s * psiKer b a m t) := by
      simp_rw [hexp c]
      exact Summable.tsum_finsetSum fun s _ => summable_sum fun t _ => (hsum s t).mul_left _
    rw [hswap]
    simp_rw [hrow]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- symmetry: `γ` depends on `|i − j|` only
    have hnat : ∀ i j : Fin T, ((j : ℤ) - (i : ℤ)).natAbs = ((i : ℤ) - (j : ℤ)).natAbs := by
      intro i j; omega
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, armaToeplitz, Matrix.of_apply,
      armaACVF, hnat i j]
  · intro c hc
    have hstar : star c = c := by funext i; simp
    rw [hstar, hquad c]
    -- the least index carrying a nonzero coefficient
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin T, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin T), S = Finset.univ.filter fun i => c i ≠ 0 :=
      ⟨_, rfl⟩
    have hmemS : ∀ i : Fin T, i ∈ S ↔ c i ≠ 0 := by intro i; rw [hSdef]; simp
    obtain ⟨s₀, hs₀S, hs₀min⟩ := S.exists_min_image (fun i => (i : ℕ)) ⟨i₀, (hmemS i₀).2 hi₀⟩
    have hc₀ : c s₀ ≠ 0 := (hmemS s₀).1 hs₀S
    -- at the absolute time `m = s₀` the filtered vector is exactly `c s₀`: the kernel is
    -- lower triangular with unit diagonal, and every earlier coefficient vanishes
    have hval : ∑ s : Fin T, c s * psiKer b a (s₀ : ℕ) (s : ℕ) = c s₀ := by
      rw [Finset.sum_eq_single s₀]
      · rw [psiKer_self, mul_one]
      · intro s _ hne
        rcases lt_or_gt_of_ne (fun h : (s : ℕ) = (s₀ : ℕ) => hne (Fin.ext h)) with h | h
        · have hcs : c s = 0 := by
            by_contra hcs
            exact absurd (hs₀min s ((hmemS s).2 hcs)) (by omega)
          rw [hcs, zero_mul]
        · rw [psiKer_eq_zero b a h, mul_zero]
      · exact fun h => absurd (Finset.mem_univ s₀) h
    have hposterm : 0 < (∑ s : Fin T, c s * psiKer b a (s₀ : ℕ) (s : ℕ)) ^ 2 := by
      rw [hval]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hc₀))
    exact lt_of_lt_of_le hposterm ((hsumsq c).le_tsum (s₀ : ℕ) fun j _ => sq_nonneg _)

end StatLean.TimeSeries
