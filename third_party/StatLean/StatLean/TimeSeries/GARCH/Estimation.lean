module
public import StatLean.TimeSeries.GARCH.GARCHBasic
public import StatLean.TimeSeries.Spectral.Periodogram
public import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Data.Real.StarOrdered

@[expose] public section

/-!
# GARCH estimation: QMLE, general-density MLE, Whittle, LAD (FY §4.2.3)

Definitions only, plus the two cited asymptotic statements as literature debts:

* **eq. (4.35)/(4.36)**: the ARCH(∞) expansion of the GARCH volatility and its
  **truncated** version `σ̃_t²(θ)` (started from a fixed presample constant), the object
  every practical criterion uses *(the printed `𝐛 = (b₁ … b_p)²` in (4.36) is a typo for
  the coefficient vector — we take the intended reading)*;
* **eq. (4.37)**: the Gaussian quasi-likelihood criterion
  `l_ν(θ) = Σ_{t=ν}^{T}(log σ̃_t² + X_t²/σ̃_t²)`, minimized to give the QMLE;
* **eq. (4.38)**: the general-density criterion `Σ_t (log σ̃_t − log f(X_t/σ̃_t))`, with
  the standardized-`t` and generalized-Gaussian densities recorded as instances;
* **eqs. (4.39)–(4.40)**: AIC/BIC for GARCH order selection;
* **eq. (4.41)**: the Whittle criterion on the squared process, built from the
  periodogram of `Y_t = X_t²` against the model spectral density — its asymptotics are
  a DEBT (Giraitis & Robinson 2001);
* **eq. (4.42)**: the LAD criterion in the median-1 reparametrization — `√T`-normality
  is a DEBT (Peng & Yao 2002).

**Scope.** §4.2.4 (Hall–Yao Theorems 4.5/4.6) and §4.2.5 (bootstrap CIs) were
**descoped on 2026-08-04** at the user's direction, together with the stable-law /
domain-of-attraction scaffolding that existed only to state them. The QMLE definitions
stay because §4.2.6's tests consume them.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.3,
eqs. (4.35)–(4.42) (pp. 156–161). (`FY §4.2.3`.)

**Bibliographic comments.** Gaussian QMLE for GARCH is Bollerslev & Wooldridge (1992);
the Whittle estimator for squared GARCH is Giraitis & Robinson, *Whittle estimation of
ARCH models* (Econometric Theory 17 (2001), 608–631); the LAD estimator is Peng & Yao,
*Least absolute deviations estimation for ARCH and GARCH models* (Biometrika 90 (2003),
967–975).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology Real ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY eq. (4.36)**: the **truncated conditional variance** of a GARCH(p, q) at
parameter `(c₀, b, a)`, computed from the data by running the volatility recursion
forward from a presample constant `v₀ ≥ 0` (the recursion is over the ARCH(∞) form, so
only past data enter). -/
noncomputable def garchTruncVol {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) : ℕ → ℝ
  | 0 => v0
  | (n + 1) =>
      c0 + (∑ i : Fin p, b i * (if h : n - (i : ℕ) < T then x ⟨n - (i : ℕ), h⟩ else 0) ^ 2)
        + ∑ j : Fin q, a j * garchTruncVol c0 b a v0 x (n - (j : ℕ))
  decreasing_by all_goals omega

/-- **FY eq. (4.37)**: the Gaussian **quasi-likelihood criterion**
`l_ν(θ) = Σ_{t=ν}^{T−1} (log σ̃_t² + X_t²/σ̃_t²)`; the QMLE minimizes it over the
admissible parameter set. -/
noncomputable def garchQuasiLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    (Real.log (garchTruncVol c0 b a v0 x t)
      + (if h : t < T then x ⟨t, h⟩ else 0) ^ 2 / garchTruncVol c0 b a v0 x t)

/-- **FY eq. (4.38)**: the **general-density criterion**
`Σ_t (log σ̃_t − log f(X_t/σ̃_t))` for a known standardized innovation density `f`. -/
noncomputable def garchDensityLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) (f : ℝ → ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    (Real.log (Real.sqrt (garchTruncVol c0 b a v0 x t))
      - Real.log (f ((if h : t < T then x ⟨t, h⟩ else 0)
          / Real.sqrt (garchTruncVol c0 b a v0 x t))))

/-- **FY eq. (4.39)**: AIC for GARCH order selection (`2(p + q + 1)` parameters). -/
noncomputable def garchAIC {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  garchQuasiLik c0 b a v0 x ν + 2 * ((p : ℝ) + (q : ℝ) + 1)

/-- **FY eq. (4.40)**: BIC for GARCH order selection. -/
noncomputable def garchBIC {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  garchQuasiLik c0 b a v0 x ν + ((p : ℝ) + (q : ℝ) + 1) * Real.log T

/-- **FY eq. (4.41)**: the **Whittle criterion** for the squared process — the
periodogram of `Y_t = X_t²` integrated against the reciprocal model spectral density,
in the discrete Fourier-frequency form. `gmodel` is the model spectral density of the
squared process at the candidate parameter. -/
noncomputable def garchWhittle {T : ℕ} (x : Fin T → ℝ) (gmodel : ℝ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 T,
    (Real.log (gmodel (fourierFreq T k))
      + periodogram (fun t => x t ^ 2) k / gmodel (fourierFreq T k))

/-- **FY eq. (4.42)**: the **LAD criterion** in the median-1 reparametrization:
`Σ_t |log X_t² − log σ̃_t²|`, minimized over the admissible set. -/
noncomputable def garchLAD {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    |Real.log ((if h : t < T then x ⟨t, h⟩ else 0) ^ 2)
      - Real.log (garchTruncVol c0 b a v0 x t)|

/-- The truncated conditional variance is nonnegative under nonnegative parameters and
presample value — the sanity fact every criterion needs for its logarithms. -/
theorem garchTruncVol_nonneg {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    {v0 : ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hv0 : 0 ≤ v0)
    {T : ℕ} (x : Fin T → ℝ) (n : ℕ) :
    0 ≤ garchTruncVol c0 b a v0 x n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa [garchTruncVol] using hv0
    | (m + 1) =>
      rw [garchTruncVol]
      have h1 : 0 ≤ ∑ i : Fin p,
          b i * (if h : m - (i : ℕ) < T then x ⟨m - (i : ℕ), h⟩ else 0) ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (sq_nonneg _)
      have h2 : 0 ≤ ∑ j : Fin q, a j * garchTruncVol c0 b a v0 x (m - (j : ℕ)) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (ih _ (by omega))
      linarith

/-! ### A counterexample to the frozen rate in `garchTruncVol_presample_stable`

The recursion (4.36) contracts the presample discrepancy at the rate of the dominant
root `ρ` of `ρ^q = ∑_j a_j ρ^{q-1-j}`, NOT at the rate `A := ∑_j a_j`. For `q = 1` the
two agree (`ρ = a₀`), but for `q ≥ 2` with mass on the higher lags `ρ > A`, and the
frozen conclusion `≤ C · A^n` is then false for every constant `C`. The witness below is
the smallest such instance: `p = 0`, `q = 2`, `c₀ = 0`, `a = (0, 9/10)`, so
`A = 9/10` but the discrepancy only halves its index each step and decays like `A^{n/2}`.
-/

private noncomputable def presampleWitnessB : Fin 0 → ℝ := fun _ => 0

private noncomputable def presampleWitnessA : Fin 2 → ℝ := ![0, 9 / 10]

private noncomputable def presampleWitnessX : Fin 0 → ℝ := fun _ => 0

/-- The witness volatility path started from presample value `w`. -/
private noncomputable def presampleWitnessV (w : ℝ) (n : ℕ) : ℝ :=
  garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA w presampleWitnessX n

private lemma presampleWitnessA_sum : (∑ j, presampleWitnessA j) = (9 / 10 : ℝ) := by
  simp [presampleWitnessA, Fin.sum_univ_two]

private lemma presampleWitnessV_zero (w : ℝ) : presampleWitnessV w 0 = w := by
  simp [presampleWitnessV, garchTruncVol]

/-- Only the lag-2 coefficient is nonzero, so the recursion drops the index by two. -/
private lemma presampleWitnessV_succ (w : ℝ) (n : ℕ) :
    presampleWitnessV w (n + 1) = (9 / 10) * presampleWitnessV w (n - 1) := by
  rw [presampleWitnessV, garchTruncVol]
  simp [presampleWitnessV, presampleWitnessB, presampleWitnessA, Fin.sum_univ_two]

private lemma presampleWitnessV_even (w : ℝ) (k : ℕ) :
    presampleWitnessV w (2 * k) = (9 / 10 : ℝ) ^ k * w := by
  induction k with
  | zero => simpa using presampleWitnessV_zero w
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, presampleWitnessV_succ,
      show 2 * k + 1 - 1 = 2 * k by omega, ih]
    ring

/-- **The conclusion of `garchTruncVol_presample_stable` is FALSE as frozen.** All of its
hypotheses hold for the witness (`c₀ = 0 ≥ 0`, `b` vacuous, `a = (0, 9/10) ≥ 0`,
`∑ a_j = 9/10 < 1`, `v₀ = 1 ≥ 0`, `v₁ = 0 ≥ 0`), yet the discrepancy at even times is
`(9/10)^k` while the claimed bound at time `2k` is `C · (9/10)^{2k}`; no constant absorbs
the missing factor `(10/9)^k`. -/
private theorem presample_stable_rate_false :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA 1 presampleWitnessX n
          - garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA 0 presampleWitnessX n|
        ≤ C * (∑ j, presampleWitnessA j) ^ n := by
  rintro ⟨C, -, hC⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 10 / 9)
  have h := hC (2 * k)
  rw [presampleWitnessA_sum] at h
  have e1 : garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA 1 presampleWitnessX
      (2 * k) = (9 / 10 : ℝ) ^ k := by
    simpa [presampleWitnessV] using presampleWitnessV_even 1 k
  have e2 : garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA 0 presampleWitnessX
      (2 * k) = 0 := by
    simpa [presampleWitnessV] using presampleWitnessV_even 0 k
  have hpos : (0 : ℝ) < (9 / 10 : ℝ) ^ k := by positivity
  rw [e1, e2, sub_zero, abs_of_pos hpos, two_mul, pow_add] at h
  have h1 : (1 : ℝ) * ((9 / 10 : ℝ) ^ k) ≤ (C * (9 / 10 : ℝ) ^ k) * ((9 / 10 : ℝ) ^ k) := by
    rw [one_mul, mul_assoc]; exact h
  have h2 : (1 : ℝ) ≤ C * (9 / 10 : ℝ) ^ k := le_of_mul_le_mul_right h1 hpos
  have h3 : C * (9 / 10 : ℝ) ^ k < ((10 : ℝ) / 9) ^ k * (9 / 10 : ℝ) ^ k :=
    mul_lt_mul_of_pos_right hk hpos
  rw [show ((10 : ℝ) / 9) ^ k * (9 / 10 : ℝ) ^ k = 1 by rw [← mul_pow]; norm_num] at h3
  linarith

/-! ### The repaired rate

The discrepancy `D n := |σ̃²_n(v₀) − σ̃²_n(v₁)|` obeys `D 0 = |v₀ − v₁|` (the `c₀` and data
terms are common to both runs and cancel) and `D (n+1) ≤ Σⱼ aⱼ · D (n − j)`. Since each
lag index `n − j` with `j < q` is at least `n + 1 − q`, one factor `A := Σⱼ aⱼ` is gained
every `q` steps: `D n ≤ |v₀ − v₁| · A ^ ⌊n/q⌋`. Choosing any `ρ ∈ (0, 1)` with `A ≤ ρ^q`
— e.g. `ρ = max (A ^ (1/q)) (1/2)`, the `max` only to keep `ρ > 0` when `A = 0` — turns
that into the geometric bound `D n ≤ (|v₀ − v₁| / ρ^{q−1}) · ρ^n`. No characteristic-root
analysis is needed: `ρ` is *some* admissible rate, not the dominant root. -/

/-- One factor `A = Σⱼ aⱼ` is gained every `q` steps of the recursion (4.36). -/
private lemma garchTruncVol_diff_le {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (ha : ∀ j, 0 ≤ a j) (ha1 : (∑ j, a j) ≤ 1) {v0 v1 : ℝ} {T : ℕ} (x : Fin T → ℝ) (n : ℕ) :
    |garchTruncVol c0 b a v0 x n - garchTruncVol c0 b a v1 x n|
      ≤ |v0 - v1| * (∑ j, a j) ^ (n / q) := by
  have hA0 : (0 : ℝ) ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [garchTruncVol]
    | (m + 1) =>
      rw [garchTruncVol, garchTruncVol]
      -- the constant and the data terms are common to both runs
      have hcancel : ∀ u v : ℝ,
          (c0 + (∑ i : Fin p, b i * (if h : m - (i : ℕ) < T then x ⟨m - (i : ℕ), h⟩ else 0) ^ 2)
              + u)
            - (c0 + (∑ i : Fin p,
                b i * (if h : m - (i : ℕ) < T then x ⟨m - (i : ℕ), h⟩ else 0) ^ 2) + v)
            = u - v := by intro u v; ring
      rw [hcancel, ← Finset.sum_sub_distrib]
      -- every lag index `m − j` (`j < q`) has quotient at least `e`
      set e : ℕ := (m + 1 - q) / q with he
      have hstep : ∀ j : Fin q,
          |a j * garchTruncVol c0 b a v0 x (m - (j : ℕ))
              - a j * garchTruncVol c0 b a v1 x (m - (j : ℕ))|
            ≤ a j * (|v0 - v1| * (∑ j, a j) ^ e) := by
        intro j
        rw [← mul_sub, abs_mul, abs_of_nonneg (ha j)]
        refine mul_le_mul_of_nonneg_left ?_ (ha j)
        refine (ih _ (by omega)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine pow_le_pow_of_le_one hA0 ha1 ?_
        have hj := j.isLt
        exact Nat.div_le_div_right (by omega)
      calc |∑ j : Fin q, (a j * garchTruncVol c0 b a v0 x (m - (j : ℕ))
                - a j * garchTruncVol c0 b a v1 x (m - (j : ℕ)))|
          ≤ ∑ j : Fin q, |a j * garchTruncVol c0 b a v0 x (m - (j : ℕ))
              - a j * garchTruncVol c0 b a v1 x (m - (j : ℕ))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin q, a j * (|v0 - v1| * (∑ j, a j) ^ e) :=
            Finset.sum_le_sum fun j _ => hstep j
        _ = |v0 - v1| * (∑ j, a j) ^ (e + 1) := by
            rw [← Finset.sum_mul, pow_succ]; ring
        _ ≤ |v0 - v1| * (∑ j, a j) ^ ((m + 1) / q) := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hA0 ha1 ?_) (abs_nonneg _)
            rcases Nat.eq_zero_or_pos q with hq | hq
            · subst hq; simp
            · rcases lt_or_ge (m + 1) q with h | h
              · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
              · rw [he]
                have : (m + 1 - q) / q + 1 = (m + 1) / q := by
                  rw [← Nat.add_div_right _ hq]
                  congr 1
                  omega
                omega

/-- **The truncation is asymptotically negligible** (the fact that makes (4.36) usable):
under `Σ a_j < 1` the effect of the presample value decays geometrically, so two
presample choices give criteria differing by `O(ρ^ν)` for **some** rate `ρ < 1`.

**Rate repaired 2026-08-09.** The statement previously claimed the rate `Σ a_j`; that is
false for `q ≥ 2` with mass on the higher lags, since the recursion contracts at the
dominant root `ρ` of `ρ^q = Σ_j a_j ρ^{q−1−j}`, which exceeds `Σ a_j`. The witness
`a = (0, 9/10)` is formalized just above (`presample_stable_rate_false`). Only the
existence of *a* geometric rate is used downstream, so the rate is now existentially
quantified. -/
theorem garchTruncVol_presample_stable {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j)
    (hsum : (∑ j, a j) < 1) {v0 v1 : ℝ} (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1)
    {T : ℕ} (x : Fin T → ℝ) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n : ℕ,
      |garchTruncVol c0 b a v0 x n - garchTruncVol c0 b a v1 x n| ≤ C * ρ ^ n := by
  have hA0 : (0 : ℝ) ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  rcases Nat.eq_zero_or_pos q with hq | hq
  · -- with no lag terms the discrepancy is annihilated after a single step
    subst hq
    refine ⟨|v0 - v1|, 0, abs_nonneg _, le_rfl, by norm_num, ?_⟩
    intro n
    match n with
    | 0 => simp [garchTruncVol]
    | (m + 1) => rw [garchTruncVol, garchTruncVol]; simp
  · have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    set A : ℝ := ∑ j, a j with hAdef
    -- any `ρ < 1` with `A ≤ ρ^q` will do; the `max` only keeps `ρ > 0` when `A = 0`
    set ρ : ℝ := max (A ^ ((q : ℝ)⁻¹)) (1 / 2) with hρdef
    have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hρ1 : ρ < 1 := max_lt (Real.rpow_lt_one hA0 hsum (inv_pos.2 hqR)) (by norm_num)
    have hAρ : A ≤ ρ ^ q := by
      have h1 : (A ^ ((q : ℝ)⁻¹)) ^ q = A := by
        rw [← Real.rpow_natCast (A ^ ((q : ℝ)⁻¹)) q, ← Real.rpow_mul hA0,
          inv_mul_cancel₀ hqR.ne', Real.rpow_one]
      calc A = (A ^ ((q : ℝ)⁻¹)) ^ q := h1.symm
        _ ≤ ρ ^ q := pow_le_pow_left₀ (Real.rpow_nonneg hA0 _) (le_max_left _ _) q
    refine ⟨|v0 - v1| / ρ ^ (q - 1), ρ, by positivity, hρ0.le, hρ1, fun n => ?_⟩
    refine (garchTruncVol_diff_le ha hsum.le x n).trans ?_
    calc |v0 - v1| * A ^ (n / q)
        ≤ |v0 - v1| * (ρ ^ q) ^ (n / q) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hAρ _) (abs_nonneg _)
      _ = |v0 - v1| * ρ ^ (q * (n / q)) := by rw [← pow_mul]
      _ ≤ |v0 - v1| * ρ ^ (n - (q - 1)) := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1.le ?_) (abs_nonneg _)
          have h1 : q * (n / q) + n % q = n := Nat.div_add_mod n q
          have h2 : n % q < q := Nat.mod_lt _ hq
          omega
      _ ≤ |v0 - v1| / ρ ^ (q - 1) * ρ ^ n := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hρ0 (q - 1)), mul_assoc, ← pow_add]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)) (abs_nonneg _)

/-! ### The frozen `whittle_clt_debt` / `lad_clt_debt` statements are FALSE — a witness

Both statements were frozen at a granularity that leaves **three** of their objects
completely unlinked to the model, which is one more than the defect list of wave `ts/s12`
for `Threshold/Estimation`'s eq. (4.8) debt (that debt has since been removed; its witness
`tarLS_clt_debt_false` is kept there):

1. **`W` is a free parameter.** The docstrings call it "the limiting covariance matrix of
   the Whittle (LAD) estimator", but formally it ranges over *all* positive-definite
   matrices with no tie to `(c₀, b, a, X, μ)`. `W` and `2W` are both admissible and force
   two different Gaussian limits for one and the same sequence.
2. **`θhat` has no defining property.** It is any measurable array of parameter vectors.
   Neither `garchWhittle` (eq. (4.41)) nor `garchLAD` (eq. (4.42)) — both *defined in this
   very file* — appears anywhere in either statement, so nothing says `θhat` is the
   estimator the theorem is about.
3. **`θ0` is a free parameter too.** It is an arbitrary vector, not the true parameter of
   the `IsGARCH` instance in the hypotheses. Even a perfect estimator would not be
   centred at it.

Any one of the three is fatal, and the cheapest satisfiable instance exhibits all three at
once: take the **degenerate GARCH** `p = q = 0`, `c₀ = 0`, so `σ_t ≡ 0` and `X ≡ 0`, and
take `θhat ≡ θ0 ≡ 0`. The scaled statistic is then identically `0`, its characteristic
function is the constant `1`, while the frozen limit at `W = 1`, `c = 1`, `u = 1` is
`exp(−1/2)`.

The instance is built from scratch on `(ℤ → ℝ, ⊗ Rademacher)`, so the witness is
**axiom-clean** and independent of `exists_stationary_garch`. The **Rademacher** noise
(rather than the Gaussian of `Threshold/Estimation.lean`) is forced by `lad_clt_debt`'s
median hypothesis `hmed`: it asks the median of `ε₀²` to be `1`, which for a mean-zero
unit-variance law means `ε₀² = 1` a.s. up to the two-sided tail balance — the two-point
law is the simple solution, whereas a standard Gaussian has `P(ε₀² ≤ 1) ≈ 0.683 ≠ 0.317`.
`X ≡ 0` makes strict stationarity and `L⁴` free, and makes `σ(X_s : s < t)` the trivial
σ-algebra, so `indep_past` is `indep_bot_right`; no shift-invariance of the noise law is
needed anywhere. -/

/-- The **Rademacher law** `(δ₋₁ + δ₁)/2`: mean `0`, variance `1`, and `x² = 1` a.s., the
last being what `lad_clt_debt`'s median hypothesis needs. -/
private noncomputable def radLaw : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (-1) + Measure.dirac 1)

private lemma radLaw_apply (s : Set ℝ) :
    radLaw s = (2 : ℝ≥0∞)⁻¹ * (s.indicator 1 (-1) + s.indicator 1 1) := by
  simp [radLaw, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply, mul_add]

private lemma radLaw_eq_one {s : Set ℝ} (h1 : (-1 : ℝ) ∈ s) (h2 : (1 : ℝ) ∈ s) :
    radLaw s = 1 := by
  rw [radLaw_apply, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  simp only [Pi.one_apply]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private lemma radLaw_eq_zero {s : Set ℝ} (h1 : (-1 : ℝ) ∉ s) (h2 : (1 : ℝ) ∉ s) :
    radLaw s = 0 := by
  rw [radLaw_apply, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  simp

private instance : IsProbabilityMeasure radLaw :=
  ⟨radLaw_eq_one (Set.mem_univ _) (Set.mem_univ _)⟩

private lemma radLaw_ae {p : ℝ → Prop} (h1 : p (-1)) (h2 : p 1) : ∀ᵐ x ∂radLaw, p x := by
  rw [Filter.eventually_iff, mem_ae_iff]
  exact radLaw_eq_zero (by simpa using h1) (by simpa using h2)

private lemma integral_radLaw (f : ℝ → ℝ) :
    ∫ x, f x ∂radLaw = (f (-1) + f 1) / 2 := by
  have hi1 : Integrable f (Measure.dirac (-1 : ℝ)) := integrable_dirac (by finiteness)
  have hi2 : Integrable f (Measure.dirac (1 : ℝ)) := integrable_dirac (by finiteness)
  rw [radLaw, integral_smul_measure, integral_add_measure hi1 hi2, integral_dirac,
    integral_dirac]
  rw [show ((2 : ℝ≥0∞)⁻¹).toReal = 1 / 2 by
    rw [ENNReal.toReal_inv]; norm_num]
  simp only [smul_eq_mul]
  ring

/-! #### The i.i.d. Rademacher noise on `ℤ` -/

private noncomputable def radMeasure : Measure (ℤ → ℝ) :=
  Measure.infinitePi fun _ : ℤ => radLaw

private instance : IsProbabilityMeasure radMeasure := by
  unfold radMeasure; infer_instance

private def radCoord (t : ℤ) (ω : ℤ → ℝ) : ℝ := ω t

private lemma radCoord_measurable (t : ℤ) : Measurable (radCoord t) := measurable_pi_apply t

private lemma radMeasure_map_coord (t : ℤ) : radMeasure.map (radCoord t) = radLaw :=
  Measure.infinitePi_map_eval _ t

private lemma radCoord_identDistrib (t : ℤ) :
    IdentDistrib (radCoord t) (id : ℝ → ℝ) radMeasure radLaw :=
  ⟨(radCoord_measurable t).aemeasurable, aemeasurable_id, by
    rw [Measure.map_id, radMeasure_map_coord t]⟩

private lemma memLp_id_radLaw : MemLp (id : ℝ → ℝ) 2 radLaw := by
  refine MemLp.of_bound aemeasurable_id.aestronglyMeasurable 1 ?_
  exact radLaw_ae (by norm_num) (by norm_num)

private lemma rad_isIIDNoise : IsIIDNoise radCoord 1 radMeasure := by
  refine ⟨radCoord_measurable, ?_, ?_, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ : ℤ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  · exact fun s t => (radCoord_identDistrib s).trans (radCoord_identDistrib t).symm
  · exact (radCoord_identDistrib 0).memLp_iff.2 memLp_id_radLaw
  · rw [(radCoord_identDistrib 0).integral_eq]
    have h := integral_radLaw (fun x : ℝ => x)
    simpa using h
  · rw [(radCoord_identDistrib 0).variance_eq, variance_eq_sub memLp_id_radLaw]
    have h1 : (∫ x, ((id : ℝ → ℝ) ^ 2) x ∂radLaw) = 1 := by
      have h := integral_radLaw (fun x : ℝ => x ^ 2)
      simpa using h
    have h2 : (∫ x, (id : ℝ → ℝ) x ∂radLaw) = 0 := by
      have h := integral_radLaw (fun x : ℝ => x)
      simpa using h
    rw [h1, h2]
    norm_num

/-! #### The degenerate GARCH instance -/

private def zeroProc : ℤ → (ℤ → ℝ) → ℝ := fun _ _ => 0

private lemma sigmaLT_zeroProc (t : ℤ) : sigmaLT zeroProc t = ⊥ := by
  refine le_antisymm (iSup₂_le fun s _ => ?_) bot_le
  exact le_of_eq (MeasurableSpace.comap_const (0 : ℝ))

private lemma rad_isGARCH :
    IsGARCH (0 : ℝ) (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : ℝ))
      zeroProc zeroProc radCoord radMeasure := by
  refine ⟨le_rfl, fun i => i.elim0, fun j => j.elim0, fun _ => measurable_const,
    fun _ => measurable_const, fun _ => Filter.Eventually.of_forall fun _ => le_rfl,
    fun _ => measurable_const, rad_isIIDNoise, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [sigmaLT_zeroProc]
    exact ProbabilityTheory.indep_bot_right _
  · filter_upwards with ω
    simp [zeroProc]
  · filter_upwards with ω
    simp [zeroProc]

private lemma zeroProc_strictlyStationary : IsStrictlyStationary zeroProc radMeasure :=
  fun _ _ _ => rfl

private lemma zeroProc_memLp (r : ℝ≥0∞) (t : ℤ) : MemLp (zeroProc t) r radMeasure :=
  memLp_const 0

private lemma rad_hmed :
    radMeasure {ω | radCoord 0 ω ^ 2 ≤ 1} = radMeasure {ω | 1 ≤ radCoord 0 ω ^ 2} := by
  have hset1 : MeasurableSet {x : ℝ | x ^ 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hset2 : MeasurableSet {x : ℝ | 1 ≤ x ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  have e1 : radMeasure {ω | radCoord 0 ω ^ 2 ≤ 1} = radLaw {x : ℝ | x ^ 2 ≤ 1} := by
    rw [← radMeasure_map_coord 0, Measure.map_apply (radCoord_measurable 0) hset1]
    rfl
  have e2 : radMeasure {ω | 1 ≤ radCoord 0 ω ^ 2} = radLaw {x : ℝ | 1 ≤ x ^ 2} := by
    rw [← radMeasure_map_coord 0, Measure.map_apply (radCoord_measurable 0) hset2]
    rfl
  rw [e1, e2, radLaw_eq_one (by norm_num) (by norm_num),
    radLaw_eq_one (by norm_num) (by norm_num)]

/-! #### The refutations -/

/-- The common tail of both refutations: on the degenerate instance the scaled statistic
is identically `0`, whose characteristic function is the constant `1`, while the frozen
limit at `W = 1`, `c = 1`, `u = 1` is `exp(−1/2)`. -/
private lemma dirac_charFun_ne_gaussian
    (key : Tendsto (fun _ : ℕ => charFun (radMeasure.map fun _ : ℤ → ℝ => (0 : ℝ)) (1 : ℝ))
      atTop (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (1 : ℝ))) 1))) :
    False := by
  have hmapconst : radMeasure.map (fun _ : ℤ → ℝ => (0 : ℝ)) = Measure.dirac 0 := by
    rw [Measure.map_const]
    simp
  rw [hmapconst] at key
  have hone : charFun (Measure.dirac (0 : ℝ)) (1 : ℝ) = 1 := by
    rw [charFun_dirac]; simp
  simp only [hone] at key
  have hlim : charFun (gaussianReal 0 (Real.toNNReal 1)) (1 : ℝ) = 1 :=
    (tendsto_nhds_unique tendsto_const_nhds key).symm
  rw [charFun_gaussianReal] at hlim
  norm_num at hlim
  rw [show ((-(1 / 2) : ℂ)) = (((-(1 / 2) : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp] at hlim
  have hR : Real.exp (-(1 / 2)) = 1 := by exact_mod_cast hlim
  have hlt : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- **The frozen `whittle_clt_debt` statement is FALSE.** -/
private theorem whittle_clt_debt_false
    (H : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {c0 : ℝ}
      {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ},
      IsGARCH c0 b a X σvol ε μ → IsStrictlyStationary X μ → (∀ t, MemLp (X t) 4 μ) →
      ∀ (W : Matrix (Fin (p + q + 1)) (Fin (p + q + 1)) ℝ), Matrix.PosDef W →
      ∀ (θhat : (T : ℕ) → Ω → Fin (p + q + 1) → ℝ), (∀ T, Measurable (θhat T)) →
      ∀ (θ0 c : Fin (p + q + 1) → ℝ) (u : ℝ),
      Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
          Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
        atTop
        (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
          (∑ i, ∑ j, c i * c j * W i j))) u))) :
    False := by
  have key := H rad_isGARCH zeroProc_strictlyStationary (zeroProc_memLp 4)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosDef.one (fun _ _ _ => 0)
    (fun _ => measurable_const) (fun _ => 0) (fun _ => 1) 1
  simp only [sub_self, mul_zero, Finset.sum_const_zero] at key
  rw [show (∑ i : Fin 1, ∑ j : Fin 1,
      (1 : ℝ) * 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) i j) = 1 from by simp] at key
  exact dirac_charFun_ne_gaussian key

/-- **The frozen `lad_clt_debt` statement is FALSE.** The median hypothesis is satisfied
outright by the Rademacher noise (`ε₀² = 1` a.s.). -/
private theorem lad_clt_debt_false
    (H : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {c0 : ℝ}
      {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ},
      IsGARCH c0 b a X σvol ε μ → IsStrictlyStationary X μ →
      μ {ω | ε 0 ω ^ 2 ≤ 1} = μ {ω | 1 ≤ ε 0 ω ^ 2} →
      ∀ (W : Matrix (Fin (p + q + 1)) (Fin (p + q + 1)) ℝ), Matrix.PosDef W →
      ∀ (θhat : (T : ℕ) → Ω → Fin (p + q + 1) → ℝ), (∀ T, Measurable (θhat T)) →
      ∀ (θ0 c : Fin (p + q + 1) → ℝ) (u : ℝ),
      Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
          Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
        atTop
        (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
          (∑ i, ∑ j, c i * c j * W i j))) u))) :
    False := by
  have key := H rad_isGARCH zeroProc_strictlyStationary rad_hmed
    (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosDef.one (fun _ _ _ => 0)
    (fun _ => measurable_const) (fun _ => 0) (fun _ => 1) 1
  simp only [sub_self, mul_zero, Finset.sum_const_zero] at key
  rw [show (∑ i : Fin 1, ∑ j : Fin 1,
      (1 : ℝ) * 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) i j) = 1 from by simp] at key
  exact dirac_charFun_ne_gaussian key

/-! ### The repaired asymptotic statements

**Statement strengthening (wave `ts/s13-whittle-lad`, 2026-08-09).** Both frozen forms are
FALSE — see `whittle_clt_debt_false` / `lad_clt_debt_false` above, kept verbatim against
the *frozen* shapes as the permanent record. Four repairs are applied to each, in the house
style of `Threshold/Estimation`'s eq. (4.8) debt (since removed); every added or changed
hypothesis is tagged `USER-INPUT`.

1. **`θ₀` is the true parameter.** `hθ0` pins it to `garchParamVec c₀ b a`, the coordinate
   packing of the `IsGARCH` instance's own `(c₀, b, a)`. Without this even a perfect
   estimator is not centred at `θ₀`.
2. **`θhat` is a genuine minimizer of the criterion the theorem is named after.** The
   frozen statements never mentioned `garchWhittle` (4.41) or `garchLAD` (4.42). The
   repair introduces the unpacked estimator `est` (with `hpack` tying `θhat` to it, as in
   the `(Fin p → ℝ) × (Fin q → ℝ)`-valued `θ` of the removed FY Thm 3.2 headline), a
   compact search region `K`
   with the truth in its interior, and exact minimization over `K` at every sample.
3. **`W` is pinned to the process** — the defect that killed the frozen form outright
   (`W` and `2W` both admissible). Unlike the removed eq. (4.8) debt, whose `W_i` is a
   plain conditional second-moment matrix (`tarRegimeDesignCov`), the Whittle and LAD limiting
   covariances are *sandwiches* that the repo cannot yet write down: Giraitis–Robinson's
   is `A⁻¹BA⁻¹` with `A` an integral of `∂_θ log g(λ; θ)` against Lebesgue measure on
   `[−π, π]` and `B` carrying the **fourth-cumulant (tri-)spectral density** of the
   squared process; Peng–Yao's is `(4f²(0))⁻¹ Ω⁻¹` with `f` the density of `log ε₀²` at its
   median and `Ω = E[∂_θ log σ_t² (∂_θ log σ_t²)ᵀ]`. Both need a **differentiable
   parametrized volatility/spectral density**, which does not exist in the repo (the file
   only has `garchTruncVol` as a function of the data), and GR's `B` additionally needs the
   trispectrum. So `W` is pinned the other way round, through what GR and PY actually
   *prove* on the way to their covariance formula: an **asymptotically linear
   representation** of the estimator with an influence process `ψ`, and `W = E[ψ₀ψ₀ᵀ]`
   (`hWdef`). This is a faithful relocation, not a weakening: the covariance formulas are
   read off `ψ` and nothing else.
4. **The Brown-CLT hypothesis on the influence process** (`hvar`) is carried explicitly.
   It is not decoration: a strictly stationary square-integrable martingale-difference
   sequence that is *not ergodic* has a variance-mixture limit, not a Gaussian one, so
   without `hvar` even the repaired statement would be false. See the residue note.

**Deliberately NOT repaired.** `hL4` (Whittle) and `hmed` (LAD) are left exactly as
frozen: they are the genuine model-side hypotheses of GR 2001 and PY 2003 and neither
participates in any of the four defects. `hW : Matrix.PosDef W` is also kept, now as a
nondegeneracy assumption on `E[ψ₀ψ₀ᵀ]`.

### Residue note: what is left to prove

**Both statements are now PROVED** (wave `ts/f3-spectral-garch-finale`, 2026-08-09):
`whittle_clt_debt` and `lad_clt_debt` are `sorry`-free and axiom-clean. The two steps
(S1)/(S2) described below were executed verbatim, and they are literally the *same* proof
in the two cases — the engine `clt_of_asymptotically_linear` below is applied twice, with
no Whittle- or LAD-specific input. Nothing in the two proofs uses `hL4`, `hmed`, `hstat`,
`hc0`, `hθ0`, `hmin`/`gmodel`/`v0`/`ν` or `hW` beyond what is recorded here: the model-side
hypotheses are consumed *inside* `hlin`/`hWdef`/`hvar`, which is exactly the relocation
repair 3 performed. `hmin` and `hK` are used only for the boundedness of `θhat`
(`exists_bound_garchParamVec`), the integrability side condition of (S1), and `hW` only
through `hWdef` (positive semidefiniteness of `E[ψ₀ψ₀ᵀ]` is *derived*, not assumed —
`nonneg_influence_form`; `Matrix.PosDef W` is therefore not needed at all).

With the repairs in place both theorems have the *same* two-step proof, and the two steps
are cleanly separated.

**(S1) `L¹`-Slutsky at the characteristic-function level — routine.** `hlin` says the
`i`-th coordinate of `√T(θ̂_T − θ₀)` differs from `T^{−1/2} Σ_{t<T} ψ_i(t+1)` by something
that vanishes in `L¹`. Summing against `c` gives
`∫ |Z_T − V_T| ≤ Σ_i |c_i| · (the i-th `hlin` sequence) → 0`, and
`‖E e^{iuZ} − E e^{iuW}‖ ≤ |u| E|Z − W|` (`Process/SampleACF.lean`'s
`norm_charFun_map_sub_le`, `private` there) transports the limit. **This step is now
CLOSED**, as the reusable brick `tendsto_charFun_map_of_l1` just below, together with the
`norm_charFun_map_sub_le` it needs. What remains of (S1) is the two-line integrability
side condition, which is *derivable* rather than assumed: `hK` compact makes `est` — hence
`θhat` — uniformly bounded, so `Z_T` is bounded and measurable, and `V_T` is a finite
linear combination of `L²` variables.

**(S2) The martingale CLT for `V_T` — `mds_clt_sequence`, three of four inputs free.**
Instantiate `ForMathlib/Probability/MartingaleCLT/BrownCLT.lean`'s `mds_clt_sequence` at
`ξ t := Σ_i c_i ψ_i(t+1)` and `G t := sigmaLT X ((t : ℤ) + 1)`:
* `hle`/`hmono` — `IsGARCH.measurableX` and `sigmaLT` monotonicity;
* `hadapted` — `hpsiAdapted`; `hmds` — `hpsiMDS`, both linear in `c`;
* `hL2` — `hpsiL2`, finite linear combination;
* `hσ : 0 ≤ σ²` — **not** `hW.posSemidef`, in the end: this Mathlib's `Matrix.PosSemidef`
  is phrased over `n →₀ R`, so matching `∑ i, ∑ j, c i * c j * W i j` to it is more work
  than proving it directly. `nonneg_influence_form` instead expands the form back into
  `∫ (Σ_i c_i ψ_i(0))² ≥ 0` through `hWdef`. Consequently `hW : Matrix.PosDef W` is
  **unused** by the proof, and stays only as the nondegeneracy statement of repair 3;
* `hvar` — **hypothesis** (repair 4);
* `hlind` — free from `hpsiId`: every summand equals `∫_{|ξ₀| ≥ ε√n} ξ₀²`, so the average
  *is* that single term, and it vanishes because `ξ₀ ∈ L²` (dominated convergence on the
  tail of a square-integrable variable — the one small analytic lemma missing here;
  everything else in (S2) is instantiation). Both halves are now built:
  `setIntegral_sq_eq_of_identDistrib` (the transfer of the truncated second moment along
  `hpsiId`, composed with the linear form `v ↦ Σ_i c_i v_i`) and
  `tendsto_setIntegral_sq_tail` (the dominated-convergence half).

**The relocated debts** (unchanged by the closure above — they are what `hlin` and `hWdef`
now *carry*, and they remain outside the repo). After the repairs the *literature* content of GR 2001 and PY 2003
is exactly the pair `(hlin, hWdef)`: the expansion of the criterion around `θ₀` producing
the influence process. That is where the genuinely hard analysis lives, and it is
different in the two cases:
* **Whittle (GR 2001).** `hlin` comes from a Taylor expansion of `garchWhittle` in `θ`
  plus a **CLT for a weighted quadratic form of the squared process**,
  `T^{−1/2} Σ_{j,k} w_{j−k} (Y_j − EY)(Y_k − EY)`. The reduction of the periodogram average
  to such a quadratic form is *available*: `Spectral/DFT.lean`'s Parseval layer (batch B,
  proved) does exactly that. The quadratic-form CLT for a non-linear, non-Gaussian,
  long-memory-capable process is the open piece; GR get it from their own
  `Σ_h |Cov(Y_0, Y_h)| < ∞` bookkeeping plus a fourth-cumulant condition — which is why
  `hL4` is there and why `B ≠ A` in their sandwich.
* **LAD (PY 2003).** `hlin` comes from Pollard's convexity argument: `garchLAD` is convex
  in the reparametrized `θ`, its subgradient at `θ₀` is `Σ_t sign(log ε_t²) ∂_θ log σ_t²`,
  a **bounded** martingale difference (the signs are `±1`), so the *score* half is
  immediate — it is `mds_clt_sequence` again, with no moment condition at all, which is
  precisely FY's point that LAD needs no moments. The hard half is the **quadratic
  approximation of the criterion over a shrinking `T^{−1/2}`-neighbourhood** — an
  empirical-process/stochastic-equicontinuity statement — plus the differentiability of
  `θ ↦ log σ̃_t²(θ)` that `garchTruncVol` would have to be shown to have. Convexity
  (Pollard's lemma: pointwise convergence of convex random functions is automatically
  uniform on compacta) is what makes the neighbourhood argument affordable; it is not in
  the repo.

Note the asymmetry: **LAD's score CLT is essentially free here** (bounded MDS), while
Whittle's is a genuine quadratic-form CLT. If only one of the two is to be pushed further,
LAD is much the cheaper. -/

/-! #### Residue (S1), CLOSED: `L¹`-Slutsky at the characteristic-function level -/

private lemma charFun_map_eq_integral' {f : Ω → ℝ} (hf : AEMeasurable f μ) (u : ℝ) :
    charFun (μ.map f) u = ∫ ω, Complex.exp (Complex.I * (u * f ω : ℝ)) ∂μ := by
  rw [charFun_apply_real, integral_map hf (by fun_prop)]
  simp only [Complex.ofReal_mul]
  congr 1 with ω
  ring_nf

private lemma integrable_cexp_mul_I' [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun ω => Complex.exp (Complex.I * (f ω : ℝ))) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (Complex.measurable_exp.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with ω
  simp [Complex.norm_exp]

/-- **The `L¹` charFun comparison**: `‖E e^{iuZ} − E e^{iuW}‖ ≤ |u| E|Z − W|`. (The same
brick as `Process/SampleACF.lean`'s `norm_charFun_map_sub_le`, which is `private` there.) -/
private lemma norm_charFun_map_sub_le [IsProbabilityMeasure μ] {Z W : Ω → ℝ}
    (hZ : Measurable Z) (hW : Measurable W)
    (hint : Integrable (fun ω => |Z ω - W ω|) μ) (u : ℝ) :
    ‖charFun (μ.map Z) u - charFun (μ.map W) u‖ ≤ |u| * ∫ ω, |Z ω - W ω| ∂μ := by
  rw [charFun_map_eq_integral' hZ.aemeasurable u, charFun_map_eq_integral' hW.aemeasurable u,
    ← integral_sub (integrable_cexp_mul_I' (hZ.const_mul u))
      (integrable_cexp_mul_I' (hW.const_mul u))]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [show |u| * ∫ ω, |Z ω - W ω| ∂μ = ∫ ω, |u| * |Z ω - W ω| ∂μ from
    (integral_const_mul _ _).symm]
  refine integral_mono (((integrable_cexp_mul_I' (hZ.const_mul u)).sub
    (integrable_cexp_mul_I' (hW.const_mul u))).norm) (hint.const_mul _) fun ω => ?_
  have hfact : Complex.exp (Complex.I * ((u * Z ω : ℝ)))
        - Complex.exp (Complex.I * ((u * W ω : ℝ)))
      = Complex.exp (Complex.I * ((u * W ω : ℝ))) *
        (Complex.exp (Complex.I * ((u * Z ω - u * W ω : ℝ))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfact, norm_mul,
    show ‖Complex.exp (Complex.I * ((u * W ω : ℝ)))‖ = 1 from by simp [Complex.norm_exp],
    one_mul]
  refine le_trans (by simpa using
      Real.norm_exp_I_mul_ofReal_sub_one_le (x := u * Z ω - u * W ω)) ?_
  rw [show u * Z ω - u * W ω = u * (Z ω - W ω) from by ring, abs_mul]

/-- **Residue (S1) of `whittle_clt_debt`/`lad_clt_debt`, discharged**: a sequence of laws
whose `L¹` distance to a convergent sequence of laws vanishes has the same limiting
characteristic function. This is the step that transports the martingale CLT for the
influence sum `V_T` across the asymptotically linear representation `hlin`. -/
private lemma tendsto_charFun_map_of_l1 [IsProbabilityMeasure μ] {u : ℝ}
    {Z W : ℕ → Ω → ℝ} (hZ : ∀ T, Measurable (Z T)) (hW : ∀ T, Measurable (W T))
    (hint : ∀ T, Integrable (fun ω => |Z T ω - W T ω|) μ)
    (h0 : Tendsto (fun T => ∫ ω, |Z T ω - W T ω| ∂μ) atTop (𝓝 0))
    {L : ℂ} (hlim : Tendsto (fun T => charFun (μ.map (W T)) u) atTop (𝓝 L)) :
    Tendsto (fun T => charFun (μ.map (Z T)) u) atTop (𝓝 L) := by
  have hd : Tendsto (fun T => charFun (μ.map (Z T)) u - charFun (μ.map (W T)) u)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun T => norm_nonneg _)
      (fun T => norm_charFun_map_sub_le (hZ T) (hW T) (hint T) u) ?_
    simpa using h0.const_mul |u|
  simpa using hd.add hlim

/-! #### Residue (S2), CLOSED: the martingale CLT for the influence sum

The bricks below instantiate `mds_clt_sequence` (Brown's martingale CLT) at the influence
process, discharging every input except the two that the repaired statements carry as
hypotheses (`hvar`, the ergodicity brick, and `hlin`, the asymptotically linear
representation).  `clt_of_asymptotically_linear` is the resulting engine: it is the whole
common proof of the Whittle and LAD statements. -/

omit [MeasurableSpace Ω] in
private lemma sigmaLT_mono_est {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s ≤ t) :
    sigmaLT X s ≤ sigmaLT X t :=
  iSup₂_le fun _ hu =>
    le_iSup₂ (f := fun r (_ : r ∈ Set.Iio t) => MeasurableSpace.comap (X r) inferInstance) _
      (lt_of_lt_of_le hu hst)

private lemma sigmaLT_le_est {X : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun _ _ => (hm _).comap_le

/-- The tail second moment of a square-integrable variable vanishes. -/
private lemma tendsto_setIntegral_sq_tail [IsProbabilityMeasure μ] {ζ : Ω → ℝ}
    (hζm : Measurable ζ) (hζ : MemLp ζ 2 μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => ∫ ω in {ω | ε * Real.sqrt m ≤ |ζ ω|}, ζ ω ^ 2 ∂μ) atTop (𝓝 0) := by
  have hint : Integrable (fun ω => ζ ω ^ 2) μ := hζ.integrable_sq
  have hset : ∀ m : ℕ, MeasurableSet {ω | ε * Real.sqrt m ≤ |ζ ω|} :=
    fun m => measurableSet_le measurable_const hζm.abs
  have hrw : ∀ m : ℕ, ∫ ω in {ω | ε * Real.sqrt m ≤ |ζ ω|}, ζ ω ^ 2 ∂μ
      = ∫ ω, Set.indicator {ω | ε * Real.sqrt m ≤ |ζ ω|} (fun ω => ζ ω ^ 2) ω ∂μ :=
    fun m => (integral_indicator (hset m)).symm
  simp only [hrw]
  have hF : ∀ m : ℕ, AEStronglyMeasurable
      (Set.indicator {ω | ε * Real.sqrt m ≤ |ζ ω|} (fun ω => ζ ω ^ 2)) μ := fun m =>
    ((hζm.pow_const 2).indicator (hset m)).aestronglyMeasurable
  have hbd : ∀ m : ℕ, ∀ᵐ ω ∂μ,
      ‖Set.indicator {ω | ε * Real.sqrt m ≤ |ζ ω|} (fun ω => ζ ω ^ 2) ω‖ ≤ ζ ω ^ 2 := by
    intro m
    filter_upwards with ω
    by_cases hω : ω ∈ {ω | ε * Real.sqrt m ≤ |ζ ω|}
    · rw [Set.indicator_of_mem hω]
      simp
    · rw [Set.indicator_of_notMem hω]
      simpa using sq_nonneg (ζ ω)
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun m : ℕ => Set.indicator {ω | ε * Real.sqrt m ≤ |ζ ω|} (fun ω => ζ ω ^ 2) ω)
      atTop (𝓝 0) := by
    filter_upwards with ω
    have hgo : Tendsto (fun m : ℕ => ε * Real.sqrt m) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hε
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hev : ∀ᶠ m : ℕ in atTop,
        Set.indicator {ω | ε * Real.sqrt m ≤ |ζ ω|} (fun ω => ζ ω ^ 2) ω = 0 := by
      filter_upwards [hgo.eventually_gt_atTop (|ζ ω|)] with m hm
      refine Set.indicator_of_notMem ?_ _
      simp only [Set.mem_setOf_eq, not_le]
      exact hm
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  have := tendsto_integral_of_dominated_convergence (F := fun m : ℕ => Set.indicator
      {ω | ε * Real.sqrt m ≤ |ζ ω|} (fun ω => ζ ω ^ 2)) (f := fun _ => (0 : ℝ))
      (fun ω => ζ ω ^ 2) hF hint hbd hlim
  simpa using this

/-- Two identically distributed variables have the same truncated second moment. -/
private lemma setIntegral_sq_eq_of_identDistrib [IsProbabilityMeasure μ] {Z ζ : Ω → ℝ}
    (hZ : Measurable Z) (hζ : Measurable ζ) (h : IdentDistrib Z ζ μ μ) (a : ℝ) :
    ∫ ω in {ω | a ≤ |Z ω|}, Z ω ^ 2 ∂μ = ∫ ω in {ω | a ≤ |ζ ω|}, ζ ω ^ 2 ∂μ := by
  have hg : Measurable (fun x : ℝ => if a ≤ |x| then x ^ 2 else 0) := by
    refine Measurable.ite (measurableSet_le measurable_const measurable_id.abs) ?_ ?_
    · fun_prop
    · fun_prop
  have e1 : ∀ Y : Ω → ℝ, Measurable Y →
      ∫ ω in {ω | a ≤ |Y ω|}, Y ω ^ 2 ∂μ
        = ∫ ω, (fun x : ℝ => if a ≤ |x| then x ^ 2 else 0) (Y ω) ∂μ := by
    intro Y hY
    rw [← integral_indicator (measurableSet_le measurable_const hY.abs)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : a ≤ |Y ω|
    · rw [Set.indicator_of_mem (by exact hω)]
      simp [hω]
    · rw [Set.indicator_of_notMem (by exact hω)]
      simp [hω]
  rw [e1 Z hZ, e1 ζ hζ]
  exact (h.comp hg).integral_eq

/-- The influence covariance quadratic form is nonnegative — it is a second moment. -/
private lemma nonneg_influence_form [IsProbabilityMeasure μ] {n : ℕ}
    {psi : Fin n → ℤ → Ω → ℝ} (hpsiL2 : ∀ i t, MemLp (psi i t) 2 μ)
    {W : Matrix (Fin n) (Fin n) ℝ} (hWdef : ∀ i j, W i j = ∫ ω, psi i 0 ω * psi j 0 ω ∂μ)
    (c : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, c i * c j * W i j := by
  classical
  have hint : ∀ i j : Fin n, Integrable (fun ω => psi i 0 ω * psi j 0 ω) μ := fun i j =>
    (hpsiL2 i 0).integrable_mul (hpsiL2 j 0)
  have hkey : ∑ i, ∑ j, c i * c j * W i j = ∫ ω, (∑ i, c i * psi i 0 ω) ^ 2 ∂μ := by
    have hpt : ∀ ω : Ω, (∑ i, c i * psi i 0 ω) ^ 2
        = ∑ i : Fin n, ∑ j : Fin n, c i * c j * (psi i 0 ω * psi j 0 ω) := by
      intro ω
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finset_sum _ (fun i _ => integrable_finset_sum _
        fun j _ => (hint i j).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => (hint i j).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, hWdef i j]
  rw [hkey]
  exact integral_nonneg fun ω => sq_nonneg _

/-- **The asymptotically-linear CLT engine.** -/
private lemma clt_of_asymptotically_linear [IsProbabilityMeasure μ] {n : ℕ}
    {X : ℤ → Ω → ℝ} (hXm : ∀ t, Measurable (X t))
    {θhat : (T : ℕ) → Ω → Fin n → ℝ} (hmeas : ∀ T, Measurable (θhat T))
    {θ0 : Fin n → ℝ} {R : ℝ} (hbdd : ∀ (T : ℕ) (ω : Ω) (i : Fin n), |θhat T ω i| ≤ R)
    {psi : Fin n → ℤ → Ω → ℝ}
    (hpsiL2 : ∀ i t, MemLp (psi i t) 2 μ)
    (hpsiAdapted : ∀ i t, Measurable[sigmaLT X (t + 1)] (psi i t))
    (hpsiMDS : ∀ i t, μ[psi i t | sigmaLT X t] =ᵐ[μ] 0)
    (hpsiId : ∀ t : ℤ, IdentDistrib (fun ω i => psi i t ω) (fun ω i => psi i 0 ω) μ μ)
    (hlin : ∀ i, Tendsto (fun T : ℕ => ∫ ω, |Real.sqrt T * (θhat T ω i - θ0 i)
        - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω| ∂μ) atTop (𝓝 0))
    (c : Fin n → ℝ) {S : ℝ} (hS : 0 ≤ S)
    (hvar : ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => (μ {ω | δ ≤ |(T : ℝ)⁻¹ *
        (∑ t ∈ Finset.range T, μ[fun ω' => (∑ i, c i * psi i ((t : ℤ) + 1) ω') ^ 2
          | sigmaLT X ((t : ℤ) + 1)] ω) - S|}).toReal)
      atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
      atTop (𝓝 (charFun (gaussianReal 0 (Real.toNNReal S)) u)) := by
  classical
  have hpsiM : ∀ i t, Measurable (psi i t) := fun i t =>
    (hpsiAdapted i t).mono (sigmaLT_le_est hXm (t + 1)) le_rfl
  -- the martingale-difference sequence and its filtration
  have hξm : ∀ k : ℕ, Measurable (fun ω => ∑ i, c i * psi i ((k : ℤ) + 1) ω) := fun k =>
    Finset.measurable_sum _ fun i _ => (hpsiM i _).const_mul _
  have hξL2 : ∀ k : ℕ, MemLp (fun ω => ∑ i, c i * psi i ((k : ℤ) + 1) ω) 2 μ := fun k =>
    memLp_finset_sum _ (fun i _ => (hpsiL2 i _).const_mul _)
  -- (S2) the martingale CLT for the influence sum
  have hCLT : Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
      (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T,
        ∑ i, c i * psi i ((t : ℤ) + 1) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal S)) u)) := by
    refine mds_clt_sequence (ξ := fun k ω => ∑ i, c i * psi i ((k : ℤ) + 1) ω)
      (G := fun k : ℕ => sigmaLT X ((k : ℤ) + 1))
      (fun k => sigmaLT_le_est hXm _) (fun k l hkl => sigmaLT_mono_est (by omega))
      ?_ hξL2 ?_ hS hvar ?_ u
    · -- adaptedness
      intro k
      refine Measurable.mono (Finset.measurable_sum _ fun i _ =>
        (hpsiAdapted i ((k : ℤ) + 1)).const_mul (c i)) ?_ le_rfl
      exact sigmaLT_mono_est (by omega)
    · -- martingale-difference property
      intro k
      have hint : ∀ i : Fin n, Integrable (fun ω => c i * psi i ((k : ℤ) + 1) ω) μ :=
        fun i => ((hpsiL2 i _).const_mul (c i)).integrable one_le_two
      have hfun : (fun ω => ∑ i, c i * psi i ((k : ℤ) + 1) ω)
          = ∑ i : Fin n, (fun ω => c i * psi i ((k : ℤ) + 1) ω) := by
        funext ω; simp
      show μ[fun ω => ∑ i, c i * psi i ((k : ℤ) + 1) ω | sigmaLT X ((k : ℤ) + 1)] =ᵐ[μ] 0
      rw [hfun]
      refine (condExp_finset_sum (fun i _ => hint i) _).trans ?_
      have hz : ∀ i : Fin n,
          μ[fun ω => c i * psi i ((k : ℤ) + 1) ω | sigmaLT X ((k : ℤ) + 1)] =ᵐ[μ] 0 := by
        intro i
        have h1 : (fun ω => c i * psi i ((k : ℤ) + 1) ω) = c i • psi i ((k : ℤ) + 1) := by
          funext ω; simp
        rw [h1]
        filter_upwards [condExp_smul (c i) (psi i ((k : ℤ) + 1)) (sigmaLT X ((k : ℤ) + 1)),
          hpsiMDS i ((k : ℤ) + 1)] with ω e1 e2
        rw [e1]
        simp [e2]
      have : (∑ i : Fin n, μ[fun ω => c i * psi i ((k : ℤ) + 1) ω | sigmaLT X ((k : ℤ) + 1)])
          =ᵐ[μ] 0 := by
        have := (ae_all_iff (ι := Fin n)).2 (fun i => hz i)
        filter_upwards [this] with ω hω
        have : ∀ i : Fin n,
            (μ[fun ω' => c i * psi i ((k : ℤ) + 1) ω' | sigmaLT X ((k : ℤ) + 1)]) ω = 0 :=
          fun i => hω i
        simp [Finset.sum_apply, this]
      exact this
    · -- averaged Lindeberg
      intro ε hε
      have hζm : Measurable (fun ω => ∑ i, c i * psi i 0 ω) :=
        Finset.measurable_sum _ fun i _ => (hpsiM i _).const_mul _
      have hζ2 : MemLp (fun ω => ∑ i, c i * psi i 0 ω) 2 μ :=
        memLp_finset_sum _ (fun i _ => (hpsiL2 i _).const_mul _)
      have hu : Measurable (fun v : Fin n → ℝ => ∑ i, c i * v i) := by fun_prop
      have hkey : ∀ m k : ℕ,
          ∫ ω in {ω | ε * Real.sqrt m ≤ |∑ i, c i * psi i ((k : ℤ) + 1) ω|},
              (∑ i, c i * psi i ((k : ℤ) + 1) ω) ^ 2 ∂μ
            = ∫ ω in {ω | ε * Real.sqrt m ≤ |∑ i, c i * psi i 0 ω|},
              (∑ i, c i * psi i 0 ω) ^ 2 ∂μ := by
        intro m k
        refine setIntegral_sq_eq_of_identDistrib (hξm k) hζm ?_ _
        exact (hpsiId ((k : ℤ) + 1)).comp hu
      refine Tendsto.congr' ?_ (tendsto_setIntegral_sq_tail hζm hζ2 hε)
      filter_upwards [eventually_ge_atTop 1] with m hm
      rw [Finset.sum_congr rfl (fun k _ => hkey m k), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      field_simp
  -- (S1) `L¹`-Slutsky
  have hZm : ∀ T : ℕ, Measurable (fun ω => Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) := by
    intro T
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    exact (((measurable_pi_apply i).comp (hmeas T)).sub_const _).const_mul _
  have hWm : ∀ T : ℕ, Measurable (fun ω => (Real.sqrt T)⁻¹ *
      ∑ t ∈ Finset.range T, ∑ i, c i * psi i ((t : ℤ) + 1) ω) := fun T =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ => hξm t) _
  have hIfirst : ∀ (T : ℕ) (i : Fin n),
      Integrable (fun ω => Real.sqrt T * (θhat T ω i - θ0 i)) μ := by
    intro T i
    refine (integrable_const (Real.sqrt T * (R + |θ0 i|))).mono'
      ((((measurable_pi_apply i).comp (hmeas T)).sub_const _).const_mul _).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact (abs_sub _ _).trans (add_le_add (hbdd T ω i) le_rfl)
  have hIsecond : ∀ (T : ℕ) (i : Fin n),
      Integrable (fun ω => (Real.sqrt T)⁻¹ *
        ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω) μ := by
    intro T i
    exact ((memLp_finset_sum (Finset.range T)
      (fun (t : ℕ) (_ : t ∈ Finset.range T) => hpsiL2 i ((t : ℤ) + 1))).const_mul
      (Real.sqrt T)⁻¹).integrable one_le_two
  have hd : ∀ (T : ℕ) (i : Fin n), Integrable (fun ω => Real.sqrt T * (θhat T ω i - θ0 i)
      - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω) μ :=
    fun T i => (hIfirst T i).sub (hIsecond T i)
  have hid : ∀ (T : ℕ) (ω : Ω),
      (Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i))
        - ((Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, ∑ i, c i * psi i ((t : ℤ) + 1) ω)
      = ∑ i, c i * (Real.sqrt T * (θhat T ω i - θ0 i)
          - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω) := by
    intro T ω
    have h1 : ∑ t ∈ Finset.range T, ∑ i, c i * psi i ((t : ℤ) + 1) ω
        = ∑ i, c i * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    rw [h1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine tendsto_charFun_map_of_l1 hZm hWm ?_ ?_ hCLT
  · intro T
    refine Integrable.abs ?_
    refine Integrable.congr ?_ (Eventually.of_forall fun ω => (hid T ω).symm)
    exact integrable_finset_sum _ fun i _ => (hd T i).const_mul _
  · refine squeeze_zero (fun T => integral_nonneg fun ω => abs_nonneg _) ?_ ?_
      (g := fun T : ℕ => ∑ i, |c i| * ∫ ω, |Real.sqrt T * (θhat T ω i - θ0 i)
        - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω| ∂μ)
    · intro T
      have hle : ∫ ω, |Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)
            - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T,
              ∑ i, c i * psi i ((t : ℤ) + 1) ω| ∂μ
          ≤ ∫ ω, ∑ i, |c i| * |Real.sqrt T * (θhat T ω i - θ0 i)
              - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω| ∂μ := by
        refine integral_mono ?_ ?_ fun ω => ?_
        · exact (Integrable.congr (integrable_finset_sum _ fun i _ => (hd T i).const_mul _)
            (Eventually.of_forall fun ω => (hid T ω).symm)).abs
        · exact integrable_finset_sum _ fun i _ => ((hd T i).abs).const_mul _
        · rw [hid T ω]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
      refine hle.trans (le_of_eq ?_)
      rw [integral_finset_sum _ fun i _ => ((hd T i).abs).const_mul _]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    · have : Tendsto (fun T : ℕ => ∑ i, |c i| * ∫ ω, |Real.sqrt T * (θhat T ω i - θ0 i)
          - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω| ∂μ)
          atTop (𝓝 (∑ i : Fin n, |c i| * 0)) :=
        tendsto_finset_sum _ fun i _ => (hlin i).const_mul _
      simpa using this

/-- The **coordinate packing of a GARCH parameter** `(c₀, b, a)` into the vector the
asymptotic statements are indexed by: slots `0, …, p−1` carry `b`, slots `p, …, p+q−1`
carry `a`, and the last slot carries `c₀`. -/
noncomputable def garchParamVec {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ) :
    Fin (p + q + 1) → ℝ := fun i =>
  if h1 : (i : ℕ) < p then b ⟨i, h1⟩
  else if h2 : (i : ℕ) - p < q then a ⟨(i : ℕ) - p, h2⟩
  else c0

/-- A compact search region bounds every coordinate of the packed parameter vector. -/
private lemma exists_bound_garchParamVec {p q : ℕ}
    {K : Set (ℝ × (Fin p → ℝ) × (Fin q → ℝ))} (hK : IsCompact K) :
    ∃ R : ℝ, ∀ x ∈ K, ∀ i : Fin (p + q + 1),
      |garchParamVec x.1 x.2.1 x.2.2 i| ≤ R := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × (Fin p → ℝ) × (Fin q → ℝ))
  refine ⟨R, fun x hx i => ?_⟩
  have hxR : ‖x‖ ≤ R := by
    simpa [dist_zero_right] using Metric.mem_closedBall.1 (hR hx)
  have h2 : ‖x.2‖ ≤ R := le_trans (norm_snd_le x) hxR
  simp only [garchParamVec]
  split_ifs with h1 hh2
  · calc |x.2.1 ⟨(i : ℕ), h1⟩| = ‖x.2.1 ⟨(i : ℕ), h1⟩‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x.2.1‖ := norm_le_pi_norm _ _
      _ ≤ ‖x.2‖ := norm_fst_le x.2
      _ ≤ R := h2
  · calc |x.2.2 ⟨(i : ℕ) - p, hh2⟩| = ‖x.2.2 ⟨(i : ℕ) - p, hh2⟩‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x.2.2‖ := norm_le_pi_norm _ _
      _ ≤ ‖x.2‖ := norm_snd_le x.2
      _ ≤ R := h2
  · calc |x.1| = ‖x.1‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_fst_le x
      _ ≤ R := hxR

/-- **DEBT (Giraitis & Robinson 2001; FY §4.2.3)**: `√T`-asymptotic normality of the
Whittle estimator of a GARCH model under fourth-order stationarity, in Cramér–Wold/charFun
form.

**Repaired 2026-08-09** — the frozen form is refuted by `whittle_clt_debt_false` above;
see the section note for the four repairs and for the residue map.

**PROVED 2026-08-09 (`ts/f3-spectral-garch-finale`)** from the repaired hypotheses, by
`clt_of_asymptotically_linear`: (S1) `L¹`-Slutsky along `hlin`, then (S2) Brown's
martingale CLT for the influence sum. Giraitis–Robinson's own analysis is exactly what
`hlin`/`hWdef` package. -/
theorem whittle_clt_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: fourth-order stationarity; FY §4.2.3 / GR 2001
    (hL4 : ∀ t, MemLp (X t) 4 μ)
    -- USER-INPUT: nondegenerate intercept; GR 2001 standing assumption
    (hc0 : 0 < c0)
    -- USER-INPUT: the limiting covariance matrix, now pinned by `hWdef` below; GR 2001
    (W : Matrix (Fin (p + q + 1)) (Fin (p + q + 1)) ℝ) (hW : Matrix.PosDef W)
    (θhat : (T : ℕ) → Ω → Fin (p + q + 1) → ℝ) (hmeas : ∀ T, Measurable (θhat T))
    (θ0 : Fin (p + q + 1) → ℝ)
    -- USER-INPUT (repair 1): `θ₀` is the parameter of the model in `h`
    (hθ0 : θ0 = garchParamVec c0 b a)
    -- USER-INPUT (repair 2): `θhat` minimizes the Whittle criterion (4.41) over a compact
    -- identifiable search region containing the truth in its interior; `gmodel ϑ` is the
    -- model spectral density of the squared process at the candidate `ϑ`
    (gmodel : ℝ × (Fin p → ℝ) × (Fin q → ℝ) → ℝ → ℝ)
    (est : (T : ℕ) → Ω → ℝ × (Fin p → ℝ) × (Fin q → ℝ))
    (hpack : ∀ (T : ℕ) (ω : Ω),
      θhat T ω = garchParamVec (est T ω).1 (est T ω).2.1 (est T ω).2.2)
    (K : Set (ℝ × (Fin p → ℝ) × (Fin q → ℝ))) (hK : IsCompact K)
    (hK0 : (c0, b, a) ∈ interior K)
    (hmin : ∀ (T : ℕ) (ω : Ω), est T ω ∈ K ∧ ∀ ϑ ∈ K,
      garchWhittle (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (gmodel (est T ω))
        ≤ garchWhittle (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (gmodel ϑ))
    -- USER-INPUT (repair 3): the asymptotically linear representation GR 2001 prove, with
    -- influence process `ψ` — a square-integrable, strict-past-adapted martingale
    -- difference with time-invariant joint law — and `W = E[ψ₀ψ₀ᵀ]`
    (psi : Fin (p + q + 1) → ℤ → Ω → ℝ)
    (hpsiL2 : ∀ i t, MemLp (psi i t) 2 μ)
    (hpsiAdapted : ∀ i t, Measurable[sigmaLT X (t + 1)] (psi i t))
    (hpsiMDS : ∀ i t, μ[psi i t | sigmaLT X t] =ᵐ[μ] 0)
    (hpsiId : ∀ t : ℤ, IdentDistrib (fun ω i => psi i t ω) (fun ω i => psi i 0 ω) μ μ)
    (hWdef : ∀ i j, W i j = ∫ ω, psi i 0 ω * psi j 0 ω ∂μ)
    (hlin : ∀ i, Tendsto (fun T : ℕ => ∫ ω, |Real.sqrt T * (θhat T ω i - θ0 i)
        - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω| ∂μ) atTop (𝓝 0))
    (c : Fin (p + q + 1) → ℝ)
    -- USER-INPUT (repair 4): Brown's conditional-variance hypothesis for the influence
    -- process — the ergodicity brick; see the residue note
    (hvar : ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => (μ {ω | δ ≤ |(T : ℝ)⁻¹ *
        (∑ t ∈ Finset.range T, μ[fun ω' => (∑ i, c i * psi i ((t : ℤ) + 1) ω') ^ 2
          | sigmaLT X ((t : ℤ) + 1)] ω) - ∑ i, ∑ j, c i * c j * W i j|}).toReal)
      atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i * c j * W i j))) u)) := by
  -- (S1) + (S2): the asymptotically linear representation `hlin` transports the martingale
  -- CLT for the influence sum, whose Brown hypotheses are `hpsiAdapted`/`hpsiMDS`/`hpsiL2`
  -- (adaptedness, martingale difference, `L²`), `hvar` (the ergodicity brick) and `hpsiId`
  -- (identical distribution, which makes the averaged Lindeberg condition free).
  obtain ⟨R, hRbd⟩ := exists_bound_garchParamVec hK
  refine clt_of_asymptotically_linear (X := X) h.measurableX hmeas (R := R) (fun T ω i => ?_)
    hpsiL2 hpsiAdapted hpsiMDS hpsiId hlin c (nonneg_influence_form hpsiL2 hWdef c) hvar u
  rw [hpack T ω]
  exact hRbd _ (hmin T ω).1 i

/-- **DEBT (Peng & Yao 2002/2003; FY §4.2.3)**: `√T`-asymptotic normality of the LAD
estimator, which unlike the QMLE needs no moment condition beyond the model's own —
the heavy-tail-robust alternative FY highlights.

**Repaired 2026-08-09** — the frozen form is refuted by `lad_clt_debt_false` above; see the
section note for the four repairs and for the residue map. Note that the LAD score is a
*bounded* martingale difference (the signs `sign(log ε_t²)` are `±1`), so `hpsiL2` is
automatic for the true influence process and the whole (S2) half is free of moment
conditions — which is exactly FY's stated reason for preferring LAD.

**PROVED 2026-08-09 (`ts/f3-spectral-garch-finale`)** by the *same* application of
`clt_of_asymptotically_linear` as `whittle_clt_debt`: the two proofs are character for
character identical, which is the sharpest confirmation that repair 3 relocated the
GR/PY-specific analysis entirely into `hlin`/`hWdef`. -/
theorem lad_clt_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: median-1 normalization of the squared innovations; Peng & Yao
    (hmed : μ {ω | ε 0 ω ^ 2 ≤ 1} = μ {ω | 1 ≤ ε 0 ω ^ 2})
    -- USER-INPUT: nondegenerate intercept; Peng & Yao standing assumption
    (hc0 : 0 < c0)
    -- USER-INPUT: the limiting covariance matrix, now pinned by `hWdef` below; PY 2003
    (W : Matrix (Fin (p + q + 1)) (Fin (p + q + 1)) ℝ) (hW : Matrix.PosDef W)
    (θhat : (T : ℕ) → Ω → Fin (p + q + 1) → ℝ) (hmeas : ∀ T, Measurable (θhat T))
    (θ0 : Fin (p + q + 1) → ℝ)
    -- USER-INPUT (repair 1): `θ₀` is the parameter of the model in `h`
    (hθ0 : θ0 = garchParamVec c0 b a)
    -- USER-INPUT (repair 2): `θhat` minimizes the LAD criterion (4.42) over a compact
    -- identifiable search region containing the truth in its interior, from the presample
    -- value `v₀` and burn-in `ν`
    (v0 : ℝ) (ν : ℕ)
    (est : (T : ℕ) → Ω → ℝ × (Fin p → ℝ) × (Fin q → ℝ))
    (hpack : ∀ (T : ℕ) (ω : Ω),
      θhat T ω = garchParamVec (est T ω).1 (est T ω).2.1 (est T ω).2.2)
    (K : Set (ℝ × (Fin p → ℝ) × (Fin q → ℝ))) (hK : IsCompact K)
    (hK0 : (c0, b, a) ∈ interior K)
    (hmin : ∀ (T : ℕ) (ω : Ω), est T ω ∈ K ∧ ∀ ϑ ∈ K,
      garchLAD (est T ω).1 (est T ω).2.1 (est T ω).2.2 v0
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ν
        ≤ garchLAD ϑ.1 ϑ.2.1 ϑ.2.2 v0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ν)
    -- USER-INPUT (repair 3): the asymptotically linear representation PY 2003 prove, with
    -- influence process `ψ` (their sign-score, a *bounded* martingale difference) and
    -- `W = E[ψ₀ψ₀ᵀ]`
    (psi : Fin (p + q + 1) → ℤ → Ω → ℝ)
    (hpsiL2 : ∀ i t, MemLp (psi i t) 2 μ)
    (hpsiAdapted : ∀ i t, Measurable[sigmaLT X (t + 1)] (psi i t))
    (hpsiMDS : ∀ i t, μ[psi i t | sigmaLT X t] =ᵐ[μ] 0)
    (hpsiId : ∀ t : ℤ, IdentDistrib (fun ω i => psi i t ω) (fun ω i => psi i 0 ω) μ μ)
    (hWdef : ∀ i j, W i j = ∫ ω, psi i 0 ω * psi j 0 ω ∂μ)
    (hlin : ∀ i, Tendsto (fun T : ℕ => ∫ ω, |Real.sqrt T * (θhat T ω i - θ0 i)
        - (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, psi i ((t : ℤ) + 1) ω| ∂μ) atTop (𝓝 0))
    (c : Fin (p + q + 1) → ℝ)
    -- USER-INPUT (repair 4): Brown's conditional-variance hypothesis for the influence
    -- process — the ergodicity brick; see the residue note
    (hvar : ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => (μ {ω | δ ≤ |(T : ℝ)⁻¹ *
        (∑ t ∈ Finset.range T, μ[fun ω' => (∑ i, c i * psi i ((t : ℤ) + 1) ω') ^ 2
          | sigmaLT X ((t : ℤ) + 1)] ω) - ∑ i, ∑ j, c i * c j * W i j|}).toReal)
      atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i * c j * W i j))) u)) := by
  -- (S1) + (S2): the asymptotically linear representation `hlin` transports the martingale
  -- CLT for the influence sum, whose Brown hypotheses are `hpsiAdapted`/`hpsiMDS`/`hpsiL2`
  -- (adaptedness, martingale difference, `L²`), `hvar` (the ergodicity brick) and `hpsiId`
  -- (identical distribution, which makes the averaged Lindeberg condition free).
  obtain ⟨R, hRbd⟩ := exists_bound_garchParamVec hK
  refine clt_of_asymptotically_linear (X := X) h.measurableX hmeas (R := R) (fun T ω i => ?_)
    hpsiL2 hpsiAdapted hpsiMDS hpsiId hlin c (nonneg_influence_form hpsiL2 hWdef c) hvar u
  rw [hpack T ω]
  exact hRbd _ (hmin T ω).1 i

/-! ### Sanity checks on the criteria

Cheap facts pinning down the degenerate corners and the AIC/BIC penalties, so that the
definitions above are exercised rather than merely stated. -/

/-- Strict positivity of the truncated volatility — what the `log σ̃_t²` in (4.37) and the
division in (4.38) actually need. -/
private lemma garchTruncVol_pos {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    {v0 : ℝ} (hc0 : 0 < c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hv0 : 0 < v0)
    {T : ℕ} (x : Fin T → ℝ) (n : ℕ) :
    0 < garchTruncVol c0 b a v0 x n := by
  match n with
  | 0 => simpa [garchTruncVol] using hv0
  | (m + 1) =>
    rw [garchTruncVol]
    have h1 : 0 ≤ ∑ i : Fin p,
        b i * (if h : m - (i : ℕ) < T then x ⟨m - (i : ℕ), h⟩ else 0) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (sq_nonneg _)
    have h2 : 0 ≤ ∑ j : Fin q, a j * garchTruncVol c0 b a v0 x (m - (j : ℕ)) :=
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (ha j) (garchTruncVol_nonneg hc0.le hb ha hv0.le x _)
    linarith

/-- The quasi-likelihood (4.37) over an empty time range is `0` (in particular at `T = 0`). -/
private lemma garchQuasiLik_of_le {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) {ν : ℕ} (h : T ≤ ν) :
    garchQuasiLik c0 b a v0 x ν = 0 := by
  simp [garchQuasiLik, Finset.Ico_eq_empty_of_le h]

/-- The general-density criterion (4.38) over an empty time range is `0`. -/
private lemma garchDensityLik_of_le {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) (f : ℝ → ℝ) {T : ℕ} (x : Fin T → ℝ) {ν : ℕ} (h : T ≤ ν) :
    garchDensityLik c0 b a v0 f x ν = 0 := by
  simp [garchDensityLik, Finset.Ico_eq_empty_of_le h]

/-- The LAD criterion (4.42) over an empty time range is `0`. -/
private lemma garchLAD_of_le {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) {ν : ℕ} (h : T ≤ ν) :
    garchLAD c0 b a v0 x ν = 0 := by
  simp [garchLAD, Finset.Ico_eq_empty_of_le h]

/-- The Whittle criterion (4.41) is well defined on an empty frequency range, where it
vanishes; the Fourier frequencies `k = 1, …, T − 1` are none for `T ≤ 1`. -/
private lemma garchWhittle_of_le_one {T : ℕ} (x : Fin T → ℝ) (gmodel : ℝ → ℝ)
    (h : T ≤ 1) : garchWhittle x gmodel = 0 := by
  simp [garchWhittle, Finset.Ico_eq_empty_of_le h]

/-- AIC (4.39) is the quasi-likelihood plus its stated `2(p + q + 1)` penalty. -/
private lemma garchAIC_sub_quasiLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) :
    garchAIC c0 b a v0 x ν - garchQuasiLik c0 b a v0 x ν = 2 * ((p : ℝ) + (q : ℝ) + 1) := by
  simp [garchAIC]

/-- BIC (4.40) is the quasi-likelihood plus its stated `(p + q + 1) log T` penalty. -/
private lemma garchBIC_sub_quasiLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) :
    garchBIC c0 b a v0 x ν - garchQuasiLik c0 b a v0 x ν
      = ((p : ℝ) + (q : ℝ) + 1) * Real.log T := by
  simp [garchBIC]

end StatLean.TimeSeries
