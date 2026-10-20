module
public import StatLean.TimeSeries.Threshold.Estimation

@[expose] public section

/-!
# Testing linearity against a two-regime TAR alternative (FY §4.1.3, eq. (4.9))

The Chan–Tong likelihood-ratio/F setup: `H₀` a linear AR(p) against `H₁` a two-regime
SETAR with common order `p`, common noise scale, known delay `d`, and threshold `r`
ranging over a known compact grid `𝓘_r`. Under `H₀` the threshold is **unidentified**,
which is why the null limit law is nonstandard — and why FY never states it.

* `arLSResidualSS` — the `H₀` residual sum of squares (a whole-sample AR(p) LS fit);
* `setarProfileResidualSS` — the `H₁` profiled residual sum of squares, minimized over
  the two regime-coefficient vectors at a fixed threshold `r`;
* `linearityStat` — **FY eq. (4.9)**
  `S_T = (T − max(p, d)) (σ̂₀² − σ̂²)/σ̂²`, with the difference in the order confirmed
  by the book's p. 139 usage *(p. 135 prints the difference flipped — documented
  misprint; we state the p. 139 order, which is the only nonnegative one)*;
* `linearityStat_nonneg` — the sanity fact that `S_T ≥ 0` (the SETAR family contains
  the AR family, so profiling can only reduce the residual sum of squares).

**Non-targets (documented).** FY eq. (4.10) is Chan's (1991) Poisson-clump *heuristic*
tail approximation, and Tables 4.1–4.2 are simulated percentage points; neither is a
theorem and neither is stated here. **The null limit law of `S_T` is never stated in
the book**, so there is nothing to formalize — not even as a debt.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.1.3,
eqs. (4.9)–(4.10) (pp. 134–136). (`FY §4.1.3`.)

**Bibliographic comments.** The test is Chan & Tong (1990) / Chan (1991); the
unidentified-nuisance-parameter phenomenon under `H₀` is Davies (1977, 1987), with the
sup-LR theory developed by Andrews & Ploberger (1994) and Hansen (1996).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- The `H₀` (linear AR(p)) **residual sum of squares** over the usable window. -/
noncomputable def arLSResidualSS {T P : ℕ} (x : Fin T → ℝ) (β0 : ℝ) (β : Fin P → ℝ) :
    ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin T => P < (t : ℕ)),
    (x t - β0 - ∑ j : Fin P, β j *
      x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩) ^ 2

/-- The `H₁` (two-regime SETAR at threshold `r`) residual sum of squares: the sum of the
two regime residual sums of squares of `Threshold/Estimation.lean`. -/
noncomputable def setarResidualSS {T P : ℕ} (x : Fin T → ℝ) (d : ℕ) (r : ℝ)
    (β0 : Fin 2 → ℝ) (β : Fin 2 → Fin P → ℝ) : ℝ :=
  tarLSResidualSS x {y : ℝ | y ≤ r} d (β0 0) (β 0)
    + tarLSResidualSS x {y : ℝ | r < y} d (β0 1) (β 1)

/-- **FY eq. (4.9)**, in the p. 139 orientation (the p. 135 display prints the
difference flipped — documented misprint): `S_T = (T − max(p,d))(σ̂₀² − σ̂²)/σ̂²`, where
`σ̂₀²` and `σ̂²` are the `H₀` and profiled-`H₁` residual sums of squares divided by the
same window size. Junk `0` when the alternative fit is degenerate (`σ̂² = 0`). -/
noncomputable def linearityStat {T P : ℕ} (x : Fin T → ℝ) (d : ℕ)
    (ss0 ss1 : ℝ) : ℝ :=
  ((T : ℝ) - (max P d : ℕ)) * (ss0 - ss1) / ss1

/-- The alternative family contains the null family (pad both regimes with the same
coefficients), so the profiled `H₁` residual sum of squares never exceeds the `H₀`
one — hence `S_T ≥ 0` whenever the alternative fit is nondegenerate. -/
theorem setarResidualSS_le_arLSResidualSS {T P : ℕ} (x : Fin T → ℝ) (d : ℕ) (r : ℝ)
    (β0 : ℝ) (β : Fin P → ℝ) (hd : 1 ≤ d) (hdP : d ≤ P) :
    setarResidualSS x d r (fun _ => β0) (fun _ => β) = arLSResidualSS x β0 β := by
  classical
  -- The two regime index sets are the two halves of the AR window split by the sign of
  -- `x_{t−d} − r`: the extra guard `d ≤ t` of `tarRegimeIndices` is implied by `P < t`
  -- (as `d ≤ P`), so it disappears from both filters.
  set S : Finset (Fin T) := Finset.univ.filter (fun t : Fin T => P < (t : ℕ)) with hS
  have hlow : tarRegimeIndices x {y : ℝ | y ≤ r} d P
      = S.filter fun t : Fin T =>
          x ⟨(t : ℕ) - d, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ ≤ r := by
    ext t
    simp only [tarRegimeIndices, hS, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨ht, -, hx⟩; exact ⟨ht, hx⟩
    · rintro ⟨ht, hx⟩; exact ⟨ht, le_of_lt (lt_of_le_of_lt hdP ht), hx⟩
  have hhigh : tarRegimeIndices x {y : ℝ | r < y} d P
      = S.filter fun t : Fin T =>
          ¬ x ⟨(t : ℕ) - d, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ ≤ r := by
    ext t
    simp only [tarRegimeIndices, hS, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq, not_le]
    constructor
    · rintro ⟨ht, -, hx⟩; exact ⟨ht, hx⟩
    · rintro ⟨ht, hx⟩; exact ⟨ht, le_of_lt (lt_of_le_of_lt hdP ht), hx⟩
  simp only [setarResidualSS, tarLSResidualSS, arLSResidualSS, hlow, hhigh, ← hS]
  exact Finset.sum_filter_add_sum_filter_not S _ _

/-- `S_T ≥ 0` at any threshold, for the best-fitting alternative: profiling over a
family containing the null cannot increase the residual sum of squares. -/
theorem linearityStat_nonneg {T P : ℕ} (x : Fin T → ℝ) (d : ℕ) {ss0 ss1 : ℝ}
    (hT : max P d ≤ T) (hss1 : 0 < ss1) (hle : ss1 ≤ ss0) :
    0 ≤ linearityStat (P := P) x d ss0 ss1 := by
  have hwin : (0 : ℝ) ≤ (T : ℝ) - ((max P d : ℕ) : ℝ) := by
    have : ((max P d : ℕ) : ℝ) ≤ (T : ℝ) := Nat.cast_le.mpr hT
    linarith
  exact div_nonneg (mul_nonneg hwin (by linarith)) hss1.le

end StatLean.TimeSeries
