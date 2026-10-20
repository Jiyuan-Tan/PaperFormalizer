module
public import StatLean.TimeSeries.Process.SecondOrder
public import StatLean.TimeSeries.ForMathlib.PosSemidefSequence

@[expose] public section

/-!
# The autocovariance function — symmetry, bounds, positive semidefiniteness
(FY §2.2.1, Theorem 2.7)

For a weakly stationary process: evenness `γ(−k) = γ(k)`, the bound `|γ(k)| ≤ γ(0)`
(Cauchy–Schwarz), and **FY Theorem 2.7 (necessity)**: the autocovariance function is an
even, positive semidefinite sequence — `Σᵢⱼ aᵢaⱼ γ(tᵢ − tⱼ) = Var(Σᵢ aᵢ X_{tᵢ}) ≥ 0`.
The **sufficiency** half lives in `Stationarity/Gaussian.lean`
(`exists_stationary_of_isPosSemidefSeq`, proved by the random-phase construction over
the Herglotz spectral measure). Basic ACF facts (`ρ(0) = 1`, `|ρ(k)| ≤ 1`) close the
section.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.2.1:
Definition 2.5, Theorem 2.7 with eq. (2.17) (pp. 39–40). (`FY §2.2.1 Thm 2.7`.)

**Proof formalization notes.** Positive semidefiniteness expands
`Var(Σ aᵢ X_{tᵢ})` bilinearly into `Σᵢⱼ aᵢaⱼ Cov(X_{tᵢ}, X_{tⱼ})` and applies
`IsStationary.cov_eq_acvf`; square-integrability comes from the `memLp` field. The
sufficiency statement quantifies existentially over the probability space (`Ω : Type`),
matching FY's "of some stationary time series".

**Bibliographic comments.** The characterization of covariance functions by nonnegative
definiteness is A. Ya. Khinchin (1934); the Gaussian-process construction of the
sufficiency half is standard Kolmogorov-extension reasoning (Kolmogorov,
*Grundbegriffe*, 1933).
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℤ → Ω → ℝ}

/-- Evenness of the autocovariance (FY §2.2.1): `γ(−k) = γ(k)`. -/
theorem IsStationary.acvf_even (h : IsStationary X μ) (k : ℤ) :
    acvf X μ (-k) = acvf X μ k := by
  have hcomm : acvf X μ (-k) = cov[X 0, X (-k); μ] := covariance_comm _ _
  rw [hcomm, h.cov_eq_acvf 0 (-k)]
  norm_num

/-- `|γ(k)| ≤ γ(0)` (Cauchy–Schwarz; FY §2.2.1). -/
theorem IsStationary.abs_acvf_le [IsProbabilityMeasure μ] (h : IsStationary X μ)
    (k : ℤ) : |acvf X μ k| ≤ acvf X μ 0 := by
  -- The `2 × 2` quadratic forms with coefficients `(1, -1)` and `(1, 1)`:
  -- `0 ≤ Var(X_k ∓ X_0) = 2γ(0) ∓ 2γ(k)`.
  have hk : Var[X k; μ] = acvf X μ 0 := (h.acvf_zero_eq_variance k).symm
  have h0 : Var[X 0; μ] = acvf X μ 0 := (h.acvf_zero_eq_variance 0).symm
  have hcov : cov[X k, X 0; μ] = acvf X μ k := rfl
  have hsub := variance_sub (μ := μ) (h.memLp k) (h.memLp 0)
  have hadd := variance_add (μ := μ) (h.memLp k) (h.memLp 0)
  rw [hk, h0, hcov] at hsub hadd
  have hsub0 : (0 : ℝ) ≤ acvf X μ 0 - 2 * acvf X μ k + acvf X μ 0 := hsub ▸ variance_nonneg _ _
  have hadd0 : (0 : ℝ) ≤ acvf X μ 0 + 2 * acvf X μ k + acvf X μ 0 := hadd ▸ variance_nonneg _ _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **FY Theorem 2.7, necessity**: the autocovariance function of a weakly stationary
process is positive semidefinite (`Σᵢⱼ aᵢaⱼ γ(tᵢ − tⱼ) = Var(Σᵢ aᵢ X_{tᵢ}) ≥ 0`,
eq. (2.17)). -/
theorem IsStationary.acvf_posSemidef [IsProbabilityMeasure μ] (h : IsStationary X μ) :
    IsPosSemidefSeq (acvf X μ) := by
  intro n t a
  -- `Σᵢⱼ aᵢaⱼ γ(tᵢ − tⱼ) = Var(Σᵢ aᵢ X_{tᵢ}) ≥ 0` (FY eq. (2.17)).
  have hmem : ∀ i : Fin n, MemLp (a i • X (t i)) 2 μ := fun i => (h.memLp (t i)).const_smul (a i)
  have hcov : ∀ i j : Fin n,
      cov[a i • X (t i), a j • X (t j); μ] = a i * a j * acvf X μ (t i - t j) := by
    intro i j
    rw [covariance_smul_left, covariance_smul_right, h.cov_eq_acvf (t i) (t j), mul_assoc]
  calc (0 : ℝ)
      ≤ Var[∑ i, a i • X (t i); μ] := variance_nonneg _ _
    _ = ∑ i, ∑ j, cov[a i • X (t i), a j • X (t j); μ] := variance_sum hmem
    _ = ∑ i, ∑ j, a i * a j * acvf X μ (t i - t j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hcov i j

/-- `ρ(0) = 1` when `γ(0) ≠ 0` (no stationarity needed: this is `div_self`). -/
theorem acf_zero (h0 : acvf X μ 0 ≠ 0) : acf X μ 0 = 1 :=
  div_self h0

/-- `|ρ(k)| ≤ 1` (FY §2.2.1). -/
theorem IsStationary.abs_acf_le_one [IsProbabilityMeasure μ] (h : IsStationary X μ)
    (k : ℤ) : |acf X μ k| ≤ 1 := by
  rcases eq_or_lt_of_le h.acvf_zero_nonneg with h0 | h0
  · -- Degenerate case `γ(0) = 0`: `ρ(k) = γ(k)/0 = 0` by Lean's division convention.
    have : acf X μ k = 0 := by rw [acf, ← h0, div_zero]
    rw [this, abs_zero]
    norm_num
  · rw [acf, abs_div, abs_of_pos h0, div_le_one h0]
    exact h.abs_acvf_le k

end StatLean.TimeSeries
