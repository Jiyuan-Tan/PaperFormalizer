module
public import StatLean.StatisticalModels.FactorModels.Moments

@[expose] public section

/-!
# Communality and specific variance — the coordinatewise variance split

The coordinatewise reading of the covariance decomposition. For standardized (orthogonal)
factors `BKM` Eq. (3.10) splits the variance of each observed coordinate into the part
explained by the common factors and the part specific to that coordinate:

* `communality P i = ∑ⱼ λᵢⱼ²` — the **communality** `hᵢ²` of coordinate `i` (`BKM` p. 49,
  immediately after Eq. (3.10));
* `specificVariance P i = ψᵢ` — the **specific variance** of coordinate `i` (`BKM`'s own
  term; the wider literature also calls it the *uniqueness*);
* **`variance_eq_communality_add_specificVariance`** — `var(xᵢ) = hᵢ² + ψᵢ`, `BKM` Eq. (3.10);
* `communality_nonneg`, `specificVariance_nonneg`, `communality_le_variance`, and — for
  standardized observed variables — `communality_le_one`.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, Eq. (3.10) and the paragraph defining
the communality (p. 49) (`BKM`).

**Proof formalization notes.** Everything here is the `(i, i)` entry of the covariance
decomposition `Σ = Λ Φ Λᵀ + Ψ`.
*Book vs Lean:* `BKM` Eq. (3.10) presumes its normalization `Φ = I` (Eq. (3.2)); the
statements below therefore carry `IsStandardized` explicitly. With correlated factors
(`Φ ≠ I`) the split is `var(xᵢ) = (Λ Φ Λᵀ)ᵢᵢ + ψᵢ`, which is
`variance_eq_common_add_specificVariance` and holds with no hypothesis at all.

**Bibliographic comments.** The communality is Thurstone's (*Multiple-Factor Analysis*, 1947);
the "communality problem" — determining `hᵢ²` from the off-diagonal correlations alone — is
the historical origin of the identifiability discussion in `BKM` §3.12.1.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-- The **communality** `hᵢ² = ∑ⱼ λᵢⱼ²` of observed coordinate `i` — the part of its variance
explained by the common factors, for standardized factors (`BKM` p. 49, after Eq. (3.10)).

*Edge behavior:* the formula is the sum of squared loadings whatever `Φ` is; it equals the
common part `(Λ Φ Λᵀ)ᵢᵢ` of the variance exactly when `Φ = I`
(`commonCovariance_diag_eq_communality`). -/
noncomputable def communality (P : FactorParams p q) (i : Fin p) : ℝ :=
  ∑ k, (P.loading i k) ^ 2

/-- The **specific variance** `ψᵢ` of observed coordinate `i` (`BKM` Eq. (3.10); the wider
literature calls it the *uniqueness*). -/
noncomputable def specificVariance (P : FactorParams p q) (i : Fin p) : ℝ :=
  P.uniqueCov i i

/-- The **general variance split**, valid for arbitrary `Φ`: the diagonal of `Σ` is the
diagonal of the common part plus the specific variance. Definitional. -/
theorem variance_eq_common_add_specificVariance (P : FactorParams p q) (i : Fin p) :
    factorCovariance P i i = commonCovariance P i i + specificVariance P i := by
  rw [factorCovariance_eq_commonCovariance_add, Matrix.add_apply]
  rfl

/-- For standardized factors the diagonal of the common part **is** the communality. -/
theorem commonCovariance_diag_eq_communality (P : FactorParams p q)
    -- USER-INPUT: BKM's normalization y ∼ N_q(0, I); BKM Eq. (3.2)
    (hP : IsStandardized P) (i : Fin p) :
    commonCovariance P i i = communality P i := by
  rw [commonCovariance_eq, hP, Matrix.mul_one, Matrix.mul_apply, communality]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.transpose_apply, sq]

/-- **`BKM` Eq. (3.10) — the variance decomposition**: for standardized orthogonal factors,
`var(xᵢ) = hᵢ² + ψᵢ`. -/
theorem variance_eq_communality_add_specificVariance (P : FactorParams p q)
    -- USER-INPUT: BKM's normalization y ∼ N_q(0, I); BKM Eq. (3.2)
    (hP : IsStandardized P) (i : Fin p) :
    factorCovariance P i i = communality P i + specificVariance P i := by
  rw [variance_eq_common_add_specificVariance, commonCovariance_diag_eq_communality P hP]

/-- Communalities are nonnegative (a sum of squares). -/
theorem communality_nonneg (P : FactorParams p q) (i : Fin p) : 0 ≤ communality P i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Specific variances are nonnegative for a genuine `Ψ`. -/
theorem specificVariance_nonneg (P : FactorParams p q)
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) (i : Fin p) :
    0 ≤ specificVariance P i :=
  hΨ.diag_nonneg

/-- The communality never exceeds the variance it decomposes (`BKM` Eq. (3.10) with
`ψᵢ ≥ 0`). -/
theorem communality_le_variance (P : FactorParams p q)
    -- USER-INPUT: BKM's normalization y ∼ N_q(0, I); BKM Eq. (3.2)
    (hP : IsStandardized P)
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) (i : Fin p) :
    communality P i ≤ factorCovariance P i i := by
  rw [variance_eq_communality_add_specificVariance P hP i]
  linarith [specificVariance_nonneg P hΨ i]

/-- For **standardized observed variables** — the correlation-matrix scaling in which factor
analysis is usually reported — the communality is at most `1`. -/
theorem communality_le_one (P : FactorParams p q)
    -- USER-INPUT: BKM's normalization y ∼ N_q(0, I); BKM Eq. (3.2)
    (hP : IsStandardized P)
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef)
    (i : Fin p)
    -- USER-INPUT: the observed variable `i` is standardized (Σ is a correlation matrix);
    -- BKM §3.4
    (hSig : factorCovariance P i i = 1) :
    communality P i ≤ 1 := by
  rw [← hSig]
  exact communality_le_variance P hP hΨ i

/-- The observed variance is the communality plus the specific variance, so the specific
variance is determined by the other two — the "communality problem" of `BKM` §3.12.1 in
equation form. -/
theorem specificVariance_eq_sub (P : FactorParams p q)
    -- USER-INPUT: BKM's normalization y ∼ N_q(0, I); BKM Eq. (3.2)
    (hP : IsStandardized P) (i : Fin p) :
    specificVariance P i = factorCovariance P i i - communality P i := by
  rw [variance_eq_communality_add_specificVariance P hP i]
  ring

end StatLean.StatisticalModels.FactorModels
