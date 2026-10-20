module
public import StatLean.PointEstimation.UMVU.Defs
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-!
# The covariance characterization of minimum-variance unbiased estimation

Adding a multiple of an unbiased estimator of zero to an unbiased estimator keeps it
unbiased and changes its variance by `λ² var(U) + 2λ cov(δ, U)`, an expression that takes
negative values for some `λ` unless `cov(δ, U) = 0`. This makes orthogonality to the space of
unbiased estimators of zero both necessary and sufficient for minimum variance:

* `isUMVU_iff_uncorrelated_unbiasedZero` — a square-integrable unbiased estimator of `g` is
  UMVU exactly when it is uncorrelated, under every member of the model, with every
  square-integrable unbiased estimator of zero.

The same orthogonality condition is what makes a covariance-based lower bound on the variance
of unbiased estimators possible at all: the bound `var(δ) ≥ cov(δ, ψ)² / var(ψ)` is useful
only when its right-hand side does not depend on the particular unbiased estimator `δ`.

* `covariance_depends_only_on_mean_iff` — the covariance of an estimator with a fixed
  reference statistic `ψ` depends on the estimator only through its mean function exactly when
  `ψ` is uncorrelated with every square-integrable unbiased estimator of zero.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.1 (UMVU
Estimators), Theorem 1.7 (an estimator is UMVU iff it is uncorrelated with every unbiased
estimator of zero). (`TPE2 §2.1 Thm 1.7`.)

**Proof formalization notes.**
* Mathlib's covariance takes its two arguments before the measure,
  `ProbabilityTheory.covariance X Y μ`, and is symmetric; the arguments are written here in
  the order (estimator, unbiased estimator of zero) to match the classical display, but no
  statement depends on the order.
* The classical statement is phrased as `E_θ(δ U) = 0`; since `E_θ U = 0` this is the same as
  `cov_θ(δ, U) = 0`, and the covariance form is used here because it is the form Mathlib's
  bilinearity API (`covariance_sub_left`, `covariance_zero_left`) consumes directly.
* Both statements quantify over the estimator class `Δ` of square-integrable estimators
  (`MemEstL2`), exactly as the classical theorems do: outside `Δ` the variance-minimization
  problem is vacuous, and the sufficiency direction of the first theorem is proved by
  discarding competitors of infinite variance.
* The second theorem formalizes "`cov(δ, ψ)` depends on `δ` only through `g(θ)`" as: any two
  square-integrable estimators with the same mean function have the same covariance with `ψ`
  at every parameter. The reference statistic is allowed to depend on the parameter
  (`ψ : Θ → 𝓧 → ℝ`), as in the classical statement where `ψ = ψ(x, θ)`; only its value at the
  parameter at which the covariance is computed ever enters, so the added generality is free.
* The reference statistic is required square-integrable under every member, which is the
  classical "finite second moment" hypothesis; without it both covariances are junk.

**Bibliographic comments.** The covariance characterization of minimum-variance unbiased
estimators is due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and
unbiased estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236) and C. R. Rao
("Sufficient statistics and minimum variance estimates," *Proc. Camb. Phil. Soc.* **45**
(1949), 213–218), with the projection-theoretic account given by R. R. Bahadur ("On unbiased
estimates of uniformly minimum variance," *Sankhyā* **18** (1957), 211–224); the extension
beyond squared-error loss also originates there. The condition under which a covariance
inequality yields a genuine lower bound for all unbiased estimators is due to C. R. Blyth
("Necessary and sufficient conditions for inequalities of Cramér–Rao type," *Ann. Statist.*
**2** (1974), 464–473); the underlying inequality goes back to C. R. Rao ("Information and the
accuracy attainable in the estimation of statistical parameters," *Bull. Calcutta Math. Soc.*
**37** (1945), 81–91).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- A quadratic `2ct + vt²` (in `t`) with `v ≥ 0` that is nonnegative for every `t` forces
its linear coefficient to vanish: the minimizer `t = -c/(v+1)` gives a strictly negative value
unless `c = 0`. -/
private lemma cov_eq_zero_of_quadratic_nonneg {c v : ℝ}
    (h : ∀ t : ℝ, 0 ≤ 2 * c * t + t ^ 2 * v) (hv : 0 ≤ v) : c = 0 := by
  have hc2 : c ^ 2 ≤ 0 := by
    rcases eq_or_lt_of_le hv with rfl | hvpos
    · nlinarith [h (-c)]
    · have ht := h (-c / v)
      have e : 2 * c * (-c / v) + (-c / v) ^ 2 * v = -(c ^ 2) / v := by
        field_simp; ring
      rw [e] at ht
      have h2 := mul_nonneg ht hvpos.le
      rw [div_mul_cancel₀ _ hvpos.ne'] at h2
      linarith
  exact sq_eq_zero_iff.mp (le_antisymm hc2 (sq_nonneg c))

/-- **UMVU ⟺ uncorrelated with every unbiased estimator of zero.** A square-integrable
unbiased estimator of `g` has uniformly minimum variance among the square-integrable unbiased
estimators of `g` exactly when its covariance with every square-integrable unbiased estimator
of zero vanishes at every parameter. -/
theorem isUMVU_iff_uncorrelated_unbiasedZero (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (g : Θ → ℝ) {δ : 𝓧 → ℝ}
    -- USER-INPUT: the candidate estimator is unbiased for the estimand
    (hδu : IsUnbiased P g δ)
    -- USER-INPUT: the candidate estimator lies in the estimator class `Δ`
    (hδ2 : MemEstL2 P δ) :
    IsUMVU P g δ ↔
      ∀ U : 𝓧 → ℝ, IsUnbiasedZero P U → MemEstL2 P U → ∀ θ, covariance δ U (P θ) = 0 := by
  constructor
  · -- (⟹) perturb `δ` by `t·U`, minimize the resulting quadratic in `t`
    rintro ⟨-, -, hmin⟩ U hU hUL2 θ
    have key : ∀ t : ℝ,
        0 ≤ 2 * covariance δ U (P θ) * t + t ^ 2 * variance U (P θ) := by
      intro t
      have hδ'u : IsUnbiased P g (fun x => δ x + t * U x) := by
        intro θ'
        rw [integral_add ((hδ2 θ').integrable one_le_two)
            (((hUL2 θ').integrable one_le_two).const_mul t), integral_const_mul, hδu θ', hU θ']
        simp
      have hδ'2 : MemEstL2 P (fun x => δ x + t * U x) :=
        fun θ' => (hδ2 θ').add ((hUL2 θ').const_mul t)
      have hle := hmin _ hδ'u hδ'2 θ
      rw [variance_fun_add (hδ2 θ) ((hUL2 θ).const_mul t), covariance_const_mul_right t,
        variance_const_mul t U] at hle
      nlinarith [hle]
    exact cov_eq_zero_of_quadratic_nonneg key (variance_nonneg _ _)
  · -- (⟸) any competitor differs from `δ` by an unbiased estimator of zero
    intro hcorr
    refine ⟨hδu, hδ2, fun δ' hδ'u hδ'2 θ => ?_⟩
    have hUz : IsUnbiasedZero P (fun x => δ' x - δ x) := by
      intro θ'
      change ∫ x, (δ' x - δ x) ∂ P θ' = 0
      rw [integral_sub ((hδ'2 θ').integrable one_le_two) ((hδ2 θ').integrable one_le_two),
        hδ'u θ', hδu θ', sub_self]
    have hUL2 : MemEstL2 P (fun x => δ' x - δ x) := fun θ' => (hδ'2 θ').sub (hδ2 θ')
    have hcov0 := hcorr _ hUz hUL2 θ
    have hvar : variance δ' (P θ)
        = variance δ (P θ) + 2 * covariance δ (fun x => δ' x - δ x) (P θ)
          + variance (fun x => δ' x - δ x) (P θ) := by
      rw [← variance_fun_add (hδ2 θ) (hUL2 θ)]
      exact variance_congr (Filter.Eventually.of_forall fun x => by ring)
    rw [hvar, hcov0]
    linarith [variance_nonneg (fun x => δ' x - δ x) (P θ)]

/-- **When does a covariance bound apply to all unbiased estimators?** The covariance of an
estimator with a fixed reference statistic `ψ` is determined by the estimator's mean function
alone exactly when `ψ` is uncorrelated with every square-integrable unbiased estimator of
zero. This is the condition under which `var(δ) ≥ cov(δ, ψ)² / var(ψ)` becomes a bound valid
for every unbiased estimator of a given estimand. -/
theorem covariance_depends_only_on_mean_iff (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (ψ : Θ → 𝓧 → ℝ)
    -- USER-INPUT: the reference statistic has a finite second moment under every member
    (hψ : ∀ θ, MemLp (ψ θ) 2 (P θ)) :
    (∀ δ₁ δ₂ : 𝓧 → ℝ, MemEstL2 P δ₁ → MemEstL2 P δ₂ →
        (∀ θ, ∫ x, δ₁ x ∂(P θ) = ∫ x, δ₂ x ∂(P θ)) →
        ∀ θ, covariance δ₁ (ψ θ) (P θ) = covariance δ₂ (ψ θ) (P θ)) ↔
      ∀ U : 𝓧 → ℝ, IsUnbiasedZero P U → MemEstL2 P U → ∀ θ, covariance U (ψ θ) (P θ) = 0 := by
  constructor
  · -- (⟹) apply the mean-invariance to `U` and the zero estimator
    intro hdep U hU hUL2 θ
    have hmean : ∀ θ', ∫ x, U x ∂(P θ') = ∫ x, (fun _ => (0 : ℝ)) x ∂(P θ') := by
      intro θ'; rw [hU θ']; simp
    have h := hdep U (fun _ => 0) hUL2 (fun _ => memLp_const 0) hmean θ
    rwa [covariance_const_left] at h
  · -- (⟸) two estimators with the same mean differ by an unbiased estimator of zero
    intro huncorr δ₁ δ₂ h1 h2 hmean θ
    have hUz : IsUnbiasedZero P (fun x => δ₁ x - δ₂ x) := by
      intro θ'
      change ∫ x, (δ₁ x - δ₂ x) ∂ P θ' = 0
      rw [integral_sub ((h1 θ').integrable one_le_two) ((h2 θ').integrable one_le_two),
        hmean θ', sub_self]
    have hc := huncorr _ hUz (fun θ' => (h1 θ').sub (h2 θ')) θ
    rw [covariance_fun_sub_left (h1 θ) (h2 θ) (hψ θ)] at hc
    linarith

end StatLean.PointEstimation
