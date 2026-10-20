module
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Measurement error — attenuation of the regression slope (exact)

**C7.** The classical errors-in-variables identity: with true covariate `X`, measurement
error `U` and response noise `ε` pairwise independent, observing `W = X + U` and
`Y = α + β·X + ε`, the population least-squares slope of `Y` on `W` is the true slope
attenuated by the reliability ratio:
$$\frac{\operatorname{cov}(Y, W)}{\operatorname{Var} W}
  = \beta\,\frac{\sigma_X^2}{\sigma_X^2 + \sigma_U^2}.$$
This is the canonical **non-ignorable** coarsening example — contrast the ignorable
mechanisms of `Coarsening.IPW`/`Coarsening.Ignorability`: here the observation channel biases
the naive analysis by an explicit, exactly computable factor.

**Reference.** W. A. Fuller, *Measurement Error Models*, Wiley, 1987, §1.1 (the attenuation
identity) (verify §) (`Fuller §1.1`).

**Proof formalization notes.** Pure covariance bilinearity: `cov(Y, W) = β·Var X` because
all cross terms vanish by pairwise independence, and `Var W = Var X + Var U` likewise.
*Book vs Lean:* the book states the identity under `E U = E ε = 0`; the covariance
formulation is automatically centered, so **no mean-zero hypotheses are needed** — a strict
strengthening. `MemLp 2` moment hypotheses are USER-INPUT: Mathlib's `covariance` junk-values
to `0` without them and the identities would be vacuous, not false.

**Bibliographic comments.** Attenuation ("regression dilution") goes back to C. Spearman,
"The proof and measurement of association between two things," *Amer. J. Psychol.* **15**
(1904), 72–101; the modern structural treatment is Fuller (1987).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels.Coarsening

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cross-covariance kill: the response built from `X` and `ε` is uncorrelated with the
measurement error `U` (Fuller §1.1 (verify §)). -/
theorem covariance_response_error (X U ε : Ω → ℝ) (α β : ℝ) [IsProbabilityMeasure μ]
    -- USER-INPUT: second moments; Fuller §1.1
    (hX : MemLp X 2 μ) (hU : MemLp U 2 μ) (hε : MemLp ε 2 μ)
    -- USER-INPUT: pairwise independence of the structural components; Fuller §1.1
    (hXU : IndepFun X U μ) (hεU : IndepFun ε U μ) :
    cov[fun ω => α + β * X ω + ε ω, U; μ] = 0 := by
  have hβX : MemLp (fun ω => β * X ω) 2 μ := hX.const_mul β
  have hβXi : Integrable (fun ω => β * X ω) μ := hβX.integrable one_le_two
  have h1 : MemLp (fun ω => α + β * X ω) 2 μ := (memLp_const α).add hβX
  rw [show (fun ω => α + β * X ω + ε ω) = (fun ω => α + β * X ω) + ε from rfl,
    covariance_add_left h1 hε hU, covariance_const_add_left hβXi α,
    covariance_const_mul_left, hXU.covariance_eq_zero hX hU,
    hεU.covariance_eq_zero hε hU]
  ring

/-- Covariance of the response with the mismeasured covariate: `cov(Y, W) = β·Var X`
(Fuller §1.1). -/
theorem covariance_response_observed (X U ε : Ω → ℝ) (α β : ℝ) [IsProbabilityMeasure μ]
    -- USER-INPUT: second moments; Fuller §1.1
    (hX : MemLp X 2 μ) (hU : MemLp U 2 μ) (hε : MemLp ε 2 μ)
    -- USER-INPUT: pairwise independence; Fuller §1.1
    (hXU : IndepFun X U μ) (hεX : IndepFun ε X μ) (hεU : IndepFun ε U μ) :
    cov[fun ω => α + β * X ω + ε ω, fun ω => X ω + U ω; μ] = β * Var[X; μ] := by
  have hβX : MemLp (fun ω => β * X ω) 2 μ := hX.const_mul β
  have hβXi : Integrable (fun ω => β * X ω) μ := hβX.integrable one_le_two
  have h1 : MemLp (fun ω => α + β * X ω) 2 μ := (memLp_const α).add hβX
  have e1 : cov[fun ω => α + β * X ω, X; μ] = β * Var[X; μ] := by
    rw [covariance_const_add_left hβXi α, covariance_const_mul_left,
      covariance_self hX.aestronglyMeasurable.aemeasurable]
  have e2 : cov[fun ω => α + β * X ω, U; μ] = 0 := by
    rw [covariance_const_add_left hβXi α, covariance_const_mul_left,
      hXU.covariance_eq_zero hX hU, mul_zero]
  rw [show (fun ω => α + β * X ω + ε ω) = (fun ω => α + β * X ω) + ε from rfl,
    show (fun ω => X ω + U ω) = X + U from rfl,
    covariance_add_left h1 hε (hX.add hU), covariance_add_right h1 hX hU,
    covariance_add_right hε hX hU, e1, e2, hεX.covariance_eq_zero hε hX,
    hεU.covariance_eq_zero hε hU]
  ring

/-- Variance of the mismeasured covariate: `Var W = Var X + Var U` (Fuller §1.1). -/
theorem variance_observed (X U : Ω → ℝ) [IsProbabilityMeasure μ]
    -- USER-INPUT: second moments; Fuller §1.1
    (hX : MemLp X 2 μ) (hU : MemLp U 2 μ)
    -- USER-INPUT: independence of covariate and measurement error; Fuller §1.1
    (hXU : IndepFun X U μ) :
    Var[fun ω => X ω + U ω; μ] = Var[X; μ] + Var[U; μ] :=
  hXU.variance_fun_add hX hU

-- `hV` (nondegeneracy) turns out to be unnecessary: Mathlib's division junk-values to `0`, so
-- both sides collapse to `0` in the degenerate case. The hypothesis is kept as stated (Fuller
-- §1.1 assumes it); the proof simply does not consume it.
set_option linter.unusedVariables false in
/-- **C7, slope attenuation** (`Fuller §1.1`; Spearman 1904): the population regression slope
of `Y` on the mismeasured `W` is the true slope times the reliability ratio. -/
theorem attenuation (X U ε : Ω → ℝ) (α β : ℝ) [IsProbabilityMeasure μ]
    -- USER-INPUT: second moments; Fuller §1.1
    (hX : MemLp X 2 μ) (hU : MemLp U 2 μ) (hε : MemLp ε 2 μ)
    -- USER-INPUT: pairwise independence; Fuller §1.1
    (hXU : IndepFun X U μ) (hεX : IndepFun ε X μ) (hεU : IndepFun ε U μ)
    -- USER-INPUT: the observed covariate is nondegenerate; Fuller §1.1
    (hV : Var[X; μ] + Var[U; μ] ≠ 0) :
    cov[fun ω => α + β * X ω + ε ω, fun ω => X ω + U ω; μ]
        / Var[fun ω => X ω + U ω; μ]
      = β * (Var[X; μ] / (Var[X; μ] + Var[U; μ])) := by
  rw [covariance_response_observed X U ε α β hX hU hε hXU hεX hεU,
    variance_observed X U hX hU hXU, mul_div_assoc]

end StatLean.StatisticalModels.Coarsening
