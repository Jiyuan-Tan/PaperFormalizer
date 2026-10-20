module
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
Pointwise convergence of the characteristic function of `gaussianReal 0 v`
in the variance parameter.

This is the analytic input to the Lévy continuity step in the LAM proof:
as a sequence of variances `v_m : ℕ → ℝ≥0` converges (in `ℝ`) to a target
`v_inf : ℝ`, the characteristic function of `gaussianReal 0 v_m`
converges pointwise (in `t`) to that of `gaussianReal 0 ⟨v_inf, _⟩`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998),
§25.3, in the proof of thm 25.21 (the `m → ∞` Gaussian-integral pass).
The Mathlib char-fn formula is `ProbabilityTheory.charFun_gaussianReal`:
`charFun (gaussianReal μ v) t = exp (t·μ·I − v·t²/2)`. Pointwise
continuity in `v` is then continuity of `v ↦ exp (− v · t² / 2)`
composed with the cast `ℝ≥0 → ℝ → ℂ`.
-/

open Filter Topology Complex MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.GaussianVarCharFn

/-- *Pointwise variance-continuity of the Gaussian characteristic function.*

Let `v : ℕ → ℝ≥0` be a sequence of variances whose real coercion converges
to `v_inf : ℝ` (necessarily `0 ≤ v_inf`). Then for every `t : ℝ`, the
characteristic function `charFun (gaussianReal 0 (v m)) t` converges in
`ℂ` to `charFun (gaussianReal 0 ⟨v_inf, h_inf_nn⟩) t`.

The proof rewrites both sides via Mathlib's `charFun_gaussianReal`
formula `charFun (gaussianReal μ v) t = exp (t·μ·I − v·t²/2)` (here
`μ = 0`, so the formula collapses to `exp (− v · t² / 2)`) and then
applies continuity of `z ↦ exp (− z · t² / 2)` composed with the real
coercion of `v`.

Used by `AsymptoticStatistics.LowerBounds.LAM` as the analytic input to
the Lévy-continuity step that passes `∫⁻ (ℓ ⊓ M) dN(0, v_m)` to
`∫⁻ (ℓ ⊓ M) dN(0, v_inf)` in the proof of thm 25.21. -/
theorem gaussian_variance_charFn_tendsto
    {v : ℕ → ℝ≥0} {v_inf : ℝ}
    (h_inf_nn : 0 ≤ v_inf)
    (hv : Tendsto (fun m => (v m : ℝ)) atTop (𝓝 v_inf)) (t : ℝ) :
    Tendsto
      (fun m => charFun (gaussianReal 0 (v m)) t) atTop
      (𝓝 (charFun (gaussianReal 0 ⟨v_inf, h_inf_nn⟩) t)) := by
  -- Rewrite both sides via the explicit char-fn formula:
  --   `charFun (gaussianReal 0 v) t = cexp (t·0·I − v·t²/2) = cexp (−v·t²/2)`.
  set w : ℝ≥0 := ⟨v_inf, h_inf_nn⟩ with hw
  simp_rw [charFun_gaussianReal]
  -- Reduced goal:
  --   Tendsto (fun m => cexp (t·0·I − ((v m : ℝ≥0) : ℂ) · t² / 2)) atTop
  --           (𝓝 (cexp (t·0·I − ((⟨v_inf,_⟩ : ℝ≥0) : ℂ) · t² / 2))).
  -- Composition of `Continuous (fun z : ℂ => cexp (t·0·I − z · t² / 2))` with
  -- the cast tendsto `((v m : ℝ≥0) : ℂ) → ((⟨v_inf,_⟩ : ℝ≥0) : ℂ)`.
  have h_cast : Tendsto (fun m => ((v m : ℝ≥0) : ℂ)) atTop
      (𝓝 ((⟨v_inf, h_inf_nn⟩ : ℝ≥0) : ℂ)) := by
    -- `((v m : ℝ≥0) : ℂ) = (((v m : ℝ≥0) : ℝ) : ℂ)`; chain `ℝ → ℂ` continuity
    -- with `hv`.
    have h_real : Tendsto (fun m => ((v m : ℝ≥0) : ℝ)) atTop (𝓝 v_inf) := hv
    have h_to_C : Tendsto (fun m => ((((v m : ℝ≥0) : ℝ)) : ℂ)) atTop
        (𝓝 ((v_inf : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp h_real
    -- The two sequences `((v m : ℝ≥0) : ℂ)` and `(((v m : ℝ≥0) : ℝ) : ℂ)`
    -- are equal pointwise (defeq); same for the limits.
    have h_eq_seq : (fun m => ((v m : ℝ≥0) : ℂ))
        = fun m => ((((v m : ℝ≥0) : ℝ)) : ℂ) := by
      funext m
      rfl
    have h_eq_lim : (((⟨v_inf, h_inf_nn⟩ : ℝ≥0) : ℂ) : ℂ) = ((v_inf : ℝ) : ℂ) := rfl
    rw [h_eq_seq, show ((⟨v_inf, h_inf_nn⟩ : ℝ≥0) : ℂ) = ((v_inf : ℝ) : ℂ) from
      h_eq_lim]
    exact h_to_C
  -- Compose with continuity of `z ↦ cexp (t·0·I − z·t²/2)`.
  have h_cont : Continuous fun z : ℂ =>
      Complex.exp ((t : ℂ) * (0 : ℂ) * Complex.I - z * (t : ℂ) ^ 2 / 2) := by
    fun_prop
  exact (h_cont.tendsto _).comp h_cast

end AsymptoticStatistics.ForMathlib.GaussianVarCharFn
