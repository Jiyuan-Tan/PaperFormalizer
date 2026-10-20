module
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Vanishing boundary terms on the whole line

The two forms of "the integral of a derivative over `ℝ` vanishes when the function dies at
both ends":

* `integral_deriv_eq_zero_of_tendsto_zero` — stated with `deriv f`, for a differentiable `f`;
* `integral_eq_zero_of_hasDerivAt_of_tendsto_zero` — stated with an explicitly supplied
  derivative `f'`, which is the form that arises when the derivative is computed by hand.

These are the boundary-term bricks for one-dimensional integration by parts: applied to a
product `f = u · v`, they turn `∫ u' v = − ∫ u v'` whenever the product vanishes at `±∞`,
which is exactly the mechanism by which the Stein identity for an exponential family drops
its boundary contributions.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.5
(Exponential Families), supporting material for Lemma 5.15 (Stein's identity): vanishing
boundary terms on the whole line. (`TPE2 §1.5 Lem 5.15`.)

**Proof formalization notes.**
* Both statements wrap `MeasureTheory.integral_of_hasDerivAt_of_tendsto`, the whole-line
  second fundamental theorem of calculus, which yields `∫ f' = n − m` for limits `m` at `-∞`
  and `n` at `+∞`; here `m = n = 0`. The `deriv` form additionally converts
  `Differentiable ℝ f` into the pointwise `HasDerivAt f (deriv f x) x` obligation.
* These are **not** subsumed by Mathlib's `integral_eq_zero_of_hasDerivAt_of_integrable`,
  which assumes `Integrable f`. Integrability of `f` is a different hypothesis from decay at
  both ends, and in the exponential-family application it is the decay that is available: the
  product of a polynomially bounded statistic with an exponentially decaying density tends to
  `0` at `±∞` without any global integrability of the product being established first.
* Integrability of the derivative stays an explicit hypothesis in both statements; without it
  the Bochner integral is junk-valued `0` and the conclusion, while accidentally true, would
  carry no content.

**Bibliographic comments.** The use of one-dimensional integration by parts with vanishing
boundary terms as a characterizing identity for a distribution — the technique these bricks
serve — is due to C. Stein ("Estimation of the mean of a multivariate normal distribution,"
*Ann. Statist.* **9** (1981), 1135–1151, §2).
-/

open MeasureTheory Filter Topology

namespace StatLean.PointEstimation

/-- If a differentiable function tends to `0` at both ends of the line and its derivative is
integrable, then the integral of the derivative vanishes. -/
theorem integral_deriv_eq_zero_of_tendsto_zero
    -- USER-INPUT: the function; genuine external data
    {f : ℝ → ℝ}
    -- USER-INPUT: differentiability everywhere; makes `deriv f` the honest derivative
    (hdiff : Differentiable ℝ f)
    -- USER-INPUT: integrability of the derivative; else `∫` is junk-valued `0`
    (hint : Integrable (deriv f))
    -- USER-INPUT: decay at `-∞`; the lower boundary term
    (hbot : Tendsto f atBot (𝓝 0))
    -- USER-INPUT: decay at `+∞`; the upper boundary term
    (htop : Tendsto f atTop (𝓝 0)) :
    ∫ (x : ℝ), deriv f x = 0 := by
  rw [integral_of_hasDerivAt_of_tendsto (fun x => (hdiff x).hasDerivAt) hint hbot htop]
  simp

/-- The explicit-derivative form: if `f` has derivative `f'` everywhere, `f'` is integrable
and `f` tends to `0` at both ends of the line, then `∫ f' = 0`. -/
theorem integral_eq_zero_of_hasDerivAt_of_tendsto_zero
    -- USER-INPUT: the function and its (hand-computed) derivative
    {f f' : ℝ → ℝ}
    -- USER-INPUT: `f'` is the derivative of `f` at every point
    (hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    -- USER-INPUT: integrability of the derivative; else `∫` is junk-valued `0`
    (hf' : Integrable f')
    -- USER-INPUT: decay at `-∞`; the lower boundary term
    (hbot : Tendsto f atBot (𝓝 0))
    -- USER-INPUT: decay at `+∞`; the upper boundary term
    (htop : Tendsto f atTop (𝓝 0)) :
    ∫ (x : ℝ), f' x = 0 := by
  rw [integral_of_hasDerivAt_of_tendsto hderiv hf' hbot htop]
  simp

end StatLean.PointEstimation
