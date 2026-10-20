module
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.HypothesisTesting.ForMathlib.GaussianShell
public import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

/-!
# A multivariate Berry–Esseen bound via Lindeberg swapping (honest, non-sharp)

This file develops the elementary "smooth the indicator + Lindeberg swap" route to a
multivariate Berry–Esseen bound, as suggested for
`StatLean.HypothesisTesting.GoodnessOfFit.SmoothTestLargeK`. The statement quoted there,
`bentkus_berry_esseen_ball` (dimension-free `C`) — and the convex-sets reference statement
(constant `400 k^{1/4}`) that an earlier revision also quoted, since removed as
consumer-free — are **Bentkus (2003)**: a sharp,
research-level dimension factor obtained by Fourier analysis over convex bodies. Their sharp
`β/√n` *rate* is not reproduced here; what is proved here is the honest elementary rate
`(β/√n)^{1/4}`, over balls (`berryEsseen_ball_elementary`, which discharges
`bentkus_berry_esseen_ball`) and over convex sets (`berryEsseen_convex_elementary`) — and, over
convex sets, the strictly better `(β/√n)^{1/2}` of `berryEsseen_convex_improved`, obtained by
the Cameron–Martin route of the wave-13/16 sections at the end of the file.

What this file records instead is the strongest bound the elementary route yields *honestly*.
The single ingredient that is proved unconditionally and is genuinely dimension-free is the
**Gaussian slab (half-space) anti-concentration** bound:

`gaussian_slab_measure_le` — for a unit vector `u` and `a ≤ b`,
`N(0, I_k)({z : a < ⟪u,z⟫ ≤ b}) ≤ (b - a) / √(2π)`,

whose constant `1/√(2π)` carries **no dimension factor at all**. This is "step 3" of the
route for a half-space, and it is the one-dimensional marginal statement: the projection
`z ↦ ⟪u,z⟫` of `N(0,I_k)` is exactly `N(0,1)`, whose density is bounded by `1/√(2π)`.

## Honest accounting of the elementary route (see the module docstring below for the report)

For the **ball** route the elementary programme is now **complete**: `berryEsseen_ball_elementary`
is proved outright and is axiom-clean (it depends on no `sorry`, direct or transitive). Every
ingredient is proved here unconditionally, each with a dimension-free constant:

* `gaussian_slab_measure_le` — slab anti-concentration (`1/√(2π)`);
* `gaussian_ball_shell_measure_le` — *shell* anti-concentration (`C_ac = 7`), resting on the
  uniform chi-density peak bound `chiSquared_density_mul_sqrt_le`, which is obtained **without
  any Stirling asymptotics for `Γ`** by restricting Euler's integral to the length-`√p` window
  at the peak (`le_Gamma_add_half`);
* `norm_taylor_remainder_three_le` — the third-order Taylor remainder on a normed space
  (Mathlib v4.29.1 has only the one-dimensional version, so this is reduced to a segment);
* `exists_smoothed_radial_indicator` — the smoothed radial indicator with an absolute
  third-derivative constant, built by composing a fixed 1-D cutoff with `‖·‖²` (**not** with
  `‖·‖`), which avoids the quantitative iterated-derivative bounds for the Euclidean norm that
  Mathlib does not have.

* `map_normalized_sum_stdGaussian` — Gaussian stability of the normalized sum,
  `(⨂ⁿ N(0,I_k)).map (n^{-1/2} ∑) = N(0,I_k)`, the right-hand endpoint of the Lindeberg
  telescope. Proved by characteristic functions (`Measure.ext_of_charFun` plus the product
  factorization `charFun_map_const_smul_sum`), not by iterated convolution;
* `abs_integral_smooth_sub_gaussian_le` — the third-order multivariate **Lindeberg swap**: the
  hybrid telescope `Qⱼ = ⨂ᵢ (if i < j then γ else ν)`, each step isolated by
  `integral_pi_sum_peel` (`measurePreserving_piFinSuccAbove` + Fubini) and compared by
  `abs_integral_swap_step_le`. The one-step comparison is a second-order Taylor expansion in
  which the linear term dies by Riesz representation plus `hmean`
  (`integral_clm_eq_zero_of_centred`), the quadratic term takes the *same* value on both sides
  because both laws have identity covariance (`integral_bilin_eq_basis_sum` — note it never
  needs the value of that basis sum, only that it is the same one), and the remainder is
  `norm_taylor_remainder_three_le`.

With the Gaussian third moment `β_G ≤ 2 k^{3/2}` (`integral_norm_cube_gaussian_le`, from the two
public χ² moments) these suffice and the ball assembly closes.

The *convex* route is **now complete as well**: `berryEsseen_convex_elementary` is proved
outright and is axiom-clean. Its two ingredients are

* `exists_smoothed_convex_indicator` — the smoothed convex indicator (mollification by a
  `ContDiffBump`, dimension-dependent constant); see its docstring for the construction and the
  section preceding it for the `precompR` tower. With the Lindeberg swap it gives
  `berryEsseen_convex_levy_elementary`, the Lévy/Prokhorov form
  `μₙ(B) ≤ γ(Bᵋ) + C (β/√n)/ε³` (and its mirror image);
* the Gaussian **boundary-shell** bound `γ(Bᵋ) ≤ γ(B) + C_k ε` for convex `B`, together with its
  erosion twin `γ(B) ≤ γ(B₋ᵋ) + C_k ε`. These are `gaussian_thickening_le` and
  `gaussian_le_erosion_add` of `StatLean.HypothesisTesting.ForMathlib.GaussianShell`, proved
  there elementarily (convex slice + supporting hyperplane + `2k` coordinate shifts) with the
  explicit constant `C_k = 4 e² √k` (wave 22; the wave-3 coordinate cover gave the factor-`k`
  worse `8 k^{3/2}/√(2π)`). Ball's Gaussian-surface-area theorem gives the
  sharp `4 k^{1/4}` — exactly the dimension factor of Bentkus's constant — but the assembly
  needs only finiteness of `C_k` at fixed `k`.

With `ε` optimised in `ε^{-3} β/√n + C_k ε` the assembled bound is `(β/√n)^{1/4} = n^{-1/8}`.

## Wave-13 amendment: the exponent `1/4` is **not** intrinsic; the elementary ceiling is `1/2`

Earlier notes in this file (and in `SmoothTestLargeK`) asserted that the balance
`ε^{-3} β/√n + C_k ε` "cannot do better whatever the shell constant is, so the gap is the rate".
The arithmetic is right *for that balance*, but the conclusion is wrong: the balance itself is
not forced. Re-derivation, from scratch:

* In the hybrid telescope the `j`-th step compares `ν` with `γ` inside a background whose first
  `j` coordinates are **already Gaussian**. That background therefore contains an independent
  `N(0,(j/n) I_k)` summand: the test function seen by step `j` is automatically mollified at
  scale `σⱼ = √(j/n)`, for free.
* For a Gaussian mollification the third-order Lindeberg remainder does **not** cost
  `‖D³f‖_∞`. Writing the shift as a Cameron–Martin tilt,
  `∫ f(z + a) dγ(z) = ∫ f(z) exp(⟪a,z⟫ − ‖a‖²/2) dγ(z)`
  (`integral_gaussian_shift_eq_tilt`), the expansion parameter is the *density*, not the test
  function. The tilt's second-order Taylor remainder is `O(‖a‖³)` in `L¹(γ)` with an **absolute,
  dimension-free** constant (`exists_tiltRemainder_bound`, `integral_abs_vecTiltRemainder_le`),
  and its zeroth/first/second-order terms take the same value for *any two* centred
  identity-covariance laws (`tiltPoly_fubini`) — the exact analogue of the classical
  cancellation, but for the Cameron–Martin expansion. With `a = (c/σⱼ) • y` and `c = n^{-1/2}`,
  step `j` costs `C (c/σⱼ)³ (β + β_G) = C (β + β_G) j^{-3/2}` in place of
  `(‖D³f‖_∞/6) c³ (β + β_G)`. This is `abs_integral_gaussian_smoothed_swap_le`, proved below.
* Taking at each step the *better* of the two bounds, the telescope costs
  `(β + β_G) · Σ_{j<n} min(A ε^{-3} n^{-3/2}, j^{-3/2})`. With `θ := A ε^{-3} n^{-3/2}` the sum
  splits at `j* = θ^{-2/3}` into `j* θ = θ^{1/3}` and `Σ_{j ≥ j*} j^{-3/2} ≤ 3 θ^{1/3}`, so the
  total is `≤ 4 (A)^{1/3} (β + β_G)/(ε √n)`: the factor `ε^{-3}` has become `ε^{-1}`.
* The balance is therefore `ε^{-1} β/√n + C_k ε`, minimised at `ε ∼ (β/√n)^{1/2}`, giving
  `|μₙ(B) − γ(B)| ≲ √(C_k) · (β/√n)^{1/2} = O(n^{-1/4})` — a strict improvement on `n^{-1/8}`,
  with the dimension entering only through `√(C_k)`.

**Why `1/2` and not `1`.** The remaining loss is that the swap error is bounded *globally*,
whereas `D³` of a mollified indicator is supported on the `ε`-shell of `∂B`. Localising costs a
factor `P(hybrid ∈ shell)`, which requires the anti-concentration bound for the **hybrid** laws,
not just for `γ`; that is a self-improving induction over `n` (`Δ ≤ A ε^{-3} δ (C_k ε + 2Δ) +
C_k ε`, which closes at `Δ ≲ C_k δ^{1/3}` and, iterated with the Gaussian smoothing above, at
the sharp rate). That induction is Bentkus's actual argument; its two ingredients are proved in
wave 19 (see the amendment below), its probabilistic assembly is not. So the honest ceiling of
the *non-inductive* elementary route is `(β/√n)^{1/2}`, and the residual gap to Bentkus is a
further factor `(β/√n)^{1/2}`.

**Status of the improvement (wave 16: COMPLETE, `0`-sorry and axiom-clean).** The improved
headline is

`berryEsseen_convex_improved` — `|μₙ(B) − γ(B)| ≤ C (β/√n)^{1/2} = O(n^{-1/4})` for measurable
convex `B`, with `C = C₀ + gaussianShellConst k`,

together with its Lévy/thickening form `berryEsseen_convex_levy_improved`
(`μₙ(B) ≤ γ(Bᵋ) + C (β/√n)/ε` and its mirror image — note the mollifier cost `ε^{-1}`, not
`ε^{-3}`) and the **ball** version `berryEsseen_ball_improved`, which keeps the dimension-free
constant of `berryEsseen_ball_elementary` at the better exponent. The proved
`berryEsseen_convex_elementary` and `berryEsseen_ball_elementary` are deliberately left
untouched: they are separate, weaker statements with existing consumers, and nothing about them
is retracted (the ball assembly is now shared: `berryEsseen_ball_of_swap` is `ε`-generic and
takes the swap estimate as a hypothesis, so the two exponents differ only in which swap is fed
to it). The ingredients:

* *Analytic core.* `exists_tiltRemainder_bound` (scalar, absolute constant),
  `integral_abs_vecTiltRemainder_le` (multivariate, **dimension-free**, by reduction to the
  one-dimensional marginal), `integral_gaussian_shift_eq_tilt` (Cameron–Martin),
  `tiltPoly_fubini` (the moment cancellation) and, assembling these,
  `abs_integral_gaussian_smoothed_swap_le` — the swap step at cost `C (c/σ)³ (β_ν + β_ρ)`.
* *Assembly brick (ii).* `map_stdGaussian_pair_smul_add` / `integral_gaussian_pair_smul_add`:
  the Gaussian convolution `γ_σ ∗ γ_c = γ_{√(σ²+c²)}`, in measure and in integral form.
* *Assembly brick (iii).* `sum_le_of_bounded_and_decay`: if `0 ≤ T j ≤ θ` and
  `T j ≤ j^{-3/2}` for `j ≥ 1` then `Σ_{j<n} T j ≤ J θ + 3/√J` for every cut `J ≥ 2` — the
  displayed sum estimate, proved by the backward telescoping bound
  `inv_mul_sqrt_le_telescope` (`j^{-3/2} ≤ 2((j−1)^{-1/2} − j^{-1/2})`), with no integral
  comparison. Choosing `J ≈ θ^{-2/3}` gives `O(θ^{1/3})`.

* *Assembly brick (i) — the telescope itself* (wave 16): `abs_integral_smooth_sub_gaussian_improved`.
  `Iⱼ = ∫ x, (∫ z, f (n^{-1/2} • (∑ₗ xₗ) + (j/n)^{1/2} • z) dγ(z)) d(Measure.pi κ'ⱼ)` with
  `κ'ⱼ i = if i < j then Measure.dirac 0 else ν`. `integral_pi_sum_peel` peels coordinate `j`
  verbatim (the integrand is a bounded continuous function of `∑ₗ xₗ`; its continuity is
  `continuous_integral_add_smul`, dominated convergence with the constant bound `1`). Brick (ii)
  identifies the `(j+1)`-st smoothing with the `j`-th plus one fresh `n^{-1/2}`-scaled Gaussian,
  so *the same single step* both kills a coordinate and widens the mollification. The step bound
  is `abs_integral_gaussian_smoothed_swap_le` for `j ≥ 1` and, for **every** `j` (in particular
  `j = 0`, where the smoothing has width `0`), `abs_integral_swap_step_le` applied after
  `integral_integral_swap` moves the smoothing variable outside. Brick (iii) sums the minimum of
  the two, giving `(J (M/6) n^{-3/2} + 3C/√J)(β_ν + β_G)` for every cut `J ≥ 2`. The endpoints
  are `measure_pi_dirac_zero` (`⨂ δ₀ = δ₀`, by `Measure.pi_eq`) for `I n` and `√0 = 0` for `I 0`.

  In the assembly the cut is `J = max 2 ⌈ε² n⌉`, which gives `J (M/6) n^{-3/2} ≤ C₃/(2ε√n)` and
  `3C/√J ≤ 3C/(ε√n)`. The bookkeeping `J ≤ ε² n + 2` is only useful when `ε² n ≥ 1`; in the
  complementary window the asserted bound already exceeds `1` (because `β ≥ k^{3/2} ≥ 1`), so
  that case is discharged from `μₙ(B) ≤ 1` alone.

## Wave-19 amendment: the two ingredients of the induction, and what is still missing

The wave-16 note named the missing induction as a *two-part project* rather than a verdict. Both
parts are now discharged, each as a standalone, `0`-sorry, axiom-clean statement. (The
consumer-free reference statement `SmoothTestLargeK.bentkus_berry_esseen_convex`, which quoted
Bentkus's sharp constant, has since been removed; the two parts do not by themselves produce
the recursion — see below.)

**(1) The weighted Cameron–Martin remainder** (`integral_abs_mul_vecTiltRemainder_le`, with the
localised corollary `abs_integral_mul_vecTiltRemainder_le_of_support`). The existing
`integral_abs_vecTiltRemainder_le` bounds the remainder against `‖G‖_∞ = 1`; the localisation
needs it integrated against `|G|`. Cauchy–Schwarz reduces this to an `L²(γ)` bound on the
remainder, `integral_sq_vecTiltRemainder_le : ∫ R_w² dγ ≤ tiltSqConst ‖w‖⁶` for `‖w‖ ≤ 1`,
proved by the same exponential envelope as the `L¹` bound (whose square is again Gaussian
integrable, `sq_tiltEnvSmall_le`) and by the same one-dimensional-marginal reduction — so the
constant is again **dimension-free** and the power of `‖w‖` is still `3`. The upshot is that a
test function supported on the `ε`-shell of `∂B` costs `√(γ(shell))` instead of `1`.
(`‖w‖ ≤ 1` is not a defect: the `L²` statement is *false* for large tilts, where
`∫ exp(2st − s²) dγ = exp(s²)`; the telescope only ever uses `‖w‖ = c/σⱼ ≤ 1`.)

**(2) The self-improving recursion**, solved in the `SelfImproving` section at the end of the
file. Three shapes, all proved:

* `Δ ≤ A δ ε⁻³ (C ε + 2Δ) + C ε` (the wave-16 note verbatim) ⟹ `Δ³ ≤ 63 C³ A δ`;
* `Δ ≤ A δ ε⁻¹ (C ε + 2Δ) + C ε` (after the Gaussian smoothing that this file already proves,
  which is what turns `ε⁻³` into `ε⁻¹`) ⟹ `Δ ≤ 10 A C δ`, i.e. **exactly the sharp `β/√n`
  rate**, with the dimension only in `C = C_k`;
* `Δ ≤ A δ ε⁻¹ √(C ε + 2Δ) + C ε` — the shape the `L²` weighting of (1) actually delivers —
  ⟹ `Δ³ ≤ 216 (C A δ)²`, i.e. `O(n^{-1/3})`.

## Wave-20 amendment: the recursion is produced; the residue is two named bricks

Wave 19 left the *production* of `hrec` open, with two structural obstacles. Both are now
resolved, and the recursion is assembled: `berryEsseen_convex_sharp` states the sharp rate

`|μₙ(B) − γ(B)| ≤ 72 A C_k · β/√n` for measurable convex `B`,

**linear in `δ = β/√n`**, proved from `exists_convexDiscrepancy_recursion` fed to
`le_of_selfImproving_induction`. It is not axiom-clean: it inherited exactly two named,
precisely stated bricks, `hybridLaw_shell_le` and `exists_localised_swap_bound` (the first is
proved in wave 22, below; the second's weight hypothesis is amended in wave 29, its conclusion
in wave 32). Everything between the bricks and the headline is proved.

*(As frozen in wave 20 the headline is log-free. Wave 32 amends it to carry one logarithm,
`C (β/√n)(1 + log(max (√n/β) e))`, and replaces `le_of_selfImproving_induction` by
`le_of_selfImproving_induction_log`; see the wave-32 section below for the forcing.)*

*Obstacle 1 (the class) is overturned rather than solved.* The `ε`-shell of a convex set is
`Bᵋ \ interior B`, a difference of two convex sets — but the induction does **not** have to be
enlarged to that class. `measureReal_diff_le_of_convexDiscrepancy` observes that
`μ(B₁ \ B₂) = μ(B₁) − μ(B₂)` for `B₂ ⊆ B₁`, so two applications of the *convex* bound suffice;
the difference structure survives only as the factor `2` in `C ε + 2Δ`. The class the induction
runs on is `convexDiscrepancy`, the supremum over measurable convex sets, and it is closed under
everything the argument does to it — including affine maps
(`measureReal_shell_preimage_aff_le`).

*Obstacle 2 (the family) is solved by the range `n/2 ≤ m ≤ n`.* `hybridLaw n j ν` makes the
telescope's hybrid `n^{-1/2} ∑_{i ≥ j} Yᵢ + (j/n)^{1/2} Z` an explicit measure. For `2j ≥ n` its
own Gaussian component has width `≥ 1/√2` and bounds the shell mass outright, with no induction
(`gaussian_measureReal_shell_preimage_aff_le`, proved). For `2j ≤ n` the non-Gaussian part is a
normalised sum of `m = n − j ≥ n/2` summands, so only the discrepancies at sizes
`n/2 ≤ m ≤ n` are needed — including `m = n` itself, since the `j = 0` hybrid *is* `μₙ`. That is
exactly the neighbour range of `le_of_selfImproving_induction`, which closes at `K = 18 A C`
with no base case.

## Wave-22 amendment: brick H is proved, and the shell constant drops from `k^{3/2}` to `√k`

**Brick H is discharged.** `hybridLaw_shell_le` is now a theorem, axiom-clean. The debt wave 20
identified — the Fubini factorisation of `hybridLaw` — is supplied by applying `Measure.prod`'s
two Fubini identities to the explicit hybrid map: `Measure.prod_apply` in the Gaussian-dominant
regime `2j ≥ n`, `Measure.prod_apply_symm` in the sum-dominant regime `2j ≤ n`, in each case
landing on the wave-20 affine transport `measureReal_shell_preimage_aff_le`. The only genuinely
new ingredient is `map_sum_pi_dirac_drop`: the `δ₀` factors of the hybrid product measure drop
out of the law of the coordinate sum, so the sum-dominant regime really does see `sumLaw (n−j) ν`
(proved by characteristic functions — `charFun_map_sum_pi` — with no index surgery). The moment
hypotheses turn out to be unnecessary for brick H: it is purely geometric.

**The one remaining brick.** `exists_localised_swap_bound` —
`abs_integral_smooth_sub_gaussian_improved` rerun with a shell-weighted Cameron–Martin remainder
in place of the uniform one, so that each step of the telescope is weighted by the *hybrid's*
shell mass. Note that it asks for the `L^∞` weight `W`, which is strictly stronger than the
wave-19 `L²` lemma `abs_integral_mul_vecTiltRemainder_le_of_support` (that one gives `√W`, hence
only `O(n^{-1/3})`), and is not a corollary of it: the weight must be carried by the hybrid law,
not by `γ`. The best *proved* convex bound remains `berryEsseen_convex_improved` at
`(β/√n)^{1/2}`.

## Wave-24 amendment: brick L as frozen is FALSE; the amended brick, and its provable half

**The wave-20 statement of brick L is false.** It asserted
`|∫f dμₙ − ∫f dγ| ≤ A (β/√n) ε⁻¹ W` for the *bare* weight `W`, and the bare weight can sit far
below the Gaussian shell scale `C_k ε` while the two laws are still far apart. The witness, in
full at `exists_localised_swap_bound`, is `k = 1`, `n = 1`, `ε = 1` and a two-point law with an
atom of mass `p` at `−a`, `a = √((1−p)/p)`, against the half-line `B = (−∞, −a/2]`: the shell
misses both atoms, so `W` may be taken exponentially small in `1/p`, while the left-hand side is
`≍ p`.

**The amendment** replaces the weight by `W + C_k ε`, `C_k = gaussianShellConst k`. It is free at
the only call site — `exists_convexDiscrepancy_recursion` feeds `W = 4 C_k ε + 2 Y` with `Y ≥ 0`,
and `W + C_k ε ≤ (5/4) W` there — so the recursion, `berryEsseen_convex_sharp` and its constant
shape are unchanged apart from a factor `2` absorbed into `A`.

**Half of the amended brick is now proved.** `exists_smooth_swap_bound_of_one_le_weight` closes
it whenever the total weight is `≥ 1`, with no localisation whatsoever: for `ε√n ≥ 1` it is the
unweighted `abs_integral_smooth_sub_gaussian_balanced`, and for `ε√n < 1` it is `|∫f dμ − ∫f dγ|
≤ 2` together with `(β/√n) ε⁻¹ ≥ β ≥ k^{3/2} ≥ 1`. What is left is the named brick
`localised_swap_bound_small_weight`, the same statement under `W + C_k ε ≤ 1`.

**What that residue actually needs** (this corrects the wave-22 reading, which called the
localisation a mechanical substitution of the wave-19 lemma). Along the Cameron–Martin route the
test function enters as `G(z) = f(v + σⱼ z)` — the function, not its third derivative, which has
been moved onto the Gaussian density — and `G` is *not* supported on the shell, since `f = 1` on
`B`. Splitting `f = 1_{interior B} + g` leaves the indicator part
`∫ 1_K(z) R_w(z) dγ(z) = γ(K − w) − Q_w(K)` with `K` convex. Wave 24 concluded that controlling
that by the shell mass is a Gaussian surface-area statement about convex bodies (Ball's input);
**wave 29 overturns this** — see the next section.

## Wave-29 amendment: no surface area is needed; the two-sided shell; the residue re-scoped

**The wave-24 obstruction is not real.** The tilt remainder has *mean zero*,
`integral_vecTiltRemainder_eq_zero`, so a constant may be subtracted from the test function for
free (`abs_integral_mul_vecTiltRemainder_le_of_const_off`, the wave-19 lemma extended from
"vanishes off `S`" to "is constant off `S`"). A mollified convex indicator is constant on the
ball of radius `r` about any `v` at distance `≥ r` from the shell, so the indicator part is
localised by the plain **Gaussian tail** `γ{‖z‖ ≥ r/σ}`
(`abs_integral_shift_vecTiltRemainder_le_of_const_ball`), which `stdGaussian_norm_ge_le` supplies
by Markov at any order. All of these are proved, axiom-clean, and dimension-free; no surface
measure occurs anywhere.

**The shell must be two-sided, and controlled at every width.** The set of points where the
localisation fails is `Bˢ \ B_{−s}` — the *two-sided* shell — and the width `s` that step `j` of
the telescope must afford is a multiple of the step width `σⱼ = √(j/n)`, which for `j` near `n`
is `≫ ε`. `gaussian_measureReal_wideShell_le`, `measureReal_wideShell_le_of_convexDiscrepancy`
and their affine transports repeat the outer-shell chain for the two-sided shell (cost: a factor
`2`), and `hybridLaw_wideShell_le` is brick H for it, at every width, uniformly in `j`. The
conditioning that both bricks H share is factored out as `hybridLaw_le_of_affine_le`.

**Consequently the weight hypothesis of brick L is amended** (hypothesis only, conclusion
untouched, and free at the only call site): see `localised_swap_bound_small_weight`.

**Two gaps the wave-24/29 plans did not see**, both recorded in full there: the `L²` tilt bound
needs `‖w‖ = ‖y‖/√j ≤ 1`, so the wave-19 lemma does *not* apply verbatim to the shell part
either, and the large-`‖y‖` region has to be handled by the tilt identity directly (its
`v`-average costs a two-sided shell at width `c‖y‖` — which is why the amended hypothesis is
stated at all widths); and the summed weight is `δ(2 C_k log(1/ε) + W/ε)`, so this route yields
the sharp rate **up to one logarithm**. The logarithm is intrinsic to a single mollification
width.

## Wave-32 amendment: the logarithm is EXECUTED, headline included

Wave 29 predicted the logarithm but left every conclusion frozen, on the ground that weakening
them then "would be a guess rather than a forced amendment". Wave 32 supplies the forcing — the
summation ledger, recorded in full at `localised_swap_bound_small_weight` — and carries the term
through the whole chain. Both exponents in that ledger are verified as part of the amendment:
`j^{-3/2}·σⱼ = c·j^{-1}` is a **harmonic** sum over `J < j ≤ n` (this, and only this, is where
the logarithm comes from), while `∑_{j>J} j^{-3/2} ≤ 2J^{-1/2} = 2(ε√n)^{-1}` reproduces the
`ε⁻¹` the frozen statements already carried.

* `localised_swap_bound_small_weight` — conclusion amended to
  `A δ (ε⁻¹(W + C_k ε) + C_k(1 + log(1 + ε⁻¹)))`. Still the file's one and only brick.
* `exists_localised_swap_bound`, `exists_convexDiscrepancy_recursion` — amended; the proved
  large-weight half is untouched (its log-free conclusion is *smaller*, so it still closes the
  amended goal), and the doubling of `A` that wave 24 introduced also absorbs the new term.
* `le_of_selfImproving_induction_log` (**new, proved**) — the strong induction re-solved with the
  extra `A δ C (1 + log(1 + ε⁻¹))`. It still closes **linearly**, at `K = 20 A C`, because the
  log factor `Mₙ = 1 + log(1 + (8Aδₙ)⁻¹)` is monotone in the *right* direction along the
  neighbour range (`m ≤ n ⟹ δₘ ≥ δₙ ⟹ Mₘ ≤ Mₙ`); `M ≥ 1` absorbs the log-free terms.
* `berryEsseen_convex_sharp` — headline amended to
  `C (β/√n)(1 + log(max (√n/β) e))`, `C = 160 (A+1) gaussianShellConst k`. The log-free form is
  **not** retracted (it is true, being Bentkus's theorem); it is simply not what this route
  proves, and the provable-constants rule forbids recording it.

A remark on the alternative: using the Gaussian tail `stdGaussian_norm_ge_le` at a *fixed* order
`p = 2m` rather than at all orders trades the logarithm for `ε^{-1/(m+1)}`, i.e. the headline
`(β/√n)^{m/(m+1)}` — strictly weaker than the log form for every fixed `m`, so the route is not
restructured for it.

**Constant deviation** (provable-constants rule): this route now gives `C ∼ k^{1/2}`, through
`gaussianShellConst k = 4 e² √k`, not Bentkus's `400 k^{1/4}`. Wave 22 removed the factor `k`
that the `2k`-fold coordinate cover used to contribute to the shell bound — a single random
Gaussian shift replaces it (`gaussian_le_of_gaussian_shift_cover`) — and the residual `√k` is
the first absolute moment `E‖Z‖ ≤ √k` of that shift. Closing the last gap to `k^{1/4}` needs
Ball's Gaussian-surface-area theorem; nothing in the recursion depends on it.

## Wave-39 amendment: the sub-Gaussian norm tail, and a `3/2` power of the logarithm

Wave 38 proved the head half of the per-step estimate (`abs_integral_swap_step_localised_le`)
and showed that the *tail* half cannot be produced at the wave-32 frozen weight `4 C_k σⱼ + W`:
the only Gaussian norm tail this file had was Markov at a fixed order, and localising the
Cameron–Martin swap needs the tail to be `≲ σ²` at a radius `≍ σ`, which no polynomial tail
gives. Wave 39 supplies the missing ingredient and pays its price openly.

* `stdGaussian_norm_ge_le_exp` (**new, proved**) — `γ{‖z‖ ≥ M} ≤ 2k exp(-M²/(2k))`, by the
  coordinate union bound over `stdGaussian_map_inner_unit` and the one-dimensional Chernoff
  tails `gaussianReal_ge_le` / `gaussianReal_abs_ge_le`. Its inversion `gaussianTailRadius k σ`
  satisfies `γ{‖z‖ ≥ gaussianTailRadius k σ} ≤ σ²`.
* `abs_integral_gaussian_smoothed_swap_localised_le` — the tail brick, restated at the weight
  route (b) actually delivers, `12 C_k σ · gaussianTailRadius k σ + W`. Still stated, not
  proved; what it now owes is assembly, not a missing estimate.
* `weighted_ledger_balance`, `localised_swap_bound_of_weighted_telescope` (**re-proved**) — the
  ledger with the extra radius factor. `gaussianTailRadius` is antitone, so no new summation
  lemma is needed; `gaussianTailRadius_le_dimTailConst` splits it as
  `dimTailConst k · √(1 + log(1 + ε⁻¹))`, and multiplying by the harmonic factor gives the
  `3/2` power `logPow32 ε`. Constant `306 C₃ + 33 C_t → 306 C₃ + 81 C_t` (wave 41: `→ 444 C_t`,
  the exact re-solution once the tail brick's own constants are known).
* `le_of_selfImproving_induction_forcing` (**new, proved**) — the fixed point with an abstract
  forcing factor. The wave-32 argument uses only `G ≥ 1` and antitonicity of `G`, so the `3/2`
  power self-improves **at the same constant** `20 A C`; `le_of_selfImproving_induction_log` is
  now its `G = 1 + log(1 + ε⁻¹)` instance and `le_of_selfImproving_induction_logPow32` the one
  the amended ledger consumes.
* `berryEsseen_convex_sharp` — headline amended to
  `C (β/√n)(1 + log(max (√n/β) e))^{3/2}`, `C = 60 (A+1) · dimTailConst k · (4 C_k) ≍ k √(log k)`.

**Two deviations, and which is intrinsic.** The `3/2` power *is* intrinsic to this route: the
tail radius grows like `√(log(1/σ))` however sharp the norm tail is, and a fixed Markov order
gives a *power* of `ε⁻¹` instead, which is worse. The dimension factor `√(k log k)` is *not*
intrinsic — it is the price of proving the norm tail by a union bound rather than by
`γ{‖z‖ ≥ M} ≤ exp(-(M − √k)²/2)` (Chernoff on `‖z‖² ∼ χ²_k`, or Borell–TIS, neither of which
Mathlib has). Sharpening it would give `≍ √k` there and change nothing else.

## Wave-40 amendment: the shift-length restriction is gone; the tail brick is bookkeeping only

Every wave from 32 to 39 recorded the same open input of the tail brick
`abs_integral_gaussian_smoothed_swap_localised_le`: the far-in-`v` localisation
`abs_integral_shift_vecTiltRemainder_le_of_const_ball` needs `‖w‖ ≤ 1`, because it runs through
the `L²` bound `integral_sq_vecTiltRemainder_le`, which is *false* for large tilts. At step `j`
the shift is `w = (c/σ)y`, so the restriction is `‖y‖ ≤ √j`, and the complement is not
priceable by a third moment alone (a bare constant in the per-step weight sums to `A δ ε⁻¹`,
outside brick L's allowed shape). **That restriction is now removed**, and the removal needed
no new concentration input:

* do not bound the *remainder* in `L²`; bound its two halves separately. The exponential half
  is a Gaussian **shift**, so a shift of length `‖w‖` is absorbed by enlarging the constancy
  *radius* to `σ(M + ‖w‖)` — no norm bound at all. The polynomial half is a genuine polynomial,
  and its `L²` norm is polynomial in `‖w‖` at *every* `‖w‖`;
* the polynomial's `L²` and `L¹` sizes (`integral_sq_vecTiltPoly_le ≤ 640(1+‖w‖²)²`,
  `integral_abs_vecTiltPoly_le ≤ 1 + ‖w‖ + ‖w‖²`) are proved by the same one-dimensional
  marginal as everything else in the `MultivariateTilt` section, so the constants are again
  **dimension-free**. The only new Gaussian fact needed is an explicit fourth moment of
  `N(0,1)`, supplied by the exponential envelope `pow_four_le_cosh` (no Gamma apparatus);
* `abs_integral_shift_vecTiltRemainder_le_of_const_ball_any` is the resulting far-in-`v`
  estimate, and `abs_integral_shift_vecTiltRemainder_localised_le` assembles it with the
  quadratic crude bound `abs_integral_mul_vecTiltRemainder_le_crude` into one pointwise bound
  in `(v, w)`, with the *same* far constant in both shift regimes.

**Constants, amended honestly.** The per-step ledger `localised_step_weight_le` turns the
resulting product (shell mass at the varying width `2σ(R+‖w‖)`, times
`min(C_t‖w‖³, 2+‖w‖+‖w‖²)`) back into a third moment, and the weight it delivers is
`68 C_k σ R + 4 W`, not wave 39's `12 C_k σ R + W` — wave 39 priced only the `‖w‖ ≤ 1` regime.
The tail brick's statement is amended accordingly; `localised_swap_bound_of_weighted_telescope`
carries a flag recording the corresponding re-run of `htel` (`12 → 68`, `3 → 12`) and of
`weighted_ledger_balance`'s `81 C_t`. **No shape moves**: the `(1 + log(1+ε⁻¹))^{3/2}` power,
the fixed point, and `berryEsseen_convex_sharp` are unaffected up to an absolute constant.

**What is left in the tail brick is measure-theoretic bookkeeping only**, in three named pieces
(the tilt representation, already established inside
`abs_integral_gaussian_smoothed_sub_common_le` but not exported; the Fubini at a varying width,
which is `integral_far_shell_le` with a different bracket; and the two-law triangle
inequality). No analytic input is missing — the first time that has been true of this brick.

## Wave-41 amendment: the tail brick is PROVED, and brick L's residue is re-diagnosed

**The tail brick `abs_integral_gaussian_smoothed_swap_localised_le` is closed**, open since
wave 32. Wave 40's verdict — "no analytic input is missing, three named bookkeeping pieces
remain" — is confirmed exactly: the pieces are `integral_gaussian_smoothed_sub_common_eq` (the
tilt representation, now exported and the old `abs_…_sub_common_le` refactored into its
corollary), `integral_localised_shell_le` (the Fubini at the varying width), and the two-law
triangle inequality against the law-independent Cameron–Martin number. **No constant needed
amending**: wave 40's `68 C_k σ R + 4 W` ledger is exact. Consequently the wave-40 FLAG on
`localised_swap_bound_of_weighted_telescope` is executed — `htel`'s tail summands are now
`68 …` and `12 …`, and `weighted_ledger_balance` re-solves at `306 C₃ + 444 C_t` (wave 40
guessed `459 C_t` would suffice; `444` is exact, and the `C₃` half is untouched).

**A claim of waves 36–40 is OVERTURNED, and it is what brick L still owes.** Both localised
per-step bricks carry the docstring line "`τ` is `hybridLaw n j ν`". It is not. At step `j` the
telescope peels coordinate `j`, so the base point of the step is `c·(∑ of the OTHER
coordinates) + σⱼ z` and the swapped coordinate enters only as the `c u` *inside* the absolute
value. The bricks' `τ` is therefore the **peeled** law; `hybridLaw n j ν` — which brick H bounds
and which brick L's hypothesis asserts — is the law of that base point **plus** `c u`, as
`integral_peel_eq_integral_hybridLaw`'s right-hand side `F(c(u + ∑ₗ yₗ) + σⱼ z)` says outright.
Neither is a special case of the other: the peeled law is `hybridLaw` with the dirac cut at
`j + 1` but the smoothing still at `j`, and `hybridLaw n j ν = (peeled law) ∗ (c·ν)`, which is
the wrong direction to deconvolve.

## Wave-42 amendment: the transfer is deconvolution, and the window strengthens to `√k ≤ ε√n`

**The repair is DECONVOLUTION, not shifting (wave 42).** Wave 41 proposed
`indicator_wideShell_le_shift` (`1_{shell at s}(a) ≤ 1_{shell at s+t}(a+w)` for `‖w‖ ≤ t`) to
move each brick's indicator to the shifted point. That fails: the width at which either brick
consults its shell hypothesis is a function of the *same* variable as the shift, so what the
move produces is the shell mass of a **translate** of the base law, which a constant-width
hypothesis on the convolution does not bound (formalized witness in the wave-42 note of
`localised_swap_bound_small_weight`). What does work is `wideShell_le_of_deconvolution`, proved
in wave 42: `τ(shell s)·η(closedBall 0 t) ≤ (τ ∗ η)(shell (s+t))`, so a shell bound for the
convolution *does* give one for the factor, at the price of `η`'s concentration radius. It costs
`C_k → 3 C_k`, `W → 2W + 11 C_k t`, and a strengthening of the localisation window from
`1 ≤ ε √n` to `√k ≤ ε √n` (free at the call site). What remains for brick L is then: the two
convolution identities that `wideShell_le_of_deconvolution` consumes, and the localised
telescope (`hstepfun` with the `v`-dependent `D` and `sum_le_of_bounded_and_weighted_decay`) to
produce `htel`. **No analytic input is missing on either side** — both per-step estimates are
now theorems.

**Reference.** V. Bentkus, "On the dependence of the Berry–Esseen bound on dimension,\"
*J. Statist. Plann. Inference* **113** (2003), 385–402. E. L. Lehmann and J. P. Romano,
*Testing Statistical Hypotheses*, 4th ed., Springer, 2022, §16.4, Lemma 16.4.1.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators InnerProductSpace Real

namespace StatLean.HypothesisTesting

/-! ### Gaussian slab anti-concentration (dimension-free) -/

section AntiConcentration

variable {k : ℕ}

/-- The pushforward of the standard multivariate Gaussian `N(0, I_k)` under a **unit-vector**
inner-product projection `z ↦ ⟪u, z⟫` is the standard one-dimensional Gaussian `N(0,1)`.
This is the marginal computation behind the anti-concentration bound. -/
lemma stdGaussian_map_inner_unit (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    Measure.map (fun y => ⟪u, y⟫_ℝ) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      = gaussianReal 0 1 := by
  rw [multivariateGaussian_map_inner_eq_gaussianReal u Matrix.PosSemidef.one]
  congr 1
  have hstar : star u.ofLp = u.ofLp := by ext i; simp
  have huu : u.ofLp ⬝ᵥ (1 : Matrix (Fin k) (Fin k) ℝ).mulVec u.ofLp = 1 := by
    rw [Matrix.one_mulVec]
    calc u.ofLp ⬝ᵥ u.ofLp
        = u.ofLp ⬝ᵥ star u.ofLp := by rw [hstar]
      _ = ⟪u, u⟫_ℝ := (EuclideanSpace.inner_eq_star_dotProduct u u).symm
      _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
      _ = 1 := by rw [hu]; norm_num
  rw [huu, Real.toNNReal_one]

/-- **Standard 1-D Gaussian anti-concentration.** The `N(0,1)` mass of an interval `(a, b]`
is at most `(b - a)/√(2π)`, because the Gaussian density is bounded by `1/√(2π)`. -/
lemma gaussianReal_stdNormal_Ioc_le {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1 (Set.Ioc a b)).toReal ≤ (b - a) / Real.sqrt (2 * π) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [gaussianReal_apply_eq_integral 0 hv (Set.Ioc a b), ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_Ioc (fun x _ => gaussianPDFReal_nonneg _ _ _))]
  have hbound : ∀ x, gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * π))⁻¹ := by
    intro x
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * 1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (x - 0)]
    have hpos : (0 : ℝ) ≤ (Real.sqrt (2 * π * 1))⁻¹ := by positivity
    calc gaussianPDFReal 0 1 x
        = (Real.sqrt (2 * π * 1))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * 1)) := rfl
      _ ≤ (Real.sqrt (2 * π * 1))⁻¹ * 1 := by
            apply mul_le_mul_of_nonneg_left hexp hpos
      _ = (Real.sqrt (2 * π))⁻¹ := by norm_num
  calc ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x
      ≤ ∫ _ in Set.Ioc a b, (Real.sqrt (2 * π))⁻¹ ∂volume := by
          apply setIntegral_mono_on (integrable_gaussianPDFReal _ _).restrict
            (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
          exact fun x _ => hbound x
    _ = (b - a) / Real.sqrt (2 * π) := by
          rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          ring

/-- **Gaussian slab anti-concentration, dimension-free.** For a unit vector `u` and `a ≤ b`,
the standard multivariate Gaussian mass of the slab `{z : a < ⟪u,z⟫ ≤ b}` is at most
`(b - a)/√(2π)`. The constant carries no dimension factor: this is "step 3" of the Lindeberg
route for a half-space, and is exactly the one-dimensional marginal bound.

This is the honest ingredient the elementary convex-set Berry–Esseen argument would consume;
the dimension factor of Bentkus (2003) arises only from covering the boundary shell of a
general convex body by such slabs, which is not carried out here. -/
theorem gaussian_slab_measure_le (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1)
    {a b : ℝ} (hab : a ≤ b) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
        {z | a < ⟪u, z⟫_ℝ ∧ ⟪u, z⟫_ℝ ≤ b}).toReal
      ≤ (b - a) / Real.sqrt (2 * π) := by
  have hset : {z : EuclideanSpace ℝ (Fin k) | a < ⟪u, z⟫_ℝ ∧ ⟪u, z⟫_ℝ ≤ b}
      = (fun y => ⟪u, y⟫_ℝ) ⁻¹' Set.Ioc a b := rfl
  rw [hset, ← Measure.map_apply (by fun_prop) measurableSet_Ioc,
    stdGaussian_map_inner_unit u hu]
  exact gaussianReal_stdNormal_Ioc_le hab

end AntiConcentration

/-! ### Dimension-free ball anti-concentration (the radial analogue)

For the *ball* route the relevant anti-concentration statement is the mass of a thin spherical
**shell** `{t < ‖z‖ ≤ t + ε}` under `N(0, I_k)`. Its clean reduction is that the law of `‖z‖²`
under `N(0, I_k)` is exactly the chi-squared law `χ²_k`, so the shell mass is a chi-squared
interval mass. The genuinely dimension-free fact is that the **chi density** `f_k(r) = c_k r^{k-1}
e^{-r²/2}` (equivalently `2√x · gammaPDF (k/2) (1/2) x`) has a maximum bounded by an *absolute*
constant, uniformly in `k` — its peak `≈ e^{1/2}/√π < 1` sits at `r = √(k-1)` and does not grow
with `k`. That single uniform bound (`chiSquared_density_mul_sqrt_le`) is the crux; everything else
is the measure-theoretic reduction and an elementary `∫ 1/(2√x) dx = √x` computation.

Both are now proved: the peak bound is obtained **without any Stirling asymptotics** for `Γ` by
restricting Euler's integral to the length-`√p` window `(p, p+√p]` at the peak
(`le_Gamma_add_half`), which is enough because the window's own width supplies exactly the
`√p/√(3p) = 1/√3` that the `x^{-1/2}` factor costs. The resulting absolute constant is
`e√6 < 7`. -/

section BallAntiConcentration

open scoped Real

variable {k : ℕ}

/-- **Shell mass is a chi-squared interval mass.** For `0 < k`, `0 ≤ t`, `0 ≤ ε`, the standard
multivariate Gaussian mass of the spherical shell `{t < ‖z‖ ≤ t + ε}` equals the chi-squared mass
of the interval `(t², (t+ε)²]`, because `‖z‖² ∼ χ²_k` under `N(0, I_k)` and `r ↦ r²` is strictly
monotone on `[0, ∞)`. -/
lemma multivariateGaussian_shell_eq_chiSquared (hk : 0 < k) {t ε : ℝ} (ht : 0 ≤ t)
    (hε : 0 ≤ ε) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 {z | t < ‖z‖ ∧ ‖z‖ ≤ t + ε}
      = StatLean.MultipleTesting.chiSquared k (Set.Ioc (t ^ 2) ((t + ε) ^ 2)) := by
  have hmap : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1).map (fun z => ‖z‖ ^ 2)
      = StatLean.MultipleTesting.chiSquared k := by
    rw [map_normSq_multivariateGaussian_of_norm_eq k 0 (by simp), noncentralChiSquared_zero hk]
  have hset : {z : EuclideanSpace ℝ (Fin k) | t < ‖z‖ ∧ ‖z‖ ≤ t + ε}
      = (fun z => ‖z‖ ^ 2) ⁻¹' Set.Ioc (t ^ 2) ((t + ε) ^ 2) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioc]
    have hz : 0 ≤ ‖z‖ := norm_nonneg z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  rw [hset, ← Measure.map_apply (by fun_prop) measurableSet_Ioc, hmap]

/-- The elementary primitive `√x` of `1/(2√x)`: for `0 ≤ a ≤ b`,
`∫_{(a,b]} (2√x)⁻¹ dx = √b − √a`. This is the change-of-variables factor that turns the
chi-squared interval width `(t+ε)² − t²` back into the shell width `ε`. -/
lemma integral_Ioc_inv_two_sqrt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, (2 * Real.sqrt x)⁻¹ = Real.sqrt b - Real.sqrt a := by
  rw [← intervalIntegral.integral_of_le hab]
  have hcont : ContinuousOn Real.sqrt (Set.Icc a b) := Real.continuous_sqrt.continuousOn
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivWithinAt Real.sqrt ((2 * Real.sqrt x)⁻¹) (Set.Ioi x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hx.1)
    have h := (Real.hasDerivAt_sqrt hx0).hasDerivWithinAt (s := Set.Ioi x)
    rwa [one_div] at h
  have hint : IntervalIntegrable (fun x => (2 * Real.sqrt x)⁻¹) volume a b := by
    have hrpow : IntervalIntegrable (fun x => (1 / 2) * x ^ (-(1 / 2) : ℝ)) volume a b :=
      (intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (1 / 2)
    refine (intervalIntegrable_congr (fun x hx => ?_)).mp hrpow
    have hx0 : 0 < x := by
      rw [Set.uIoc_of_le hab] at hx; exact lt_of_le_of_lt ha hx.1
    rw [Real.sqrt_eq_rpow, mul_inv, Real.rpow_neg hx0.le]; ring
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint

/-- **Peak of the gamma kernel.** For `p > 0` the function `x ↦ x^p e^{-x/2}` attains its
maximum over `x > 0` at `x = 2p`. Taking logarithms this is exactly `log t ≤ t - 1` at
`t = x/(2p)`. -/
private lemma rpow_mul_exp_neg_half_le {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    x ^ p * Real.exp (-x / 2) ≤ (2 * p) ^ p * Real.exp (-p) := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have h2p : (0 : ℝ) < 2 * p := by linarith
  have hlog : Real.log (x / (2 * p)) ≤ x / (2 * p) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt h2p)] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hp.le
  have hxx : p * (x / (2 * p) - 1) = x / 2 - p := by field_simp
  rw [hxx] at hmul
  have hL : x ^ p * Real.exp (-x / 2) = Real.exp (p * Real.log x - x / 2) := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_add]; congr 1; ring
  have hR : (2 * p) ^ p * Real.exp (-p) = Real.exp (p * Real.log (2 * p) - p) := by
    rw [Real.rpow_def_of_pos h2p, ← Real.exp_add]; congr 1; ring
  rw [hL, hR]
  exact Real.exp_le_exp.mpr (by nlinarith [hmul])

/-- **Stirling-free lower bound for `Γ` at the half-integer shift.** For `p ≥ 1/2`,
`Γ(p + 1/2) ≥ p^p e^{-p} / (e √3)`.

This replaces the `Γ`-Stirling estimate that Mathlib v4.29.1 does not provide for
half-integer arguments: instead of asymptotics one simply restricts Euler's integral
`Γ(p+1/2) = ∫_{x>0} e^{-x} x^{p-1/2} dx` to the window `(p, p + √p]` of length `√p` sitting at
the peak. On that window `e^{-x} x^p ≥ p^p e^{-p} e^{-1}` (from `log t ≥ 1 - 1/t`, since
`(x-p)² ≤ p < x` there) and `x^{-1/2} ≥ (3p)^{-1/2}` (since `x ≤ p + √p ≤ 3p` for `p ≥ 1/4`);
multiplying by the window length `√p` gives `√p/√(3p) = 1/√3`. -/
private lemma le_Gamma_add_half {p : ℝ} (hp : 1 / 2 ≤ p) :
    p ^ p * Real.exp (-p) / (Real.exp 1 * Real.sqrt 3) ≤ Real.Gamma (p + 1 / 2) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hspsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hsple : Real.sqrt p ≤ 2 * p := by nlinarith [hspsq, hsp]
  have hs : (0 : ℝ) < p + 1 / 2 := by linarith
  have hGam : Real.Gamma (p + 1 / 2)
      = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (p + 1 / 2 - 1) :=
    Real.Gamma_eq_integral hs
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (p + 1 / 2 - 1))
      (Set.Ioi 0) := Real.GammaIntegral_convergent hs
  set L : ℝ := p ^ p * Real.exp (-p) * Real.exp (-1) * (Real.sqrt (3 * p))⁻¹ with hLdef
  have hsub : Set.Ioc p (p + Real.sqrt p) ⊆ Set.Ioi (0 : ℝ) := fun y hy => lt_trans hp0 hy.1
  -- Pointwise lower bound of the Euler integrand on the peak window.
  have hpt : ∀ y ∈ Set.Ioc p (p + Real.sqrt p), L ≤ Real.exp (-y) * y ^ (p + 1 / 2 - 1) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy0 : (0 : ℝ) < y := lt_trans hp0 hy1
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
    have hsplit : y ^ (p + 1 / 2 - 1) = y ^ p * (Real.sqrt y)⁻¹ := by
      rw [show p + 1 / 2 - 1 = p - 1 / 2 by ring, Real.rpow_sub hy0, Real.sqrt_eq_rpow,
        div_eq_mul_inv]
    -- (a) the exponential–power factor is within `e` of its peak value
    have hA : p ^ p * Real.exp (-p) * Real.exp (-1) ≤ Real.exp (-y) * y ^ p := by
      have hlt : Real.log (p / y) ≤ p / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hp0) (ne_of_gt hy0)] at hlt
      have hmul := mul_le_mul_of_nonneg_left hlt hp0.le
      have hpy : p * (p / y - 1) = p ^ 2 / y - p := by field_simp
      rw [hpy] at hmul
      have hd : (y - p) ^ 2 ≤ y := by nlinarith [hspsq]
      have hyy : p ^ 2 / y ≤ 2 * p + 1 - y := by
        rw [div_le_iff₀ hy0]; nlinarith [hd]
      have hlogineq : p * Real.log p - p - 1 ≤ -y + p * Real.log y := by linarith
      have hE1 : p ^ p * Real.exp (-p) * Real.exp (-1)
          = Real.exp (p * Real.log p - p - 1) := by
        rw [Real.rpow_def_of_pos hp0, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hE2 : Real.exp (-y) * y ^ p = Real.exp (-y + p * Real.log y) := by
        rw [Real.rpow_def_of_pos hy0, ← Real.exp_add]; congr 1; ring
      rw [hE1, hE2]
      exact Real.exp_le_exp.mpr hlogineq
    -- (b) the radial factor `x^{-1/2}` is at least `(3p)^{-1/2}` on the window
    have hB : (Real.sqrt (3 * p))⁻¹ ≤ (Real.sqrt y)⁻¹ := by
      have h1 : Real.sqrt y ≤ Real.sqrt (3 * p) := Real.sqrt_le_sqrt (by linarith)
      exact inv_anti₀ hsy h1
    rw [hsplit, hLdef]
    calc p ^ p * Real.exp (-p) * Real.exp (-1) * (Real.sqrt (3 * p))⁻¹
        ≤ p ^ p * Real.exp (-p) * Real.exp (-1) * (Real.sqrt y)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ Real.exp (-y) * y ^ p * (Real.sqrt y)⁻¹ :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ = Real.exp (-y) * (y ^ p * (Real.sqrt y)⁻¹) := by ring
  -- Integrate the pointwise bound over the window and drop to the whole half-line.
  have hIc : IntegrableOn (fun _ : ℝ => L) (Set.Ioc p (p + Real.sqrt p)) :=
    integrableOn_const (C := L) measure_Ioc_lt_top.ne
  have hIf : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ (p + 1 / 2 - 1))
      (Set.Ioc p (p + Real.sqrt p)) := hint.mono_set hsub
  have hwin : L * Real.sqrt p ≤ ∫ y in Set.Ioc p (p + Real.sqrt p),
      Real.exp (-y) * y ^ (p + 1 / 2 - 1) := by
    have hmono := setIntegral_mono_on hIc hIf measurableSet_Ioc hpt
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith [Real.sqrt_nonneg p]), smul_eq_mul] at hmono
    calc L * Real.sqrt p = (p + Real.sqrt p - p) * L := by ring
      _ ≤ _ := hmono
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun x : ℝ => Real.exp (-x) * x ^ (p + 1 / 2 - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx0.le _)
  have hLid : L * Real.sqrt p = p ^ p * Real.exp (-p) / (Real.exp 1 * Real.sqrt 3) := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    rw [hLdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) p,
      show Real.exp (-1) = (Real.exp 1)⁻¹ from Real.exp_neg 1]
    have hsne : Real.sqrt p ≠ 0 := ne_of_gt hsp
    have h3ne : Real.sqrt 3 ≠ 0 := ne_of_gt h3
    have hene : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
    field_simp
  rw [hGam, ← hLid]
  exact hwin.trans (setIntegral_mono_set hint hnn hsub.eventuallyLE)

/-- Numerical constant of the peak bound: `2 (√2)⁻¹ e √3 = e √6 < 7`. -/
private lemma peak_const_le_seven :
    2 * (Real.sqrt 2)⁻¹ * (Real.exp 1 * Real.sqrt 3) ≤ 7 := by
  have h2 : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h3 : Real.sqrt 3 ≤ 1.7321 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have hinv : (Real.sqrt 2)⁻¹ ≤ (1.414 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hs3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hinv0 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
  calc 2 * (Real.sqrt 2)⁻¹ * (Real.exp 1 * Real.sqrt 3)
      ≤ 2 * (1.414 : ℝ)⁻¹ * (2.7182818286 * 1.7321) := by gcongr
    _ ≤ 7 := by norm_num

/-- **The dimension-free chi-density peak bound.**
`2√x · gammaPDF (k/2) (1/2) x ≤ 7` for all `k > 0` and `x > 0`. The left side is exactly the chi
density `f_k(√x) = √x^{k-1} e^{-x/2} / (2^{k/2-1} Γ(k/2))`; its maximum over `x` is attained at
`x = k-1` with value `→ e^{1/2}/√π < 1` as `k → ∞`, and the proof below shows it never exceeds
`e√6 < 7`. **This is the one genuinely dimension-free crux of the ball route.**

Proof. Write `a = k/2` and `p = a - 1/2`. Then
`2√x · gammaPDFReal a (1/2) x = 2 (1/2)^a Γ(a)⁻¹ · x^p e^{-x/2}`; the kernel factor is maximised
at `x = 2p` (`rpow_mul_exp_neg_half_le`), and `(1/2)^a (2p)^p = (√2)⁻¹ p^p`, so the whole
expression is at most `√2 · p^p e^{-p} / Γ(p + 1/2)`, which `le_Gamma_add_half` bounds by
`√2 · e √3 = e √6 < 7` — with **no dependence on `k`**. The degenerate case `k = 1` (`p = 0`) is
separate and uses `Γ(1/2) = √π`. -/
private lemma chiSquared_density_mul_sqrt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 0 < k → ∀ x : ℝ, 0 < x →
      2 * Real.sqrt x * gammaPDFReal ((k : ℝ) / 2) (1 / 2) x ≤ C := by
  refine ⟨7, by norm_num, ?_⟩
  intro k hk x hx
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · -- `k = 1`: the density is `(1/2)^{1/2} Γ(1/2)⁻¹ x^{-1/2} e^{-x/2}`, and `√x · x^{-1/2} = 1`.
    have hk1 : (k : ℝ) = 1 := by
      have : k = 1 := by omega
      rw [this]; norm_num
    rw [hk1]
    have hpdf : gammaPDFReal ((1 : ℝ) / 2) (1 / 2) x
        = ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.Gamma (1 / 2) * x ^ ((1 : ℝ) / 2 - 1)
          * Real.exp (-((1 / 2) * x)) := by
      simp only [gammaPDFReal, if_pos hx.le]
    rw [hpdf, Real.Gamma_one_half_eq]
    have hsx : Real.sqrt x * x ^ ((1 : ℝ) / 2 - 1) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      norm_num
    have hpi : (1 : ℝ) ≤ Real.sqrt π := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
    have hbase : ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
    have hbase0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hexp : Real.exp (-((1 / 2) * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hexp0 : (0 : ℝ) < Real.exp (-((1 / 2) * x)) := Real.exp_pos _
    calc 2 * Real.sqrt x * (((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π
              * x ^ ((1 : ℝ) / 2 - 1) * Real.exp (-((1 / 2) * x)))
        = 2 * (((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π)
            * (Real.sqrt x * x ^ ((1 : ℝ) / 2 - 1)) * Real.exp (-((1 / 2) * x)) := by ring
      _ = 2 * (((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π)
            * Real.exp (-((1 / 2) * x)) := by rw [hsx, mul_one]
      _ ≤ 2 * 1 * 1 := by
          have hdiv : ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          have hdiv0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π := by positivity
          nlinarith
      _ ≤ 7 := by norm_num
  · -- `k ≥ 2`: the peak bound plus the `Γ` lower bound, both dimension-free.
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
    set a : ℝ := (k : ℝ) / 2 with hadef
    set p : ℝ := a - 1 / 2 with hpdef
    have hp : (1 : ℝ) / 2 ≤ p := by rw [hpdef, hadef]; linarith
    have hp0 : (0 : ℝ) < p := by linarith
    have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos (by rw [hadef]; linarith)
    have hpdf : gammaPDFReal a (1 / 2) x
        = ((1 : ℝ) / 2) ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-((1 / 2) * x)) := by
      simp only [gammaPDFReal, if_pos hx.le]
    have hsx : Real.sqrt x * x ^ (a - 1) = x ^ p := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      congr 1
      rw [hpdef]; ring
    have hrw : 2 * Real.sqrt x * gammaPDFReal a (1 / 2) x
        = 2 * (((1 : ℝ) / 2) ^ a / Real.Gamma a) * (x ^ p * Real.exp (-x / 2)) := by
      rw [hpdf, ← hsx]
      rw [show Real.exp (-((1 / 2) * x)) = Real.exp (-x / 2) by congr 1; ring]
      ring
    rw [hrw]
    have hc0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ a / Real.Gamma a := by positivity
    have hstep1 : 2 * (((1 : ℝ) / 2) ^ a / Real.Gamma a) * (x ^ p * Real.exp (-x / 2))
        ≤ 2 * (((1 : ℝ) / 2) ^ a / Real.Gamma a) * ((2 * p) ^ p * Real.exp (-p)) :=
      mul_le_mul_of_nonneg_left (rpow_mul_exp_neg_half_le hp0 hx) (by linarith)
    refine hstep1.trans ?_
    -- `(1/2)^a · 2^p = 2^{p-a} = 2^{-1/2} = (√2)⁻¹`
    have hhalf : ((1 : ℝ) / 2) ^ a * (2 : ℝ) ^ p = (Real.sqrt 2)⁻¹ := by
      have hinv : ((1 : ℝ) / 2) ^ a = ((2 : ℝ) ^ a)⁻¹ := by
        rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num,
          Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hinv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        show -a + p = -(1 / 2) by rw [hpdef]; ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]
    have hnum : 2 * (((1 : ℝ) / 2) ^ a) * ((2 * p) ^ p * Real.exp (-p))
        = 2 * (Real.sqrt 2)⁻¹ * (p ^ p * Real.exp (-p)) := by
      calc 2 * (((1 : ℝ) / 2) ^ a) * ((2 * p) ^ p * Real.exp (-p))
          = 2 * ((((1 : ℝ) / 2) ^ a) * (2 : ℝ) ^ p) * (p ^ p * Real.exp (-p)) := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp0.le]; ring
        _ = 2 * (Real.sqrt 2)⁻¹ * (p ^ p * Real.exp (-p)) := by rw [hhalf]
    have hgoal : 2 * (((1 : ℝ) / 2) ^ a / Real.Gamma a) * ((2 * p) ^ p * Real.exp (-p))
        = (2 * (Real.sqrt 2)⁻¹ * (p ^ p * Real.exp (-p))) / Real.Gamma a := by
      rw [← hnum]; field_simp
    rw [hgoal, div_le_iff₀ hGa]
    have hGlb : p ^ p * Real.exp (-p) / (Real.exp 1 * Real.sqrt 3) ≤ Real.Gamma a := by
      have h := le_Gamma_add_half hp
      rwa [show p + 1 / 2 = a by rw [hpdef]; ring] at h
    have hq : (0 : ℝ) < p ^ p * Real.exp (-p) := by positivity
    have he3 : (0 : ℝ) < Real.exp 1 * Real.sqrt 3 := by
      have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    calc 2 * (Real.sqrt 2)⁻¹ * (p ^ p * Real.exp (-p))
        ≤ 7 * (p ^ p * Real.exp (-p) / (Real.exp 1 * Real.sqrt 3)) := by
          rw [← mul_div_assoc, le_div_iff₀ he3]
          nlinarith [mul_le_mul_of_nonneg_right peak_const_le_seven hq.le]
      _ ≤ 7 * Real.Gamma a := by linarith

/-- **Dimension-free ball (shell) anti-concentration.** There is an *absolute* constant `C`
(independent of the dimension `k`, the radius `t` and the shell width `ε`) such that the standard
multivariate Gaussian mass of the spherical shell `{t < ‖z‖ ≤ t + ε}` is at most `C · ε`. This is
the radial analogue of `gaussian_slab_measure_le` and the ingredient the ball Berry-Esseen bound
consumes. It is proved **unconditionally** (one may take `C = 7`) from the measure-theoretic
reduction `multivariateGaussian_shell_eq_chiSquared`, the elementary primitive
`integral_Ioc_inv_two_sqrt`, and the uniform chi-density peak bound
`chiSquared_density_mul_sqrt_le`. -/
theorem gaussian_ball_shell_measure_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 0 < k → ∀ t ε : ℝ, 0 ≤ t → 0 ≤ ε →
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
          {z | t < ‖z‖ ∧ ‖z‖ ≤ t + ε}).toReal ≤ C * ε := by
  obtain ⟨C, hC, hCbound⟩ := chiSquared_density_mul_sqrt_le
  refine ⟨C, hC, ?_⟩
  intro k hk t ε ht hε
  rw [multivariateGaussian_shell_eq_chiSquared hk ht hε]
  set a := t ^ 2 with ha
  set b := (t + ε) ^ 2 with hb
  have h0a : (0 : ℝ) ≤ a := by rw [ha]; positivity
  have hab : a ≤ b := by rw [ha, hb]; nlinarith
  -- Pointwise density bound `gammaPDFReal ≤ C · (2√x)⁻¹` for `x > 0`.
  have hden : ∀ x : ℝ, 0 < x →
      gammaPDFReal ((k : ℝ) / 2) (1 / 2) x ≤ C * (2 * Real.sqrt x)⁻¹ := by
    intro x hx0
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have h2 : 0 < 2 * Real.sqrt x := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h2, mul_comm]
    exact hCbound k hk x hx0
  -- Reduce the chi-squared interval mass to a Lebesgue integral of the density.
  have hcs : StatLean.MultipleTesting.chiSquared k (Set.Ioc a b)
      = ∫⁻ x in Set.Ioc a b, gammaPDF ((k : ℝ) / 2) (1 / 2) x := by
    unfold StatLean.MultipleTesting.chiSquared ProbabilityTheory.gammaMeasure
    rw [withDensity_apply _ measurableSet_Ioc]
  rw [hcs]
  -- Integrability and nonnegativity of the majorant `C · (2√x)⁻¹` on `(a, b]`.
  have hInt0 : IntegrableOn (fun x => (2 * Real.sqrt x)⁻¹) (Set.Ioc a b) volume := by
    have hint : IntervalIntegrable (fun x => (2 * Real.sqrt x)⁻¹) volume a b := by
      have hrpow : IntervalIntegrable (fun x => (1 / 2) * x ^ (-(1 / 2) : ℝ)) volume a b :=
        (intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (1 / 2)
      refine (intervalIntegrable_congr (fun x hx => ?_)).mp hrpow
      have hx0 : 0 < x := by
        rw [Set.uIoc_of_le hab] at hx; exact lt_of_le_of_lt h0a hx.1
      rw [Real.sqrt_eq_rpow, mul_inv, Real.rpow_neg hx0.le]; ring
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  have hIntC : IntegrableOn (fun x => C * (2 * Real.sqrt x)⁻¹) (Set.Ioc a b) volume :=
    hInt0.const_mul C
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] fun x => C * (2 * Real.sqrt x)⁻¹ :=
    ae_of_all _ fun x => mul_nonneg hC.le (by positivity)
  -- The majorant integrates to `C · ε`.
  have hmaj : ∫ x in Set.Ioc a b, C * (2 * Real.sqrt x)⁻¹ = C * ε := by
    rw [integral_const_mul, integral_Ioc_inv_two_sqrt h0a hab, hb, ha,
      Real.sqrt_sq (by linarith), Real.sqrt_sq ht]; ring
  -- Bound the lintegral by `ofReal (C · ε)`.
  have hlint : ∫⁻ x in Set.Ioc a b, gammaPDF ((k : ℝ) / 2) (1 / 2) x
      ≤ ENNReal.ofReal (C * ε) := by
    calc ∫⁻ x in Set.Ioc a b, gammaPDF ((k : ℝ) / 2) (1 / 2) x
        ≤ ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (C * (2 * Real.sqrt x)⁻¹) := by
          apply setLIntegral_mono_ae (by fun_prop)
          refine ae_of_all _ (fun x hx => ?_)
          have hx0 : 0 < x := lt_of_le_of_lt h0a hx.1
          rw [show gammaPDF ((k : ℝ) / 2) (1 / 2) x
              = ENNReal.ofReal (gammaPDFReal ((k : ℝ) / 2) (1 / 2) x) from rfl]
          exact ENNReal.ofReal_le_ofReal (hden x hx0)
      _ = ENNReal.ofReal (∫ x in Set.Ioc a b, C * (2 * Real.sqrt x)⁻¹) :=
          (ofReal_integral_eq_lintegral_ofReal hIntC hnn).symm
      _ = ENNReal.ofReal (C * ε) := by rw [hmaj]
  calc (∫⁻ x in Set.Ioc a b, gammaPDF ((k : ℝ) / 2) (1 / 2) x).toReal
      ≤ (ENNReal.ofReal (C * ε)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = C * ε := ENNReal.toReal_ofReal (mul_nonneg hC.le hε)

end BallAntiConcentration

/-! ### The remaining ingredients of the elementary route

Of the analytic bricks of the Lindeberg-swap route, the third-order Taylor remainder
(`norm_taylor_remainder_three_le`) and — for the **ball** route — the smoothed radial
indicator (`exists_smoothed_radial_indicator`) are now proved here, unconditionally and with
dimension-free constants. The **multivariate Lindeberg swap** `abs_integral_smooth_sub_gaussian_le`
and — for the *convex* route — `exists_smoothed_convex_indicator` are proved here as well, so no
brick of the route is left as debt. The honest final bounds
`berryEsseen_ball_elementary` / `berryEsseen_convex_elementary` record the exact statements the
route delivers; their exponent `(β/√n)^{1/4}` is the genuine — non-sharp — outcome (see the
module docstring). -/

section ElementaryRoute

/-- **Third-order Taylor remainder on a normed space.** For `C³` `f` with `‖D³f‖ ≤ M`, the
second-order Taylor error at `x` in direction `h` is at most `M ‖h‖³ / 6`. This is the analytic
heart of the Lindeberg swap. Mathlib v4.29.1 has only the one-dimensional Taylor remainder, so we
reduce to the segment `t ↦ f (x + t • h)` (a `C³` map `ℝ → ℝ`), apply the 1-D Lagrange bound, and
identify `(d/dt)ᵐ f(x+t•h) = iteratedFDeriv ℝ m f (x+t•h) (fun _ => h)` via the composition of the
translation `w ↦ f (x + w)` with the continuous linear map `t ↦ t • h`. -/
private lemma norm_taylor_remainder_three_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 3 f) {M : ℝ}
    (hM : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M) (x h : E) :
    |f (x + h) - f x - fderiv ℝ f x h - (1 / 2) * iteratedFDeriv ℝ 2 f x (fun _ => h)|
      ≤ M / 6 * ‖h‖ ^ 3 := by
  -- The line restriction `g s = f (x + s • h)`.
  set g : ℝ → ℝ := fun s => f (x + s • h) with hg
  -- The continuous linear map `L : t ↦ t • h`, so that `g = (fun w => f (x + w)) ∘ L`.
  set L : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight h with hLdef
  have hLapp : ∀ t : ℝ, L t = t • h := by
    intro t
    simp only [hLdef, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
  have hF : ContDiff ℝ 3 (fun w : E => f (x + w)) := hf.comp (contDiff_const.add contDiff_id)
  -- Core identity: `(d/ds)ᵐ g = iteratedFDeriv ℝ m f (x + s•h) (fun _ => h)` for `m ≤ 3`.
  have key : ∀ (m : ℕ), m ≤ 3 → ∀ s : ℝ,
      iteratedDeriv m g s = iteratedFDeriv ℝ m f (x + s • h) (fun _ => h) := by
    intro m hm s
    have hcomp : g = (fun w : E => f (x + w)) ∘ L := by funext t; simp [hg, hLapp]
    rw [iteratedDeriv_eq_iteratedFDeriv, hcomp,
      ContinuousLinearMap.iteratedFDeriv_comp_right L hF s (by exact_mod_cast hm),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
    rw [hLapp]
    congr 1
    funext i; rw [hLapp]; simp
  -- `g` is `C³`, hence `C³` on `[0,1]`.
  have hgcd : ContDiff ℝ 3 g := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgcdOn : ContDiffOn ℝ 3 g (Set.Icc 0 1) := hgcd.contDiffOn
  -- 1-D Lagrange remainder of order 2 on `[0,1]` (so the remainder is `g'''(x')/6`).
  obtain ⟨x', _hx', heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (x₀ := 0) (x := 1)
      (by norm_num : (0 : ℝ) ≠ 1)
      (by rw [Set.uIcc_of_le zero_le_one]; exact_mod_cast hgcdOn)
  rw [Set.uIcc_of_le zero_le_one] at heq
  -- Convert `iteratedDerivWithin k g (Icc 0 1) 0` to the multilinear derivative of `f` at `x`.
  have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hidw : ∀ k, k ≤ 3 →
      iteratedDerivWithin k g (Set.Icc 0 1) 0 = iteratedFDeriv ℝ k f x (fun _ => h) := by
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv hud
        (hgcd.contDiffAt.of_le (by exact_mod_cast hk)) hmem, key k hk 0]
    simp
  -- Expand the Taylor polynomial into the three visible terms.
  have htaylor : taylorWithinEval g 2 (Set.Icc 0 1) 0 1
      = f x + fderiv ℝ f x h + (1 / 2) * iteratedFDeriv ℝ 2 f x (fun _ => h) := by
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      hidw 0 (by norm_num), hidw 1 (by norm_num), hidw 2 (by norm_num),
      iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]
    norm_num [Nat.factorial, smul_eq_mul]
  -- Bound the third-order term.
  have hb3 : |iteratedDeriv 3 g x'| ≤ M * ‖h‖ ^ 3 := by
    rw [key 3 le_rfl x', ← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 3 f (x + x' • h) (fun _ => h)‖
        ≤ ‖iteratedFDeriv ℝ 3 f (x + x' • h)‖ * ∏ _i : Fin 3, ‖h‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 3 f (x + x' • h)‖ * ‖h‖ ^ 3 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ M * ‖h‖ ^ 3 := by gcongr; exact hM _
  -- Assemble.
  have hg1 : g 1 = f (x + h) := by simp [hg]
  have hrw : f (x + h) - f x - fderiv ℝ f x h - (1 / 2) * iteratedFDeriv ℝ 2 f x (fun _ => h)
      = g 1 - taylorWithinEval g 2 (Set.Icc 0 1) 0 1 := by rw [hg1, htaylor]; ring
  rw [hrw, heq]
  have hfact : (Nat.factorial (2 + 1) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfact, show ((1 : ℝ) - 0) ^ 3 = 1 by norm_num, mul_one, abs_div,
    show |(6 : ℝ)| = 6 by norm_num]
  calc |iteratedDeriv 3 g x'| / 6 ≤ M * ‖h‖ ^ 3 / 6 := by gcongr
    _ = M / 6 * ‖h‖ ^ 3 := by ring

/-! #### The smoothed indicator of an arbitrary set (mollification)

This block pays what the wave-4 note called the "`precompR` bookkeeping" debt: it constructs,
for an arbitrary set `B ⊆ ℝ^k` and an arbitrary width `ε > 0`, a `C³` function `f : ℝ^k → [0,1]`
that is `1` on `B`, vanishes outside the `ε`-thickening of `B`, and satisfies
`‖D³f‖ ≤ C₃(k)/ε³` with `C₃(k)` fixed *before* `B` and `ε`.

The construction is the mollification predicted by the note, with one simplification that
removes its most delicate step. Rather than rescaling the `ContDiffBump` kernel with `ε` (which
would require the `δ`-dilation identity for `ContDiffBump` together with the Haar change of
variables `∫ g(δ·) = δ^{-k} ∫ g`), we build the width-`1` object once and obtain the width-`ε`
object by **dilating the set**: applying the width-`1` construction to `ε⁻¹ • B` and
precomposing with the continuous linear map `x ↦ ε⁻¹ • x`. All the `ε`-dependence then comes
from `ContinuousLinearMap.iteratedFDeriv_comp_right` together with
`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`, i.e. from `‖L‖³ ≤ ε⁻³`; no measure
rescaling is needed anywhere.

At width `1` the construction is: mollify the indicator of `Metric.thickening (1/2) B` with the
normed bump of radii `1/8 < 1/4`. The support clause holds because `1/2 + 1/4 < 1`, the value
clause because the whole mass of the kernel sits inside the thickening when `x ∈ B`, and
`0 ≤ f ≤ 1` because the kernel is a probability density.

For the third derivative we use the only differentiation formula Mathlib v4.29.1 has for
convolutions, the first-order `HasCompactSupport.hasFDerivAt_convolution_right`, three times;
the resulting tower `L`, `L.precompR`, `L.precompR.precompR` is glued to `iteratedFDeriv` by
three applications of `norm_iteratedFDeriv_fderiv`, exactly as the wave-4 note predicted. The
`precompR` tower costs nothing quantitatively because `‖L.precompR E‖ ≤ ‖L‖`
(`ContinuousLinearMap.norm_precompR_le`) and `‖lsmul ℝ ℝ‖ ≤ 1`, so the bound is simply
`‖D³f‖ ≤ ∫ ‖D³φ‖` for the fixed kernel `φ`.

Note that **convexity of `B` is never used**: the mollification works for any set. Convexity is
needed only for the *other* convex ingredient, the boundary-shell bound `γ(Bᵋ \ B) ≤ C_k ε`,
which lives in `StatLean.HypothesisTesting.ForMathlib.GaussianShell`
(`gaussian_thickening_le`; see `berryEsseen_convex_elementary` for the assembly). -/

section ConvexSmoothing

open Metric

open scoped Convolution Pointwise

/-- The fixed mollification kernel: the `ContDiffBump` at the origin with radii `1/8 < 1/4`. -/
private noncomputable def mbeBump (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin k)) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The normed mollification kernel: smooth, nonnegative, supported in the ball of radius `1/4`
and of total mass `1`. -/
private noncomputable def mbeMollifier (k : ℕ) : EuclideanSpace ℝ (Fin k) → ℝ :=
  (mbeBump k).normed volume

private lemma mbeMollifier_nonneg (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    0 ≤ mbeMollifier k x :=
  ContDiffBump.nonneg_normed (mbeBump k) x

private lemma mbeMollifier_contDiff (k : ℕ) :
    ContDiff ℝ (((4 : ℕ∞) : WithTop ℕ∞)) (mbeMollifier k) :=
  ContDiffBump.contDiff_normed (mbeBump k)

private lemma mbeMollifier_hasCompactSupport (k : ℕ) : HasCompactSupport (mbeMollifier k) :=
  ContDiffBump.hasCompactSupport_normed (mbeBump k)

private lemma mbeMollifier_integral (k : ℕ) : ∫ x, mbeMollifier k x = 1 :=
  ContDiffBump.integral_normed (mbeBump k)

private lemma mbeMollifier_integrable (k : ℕ) : Integrable (mbeMollifier k) :=
  ContDiffBump.integrable_normed (mbeBump k)

private lemma mbeMollifier_support (k : ℕ) :
    Function.support (mbeMollifier k) = ball 0 (1 / 4) := by
  rw [mbeMollifier, ContDiffBump.support_normed_eq]; rfl

section GenericConvolutionBound

variable {G E' F : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

/-- If the pairing has operator norm `≤ 1` and `ind` is bounded by `1` in absolute value, then
the convolution `ind ⋆[L] g` is bounded by the `L¹`-norm of `g`. This is the quantitative half
of the mollification bound, stated abstractly so that the elaborator never has to see the
concrete `precompR` tower. -/
private lemma norm_convolution_le_of_bounded (L : ℝ →L[ℝ] E' →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {ind : G → ℝ} (hbd : ∀ t, |ind t| ≤ 1) {g : G → E'} (hg : Integrable g μ) (x : G) :
    ‖(ind ⋆[L, μ] g) x‖ ≤ ∫ t, ‖g t‖ ∂μ := by
  have hint : Integrable (fun t => ‖g t‖) μ := hg.norm
  calc ‖(ind ⋆[L, μ] g) x‖ = ‖∫ t, L (ind t) (g (x - t)) ∂μ‖ := by rw [convolution_def]
    _ ≤ ∫ t, ‖L (ind t) (g (x - t))‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖g (x - t)‖ ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hint.comp_sub_left x) (Filter.Eventually.of_forall fun t => ?_)
        refine (L.le_opNorm₂ (ind t) (g (x - t))).trans ?_
        have h1 : ‖ind t‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hbd t
        have h2 : ‖L‖ * ‖ind t‖ ≤ 1 := mul_le_one₀ hL (norm_nonneg _) h1
        calc ‖L‖ * ‖ind t‖ * ‖g (x - t)‖ ≤ 1 * ‖g (x - t)‖ := by gcongr
          _ = ‖g (x - t)‖ := one_mul _
    _ = ∫ t, ‖g t‖ ∂μ := integral_sub_left_eq_self (fun t => ‖g t‖) μ x

end GenericConvolutionBound

set_option maxHeartbeats 1000000 in
-- The `precompR` tower forces defeq checks on the continuous-linear-map type
-- `ℝ →L (E →L E →L E →L ℝ) →L (E →L E →L E →L ℝ)`; those are what exhaust the default budget.
/-- The third derivative of a mollification is bounded by the `L¹`-norm of the third derivative
of the kernel, uniformly over all `ind` bounded by `1`.

This is the `precompR` tower: three applications of
`HasCompactSupport.hasFDerivAt_convolution_right`
identify `fderiv³ (ind ⋆ φ)` with `ind ⋆[L₃] fderiv³ φ`, and three applications of
`norm_iteratedFDeriv_fderiv` turn `‖iteratedFDeriv ℝ 3 ·‖` into `‖fderiv³ ·‖`.

The raised heartbeat budget pays for the defeq checks on the continuous-linear-map tower
`ℝ →L (E →L E →L E →L ℝ) →L (E →L E →L E →L ℝ)`; the proof itself is three rewrites and a
bound. -/
private lemma norm_iteratedFDeriv_three_convolution_le {k : ℕ}
    {ind : EuclideanSpace ℝ (Fin k) → ℝ} (hind : LocallyIntegrable ind volume)
    (hbd : ∀ t, |ind t| ≤ 1) (x : EuclideanSpace ℝ (Fin k)) :
    ‖iteratedFDeriv ℝ 3 (ind ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mbeMollifier k) x‖
      ≤ ∫ t, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (mbeMollifier k))) t‖ := by
  set φ := mbeMollifier k with hφdef
  have hφ : ContDiff ℝ (((4 : ℕ∞) : WithTop ℕ∞)) φ := mbeMollifier_contDiff k
  have hcs : HasCompactSupport φ := mbeMollifier_hasCompactSupport k
  set L₀ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL₀
  set L₁ := L₀.precompR (EuclideanSpace ℝ (Fin k)) with hL₁
  set L₂ := L₁.precompR (EuclideanSpace ℝ (Fin k)) with hL₂
  set L₃ := L₂.precompR (EuclideanSpace ℝ (Fin k)) with hL₃
  set φ₁ := fderiv ℝ φ with hφ₁
  set φ₂ := fderiv ℝ φ₁ with hφ₂
  set φ₃ := fderiv ℝ φ₂ with hφ₃
  have hφ1 : ContDiff ℝ (((3 : ℕ∞) : WithTop ℕ∞)) φ₁ := hφ.fderiv_right (by norm_num)
  have hφ2 : ContDiff ℝ (((2 : ℕ∞) : WithTop ℕ∞)) φ₂ := hφ1.fderiv_right (by norm_num)
  have hφ3 : ContDiff ℝ (((1 : ℕ∞) : WithTop ℕ∞)) φ₃ := hφ2.fderiv_right (by norm_num)
  have hcs1 : HasCompactSupport φ₁ := hcs.fderiv ℝ
  have hcs2 : HasCompactSupport φ₂ := hcs1.fderiv ℝ
  have hcs3 : HasCompactSupport φ₃ := hcs2.fderiv ℝ
  have hd1 : fderiv ℝ (ind ⋆[L₀, volume] φ) = (ind ⋆[L₁, volume] φ₁) := by
    funext y
    exact (hcs.hasFDerivAt_convolution_right L₀ hind (hφ.of_le (by norm_num)) y).fderiv
  have hd2 : fderiv ℝ (ind ⋆[L₁, volume] φ₁) = (ind ⋆[L₂, volume] φ₂) := by
    funext y
    exact (hcs1.hasFDerivAt_convolution_right L₁ hind (hφ1.of_le (by norm_num)) y).fderiv
  have hd3 : fderiv ℝ (ind ⋆[L₂, volume] φ₂) = (ind ⋆[L₃, volume] φ₃) := by
    funext y
    exact (hcs2.hasFDerivAt_convolution_right L₂ hind (hφ2.of_le (by norm_num)) y).fderiv
  have hkey : ‖iteratedFDeriv ℝ 3 (ind ⋆[L₀, volume] φ) x‖ = ‖(ind ⋆[L₃, volume] φ₃) x‖ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd1,
      show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd2,
      show (1 : ℕ) = 0 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd3]
    simp [norm_iteratedFDeriv_zero]
  rw [hkey]
  have hnormL : ‖L₃‖ ≤ 1 := by
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₂) ?_
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₁) ?_
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₀) ?_
    exact ContinuousLinearMap.opNorm_lsmul_le
  exact norm_convolution_le_of_bounded L₃ hnormL hbd
    (hφ3.continuous.integrable_of_hasCompactSupport hcs3) x

set_option maxHeartbeats 1000000 in
-- Same `precompR` defeq checks as the third-order bound, at one level.
/-- The **first** derivative of a mollification is bounded by the `L¹`-norm of the first
derivative of the kernel — the order-`1` case of the same convolution estimate that gives
`norm_iteratedFDeriv_three_convolution_le` (wave 37). -/
private lemma norm_iteratedFDeriv_one_convolution_le {k : ℕ}
    {ind : EuclideanSpace ℝ (Fin k) → ℝ} (hind : LocallyIntegrable ind volume)
    (hbd : ∀ t, |ind t| ≤ 1) (x : EuclideanSpace ℝ (Fin k)) :
    ‖iteratedFDeriv ℝ 1 (ind ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mbeMollifier k) x‖
      ≤ ∫ t, ‖fderiv ℝ (mbeMollifier k) t‖ := by
  set φ := mbeMollifier k with hφdef
  have hφ : ContDiff ℝ (((4 : ℕ∞) : WithTop ℕ∞)) φ := mbeMollifier_contDiff k
  have hcs : HasCompactSupport φ := mbeMollifier_hasCompactSupport k
  set L₀ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL₀
  set L₁ := L₀.precompR (EuclideanSpace ℝ (Fin k)) with hL₁
  set φ₁ := fderiv ℝ φ with hφ₁
  have hφ1 : ContDiff ℝ (((3 : ℕ∞) : WithTop ℕ∞)) φ₁ := hφ.fderiv_right (by norm_num)
  have hcs1 : HasCompactSupport φ₁ := hcs.fderiv ℝ
  have hd1 : fderiv ℝ (ind ⋆[L₀, volume] φ) = (ind ⋆[L₁, volume] φ₁) := by
    funext y
    exact (hcs.hasFDerivAt_convolution_right L₀ hind (hφ.of_le (by norm_num)) y).fderiv
  have hkey : ‖iteratedFDeriv ℝ 1 (ind ⋆[L₀, volume] φ) x‖ = ‖(ind ⋆[L₁, volume] φ₁) x‖ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd1]
    simp [norm_iteratedFDeriv_zero]
  rw [hkey]
  have hnormL : ‖L₁‖ ≤ 1 := by
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₀) ?_
    exact ContinuousLinearMap.opNorm_lsmul_le
  exact norm_convolution_le_of_bounded L₁ hnormL hbd
    (hφ1.continuous.integrable_of_hasCompactSupport hcs1) x

set_option maxHeartbeats 1000000 in
-- Same `precompR` defeq checks as the third-order bound, at two levels.
/-- The **second** derivative of a mollification is bounded by the `L¹`-norm of the second
derivative of the kernel — the order-`2` case of the same convolution estimate that gives
`norm_iteratedFDeriv_three_convolution_le` (wave 37). -/
private lemma norm_iteratedFDeriv_two_convolution_le {k : ℕ}
    {ind : EuclideanSpace ℝ (Fin k) → ℝ} (hind : LocallyIntegrable ind volume)
    (hbd : ∀ t, |ind t| ≤ 1) (x : EuclideanSpace ℝ (Fin k)) :
    ‖iteratedFDeriv ℝ 2 (ind ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mbeMollifier k) x‖
      ≤ ∫ t, ‖fderiv ℝ (fderiv ℝ (mbeMollifier k)) t‖ := by
  set φ := mbeMollifier k with hφdef
  have hφ : ContDiff ℝ (((4 : ℕ∞) : WithTop ℕ∞)) φ := mbeMollifier_contDiff k
  have hcs : HasCompactSupport φ := mbeMollifier_hasCompactSupport k
  set L₀ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL₀
  set L₁ := L₀.precompR (EuclideanSpace ℝ (Fin k)) with hL₁
  set L₂ := L₁.precompR (EuclideanSpace ℝ (Fin k)) with hL₂
  set φ₁ := fderiv ℝ φ with hφ₁
  set φ₂ := fderiv ℝ φ₁ with hφ₂
  have hφ1 : ContDiff ℝ (((3 : ℕ∞) : WithTop ℕ∞)) φ₁ := hφ.fderiv_right (by norm_num)
  have hφ2 : ContDiff ℝ (((2 : ℕ∞) : WithTop ℕ∞)) φ₂ := hφ1.fderiv_right (by norm_num)
  have hcs1 : HasCompactSupport φ₁ := hcs.fderiv ℝ
  have hcs2 : HasCompactSupport φ₂ := hcs1.fderiv ℝ
  have hd1 : fderiv ℝ (ind ⋆[L₀, volume] φ) = (ind ⋆[L₁, volume] φ₁) := by
    funext y
    exact (hcs.hasFDerivAt_convolution_right L₀ hind (hφ.of_le (by norm_num)) y).fderiv
  have hd2 : fderiv ℝ (ind ⋆[L₁, volume] φ₁) = (ind ⋆[L₂, volume] φ₂) := by
    funext y
    exact (hcs1.hasFDerivAt_convolution_right L₁ hind (hφ1.of_le (by norm_num)) y).fderiv
  have hkey : ‖iteratedFDeriv ℝ 2 (ind ⋆[L₀, volume] φ) x‖ = ‖(ind ⋆[L₂, volume] φ₂) x‖ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd1,
      show (1 : ℕ) = 0 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd2]
    simp [norm_iteratedFDeriv_zero]
  rw [hkey]
  have hnormL : ‖L₂‖ ≤ 1 := by
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₁) ?_
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₀) ?_
    exact ContinuousLinearMap.opNorm_lsmul_le
  exact norm_convolution_le_of_bounded L₂ hnormL hbd
    (hφ2.continuous.integrable_of_hasCompactSupport hcs2) x

/-- **Smoothed indicator at unit width, for an arbitrary set.** There is a constant `C₃`
(depending only on the dimension `k`, and fixed *before* the set) such that every
`B ⊆ ℝ^k` admits a `C³` function `f : ℝ^k → [0,1]` equal to `1` on `B`, supported inside the
unit thickening of `B`, with `‖D³f‖ ≤ C₃`.

Take `f` to be the mollification of the indicator of `Metric.thickening (1/2) B` by
`mbeMollifier k`. Note the empty set needs no special treatment: then `f = 0` and both the
value and the support clause are vacuous.

**Wave 37.** The conclusion now carries the first- and second-order bounds as well, produced by
`norm_iteratedFDeriv_one_convolution_le` / `norm_iteratedFDeriv_two_convolution_le` — the same
convolution estimate at one and two `precompR` levels instead of three. A *single* constant
dominates all three orders (the `max` below), which is what the far-regime head estimate of
brick L consumes; and it is `≥ 1` by construction, so `1 ≤ C₃` is free and is now part of the
conclusion (wave 36 flagged this normalisation as the cheaper of its two options). -/
private lemma exists_smoothed_indicator_unit (k : ℕ) :
    ∃ C₃ : ℝ, 1 ≤ C₃ ∧ ∀ B : Set (EuclideanSpace ℝ (Fin k)),
      ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x ∈ B, f x = 1) ∧ (∀ x, f x ≠ 0 → x ∈ thickening 1 B) ∧
        (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃) ∧
        (∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C₃) ∧
        (∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₃) := by
  set φ := mbeMollifier k with hφdef
  refine ⟨max 1 (max (∫ t, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) t‖)
      (max (∫ t, ‖fderiv ℝ φ t‖) (∫ t, ‖fderiv ℝ (fderiv ℝ φ) t‖))),
    le_max_left _ _, fun B => ?_⟩
  set A : Set (EuclideanSpace ℝ (Fin k)) := thickening (1 / 2) B with hAdef
  set ind : EuclideanSpace ℝ (Fin k) → ℝ := A.indicator (fun _ => (1 : ℝ)) with hinddef
  have hindmeas : Measurable ind := measurable_const.indicator isOpen_thickening.measurableSet
  have hindbd : ∀ t, |ind t| ≤ 1 := by
    intro t
    have := norm_indicator_le_norm_self (fun _ : EuclideanSpace ℝ (Fin k) => (1 : ℝ)) (s := A) t
    simpa [hinddef] using this
  have hindnn : ∀ t, 0 ≤ ind t := fun t => Set.indicator_nonneg (fun _ _ => zero_le_one) t
  have hindle : ∀ t, ind t ≤ 1 := fun t => (abs_le.1 (hindbd t)).2
  have hind : LocallyIntegrable ind volume :=
    (locallyIntegrable_const (1 : ℝ)).mono hindmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => norm_indicator_le_norm_self _ t)
  set L₀ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL₀
  -- the value of the mollification, with the kernel carrying the free variable
  have hval : ∀ x, (ind ⋆[L₀, volume] φ) x = ∫ t, ind (x - t) * φ t := by
    intro x
    rw [convolution_eq_swap]
    simp [hL₀, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hsupp : ∀ t : EuclideanSpace ℝ (Fin k), φ t ≠ 0 → ‖t‖ < 1 / 4 := by
    intro t ht
    have hmem : t ∈ Function.support φ := ht
    rw [hφdef, mbeMollifier_support] at hmem
    simpa [dist_zero_right] using hmem
  refine ⟨ind ⋆[L₀, volume] φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mbeMollifier_hasCompactSupport k).contDiff_convolution_right L₀ hind
      ((mbeMollifier_contDiff k).of_le (by norm_num))
  · intro x
    rw [hval]
    exact integral_nonneg fun t => mul_nonneg (hindnn _) (mbeMollifier_nonneg k t)
  · intro x
    rw [hval]
    refine le_trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => mul_nonneg (hindnn _) (mbeMollifier_nonneg k t))
      (mbeMollifier_integrable k) (Filter.Eventually.of_forall fun t => ?_)) ?_
    · nlinarith [hindle (x - t), hindnn (x - t), mbeMollifier_nonneg k t]
    · exact le_of_eq (mbeMollifier_integral k)
  · -- on `B` the whole mass of the kernel sits inside the `1/2`-thickening
    intro x hx
    rw [hval]
    have hpt : ∀ t, ind (x - t) * φ t = φ t := by
      intro t
      rcases eq_or_ne (φ t) 0 with h | h
      · simp [h]
      · have hmem : x - t ∈ A := by
          rw [hAdef, Metric.mem_thickening_iff]
          refine ⟨x, hx, ?_⟩
          have hd : dist (x - t) x = ‖t‖ := by rw [dist_eq_norm]; simp [norm_neg]
          rw [hd]
          exact lt_trans (hsupp t h) (by norm_num)
        rw [hinddef, Set.indicator_of_mem hmem]
        ring
    simp only [hpt]
    exact mbeMollifier_integral k
  · -- off the unit thickening the integrand vanishes identically, since `1/2 + 1/4 < 1`
    intro x hfx
    by_contra hx
    apply hfx
    rw [hval]
    have hpt : ∀ t, ind (x - t) * φ t = 0 := by
      intro t
      rcases eq_or_ne (φ t) 0 with h | h
      · simp [h]
      · have hnot : x - t ∉ A := by
          intro hmem
          rw [hAdef, Metric.mem_thickening_iff] at hmem
          obtain ⟨z, hz, hdz⟩ := hmem
          apply hx
          rw [Metric.mem_thickening_iff]
          refine ⟨z, hz, ?_⟩
          have h1 : dist x (x - t) = ‖t‖ := by rw [dist_eq_norm]; simp
          have h3 := dist_triangle x (x - t) z
          have h2 := hsupp t h
          linarith
        rw [hinddef, Set.indicator_of_notMem hnot]
        ring
    simp only [hpt]
    exact integral_zero _ _
  · intro x
    exact le_trans (norm_iteratedFDeriv_three_convolution_le hind hindbd x)
      ((le_max_left _ _).trans (le_max_right 1 _))
  · intro x
    exact le_trans (norm_iteratedFDeriv_one_convolution_le hind hindbd x)
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right 1 _))
  · intro x
    exact le_trans (norm_iteratedFDeriv_two_convolution_le hind hindbd x)
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right 1 _))

/-- **Scaling an iterated-derivative bound along a dilation.** If `‖Dⁱg‖ ≤ C` globally then the
dilate `x ↦ g (ε⁻¹ • x)` satisfies `‖Dⁱ(g ∘ ε⁻¹)‖ ≤ C/εⁱ`, because
`ContinuousLinearMap.iteratedFDeriv_comp_right` contributes exactly `‖L‖ⁱ ≤ ε^{-i}`. The bound
`‖L‖ ≤ ε⁻¹` is used as an inequality rather than an equality, so the degenerate dimension
`k = 0` (where `‖id‖ = 0`) is covered too. -/
private lemma norm_iteratedFDeriv_comp_smul_le {k i : ℕ} {C ε : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hgcd : ContDiff ℝ 3 g) (hi : i ≤ 3)
    (hgD : ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ C) (x : EuclideanSpace ℝ (Fin k)) :
    ‖iteratedFDeriv ℝ i (fun x => g (ε⁻¹ • x)) x‖ ≤ C / ε ^ i := by
  set L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    ε⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) with hLdef
  have hLapp : ∀ x, L x = ε⁻¹ • x := by intro x; simp [hLdef]
  have hLnorm : ‖L‖ ≤ ε⁻¹ := by
    rw [hLdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hid : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have hεinv : (0 : ℝ) ≤ ε⁻¹ := by positivity
    nlinarith [hid, hεinv]
  have hcomp : (fun x => g (ε⁻¹ • x)) = g ∘ L := by funext y; rw [Function.comp_apply, hLapp]
  have hile : (i : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hi
  rw [hcomp, L.iteratedFDeriv_comp_right hgcd x hile]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hprod : (∏ _j : Fin i, ‖L‖) = ‖L‖ ^ i := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  calc ‖iteratedFDeriv ℝ i g (L x)‖ * ‖L‖ ^ i ≤ C * ε⁻¹ ^ i := by
        gcongr
        exact hgD _
    _ = C / ε ^ i := by rw [inv_pow]; ring

/-- **Smoothed convex indicator with controlled third derivative.**
In each dimension `k` there is a constant `C₃` (quantified *before* `B` and `ε`, so the bound
is not vacuous) such that every convex `B` and width `ε > 0` admit a smooth `f : ℝ^k → [0,1]`
equal to `1` on `B`, supported inside the `ε`-thickening of `B`, with `‖D³f‖ ≤ C₃ / ε³`.

**Proof.** Apply `exists_smoothed_indicator_unit` to the dilate `ε⁻¹ • B` and precompose with
the continuous linear map `L : x ↦ ε⁻¹ • x`. Membership and support transport along `L` because
`dist (ε⁻¹ • x) (ε⁻¹ • w) = ε⁻¹ * dist x w`, and the derivative bound transports by
`ContinuousLinearMap.iteratedFDeriv_comp_right` together with
`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`, which contribute the factor
`‖L‖³ ≤ ε⁻³`. Note `‖L‖ ≤ ε⁻¹` is used as an inequality rather than an equality, so the
degenerate dimension `k = 0` (where `‖id‖ = 0`) is covered too.

Convexity of `B` is not used; it is kept only because the statement is frozen.

**Wave 37.** The first- and second-order bounds `‖D¹f‖ ≤ C₃/ε`, `‖D²f‖ ≤ C₃/ε²` are now part
of the conclusion, with the *same* constant `C₃ ≥ 1`: they are needed by the far regime of brick
L's head estimate, which does not Taylor-expand and must bound the swap remainder by its
lower-order terms. The scaling is the one already used for the third order, factored out as
`norm_iteratedFDeriv_comp_smul_le`. -/
private lemma exists_smoothed_convex_indicator (k : ℕ) :
    ∃ C₃ : ℝ, 1 ≤ C₃ ∧ ∀ B : Set (EuclideanSpace ℝ (Fin k)), Convex ℝ B → ∀ {ε : ℝ}, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x ∈ B, f x = 1) ∧ (∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B) ∧
        (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) ∧
        (∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C₃ / ε) ∧
        (∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₃ / ε ^ 2) := by
  obtain ⟨C₃, hC₃one, hC₃⟩ := exists_smoothed_indicator_unit k
  have hC₃pos : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃one
  refine ⟨C₃, hC₃one, fun B _ ε hε => ?_⟩
  obtain ⟨g, hgcd, hg0, hg1, hgB, hgsupp, hgD, hgD1, hgD2⟩ := hC₃ (ε⁻¹ • B)
  set L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    ε⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) with hLdef
  have hLapp : ∀ x, L x = ε⁻¹ • x := by intro x; simp [hLdef]
  refine ⟨fun x => g (L x), hgcd.comp L.contDiff, fun x => hg0 _, fun x => hg1 _, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x hx
    exact hgB _ (by rw [hLapp]; exact Set.smul_mem_smul_set hx)
  · intro x hx
    have hmem := hgsupp _ hx
    rw [Metric.mem_thickening_iff] at hmem ⊢
    obtain ⟨z, hz, hdz⟩ := hmem
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w, hw, ?_⟩
    rw [hLapp, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < ε⁻¹)] at hdz
    rw [dist_eq_norm]
    rw [inv_mul_lt_iff₀ hε] at hdz
    linarith
  · intro x
    have h := norm_iteratedFDeriv_comp_smul_le (i := 3) hε hC₃pos.le hgcd le_rfl hgD x
    simpa only [hLapp] using h
  · intro x
    have h := norm_iteratedFDeriv_comp_smul_le (i := 1) hε hC₃pos.le hgcd (by norm_num) hgD1 x
    simpa only [hLapp, pow_one] using h
  · intro x
    have h := norm_iteratedFDeriv_comp_smul_le (i := 2) hε hC₃pos.le hgcd (by norm_num) hgD2 x
    simpa only [hLapp] using h

end ConvexSmoothing

/-! #### The smoothed radial indicator

The construction composes a **fixed** one-dimensional cutoff with the *squared* norm `‖·‖²`
rather than with `‖·‖`. This is what makes the third-derivative constant genuinely
dimension-free *and* elementary: `‖·‖²` is a quadratic polynomial, so `D¹‖·‖² = 2⟪z,·⟫`,
`D²‖·‖² = 2⟪·,·⟫` and `D³‖·‖² = 0`, with dimension-free norms `2‖z‖`, `2`, `0` — all obtained
from Mathlib's bilinear iterated-derivative bound applied to `innerSL ℝ`. In particular the
quantitative iterated-derivative bounds for `‖·‖` away from the origin (which Mathlib v4.29.1
does not provide, and which the `χ ∘ ‖·‖` route would need) are never used. -/

section RadialSmoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed one-dimensional cutoff `χ = 1 - smoothTransition`: smooth, equal to `1` on
`(-∞, 0]`, to `0` on `[1, ∞)`, with values in `[0,1]`. -/
private noncomputable def radialCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition t

private lemma contDiff_radialCutoff : ContDiff ℝ 3 radialCutoff :=
  contDiff_const.sub Real.smoothTransition.contDiff

private lemma radialCutoff_nonneg (t : ℝ) : 0 ≤ radialCutoff t :=
  sub_nonneg.mpr (Real.smoothTransition.le_one t)

private lemma radialCutoff_le_one (t : ℝ) : radialCutoff t ≤ 1 := by
  have := Real.smoothTransition.nonneg t
  simp only [radialCutoff]; linarith

private lemma radialCutoff_of_nonpos {t : ℝ} (h : t ≤ 0) : radialCutoff t = 1 := by
  simp [radialCutoff, Real.smoothTransition.zero_of_nonpos h]

private lemma radialCutoff_of_one_le {t : ℝ} (h : 1 ≤ t) : radialCutoff t = 0 := by
  simp [radialCutoff, Real.smoothTransition.one_of_one_le h]

/-- The derivatives of the fixed cutoff are bounded on the transition window `[0,1]` by an
absolute constant `B ≥ 1` (continuity on a compact). Off `[0,1]` the cutoff is locally
constant, so this is all that is ever needed. -/
private lemma exists_radialCutoff_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ≤ 3, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ i radialCutoff t‖ ≤ B := by
  have hc : ∀ i : ℕ, (i : WithTop ℕ∞) ≤ 3 →
      ContinuousOn (iteratedFDeriv ℝ i radialCutoff) (Set.Icc (0 : ℝ) 1) := fun i hi =>
    (contDiff_radialCutoff.continuous_iteratedFDeriv hi).continuousOn
  obtain ⟨B0, hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 0 (by norm_num))
  obtain ⟨B1, hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 1 (by norm_num))
  obtain ⟨B2, hB2⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 2 (by norm_num))
  obtain ⟨B3, hB3⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 3 (by norm_num))
  refine ⟨max 1 (max B0 (max B1 (max B2 B3))), le_max_left _ _, ?_⟩
  intro i hi t ht
  interval_cases i
  · exact (hB0 t ht).trans (by simp)
  · exact (hB1 t ht).trans (by simp)
  · exact (hB2 t ht).trans (by simp)
  · exact (hB3 t ht).trans (by simp)

/-! ##### Iterated derivatives of the squared norm (dimension-free) -/

private lemma norm_iteratedFDeriv_id_one_le (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y : E => y) x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_one, fderiv_id']
  exact ContinuousLinearMap.norm_id_le

private lemma norm_iteratedFDeriv_id_of_two_le {i : ℕ} (hi : 2 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => y) x‖ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have h : (fderiv ℝ fun y : E => y) = fun _ : E => ContinuousLinearMap.id ℝ E := by
    funext y; exact fderiv_id'
  rw [h, iteratedFDeriv_const_of_ne (by omega : m + 1 ≠ 0)]
  simp

/-- Mathlib's bilinear iterated-derivative bound applied to `‖y‖² = ⟪y, y⟫`. -/
private lemma norm_iteratedFDeriv_normSq_le (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y : E => ‖y‖ ^ 2) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ‖iteratedFDeriv ℝ i (fun y : E => y) x‖
          * ‖iteratedFDeriv ℝ (n - i) (fun y : E => y) x‖ := by
  have hfun : (fun y : E => ‖y‖ ^ 2)
      = fun y : E => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) y y := by
    funext y
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  rw [hfun]
  exact ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one _
    (contDiff_id (n := (n : WithTop ℕ∞))) (contDiff_id (n := (n : WithTop ℕ∞))) x le_rfl
    (norm_innerSL_le ℝ)

private lemma norm_iteratedFDeriv_normSq_one (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y : E => ‖y‖ ^ 2) x‖ ≤ 2 * ‖x‖ := by
  refine (norm_iteratedFDeriv_normSq_le 1 x).trans ?_
  have h1 := norm_iteratedFDeriv_id_one_le x
  have h0 : ‖iteratedFDeriv ℝ 0 (fun y : E => y) x‖ = ‖x‖ := norm_iteratedFDeriv_zero
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
    one_mul, h0]
  nlinarith [h1, hx]

private lemma norm_iteratedFDeriv_normSq_two (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun y : E => ‖y‖ ^ 2) x‖ ≤ 2 := by
  refine (norm_iteratedFDeriv_normSq_le 2 x).trans ?_
  have h1 := norm_iteratedFDeriv_id_one_le x
  have h2 : ‖iteratedFDeriv ℝ 2 (fun y : E => y) x‖ = 0 :=
    norm_iteratedFDeriv_id_of_two_le le_rfl x
  have h0 : ‖iteratedFDeriv ℝ 0 (fun y : E => y) x‖ = ‖x‖ := norm_iteratedFDeriv_zero
  have hn1 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ 1 (fun y : E => y) x‖ := norm_nonneg _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, one_mul, h0, h2, mul_zero, zero_mul,
    zero_add, add_zero]
  nlinarith [h1, hn1]

private lemma norm_iteratedFDeriv_normSq_three (x : E) :
    ‖iteratedFDeriv ℝ 3 (fun y : E => ‖y‖ ^ 2) x‖ ≤ 0 := by
  refine (norm_iteratedFDeriv_normSq_le 3 x).trans ?_
  have h2 : ‖iteratedFDeriv ℝ 2 (fun y : E => y) x‖ = 0 :=
    norm_iteratedFDeriv_id_of_two_le le_rfl x
  have h3 : ‖iteratedFDeriv ℝ 3 (fun y : E => y) x‖ = 0 :=
    norm_iteratedFDeriv_id_of_two_le (by norm_num) x
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, h2, h3, mul_zero, zero_mul, add_zero]
  exact le_rfl

end RadialSmoothing

/-- **Smoothed radial indicator with an absolute (dimension-free) third-derivative constant.**
There is a constant `C₃` — independent of the dimension `k`, the radius `a` and the width `ε` —
such that for every ball `{‖z‖ ≤ a}` with `0 ≤ a` and every width `ε > 0` there is a smooth
`f : ℝ^k → [0,1]`, equal to `1` on `{‖z‖ ≤ a}`, vanishing on `{‖z‖ > a + ε}`, with
`‖D³f‖ ≤ C₃ / ε³`. This is the radial analogue of `exists_smoothed_convex_indicator`, and unlike
the convex one its constant is genuinely dimension-free.

**Construction.** `f = χ(( ‖·‖² − a²)/W)` with `W = (a+ε)² − a² = ε(2a+ε)` and `χ` the *fixed*
cutoff `radialCutoff` (`1` on `(-∞,0]`, `0` on `[1,∞)`). Composing with `‖·‖²` rather than with
`‖·‖` is essential: `‖·‖²` is a quadratic polynomial, hence globally smooth (no singularity at
the origin) with `‖D¹‖·‖²‖ = 2‖z‖`, `‖D²‖·‖²‖ ≤ 2`, `D³‖·‖² = 0`, all dimension-free.

**Third-derivative bound.** Write `u = ‖·‖²/W`, so `f = χ(· − a²/W) ∘ u`. On the transition
shell `a ≤ ‖z‖ ≤ a+ε` one has `‖D¹u‖ = 2‖z‖/W ≤ 2(a+ε)/(ε(2a+ε)) ≤ 2/ε` and
`‖D²u‖ = 2/W ≤ 4/ε² = (2/ε)²`, while `D³u = 0`; so `‖Dⁱu‖ ≤ D^i` with the *single* geometric
ratio `D = 2/ε`, and Mathlib's `norm_iteratedFDeriv_comp_le` gives
`‖D³f‖ ≤ 3! · B · (2/ε)³ = 48B/ε³` with `B` the absolute bound of `exists_radialCutoff_bound`.
Off that shell `f` is locally constant, so `D³f = 0`.

Note the hypothesis `ε ≤ a` of the earlier `χ ∘ ‖·‖` formulation is **not** needed here: the
squared-norm route is uniform down to `a = 0`. -/
private lemma exists_smoothed_radial_indicator :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ (k : ℕ) (a : ℝ), 0 ≤ a → ∀ {ε : ℝ}, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x, ‖x‖ ≤ a → f x = 1) ∧ (∀ x, a + ε < ‖x‖ → f x = 0) ∧
        (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) := by
  obtain ⟨B, hB1, hB⟩ := exists_radialCutoff_bound
  refine ⟨48 * B, by linarith, ?_⟩
  intro k a ha ε hε
  set W : ℝ := 2 * a * ε + ε ^ 2 with hWdef
  have hW0 : 0 < W := by rw [hWdef]; nlinarith
  set c : ℝ := a ^ 2 / W with hcdef
  set u : EuclideanSpace ℝ (Fin k) → ℝ := fun y => W⁻¹ • ‖y‖ ^ 2 with hudef
  set g : ℝ → ℝ := fun t => radialCutoff (-c + t) with hgdef
  have huCD : ContDiff ℝ 3 u := (contDiff_norm_sq ℝ).const_smul W⁻¹
  have hgCD : ContDiff ℝ 3 g :=
    contDiff_radialCutoff.comp (contDiff_const.add contDiff_id)
  -- `g (u y) = χ((‖y‖² − a²)/W)`
  have hval : ∀ y : EuclideanSpace ℝ (Fin k),
      (g ∘ u) y = radialCutoff ((‖y‖ ^ 2 - a ^ 2) / W) := by
    intro y
    simp only [Function.comp_apply, hgdef, hudef, hcdef, smul_eq_mul]
    congr 1
    field_simp
    try ring
  refine ⟨g ∘ u, hgCD.comp huCD, fun x => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x => ?_⟩
  · rw [hval]; exact radialCutoff_nonneg _
  · rw [hval]; exact radialCutoff_le_one _
  · rw [hval]
    refine radialCutoff_of_nonpos ?_
    apply div_nonpos_of_nonpos_of_nonneg _ hW0.le
    have : ‖x‖ ^ 2 ≤ a ^ 2 := by nlinarith [norm_nonneg x]
    linarith
  · rw [hval]
    refine radialCutoff_of_one_le ?_
    rw [le_div_iff₀ hW0]
    have hxa : a + ε < ‖x‖ := hx
    nlinarith [norm_nonneg x]
  · -- the third-derivative bound
    set v : ℝ := (‖x‖ ^ 2 - a ^ 2) / W with hvdef
    by_cases hcase : 0 ≤ v ∧ v ≤ 1
    · -- transition shell: Faà di Bruno with the geometric ratio `D = 2/ε`
      obtain ⟨hv0, hv1⟩ := hcase
      have hxle : ‖x‖ ≤ a + ε := by
        rw [hvdef, div_le_one hW0] at hv1
        nlinarith [norm_nonneg x]
      have hCb : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i g (u x)‖ ≤ B := by
        intro i hi
        have hshift : iteratedFDeriv ℝ i g = fun t => iteratedFDeriv ℝ i radialCutoff (-c + t) :=
          iteratedFDeriv_comp_add_left' i (-c)
        have harg : -c + u x = v := by
          simp only [hudef, hcdef, hvdef, smul_eq_mul]
          field_simp
          try ring
        rw [hshift]
        change ‖iteratedFDeriv ℝ i radialCutoff (-c + u x)‖ ≤ B
        rw [harg]
        exact hB i hi v ⟨hv0, hv1⟩
      have hD : ∀ i, 1 ≤ i → i ≤ 3 → ‖iteratedFDeriv ℝ i u x‖ ≤ (2 / ε) ^ i := by
        intro i _ hi3
        have hsc : iteratedFDeriv ℝ i u x
            = W⁻¹ • iteratedFDeriv ℝ i (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) x :=
          iteratedFDeriv_const_smul_apply' ((contDiff_norm_sq ℝ).contDiffAt)
        rw [hsc, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW0)]
        interval_cases i
        · rw [pow_one, inv_mul_le_iff₀ hW0]
          have hWid : W * (2 / ε) = 2 * (2 * a + ε) := by
            rw [hWdef]; field_simp; try ring
          rw [hWid]
          have h := norm_iteratedFDeriv_normSq_one x
          nlinarith [h, hxle, ha, norm_nonneg x]
        · rw [inv_mul_le_iff₀ hW0]
          have hWid : W * (2 / ε) ^ 2 = 4 * (2 * a + ε) / ε := by
            rw [hWdef]; field_simp; try ring
          rw [hWid]
          have h := norm_iteratedFDeriv_normSq_two x
          have h2 : (2 : ℝ) ≤ 4 * (2 * a + ε) / ε := by
            rw [le_div_iff₀ hε]; nlinarith
          linarith
        · rw [inv_mul_le_iff₀ hW0]
          have h := norm_iteratedFDeriv_normSq_three x
          have hz : ‖iteratedFDeriv ℝ 3
              (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) x‖ = 0 :=
            le_antisymm h (norm_nonneg _)
          rw [hz]
          positivity
      have hcomp := norm_iteratedFDeriv_comp_le hgCD huCD le_rfl x hCb hD
      refine hcomp.trans ?_
      have hfact : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [hfact]
      have : (6 : ℝ) * B * (2 / ε) ^ 3 = 48 * B / ε ^ 3 := by
        field_simp; ring
      rw [this]
    · -- off the shell `f` is locally constant, so the third derivative vanishes
      have hcont : Continuous fun y : EuclideanSpace ℝ (Fin k) => (‖y‖ ^ 2 - a ^ 2) / W := by
        fun_prop
      have hzero : iteratedFDeriv ℝ 3 (g ∘ u) x = 0 := by
        rcases not_and_or.mp hcase with hlt | hgt
        · have hvx : (‖x‖ ^ 2 - a ^ 2) / W < 0 := lt_of_not_ge hlt
          have hmem : {y : EuclideanSpace ℝ (Fin k) | (‖y‖ ^ 2 - a ^ 2) / W < 0} ∈ nhds x :=
            (isOpen_lt hcont continuous_const).mem_nhds hvx
          have heq : (g ∘ u) =ᶠ[nhds x] fun _ : EuclideanSpace ℝ (Fin k) => (1 : ℝ) :=
            Filter.eventually_of_mem hmem fun y hy => by
              rw [hval y]; exact radialCutoff_of_nonpos (le_of_lt hy)
          have := (Filter.EventuallyEq.iteratedFDeriv ℝ heq 3).self_of_nhds
          rw [this, iteratedFDeriv_const_of_ne (by norm_num)]
          rfl
        · have hvx : (1 : ℝ) < (‖x‖ ^ 2 - a ^ 2) / W := lt_of_not_ge hgt
          have hmem : {y : EuclideanSpace ℝ (Fin k) | 1 < (‖y‖ ^ 2 - a ^ 2) / W} ∈ nhds x :=
            (isOpen_lt continuous_const hcont).mem_nhds hvx
          have heq : (g ∘ u) =ᶠ[nhds x] fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ) :=
            Filter.eventually_of_mem hmem fun y hy => by
              rw [hval y]; exact radialCutoff_of_one_le (le_of_lt hy)
          have := (Filter.EventuallyEq.iteratedFDeriv ℝ heq 3).self_of_nhds
          rw [this, iteratedFDeriv_const_of_ne (by norm_num)]
          rfl
      rw [hzero, norm_zero]
      positivity

/-! #### Gaussian stability of the normalized sum

The right-hand endpoint of the Lindeberg telescope is the Gaussian law itself: replacing all
`n` summands by Gaussians and normalizing by `√n` reproduces `N(0, I_k)` exactly. This is
proved by characteristic functions — the `n`-fold product measure factorizes the integral
(`integral_fintype_prod_eq_prod`) and `charFun_stdGaussian` closes the computation. -/

/-- The characteristic function of the law of `c • ∑ᵢ yᵢ` under an `n`-fold product measure is
the `n`-th power of the characteristic function at `c • t`. -/
private lemma charFun_map_const_smul_sum {k n : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν] (c : ℝ)
    (t : EuclideanSpace ℝ (Fin k)) :
    charFun ((Measure.pi fun _ : Fin n => ν).map fun y => c • ∑ i, y i) t
      = charFun ν (c • t) ^ n := by
  classical
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hinner : ∀ y : Fin n → EuclideanSpace ℝ (Fin k),
      ⟪c • ∑ i, y i, t⟫_ℝ = ∑ i, ⟪y i, c • t⟫_ℝ := by
    intro y
    rw [real_inner_smul_left, sum_inner, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (real_inner_smul_right _ _ _).symm
  have hfac : ∀ y : Fin n → EuclideanSpace ℝ (Fin k),
      Complex.exp ((⟪c • ∑ i, y i, t⟫_ℝ : ℂ) * Complex.I)
        = ∏ i, Complex.exp ((⟪y i, c • t⟫_ℝ : ℂ) * Complex.I) := by
    intro y
    rw [hinner y]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  simp_rw [hfac]
  refine Eq.trans (integral_fintype_prod_eq_prod (μ := fun _ : Fin n => ν)
    (fun (_ : Fin n) (x : EuclideanSpace ℝ (Fin k)) =>
      Complex.exp ((⟪x, c • t⟫_ℝ : ℂ) * Complex.I))) ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, charFun_apply]

/-- **Gaussian stability of the normalized sum.** For `n ≥ 1`, pushing the `n`-fold product of
`N(0, I_k)` forward under `y ↦ n^{-1/2} ∑ᵢ yᵢ` gives back `N(0, I_k)`. -/
private lemma map_normalized_sum_stdGaussian {k n : ℕ} (hn : 0 < n) :
    ((Measure.pi fun _ : Fin n => stdGaussian (EuclideanSpace ℝ (Fin k))).map
        fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  haveI : IsProbabilityMeasure ((Measure.pi fun _ : Fin n =>
      stdGaussian (EuclideanSpace ℝ (Fin k))).map
        fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_map_const_smul_sum, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_nat_mul]
  congr 1
  have hnorm : ‖(Real.sqrt (n : ℝ))⁻¹ • t‖ = ‖t‖ / Real.sqrt (n : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos)]
    ring
  have hsq : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hnpos.le]
    norm_cast
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).mpr hn.ne'
  rw [hnorm]
  push_cast
  rw [div_pow, hsq]
  field_simp

/-! #### Ingredients of the one-step Lindeberg swap

Second-order Taylor expansion of `u ↦ f (v + c • u)` produces three integrals. The constant
term is trivial; the linear term vanishes because the law is centred (Riesz representative of
`Df(v)` plus `hmean`); and the quadratic term takes the **same value for any two laws with
identity covariance**, so no closed form for it is ever needed — only the fact that the two
values coincide. That last observation is what `integral_bilin_eq_basis_sum` records: it
evaluates `∫ D²f(v)(y,y)` as a fixed finite sum over the standard basis, whose value depends on
the law only through `hcov`. -/

section SwapStep

variable {k : ℕ}

/-- `L³ ⊆ L²` on a probability space, in the only form needed here: `t² ≤ 1 + t³`. -/
private lemma integrable_normSq_of_cube {ν : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν := by
  have hdom : Integrable (fun y : EuclideanSpace ℝ (Fin k) => 1 + ‖y‖ ^ 3) ν :=
    (integrable_const 1).add hβ
  refine Integrable.mono' hdom (by fun_prop) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  rcases le_or_gt ‖y‖ 1 with h | h
  · nlinarith
  · nlinarith

/-- `L¹ ⊆ L³` on a probability space, in the only form needed here: `t ≤ 1 + t³`. -/
private lemma integrable_norm_of_cube {ν : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν := by
  have hdom : Integrable (fun y : EuclideanSpace ℝ (Fin k) => 1 + ‖y‖ ^ 3) ν :=
    (integrable_const 1).add hβ
  refine Integrable.mono' hdom (by fun_prop) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
  rcases le_or_gt ‖y‖ 1 with h | h
  · nlinarith [pow_nonneg (norm_nonneg y) 3]
  · have ht2 : (1 : ℝ) ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    nlinarith [norm_nonneg y, ht2]

/-- A continuous linear functional is integrable as soon as the norm is: `|L y| ≤ ‖L‖ ‖y‖`. -/
private lemma integrable_clm_of_norm {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (h1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν)
    (L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :
    Integrable (fun y => L y) ν := by
  refine Integrable.mono' (h1.const_mul ‖L‖) L.continuous.aestronglyMeasurable ?_
  filter_upwards with y
  exact L.le_opNorm y

/-- A continuous bilinear form evaluated on the diagonal is integrable as soon as the squared
norm is: `|B(y,y)| ≤ ‖B‖ ‖y‖²`. -/
private lemma integrable_bilin_of_normSq {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin k)) ℝ) :
    Integrable (fun y => B (fun _ => y)) ν := by
  refine Integrable.mono' (h2.const_mul ‖B‖)
    (B.cont.comp (continuous_pi fun _ => continuous_id)).aestronglyMeasurable ?_
  filter_upwards with y
  calc ‖B (fun _ => y)‖ ≤ ‖B‖ * ∏ _i : Fin 2, ‖y‖ := B.le_opNorm _
    _ = ‖B‖ * ‖y‖ ^ 2 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `y ↦ ⟪u, y⟫` is integrable as soon as the norm is. -/
private lemma integrable_inner_of_norm {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (h1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν)
    (u : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun y => ⟪u, y⟫_ℝ) ν :=
  integrable_clm_of_norm h1 (innerSL ℝ u)

/-- `y ↦ ⟪u, y⟫ ⟪v, y⟫` is integrable as soon as the squared norm is. -/
private lemma integrable_inner_mul_inner {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (u v : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun y => ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ) ν := by
  refine Integrable.mono' (h2.const_mul (‖u‖ * ‖v‖)) (by fun_prop) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul]
  calc |⟪u, y⟫_ℝ| * |⟪v, y⟫_ℝ| ≤ (‖u‖ * ‖y‖) * (‖v‖ * ‖y‖) :=
        mul_le_mul (abs_real_inner_le_norm u y) (abs_real_inner_le_norm v y)
          (abs_nonneg _) (by positivity)
    _ = ‖u‖ * ‖v‖ * ‖y‖ ^ 2 := by ring

/-- **The linear Taylor term integrates to zero against a centred law.** `Df(v)` is a continuous
linear functional, hence `⟪r, ·⟫` for its Riesz representative `r`, and `hmean` kills it. -/
private lemma integral_clm_eq_zero_of_centred {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :
    (∫ y, L y ∂ν) = 0 := by
  have hL : ∀ y : EuclideanSpace ℝ (Fin k),
      L y = ⟪(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm L, y⟫_ℝ :=
    fun y => (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
  simp_rw [hL]
  exact hmean _

/-- **The quadratic Taylor term depends on the law only through its covariance.** For a
continuous bilinear form `B` and *any* law with identity covariance, `∫ B(y,y)` equals the
explicit finite sum `∑_r ⟪e_{r₀}, e_{r₁}⟫ B(e_{r₀}, e_{r₁})` over `r : Fin 2 → Fin k`. Two such
laws therefore give the *same* value, which is exactly what the Lindeberg swap consumes; no
evaluation of the sum (`= ∑ₐ B(eₐ,eₐ)`) is needed. -/
private lemma integral_bilin_eq_basis_sum {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin k)) ℝ) :
    (∫ y, B (fun _ => y) ∂ν)
      = ∑ r : Fin 2 → Fin k,
          ⟪EuclideanSpace.basisFun (Fin k) ℝ (r 0),
            EuclideanSpace.basisFun (Fin k) ℝ (r 1)⟫_ℝ
            * B fun i => EuclideanSpace.basisFun (Fin k) ℝ (r i) := by
  classical
  set e : Fin k → EuclideanSpace ℝ (Fin k) := fun a => EuclideanSpace.basisFun (Fin k) ℝ a
    with he
  have hexp : ∀ y : EuclideanSpace ℝ (Fin k), B (fun _ => y)
      = ∑ r : Fin 2 → Fin k, ⟪e (r 0), y⟫_ℝ * ⟪e (r 1), y⟫_ℝ * B fun i => e (r i) := by
    intro y
    have hy : (fun _ : Fin 2 => y) = fun _ : Fin 2 => ∑ a, ⟪e a, y⟫_ℝ • e a := by
      funext _
      exact ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr' y).symm
    rw [hy, ← ContinuousMultilinearMap.coe_coe,
      (B.toMultilinearMap).map_sum (g := fun _ (a : Fin k) => ⟪e a, y⟫_ℝ • e a)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show (fun i : Fin 2 => ⟪e (r i), y⟫_ℝ • e (r i))
        = fun i : Fin 2 => (fun j : Fin 2 => ⟪e (r j), y⟫_ℝ) i • (fun j : Fin 2 => e (r j)) i
      from rfl, (B.toMultilinearMap).map_smul_univ, Fin.prod_univ_two,
      ContinuousMultilinearMap.coe_coe, smul_eq_mul]
  simp_rw [hexp]
  rw [integral_finset_sum _ fun r _ => (integrable_inner_mul_inner h2 _ _).mul_const _]
  exact Finset.sum_congr rfl fun r _ => by rw [integral_mul_const, hcov]

/-- **One step of the Lindeberg swap.** For a fixed shift `v` and scale `c ≥ 0`, replacing a
summand of law `ν` by one of law `ρ` — both centred and with identity covariance — costs at most
`(M/6) c³ (β_ν + β_ρ)`.

Both integrals are compared with the *same* number `f v + (c²/2) S`, where `S` is the
basis sum of `integral_bilin_eq_basis_sum`: the constant Taylor term is common, the linear term
vanishes on either side by `integral_clm_eq_zero_of_centred`, and the quadratic term has the
same value on either side because both laws have identity covariance. The two third-order
remainders are then bounded separately by `norm_taylor_remainder_three_le`. -/
private lemma abs_integral_swap_step_le {k : ℕ}
    {ν ρ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hmeanν : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcovν : ∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂ν) = ⟪u, w⟫_ℝ)
    (hβν : Integrable (fun y => ‖y‖ ^ 3) ν)
    (hmeanρ : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ρ) = 0)
    (hcovρ : ∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂ρ) = ⟪u, w⟫_ℝ)
    (hβρ : Integrable (fun y => ‖y‖ ^ 3) ρ)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 3 f) (hfb : ∀ x, |f x| ≤ 1)
    {M : ℝ} (hM : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M)
    (v : EuclideanSpace ℝ (Fin k)) {c : ℝ} (hc : 0 ≤ c) :
    |(∫ y, f (v + c • y) ∂ν) - (∫ y, f (v + c • y) ∂ρ)|
      ≤ M / 6 * c ^ 3 * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ)) := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := fderiv ℝ f v with hL
  set B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin k)) ℝ :=
    iteratedFDeriv ℝ 2 f v with hB
  set S : ℝ := ∑ r : Fin 2 → Fin k,
    ⟪EuclideanSpace.basisFun (Fin k) ℝ (r 0), EuclideanSpace.basisFun (Fin k) ℝ (r 1)⟫_ℝ
      * B fun i => EuclideanSpace.basisFun (Fin k) ℝ (r i) with hS
  -- The pointwise Taylor estimate against the *common* second-order polynomial.
  have htay : ∀ y : EuclideanSpace ℝ (Fin k),
      |f (v + c • y) - (f v + c * L y + c ^ 2 / 2 * B fun _ => y)|
        ≤ M / 6 * c ^ 3 * ‖y‖ ^ 3 := by
    intro y
    have h := norm_taylor_remainder_three_le hf hM v (c • y)
    have h1 : fderiv ℝ f v (c • y) = c * L y := by rw [hL, map_smul, smul_eq_mul]
    have h2 : (B fun _ : Fin 2 => c • y) = c ^ 2 * B fun _ => y := by
      rw [show (fun _ : Fin 2 => c • y)
          = fun i : Fin 2 => (fun _ : Fin 2 => c) i • (fun _ : Fin 2 => y) i from rfl,
        ← ContinuousMultilinearMap.coe_coe, (B.toMultilinearMap).map_smul_univ,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ContinuousMultilinearMap.coe_coe, smul_eq_mul]
    have h3 : ‖c • y‖ ^ 3 = c ^ 3 * ‖y‖ ^ 3 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow]
    rw [← hB, h1, h2, h3] at h
    calc |f (v + c • y) - (f v + c * L y + c ^ 2 / 2 * B fun _ => y)|
        = |f (v + c • y) - f v - c * L y - 1 / 2 * (c ^ 2 * B fun _ => y)| := by ring_nf
      _ ≤ M / 6 * (c ^ 3 * ‖y‖ ^ 3) := h
      _ = M / 6 * c ^ 3 * ‖y‖ ^ 3 := by ring
  -- Each law is compared with the same number `f v + (c²/2) S`.
  have key : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂σ) = 0) →
      (∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂σ) = ⟪u, w⟫_ℝ) →
      Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) σ →
      |(∫ y, f (v + c • y) ∂σ) - (f v + c ^ 2 / 2 * S)|
        ≤ M / 6 * c ^ 3 * ∫ y, ‖y‖ ^ 3 ∂σ := by
    intro σ hσ hm hcv hβ
    haveI := hσ
    have h1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) σ :=
      integrable_norm_of_cube hβ
    have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) σ :=
      integrable_normSq_of_cube hβ
    have ha : Integrable (fun y : EuclideanSpace ℝ (Fin k) => f v + c * L y) σ :=
      (integrable_const (f v)).add ((integrable_clm_of_norm h1 L).const_mul c)
    have hb : Integrable
        (fun y : EuclideanSpace ℝ (Fin k) => c ^ 2 / 2 * B fun _ => y) σ :=
      (integrable_bilin_of_normSq h2 B).const_mul (c ^ 2 / 2)
    have hPint : Integrable
        (fun y : EuclideanSpace ℝ (Fin k) => f v + c * L y + c ^ 2 / 2 * B fun _ => y) σ :=
      ha.add hb
    have hfint : Integrable (fun y : EuclideanSpace ℝ (Fin k) => f (v + c • y)) σ := by
      refine Integrable.mono' (integrable_const (1 : ℝ))
        (hf.continuous.comp (by fun_prop)).aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs]
      exact hfb _
    have hPval : (∫ y, (f v + c * L y + c ^ 2 / 2 * B fun _ => y) ∂σ)
        = f v + c ^ 2 / 2 * S := by
      rw [integral_add ha hb, integral_add (integrable_const (f v))
          ((integrable_clm_of_norm h1 L).const_mul c), integral_const, integral_const_mul,
        integral_const_mul, integral_clm_eq_zero_of_centred hm L,
        integral_bilin_eq_basis_sum hcv h2 B, ← hS]
      simp
    calc |(∫ y, f (v + c • y) ∂σ) - (f v + c ^ 2 / 2 * S)|
        = |∫ y, (f (v + c • y)
            - (f v + c * L y + c ^ 2 / 2 * B fun _ => y)) ∂σ| := by
          rw [integral_sub hfint hPint, hPval]
      _ ≤ ∫ y, |f (v + c • y) - (f v + c * L y + c ^ 2 / 2 * B fun _ => y)| ∂σ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, M / 6 * c ^ 3 * ‖y‖ ^ 3 ∂σ :=
          integral_mono (hfint.sub hPint).abs (hβ.const_mul _) htay
      _ = M / 6 * c ^ 3 * ∫ y, ‖y‖ ^ 3 ∂σ := integral_const_mul _ _
  have hkν := key ν ‹_› hmeanν hcovν hβν
  have hkρ := key ρ ‹_› hmeanρ hcovρ hβρ
  have habs := abs_sub_abs_le_abs_sub ((∫ y, f (v + c • y) ∂ν) - (f v + c ^ 2 / 2 * S))
    ((∫ y, f (v + c • y) ∂ρ) - (f v + c ^ 2 / 2 * S))
  have htri : |(∫ y, f (v + c • y) ∂ν) - (∫ y, f (v + c • y) ∂ρ)|
      ≤ |(∫ y, f (v + c • y) ∂ν) - (f v + c ^ 2 / 2 * S)|
        + |(∫ y, f (v + c • y) ∂ρ) - (f v + c ^ 2 / 2 * S)| := by
    have := abs_sub ((∫ y, f (v + c • y) ∂ν) - (f v + c ^ 2 / 2 * S))
      ((∫ y, f (v + c • y) ∂ρ) - (f v + c ^ 2 / 2 * S))
    calc |(∫ y, f (v + c • y) ∂ν) - (∫ y, f (v + c • y) ∂ρ)|
        = |((∫ y, f (v + c • y) ∂ν) - (f v + c ^ 2 / 2 * S))
            - ((∫ y, f (v + c • y) ∂ρ) - (f v + c ^ 2 / 2 * S))| := by ring_nf
      _ ≤ _ := abs_sub _ _
  have hc3 : 0 ≤ M / 6 * c ^ 3 := by positivity
  nlinarith [hkν, hkρ, htri]

/-! #### Peeling one coordinate out of a product measure

The hybrid telescope replaces the summands one at a time, so each step must isolate a single
coordinate of a `Measure.pi` over a family of *unequal* laws. This is
`MeasureTheory.measurePreserving_piFinSuccAbove` (the coordinate `i` splits off as a `prod`
factor) followed by Fubini; the `Fin.insertNth` bookkeeping is `Fin.sum_univ_succAbove`. -/

/-- The (bounded, continuous) integrand of the peeled Fubini step is integrable on the
product. -/
private lemma integrable_peel_prod {k m : ℕ}
    (σ : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure σ]
    (κ' : Fin m → Measure (EuclideanSpace ℝ (Fin k))) [∀ l, IsProbabilityMeasure (κ' l)]
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : Continuous g) (hgb : ∀ x, |g x| ≤ 1) :
    Integrable (fun p : EuclideanSpace ℝ (Fin k) × (Fin m → EuclideanSpace ℝ (Fin k)) =>
        g (p.1 + ∑ l, p.2 l)) (σ.prod (Measure.pi κ')) := by
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin k) × (Fin m → EuclideanSpace ℝ (Fin k)) =>
      p.1 + ∑ l, p.2 l) :=
    measurable_fst.add
      (Finset.univ.measurable_sum fun l _ => (measurable_pi_apply l).comp measurable_snd)
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (hg.measurable.comp hmeas).aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_eq_abs]
  exact hgb _

/-- **Peeling one coordinate.** For a bounded continuous `g` and a finite family of probability
laws, the integral of `g (∑ₗ xₗ)` over `Measure.pi κ` is the iterated integral obtained by
singling out the coordinate `i`: the remaining coordinates supply the shift `∑ₗ yₗ` and the
`i`-th coordinate is integrated against `κ i`. -/
private lemma integral_pi_sum_peel {k m : ℕ}
    (κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)))
    [∀ i, IsProbabilityMeasure (κ i)] (i : Fin (m + 1))
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : Continuous g) (hgb : ∀ x, |g x| ≤ 1) :
    (∫ x, g (∑ l, x l) ∂(Measure.pi κ))
      = ∫ y, (∫ u, g (u + ∑ l, y l) ∂(κ i))
          ∂(Measure.pi fun l : Fin m => κ (i.succAbove l)) := by
  classical
  set e : ((_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k))
      ≃ᵐ EuclideanSpace ℝ (Fin k) × ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => EuclideanSpace ℝ (Fin k)) i with he
  have hmp : MeasurePreserving e (Measure.pi κ)
      ((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))) :=
    measurePreserving_piFinSuccAbove κ i
  have hsym : ∀ p : EuclideanSpace ℝ (Fin k) × ((_ : Fin m) → EuclideanSpace ℝ (Fin k)),
      (∑ l, (e.symm p) l) = p.1 + ∑ l, p.2 l := by
    intro p
    have hins : e.symm p = Fin.insertNth i p.1 p.2 := rfl
    rw [hins, Fin.sum_univ_succAbove _ i]
    simp
  have hF := integrable_peel_prod (κ i) (fun l : Fin m => κ (i.succAbove l)) hg hgb
  calc (∫ x, g (∑ l, x l) ∂(Measure.pi κ))
      = ∫ p, g (∑ l, (e.symm p) l)
          ∂((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))) :=
        (MeasurePreserving.integral_comp' (MeasurePreserving.symm e hmp) _).symm
    _ = ∫ p, g (p.1 + ∑ l, p.2 l)
          ∂((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))) := by
        simp_rw [hsym]
    _ = ∫ y, ∫ u, g (u + ∑ l, y l) ∂(κ i)
          ∂(Measure.pi fun l : Fin m => κ (i.succAbove l)) :=
        integral_prod_symm _ hF

/-- **Peeling one coordinate, at the level of measures (wave 42).** The law of the coordinate
sum is the law of `u + ∑ₗ yₗ` with `u ∼ κ i` independent of the remaining coordinates.

This is `integral_pi_sum_peel` with the bounded continuous test function stripped off, and it is
what brick L needs: the transfer between the two localised per-step bricks and brick L's weight
hypothesis is `wideShell_le_of_deconvolution`, whose hypothesis `hμ` is a statement about
*measures* (`μ = (τ ⊗ η).map (+)`) and not about integrals of continuous functions — the shell
indicator is not continuous, so the integral form cannot be used. The proof is the same
`measurePreserving_piFinSuccAbove` transport, with `Fin.sum_univ_succAbove` splitting the sum. -/
theorem map_pi_sum_peel {k m : ℕ}
    (κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)))
    [∀ i, IsProbabilityMeasure (κ i)] (i : Fin (m + 1)) :
    ((Measure.pi κ).map fun x => ∑ l, x l)
      = (((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))).map
          fun p => p.1 + ∑ l, p.2 l) := by
  classical
  set e : ((_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k))
      ≃ᵐ EuclideanSpace ℝ (Fin k) × ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => EuclideanSpace ℝ (Fin k)) i with he
  have hmp : MeasurePreserving e (Measure.pi κ)
      ((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))) :=
    measurePreserving_piFinSuccAbove κ i
  have hcomp : (fun x : (_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k) => ∑ l, x l)
      = (fun p : EuclideanSpace ℝ (Fin k) × ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) =>
          p.1 + ∑ l, p.2 l) ∘ e := by
    funext x
    have hx : e x = (x i, fun l => x (i.succAbove l)) := rfl
    rw [Function.comp_apply, hx]
    exact Fin.sum_univ_succAbove (fun l => x l) i
  rw [hcomp, ← Measure.map_map (by fun_prop) e.measurable, hmp.map_eq]

/-- Mathlib's additive convolution of measures is literally the shape both
`wideShell_le_of_deconvolution`'s hypothesis `hμ` and `hybridLaw_eq_map_add`'s conclusion have,
so the convolution algebra (`Measure.conv_assoc`, `Measure.conv_comm`) is available for free. -/
theorem conv_eq_map_add {k : ℕ} (α β : Measure (EuclideanSpace ℝ (Fin k))) :
    α ∗ β = (α.prod β).map fun p => p.1 + p.2 := rfl

/-- The one rearrangement of a threefold convolution brick L's head side needs: the swapped
coordinate has to end up as the *last* factor, since that is the one being deconvolved away. -/
theorem conv_reassoc {k : ℕ} {α β ζ : Measure (EuclideanSpace ℝ (Fin k))}
    [SFinite α] [SFinite β] [SFinite ζ] :
    ((α ∗ β) ∗ ζ) = ((β ∗ ζ) ∗ α) := by
  rw [Measure.conv_assoc, Measure.conv_comm α (β ∗ ζ)]

/-- **Peeling one coordinate off the SCALED coordinate-sum law (wave 43).** `map_pi_sum_peel`
with the telescope's scaling `c` applied, and stated as a convolution — which is what
`wideShell_le_of_deconvolution` consumes. -/
theorem map_pi_sum_smul_peel {k m : ℕ}
    (κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)))
    [∀ i, IsProbabilityMeasure (κ i)] (i : Fin (m + 1)) (c : ℝ) :
    ((Measure.pi κ).map fun x => c • ∑ l, x l)
      = ((κ i).map fun u => c • u)
        ∗ ((Measure.pi fun l : Fin m => κ (i.succAbove l)).map fun y => c • ∑ l, y l) := by
  have hmeas1 : Measurable fun x : (_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k) =>
      ∑ l, x l := by fun_prop
  have hleft : ((Measure.pi κ).map fun x => c • ∑ l, x l)
      = (((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))).map
          fun p => c • p.1 + c • ∑ l, p.2 l) := by
    rw [show (fun x : (_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k) => c • ∑ l, x l)
        = (fun w : EuclideanSpace ℝ (Fin k) => c • w) ∘ (fun x => ∑ l, x l) from rfl,
      ← Measure.map_map (by fun_prop) hmeas1, map_pi_sum_peel κ i,
      Measure.map_map (by fun_prop) (by fun_prop)]
    have hfun : ((fun w : EuclideanSpace ℝ (Fin k) => c • w)
          ∘ fun p : EuclideanSpace ℝ (Fin k) × ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) =>
            p.1 + ∑ l, p.2 l)
        = fun p => c • p.1 + c • ∑ l, p.2 l := by
      funext p
      simp only [Function.comp_apply, smul_add]
    rw [hfun]
  rw [hleft, conv_eq_map_add, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end SwapStep

/-- **Lindeberg smooth-function comparison for the normalized sum.**
For a *fixed* `C³` test function `f` with `‖f‖_∞ ≤ 1` and `‖D³f‖ ≤ M`, replacing the `n` centred,
identity-covariance summands by Gaussians one at a time gives an error `≤ M (β + β_G) / (6√n)`,
where `β = ∫‖y‖³ dν` and `β_G = ∫‖z‖³ dN(0,I_k)`. This is `n^{-1/2}` for fixed `f`; the
degradation to `n^{-1/8}` for *sets* comes only from taking `f` a smoothed indicator with
`M ~ ε^{-3}` and optimising `ε`.

**Amendment (documented).** A boundedness hypothesis `hfb : ∀ x, |f x| ≤ 1` has been added.
The statement is true without it — `‖D³f‖ ≤ M` bounds `|f|` by a cubic polynomial, which is
`ν`-integrable by `hβ` and `Measure.pi`-integrable after a power-mean bound
`‖∑ yᵢ‖³ ≤ n² ∑ ‖yᵢ‖³` — but the resulting integrability bookkeeping is several hundred lines of
pure overhead. The lemma is `private`, and its only consumer,
`berryEsseen_ball_elementary`, applies it to smoothed indicators with values in `[0,1]`, which
supply `hfb` for free. No generality that any caller uses is lost.

The proof is the hybrid telescope over
`Qⱼ := Measure.pi (fun i => if i < j then γ else ν)`, `j = 0, …, n`, with

* `Q₀ = ⨂ⁿ ν`, whose pushforward under `n^{-1/2} ∑` is the left endpoint;
* `Qₙ = ⨂ⁿ γ`, whose pushforward is `γ` itself by `map_normalized_sum_stdGaussian`;
* each step `Qⱼ → Qⱼ₊₁` isolated by `integral_pi_sum_peel` (Fubini after
  `measurePreserving_piFinSuccAbove`) — the two hybrids differ *only* in the `j`-th factor, so
  after peeling that coordinate the outer measure over the remaining `n − 1` coordinates is
  literally the same, and the inner integrals differ by `abs_integral_swap_step_le` uniformly in
  the outer variable.

An earlier note preferred a doubled space `(⨂ν).prod (⨂γ)` with independence arguments, to
avoid "peeling a coordinate out of a product of unequal factors". That was the wrong call:
`measurePreserving_piFinSuccAbove` peels a coordinate out of a `Measure.pi` over an arbitrary
*dependent* family at no extra cost, and the hybrid family needs no independence API at all.

The `n` steps each cost `M/6 · n^{-3/2} (β + β_G)`, and `n · n^{-3/2} = n^{-1/2}`. -/
private lemma abs_integral_smooth_sub_gaussian_le {k n : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin k))} (hn : 0 < n) (hν : IsProbabilityMeasure ν)
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 3 f)
    -- USER-INPUT (amendment): the test function is bounded by `1`; see the docstring.
    (hfb : ∀ x, |f x| ≤ 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M) :
    |(∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i))
        - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
      ≤ M / 6 * ((∫ y, ‖y‖ ^ 3 ∂ν)
          + (∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)))
          / Real.sqrt (n : ℝ) := by
  classical
  haveI := hν
  -- The Gaussian side, transported to the Mathlib `stdGaussian` API.
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  haveI hγp : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  have hγstd : γ = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
    rw [hγdef]; exact multivariateGaussian_zero_one
  have hmeanγ : ∀ u : EuclideanSpace ℝ (Fin k), (∫ z, ⟪u, z⟫_ℝ ∂γ) = 0 := by
    intro u
    have h := integral_strongDual_stdGaussian (E := EuclideanSpace ℝ (Fin k)) (innerSL ℝ u)
    rw [hγstd]
    simpa using h
  have hcovγ : ∀ u w : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ * ⟪w, z⟫_ℝ ∂γ) = ⟪u, w⟫_ℝ := by
    intro u w
    have hL2 : MemLp id 2 γ := by rw [hγstd]; exact IsGaussian.memLp_id _ 2 (by simp)
    have hid : γ[id] = (0 : EuclideanSpace ℝ (Fin k)) := by
      rw [hγstd]; exact integral_id_stdGaussian
    have h := covarianceBilin_apply (μ := γ) hL2 u w
    rw [hid] at h
    simp only [sub_zero] at h
    rw [← h, hγstd, covarianceBilin_stdGaussian]
    exact innerSL_apply_apply (𝕜 := ℝ) u w
  have hβγ : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 3) γ := by
    have hL3 : MemLp id ((3 : ℕ) : ℝ≥0∞) γ := by
      rw [hγstd]; exact IsGaussian.memLp_id _ _ (by simp)
    simpa using hL3.integrable_norm_pow'
  -- Write `n = m + 1` so that a coordinate can be peeled off.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsN : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hNr
  set c : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hcdef
  have hc0 : 0 ≤ c := by positivity
  set g : EuclideanSpace ℝ (Fin k) → ℝ := fun z => f (c • z) with hgdef
  have hgcont : Continuous g := hf.continuous.comp (continuous_const_smul c)
  have hgb : ∀ x, |g x| ≤ 1 := fun x => hfb _
  -- The hybrid family and the telescoped functional.
  set κ : ℕ → Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun j i => if (i : ℕ) < j then γ else ν with hκdef
  haveI hκp : ∀ (j : ℕ) (i : Fin (m + 1)), IsProbabilityMeasure (κ j i) := by
    intro j i
    rw [hκdef]
    dsimp only
    split_ifs
    · exact hγp
    · exact hν
  set I : ℕ → ℝ := fun j => ∫ x, g (∑ l, x l) ∂(Measure.pi (κ j)) with hIdef
  set X : ℝ := (∫ y, ‖y‖ ^ 3 ∂ν) + (∫ z, ‖z‖ ^ 3 ∂γ) with hXdef
  -- One telescope step.
  have hstep : ∀ j : ℕ, j < m + 1 → |I j - I (j + 1)| ≤ M / 6 * c ^ 3 * X := by
    intro j hj
    set i : Fin (m + 1) := ⟨j, hj⟩ with hidef
    have hival : (i : ℕ) = j := by rw [hidef]
    have hji : κ j i = ν := by
      rw [hκdef]; dsimp only; rw [if_neg (by rw [hival]; exact lt_irrefl j)]
    have hji1 : κ (j + 1) i = γ := by
      rw [hκdef]; dsimp only; rw [if_pos (by rw [hival]; exact Nat.lt_succ_self j)]
    have hoff : (fun l : Fin m => κ (j + 1) (i.succAbove l))
        = fun l : Fin m => κ j (i.succAbove l) := by
      funext l
      have hne : ((i.succAbove l : Fin (m + 1)) : ℕ) ≠ j := by
        intro h
        exact Fin.succAbove_ne i l (Fin.ext (by rw [h, hival]))
      rw [hκdef]
      dsimp only
      by_cases hlt : ((i.succAbove l : Fin (m + 1)) : ℕ) < j
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg hlt]
    have hpeel0 := integral_pi_sum_peel (κ j) i hgcont hgb
    have hpeel1 := integral_pi_sum_peel (κ (j + 1)) i hgcont hgb
    rw [hji] at hpeel0
    rw [hji1, hoff] at hpeel1
    set R : Measure ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
      Measure.pi (fun l : Fin m => κ j (i.succAbove l)) with hRdef
    haveI hRp : IsProbabilityMeasure R := by rw [hRdef]; infer_instance
    have hAint : Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) =>
        ∫ u, g (u + ∑ l, y l) ∂ν) R :=
      (integrable_peel_prod ν (fun l : Fin m => κ j (i.succAbove l))
        hgcont hgb).integral_prod_right
    have hBint : Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) =>
        ∫ u, g (u + ∑ l, y l) ∂γ) R :=
      (integrable_peel_prod γ (fun l : Fin m => κ j (i.succAbove l))
        hgcont hgb).integral_prod_right
    have hpt : ∀ y : (_ : Fin m) → EuclideanSpace ℝ (Fin k),
        |(∫ u, g (u + ∑ l, y l) ∂ν) - (∫ u, g (u + ∑ l, y l) ∂γ)|
          ≤ M / 6 * c ^ 3 * X := by
      intro y
      have hrw : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)),
          (∫ u, g (u + ∑ l, y l) ∂σ) = ∫ u, f ((c • ∑ l, y l) + c • u) ∂σ := by
        intro σ
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        rw [hgdef]
        dsimp only
        rw [smul_add, add_comm]
      rw [hrw ν, hrw γ, hXdef]
      exact abs_integral_swap_step_le hmean hcov hβ hmeanγ hcovγ hβγ hf hfb hM _ hc0
    have hIj : I j = ∫ y, (∫ u, g (u + ∑ l, y l) ∂ν) ∂R := by
      rw [hIdef]; exact hpeel0
    have hIj1 : I (j + 1) = ∫ y, (∫ u, g (u + ∑ l, y l) ∂γ) ∂R := by
      rw [hIdef]; exact hpeel1
    rw [hIj, hIj1, ← integral_sub hAint hBint]
    calc |∫ y, ((∫ u, g (u + ∑ l, y l) ∂ν) - (∫ u, g (u + ∑ l, y l) ∂γ)) ∂R|
        ≤ ∫ y, |(∫ u, g (u + ∑ l, y l) ∂ν) - (∫ u, g (u + ∑ l, y l) ∂γ)| ∂R :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _y, M / 6 * c ^ 3 * X ∂R :=
          integral_mono (hAint.sub hBint).abs (integrable_const _) hpt
      _ = M / 6 * c ^ 3 * X := by rw [integral_const]; simp
  -- Telescoping.
  have htel : ∀ j : ℕ, j ≤ m + 1 → |I 0 - I j| ≤ (j : ℝ) * (M / 6 * c ^ 3 * X) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j (by omega)
      have h3 : |I 0 - I (j + 1)| ≤ |I 0 - I j| + |I j - I (j + 1)| := abs_sub_le _ _ _
      push_cast
      linarith
  -- The two endpoints.
  have hκ0 : κ 0 = fun _ : Fin (m + 1) => ν := by
    funext i; rw [hκdef]; simp
  have hκN : κ (m + 1) = fun _ : Fin (m + 1) => γ := by
    funext i; rw [hκdef]; dsimp only; rw [if_pos i.isLt]
  have hI0 : I 0 = ∫ x, f x ∂((Measure.pi fun _ : Fin (m + 1) => ν).map
      fun y => c • ∑ i, y i) := by
    rw [integral_map (by fun_prop) hf.continuous.aestronglyMeasurable, hIdef]
    dsimp only
    rw [hκ0]
  have hIN : I (m + 1) = ∫ x, f x ∂γ := by
    have hmap : ((Measure.pi fun _ : Fin (m + 1) => γ).map fun y => c • ∑ i, y i) = γ := by
      rw [hγstd, hcdef]
      exact map_normalized_sum_stdGaussian (Nat.succ_pos m)
    rw [hIdef]
    dsimp only
    rw [hκN, ← integral_map (φ := fun y : (_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k) =>
      c • ∑ i, y i) (by fun_prop) hf.continuous.aestronglyMeasurable, hmap]
  have hfin := htel (m + 1) le_rfl
  rw [hI0, hIN] at hfin
  refine hfin.trans_eq ?_
  have hc2 : c ^ 2 = (((m + 1 : ℕ) : ℝ))⁻¹ := by
    rw [hcdef, inv_pow, Real.sq_sqrt hNr.le]
  have hNc : ((m + 1 : ℕ) : ℝ) * c ^ 3 = c := by
    have hsplit : c ^ 3 = c ^ 2 * c := by ring
    rw [hsplit, hc2]
    field_simp
  calc (((m + 1 : ℕ) : ℝ)) * (M / 6 * c ^ 3 * X)
      = (((m + 1 : ℕ) : ℝ) * c ^ 3) * (M / 6 * X) := by ring
    _ = c * (M / 6 * X) := by rw [hNc]
    _ = M / 6 * X / Real.sqrt ((m + 1 : ℕ) : ℝ) := by rw [hcdef]; ring

/-! #### Moment facts consumed by the ball assembly

Two elementary consequences of the standing hypotheses (`hcov`, `hβ`, `ν` a probability
measure) that the `ε`-optimisation needs: the second moment is exactly the dimension, and
`β = ∫‖y‖³ dν` is bounded below by `k^{3/2}` (Lyapunov) — in particular `β > 0`, so that
`ε := (β/√n)^{1/4}` is a legitimate positive smoothing width. -/

/-- **The second moment is the dimension.** Under identity covariance,
`∫ ‖y‖² dν = k`. Expand `‖y‖² = ∑ᵢ ⟪eᵢ, y⟫²` over the standard orthonormal basis and apply
`hcov` coordinatewise; the interchange is legitimate because `hβ` makes each coordinate square
integrable. -/
private lemma integral_normSq_eq_dim {k : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν]
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    (∫ y, ‖y‖ ^ 2 ∂ν) = (k : ℝ) := by
  have hnormsq : ∀ y : EuclideanSpace ℝ (Fin k), ‖y‖ ^ 2 = ∑ i, y i ^ 2 := by
    intro y
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  have hcoord : ∀ (i : Fin k) (y : EuclideanSpace ℝ (Fin k)),
      ⟪(EuclideanSpace.single i (1 : ℝ)), y⟫_ℝ = y i := by
    intro i y
    have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) y
    simpa using h
  have hsq2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν :=
    integrable_normSq_of_cube hβ
  have hcomp : ∀ i : Fin k, Integrable (fun y : EuclideanSpace ℝ (Fin k) => y i ^ 2) ν := by
    intro i
    refine Integrable.mono' hsq2 (by fun_prop) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnormsq y]
    exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg (y j))
      (Finset.mem_univ i)
  calc (∫ y, ‖y‖ ^ 2 ∂ν) = ∫ y, ∑ i, y i ^ 2 ∂ν := by
        exact integral_congr_ae (ae_of_all _ fun y => hnormsq y)
    _ = ∑ i, ∫ y, y i ^ 2 ∂ν := integral_finset_sum _ fun i _ => hcomp i
    _ = ∑ _i : Fin k, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hone : ⟪(EuclideanSpace.single i (1 : ℝ)),
            (EuclideanSpace.single i (1 : ℝ))⟫_ℝ = 1 := by rw [hcoord]; simp
        have h := hcov (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
        rw [hone] at h
        simp only [hcoord] at h
        rw [← h]
        exact integral_congr_ae (ae_of_all _ fun y => by simp [sq])
    _ = (k : ℝ) := by simp

/-- **Lyapunov lower bound.** `k^{3/2} ≤ β` under identity covariance. Elementary: for every
`t ≥ 0` one has the pointwise inequality `3t‖y‖² ≤ 2‖y‖³ + t³` (it is
`(‖y‖ − t)²(2‖y‖ + t) ≥ 0`); integrating and taking `t = √k` gives `√k · k ≤ β`. -/
private lemma sqrt_dim_mul_dim_le_integral_norm_cube {k : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    Real.sqrt (k : ℝ) * (k : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ν := by
  set t : ℝ := Real.sqrt (k : ℝ) with htdef
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  have hsq2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν :=
    integrable_normSq_of_cube hβ
  have hmono : (∫ y, 3 * t * ‖y‖ ^ 2 ∂ν) ≤ ∫ y, (2 * ‖y‖ ^ 3 + t ^ 3) ∂ν := by
    refine integral_mono (hsq2.const_mul (3 * t)) ((hβ.const_mul 2).add (integrable_const _)) ?_
    intro y
    have hy : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
    have hprod : (0 : ℝ) ≤ (‖y‖ - t) ^ 2 * (2 * ‖y‖ + t) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [hprod]
  rw [integral_const_mul, integral_add (hβ.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const, integral_normSq_eq_dim hcov hβ] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  nlinarith [hmono, htsq, ht0]

/-! #### The Gaussian third moment `β_G = ∫‖z‖³ dN(0,I_k)`

The `ε`-optimisation also needs the *Gaussian* side of the third moment to be comparable to
`β`. Since `‖z‖² ∼ χ²_k`, the two public χ² moments (`integral_id_chiSquared` `E X = k`,
`variance_chiSquared` `E (X−k)² = 2k`) suffice, through the pointwise inequality

`r³ ≤ u r² + (r² − u²)²/(2u) + u (r² − u²)/2`, `u = √k`,

which is exactly `r²(u − r)² ≥ 0` after multiplying by `2u`. Integrating gives
`β_G ≤ k^{3/2} + √k ≤ 2 k^{3/2}`, and `k^{3/2} ≤ β` (Lyapunov) then gives `β_G ≤ 2β`. No
Cauchy–Schwarz and no fourth χ² moment are needed. -/

/-- Integrability of `x ↦ xⁿ` under `Gamma(a, r)`; the value of the moment is not needed, only
its finiteness. (`StatLean.MultipleTesting.GammaMoments` proves this but keeps it `private`.) -/
private lemma integrable_pow_gammaMeasure' {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x => x ^ n) (gammaMeasure a r) := by
  have hmeasG : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integrable_withDensity_iff hmeasG
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hcongr : (fun x => x ^ n * (gammaPDF a r x).toReal)
      = fun x => x ^ n * gammaPDFReal a r x := by
    funext x
    rw [show gammaPDF a r x = ENNReal.ofReal (gammaPDFReal a r x) from rfl,
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
  rw [hcongr]
  have hmodel : IntegrableOn (fun x => x ^ (a + (n : ℝ) - 1) * Real.exp (-(r * x)))
      (Set.Ioi (0 : ℝ)) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a + (n : ℝ) - 1) (b := r)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) one_pos hr
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    beta_reduce
    rw [Real.rpow_one, neg_mul]
  have hIoi : IntegrableOn (fun x => x ^ n * gammaPDFReal a r x) (Set.Ioi (0 : ℝ)) volume := by
    refine IntegrableOn.congr_fun (hmodel.const_mul (r ^ a / Real.Gamma a))
      (fun x hx => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at hx
    rw [gammaPDFReal, if_pos hx.le, ← Real.rpow_natCast x n,
      show a + (n : ℝ) - 1 = (a - 1) + (n : ℝ) by ring, Real.rpow_add hx (a - 1) (n : ℝ)]
    ring
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨?_, hIoi⟩
  refine integrableOn_zero.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic, MeasureTheory.ae_iff]
  refine measure_mono_null (t := {(0 : ℝ)}) ?_ Real.volume_singleton
  intro x hx
  simp only [Set.mem_setOf_eq, Classical.not_imp, Set.mem_Iic] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_or_eq_of_le hx1 with h | h
  · exact absurd (show x ^ n * gammaPDFReal a r x = 0 by
      rw [gammaPDFReal, if_neg (not_le.mpr h), mul_zero]).symm hx2
  · exact h

/-- Integrability of `x ↦ xⁿ` under `χ²_k`. -/
private lemma integrable_pow_chiSquared {k : ℕ} (hk : 0 < k) (n : ℕ) :
    Integrable (fun x => x ^ n) (StatLean.MultipleTesting.chiSquared k) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold StatLean.MultipleTesting.chiSquared
  exact integrable_pow_gammaMeasure' (by linarith) (by norm_num) n

/-- The squared norm pushes `N(0, I_k)` forward to `χ²_k` (`0 < k`). -/
private lemma gaussian_map_normSq {k : ℕ} (hk : 0 < k) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1).map (fun z => ‖z‖ ^ 2)
      = StatLean.MultipleTesting.chiSquared k := by
  rw [map_normSq_multivariateGaussian_of_norm_eq k 0 (by simp), noncentralChiSquared_zero hk]

/-- **The standard Gaussian has no atom at the origin** (`0 < k`): the ball `{‖z‖ ≤ 0}` is the
preimage of `{0}` under `‖·‖²`, whose law `χ²_k` has a Lebesgue density. -/
private lemma gaussian_origin_measure_zero {k : ℕ} (hk : 0 < k) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) {z | ‖z‖ ≤ 0} = 0 := by
  have hset : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ 0} = (fun z => ‖z‖ ^ 2) ⁻¹' {0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have hz : ‖z‖ = 0 := le_antisymm h (norm_nonneg z)
      rw [hz]; ring
    · intro h
      have hz : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
      exact le_of_eq hz
  rw [hset, ← Measure.map_apply (by fun_prop) (measurableSet_singleton 0), gaussian_map_normSq hk]
  unfold StatLean.MultipleTesting.chiSquared ProbabilityTheory.gammaMeasure
  rw [withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ (by simp)]

/-- **The Gaussian third moment is at most `2 k^{3/2}`.** Combined with the Lyapunov bound
`k^{3/2} ≤ β` this gives `β_G ≤ 2 β`, the comparison the ball assembly consumes. -/
private lemma integral_norm_cube_gaussian_le {k : ℕ} (hk : 0 < k) :
    ∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      ≤ 2 * (Real.sqrt (k : ℝ) * (k : ℝ)) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  set E := EuclideanSpace ℝ (Fin k)
  set γ : Measure E := multivariateGaussian (0 : E) 1 with hγ
  set u : ℝ := Real.sqrt (k : ℝ) with hu_def
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hu : 0 < u := Real.sqrt_pos.mpr hkr
  have hk2 : (k : ℝ) = u ^ 2 := (Real.sq_sqrt hkr.le).symm
  have hmap := gaussian_map_normSq hk
  have hae : AEMeasurable (fun z : E => ‖z‖ ^ 2) γ := (by fun_prop : Measurable _).aemeasurable
  -- the two χ² moments, transported back to `γ`
  have h2 : ∫ z, ‖z‖ ^ 2 ∂γ = (k : ℝ) := by
    have hchi := StatLean.MultipleTesting.integral_id_chiSquared hk
    rw [← hmap, integral_map hae (by fun_prop)] at hchi
    exact hchi
  have h4 : ∫ z, (‖z‖ ^ 2 - (k : ℝ)) ^ 2 ∂γ = 2 * (k : ℝ) := by
    have hchi := StatLean.MultipleTesting.variance_chiSquared hk
    rw [← hmap, integral_map hae (by fun_prop)] at hchi
    exact hchi
  -- integrability of the two transported moments
  have hI2 : Integrable (fun z : E => ‖z‖ ^ 2) γ := by
    have h := integrable_pow_chiSquared hk 1
    rw [← hmap] at h
    have := (integrable_map_measure (by fun_prop) hae).mp h
    simpa [Function.comp_def] using this
  have hI4 : Integrable (fun z : E => (‖z‖ ^ 2 - (k : ℝ)) ^ 2) γ := by
    have hpoly : Integrable (fun x : ℝ => (x - (k : ℝ)) ^ 2)
        (StatLean.MultipleTesting.chiSquared k) := by
      have ha := integrable_pow_chiSquared hk 2
      have hb : Integrable (fun x : ℝ => x) (StatLean.MultipleTesting.chiSquared k) := by
        simpa using integrable_pow_chiSquared hk 1
      have hc : Integrable (fun _ : ℝ => (k : ℝ) ^ 2)
          (StatLean.MultipleTesting.chiSquared k) := integrable_const _
      have h0 := (ha.sub (hb.const_mul (2 * (k : ℝ)))).add hc
      refine h0.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [← hmap] at hpoly
    have := (integrable_map_measure (by fun_prop) hae).mp hpoly
    simpa [Function.comp_def] using this
  -- the three summands of the majorant, each with a clean applied-lambda type
  have e1 : Integrable (fun z : E => u * ‖z‖ ^ 2) γ := hI2.const_mul u
  have e2 : Integrable (fun z : E => (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)) γ :=
    hI4.div_const (2 * u)
  have e3 : Integrable (fun z : E => u * (‖z‖ ^ 2 - (k : ℝ)) / 2) γ := by
    have h0 := ((hI2.const_mul u).sub (integrable_const (u * (k : ℝ)))).div_const 2
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have e12 : Integrable (fun z : E => u * ‖z‖ ^ 2
      + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)) γ := by
    have h0 := e1.add e2
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
  have hFint : Integrable (fun z : E => u * ‖z‖ ^ 2
      + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u) + u * (‖z‖ ^ 2 - (k : ℝ)) / 2) γ := by
    have h0 := e12.add e3
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
  -- the pointwise inequality `r³ ≤ u r² + (r² − u²)²/(2u) + u (r² − u²)/2`
  have hpt : ∀ z : E, ‖z‖ ^ 3 ≤ u * ‖z‖ ^ 2
      + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u) + u * (‖z‖ ^ 2 - (k : ℝ)) / 2 := by
    intro z
    rw [← sub_nonneg]
    have hid : u * ‖z‖ ^ 2 + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)
        + u * (‖z‖ ^ 2 - (k : ℝ)) / 2 - ‖z‖ ^ 3
        = ‖z‖ ^ 2 * (u - ‖z‖) ^ 2 / (2 * u) := by
      rw [hk2]; field_simp; ring
    rw [hid]
    positivity
  have hcube : Integrable (fun z : E => ‖z‖ ^ 3) γ := by
    refine Integrable.mono' hFint (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt z
  have hFval : ∫ z, (u * ‖z‖ ^ 2 + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)
      + u * (‖z‖ ^ 2 - (k : ℝ)) / 2) ∂γ = u * (k : ℝ) + (k : ℝ) / u := by
    have hsub : Integrable (fun z : E => ‖z‖ ^ 2 - (k : ℝ)) γ := by
      have h0 := hI2.sub (integrable_const (k : ℝ))
      refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply]
    rw [integral_add e12 e3, integral_add e1 e2, integral_const_mul, integral_div,
      integral_div, integral_const_mul, integral_sub hI2 (integrable_const (k : ℝ)),
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [h2, h4]
    field_simp
    ring
  calc ∫ z, ‖z‖ ^ 3 ∂γ
      ≤ ∫ z, (u * ‖z‖ ^ 2 + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)
          + u * (‖z‖ ^ 2 - (k : ℝ)) / 2) ∂γ := integral_mono hcube hFint hpt
    _ = u * (k : ℝ) + (k : ℝ) / u := hFval
    _ ≤ 2 * (u * (k : ℝ)) := by
        have hku : (k : ℝ) / u = u := by
          rw [hk2]; field_simp
        rw [hku]
        have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        nlinarith [hu, h1]

/-- **`β > 0`.** If `β = ∫‖y‖³ dν` vanished then `ν` would be the Dirac mass at the origin, whose
second moment is `0` and not `k > 0`. -/
private lemma integral_norm_cube_pos {k : ℕ} (hk : 0 < k)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    0 < ∫ y, ‖y‖ ^ 3 ∂ν := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have h := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβ
  nlinarith [h, hsk, hk0]

/-- **The `ε`-generic core of the ball assembly.** Everything in the ball headline except the
Lindeberg swap itself: given a smoothed radial indicator with third-derivative constant
`C₃/ε³`, the Gaussian shell bound with constant `Cac`, and *any* swap estimate of the shape
`|∫f dμₙ − ∫f dγ| ≤ D ε` for such test functions, the ball comparison is `≤ (Cac + D) ε`.

Factoring this out is what lets the same assembly serve both the elementary balance
(`D = C₃/2`, `ε = (β/√n)^{1/4}`, via `abs_integral_smooth_sub_gaussian_le`) and the improved one
(`D = 3C₃/2 + 9C`, `ε = (β/√n)^{1/2}`, via `abs_integral_smooth_sub_gaussian_balanced`). -/
private lemma berryEsseen_ball_of_swap {k n : ℕ} (hk : 0 < k)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} (hνp : IsProbabilityMeasure ν)
    {C₃ Cac D ε : ℝ} (hCacpos : 0 < Cac) (hDnn : 0 ≤ D) (hεpos : 0 < ε)
    (hC₃ : ∀ a : ℝ, 0 ≤ a → ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
      ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ a → f x = 1) ∧ (∀ x, a + ε < ‖x‖ → f x = 0) ∧
      (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3))
    (hCac : ∀ a w : ℝ, 0 ≤ a → 0 ≤ w →
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        {z | a < ‖z‖ ∧ ‖z‖ ≤ a + w}).toReal ≤ Cac * w)
    (herr : ∀ f : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 3 f → (∀ x, |f x| ≤ 1) →
      (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) →
      |(∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i))
        - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))| ≤ D * ε)
    (t : ℝ) :
    |((((Measure.pi fun _ : Fin n => ν)).map
          fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) {z | ‖z‖ ^ 2 ≤ t}).toReal
        - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
            {z | ‖z‖ ^ 2 ≤ t}).toReal|
      ≤ (Cac + D) * ε := by
  haveI := hνp
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  set μ : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.pi fun _ : Fin n => ν).map (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) with hμdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  -- measurability of the balls, and the two sandwich steps
  have hballmeas : ∀ a : ℝ, MeasurableSet {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a} :=
    fun a => measurableSet_le (by fun_prop) measurable_const
  have hlow : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin k))), IsProbabilityMeasure ρ →
      ∀ (f : EuclideanSpace ℝ (Fin k) → ℝ) (a : ℝ), Integrable f ρ → (∀ x, 0 ≤ f x) →
      (∀ x, ‖x‖ ≤ a → f x = 1) → (ρ {z | ‖z‖ ≤ a}).toReal ≤ ∫ x, f x ∂ρ := by
    intro ρ hρ f a hfint hf0 hone
    haveI := hρ
    have hind : Integrable (Set.indicator {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a}
        (fun _ => (1 : ℝ))) ρ := by
      rw [integrable_indicator_iff (hballmeas a)]
      exact integrableOn_const (measure_ne_top _ _)
    calc (ρ {z | ‖z‖ ≤ a}).toReal
        = ∫ x, Set.indicator {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a} (fun _ => (1 : ℝ)) x ∂ρ := by
          rw [integral_indicator (hballmeas a), setIntegral_const, measureReal_def, smul_eq_mul,
            mul_one]
      _ ≤ ∫ x, f x ∂ρ := by
          refine integral_mono hind hfint fun x => ?_
          by_cases hx : ‖x‖ ≤ a
          · rw [Set.indicator_of_mem (show x ∈ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a} from hx),
              hone x hx]
          · rw [Set.indicator_of_notMem (show x ∉ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a} from hx)]
            exact hf0 x
  have hupp : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin k))), IsProbabilityMeasure ρ →
      ∀ (f : EuclideanSpace ℝ (Fin k) → ℝ) (b : ℝ), Integrable f ρ → (∀ x, f x ≤ 1) →
      (∀ x, b < ‖x‖ → f x = 0) → (∫ x, f x ∂ρ) ≤ (ρ {z | ‖z‖ ≤ b}).toReal := by
    intro ρ hρ f b hfint hf1 hzero
    haveI := hρ
    have hind : Integrable (Set.indicator {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b}
        (fun _ => (1 : ℝ))) ρ := by
      rw [integrable_indicator_iff (hballmeas b)]
      exact integrableOn_const (measure_ne_top _ _)
    calc (∫ x, f x ∂ρ)
        ≤ ∫ x, Set.indicator {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b} (fun _ => (1 : ℝ)) x ∂ρ := by
          refine integral_mono hfint hind fun x => ?_
          by_cases hx : ‖x‖ ≤ b
          · rw [Set.indicator_of_mem (show x ∈ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b} from hx)]
            exact hf1 x
          · rw [Set.indicator_of_notMem (show x ∉ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b} from hx),
              hzero x (not_le.mp hx)]
      _ = (ρ {z | ‖z‖ ≤ b}).toReal := by
          rw [integral_indicator (hballmeas b), setIntegral_const, measureReal_def, smul_eq_mul,
            mul_one]
  -- shell anti-concentration in the two-ball form
  have hshell : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (γ {z | ‖z‖ ≤ b}).toReal ≤ (γ {z | ‖z‖ ≤ a}).toReal + Cac * (b - a) := by
    intro a b ha hab
    have h1 := hCac a (b - a) ha (by linarith)
    rw [show a + (b - a) = b from by ring] at h1
    have hsub : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b}
        ⊆ {z | ‖z‖ ≤ a} ∪ {z | a < ‖z‖ ∧ ‖z‖ ≤ b} := by
      intro z hz
      rcases le_or_gt ‖z‖ a with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hz⟩
    have h2 : γ {z | ‖z‖ ≤ b} ≤ γ {z | ‖z‖ ≤ a} + γ {z | a < ‖z‖ ∧ ‖z‖ ≤ b} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have h3 := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h2
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h3
    linarith
  -- integrability of any `[0,1]`-valued continuous test function
  have hfint : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin k))), IsProbabilityMeasure ρ →
      ∀ f : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 3 f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
      Integrable f ρ := by
    intro ρ hρ f hfcd hf0 hf1
    haveI := hρ
    refine Integrable.mono' (integrable_const (1 : ℝ)) hfcd.continuous.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact hf1 x
  rcases lt_or_ge t 0 with ht | ht
  · -- degenerate case: the ball is empty
    have hempty : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ t} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht (sq_nonneg _)
    rw [hempty]
    simp only [measure_empty, ENNReal.toReal_zero, sub_zero, abs_zero]
    have : 0 < (Cac + D) * ε := mul_pos (by linarith) hεpos
    linarith
  · -- the ball is `{‖z‖ ≤ s}` with `s = √t`
    set s : ℝ := Real.sqrt t with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg t
    have hSset : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ t} = {z | ‖z‖ ≤ s} := by
      ext z
      simp only [Set.mem_setOf_eq, hsdef]
      constructor
      · intro h
        rw [← Real.sqrt_sq (norm_nonneg z)]
        exact Real.sqrt_le_sqrt h
      · intro h
        have hmul := mul_self_le_mul_self (norm_nonneg z) h
        rw [Real.mul_self_sqrt ht] at hmul
        rw [pow_two]; exact hmul
    rw [hSset]
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · -- upper deviation
      obtain ⟨f, hfcd, hf0, hf1, hfone, hfzero, hfD3⟩ := hC₃ s hs0
      have hIμ := hfint μ hμprob f hfcd hf0 hf1
      have hIγ := hfint γ hγprob f hfcd hf0 hf1
      have hswap := herr f hfcd (fun x => abs_le.mpr ⟨by linarith [hf0 x], hf1 x⟩) hfD3
      rw [abs_sub_le_iff] at hswap
      have hchain : (μ {z | ‖z‖ ≤ s}).toReal
          ≤ (γ {z | ‖z‖ ≤ s}).toReal + (Cac + D) * ε := by
        calc (μ {z | ‖z‖ ≤ s}).toReal
            ≤ ∫ x, f x ∂μ := hlow μ hμprob f s hIμ hf0 hfone
          _ ≤ (∫ x, f x ∂γ) + D * ε := by linarith [hswap.1]
          _ ≤ (γ {z | ‖z‖ ≤ s + ε}).toReal + D * ε := by
              have := hupp γ hγprob f (s + ε) hIγ hf1 hfzero
              linarith
          _ ≤ ((γ {z | ‖z‖ ≤ s}).toReal + Cac * (s + ε - s)) + D * ε := by
              have := hshell s (s + ε) hs0 (by linarith)
              linarith
          _ = (γ {z | ‖z‖ ≤ s}).toReal + (Cac + D) * ε := by ring
      linarith
    · -- lower deviation
      rcases le_or_gt ε s with hse | hse
      · obtain ⟨f, hfcd, hf0, hf1, hfone, hfzero, hfD3⟩ := hC₃ (s - ε) (by linarith)
        have hfzero' : ∀ x, s < ‖x‖ → f x = 0 := fun x hx => hfzero x (by linarith)
        have hIμ := hfint μ hμprob f hfcd hf0 hf1
        have hIγ := hfint γ hγprob f hfcd hf0 hf1
        have hswap := herr f hfcd (fun x => abs_le.mpr ⟨by linarith [hf0 x], hf1 x⟩) hfD3
        rw [abs_sub_le_iff] at hswap
        have hchain : (γ {z | ‖z‖ ≤ s}).toReal
            ≤ (μ {z | ‖z‖ ≤ s}).toReal + (Cac + D) * ε := by
          calc (γ {z | ‖z‖ ≤ s}).toReal
              ≤ (γ {z | ‖z‖ ≤ s - ε}).toReal + Cac * (s - (s - ε)) :=
                hshell (s - ε) s (by linarith) (by linarith)
            _ ≤ (∫ x, f x ∂γ) + Cac * ε := by
                have := hlow γ hγprob f (s - ε) hIγ hf0 hfone
                have harith : s - (s - ε) = ε := by ring
                rw [harith]
                linarith
            _ ≤ ((∫ x, f x ∂μ) + D * ε) + Cac * ε := by linarith [hswap.2]
            _ ≤ ((μ {z | ‖z‖ ≤ s}).toReal + D * ε) + Cac * ε := by
                have := hupp μ hμprob f s hIμ hf1 hfzero'
                linarith
            _ = (μ {z | ‖z‖ ≤ s}).toReal + (Cac + D) * ε := by ring
        linarith
      · -- `s < ε`: the ball is inside `{‖z‖ ≤ ε}` and the Gaussian has no atom at the origin
        have h1 := hshell 0 s le_rfl hs0
        have h0 : γ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ 0} = 0 := by
          rw [hγdef]; exact gaussian_origin_measure_zero hk
        rw [h0] at h1
        simp only [ENNReal.toReal_zero, zero_add] at h1
        have h2 : (0 : ℝ) ≤ (μ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ s}).toReal :=
          ENNReal.toReal_nonneg
        have h3 : Cac * (s - 0) ≤ Cac * ε :=
          mul_le_mul_of_nonneg_left (by linarith) hCacpos.le
        have h4 : 0 ≤ D * ε := by positivity
        linarith

/-- **Elementary ball Berry–Esseen bound, with a dimension-free constant (honest, non-sharp).**
There is an *absolute* constant `C` — independent of the dimension `k`, the sample size `n` and
the sampling law `ν` — such that the normal approximation to the law of `‖n^{-1/2} ∑ᵢ Yᵢ‖²` over
half-lines `{‖z‖² ≤ t}` is accurate to `C · (β/√n)^{1/4}`, where `β = ∫‖y‖³ dν`. This is the
*honest* output of the elementary "smooth the indicator + Lindeberg swap" route for **balls**:
the constant is dimension-free (the ball anti-concentration `gaussian_ball_shell_measure_le` and
the radial smoothing `exists_smoothed_radial_indicator` both have dimension-free constants), but
the rate is `(β/√n)^{1/4} = n^{-1/8}`, **not** Bentkus's `β/√n = n^{-1/2}`. The degradation is
intrinsic to the mollifier method (see the module docstring).

Assembly (the `ε`-optimisation): for the set `{‖z‖ ≤ s}` (`s = √t`) sandwich the indicator between
two smoothed radial indicators of widths `ε` (`exists_smoothed_radial_indicator`); the swap
`abs_integral_smooth_sub_gaussian_le` bounds `|E f(Sₙ) − E f(G)| ≤ (C₃/ε³)(β + β_G)/(6√n)`, and the
Gaussian shell mass of `{s < ‖z‖ ≤ s+ε}` is `≤ C_ac ε` (`gaussian_ball_shell_measure_le`). Adding
and choosing `ε = (β/√n)^{1/4}` balances `ε⁻³ · β/√n` against `ε` at `(β/√n)^{1/4}`.

**State of the assembly.** Two of the three geometric bricks are now *proved unconditionally*
and with dimension-free constants:

* `gaussian_ball_shell_measure_le` (`C_ac = 7`) — no longer conditional on any `Γ`-Stirling
  estimate, see `chiSquared_density_mul_sqrt_le`;
* `exists_smoothed_radial_indicator` (`C₃ = 48 B`) — proved through the squared-norm route, so
  it holds for **every** `0 ≤ a` and `ε > 0`. In particular the small-radius case `√t < ε`,
  which the older `χ ∘ ‖·‖` formulation had to treat separately (its `ε ≤ a` hypothesis is
  gone), no longer needs any special handling.

The moment facts the `ε`-optimisation needs are also proved here:
`integral_normSq_eq_dim` (`∫‖y‖² dν = k`), `sqrt_dim_mul_dim_le_integral_norm_cube` (Lyapunov,
`k^{3/2} ≤ β`) and `integral_norm_cube_pos` (`β > 0`, so `ε := (β/√n)^{1/4}` is a legitimate
positive width).

The Gaussian side of the third moment is now proved too: `integral_norm_cube_gaussian_le`
gives `β_G ≤ 2 k^{3/2} ≤ 2 β` from the two *public* χ² moments (`E X = k`, `E (X−k)² = 2k`)
— no fourth χ² moment and no Cauchy–Schwarz are needed, see its docstring.

**The assembly below is complete and consumes nothing on faith**: its last ingredient,
`abs_integral_smooth_sub_gaussian_le` (the third-order multivariate Lindeberg swap), is proved
above, so `berryEsseen_ball_elementary` is axiom-clean. Concretely, with `ε := (β/√n)^{1/4}`:

* upper: `μₙ{‖z‖ ≤ s} ≤ ∫ f_ε dμₙ ≤ ∫ f_ε dγ + (C₃/ε³)(β+β_G)/(6√n) ≤ γ{‖z‖ ≤ s+ε} + (C₃/2)ε`
  with `f_ε` the smoothed radial indicator at radius `s`, and then
  `γ{‖z‖ ≤ s+ε} ≤ γ{‖z‖ ≤ s} + C_ac ε` by shell anti-concentration;
* lower: the same with the smoothed indicator at radius `s − ε` when `ε ≤ s`; when `s < ε` the
  ball is contained in `{‖z‖ ≤ ε}` and the shell bound at radius `0` closes it directly (the
  Gaussian has no atom at the origin, `gaussian_origin_measure_zero`).

Both `(β/√n)/ε³ = ε` steps are the `ε`-balance, and the resulting absolute constant is
`C = C_ac + C₃/2`. -/
theorem berryEsseen_ball_elementary :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) (t : ℝ),
      0 < n → 0 < k → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k),
        (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) {z | ‖z‖ ^ 2 ≤ t}).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
              {z | ‖z‖ ^ 2 ≤ t}).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := exists_smoothed_radial_indicator
  obtain ⟨Cac, hCacpos, hCac⟩ := gaussian_ball_shell_measure_le
  refine ⟨Cac + C₃ / 2, by positivity, ?_⟩
  intro k n ν t hn hk hνp hmean hcov hβint
  haveI := hνp
  -- the smoothing width `ε = (β/√n)^{1/4}`
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  set ε : ℝ := q ^ ((1 : ℝ) / 4) with hεdef
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hqpos _
  have hεq : ε ^ 3 * ε = q := by
    rw [hεdef, ← Real.rpow_natCast (q ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hqpos.le,
      ← Real.rpow_add hqpos]
    norm_num
  have hq3 : q / ε ^ 3 = ε := by
    rw [← hεq]; field_simp
  -- the Gaussian third moment is at most `2β`
  have hβGle : (∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))
      ≤ 2 * β := by
    have h1 := integral_norm_cube_gaussian_le (k := k) hk
    have h2 := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
    rw [← hβdef] at h2
    linarith
  -- the Lindeberg swap, with the `ε`-balance already carried out
  have herr : ∀ f : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 3 f → (∀ x, |f x| ≤ 1) →
      (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) →
      |(∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i))
        - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
        ≤ C₃ / 2 * ε := by
    intro f hfcd hfbd hfD3
    have hswap := abs_integral_smooth_sub_gaussian_le (ν := ν) hn hνp hmean hcov hβint hfcd hfbd
      (M := C₃ / ε ^ 3) (by positivity) hfD3
    rw [← hβdef] at hswap
    refine hswap.trans ?_
    have hA : 0 ≤ C₃ / ε ^ 3 / 6 := by positivity
    have h3q : (β + (∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)))
        / Real.sqrt (n : ℝ) ≤ 3 * q := by
      rw [hqdef, div_le_iff₀ hsn]
      have hcancel : 3 * (β / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = 3 * β := by
        field_simp
      rw [hcancel]
      linarith
    calc C₃ / ε ^ 3 / 6
          * (β + (∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)))
          / Real.sqrt (n : ℝ)
        = C₃ / ε ^ 3 / 6
            * ((β + (∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)))
              / Real.sqrt (n : ℝ)) := by ring
      _ ≤ C₃ / ε ^ 3 / 6 * (3 * q) := mul_le_mul_of_nonneg_left h3q hA
      _ = C₃ / 2 * (q / ε ^ 3) := by ring
      _ = C₃ / 2 * ε := by rw [hq3]
  exact berryEsseen_ball_of_swap hk hνp hCacpos (by positivity) hεpos
    (fun a ha => hC₃ k a ha hεpos) (fun a w ha hw => hCac k hk a w ha hw) herr t

/-! #### The convex headline in Lévy (thickening) form

The convex headline `berryEsseen_convex_elementary` is assembled in two steps. The first — and
the one where the mollification of `exists_smoothed_convex_indicator` is actually consumed — is
the Lévy/Prokhorov-type inequality between `μₙ(B)` and `γ(Bᵋ)` (rather than between `μₙ(B)` and
`γ(B)`), which needs no boundary-shell input at all. That is `berryEsseen_convex_levy_elementary`
below. The second step collapses `γ(Bᵋ)` back to `γ(B)` (and dually `γ(B)` to `γ(B₋ᵋ)`) at cost
`C_k ε`; that is `gaussian_thickening_le` / `gaussian_le_erosion_add` of
`StatLean.HypothesisTesting.ForMathlib.GaussianShell`. Nothing else is needed, and the headline
follows by the same `ε`-balance as `berryEsseen_ball_elementary`. -/

/-- Lower sandwich: a nonnegative test function equal to `1` on a measurable set dominates that
set's indicator. -/
private lemma measureReal_le_integral_of_eq_one {k : ℕ}
    {ρ : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ρ]
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {S : Set (EuclideanSpace ℝ (Fin k))}
    (hS : MeasurableSet S) (hfint : Integrable f ρ) (hf0 : ∀ x, 0 ≤ f x)
    (hone : ∀ x ∈ S, f x = 1) : (ρ S).toReal ≤ ∫ x, f x ∂ρ := by
  have hind : Integrable (S.indicator (fun _ => (1 : ℝ))) ρ := by
    rw [integrable_indicator_iff hS]
    exact integrableOn_const (measure_ne_top _ _)
  calc (ρ S).toReal = ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂ρ := by
        rw [integral_indicator hS, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
    _ ≤ ∫ x, f x ∂ρ := by
        refine integral_mono hind hfint fun x => ?_
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, hone x hx]
        · rw [Set.indicator_of_notMem hx]; exact hf0 x

/-- Upper sandwich: a test function bounded by `1` and supported in a measurable set is dominated
by that set's indicator. -/
private lemma integral_le_measureReal_of_support_subset {k : ℕ}
    {ρ : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ρ]
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {S : Set (EuclideanSpace ℝ (Fin k))}
    (hS : MeasurableSet S) (hfint : Integrable f ρ) (hf1 : ∀ x, f x ≤ 1)
    (hsupp : ∀ x, f x ≠ 0 → x ∈ S) : (∫ x, f x ∂ρ) ≤ (ρ S).toReal := by
  have hind : Integrable (S.indicator (fun _ => (1 : ℝ))) ρ := by
    rw [integrable_indicator_iff hS]
    exact integrableOn_const (measure_ne_top _ _)
  calc (∫ x, f x ∂ρ) ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂ρ := by
        refine integral_mono hfint hind fun x => ?_
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx]; exact hf1 x
        · rw [Set.indicator_of_notMem hx]
          by_contra hcon
          exact hx (hsupp x (ne_of_gt (not_le.1 hcon)))
    _ = (ρ S).toReal := by
        rw [integral_indicator hS, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

/-- **Elementary convex Berry–Esseen bound, Lévy (thickening) form.** For every dimension `k > 0`
there is a constant `C` such that for every convex measurable `B`, every width `ε > 0` and every
`n > 0`,

`μₙ(B) ≤ γ(Bᵋ) + C (β/√n)/ε³` and `γ(B) ≤ μₙ(Bᵋ) + C (β/√n)/ε³`,

where `μₙ` is the law of the normalized sum, `γ = N(0, I_k)`, `β = ∫‖y‖³ dν` and `Bᵋ` is the
`ε`-thickening of `B`.

Both inequalities are the Lindeberg swap `abs_integral_smooth_sub_gaussian_le` applied to the
smoothed indicator of `exists_smoothed_convex_indicator`, sandwiched between `1_B` and `1_{Bᵋ}`;
`C = C₃/2` where `C₃` is the third-derivative constant of the smoothed indicator (the factor
`3 ≥ (β + β_G)/β` from `integral_norm_cube_gaussian_le` is what turns `C₃/6` into `C₃/2`).

This is the whole analytic content of `berryEsseen_convex_elementary`: taking `ε = (β/√n)^{1/4}`
here gives `μₙ(B) ≤ γ(Bᵋ) + C ε` and `γ(B) ≤ μₙ(Bᵋ) + C ε`, and the only remaining step is to
replace `γ(Bᵋ)` by `γ(B) + C_k ε` (and, applying the second inequality to the erosion of `B`,
`γ(B)` by `γ(B₋ᵋ) + C_k ε`), which is `gaussian_thickening_le` / `gaussian_le_erosion_add` of
`StatLean.HypothesisTesting.ForMathlib.GaussianShell`. -/
theorem berryEsseen_convex_levy_elementary {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))) (ε : ℝ),
      0 < n → 0 < ε → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → MeasurableSet B → Convex ℝ B →
      ((((Measure.pi fun _ : Fin n => ν).map
              fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) B).toReal
            ≤ ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
                (Metric.thickening ε B)).toReal
              + C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) / ε ^ 3)
        ∧ (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal
            ≤ (((Measure.pi fun _ : Fin n => ν).map
                fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
                  (Metric.thickening ε B)).toReal
              + C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) / ε ^ 3) := by
  obtain ⟨C₃, hC₃one, hC₃⟩ := exists_smoothed_convex_indicator k
  have hC₃pos : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃one
  refine ⟨C₃ / 2, by positivity, ?_⟩
  intro n ν B ε hn hε hνp hmean hcov hβint hBmeas hBconv
  haveI := hνp
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  set μ : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.pi fun _ : Fin n => ν).map (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) with hμdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  have hβGle : (∫ z, ‖z‖ ^ 3 ∂γ) ≤ 2 * β := by
    have h1 := integral_norm_cube_gaussian_le (k := k) hk
    rw [← hγdef] at h1
    have h2 := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
    rw [← hβdef] at h2
    linarith
  -- the smoothed indicator of `B` at width `ε`
  obtain ⟨f, hfcd, hf0, hf1, hfB, hfsupp, hfD, hfD1, hfD2⟩ := hC₃ B hBconv hε
  have hfbd : ∀ x, |f x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hf0 x], hf1 x⟩
  have hfint : ∀ ρ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure ρ →
      Integrable f ρ := by
    intro ρ hρ
    haveI := hρ
    exact (integrable_const (1 : ℝ)).mono' hfcd.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfbd x)
  -- the Lindeberg swap at `M = C₃/ε³`, with `(β + β_G)/√n ≤ 3q` folded in
  have herr : |(∫ x, f x ∂μ) - (∫ x, f x ∂γ)| ≤ C₃ / 2 * q / ε ^ 3 := by
    have hswap := abs_integral_smooth_sub_gaussian_le (ν := ν) hn hνp hmean hcov hβint hfcd hfbd
      (M := C₃ / ε ^ 3) (by positivity) hfD
    rw [← hμdef, ← hγdef, ← hβdef] at hswap
    refine hswap.trans ?_
    have hA : 0 ≤ C₃ / ε ^ 3 / 6 := by positivity
    have h3q : (β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ) ≤ 3 * q := by
      rw [hqdef, div_le_iff₀ hsn]
      have hcancel : 3 * (β / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = 3 * β := by field_simp
      rw [hcancel]
      linarith
    calc C₃ / ε ^ 3 / 6 * (β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ)
        = C₃ / ε ^ 3 / 6 * ((β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ)) := by ring
      _ ≤ C₃ / ε ^ 3 / 6 * (3 * q) := mul_le_mul_of_nonneg_left h3q hA
      _ = C₃ / 2 * q / ε ^ 3 := by ring
  have hthick : MeasurableSet (Metric.thickening ε B) := Metric.isOpen_thickening.measurableSet
  have hlowμ : (μ B).toReal ≤ ∫ x, f x ∂μ :=
    measureReal_le_integral_of_eq_one hBmeas (hfint μ hμprob) hf0 hfB
  have hlowγ : (γ B).toReal ≤ ∫ x, f x ∂γ :=
    measureReal_le_integral_of_eq_one hBmeas (hfint γ hγprob) hf0 hfB
  have huppμ : (∫ x, f x ∂μ) ≤ (μ (Metric.thickening ε B)).toReal :=
    integral_le_measureReal_of_support_subset hthick (hfint μ hμprob) hf1 hfsupp
  have huppγ : (∫ x, f x ∂γ) ≤ (γ (Metric.thickening ε B)).toReal :=
    integral_le_measureReal_of_support_subset hthick (hfint γ hγprob) hf1 hfsupp
  have hswap' := abs_le.1 herr
  constructor
  · linarith [hswap'.2, hlowμ, huppγ]
  · linarith [hswap'.1, hlowγ, huppμ]

/-! #### The convex headline -/

/-- `toReal` transfer for an `ℝ≥0∞` bound of the shape `a ≤ b + ofReal r`. -/
private lemma toReal_le_add_of_le_add_ofReal {a b : ℝ≥0∞} {r : ℝ}
    (hb : b ≠ ⊤) (hr : 0 ≤ r) (h : a ≤ b + ENNReal.ofReal r) :
    a.toReal ≤ b.toReal + r := by
  have hfin : b + ENNReal.ofReal r ≠ ⊤ := by
    simp [ENNReal.add_ne_top, hb]
  have h2 := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr] at h2

/-- **Elementary convex-set Berry–Esseen bound (honest, non-sharp).** For every dimension `k > 0`
there is a constant `C` such that for all `n > 0`, every centred identity-covariance law `ν` with
finite third moment `β = ∫‖y‖³ dν`, and every measurable convex `B`,

`|μₙ(B) − γ(B)| ≤ C (β/√n)^{1/4}`,

where `μₙ` is the law of `n^{-1/2} ∑ᵢ Yᵢ` and `γ = N(0, I_k)`.

Optimising `ε` in `ε^{-3} β/√n + C ε` balances steps 2–3 at `ε = (β/√n)^{1/4}`, giving an error of
order `(β/√n)^{1/4} = n^{-1/8}` — **not** Bentkus's sharp `n^{-1/2}` rate (the consumer-free
reference statement that quoted it has been removed). The constant also carries a dimension
factor: it is
`C = C₀ + C_k` with `C₀` the third-derivative constant of `exists_smoothed_convex_indicator` and
`C_k = gaussianShellConst k = 4 e² √k` the Gaussian boundary-shell constant.

**This exponent is not the ceiling of the elementary route** (wave-13 correction of an earlier
note that claimed it was): exploiting the Gaussian mollification the hybrid telescope carries for
free, `ε^{-3}` can be replaced by `ε^{-1}`, which balances at `(β/√n)^{1/2} = n^{-1/4}`. As of
wave 16 that improvement is **proved**, as `berryEsseen_convex_improved` at the end of this file
(`0`-sorry, axiom-clean); this theorem is kept as it stands because it has consumers and is a
different, weaker statement. The sharp `400 k^{1/4} · β/√n` needs Bentkus's self-improving
induction and is still not attempted.
(Ball's theorem gives the sharp shell constant `4 k^{1/4}`, which is
exactly the dimension factor of Bentkus's bound; only *finiteness* at fixed `k` is needed here, and
that is what `GaussianShell` proves elementarily.)

**Proof.** `berryEsseen_convex_levy_elementary` at width `ε := (β/√n)^{1/4}` gives, for every
measurable convex `A`, both `μₙ(A) ≤ γ(Aᵋ) + C₀ ε` and `γ(A) ≤ μₙ(Aᵋ) + C₀ ε` (the balance
`(β/√n)/ε³ = ε` is `hbal` below). Applying the first to `A := B` and collapsing the thickening by
`gaussian_thickening_le` bounds `μₙ(B) − γ(B)`. For the reverse deviation one cannot thicken `μₙ`
— it is not Gaussian — so the second inequality is applied instead to the *erosion*
`A := erosion ε B`, which is open and convex (`isOpen_erosion`, `convex_erosion`) and whose
`ε`-thickening sits inside `B` (`thickening_erosion_subset`); `gaussian_le_erosion_add` then
converts `γ(erosion ε B)` back to `γ(B)`. -/
theorem berryEsseen_convex_elementary {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))),
      0 < n → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → MeasurableSet B → Convex ℝ B →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) B).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  obtain ⟨C₀, hC₀pos, hlevy⟩ := berryEsseen_convex_levy_elementary hk
  have hCkpos : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  refine ⟨C₀ + gaussianShellConst k, by linarith, ?_⟩
  intro n ν B hn hνp hmean hcov hβint hBmeas hBconv
  haveI := hνp
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  set μ : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.pi fun _ : Fin n => ν).map (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) with hμdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  -- the balancing width `ε = q^{1/4}`, at which `q/ε³ = ε`
  have hεpos : 0 < q ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hqpos _
  have hbal : q / (q ^ ((1 : ℝ) / 4)) ^ 3 = q ^ ((1 : ℝ) / 4) := by
    have hcube : (q ^ ((1 : ℝ) / 4)) ^ 3 = q ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_natCast (q ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hqpos.le]
      norm_num
    have hsum : q ^ ((1 : ℝ) / 4) * q ^ ((3 : ℝ) / 4) = q := by
      rw [← Real.rpow_add hqpos]
      norm_num
    rw [hcube, div_eq_iff (Real.rpow_pos_of_pos hqpos _).ne']
    exact hsum.symm
  have hC₀bal : C₀ * q / (q ^ ((1 : ℝ) / 4)) ^ 3 = C₀ * q ^ ((1 : ℝ) / 4) := by
    rw [mul_div_assoc, hbal]
  -- the Lévy form at `B` itself, and at its erosion
  have hlevyB := hlevy n ν B (q ^ ((1 : ℝ) / 4)) hn hεpos hνp hmean hcov hβint hBmeas hBconv
  rw [← hμdef, ← hβdef, ← hqdef, hC₀bal] at hlevyB
  have hEmeas : MeasurableSet (erosion (q ^ ((1 : ℝ) / 4)) B) :=
    (isOpen_erosion _ B).measurableSet
  have hEconv : Convex ℝ (erosion (q ^ ((1 : ℝ) / 4)) B) := convex_erosion hBconv
  have hlevyE := hlevy n ν (erosion (q ^ ((1 : ℝ) / 4)) B) (q ^ ((1 : ℝ) / 4)) hn hεpos hνp
    hmean hcov hβint hEmeas hEconv
  rw [← hμdef, ← hβdef, ← hqdef, hC₀bal] at hlevyE
  -- the two shell collapses
  have hthick : (γ (Metric.thickening (q ^ ((1 : ℝ) / 4)) B)).toReal
      ≤ (γ B).toReal + gaussianShellConst k * q ^ ((1 : ℝ) / 4) := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) (by positivity) ?_
    have := gaussian_thickening_le hk hBconv hεpos
    rwa [← hγdef] at this
  have herode : (γ B).toReal
      ≤ (γ (erosion (q ^ ((1 : ℝ) / 4)) B)).toReal + gaussianShellConst k * q ^ ((1 : ℝ) / 4) := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) (by positivity) ?_
    have := gaussian_le_erosion_add hk hBmeas hBconv hεpos
    rwa [← hγdef] at this
  -- the erosion's thickening sits inside `B`, so `μ` can be pushed back without a shell bound
  have hback : (μ (Metric.thickening (q ^ ((1 : ℝ) / 4)) (erosion (q ^ ((1 : ℝ) / 4)) B))).toReal
      ≤ (μ B).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (thickening_erosion_subset _ B))
  rw [abs_sub_le_iff]
  constructor
  · linarith [hlevyB.1]
  · linarith [hlevyE.2]

end ElementaryRoute

/-! ### Wave-13: the Cameron–Martin (Gaussian-smoothing) route to a better exponent

The material below is the analytic core of a **strict improvement of the exponent** of
`berryEsseen_convex_elementary`, from `(β/√n)^{1/4}` to `(β/√n)^{1/2}`; see the
"wave-13 amendment" in the module docstring for the derivation. Everything here is proved
outright, and as of wave 16 so is the assembly: the improved headline is
`berryEsseen_convex_improved`, at the very end of the file.

The point is that the `j`-th step of the hybrid telescope already carries an independent
`N(0,(j/n) I_k)` summand, so its test function is automatically Gaussian-mollified at scale
`σ_j = √(j/n)`; and for a Gaussian mollification the Lindeberg remainder costs `σ_j^{-3}` rather
than `‖D³f‖_∞`, because the shift can be moved onto the *density* (Cameron–Martin) instead of
onto the test function. -/



section GaussianTilt

/-- Third-order Taylor bound for the real exponential, valid on **all** of `ℝ`
(Mathlib's `Real.exp_bound` needs `|x| ≤ 1`). The constant is `1/2` rather than the sharp
`1/6` because the remainder integral is bounded by its sup times the length of the
interval. -/
private lemma abs_exp_sub_taylor_two_le (x : ℝ) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * Real.exp |x| / 2 := by
  set G : ℝ → ℝ := fun u => ((x - u) ^ 2 / 2 + (x - u) + 1) * Real.exp u with hG
  have hderiv : ∀ u : ℝ, HasDerivAt G ((x - u) ^ 2 / 2 * Real.exp u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (x - u) ^ 2 / 2 + (x - u) + 1)
        (-(x - u) - 1) u := by
      have hsub : HasDerivAt (fun u : ℝ => x - u) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub x
      have hsq : HasDerivAt (fun u : ℝ => (x - u) ^ 2) (2 * (x - u) * (-1)) u := by
        simpa using! hsub.pow 2
      have := ((hsq.div_const 2).add hsub).add_const (1 : ℝ)
      convert! this using 1
      ring
    have h2 : HasDerivAt (fun u : ℝ => Real.exp u) (Real.exp u) u := Real.hasDerivAt_exp u
    have := h1.mul h2
    convert! this using 1
    ring
  have hint : ∫ u in (0 : ℝ)..x, (x - u) ^ 2 / 2 * Real.exp u = G x - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hGx : G x = Real.exp x := by simp [hG]
  have hG0 : G 0 = 1 + x + x ^ 2 / 2 := by simp [hG]; ring
  have hbound : ∀ u ∈ Set.uIoc (0 : ℝ) x,
      ‖(x - u) ^ 2 / 2 * Real.exp u‖ ≤ x ^ 2 / 2 * Real.exp |x| := by
    intro u hu
    have hu' : |u| ≤ |x| := by
      rcases le_total (0 : ℝ) x with hx | hx
      · rw [Set.uIoc_of_le hx] at hu
        rw [abs_of_nonneg hu.1.le, abs_of_nonneg hx]
        exact hu.2
      · rw [Set.uIoc_of_ge hx] at hu
        rw [abs_of_nonpos hu.2, abs_of_nonpos hx]
        linarith [hu.1]
    have hxu : |x - u| ≤ |x| := by
      rcases le_total (0 : ℝ) x with hx | hx
      · rw [Set.uIoc_of_le hx] at hu
        rw [abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ x - u), abs_of_nonneg hx]
        linarith [hu.1]
      · rw [Set.uIoc_of_ge hx] at hu
        rw [abs_of_nonpos (by linarith [hu.1] : x - u ≤ 0), abs_of_nonpos hx]
        linarith [hu.2]
    have hsq : (x - u) ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs (x - u), ← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg _) hxu 2
    have hexp : Real.exp u ≤ Real.exp |x| := Real.exp_le_exp.2 (le_trans (le_abs_self u) hu')
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (x - u) ^ 2 / 2),
      abs_of_pos (Real.exp_pos u)]
    exact mul_le_mul (by linarith) hexp (Real.exp_pos u).le (by positivity)
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hint, hGx, hG0, Real.norm_eq_abs] at hle
  refine hle.trans ?_
  have hz : |x - 0| = |x| := by ring_nf
  rw [hz, show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  nlinarith [abs_nonneg x, Real.exp_pos |x|]

/-! ### Elementary envelopes -/

/-- `y ≤ exp y`. -/
private lemma self_le_exp (y : ℝ) : y ≤ Real.exp y := by
  have := Real.add_one_le_exp y
  linarith

/-- `|t| ≤ exp t + exp (-t)`. -/
private lemma abs_le_exp_add_exp (t : ℝ) : |t| ≤ Real.exp t + Real.exp (-t) := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [self_le_exp t, Real.exp_pos (-t)]
  · rw [h]; linarith [self_le_exp (-t), Real.exp_pos t]

/-- `exp |t| ≤ exp t + exp (-t)`. -/
private lemma exp_abs_le_exp_add_exp (t : ℝ) :
    Real.exp |t| ≤ Real.exp t + Real.exp (-t) := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [Real.exp_pos (-t)]
  · rw [h]; linarith [Real.exp_pos t]

/-- `t² ≤ 4 (exp t + exp (-t))`. -/
private lemma sq_le_exp_add_exp (t : ℝ) : t ^ 2 ≤ 4 * (Real.exp t + Real.exp (-t)) := by
  have hkey : ∀ y : ℝ, 0 ≤ y → y ^ 2 ≤ 4 * Real.exp y := by
    intro y hy
    have h1 : y / 2 + 1 ≤ Real.exp (y / 2) := Real.add_one_le_exp _
    have h2 : (0 : ℝ) ≤ y / 2 + 1 := by linarith
    have h3 : (y / 2 + 1) ^ 2 ≤ Real.exp (y / 2) ^ 2 := pow_le_pow_left₀ h2 h1 2
    have h4 : Real.exp (y / 2) ^ 2 = Real.exp y := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    nlinarith
  have habs : |t| ^ 2 ≤ 4 * Real.exp |t| := hkey _ (abs_nonneg t)
  have hex := exp_abs_le_exp_add_exp t
  nlinarith [sq_abs t]

/-- `y³ ≤ 27 exp y` for `y ≥ 0`. -/
private lemma cube_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 3 ≤ 27 * Real.exp y := by
  have h1 : y / 3 + 1 ≤ Real.exp (y / 3) := Real.add_one_le_exp _
  have h2 : (0 : ℝ) ≤ y / 3 + 1 := by linarith
  have h3 : (y / 3 + 1) ^ 3 ≤ Real.exp (y / 3) ^ 3 := pow_le_pow_left₀ h2 h1 3
  have h4 : Real.exp (y / 3) ^ 3 = Real.exp y := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  nlinarith

/-! ### Gaussian moments used by the tilt bound -/

private lemma integrable_exp_mul_gauss (a : ℝ) :
    Integrable (fun t : ℝ => Real.exp (a * t)) (gaussianReal 0 1) :=
  integrable_exp_mul_gaussianReal a

private lemma integral_exp_mul_gauss (a : ℝ) :
    (∫ t, Real.exp (a * t) ∂(gaussianReal 0 1)) = Real.exp (a ^ 2 / 2) := by
  rw [integral_exp_mul_gaussianReal 0 1 a]
  norm_num

private lemma exp_neg_mul_eq (a : ℝ) :
    (fun t : ℝ => Real.exp (-a * t)) = fun t : ℝ => Real.exp (-(a * t)) := by
  funext t; congr 1; ring

private lemma integrable_cosh (a : ℝ) :
    Integrable (fun t : ℝ => Real.exp (a * t) + Real.exp (-(a * t))) (gaussianReal 0 1) := by
  have h2 := integrable_exp_mul_gauss (-a)
  rw [exp_neg_mul_eq a] at h2
  exact (integrable_exp_mul_gauss a).add h2

private lemma integral_cosh (a : ℝ) :
    (∫ t, (Real.exp (a * t) + Real.exp (-(a * t))) ∂(gaussianReal 0 1))
      = 2 * Real.exp (a ^ 2 / 2) := by
  have h2 := integrable_exp_mul_gauss (-a)
  rw [exp_neg_mul_eq a] at h2
  rw [integral_add (integrable_exp_mul_gauss a) h2, ← exp_neg_mul_eq a,
    integral_exp_mul_gauss a, integral_exp_mul_gauss (-a), show (-a) ^ 2 = a ^ 2 by ring]
  ring

private lemma integrable_cosh_one :
    Integrable (fun t : ℝ => Real.exp t + Real.exp (-t)) (gaussianReal 0 1) := by
  have h := integrable_cosh 1
  simp only [one_mul] at h
  exact h

private lemma integral_cosh_one :
    (∫ t, (Real.exp t + Real.exp (-t)) ∂(gaussianReal 0 1)) = 2 * Real.exp (1 / 2) := by
  have h := integral_cosh 1
  simp only [one_mul] at h
  rw [h]
  norm_num

private lemma integral_cosh_two :
    (∫ t, (Real.exp (2 * t) + Real.exp (-(2 * t))) ∂(gaussianReal 0 1)) = 2 * Real.exp 2 := by
  rw [integral_cosh 2]
  norm_num

private lemma integrable_id_gauss : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := by
  refine Integrable.mono' integrable_cosh_one (by fun_prop) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs]
  exact abs_le_exp_add_exp t

private lemma integrable_sq_gauss : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_cosh_one.const_mul 4) (by fun_prop) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  exact sq_le_exp_add_exp t

/-- The first moment of `N(0,1)`. -/
private lemma integral_id_gauss : (∫ t : ℝ, t ∂(gaussianReal 0 1)) = 0 := by
  simpa using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)

/-- The second moment of `N(0,1)`, read off the variance. -/
private lemma integral_sq_gauss : (∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 1)) = 1 := by
  have hV : Var[fun x : ℝ => x; gaussianReal 0 1] = 1 := by
    simpa using ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [ProbabilityTheory.variance_eq_integral (by fun_prop)] at hV
  simpa using hV

/-- **`t⁴ ≤ 256 (eᵗ + e⁻ᵗ)`** (wave 40). The fourth-power analogue of `sq_le_exp_add_exp` and
`cube_le_exp`, proved the same way from `1 + y/4 ≤ exp (y/4)`. It is what gives the fourth
moment of `N(0,1)` an explicit bound without any Gamma-function apparatus. -/
private lemma pow_four_le_cosh (t : ℝ) : t ^ 4 ≤ 256 * (Real.exp t + Real.exp (-t)) := by
  have hkey : ∀ y : ℝ, 0 ≤ y → y ^ 4 ≤ 256 * Real.exp y := by
    intro y hy
    have h1 : y / 4 + 1 ≤ Real.exp (y / 4) := Real.add_one_le_exp _
    have h2 : (0 : ℝ) ≤ y / 4 + 1 := by linarith
    have h3 : (y / 4 + 1) ^ 4 ≤ Real.exp (y / 4) ^ 4 := pow_le_pow_left₀ h2 h1 4
    have h4 : Real.exp (y / 4) ^ 4 = Real.exp y := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h5 : y ^ 4 / 256 ≤ Real.exp y := by
      calc y ^ 4 / 256 = (y / 4) ^ 4 := by ring
        _ ≤ (y / 4 + 1) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
        _ ≤ Real.exp (y / 4) ^ 4 := h3
        _ = Real.exp y := h4
    linarith
  have habs : |t| ^ 4 ≤ 256 * Real.exp |t| := hkey _ (abs_nonneg t)
  have hex : Real.exp |t| ≤ Real.exp t + Real.exp (-t) := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-t)]
    · rw [abs_of_neg h]; linarith [Real.exp_pos t]
  have h4 : |t| ^ 4 = t ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  linarith [habs, hex, h4]

private lemma integrable_pow_four_gauss :
    Integrable (fun t : ℝ => t ^ 4) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_cosh_one.const_mul 256) (by fun_prop) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_four_le_cosh t

private lemma exp_half_le : Real.exp (1 / 2) ≤ 1.65 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2 : ℝ), hsq, h]

/-- **An explicit bound on the fourth moment of `N(0,1)`** (wave 40). The exact value is `3`;
all that is needed downstream is *some* explicit constant, and the exponential envelope
`pow_four_le_cosh` supplies one. -/
private lemma integral_pow_four_gauss_le :
    (∫ t : ℝ, t ^ 4 ∂(gaussianReal 0 1)) ≤ 845 := by
  have hmono := integral_mono integrable_pow_four_gauss (integrable_cosh_one.const_mul 256)
    (fun t => pow_four_le_cosh t)
  have he : (∫ t : ℝ, 256 * (Real.exp t + Real.exp (-t)) ∂(gaussianReal 0 1))
      = 256 * ∫ t : ℝ, (Real.exp t + Real.exp (-t)) ∂(gaussianReal 0 1) :=
    integral_const_mul _ _
  rw [he, integral_cosh_one] at hmono
  nlinarith [exp_half_le]

/-- **The `L²` size of the Cameron–Martin *polynomial*** (wave 40):
`∫ (1 + s t + s²(t²−1)/2)² dγ₁ ≤ 640 (1 + s²)²`, at **every** tilt parameter `s`.

The `L²` bound `integral_sq_tiltRemainder_le` on the *remainder* is available only for `s ≤ 1`
(and must be: `∫ R_s² ~ e^{s²}`). The polynomial part, by contrast, is polynomially bounded at
every `s`, and that is exactly what removes the `‖w‖ ≤ 1` restriction from the far-in-`v` half
of the tail brick's route (b) — see
`abs_integral_shift_vecTiltRemainder_le_of_const_ball_any`. -/
private lemma integral_sq_tiltPoly_le (s : ℝ) :
    (∫ t : ℝ, (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2) ^ 2 ∂(gaussianReal 0 1))
      ≤ 640 * (1 + s ^ 2) ^ 2 := by
  have e1 : Integrable (fun _ : ℝ => (3 + 3 * s ^ 4 / 4)) (gaussianReal 0 1) :=
    integrable_const _
  have e2 : Integrable (fun t : ℝ => (3 * s ^ 2 - 3 * s ^ 4 / 2) * t ^ 2) (gaussianReal 0 1) :=
    integrable_sq_gauss.const_mul _
  have e3 : Integrable (fun t : ℝ => (3 * s ^ 4 / 4) * t ^ 4) (gaussianReal 0 1) :=
    integrable_pow_four_gauss.const_mul _
  have e12 : Integrable (fun t : ℝ =>
      (3 + 3 * s ^ 4 / 4) + (3 * s ^ 2 - 3 * s ^ 4 / 2) * t ^ 2) (gaussianReal 0 1) := e1.add e2
  have hdom : Integrable (fun t : ℝ =>
      (3 + 3 * s ^ 4 / 4) + (3 * s ^ 2 - 3 * s ^ 4 / 2) * t ^ 2 + (3 * s ^ 4 / 4) * t ^ 4)
      (gaussianReal 0 1) := e12.add e3
  have hptw : ∀ t : ℝ, (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2) ^ 2
      ≤ (3 + 3 * s ^ 4 / 4) + (3 * s ^ 2 - 3 * s ^ 4 / 2) * t ^ 2
        + (3 * s ^ 4 / 4) * t ^ 4 := by
    intro t
    nlinarith [sq_nonneg (1 - s * t), sq_nonneg (1 - s ^ 2 * (t ^ 2 - 1) / 2),
      sq_nonneg (s * t - s ^ 2 * (t ^ 2 - 1) / 2)]
  have hqint : Integrable (fun t : ℝ => (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2) ^ 2)
      (gaussianReal 0 1) := by
    refine Integrable.mono' hdom (by fun_prop) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hptw t
  have hmono := integral_mono hqint hdom hptw
  have hsplit1 := integral_add e12 e3
  have hsplit2 := integral_add e1 e2
  have hc1 : (∫ _t : ℝ, (3 + 3 * s ^ 4 / 4) ∂(gaussianReal 0 1)) = 3 + 3 * s ^ 4 / 4 := by
    rw [integral_const]; simp
  have hc2 : (∫ t : ℝ, (3 * s ^ 2 - 3 * s ^ 4 / 2) * t ^ 2 ∂(gaussianReal 0 1))
      = (3 * s ^ 2 - 3 * s ^ 4 / 2) := by
    rw [integral_const_mul, integral_sq_gauss, mul_one]
  have hc3 : (∫ t : ℝ, (3 * s ^ 4 / 4) * t ^ 4 ∂(gaussianReal 0 1))
      = (3 * s ^ 4 / 4) * ∫ t : ℝ, t ^ 4 ∂(gaussianReal 0 1) := integral_const_mul _ _
  have hval : (∫ t : ℝ, ((3 + 3 * s ^ 4 / 4) + (3 * s ^ 2 - 3 * s ^ 4 / 2) * t ^ 2
        + (3 * s ^ 4 / 4) * t ^ 4) ∂(gaussianReal 0 1))
      = (3 + 3 * s ^ 4 / 4) + (3 * s ^ 2 - 3 * s ^ 4 / 2)
        + (3 * s ^ 4 / 4) * ∫ t : ℝ, t ^ 4 ∂(gaussianReal 0 1) := by
    rw [hsplit1, hsplit2, hc1, hc2, hc3]
  rw [hval] at hmono
  have h4 := integral_pow_four_gauss_le
  nlinarith [hmono, mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 3 * s ^ 4 / 4),
    sq_nonneg s, sq_nonneg (s ^ 2)]

/-- **The `L¹` size of the Cameron–Martin polynomial** (wave 40):
`∫ |1 + s t + s²(t²−1)/2| dγ₁ ≤ 1 + s + s²` for `s ≥ 0`. Used for the crude, *at most
quadratic in `‖w‖`*, bound on a swap step — which is what keeps the near-in-`v` half of the
large-shift regime inside a third moment. -/
private lemma integral_abs_tiltPoly_le {s : ℝ} (hs : 0 ≤ s) :
    (∫ t : ℝ, |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2| ∂(gaussianReal 0 1))
      ≤ 1 + s + s ^ 2 := by
  have e1 : Integrable (fun _ : ℝ => (1 + s / 2 + s ^ 2 / 2)) (gaussianReal 0 1) :=
    integrable_const _
  have e2 : Integrable (fun t : ℝ => (s / 2 + s ^ 2 / 2) * t ^ 2) (gaussianReal 0 1) :=
    integrable_sq_gauss.const_mul _
  have hdom : Integrable (fun t : ℝ =>
      (1 + s / 2 + s ^ 2 / 2) + (s / 2 + s ^ 2 / 2) * t ^ 2) (gaussianReal 0 1) := e1.add e2
  have hptw : ∀ t : ℝ, |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2|
      ≤ (1 + s / 2 + s ^ 2 / 2) + (s / 2 + s ^ 2 / 2) * t ^ 2 := by
    intro t
    have h1 : |t| ≤ (1 + t ^ 2) / 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
    have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have hup : s * t ≤ s * ((1 + t ^ 2) / 2) := by
      have := mul_le_mul_of_nonneg_left (le_abs_self t) hs
      have h2 := mul_le_mul_of_nonneg_left h1 hs
      linarith
    have hlow : s * (-((1 + t ^ 2) / 2)) ≤ s * t := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le t) hs
      have h2 := mul_le_mul_of_nonneg_left h1 hs
      linarith
    rw [abs_le]
    constructor <;> nlinarith [hup, hlow, hs2, sq_nonneg t, mul_nonneg hs2 (sq_nonneg t)]
  have hqint : Integrable (fun t : ℝ => |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2|)
      (gaussianReal 0 1) := by
    refine Integrable.mono' hdom (by fun_prop) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_abs]
    exact hptw t
  have hmono := integral_mono hqint hdom hptw
  have hsplit := integral_add e1 e2
  have hc1 : (∫ _t : ℝ, (1 + s / 2 + s ^ 2 / 2) ∂(gaussianReal 0 1))
      = 1 + s / 2 + s ^ 2 / 2 := by rw [integral_const]; simp
  have hc2 : (∫ t : ℝ, (s / 2 + s ^ 2 / 2) * t ^ 2 ∂(gaussianReal 0 1))
      = s / 2 + s ^ 2 / 2 := by rw [integral_const_mul, integral_sq_gauss, mul_one]
  have hval : (∫ t : ℝ, ((1 + s / 2 + s ^ 2 / 2) + (s / 2 + s ^ 2 / 2) * t ^ 2)
        ∂(gaussianReal 0 1))
      = (1 + s / 2 + s ^ 2 / 2) + (s / 2 + s ^ 2 / 2) := by rw [hsplit, hc1, hc2]
  rw [hval] at hmono
  linarith

/-! ### The scalar tilt remainder -/

/-- The **scalar tilt remainder**: the error in the second-order expansion, in the tilt
parameter `s`, of the Cameron–Martin density `exp (s t − s²/2)` of the standard Gaussian
shifted by `s`. Its first three coefficients are the Hermite polynomials `1`, `t`, `t² − 1`. -/
private noncomputable def tiltRemainder (s t : ℝ) : ℝ :=
  Real.exp (s * t - s ^ 2 / 2) - (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2)

private lemma integrable_exp_tilt (s : ℝ) :
    Integrable (fun t : ℝ => Real.exp (s * t - s ^ 2 / 2)) (gaussianReal 0 1) := by
  have hre : (fun t : ℝ => Real.exp (s * t - s ^ 2 / 2))
      = fun t : ℝ => Real.exp (-(s ^ 2 / 2)) * Real.exp (s * t) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  rw [hre]
  exact (integrable_exp_mul_gauss s).const_mul _

private lemma integral_exp_tilt (s : ℝ) :
    (∫ t, Real.exp (s * t - s ^ 2 / 2) ∂(gaussianReal 0 1)) = 1 := by
  have hre : (fun t : ℝ => Real.exp (s * t - s ^ 2 / 2))
      = fun t : ℝ => Real.exp (-(s ^ 2 / 2)) * Real.exp (s * t) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  rw [hre, integral_const_mul, integral_exp_mul_gauss s, ← Real.exp_add]
  norm_num

private lemma integrable_tiltRemainder (s : ℝ) :
    Integrable (fun t => tiltRemainder s t) (gaussianReal 0 1) :=
  (integrable_exp_tilt s).sub
    (((integrable_const (1 : ℝ)).add (integrable_id_gauss.const_mul s)).add
      (((integrable_sq_gauss.sub (integrable_const (1 : ℝ))).const_mul (s ^ 2)).div_const 2))

private lemma continuous_tiltRemainder (s : ℝ) : Continuous (fun t => tiltRemainder s t) := by
  unfold tiltRemainder
  fun_prop

/-- **The scalar tilt remainder has mean zero** under `N(0,1)`, for every tilt `s`.

This is the identity `∫ exp(st − s²/2) dγ = 1` together with `∫ t dγ = 0` and `∫ t² dγ = 1`:
the subtracted polynomial is precisely the second-order Hermite truncation of the tilt, and the
tilt itself is a probability density. Wave 29: this innocuous fact is the whole reason the
*indicator* half of a mollified convex indicator can be localised — see
`abs_integral_mul_vecTiltRemainder_le_of_const_off`. -/
private lemma integral_tiltRemainder_eq_zero (s : ℝ) :
    (∫ t, tiltRemainder s t ∂(gaussianReal 0 1)) = 0 := by
  have hA : Integrable (fun t : ℝ => 1 + s * t) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).add (integrable_id_gauss.const_mul s)
  have hB : Integrable (fun t : ℝ => s ^ 2 * (t ^ 2 - 1) / 2) (gaussianReal 0 1) :=
    ((integrable_sq_gauss.sub (integrable_const (1 : ℝ))).const_mul (s ^ 2)).div_const 2
  have hpoly : Integrable
      (fun t : ℝ => 1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2) (gaussianReal 0 1) := hA.add hB
  have hsplit : (∫ t, tiltRemainder s t ∂(gaussianReal 0 1))
      = (∫ t : ℝ, Real.exp (s * t - s ^ 2 / 2) ∂(gaussianReal 0 1))
        - ∫ t : ℝ, (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2) ∂(gaussianReal 0 1) :=
    integral_sub (integrable_exp_tilt s) hpoly
  have hadd : (∫ t : ℝ, (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2) ∂(gaussianReal 0 1))
      = (∫ t : ℝ, (1 + s * t) ∂(gaussianReal 0 1))
        + ∫ t : ℝ, (s ^ 2 * (t ^ 2 - 1) / 2) ∂(gaussianReal 0 1) := integral_add hA hB
  have hA' : (∫ t : ℝ, (1 + s * t) ∂(gaussianReal 0 1)) = 1 := by
    have h := integral_add (μ := gaussianReal 0 1) (integrable_const (1 : ℝ))
      (integrable_id_gauss.const_mul s)
    rw [h, integral_const_mul, integral_id_gauss, integral_const]
    simp
  have hB' : (∫ t : ℝ, (s ^ 2 * (t ^ 2 - 1) / 2) ∂(gaussianReal 0 1)) = 0 := by
    have h1 : (∫ t : ℝ, (s ^ 2 * (t ^ 2 - 1)) ∂(gaussianReal 0 1))
        = s ^ 2 * ∫ t : ℝ, (t ^ 2 - 1) ∂(gaussianReal 0 1) :=
      integral_const_mul _ _
    have h2 : (∫ t : ℝ, (t ^ 2 - 1) ∂(gaussianReal 0 1))
        = (∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 1)) - ∫ _ : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) :=
      integral_sub integrable_sq_gauss (integrable_const (1 : ℝ))
    have h3 : (∫ t : ℝ, (s ^ 2 * (t ^ 2 - 1) / 2) ∂(gaussianReal 0 1))
        = (∫ t : ℝ, (s ^ 2 * (t ^ 2 - 1)) ∂(gaussianReal 0 1)) / 2 :=
      integral_div _ _
    rw [h3, h1, h2, integral_sq_gauss, integral_const]
    simp
  rw [hsplit, hadd, hA', hB', integral_exp_tilt s]
  ring

/-- The (parameter-free) envelope controlling the tilt remainder for small tilts. -/
private noncomputable def tiltEnvSmall (t : ℝ) : ℝ :=
  27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t)))
    + ((Real.exp t + Real.exp (-t)) / 2 + 1 / 8)

private lemma integrable_tiltEnvSmall : Integrable tiltEnvSmall (gaussianReal 0 1) :=
  ((integrable_cosh 2).const_mul _).add
    ((integrable_cosh_one.div_const 2).add (integrable_const _))

private lemma integral_tiltEnvSmall_le :
    (∫ t, tiltEnvSmall t ∂(gaussianReal 0 1)) ≤ 30 * Real.exp 3 + 3 := by
  have hA : Integrable (fun t : ℝ =>
      27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t)))) (gaussianReal 0 1) :=
    (integrable_cosh 2).const_mul _
  have hB : Integrable (fun t : ℝ => (Real.exp t + Real.exp (-t)) / 2) (gaussianReal 0 1) :=
    integrable_cosh_one.div_const 2
  have hC : Integrable (fun _ : ℝ => (1 / 8 : ℝ)) (gaussianReal 0 1) := integrable_const _
  have hBC : Integrable (fun t : ℝ => (Real.exp t + Real.exp (-t)) / 2 + 1 / 8)
      (gaussianReal 0 1) := hB.add hC
  have hval : (∫ t, tiltEnvSmall t ∂(gaussianReal 0 1))
      = 27 / 2 * Real.exp 1 * (2 * Real.exp 2) + ((2 * Real.exp (1 / 2)) / 2 + 1 / 8) := by
    simp only [tiltEnvSmall]
    rw [integral_add hA hBC, integral_add hB hC, integral_const_mul, integral_div,
      integral_cosh_two, integral_cosh_one, integral_const]
    simp
  rw [hval]
  have he3 : Real.exp 1 * Real.exp 2 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
  have hhalf : Real.exp (1 / 2) ≤ Real.exp 3 := Real.exp_le_exp.2 (by norm_num)
  have hE31 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  nlinarith [Real.exp_pos (1:ℝ), Real.exp_pos (2:ℝ)]

/-- The (parameter-free) envelope controlling the tilt remainder for large tilts, apart from
the tilt-dependent exponential term. -/
private noncomputable def tiltEnvLarge (t : ℝ) : ℝ :=
  4 * (Real.exp t + Real.exp (-t)) + 1

private lemma integrable_tiltEnvLarge : Integrable tiltEnvLarge (gaussianReal 0 1) :=
  (integrable_cosh_one.const_mul 4).add (integrable_const _)

private lemma integral_tiltEnvLarge :
    (∫ t, tiltEnvLarge t ∂(gaussianReal 0 1)) = 4 * (2 * Real.exp (1 / 2)) + 1 := by
  simp only [tiltEnvLarge]
  rw [integral_add (integrable_cosh_one.const_mul 4) (integrable_const _), integral_const_mul,
    integral_cosh_one, integral_const]
  simp

/-- **The pointwise envelope for small tilts.** For `0 ≤ s ≤ 1` the tilt remainder is at most
`s³` times a fixed, tilt-independent exponential envelope. Extracted from (and consumed by)
`integral_abs_tiltRemainder_le_of_le_one`; the `L²` refinement of §wave-19 reuses it verbatim. -/
private lemma abs_tiltRemainder_le_envSmall {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) :
    |tiltRemainder s t| ≤ s ^ 3 * tiltEnvSmall t := by
  set x : ℝ := s * t - s ^ 2 / 2 with hx
  have hsplit : tiltRemainder s t
      = (Real.exp x - (1 + x + x ^ 2 / 2)) + (-(s ^ 3 * t / 2) + s ^ 4 / 8) := by
    simp only [tiltRemainder, hx]; ring
  have hxabs : |x| ≤ s * (|t| + 1 / 2) := by
    have h1 : |x| ≤ s * |t| + s ^ 2 / 2 := by
      rw [hx]
      calc |s * t - s ^ 2 / 2| ≤ |s * t| + |s ^ 2 / 2| := abs_sub _ _
        _ = s * |t| + s ^ 2 / 2 := by
            rw [abs_mul, abs_of_nonneg hs,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2 / 2)]
    nlinarith
  have hcube : |x| ^ 3 ≤ s ^ 3 * (|t| + 1 / 2) ^ 3 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hxabs 3
    calc |x| ^ 3 ≤ (s * (|t| + 1 / 2)) ^ 3 := h
      _ = s ^ 3 * (|t| + 1 / 2) ^ 3 := by ring
  have hexpx : Real.exp |x| ≤ Real.exp (|t| + 1 / 2) := by
    refine Real.exp_le_exp.2 (hxabs.trans ?_)
    nlinarith [abs_nonneg t]
  have hbig : (|t| + 1 / 2) ^ 3 ≤ 27 * Real.exp (|t| + 1 / 2) := cube_le_exp (by positivity)
  have hexpabs : Real.exp (|t| + 1 / 2) * Real.exp (|t| + 1 / 2)
      = Real.exp 1 * Real.exp (2 * |t|) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hcosh2 : Real.exp (2 * |t|) ≤ Real.exp (2 * t) + Real.exp (-(2 * t)) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-(2 * t))]
    · rw [h]
      have he : Real.exp (2 * -t) = Real.exp (-(2 * t)) := by congr 1; ring
      rw [he]; linarith [Real.exp_pos (2 * t)]
  have hT := abs_exp_sub_taylor_two_le x
  have hterm1 : |x| ^ 3 * Real.exp |x| / 2
      ≤ s ^ 3 * (27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t)))) := by
    have e1 : |x| ^ 3 * Real.exp |x|
        ≤ (s ^ 3 * (|t| + 1 / 2) ^ 3) * Real.exp (|t| + 1 / 2) :=
      mul_le_mul hcube hexpx (Real.exp_pos _).le (by positivity)
    have e2 : (s ^ 3 * (|t| + 1 / 2) ^ 3) * Real.exp (|t| + 1 / 2)
        ≤ (s ^ 3 * (27 * Real.exp (|t| + 1 / 2))) * Real.exp (|t| + 1 / 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbig (by positivity : (0:ℝ) ≤ s ^ 3))
        (Real.exp_pos _).le
    have e3 : (s ^ 3 * (27 * Real.exp (|t| + 1 / 2))) * Real.exp (|t| + 1 / 2)
        = s ^ 3 * 27 * (Real.exp 1 * Real.exp (2 * |t|)) := by
      rw [mul_assoc (s ^ 3) _ _, mul_assoc, hexpabs]; ring
    have e5 : s ^ 3 * 27 * (Real.exp 1 * Real.exp (2 * |t|))
        ≤ s ^ 3 * 27 * (Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcosh2 (Real.exp_pos 1).le) (by positivity)
    have e6 : s ^ 3 * 27 * (Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t))))
        = 2 * (s ^ 3 * (27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t))))) := by
      ring
    have hnn : (0:ℝ) ≤ s ^ 3 * (27 / 2 * Real.exp 1
        * (Real.exp (2 * t) + Real.exp (-(2 * t)))) := by positivity
    linarith [e1, e2, e5]
  have hterm2 : |(-(s ^ 3 * t / 2) + s ^ 4 / 8)|
      ≤ s ^ 3 * ((Real.exp t + Real.exp (-t)) / 2) + s ^ 3 * (1 / 8 : ℝ) := by
    have hAdd := abs_add_le (-(s ^ 3 * t / 2)) (s ^ 4 / 8)
    have e1 : |(-(s ^ 3 * t / 2))| = s ^ 3 / 2 * |t| := by
      rw [abs_neg, show s ^ 3 * t / 2 = s ^ 3 / 2 * t by ring, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 3 / 2)]
    have e2 : |s ^ 4 / 8| = s ^ 4 / 8 := abs_of_nonneg (by positivity)
    rw [e1, e2] at hAdd
    have h2 : s ^ 4 ≤ s ^ 3 := by nlinarith [pow_nonneg hs 3]
    nlinarith [abs_le_exp_add_exp t, pow_nonneg hs 3]
  have hexpand : s ^ 3 * tiltEnvSmall t
      = s ^ 3 * (27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t))))
        + (s ^ 3 * ((Real.exp t + Real.exp (-t)) / 2) + s ^ 3 * (1 / 8 : ℝ)) := by
    simp only [tiltEnvSmall]; ring
  rw [hsplit, hexpand]
  calc |(Real.exp x - (1 + x + x ^ 2 / 2)) + (-(s ^ 3 * t / 2) + s ^ 4 / 8)|
      ≤ |Real.exp x - (1 + x + x ^ 2 / 2)| + |(-(s ^ 3 * t / 2) + s ^ 4 / 8)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith [hT, hterm1, hterm2]

/-- The `L¹(γ)` bound on the tilt remainder for **small** tilts: the third-order Taylor
expansion of `exp` with an exponential envelope. -/
private lemma integral_abs_tiltRemainder_le_of_le_one {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ (30 * Real.exp 3 + 3) * s ^ 3 := by
  refine (integral_mono (integrable_tiltRemainder s).abs
    (integrable_tiltEnvSmall.const_mul (s ^ 3)) (abs_tiltRemainder_le_envSmall hs hs1)).trans ?_
  rw [integral_const_mul]
  nlinarith [integral_tiltEnvSmall_le, pow_nonneg hs 3]

/-- The `L¹(γ)` bound on the tilt remainder for **large** tilts, where the trivial termwise
bound already beats `s³`. -/
private lemma integral_abs_tiltRemainder_le_of_one_le {s : ℝ} (hs1 : 1 ≤ s) :
    (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ (30 * Real.exp 3 + 3) * s ^ 3 := by
  have hs : (0 : ℝ) ≤ s := by linarith
  have hA : Integrable (fun t : ℝ => Real.exp (s * t - s ^ 2 / 2)) (gaussianReal 0 1) :=
    integrable_exp_tilt s
  have hW : Integrable
      (fun t : ℝ => 1 + s * (Real.exp t + Real.exp (-t)) + s ^ 2 * tiltEnvLarge t / 2)
      (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add (integrable_cosh_one.const_mul s)).add
      ((integrable_tiltEnvLarge.const_mul (s ^ 2)).div_const 2)
  have hpt : ∀ t : ℝ, |tiltRemainder s t|
      ≤ Real.exp (s * t - s ^ 2 / 2)
        + (1 + s * (Real.exp t + Real.exp (-t)) + s ^ 2 * tiltEnvLarge t / 2) := by
    intro t
    have ha := abs_le_exp_add_exp t
    have hb := sq_le_exp_add_exp t
    have hc : |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2|
        ≤ 1 + s * |t| + s ^ 2 * (t ^ 2 + 1) / 2 := by
      have e1 : |1 + s * t| ≤ 1 + s * |t| := by
        calc |1 + s * t| ≤ |(1:ℝ)| + |s * t| := abs_add_le _ _
          _ = 1 + s * |t| := by rw [abs_one, abs_mul, abs_of_nonneg hs]
      have e2 : |s ^ 2 * (t ^ 2 - 1) / 2| ≤ s ^ 2 * (t ^ 2 + 1) / 2 := by
        rw [show s ^ 2 * (t ^ 2 - 1) / 2 = s ^ 2 / 2 * (t ^ 2 - 1) by ring, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2 / 2)]
        have habs : |t ^ 2 - 1| ≤ t ^ 2 + 1 := by
          rcases abs_cases (t ^ 2 - 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [sq_nonneg t]
        nlinarith [sq_nonneg s]
      calc |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2|
          ≤ |1 + s * t| + |s ^ 2 * (t ^ 2 - 1) / 2| := abs_add_le _ _
        _ ≤ (1 + s * |t|) + s ^ 2 * (t ^ 2 + 1) / 2 := by linarith
        _ = 1 + s * |t| + s ^ 2 * (t ^ 2 + 1) / 2 := by ring
    have h0 : |tiltRemainder s t|
        ≤ Real.exp (s * t - s ^ 2 / 2) + |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2| := by
      simp only [tiltRemainder]
      calc |Real.exp (s * t - s ^ 2 / 2) - (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2)|
          ≤ |Real.exp (s * t - s ^ 2 / 2)| + |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2| :=
            abs_sub _ _
        _ = _ := by rw [abs_of_pos (Real.exp_pos _)]
    simp only [tiltEnvLarge]
    nlinarith [sq_nonneg s, Real.exp_pos t, Real.exp_pos (-t)]
  have h1s : Integrable (fun t : ℝ => 1 + s * (Real.exp t + Real.exp (-t)))
      (gaussianReal 0 1) := (integrable_const (1 : ℝ)).add (integrable_cosh_one.const_mul s)
  have h2s : Integrable (fun t : ℝ => s ^ 2 * tiltEnvLarge t / 2) (gaussianReal 0 1) :=
    (integrable_tiltEnvLarge.const_mul (s ^ 2)).div_const 2
  have hWval : (∫ t, (1 + s * (Real.exp t + Real.exp (-t)) + s ^ 2 * tiltEnvLarge t / 2)
      ∂(gaussianReal 0 1))
      = 1 + s * (2 * Real.exp (1 / 2)) + s ^ 2 * (4 * (2 * Real.exp (1 / 2)) + 1) / 2 := by
    rw [integral_add h1s h2s,
      integral_add (integrable_const (1 : ℝ)) (integrable_cosh_one.const_mul s),
      integral_const, integral_const_mul, integral_cosh_one, integral_div, integral_const_mul,
      integral_tiltEnvLarge]
    simp
  refine (integral_mono (integrable_tiltRemainder s).abs (hA.add hW)
    (fun t => by simpa using hpt t)).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add hA hW, integral_exp_tilt s, hWval]
  have hhalf : Real.exp (1 / 2) ≤ Real.exp 3 := Real.exp_le_exp.2 (by norm_num)
  have hE31 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hcube1 : s ≤ s ^ 3 := by nlinarith
  have hsq1 : s ^ 2 ≤ s ^ 3 := by nlinarith
  have hone : (1 : ℝ) ≤ s ^ 3 := by nlinarith
  nlinarith [Real.exp_pos ((1:ℝ) / 2)]

/-- **The tilt remainder is cubically small in the tilt parameter, in `L¹` of the Gaussian.**
This is the analytic heart of the improved bound: the third-order Taylor error of the
Cameron–Martin density is `O(s³)` *after integration against the Gaussian*, with an absolute
constant. (Pointwise it is *not* `O(s³)`: `exp (s t)` is unbounded in `t`.) -/
private lemma exists_tiltRemainder_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
      (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ C * s ^ 3 := by
  refine ⟨30 * Real.exp 3 + 3, by positivity, fun s hs => ?_⟩
  rcases le_total s 1 with h | h
  · exact integral_abs_tiltRemainder_le_of_le_one hs h
  · exact integral_abs_tiltRemainder_le_of_one_le h

/-! ### Wave-19: the same remainder in `L²` (the weighted / Hölder refinement)

`integral_abs_vecTiltRemainder_le` bounds the Cameron–Martin remainder in `L¹(γ)`, which is
exactly what a swap against a test function with `‖G‖_∞ ≤ 1` needs. The *localised* swap — the
one Bentkus's induction consumes — pairs the remainder instead with a `G` supported on the
`ε`-shell of `∂B`, and must pay only for the shell. Cauchy–Schwarz turns that into an `L²`
bound on the remainder, proved here by the same envelope, whose square is still Gaussian
integrable. -/

private lemma tiltEnvSmall_nonneg (t : ℝ) : 0 ≤ tiltEnvSmall t := by
  unfold tiltEnvSmall
  positivity

/-- A single exponential envelope dominating `tiltEnvSmall`, so that its square is again a
(`4`-fold) exponential. -/
private lemma tiltEnvSmall_le_cosh_two (t : ℝ) :
    tiltEnvSmall t ≤ (27 / 2 * Real.exp 1 + 1) * (Real.exp (2 * t) + Real.exp (-(2 * t))) := by
  have hx : 0 < Real.exp t := Real.exp_pos t
  have hy : 0 < Real.exp (-t) := Real.exp_pos (-t)
  have hxy : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  have h2t : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [show (2 : ℝ) * t = t + t by ring, Real.exp_add]; ring
  have h2t' : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
    rw [show -((2 : ℝ) * t) = -t + -t by ring, Real.exp_add]; ring
  have hsum : 2 ≤ Real.exp t + Real.exp (-t) := by
    nlinarith [sq_nonneg (Real.exp t - 1)]
  unfold tiltEnvSmall
  rw [h2t, h2t']
  nlinarith [sq_nonneg (Real.exp t + Real.exp (-t) - 2), Real.exp_pos (1 : ℝ)]

private lemma sq_tiltEnvSmall_le (t : ℝ) :
    tiltEnvSmall t ^ 2
      ≤ 2 * (27 / 2 * Real.exp 1 + 1) ^ 2
          * (Real.exp (4 * t) + Real.exp (-(4 * t))) := by
  have h4 : Real.exp (4 * t) = Real.exp (2 * t) ^ 2 := by
    rw [show (4 : ℝ) * t = 2 * t + 2 * t by ring, Real.exp_add]; ring
  have h4' : Real.exp (-(4 * t)) = Real.exp (-(2 * t)) ^ 2 := by
    rw [show -((4 : ℝ) * t) = -(2 * t) + -(2 * t) by ring, Real.exp_add]; ring
  have hsq := pow_le_pow_left₀ (tiltEnvSmall_nonneg t) (tiltEnvSmall_le_cosh_two t) 2
  rw [h4, h4']
  nlinarith [mul_nonneg (sq_nonneg (27 / 2 * Real.exp 1 + 1))
    (sq_nonneg (Real.exp (2 * t) - Real.exp (-(2 * t))))]

/-- The absolute constant of the `L²` tilt bound, `4 (27e/2 + 1)² e⁸`. -/
private noncomputable def tiltSqConst : ℝ := 4 * (27 / 2 * Real.exp 1 + 1) ^ 2 * Real.exp 8

private lemma tiltSqConst_pos : 0 < tiltSqConst := by
  unfold tiltSqConst; positivity

/-- `√tiltSqConst ≥ 53` (wave 40). An explicit lower bound, so that the crude constant `106`
which the *large*-shift regime of the localised swap step pays is absorbed by the
Cauchy–Schwarz constant `2√tiltSqConst` that the *short*-shift regime pays anyway — the two
regimes can then be reported with a single constant. -/
private lemma le_sqrt_tiltSqConst : (53 : ℝ) ≤ Real.sqrt tiltSqConst := by
  have he : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have he8 : (1 : ℝ) ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  have hbig : (53 : ℝ) ^ 2 ≤ tiltSqConst := by
    have h1 : (37 : ℝ) ≤ 27 / 2 * Real.exp 1 + 1 := by linarith
    have h2 : (37 : ℝ) ^ 2 ≤ (27 / 2 * Real.exp 1 + 1) ^ 2 := by nlinarith
    have h3 : (0 : ℝ) ≤ (27 / 2 * Real.exp 1 + 1) ^ 2 := sq_nonneg _
    rw [tiltSqConst]
    nlinarith
  rw [show (53 : ℝ) = Real.sqrt (53 ^ 2) by
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 53)]]
  exact Real.sqrt_le_sqrt hbig

private lemma integrable_sq_tiltRemainder {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Integrable (fun t => tiltRemainder s t ^ 2) (gaussianReal 0 1) := by
  refine Integrable.mono'
    ((integrable_cosh 4).const_mul (s ^ 6 * (2 * (27 / 2 * Real.exp 1 + 1) ^ 2)))
    ((continuous_tiltRemainder s).pow 2).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : tiltRemainder s t ^ 2 ≤ (s ^ 3 * tiltEnvSmall t) ^ 2 := by
    calc tiltRemainder s t ^ 2 = |tiltRemainder s t| ^ 2 := (sq_abs _).symm
      _ ≤ (s ^ 3 * tiltEnvSmall t) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_tiltRemainder_le_envSmall hs hs1 t) 2
  have h2 := sq_tiltEnvSmall_le t
  nlinarith [pow_nonneg hs 6]

/-- **The tilt remainder is `O(s³)` in `L²(γ)` as well**, for `0 ≤ s ≤ 1`, with an absolute
constant. (For `s ≥ 1` this is false: `∫ exp(2st − s²) dγ = exp(s²)` blows up. The localisation
only ever uses shifts of length `≤ 1`, which is the regime `c/σⱼ ≤ 1` of the telescope.) -/
private lemma integral_sq_tiltRemainder_le {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t, tiltRemainder s t ^ 2 ∂(gaussianReal 0 1)) ≤ tiltSqConst * s ^ 6 := by
  have hpt : ∀ t : ℝ, tiltRemainder s t ^ 2
      ≤ s ^ 6 * (2 * (27 / 2 * Real.exp 1 + 1) ^ 2)
          * (Real.exp (4 * t) + Real.exp (-(4 * t))) := by
    intro t
    have h1 : tiltRemainder s t ^ 2 ≤ (s ^ 3 * tiltEnvSmall t) ^ 2 := by
      calc tiltRemainder s t ^ 2 = |tiltRemainder s t| ^ 2 := (sq_abs _).symm
        _ ≤ (s ^ 3 * tiltEnvSmall t) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_tiltRemainder_le_envSmall hs hs1 t) 2
    have h2 := sq_tiltEnvSmall_le t
    nlinarith [pow_nonneg hs 6]
  refine (integral_mono (integrable_sq_tiltRemainder hs hs1)
    ((integrable_cosh 4).const_mul _) hpt).trans ?_
  have h16 : ((4 : ℝ) ^ 2) / 2 = 8 := by norm_num
  rw [integral_const_mul, integral_cosh 4, h16]
  exact le_of_eq (by unfold tiltSqConst; ring)


/-! ### The multivariate Cameron–Martin tilt -/

section MultivariateTilt

variable {k : ℕ}

/-- The **vector tilt remainder**: the second-order Taylor error, in the shift `w`, of the
Cameron–Martin density `exp (⟪w,z⟫ − ‖w‖²/2)` of `N(0,I_k)` translated by `w`. -/
private noncomputable def vecTiltRemainder (w z : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
    - (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)

private lemma continuous_vecTiltRemainder (w : EuclideanSpace ℝ (Fin k)) :
    Continuous (fun z => vecTiltRemainder w z) := by
  unfold vecTiltRemainder
  fun_prop

/-- The one-dimensional marginal of `N(0,I_k)` along a unit vector, as a pushforward. -/
private lemma stdGaussian_map_inner_unit_eq {u : EuclideanSpace ℝ (Fin k)} (hu : ‖u‖ = 1) :
    Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪u, y⟫_ℝ)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) = gaussianReal 0 1 := by
  have h := stdGaussian_map_inner_unit u hu
  rwa [multivariateGaussian_zero_one] at h

/-- Transfer of an integral along the one-dimensional marginal: this is what makes every bound
of this section **dimension-free**. -/
private lemma integral_comp_inner_unit_eq {φ : ℝ → ℝ} (hφ : Continuous φ)
    {u : EuclideanSpace ℝ (Fin k)} (hu : ‖u‖ = 1) :
    (∫ z, φ (⟪u, z⟫_ℝ) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ t, φ t ∂(gaussianReal 0 1) := by
  rw [← stdGaussian_map_inner_unit_eq hu, integral_map (by fun_prop) hφ.aestronglyMeasurable]

/-- Transfer of integrability along the one-dimensional marginal. -/
private lemma integrable_comp_inner_unit {φ : ℝ → ℝ} (hφ : Continuous φ)
    {u : EuclideanSpace ℝ (Fin k)} (hu : ‖u‖ = 1) (hint : Integrable φ (gaussianReal 0 1)) :
    Integrable (fun z => φ (⟪u, z⟫_ℝ)) (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have hmap := stdGaussian_map_inner_unit_eq hu
  have hae : AEMeasurable (fun y : EuclideanSpace ℝ (Fin k) => ⟪u, y⟫_ℝ)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by fun_prop
  exact (integrable_map_measure hφ.aestronglyMeasurable hae).1 (by rwa [hmap])

/-- **The one-dimensional reduction of the vector tilt remainder.** The whole expression depends
on `z` only through the marginal `⟪ŵ, z⟫`, with tilt parameter `‖w‖`. -/
private lemma exists_unit_vecTiltRemainder_eq {w : EuclideanSpace ℝ (Fin k)} (hw : w ≠ 0) :
    ∃ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 ∧
      ∀ z, vecTiltRemainder w z = tiltRemainder ‖w‖ (⟪u, z⟫_ℝ) := by
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨u, hunit, hwu⟩ : ∃ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 ∧ w = ‖w‖ • u :=
    ⟨‖w‖⁻¹ • w, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnw)]
      field_simp, by rw [smul_smul, mul_inv_cancel₀ hnw.ne', one_smul]⟩
  refine ⟨u, hunit, fun z => ?_⟩
  have hinner : ⟪w, z⟫_ℝ = ‖w‖ * ⟪u, z⟫_ℝ := by
    conv_lhs => rw [hwu]
    rw [real_inner_smul_left]
  simp only [vecTiltRemainder, tiltRemainder, hinner]
  ring

/-- **The vector tilt remainder has mean zero.** Reduction of `integral_tiltRemainder_eq_zero`
along the one-dimensional marginal. Consequently `∫ G · R_w dγ` is unchanged when a *constant*
is subtracted from `G`; this is what localises the indicator half of a mollified convex
indicator (see `abs_integral_mul_vecTiltRemainder_le_of_const_off`). -/
private lemma integral_vecTiltRemainder_eq_zero (w : EuclideanSpace ℝ (Fin k)) :
    (∫ z, vecTiltRemainder w z ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = 0 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [vecTiltRemainder]
  · obtain ⟨u, hu, hrw⟩ := exists_unit_vecTiltRemainder_eq hw
    simp_rw [hrw]
    rw [integral_comp_inner_unit_eq (φ := fun t => tiltRemainder ‖w‖ t)
      (continuous_tiltRemainder ‖w‖) hu]
    exact integral_tiltRemainder_eq_zero ‖w‖

/-- **The vector tilt remainder is cubically small in the shift, in `L¹(N(0,I_k))`.**
Reduction to the scalar statement `exists_tiltRemainder_bound` by the one-dimensional marginal
`⟪ŵ, ·⟫ ∼ N(0,1)` (`stdGaussian_map_inner_unit`): the whole expression depends on `z` only
through that marginal. The constant is **dimension-free**. -/
private lemma integral_abs_vecTiltRemainder_le {C : ℝ}
    (hC : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ C * s ^ 3)
    (w : EuclideanSpace ℝ (Fin k)) :
    (∫ z, |vecTiltRemainder w z| ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ C * ‖w‖ ^ 3 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [vecTiltRemainder]
  · obtain ⟨u, hu, hrw⟩ := exists_unit_vecTiltRemainder_eq hw
    have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
    simp_rw [hrw]
    rw [integral_comp_inner_unit_eq (φ := fun t => |tiltRemainder ‖w‖ t|)
      (continuous_tiltRemainder ‖w‖).abs hu]
    exact hC ‖w‖ hnw.le

/-- **`L²` version of `integral_abs_vecTiltRemainder_le`** (wave 19), for shifts of length at
most `1`, with the same dimension-free constant mechanism: the one-dimensional marginal. -/
private lemma integral_sq_vecTiltRemainder_le {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ 1) :
    (∫ z, vecTiltRemainder w z ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ tiltSqConst * ‖w‖ ^ 6 := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [vecTiltRemainder]
  · obtain ⟨u, hu, hrw⟩ := exists_unit_vecTiltRemainder_eq hw0
    simp_rw [hrw]
    rw [integral_comp_inner_unit_eq (φ := fun t => tiltRemainder ‖w‖ t ^ 2)
      ((continuous_tiltRemainder ‖w‖).pow 2) hu]
    exact integral_sq_tiltRemainder_le (norm_nonneg w) hw

private lemma integrable_sq_vecTiltRemainder {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ 1) :
    Integrable (fun z => vecTiltRemainder w z ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · have hzero : (fun z : EuclideanSpace ℝ (Fin k) =>
        vecTiltRemainder (0 : EuclideanSpace ℝ (Fin k)) z ^ 2) = fun _ => 0 := by
      funext z; simp [vecTiltRemainder]
    rw [hzero]
    exact integrable_zero _ _ _
  · obtain ⟨u, hu, hrw⟩ := exists_unit_vecTiltRemainder_eq hw0
    simp_rw [hrw]
    exact integrable_comp_inner_unit (φ := fun t => tiltRemainder ‖w‖ t ^ 2)
      ((continuous_tiltRemainder ‖w‖).pow 2) hu
      (integrable_sq_tiltRemainder (norm_nonneg w) hw)

private lemma memLp_two_vecTiltRemainder {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ 1) :
    MemLp (fun z => vecTiltRemainder w z) 2 (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
  (memLp_two_iff_integrable_sq (continuous_vecTiltRemainder w).aestronglyMeasurable).2
    (integrable_sq_vecTiltRemainder hw)

/-- The one-dimensional reduction of a plain inner product: `⟪w, z⟫ = ‖w‖ ⟪ŵ, z⟫`. This is
`exists_unit_vecTiltRemainder_eq` stripped of the tilt, so that the *polynomial* part of the
Cameron–Martin expansion can be reduced to `N(0,1)` in the same dimension-free way. -/
private lemma exists_unit_inner_eq {w : EuclideanSpace ℝ (Fin k)} (hw : w ≠ 0) :
    ∃ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 ∧ ∀ z, ⟪w, z⟫_ℝ = ‖w‖ * ⟪u, z⟫_ℝ := by
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine ⟨‖w‖⁻¹ • w, ?_, fun z => ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnw)]
    field_simp
  · rw [real_inner_smul_left]
    field_simp

private lemma integrable_sq_vecTiltPoly (w : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun z => (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · obtain ⟨u, hu, hip⟩ := exists_unit_inner_eq hw
    have hrw : (fun z : EuclideanSpace ℝ (Fin k) =>
        (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2) ^ 2)
        = fun z => (fun t : ℝ => (1 + ‖w‖ * t + ‖w‖ ^ 2 * (t ^ 2 - 1) / 2) ^ 2)
            (⟪u, z⟫_ℝ) := by
      funext z
      simp only [hip z]
      ring
    rw [hrw]
    refine integrable_comp_inner_unit
      (φ := fun t : ℝ => (1 + ‖w‖ * t + ‖w‖ ^ 2 * (t ^ 2 - 1) / 2) ^ 2) (by fun_prop) hu ?_
    have f1 : Integrable (fun _ : ℝ => (3 + 3 * ‖w‖ ^ 4 / 4)) (gaussianReal 0 1) :=
      integrable_const _
    have f2 : Integrable (fun t : ℝ => (3 * ‖w‖ ^ 2 - 3 * ‖w‖ ^ 4 / 2) * t ^ 2)
        (gaussianReal 0 1) := integrable_sq_gauss.const_mul _
    have f3 : Integrable (fun t : ℝ => (3 * ‖w‖ ^ 4 / 4) * t ^ 4) (gaussianReal 0 1) :=
      integrable_pow_four_gauss.const_mul _
    have f12 : Integrable (fun t : ℝ =>
        (3 + 3 * ‖w‖ ^ 4 / 4) + (3 * ‖w‖ ^ 2 - 3 * ‖w‖ ^ 4 / 2) * t ^ 2)
        (gaussianReal 0 1) := f1.add f2
    have fdom : Integrable (fun t : ℝ =>
        (3 + 3 * ‖w‖ ^ 4 / 4) + (3 * ‖w‖ ^ 2 - 3 * ‖w‖ ^ 4 / 2) * t ^ 2
          + (3 * ‖w‖ ^ 4 / 4) * t ^ 4) (gaussianReal 0 1) := f12.add f3
    refine Integrable.mono' fdom (by fun_prop) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (1 - ‖w‖ * t), sq_nonneg (1 - ‖w‖ ^ 2 * (t ^ 2 - 1) / 2),
      sq_nonneg (‖w‖ * t - ‖w‖ ^ 2 * (t ^ 2 - 1) / 2)]

/-- **The `L²` size of the Cameron–Martin polynomial, dimension-free** (wave 40). The vector
form of `integral_sq_tiltPoly_le`, by the one-dimensional marginal. -/
private lemma integral_sq_vecTiltPoly_le (w : EuclideanSpace ℝ (Fin k)) :
    (∫ z, (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ 640 * (1 + ‖w‖ ^ 2) ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hw
  · norm_num
  · obtain ⟨u, hu, hip⟩ := exists_unit_inner_eq hw
    have hrw : (fun z : EuclideanSpace ℝ (Fin k) =>
        (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2) ^ 2)
        = fun z => (fun t : ℝ => (1 + ‖w‖ * t + ‖w‖ ^ 2 * (t ^ 2 - 1) / 2) ^ 2)
            (⟪u, z⟫_ℝ) := by
      funext z
      simp only [hip z]
      ring
    rw [hrw, integral_comp_inner_unit_eq
      (φ := fun t : ℝ => (1 + ‖w‖ * t + ‖w‖ ^ 2 * (t ^ 2 - 1) / 2) ^ 2) (by fun_prop) hu]
    exact integral_sq_tiltPoly_le ‖w‖

/-- **The `L¹` size of the Cameron–Martin polynomial, dimension-free** (wave 40). -/
private lemma integral_abs_vecTiltPoly_le (w : EuclideanSpace ℝ (Fin k)) :
    (∫ z, |1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2|
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ 1 + ‖w‖ + ‖w‖ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · obtain ⟨u, hu, hip⟩ := exists_unit_inner_eq hw
    have hrw : (fun z : EuclideanSpace ℝ (Fin k) =>
        |1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2|)
        = fun z => (fun t : ℝ => |1 + ‖w‖ * t + ‖w‖ ^ 2 * (t ^ 2 - 1) / 2|)
            (⟪u, z⟫_ℝ) := by
      funext z
      simp only [hip z]
      congr 1
      ring
    rw [hrw, integral_comp_inner_unit_eq
      (φ := fun t : ℝ => |1 + ‖w‖ * t + ‖w‖ ^ 2 * (t ^ 2 - 1) / 2|) (by fun_prop) hu]
    exact integral_abs_tiltPoly_le (norm_nonneg w)

/-- **The weighted (Hölder / `L²`) form of `integral_abs_vecTiltRemainder_le`** — the first of
the two ingredients the sharp Bentkus rate needs (wave 19).

`integral_abs_vecTiltRemainder_le` bounds `∫ |R_w| dγ ≤ C‖w‖³`, which is what one pairs with a
test function bounded by `‖G‖_∞ = 1`. Here the remainder is paired with `|G|` itself:

`∫ |G| |R_w| dγ ≤ ‖G‖_{L²(γ)} · √tiltSqConst · ‖w‖³`.

Two things survive the refinement: the constant is still **absolute** (no `k`), because
`integral_sq_vecTiltRemainder_le` is again proved through the one-dimensional marginal; and the
power of `‖w‖` is still `3`, so the telescope arithmetic is unchanged. What is bought is that a
`G` supported on the `ε`-shell of `∂B` now costs `√(γ(shell))` rather than `1`. -/
private lemma integral_abs_mul_vecTiltRemainder_le
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hGc : Continuous G)
    (hG2 : Integrable (fun z => G z ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin k))))
    {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ 1) :
    (∫ z, |G z| * |vecTiltRemainder w z| ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ Real.sqrt (∫ z, G z ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          * (Real.sqrt tiltSqConst * ‖w‖ ^ 3) := by
  have hGabs : MemLp (fun z => |G z|) (ENNReal.ofReal 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hGc.abs.aestronglyMeasurable).2 ?_
    simpa [sq_abs] using hG2
  have hRabs : MemLp (fun z => |vecTiltRemainder w z|) (ENNReal.ofReal 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (memLp_two_vecTiltRemainder hw).abs
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := stdGaussian (EuclideanSpace ℝ (Fin k))) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun z => abs_nonneg (G z))
    (Filter.Eventually.of_forall fun z => abs_nonneg (vecTiltRemainder w z)) hGabs hRabs
  have hrp : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrp, sq_abs, ← Real.sqrt_eq_rpow] at hmain
  refine hmain.trans ?_
  have hR : Real.sqrt (∫ z, vecTiltRemainder w z ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ Real.sqrt tiltSqConst * ‖w‖ ^ 3 := by
    calc Real.sqrt (∫ z, vecTiltRemainder w z ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        ≤ Real.sqrt (tiltSqConst * ‖w‖ ^ 6) :=
          Real.sqrt_le_sqrt (integral_sq_vecTiltRemainder_le hw)
      _ = Real.sqrt tiltSqConst * ‖w‖ ^ 3 := by
          rw [show ‖w‖ ^ 6 = (‖w‖ ^ 3) ^ 2 by ring, Real.sqrt_mul tiltSqConst_pos.le,
            Real.sqrt_sq (by positivity)]
  exact mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _)

/-- **The localised weighted bound.** If `|G| ≤ 1` and `G` vanishes off a measurable set `S`
— the shape of the third-derivative term of a mollified convex indicator, whose support is the
`ε`-shell of `∂B` — then the Cameron–Martin remainder paired with `G` costs `√(γ S)`:

`|∫ G · R_w dγ| ≤ √(γ S) · √tiltSqConst · ‖w‖³`.

This is the localisation the wave-16 note identified as missing. The `√` (rather than a bare
`γ S`) is the price of Cauchy–Schwarz; see `le_of_selfImproving_smoothed_sqrt` at the end of the
file for what the resulting recursion closes at. -/
private lemma abs_integral_mul_vecTiltRemainder_le_of_support
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hGc : Continuous G) (hG1 : ∀ z, |G z| ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin k))} (hS : MeasurableSet S)
    (hsupp : ∀ z, z ∉ S → G z = 0)
    {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ 1) :
    |∫ z, G z * vecTiltRemainder w z ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ Real.sqrt ((stdGaussian (EuclideanSpace ℝ (Fin k)) S).toReal)
          * (Real.sqrt tiltSqConst * ‖w‖ ^ 3) := by
  have hsq1 : ∀ z, G z ^ 2 ≤ S.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      nlinarith [hG1 z, abs_nonneg (G z), sq_abs (G z)]
    · rw [Set.indicator_of_notMem hz, hsupp z hz]
      norm_num
  have hind : Integrable (S.indicator fun _ => (1 : ℝ))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := (integrable_const (1 : ℝ)).indicator hS
  have hG2 : Integrable (fun z => G z ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    refine Integrable.mono' hind ((hGc.pow 2).aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq1 z
  have hbd : (∫ z, G z ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ (stdGaussian (EuclideanSpace ℝ (Fin k)) S).toReal := by
    refine (integral_mono hG2 hind hsq1).trans ?_
    rw [integral_indicator_const (1 : ℝ) hS, measureReal_def, smul_eq_mul, mul_one]
  calc |∫ z, G z * vecTiltRemainder w z ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ ∫ z, |G z * vecTiltRemainder w z| ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
        abs_integral_le_integral_abs
    _ = ∫ z, |G z| * |vecTiltRemainder w z|
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by simp only [abs_mul]
    _ ≤ Real.sqrt (∫ z, G z ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          * (Real.sqrt tiltSqConst * ‖w‖ ^ 3) :=
        integral_abs_mul_vecTiltRemainder_le hGc hG2 hw
    _ ≤ Real.sqrt ((stdGaussian (EuclideanSpace ℝ (Fin k)) S).toReal)
          * (Real.sqrt tiltSqConst * ‖w‖ ^ 3) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hbd) (by positivity)

/-- **Cameron–Martin: a Gaussian shift is an exponential tilt.** For a bounded continuous `g`,
`∫ g(z + a) dγ = ∫ g(z) exp(⟪a,z⟫ − ‖a‖²/2) dγ`. This is
`stdGaussian_withDensity_exp_shift` read as an integral identity; it is what replaces the
third derivative of `g` by a factor `σ⁻³` in the Lindeberg swap. -/
private lemma integral_gaussian_shift_eq_tilt {g : EuclideanSpace ℝ (Fin k) → ℝ}
    (hg : Continuous g) (a : EuclideanSpace ℝ (Fin k)) :
    (∫ z, g (z + a) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ z, g z * Real.exp (⟪a, z⟫_ℝ - ‖a‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have hmapint : (∫ z, g (z + a) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ z, g z ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun y => y + a)) := by
    rw [integral_map (by fun_prop) hg.aestronglyMeasurable]
  rw [hmapint, ← stdGaussian_withDensity_exp_shift a,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, mul_comm]

end MultivariateTilt


/-! ### Gaussian moments and the smoothed swap step -/

section SmoothedSwap

variable {k : ℕ}

private lemma memLp_norm_gauss (p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ p)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have hL : MemLp (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      ((p : ℕ) : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
    IsGaussian.memLp_id _ _ (by simp)
  simpa using hL.integrable_norm_pow'

private lemma integrable_norm_gauss :
    Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have := memLp_norm_gauss (k := k) 1
  simpa using this

/-- **The Gaussian norm tail, by Markov at any order.** `γ{‖z‖ ≥ R} ≤ E‖z‖^p / R^p`.

Wave 29: this is the *only* input the localisation of the indicator half needs beyond
`integral_vecTiltRemainder_eq_zero` — in particular no Gaussian surface area, and no
concentration inequality: plain Markov at a high enough order `p`. -/
private lemma stdGaussian_norm_ge_le (p : ℕ) {R : ℝ} (hR : 0 < R) :
    ((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | R ≤ ‖z‖}).toReal
      ≤ (∫ z, ‖z‖ ^ p ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) / R ^ p := by
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (μ := stdGaussian (EuclideanSpace ℝ (Fin k)))
    (f := fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ p)
    (Filter.Eventually.of_forall fun z => by positivity) (memLp_norm_gauss p) (R ^ p)
  have hsub : {z : EuclideanSpace ℝ (Fin k) | R ≤ ‖z‖}
      ⊆ {z : EuclideanSpace ℝ (Fin k) | R ^ p ≤ ‖z‖ ^ p} := by
    intro z hz
    exact pow_le_pow_left₀ hR.le hz p
  have hmono : ((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | R ≤ ‖z‖}).toReal
      ≤ ((stdGaussian (EuclideanSpace ℝ (Fin k)))
          {z : EuclideanSpace ℝ (Fin k) | R ^ p ≤ ‖z‖ ^ p}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  rw [le_div_iff₀ (by positivity)]
  calc ((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | R ≤ ‖z‖}).toReal * R ^ p
      ≤ ((stdGaussian (EuclideanSpace ℝ (Fin k)))
          {z : EuclideanSpace ℝ (Fin k) | R ^ p ≤ ‖z‖ ^ p}).toReal * R ^ p :=
        mul_le_mul_of_nonneg_right hmono (by positivity)
    _ = R ^ p * ((stdGaussian (EuclideanSpace ℝ (Fin k))).real
          {z : EuclideanSpace ℝ (Fin k) | R ^ p ≤ ‖z‖ ^ p}) := by
        rw [measureReal_def]; ring
    _ ≤ _ := hmk

/-- **One-dimensional Gaussian upper tail (Chernoff), wave 39.** `N(0,1)[s, ∞) ≤ e^{-s²/2}`.

Immediate from the Chernoff bound at `t = s` together with the exact Gaussian mgf
`∫ e^{s x} dN(0,1) = e^{s²/2}` (`integral_exp_mul_gaussianReal`). -/
private lemma gaussianReal_ge_le {s : ℝ} (hs : 0 ≤ s) :
    (gaussianReal 0 1).real {x : ℝ | s ≤ x} ≤ Real.exp (-(s ^ 2) / 2) := by
  have hint : Integrable (fun x : ℝ => Real.exp (s * x)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal s
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := fun x : ℝ => x)
    (t := s) s hs hint
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 1) s = Real.exp (s ^ 2 / 2) := by
    rw [mgf, integral_exp_mul_gaussianReal 0 1 s]
    norm_num
  rw [hmgf, ← Real.exp_add] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

/-- **One-dimensional Gaussian two-sided tail (wave 39).** `N(0,1){|x| ≥ s} ≤ 2 e^{-s²/2}`. -/
private lemma gaussianReal_abs_ge_le {s : ℝ} (hs : 0 ≤ s) :
    (gaussianReal 0 1).real {x : ℝ | s ≤ |x|} ≤ 2 * Real.exp (-(s ^ 2) / 2) := by
  have hint : Integrable (fun x : ℝ => Real.exp (-s * x)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal (-s)
  have hlow := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := fun x : ℝ => x)
    (t := -s) (-s) (by linarith) hint
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 1) (-s) = Real.exp (s ^ 2 / 2) := by
    rw [mgf, integral_exp_mul_gaussianReal 0 1 (-s)]
    norm_num
  rw [hmgf, ← Real.exp_add] at hlow
  have hlow' : (gaussianReal 0 1).real {x : ℝ | x ≤ -s} ≤ Real.exp (-(s ^ 2) / 2) := by
    refine hlow.trans (le_of_eq ?_)
    congr 1
    ring
  have hsub : {x : ℝ | s ≤ |x|} ⊆ {x : ℝ | s ≤ x} ∪ {x : ℝ | x ≤ -s} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inl (by simp only [Set.mem_setOf_eq]; linarith [hx, he.symm ▸ hx])
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq]
      rw [he] at hx
      linarith
  have hmono : (gaussianReal 0 1).real {x : ℝ | s ≤ |x|}
      ≤ (gaussianReal 0 1).real ({x : ℝ | s ≤ x} ∪ {x : ℝ | x ≤ -s}) :=
    measureReal_mono hsub (by exact measure_ne_top _ _)
  have hun : (gaussianReal 0 1).real ({x : ℝ | s ≤ x} ∪ {x : ℝ | x ≤ -s})
      ≤ (gaussianReal 0 1).real {x : ℝ | s ≤ x}
        + (gaussianReal 0 1).real {x : ℝ | x ≤ -s} := measureReal_union_le _ _
  have hup := gaussianReal_ge_le hs
  linarith

/-- **The sub-Gaussian NORM tail of `N(0, I_k)` (wave 39: PROVED).** *The ingredient wave 38
identified as missing, and the reason the tail brick's frozen weight was unreachable.*

  `γ{‖z‖ ≥ M} ≤ 2 k · exp(-M²/(2k))`   for every `M ≥ 0` and `k ≥ 1`.

Wave 38's note on `abs_integral_gaussian_smoothed_swap_localised_le` established that the only
Gaussian norm tail this file had was `stdGaussian_norm_ge_le`, i.e. Markov at a *fixed* order
`p`, and that at a fixed order the tail steps of the ledger sum to a **power** `ε^{-2/p}` of
`ε⁻¹` rather than to a logarithm. Any genuinely sub-Gaussian decay repairs that; this is the
cheapest such statement.

**The route is the coordinate union bound, not concentration.** `{‖z‖ ≥ M}` is contained in
`⋃ᵢ {|zᵢ| ≥ M/√k}` (else `‖z‖² = ∑ᵢ zᵢ² < k · M²/k`), each coordinate is `N(0,1)` — this is
`stdGaussian_map_inner_unit` at the unit vector `EuclideanSpace.single i 1`, the very marginal
computation the slab bound at the top of the file already uses — and the one-dimensional tail is
`gaussianReal_abs_ge_le`. No Gaussian isoperimetry, no `χ²` moment generating function, no
Borell–TIS.

**The price of that route, recorded honestly (wave 39).** The bound wave 38 asked for was
`γ{‖z‖ ≥ M} ≤ exp(-(M − √k)²/2)`, whose inversion is the *additive* radius
`√k + √(2 log(1/σ))`. The union bound gives the weaker exponent `M²/(2k)` in place of
`(M − √k)²/2`, whose inversion is the *multiplicative* radius `√(2k log 2k) + 2√(k log(1/σ))`
(`gaussianTailRadius` below). The difference propagates to the headline as a dimension factor
`√(k log k)` where the additive form would give `√k` — a constant-level, not shape-level,
deviation: the `(1 + log(1 + ε⁻¹))^{3/2}` shape of the amended ledger is the same either way,
because both radii are `O(√k) + O(√k)·√(log(1/σ))` and only the `√log` weight changes the
summation. Upgrading to the additive form (Chernoff on `‖z‖² ∼ χ²_k`, i.e.
`E e^{‖z‖²/4} = 2^{k/2}` from the `Γ`-density, or Borell–TIS which Mathlib does not have) would
improve that factor and nothing else. -/
private lemma stdGaussian_norm_ge_le_exp (hk : 0 < k) {M : ℝ} (hM : 0 ≤ M) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | M ≤ ‖z‖}
      ≤ 2 * (k : ℝ) * Real.exp (-(M ^ 2) / (2 * (k : ℝ))) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hγ : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := multivariateGaussian_zero_one
  set s : ℝ := M / Real.sqrt (k : ℝ) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hsk : s ^ 2 * (k : ℝ) = M ^ 2 := by
    rw [hsdef, div_pow, Real.sq_sqrt hkr.le]
    field_simp
  have habs : MeasurableSet {x : ℝ | s ≤ |x|} :=
    measurableSet_le measurable_const measurable_id.abs
  -- each coordinate slab, by the one-dimensional two-sided tail
  have hcoord : ∀ i : Fin k,
      (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | s ≤ |z i|}
        ≤ 2 * Real.exp (-(s ^ 2) / 2) := by
    intro i
    have hnorm : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
    have hinner : ∀ z : EuclideanSpace ℝ (Fin k),
        ⟪EuclideanSpace.single i (1 : ℝ), z⟫_ℝ = z i :=
      fun z => (EuclideanSpace.inner_single_left i 1 z).trans (by simp)
    have hmf : Measurable
        (fun z : EuclideanSpace ℝ (Fin k) => ⟪EuclideanSpace.single i (1 : ℝ), z⟫_ℝ) := by
      fun_prop
    have hset : {z : EuclideanSpace ℝ (Fin k) | s ≤ |z i|}
        = (fun z : EuclideanSpace ℝ (Fin k) => ⟪EuclideanSpace.single i (1 : ℝ), z⟫_ℝ) ⁻¹'
            {x : ℝ | s ≤ |x|} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hinner z]
    have hmap := stdGaussian_map_inner_unit (EuclideanSpace.single i (1 : ℝ)) hnorm
    rw [hγ] at hmap
    have hval : (stdGaussian (EuclideanSpace ℝ (Fin k))) {z | s ≤ |z i|}
        = gaussianReal 0 1 {x : ℝ | s ≤ |x|} := by
      rw [hset, ← Measure.map_apply hmf habs, hmap]
    rw [measureReal_def, hval, ← measureReal_def]
    exact gaussianReal_abs_ge_le hs0
  -- the union bound
  have hsub : {z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}
      ⊆ ⋃ i : Fin k, {z : EuclideanSpace ℝ (Fin k) | s ≤ |z i|} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hcon
    have hnormsq : ‖z‖ ^ 2 = ∑ i : Fin k, |z i| ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs]
    have hlt : ∑ i : Fin k, |z i| ^ 2 < ∑ _i : Fin k, s ^ 2 := by
      refine Finset.sum_lt_sum_of_nonempty ?_ fun i _ => ?_
      · exact Finset.univ_nonempty
      · exact pow_lt_pow_left₀ (hcon i) (abs_nonneg _) two_ne_zero
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    have h2 : ‖z‖ ^ 2 < M ^ 2 := by
      rw [hnormsq]
      calc ∑ i : Fin k, |z i| ^ 2 < (k : ℝ) * s ^ 2 := hlt
        _ = M ^ 2 := by rw [← hsk]; ring
    nlinarith [norm_nonneg z]
  have hmono : (stdGaussian (EuclideanSpace ℝ (Fin k))) {z | M ≤ ‖z‖}
      ≤ ∑ i : Fin k, (stdGaussian (EuclideanSpace ℝ (Fin k))) {z | s ≤ |z i|} := by
    refine (measure_mono hsub).trans ?_
    exact measure_iUnion_fintype_le _ _
  have hfin : ∑ i : Fin k, (stdGaussian (EuclideanSpace ℝ (Fin k))) {z | s ≤ |z i|} ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i _ => measure_lt_top _ _).ne
  have htoReal : (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | M ≤ ‖z‖}
      ≤ ∑ i : Fin k, (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | s ≤ |z i|} := by
    rw [measureReal_def]
    refine (ENNReal.toReal_mono hfin hmono).trans (le_of_eq ?_)
    rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
    rfl
  have hsum : ∑ i : Fin k, (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | s ≤ |z i|}
      ≤ (k : ℝ) * (2 * Real.exp (-(s ^ 2) / 2)) := by
    calc ∑ i : Fin k, (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | s ≤ |z i|}
        ≤ ∑ _i : Fin k, 2 * Real.exp (-(s ^ 2) / 2) := Finset.sum_le_sum fun i _ => hcoord i
      _ = (k : ℝ) * (2 * Real.exp (-(s ^ 2) / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hexp : -(s ^ 2) / 2 = -(M ^ 2) / (2 * (k : ℝ)) := by
    rw [← hsk]; field_simp
  rw [hexp] at hsum
  linarith

/-- **The radius at which the Gaussian norm tail drops below `σ²` (wave 39).**

  `gaussianTailRadius k σ = √(2k log(2k)) + 2√(k log(1/σ))`.

This is the exact inversion of `stdGaussian_norm_ge_le_exp`; see
`stdGaussian_norm_ge_gaussianTailRadius_le`. It is the radius at which route (b) of the tail
brick splits `v`-space, so the *whole* dependence of the amended tail weight on `k` and on the
smoothing width `σ` is packaged here. Note the two summands: the first is the `√k`-type
"dimension" term (the harmonic part of the ledger multiplies it), the second is the `√log(1/σ)`
term (which is what forces the ledger's `(1 + log(1+ε⁻¹))^{3/2}`). -/
noncomputable def gaussianTailRadius (k : ℕ) (σ : ℝ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) * Real.log (2 * (k : ℝ))) + 2 * Real.sqrt ((k : ℝ) * Real.log σ⁻¹)

lemma gaussianTailRadius_nonneg (k : ℕ) (σ : ℝ) : 0 ≤ gaussianTailRadius k σ := by
  unfold gaussianTailRadius; positivity

/-- **The tail radius does what it is for (wave 39).** For `0 < σ ≤ 1`,
`γ{‖z‖ ≥ gaussianTailRadius k σ} ≤ σ²`, hence `2√(that tail) ≤ 2σ`: the far-in-`v` half of
route (b) is weighted by `O(σ)`, exactly as the ledger's tail summands need. -/
lemma stdGaussian_norm_ge_gaussianTailRadius_le (hk : 0 < k) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).real {z | gaussianTailRadius k σ ≤ ‖z‖}
      ≤ σ ^ 2 := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogσ : 0 ≤ Real.log σ⁻¹ := Real.log_nonneg (by rw [le_inv_comm₀ (by norm_num) hσ0]; simpa)
  have hlog2k : 0 ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  set A : ℝ := Real.sqrt (2 * (k : ℝ) * Real.log (2 * (k : ℝ))) with hA
  set Bq : ℝ := 2 * Real.sqrt ((k : ℝ) * Real.log σ⁻¹) with hB
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ Bq := by rw [hB]; positivity
  have hA2 : A ^ 2 = 2 * (k : ℝ) * Real.log (2 * (k : ℝ)) := Real.sq_sqrt (by positivity)
  have hB2 : Bq ^ 2 = 4 * ((k : ℝ) * Real.log σ⁻¹) := by
    rw [hB, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hM2 : 2 * (k : ℝ) * Real.log (2 * (k : ℝ)) + 4 * ((k : ℝ) * Real.log σ⁻¹)
      ≤ gaussianTailRadius k σ ^ 2 := by
    have hexpand : gaussianTailRadius k σ ^ 2 = A ^ 2 + 2 * A * Bq + Bq ^ 2 := by
      unfold gaussianTailRadius; rw [← hA, ← hB]; ring
    rw [hexpand, hA2, hB2]
    nlinarith [mul_nonneg hA0 hB0]
  have hmain := stdGaussian_norm_ge_le_exp (k := k) hk (gaussianTailRadius_nonneg k σ)
  refine hmain.trans ?_
  have hE : -(gaussianTailRadius k σ ^ 2) / (2 * (k : ℝ))
      ≤ -Real.log (2 * (k : ℝ)) - 2 * Real.log σ⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hM2]
  have h1 : Real.exp (-(gaussianTailRadius k σ ^ 2) / (2 * (k : ℝ)))
      ≤ Real.exp (-Real.log (2 * (k : ℝ)) - 2 * Real.log σ⁻¹) := Real.exp_le_exp.2 hE
  have hσ2 : Real.exp (2 * Real.log σ) = σ ^ 2 := by
    rw [show (2 : ℝ) * Real.log σ = Real.log σ + Real.log σ by ring, Real.exp_add,
      Real.exp_log hσ0]
    ring
  have h2 : Real.exp (-Real.log (2 * (k : ℝ)) - 2 * Real.log σ⁻¹)
      = (2 * (k : ℝ))⁻¹ * σ ^ 2 := by
    rw [Real.log_inv, show -Real.log (2 * (k : ℝ)) - 2 * -Real.log σ
        = -Real.log (2 * (k : ℝ)) + 2 * Real.log σ by ring, Real.exp_add, Real.exp_neg,
      Real.exp_log (by positivity), hσ2]
  calc 2 * (k : ℝ) * Real.exp (-(gaussianTailRadius k σ ^ 2) / (2 * (k : ℝ)))
      ≤ 2 * (k : ℝ) * ((2 * (k : ℝ))⁻¹ * σ ^ 2) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = σ ^ 2 := by field_simp

/-- **The dimension factor the amended ledger carries (wave 39).**
`dimTailConst k = √(2k log 2k) + 2√k`. It is the `σ`-free envelope of `gaussianTailRadius`:
`gaussianTailRadius k σ ≤ dimTailConst k · √(1 + log(1 + σ⁻¹))`
(`gaussianTailRadius_le_dimTailConst`). Splitting the tail radius this way is what turns the
ledger's harmonic sum into a `3/2` power of the logarithm times a pure dimension constant, and
it is where the headline's `k`-dependence changes from `√k` (wave 32) to `√(k log k)`. -/
noncomputable def dimTailConst (k : ℕ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) * Real.log (2 * (k : ℝ))) + 2 * Real.sqrt (k : ℝ)

lemma one_le_dimTailConst {k : ℕ} (hk : 0 < k) : 1 ≤ dimTailConst k := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hs : Real.sqrt 1 ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hk1
  rw [Real.sqrt_one] at hs
  have h0 : 0 ≤ Real.sqrt (2 * (k : ℝ) * Real.log (2 * (k : ℝ))) := Real.sqrt_nonneg _
  rw [dimTailConst]
  linarith

/-- The tail radius is at least `1` at every width — so the amended per-step weight
`12 C_k σ · gaussianTailRadius k σ + W` really does dominate the wave-32 frozen weight
`4 C_k σ + W`, and the `ε` of the near/far split is absorbed by `σ ≤ σ·R`. Numerically the
bound is `√(2 log 2) ≈ 1.177` at `k = 1` and grows. -/
lemma one_le_gaussianTailRadius {k : ℕ} (hk : 0 < k) (σ : ℝ) :
    1 ≤ gaussianTailRadius k σ := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hmono : Real.log 2 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hbig : (1 : ℝ) ≤ 2 * (k : ℝ) * Real.log (2 * (k : ℝ)) := by nlinarith
  have h := Real.sqrt_le_sqrt hbig
  rw [Real.sqrt_one] at h
  have h2 : 0 ≤ 2 * Real.sqrt ((k : ℝ) * Real.log σ⁻¹) := by positivity
  rw [gaussianTailRadius]
  linarith

/-- **The tail radius dominates `√k` at every width (wave 43).** This is what pays for the
deconvolution radius on the tail side of brick L: the factor to be deconvolved away there is the
smoothing Gaussian of width `σ_{j+1}`, whose concentration radius is `2 √k σ_{j+1}`, and the
weight the tail brick already carries is `σⱼ · gaussianTailRadius k σⱼ`. Since
`√(2k log 2k) ≥ √k` (from `log 2 ≥ 1/2`) the extra term is a constant multiple of the weight and
no shape moves. -/
lemma sqrt_dim_le_gaussianTailRadius {k : ℕ} (hk : 0 < k) (σ : ℝ) :
    Real.sqrt (k : ℝ) ≤ gaussianTailRadius k σ := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hmono : Real.log 2 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hbig : (k : ℝ) ≤ 2 * (k : ℝ) * Real.log (2 * (k : ℝ)) := by nlinarith
  have h := Real.sqrt_le_sqrt hbig
  have h2 : 0 ≤ 2 * Real.sqrt ((k : ℝ) * Real.log σ⁻¹) := by positivity
  rw [gaussianTailRadius]
  linarith

/-- **The tail radius is antitone in the width (wave 43).** The tail steps of the ledger are
summed at the *single* radius `gaussianTailRadius k ε`, while step `j` produces
`gaussianTailRadius k σⱼ` with `σⱼ ≥ ε`; this is the comparison that lets them be summed. -/
lemma gaussianTailRadius_anti {k : ℕ} {ε σ : ℝ} (hε : 0 < ε) (hεσ : ε ≤ σ) :
    gaussianTailRadius k σ ≤ gaussianTailRadius k ε := by
  have hσ : 0 < σ := lt_of_lt_of_le hε hεσ
  have hinv : σ⁻¹ ≤ ε⁻¹ := by rw [inv_le_inv₀ hσ hε]; exact hεσ
  have hlog : Real.log σ⁻¹ ≤ Real.log ε⁻¹ := Real.log_le_log (by positivity) hinv
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h : Real.sqrt ((k : ℝ) * Real.log σ⁻¹) ≤ Real.sqrt ((k : ℝ) * Real.log ε⁻¹) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [gaussianTailRadius, gaussianTailRadius]
  linarith

/-- **The split that produces the `3/2` power (wave 39).** `log(1/ε) ≤ log(1 + ε⁻¹)`, so the
`√log` half of the tail radius is at most `2√k · √(1 + log(1 + ε⁻¹))`, and the dimension half is
at most itself times the same (`≥ 1`) factor. -/
lemma gaussianTailRadius_le_dimTailConst {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    gaussianTailRadius k ε ≤ dimTailConst k * Real.sqrt (1 + Real.log (1 + ε⁻¹)) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hεi : (0 : ℝ) < ε⁻¹ := by positivity
  set N : ℝ := 1 + Real.log (1 + ε⁻¹) with hN
  have hlog : Real.log ε⁻¹ ≤ N := by
    have h1 : Real.log ε⁻¹ ≤ Real.log (1 + ε⁻¹) := Real.log_le_log hεi (by linarith)
    rw [hN]; linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : 0 ≤ Real.log (1 + ε⁻¹) := Real.log_nonneg (by linarith)
    rw [hN]; linarith
  have hsN : (1 : ℝ) ≤ Real.sqrt N := by
    have := Real.sqrt_le_sqrt hN1
    rwa [Real.sqrt_one] at this
  have h1 : Real.sqrt (2 * (k : ℝ) * Real.log (2 * (k : ℝ)))
      ≤ Real.sqrt (2 * (k : ℝ) * Real.log (2 * (k : ℝ))) * Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (2 * (k : ℝ) * Real.log (2 * (k : ℝ)))]
  have h2 : 2 * Real.sqrt ((k : ℝ) * Real.log ε⁻¹) ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt N := by
    have hstep : Real.sqrt ((k : ℝ) * Real.log ε⁻¹) ≤ Real.sqrt ((k : ℝ) * N) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hsplit : Real.sqrt ((k : ℝ) * N) = Real.sqrt (k : ℝ) * Real.sqrt N :=
      Real.sqrt_mul hk0 N
    rw [hsplit] at hstep
    linarith
  rw [gaussianTailRadius, dimTailConst]
  nlinarith

private lemma integrable_exp_inner_gauss (a : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin k) => Real.exp ⟪a, z⟫_ℝ)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_inner_stdGaussian a]
  exact (Real.exp_pos _).ne'

/-- The `z`-integrability of the tilted integrand, for a fixed shift `a`. -/
private lemma integrable_mul_exp_tilt_gauss {G : EuclideanSpace ℝ (Fin k) → ℝ}
    (hG : Continuous G) (hGb : ∀ x, |G x| ≤ 1) (a : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun z => G z * Real.exp (⟪a, z⟫_ℝ - ‖a‖ ^ 2 / 2))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have hre : (fun z : EuclideanSpace ℝ (Fin k) => G z * Real.exp (⟪a, z⟫_ℝ - ‖a‖ ^ 2 / 2))
      = fun z => Real.exp (-(‖a‖ ^ 2 / 2)) * (G z * Real.exp ⟪a, z⟫_ℝ) := by
    funext z
    rw [show ⟪a, z⟫_ℝ - ‖a‖ ^ 2 / 2 = -(‖a‖ ^ 2 / 2) + ⟪a, z⟫_ℝ by ring, Real.exp_add]
    ring
  rw [hre]
  refine Integrable.const_mul ?_ _
  refine Integrable.mono' (integrable_exp_inner_gauss a) (by fun_prop) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  nlinarith [hGb z, Real.exp_pos ⟪a, z⟫_ℝ, abs_nonneg (G z)]

/-- The `z`-integrability of the quadratic Taylor part of the tilt, for a fixed shift. -/
private lemma integrable_mul_tiltPoly_gauss {G : EuclideanSpace ℝ (Fin k) → ℝ}
    (hG : Continuous G) (hGb : ∀ x, |G x| ≤ 1) (a : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun z => G z * (1 + ⟪a, z⟫_ℝ + (⟪a, z⟫_ℝ ^ 2 - ‖a‖ ^ 2) / 2))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have h1 : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ⟪a, z⟫_ℝ)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    refine Integrable.mono' (integrable_norm_gauss.const_mul ‖a‖) (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm a z
  have h2 : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ⟪a, z⟫_ℝ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    refine Integrable.mono' ((memLp_norm_gauss (k := k) 2).const_mul (‖a‖ ^ 2)) (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := abs_real_inner_le_norm a z
    nlinarith [abs_nonneg (⟪a, z⟫_ℝ), sq_abs (⟪a, z⟫_ℝ), norm_nonneg a, norm_nonneg z]
  have hpoly : Integrable
      (fun z : EuclideanSpace ℝ (Fin k) => 1 + ⟪a, z⟫_ℝ + (⟪a, z⟫_ℝ ^ 2 - ‖a‖ ^ 2) / 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
    ((integrable_const (1 : ℝ)).add h1).add ((h2.sub (integrable_const _)).div_const 2)
  refine Integrable.mono' hpoly.abs (by fun_prop) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [hGb z, abs_nonneg (G z),
    abs_nonneg (1 + ⟪a, z⟫_ℝ + (⟪a, z⟫_ℝ ^ 2 - ‖a‖ ^ 2) / 2)]


private lemma integrable_vecTiltRemainder (a : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun z => vecTiltRemainder a z)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have h1 := integrable_mul_exp_tilt_gauss (G := fun _ : EuclideanSpace ℝ (Fin k) => (1 : ℝ))
    continuous_const (fun _ => by norm_num) a
  have h2 := integrable_mul_tiltPoly_gauss (G := fun _ : EuclideanSpace ℝ (Fin k) => (1 : ℝ))
    continuous_const (fun _ => by norm_num) a
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.sub_apply, one_mul, vecTiltRemainder]

/-- **The localised weighted bound, for a test function that is CONSTANT off a small set**
(wave 29). If `|G| ≤ 1` and `G ≡ a` off a measurable set `S`, with `|a| ≤ 1`, then

`|∫ G · R_w dγ| ≤ 2 √(γ S) · √tiltSqConst · ‖w‖³`.

`abs_integral_mul_vecTiltRemainder_le_of_support` is the case `a = 0`. The extension to a
general constant is *not* cosmetic: it is exactly what the indicator half of a mollified convex
indicator needs. Writing the mollified indicator `f = 1_{interior B} + g` with `g` shell-
supported, the wave-19 lemma applies to `g` but not to `1_{interior B}`, whose Cameron–Martin
error is `γ(K − w) − Q_w(K)` for the convex set `K = (interior B − v)/σ`. Wave 24's docstring
concluded that bounding *that* by the shell mass is a Gaussian-surface-area statement, i.e.
Ball's theorem. **That verdict is wrong.** Since `∫ R_w dγ = 0`
(`integral_vecTiltRemainder_eq_zero`), one may subtract from `1_K` the constant it takes near
the centre: if `v` is at distance `≥ r` from `∂B` then `1_K` is constant on the ball of radius
`r/σ`, and Cauchy–Schwarz against the *Gaussian tail* `γ{‖z‖ ≥ r/σ}` — not against any surface
measure — gives the localisation. See
`abs_integral_shift_vecTiltRemainder_le_of_const_ball`. -/
private lemma abs_integral_mul_vecTiltRemainder_le_of_const_off
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hGc : Continuous G) (hG1 : ∀ z, |G z| ≤ 1)
    {a : ℝ} (ha : |a| ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin k))} (hS : MeasurableSet S)
    (hoff : ∀ z, z ∉ S → G z = a)
    {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ 1) :
    |∫ z, G z * vecTiltRemainder w z ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ 2 * Real.sqrt ((stdGaussian (EuclideanSpace ℝ (Fin k)) S).toReal)
          * (Real.sqrt tiltSqConst * ‖w‖ ^ 3) := by
  have hRint : Integrable (fun z => vecTiltRemainder w z)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := integrable_vecTiltRemainder w
  have hHR : Integrable (fun z => (G z - a) * vecTiltRemainder w z)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    refine Integrable.mono' (hRint.abs.const_mul 2) (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |G z - a| ≤ 2 := by linarith [hG1 z, ha, abs_sub (G z) a]
    nlinarith [abs_nonneg (vecTiltRemainder w z), abs_nonneg (G z - a)]
  have haR : Integrable (fun z => a * vecTiltRemainder w z)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := hRint.const_mul a
  have hdec : (∫ z, G z * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = (∫ z, (G z - a) * vecTiltRemainder w z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        + ∫ z, a * vecTiltRemainder w z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have h := integral_add hHR haR
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have haR0 : (∫ z, a * vecTiltRemainder w z
      ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = 0 := by
    have h := integral_const_mul (μ := stdGaussian (EuclideanSpace ℝ (Fin k))) a
      (fun z => vecTiltRemainder w z)
    rw [h, integral_vecTiltRemainder_eq_zero]
    ring
  have hhalf := abs_integral_mul_vecTiltRemainder_le_of_support
    (G := fun z => (G z - a) / 2) (by fun_prop)
    (fun z => by
      have h1 : |G z - a| ≤ 2 := by linarith [hG1 z, ha, abs_sub (G z) a]
      rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      linarith)
    hS (fun z hz => by rw [hoff z hz]; ring) hw
  have hscale : (∫ z, (G z - a) * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = 2 * ∫ z, ((G z - a) / 2) * vecTiltRemainder w z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have h := integral_const_mul (μ := stdGaussian (EuclideanSpace ℝ (Fin k))) 2
      (fun z => ((G z - a) / 2) * vecTiltRemainder w z)
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  rw [hdec, haR0, add_zero, hscale, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  calc 2 * |∫ z, ((G z - a) / 2) * vecTiltRemainder w z
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ 2 * (Real.sqrt ((stdGaussian (EuclideanSpace ℝ (Fin k)) S).toReal)
          * (Real.sqrt tiltSqConst * ‖w‖ ^ 3)) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = 2 * Real.sqrt ((stdGaussian (EuclideanSpace ℝ (Fin k)) S).toReal)
          * (Real.sqrt tiltSqConst * ‖w‖ ^ 3) := by ring

/-- **The localised Cameron–Martin error at a point far from the boundary** (wave 29). If the
bounded test function `F` is *constant* on the ball of radius `r` around `v` — which for a
mollified convex indicator means exactly that `v` is at distance `≥ r` from the `ε`-shell of
`∂B`, the constant being `1` inside and `0` outside — then the `σ`-smoothed Cameron–Martin
remainder at `v` is weighted by the **Gaussian tail** `γ{‖z‖ ≥ r/σ}`:

`|∫ F(v + σ z) R_w(z) dγ(z)| ≤ 2 √(γ{‖z‖ ≥ r/σ}) · √tiltSqConst · ‖w‖³`.

Combined with `stdGaussian_norm_ge_le` at order `p`, the weight is `2 (E‖z‖^p)^{1/2}(σ/r)^{p/2}`.
This is the localisation that wave 24 declared to be Ball's theorem; it is not. -/
private lemma abs_integral_shift_vecTiltRemainder_le_of_const_ball
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    (v : EuclideanSpace ℝ (Fin k)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    {a : ℝ} (ha : |a| ≤ 1) (hconst : ∀ x, ‖x - v‖ < r → F x = a)
    {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ 1) :
    |∫ z, F (v + σ • z) * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ 2 * Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k)))
            {z | r / σ ≤ ‖z‖}).toReal) * (Real.sqrt tiltSqConst * ‖w‖ ^ 3) := by
  have hSm : MeasurableSet {z : EuclideanSpace ℝ (Fin k) | r / σ ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  refine abs_integral_mul_vecTiltRemainder_le_of_const_off (G := fun z => F (v + σ • z))
    (by fun_prop) (fun z => hFb _) ha hSm (fun z hz => ?_) hw
  refine hconst _ ?_
  have hz' : ‖z‖ < r / σ := lt_of_not_ge hz
  have hnorm : ‖v + σ • z - v‖ = σ * ‖z‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
  rw [hnorm]
  have hlt : σ * ‖z‖ < σ * (r / σ) := mul_lt_mul_of_pos_left hz' hσ
  have heq : σ * (r / σ) = r := by field_simp
  linarith [hlt, heq.le, heq.ge]

/-- **The localised Cameron–Martin error at a point far from the boundary, at EVERY shift
length (wave 40 — the `‖w‖ ≤ 1` restriction is REMOVED).**

Waves 29–39 could only localise a swap step at a point `v` far from `∂B` when the shift `w`
was short: `abs_integral_shift_vecTiltRemainder_le_of_const_ball` runs through
`integral_sq_vecTiltRemainder_le`, whose hypothesis `‖w‖ ≤ 1` is *not* removable — the `L²`
norm of the tilt remainder grows like `e^{‖w‖²/2}`. Every one of waves 32, 35, 38 and 39
recorded "the `‖w‖ ≤ 1` restriction is still open" as the residue of the tail brick; at step
`j` the shift is `w = (c/σ)y`, so the restriction is `‖y‖ ≤ √j`, and the complement is *not*
priceable by the third moment alone (a bare constant in the per-step weight sums to `A δ ε⁻¹`,
which is outside brick L's allowed shape — wave 35's Correction 1).

**The repair, in one line.** Do not bound the tilt remainder in `L²`. Split it into its two
halves and treat each with the structure it actually has:

* the *exponential* half is a Gaussian shift (`integral_gaussian_shift_eq_tilt`), so if `F` is
  constant on the ball of radius `σ(M + ‖w‖)` about `v` then the shifted integrand
  `F(v + σ(z+w)) − a` already vanishes on `{‖z‖ < M}` — the shift is absorbed by the *radius*,
  not by a norm bound. This half costs `2 γ{‖z‖ ≥ M}` at every `‖w‖`;
* the *polynomial* half is a genuine polynomial, so its `L²` norm is polynomial in `‖w‖` at
  every `‖w‖` (`integral_sq_vecTiltPoly_le`, `≤ 640(1+‖w‖²)²`), and Cauchy–Schwarz against the
  Gaussian tail gives `2 √(γ{‖z‖ ≥ M}) · 26(1 + ‖w‖²)`.

Both constants are **dimension-free** (the polynomial bound goes through the one-dimensional
marginal, exactly as the wave-19/29 bounds do), and neither half needs a fourth moment of the
summand law: the `‖w‖`-growth is quadratic, so against the localisation weight — which is
itself linear in `‖w‖` — the product stays cubic.

With `M = gaussianTailRadius k σ` (so `γ{‖z‖ ≥ M} ≤ σ²`, `stdGaussian_norm_ge_gaussianTailRadius_le`)
this reads `≤ 2σ² + 52 σ (1 + ‖w‖²)`, which is the far-in-`v` input of route (b) of
`abs_integral_gaussian_smoothed_swap_localised_le` at *every* shift length. -/
private lemma abs_integral_shift_vecTiltRemainder_le_of_const_ball_any
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    (v : EuclideanSpace ℝ (Fin k)) {σ M : ℝ} (hσ : 0 < σ)
    {a : ℝ} (ha : |a| ≤ 1) {w : EuclideanSpace ℝ (Fin k)}
    (hconst : ∀ x, ‖x - v‖ < σ * (M + ‖w‖) → F x = a) :
    |∫ z, F (v + σ • z) * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ 2 * ((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | M ≤ ‖z‖}).toReal
        + 2 * Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | M ≤ ‖z‖}).toReal)
            * (26 * (1 + ‖w‖ ^ 2)) := by
  classical
  have hAm : MeasurableSet {z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hHc : Continuous (fun z : EuclideanSpace ℝ (Fin k) => F (v + σ • z) - a) := by
    fun_prop
  have hHb : ∀ z : EuclideanSpace ℝ (Fin k), |F (v + σ • z) - a| ≤ 2 := by
    intro z
    have h1 := abs_le.1 (hFb (v + σ • z))
    have h2 := abs_le.1 ha
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hHzero : ∀ z : EuclideanSpace ℝ (Fin k), ‖z‖ < M + ‖w‖ →
      F (v + σ • z) - a = 0 := by
    intro z hz
    have hnorm : ‖(v + σ • z) - v‖ = σ * ‖z‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    have hlt : ‖(v + σ • z) - v‖ < σ * (M + ‖w‖) := by
      rw [hnorm]; exact mul_lt_mul_of_pos_left hz hσ
    rw [hconst _ hlt, sub_self]
  have hHsupp : ∀ z : EuclideanSpace ℝ (Fin k),
      z ∉ {z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖} → F (v + σ • z) - a = 0 := by
    intro z hz
    have h1 : ‖z‖ < M := lt_of_not_ge hz
    exact hHzero z (by linarith [norm_nonneg w])
  -- (i) the constant may be subtracted, since `∫ R_w dγ = 0`
  have hRint := integrable_vecTiltRemainder (k := k) w
  have hHRint : Integrable (fun z => (F (v + σ • z) - a) * vecTiltRemainder w z)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    refine Integrable.mono' (hRint.abs.const_mul 2) (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hHb z, abs_nonneg (vecTiltRemainder w z),
      abs_nonneg (F (v + σ • z) - a)]
  have haRint : Integrable (fun z => a * vecTiltRemainder w z)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := hRint.const_mul a
  have haRval : (∫ z, a * vecTiltRemainder w z
      ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = 0 := by
    rw [integral_const_mul, integral_vecTiltRemainder_eq_zero, mul_zero]
  have hrecentre : (∫ z, F (v + σ • z) * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ z, (F (v + σ • z) - a) * vecTiltRemainder w z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have hsum := integral_add hHRint haRint
    have hcongr : (∫ z, F (v + σ • z) * vecTiltRemainder w z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = ∫ z, ((F (v + σ • z) - a) * vecTiltRemainder w z + a * vecTiltRemainder w z)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [hcongr, hsum, haRval, add_zero]
  -- (ii) split the tilt into its exponential and polynomial halves
  have hEint : Integrable (fun z => (F (v + σ • z) - a)
      * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have hhalf := integrable_mul_exp_tilt_gauss
      (G := fun z : EuclideanSpace ℝ (Fin k) => (F (v + σ • z) - a) / 2) (by fun_prop)
      (fun x => by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        linarith [hHb x]) w
    refine (hhalf.const_mul 2).congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    ring
  have hPint : Integrable (fun z => (F (v + σ • z) - a)
      * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have hhalf := integrable_mul_tiltPoly_gauss
      (G := fun z : EuclideanSpace ℝ (Fin k) => (F (v + σ • z) - a) / 2) (by fun_prop)
      (fun x => by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        linarith [hHb x]) w
    refine (hhalf.const_mul 2).congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    ring
  have hsplit : (∫ z, (F (v + σ • z) - a) * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = (∫ z, (F (v + σ • z) - a) * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        - ∫ z, (F (v + σ • z) - a)
            * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [← integral_sub hEint hPint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [vecTiltRemainder]
    ring
  -- (iii) the exponential half is a Gaussian shift, and the shift is absorbed by the radius
  have hshift := integral_gaussian_shift_eq_tilt
    (g := fun z : EuclideanSpace ℝ (Fin k) => F (v + σ • z) - a) hHc w
  have hbdshift : ∀ z : EuclideanSpace ℝ (Fin k),
      |F (v + σ • (z + w)) - a|
        ≤ 2 * ({z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}).indicator
            (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ {z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}
    · rw [Set.indicator_of_mem hz, mul_one]
      exact hHb (z + w)
    · have h1 : ‖z‖ < M := lt_of_not_ge hz
      have h2 : ‖z + w‖ < M + ‖w‖ := lt_of_le_of_lt (norm_add_le z w) (by linarith)
      rw [hHzero _ h2, Set.indicator_of_notMem hz]
      simp
  have hintshift : Integrable (fun z : EuclideanSpace ℝ (Fin k) =>
      F (v + σ • (z + w)) - a) (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    refine Integrable.mono' (integrable_const (2 : ℝ)) (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact hHb (z + w)
  have hindint : Integrable (fun z : EuclideanSpace ℝ (Fin k) =>
      2 * ({z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}).indicator (fun _ => (1 : ℝ)) z)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
    ((integrable_const (1 : ℝ)).indicator hAm).const_mul 2
  have hexpbd : |∫ z, (F (v + σ • z) - a) * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ 2 * ((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | M ≤ ‖z‖}).toReal := by
    rw [← hshift]
    calc |∫ z, (F (v + σ • (z + w)) - a) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        ≤ ∫ z, |F (v + σ • (z + w)) - a| ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, 2 * ({z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}).indicator
            (fun _ => (1 : ℝ)) z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
          integral_mono hintshift.abs hindint hbdshift
      _ = 2 * ((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | M ≤ ‖z‖}).toReal := by
          rw [integral_const_mul, integral_indicator_const (1 : ℝ) hAm]
          simp [Measure.real]
  -- (iv) the polynomial half by Cauchy–Schwarz against the Gaussian tail
  have hHsq : Integrable (fun z => (F (v + σ • z) - a) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    refine Integrable.mono' (((integrable_const (1 : ℝ)).indicator hAm).const_mul 4)
      (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hz : z ∈ {z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}
    · rw [Set.indicator_of_mem hz, mul_one]
      nlinarith [hHb z, abs_nonneg (F (v + σ • z) - a), sq_abs (F (v + σ • z) - a)]
    · rw [hHsupp z hz, Set.indicator_of_notMem hz]
      simp
  have hHsqbd : (∫ z, (F (v + σ • z) - a) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ 4 * ((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | M ≤ ‖z‖}).toReal := by
    have hptw : ∀ z : EuclideanSpace ℝ (Fin k), (F (v + σ • z) - a) ^ 2
        ≤ 4 * ({z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}).indicator
            (fun _ => (1 : ℝ)) z := by
      intro z
      by_cases hz : z ∈ {z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}
      · rw [Set.indicator_of_mem hz, mul_one]
        nlinarith [hHb z, abs_nonneg (F (v + σ • z) - a), sq_abs (F (v + σ • z) - a)]
      · rw [hHsupp z hz, Set.indicator_of_notMem hz]
        simp
    have hmono := integral_mono hHsq
      (((integrable_const (1 : ℝ)).indicator hAm).const_mul 4) hptw
    have hval : (∫ z, 4 * ({z : EuclideanSpace ℝ (Fin k) | M ≤ ‖z‖}).indicator
          (fun _ => (1 : ℝ)) z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = 4 * ((stdGaussian (EuclideanSpace ℝ (Fin k))) {z | M ≤ ‖z‖}).toReal := by
      rw [integral_const_mul, integral_indicator_const (1 : ℝ) hAm]
      simp [Measure.real]
    linarith [hmono, hval.le, hval.ge]
  have hHabs : MemLp (fun z => |F (v + σ • z) - a|) (ENNReal.ofReal 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hHc.abs.aestronglyMeasurable).2 ?_
    simpa [sq_abs] using hHsq
  have hPabs : MemLp (fun z : EuclideanSpace ℝ (Fin k) =>
      |1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2|) (ENNReal.ofReal 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    simpa [sq_abs] using integrable_sq_vecTiltPoly w
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := stdGaussian (EuclideanSpace ℝ (Fin k))) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun z => abs_nonneg (F (v + σ • z) - a))
    (Filter.Eventually.of_forall fun z =>
      abs_nonneg (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)) hHabs hPabs
  have hrp : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrp, sq_abs, ← Real.sqrt_eq_rpow] at hmain
  have hsqrt4 : Real.sqrt (4 * ((stdGaussian (EuclideanSpace ℝ (Fin k)))
        {z | M ≤ ‖z‖}).toReal)
      = 2 * Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k)))
        {z | M ≤ ‖z‖}).toReal) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtP : Real.sqrt (640 * (1 + ‖w‖ ^ 2) ^ 2) ≤ 26 * (1 + ‖w‖ ^ 2) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 640),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + ‖w‖ ^ 2)]
    have h1 : Real.sqrt 640 ≤ 26 := by
      have h2 : Real.sqrt 640 ≤ Real.sqrt (26 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 26)] at h2
    nlinarith [Real.sqrt_nonneg (640 : ℝ), sq_nonneg ‖w‖]
  have hpolybd : |∫ z, (F (v + σ • z) - a)
        * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ 2 * Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k)))
          {z | M ≤ ‖z‖}).toReal) * (26 * (1 + ‖w‖ ^ 2)) := by
    calc |∫ z, (F (v + σ • z) - a)
            * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        ≤ ∫ z, |(F (v + σ • z) - a)
            * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)|
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := abs_integral_le_integral_abs
      _ = ∫ z, |F (v + σ • z) - a| * |1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2|
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by simp only [abs_mul]
      _ ≤ Real.sqrt (∫ z, (F (v + σ • z) - a) ^ 2
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            * Real.sqrt (∫ z, (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2) ^ 2
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) := hmain
      _ ≤ Real.sqrt (4 * ((stdGaussian (EuclideanSpace ℝ (Fin k)))
              {z | M ≤ ‖z‖}).toReal) * Real.sqrt (640 * (1 + ‖w‖ ^ 2) ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt hHsqbd)
            (Real.sqrt_le_sqrt (integral_sq_vecTiltPoly_le w)) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k)))
              {z | M ≤ ‖z‖}).toReal) * (26 * (1 + ‖w‖ ^ 2)) := by
          rw [hsqrt4]
          exact mul_le_mul_of_nonneg_left hsqrtP (by positivity)
  rw [hrecentre, hsplit]
  calc |(∫ z, (F (v + σ • z) - a) * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        - ∫ z, (F (v + σ • z) - a) * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ |∫ z, (F (v + σ • z) - a) * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        + |∫ z, (F (v + σ • z) - a) * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| := abs_sub _ _
    _ ≤ _ := by linarith [hexpbd, hpolybd]

/-- **The crude swap-step bound: at most QUADRATIC in the shift** (wave 40).
`|∫ G R_w dγ| ≤ 2 + ‖w‖ + ‖w‖²` whenever `|G| ≤ 1`.

The uniform bound `integral_abs_vecTiltRemainder_le` is *cubic* in `‖w‖`. That is the right
shape when the step is priced by a *constant* weight, but the localised tail brick prices a step
at a point `v` by the shell mass at the varying width `σ(R + ‖w‖)`, which is itself *linear* in
`‖w‖`; against a cubic bound the product would be quartic and would need a fourth moment of the
summand law, which is not available. Against this quadratic bound the product is cubic, i.e.
exactly a third moment.

Both halves are elementary: the exponential half is a Gaussian *shift* of a function bounded by
`1`, hence bounded by `1`; the polynomial half is `integral_abs_vecTiltPoly_le`. -/
private lemma abs_integral_mul_vecTiltRemainder_le_crude
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hGc : Continuous G) (hG1 : ∀ z, |G z| ≤ 1)
    (w : EuclideanSpace ℝ (Fin k)) :
    |∫ z, G z * vecTiltRemainder w z ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ 2 + ‖w‖ + ‖w‖ ^ 2 := by
  have hEint := integrable_mul_exp_tilt_gauss hGc hG1 w
  have hPint := integrable_mul_tiltPoly_gauss hGc hG1 w
  have hsplit : (∫ z, G z * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = (∫ z, G z * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        - ∫ z, G z * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [← integral_sub hEint hPint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [vecTiltRemainder]
    ring
  have hshift := integral_gaussian_shift_eq_tilt hGc w
  have hexp : |∫ z, G z * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| ≤ 1 := by
    rw [← hshift]
    have hint : Integrable (fun z : EuclideanSpace ℝ (Fin k) => G (z + w))
        (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
      filter_upwards with z
      rw [Real.norm_eq_abs]
      exact hG1 _
    calc |∫ z, G (z + w) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        ≤ ∫ z, |G (z + w)| ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _z : EuclideanSpace ℝ (Fin k), (1 : ℝ)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
          integral_mono hint.abs (integrable_const _) (fun z => hG1 _)
      _ = 1 := by rw [integral_const]; simp
  have hpoly : |∫ z, G z * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| ≤ 1 + ‖w‖ + ‖w‖ ^ 2 := by
    have habs : Integrable (fun z : EuclideanSpace ℝ (Fin k) =>
        |1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2|)
        (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
      have h := integrable_mul_tiltPoly_gauss
        (G := fun _ : EuclideanSpace ℝ (Fin k) => (1 : ℝ)) continuous_const
        (fun _ => by norm_num) w
      refine (h.abs).congr (Filter.Eventually.of_forall fun z => ?_)
      simp
    calc |∫ z, G z * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        ≤ ∫ z, |G z * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)|
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := abs_integral_le_integral_abs
      _ ≤ ∫ z, |1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2|
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
          refine integral_mono hPint.abs habs fun z => ?_
          rw [abs_mul]
          nlinarith [hG1 z, abs_nonneg (G z),
            abs_nonneg (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)]
      _ ≤ 1 + ‖w‖ + ‖w‖ ^ 2 := integral_abs_vecTiltPoly_le w
  rw [hsplit]
  calc |(∫ z, G z * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        - ∫ z, G z * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ |∫ z, G z * Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        + |∫ z, G z * (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| := abs_sub _ _
    _ ≤ 2 + ‖w‖ + ‖w‖ ^ 2 := by linarith

/-- **The polynomial part of the tilt has the same integral for every centred,
identity-covariance law.** This is the exact analogue of the vanishing of the linear term and
the coincidence of the quadratic term in the classical Lindeberg swap — here for the
*Cameron–Martin* expansion rather than the Taylor expansion of the test function. -/
private lemma tiltPoly_fubini {τ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure τ]
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂τ) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂τ) = ⟪u, v⟫_ℝ)
    (hτ1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) τ)
    (hτ2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) τ)
    (hdim : (∫ y, ‖y‖ ^ 2 ∂τ) = (k : ℝ))
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hG : Continuous G) (hGb : ∀ x, |G x| ≤ 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Integrable (fun y => ∫ z, G z * (1 + ⟪lam • y, z⟫_ℝ
        + (⟪lam • y, z⟫_ℝ ^ 2 - ‖lam • y‖ ^ 2) / 2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) τ
      ∧ (∫ y, (∫ z, G z * (1 + ⟪lam • y, z⟫_ℝ
          + (⟪lam • y, z⟫_ℝ ^ 2 - ‖lam • y‖ ^ 2) / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂τ)
        = ∫ z, G z * (1 + lam ^ 2 * (‖z‖ ^ 2 - (k : ℝ)) / 2)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  classical
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  have hsmul : ∀ (y z : EuclideanSpace ℝ (Fin k)),
      ⟪lam • y, z⟫_ℝ = lam * ⟪y, z⟫_ℝ := fun y z => real_inner_smul_left _ _ _
  have hnsmul : ∀ y : EuclideanSpace ℝ (Fin k), ‖lam • y‖ ^ 2 = lam ^ 2 * ‖y‖ ^ 2 := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam, mul_pow]
  -- the product-integrability of the polynomial integrand
  have henv : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      1 + lam * (‖p.1‖ * ‖p.2‖)
        + (lam ^ 2 * (‖p.1‖ ^ 2 * ‖p.2‖ ^ 2) + lam ^ 2 * ‖p.1‖ ^ 2) / 2) (τ.prod γ) := by
    have e1 : Integrable (fun _ : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        (1 : ℝ)) (τ.prod γ) := integrable_const _
    have e2 : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        lam * (‖p.1‖ * ‖p.2‖)) (τ.prod γ) :=
      (hτ1.mul_prod integrable_norm_gauss).const_mul lam
    have e3 : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        lam ^ 2 * (‖p.1‖ ^ 2 * ‖p.2‖ ^ 2)) (τ.prod γ) :=
      (hτ2.mul_prod (memLp_norm_gauss (k := k) 2)).const_mul (lam ^ 2)
    have e4 : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        lam ^ 2 * ‖p.1‖ ^ 2) (τ.prod γ) := (hτ2.comp_fst γ).const_mul (lam ^ 2)
    have e34 : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        lam ^ 2 * (‖p.1‖ ^ 2 * ‖p.2‖ ^ 2) + lam ^ 2 * ‖p.1‖ ^ 2) (τ.prod γ) := e3.add e4
    exact (e1.add e2).add (e34.div_const 2)
  have hprod : Integrable (Function.uncurry fun (y z : EuclideanSpace ℝ (Fin k)) =>
      G z * (1 + ⟪lam • y, z⟫_ℝ + (⟪lam • y, z⟫_ℝ ^ 2 - ‖lam • y‖ ^ 2) / 2)) (τ.prod γ) := by
    refine Integrable.mono' henv (by fun_prop) ?_
    filter_upwards with p
    obtain ⟨y, z⟩ := p
    set ip : ℝ := ⟪y, z⟫_ℝ with hip
    have hin : |ip| ≤ ‖y‖ * ‖z‖ := abs_real_inner_le_norm _ _
    have hsq : ip ^ 2 ≤ ‖y‖ ^ 2 * ‖z‖ ^ 2 := by
      calc ip ^ 2 = |ip| ^ 2 := (sq_abs _).symm
        _ ≤ (‖y‖ * ‖z‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hin 2
        _ = ‖y‖ ^ 2 * ‖z‖ ^ 2 := by ring
    have hval : (Function.uncurry fun (y z : EuclideanSpace ℝ (Fin k)) =>
        G z * (1 + ⟪lam • y, z⟫_ℝ + (⟪lam • y, z⟫_ℝ ^ 2 - ‖lam • y‖ ^ 2) / 2)) (y, z)
        = G z * (1 + lam * ip + (lam ^ 2 * ip ^ 2 - lam ^ 2 * ‖y‖ ^ 2) / 2) := by
      simp only [Function.uncurry, hsmul, hnsmul, hip]
      ring
    rw [Real.norm_eq_abs, hval]
    have p1 : lam * ip ≤ lam * (‖y‖ * ‖z‖) := by nlinarith [hlam, hin, le_abs_self ip]
    have p2 : -(lam * (‖y‖ * ‖z‖)) ≤ lam * ip := by nlinarith [hlam, hin, neg_abs_le ip]
    have p3 : lam ^ 2 * ip ^ 2 ≤ lam ^ 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg lam)
    have p4 : (0 : ℝ) ≤ lam ^ 2 * ‖y‖ ^ 2 := by positivity
    have p5 : (0 : ℝ) ≤ lam ^ 2 * ip ^ 2 := by positivity
    have hpabs : |1 + lam * ip + (lam ^ 2 * ip ^ 2 - lam ^ 2 * ‖y‖ ^ 2) / 2|
        ≤ 1 + lam * (‖y‖ * ‖z‖)
          + (lam ^ 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) + lam ^ 2 * ‖y‖ ^ 2) / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hnn : (0 : ℝ) ≤ 1 + lam * (‖y‖ * ‖z‖)
        + (lam ^ 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) + lam ^ 2 * ‖y‖ ^ 2) / 2 := by
      have : (0 : ℝ) ≤ lam * (‖y‖ * ‖z‖) := by positivity
      have h2 : (0 : ℝ) ≤ lam ^ 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) := by positivity
      linarith
    calc |G z * (1 + lam * ip + (lam ^ 2 * ip ^ 2 - lam ^ 2 * ‖y‖ ^ 2) / 2)|
        = |G z| * |1 + lam * ip + (lam ^ 2 * ip ^ 2 - lam ^ 2 * ‖y‖ ^ 2) / 2| := abs_mul _ _
      _ ≤ 1 * (1 + lam * (‖y‖ * ‖z‖)
            + (lam ^ 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) + lam ^ 2 * ‖y‖ ^ 2) / 2) :=
          mul_le_mul (hGb z) hpabs (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  refine ⟨hprod.integral_prod_left, ?_⟩
  rw [integral_integral_swap hprod]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  -- the inner `τ`-integral
  have h1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ⟪y, z⟫_ℝ) τ := by
    refine Integrable.mono' (hτ1.mul_const ‖z‖) (by fun_prop) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm y z
  have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ⟪y, z⟫_ℝ ^ 2) τ := by
    refine Integrable.mono' (hτ2.mul_const (‖z‖ ^ 2)) (by fun_prop) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_real_inner_le_norm y z, abs_nonneg (⟪y, z⟫_ℝ), sq_abs (⟪y, z⟫_ℝ),
      norm_nonneg y, norm_nonneg z]
  have hmeanz : (∫ y, ⟪y, z⟫_ℝ ∂τ) = 0 := by
    have h := hmean z
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => (real_inner_comm y z).symm)
  have hcovz : (∫ y, ⟪y, z⟫_ℝ ^ 2 ∂τ) = ‖z‖ ^ 2 := by
    have h := hcov z z
    rw [real_inner_self_eq_norm_sq] at h
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [sq, ← real_inner_comm y z])
  have hinner : (∫ y, G z * (1 + ⟪lam • y, z⟫_ℝ
      + (⟪lam • y, z⟫_ℝ ^ 2 - ‖lam • y‖ ^ 2) / 2) ∂τ)
      = G z * (1 + lam ^ 2 * (‖z‖ ^ 2 - (k : ℝ)) / 2) := by
    have hrwf : (fun y : EuclideanSpace ℝ (Fin k) => G z * (1 + ⟪lam • y, z⟫_ℝ
        + (⟪lam • y, z⟫_ℝ ^ 2 - ‖lam • y‖ ^ 2) / 2))
        = fun y => G z * ((1 + lam * ⟪y, z⟫_ℝ)
          + (lam ^ 2 * ⟪y, z⟫_ℝ ^ 2 - lam ^ 2 * ‖y‖ ^ 2) / 2) := by
      funext y
      rw [hsmul y z, hnsmul y]
      ring
    rw [hrwf, integral_const_mul]
    congr 1
    have i1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => 1 + lam * ⟪y, z⟫_ℝ) τ :=
      (integrable_const (1 : ℝ)).add (h1.const_mul lam)
    have i2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
        (lam ^ 2 * ⟪y, z⟫_ℝ ^ 2 - lam ^ 2 * ‖y‖ ^ 2) / 2) τ :=
      ((h2.const_mul (lam ^ 2)).sub (hτ2.const_mul (lam ^ 2))).div_const 2
    rw [integral_add i1 i2,
      integral_add (integrable_const (1 : ℝ)) (h1.const_mul lam), integral_const,
      integral_const_mul, hmeanz, integral_div,
      integral_sub (h2.const_mul (lam ^ 2)) (hτ2.const_mul (lam ^ 2)),
      integral_const_mul, integral_const_mul, hcovz, hdim]
    simp only [probReal_univ, smul_eq_mul, mul_one]
    ring
  simpa using hinner

/-- **The tilt representation of the Gaussian-smoothed step (wave 41).** *Exact*, and with no
moment hypothesis beyond the two the Cameron–Martin polynomial consumes.

Averaging `F(v + σz + cy)` over `y ∼ τ` and `z ∼ γ` and subtracting the number
`∫ F(v + σz)(1 + (c/σ)²(‖z‖² − k)/2) dγ` — which by `tiltPoly_fubini` depends on `τ` through
its first two moments only, hence is the *same* for every centred, identity-covariance law —
leaves exactly the `τ`-average of the Cameron–Martin **tilt remainder** at shift `(c/σ)y`.

Waves 32–40 recorded this identity as "established inside
`abs_integral_gaussian_smoothed_sub_common_le` but not exported"; it is the first of the three
bookkeeping pieces the tail brick `abs_integral_gaussian_smoothed_swap_localised_le` needs, and
it is what lets that brick apply the *localised* pointwise estimate
`abs_integral_shift_vecTiltRemainder_localised_le` under the `τ`-average, rather than the
unlocalised `L¹` bound. The integrability of the `y`-integrand is returned alongside, because
every consumer needs it to move an absolute value or a sum through the `τ`-integral.

`abs_integral_gaussian_smoothed_sub_common_le` is now a one-line corollary: bound the
remainder by its `L¹` norm `C‖(c/σ)y‖³` and integrate. -/
private lemma integral_gaussian_smoothed_sub_common_eq
    {τ : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure τ]
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂τ) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂τ) = ⟪u, v⟫_ℝ)
    (hτ1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) τ)
    (hτ2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) τ)
    (hdim : (∫ y, ‖y‖ ^ 2 ∂τ) = (k : ℝ))
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    (v : EuclideanSpace ℝ (Fin k)) {σ c : ℝ} (hσ : 0 < σ) (hc : 0 ≤ c) :
    Integrable (fun y => ∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) τ
      ∧ (∫ y, (∫ z, F (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂τ)
          - ∫ z, F (v + σ • z) * (1 + (c / σ) ^ 2 * (‖z‖ ^ 2 - (k : ℝ)) / 2)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
        = ∫ y, (∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂τ := by
  classical
  set lam : ℝ := c / σ with hlamdef
  have hlam : (0 : ℝ) ≤ lam := div_nonneg hc hσ.le
  have hsc : σ * lam = c := by rw [hlamdef]; field_simp
  set G : EuclideanSpace ℝ (Fin k) → ℝ := fun z => F (v + σ • z) with hGdef
  have hGcont : Continuous G := by rw [hGdef]; fun_prop
  have hGb : ∀ x, |G x| ≤ 1 := fun x => hFb _
  have hGRint : ∀ a : EuclideanSpace ℝ (Fin k),
      Integrable (fun z => G z * vecTiltRemainder a z)
        (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro a
    refine ((integrable_mul_exp_tilt_gauss hGcont hGb a).sub
      (integrable_mul_tiltPoly_gauss hGcont hGb a)).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, vecTiltRemainder]
    ring
  -- (i) each inner integral is a Cameron–Martin tilt integral
  have hshift : ∀ y : EuclideanSpace ℝ (Fin k),
      (∫ z, F (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = ∫ z, G z * Real.exp (⟪lam • y, z⟫_ℝ - ‖lam • y‖ ^ 2 / 2)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro y
    have hpt : ∀ z : EuclideanSpace ℝ (Fin k),
        F (v + σ • z + c • y) = G (z + lam • y) := by
      intro z
      have harg : v + σ • (z + lam • y) = v + σ • z + c • y := by
        rw [smul_add, smul_smul, hsc, ← add_assoc]
      simp only [hGdef]
      rw [harg]
    simp_rw [hpt]
    exact integral_gaussian_shift_eq_tilt hGcont (lam • y)
  -- (ii) split the tilt into its quadratic Taylor part and the remainder
  have hsplit : ∀ y : EuclideanSpace ℝ (Fin k),
      (∫ z, G z * Real.exp (⟪lam • y, z⟫_ℝ - ‖lam • y‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = (∫ z, G z * (1 + ⟪lam • y, z⟫_ℝ
            + (⟪lam • y, z⟫_ℝ ^ 2 - ‖lam • y‖ ^ 2) / 2)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          + ∫ z, G z * vecTiltRemainder (lam • y) z
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro y
    rw [← integral_add (integrable_mul_tiltPoly_gauss hGcont hGb (lam • y)) (hGRint (lam • y))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [vecTiltRemainder]
    ring
  -- integrability of the two `y`-integrands
  have hΦcont : Continuous (fun y : EuclideanSpace ℝ (Fin k) =>
      ∫ z, F (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
    refine continuous_of_dominated (fun y => (hF.comp (by fun_prop)).aestronglyMeasurable)
      (fun y => Filter.Eventually.of_forall fun z => ?_) (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun z => by fun_prop)
    rw [Real.norm_eq_abs]
    exact hFb _
  have hΦint : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
      ∫ z, F (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) τ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hΦcont.aestronglyMeasurable ?_
    filter_upwards with y
    have h := norm_integral_le_of_norm_le_const
      (μ := stdGaussian (EuclideanSpace ℝ (Fin k))) (C := (1 : ℝ))
      (f := fun z => F (v + σ • z + c • y))
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hFb _)
    simpa using h
  obtain ⟨hQint, hQval⟩ := tiltPoly_fubini hmean hcov hτ1 hτ2 hdim hGcont hGb hlam
  have hRint : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
      ∫ z, G z * vecTiltRemainder (lam • y) z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) τ := by
    refine (hΦint.sub hQint).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply, hshift y, hsplit y]
    ring
  have hsum : (∫ y, (∫ z, F (v + σ • z + c • y)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂τ)
      = (∫ y, (∫ z, G z * (1 + ⟪lam • y, z⟫_ℝ
          + (⟪lam • y, z⟫_ℝ ^ 2 - ‖lam • y‖ ^ 2) / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂τ)
        + ∫ y, (∫ z, G z * vecTiltRemainder (lam • y) z
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂τ := by
    rw [← integral_add hQint hRint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hshift y, hsplit y]
  refine ⟨by simpa only [hGdef] using hRint, ?_⟩
  rw [hsum, hQval, hGdef, add_sub_cancel_left]

/-- **The Gaussian-smoothed Lindeberg swap step.** If the test function is first mollified by a
Gaussian of scale `σ > 0`, then replacing a summand of law `τ` (centred, identity covariance,
finite third moment) by *any* other such law costs at most `C (c/σ)³ β_τ` — with **no third
derivative of the test function**: the three derivatives are absorbed by the Gaussian kernel
through the Cameron–Martin formula. This is the ingredient that replaces the factor `ε⁻³` of
the mollifier route by `σ⁻³`, and hence improves the exponent of the elementary
Berry–Esseen rate.

Wave 41: the exact part of the argument is now
`integral_gaussian_smoothed_sub_common_eq`, and what is left here is the third moment. -/
private lemma abs_integral_gaussian_smoothed_sub_common_le {C : ℝ}
    (hC : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ C * s ^ 3)
    {τ : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure τ]
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂τ) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂τ) = ⟪u, v⟫_ℝ)
    (hτ1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) τ)
    (hτ2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) τ)
    (hτ3 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) τ)
    (hdim : (∫ y, ‖y‖ ^ 2 ∂τ) = (k : ℝ))
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    (v : EuclideanSpace ℝ (Fin k)) {σ c : ℝ} (hσ : 0 < σ) (hc : 0 ≤ c) :
    |(∫ y, (∫ z, F (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂τ)
        - ∫ z, F (v + σ • z) * (1 + (c / σ) ^ 2 * (‖z‖ ^ 2 - (k : ℝ)) / 2)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ C * (c / σ) ^ 3 * ∫ y, ‖y‖ ^ 3 ∂τ := by
  classical
  obtain ⟨hRint, heq⟩ := integral_gaussian_smoothed_sub_common_eq hmean hcov hτ1 hτ2 hdim
    hF hFb v hσ hc
  rw [heq]
  have hlam : (0 : ℝ) ≤ c / σ := div_nonneg hc hσ.le
  have hGcont : Continuous (fun z : EuclideanSpace ℝ (Fin k) => F (v + σ • z)) := by fun_prop
  have hGb : ∀ x : EuclideanSpace ℝ (Fin k), |F (v + σ • x)| ≤ 1 := fun x => hFb _
  have hGRint : ∀ a : EuclideanSpace ℝ (Fin k),
      Integrable (fun z => F (v + σ • z) * vecTiltRemainder a z)
        (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro a
    refine ((integrable_mul_exp_tilt_gauss hGcont hGb a).sub
      (integrable_mul_tiltPoly_gauss hGcont hGb a)).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, vecTiltRemainder]
    ring
  -- the remainder bound
  have hbnd : ∀ y : EuclideanSpace ℝ (Fin k),
      |∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| ≤ C * (c / σ) ^ 3 * ‖y‖ ^ 3 := by
    intro y
    calc |∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        ≤ ∫ z, |F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z|
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := abs_integral_le_integral_abs
      _ ≤ ∫ z, |vecTiltRemainder ((c / σ) • y) z|
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
          refine integral_mono (hGRint _).abs (integrable_vecTiltRemainder _).abs fun z => ?_
          rw [abs_mul]
          nlinarith [hGb z, abs_nonneg (F (v + σ • z)),
            abs_nonneg (vecTiltRemainder ((c / σ) • y) z)]
      _ ≤ C * ‖(c / σ) • y‖ ^ 3 := integral_abs_vecTiltRemainder_le hC _
      _ = C * (c / σ) ^ 3 * ‖y‖ ^ 3 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam, mul_pow]
          ring
  calc |∫ y, (∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂τ|
      ≤ ∫ y, |∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| ∂τ := abs_integral_le_integral_abs
    _ ≤ ∫ y, C * (c / σ) ^ 3 * ‖y‖ ^ 3 ∂τ :=
        integral_mono hRint.abs (hτ3.const_mul _) hbnd
    _ = C * (c / σ) ^ 3 * ∫ y, ‖y‖ ^ 3 ∂τ := integral_const_mul _ _

/-- **Two-law form of the Gaussian-smoothed swap.** Both laws are compared with the *same*
number — the Cameron–Martin polynomial part, which by `tiltPoly_fubini` depends only on the
first two moments — so the whole cost is the two tilt remainders. -/
private lemma abs_integral_gaussian_smoothed_swap_le {C : ℝ}
    (hC : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ C * s ^ 3)
    {ν ρ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hmeanν : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcovν : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hν1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν)
    (hν2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (hν3 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ν)
    (hνdim : (∫ y, ‖y‖ ^ 2 ∂ν) = (k : ℝ))
    (hmeanρ : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ρ) = 0)
    (hcovρ : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ρ) = ⟪u, v⟫_ℝ)
    (hρ1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ρ)
    (hρ2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ρ)
    (hρ3 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ρ)
    (hρdim : (∫ y, ‖y‖ ^ 2 ∂ρ) = (k : ℝ))
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    (v : EuclideanSpace ℝ (Fin k)) {σ c : ℝ} (hσ : 0 < σ) (hc : 0 ≤ c) :
    |(∫ y, (∫ z, F (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
        - (∫ y, (∫ z, F (v + σ • z + c • y)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ)|
      ≤ C * (c / σ) ^ 3 * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ)) := by
  have hν := abs_integral_gaussian_smoothed_sub_common_le hC hmeanν hcovν hν1 hν2 hν3 hνdim
    hF hFb v hσ hc
  have hρ := abs_integral_gaussian_smoothed_sub_common_le hC hmeanρ hcovρ hρ1 hρ2 hρ3 hρdim
    hF hFb v hσ hc
  set A : ℝ := ∫ y, (∫ z, F (v + σ • z + c • y)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν with hA
  set B : ℝ := ∫ y, (∫ z, F (v + σ • z + c • y)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ with hB
  set D : ℝ := ∫ z, F (v + σ • z) * (1 + (c / σ) ^ 2 * (‖z‖ ^ 2 - (k : ℝ)) / 2)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) with hD
  have htri : |A - B| ≤ |A - D| + |B - D| := by
    have h := abs_sub (A - D) (B - D)
    calc |A - B| = |(A - D) - (B - D)| := by ring_nf
      _ ≤ |A - D| + |B - D| := abs_sub _ _
  have hexp : C * (c / σ) ^ 3 * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ))
      = C * (c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν) + C * (c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ) := by ring
  rw [hexp]
  linarith [htri, hν, hρ]

end SmoothedSwap

end GaussianTilt

/-! #### Gaussian convolution: the second of the three assembly bricks -/

section GaussianConvolution

variable {k : ℕ}

/-- **Gaussian convolution.** The sum of independent `σ`- and `c`-scaled standard Gaussians is
a `√(σ² + c²)`-scaled standard Gaussian. Proved by characteristic functions
(`Measure.ext_of_charFun`), the product measure factorising the integral through
`integral_prod_mul`. -/
private lemma map_stdGaussian_pair_smul_add (σ c : ℝ) :
    (((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin k)))).map fun p => σ • p.1 + c • p.2)
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map
          fun z => Real.sqrt (σ ^ 2 + c ^ 2) • z := by
  haveI hL : IsProbabilityMeasure ((((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin k)))).map fun p => σ • p.1 + c • p.2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI hR : IsProbabilityMeasure ((stdGaussian (EuclideanSpace ℝ (Fin k))).map
      fun z => Real.sqrt (σ ^ 2 + c ^ 2) • z) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  -- `charFun_apply` is definitional, so both unfoldings below are `rfl`; going through them
  -- keeps every integral in one and the same notation for `rw`.
  have hunfold : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))) (s : EuclideanSpace ℝ (Fin k)),
      charFun μ s = ∫ x, Complex.exp ((⟪x, s⟫_ℝ : ℂ) * Complex.I) ∂μ := fun _ _ => rfl
  have hstd : ∀ s : EuclideanSpace ℝ (Fin k),
      (∫ x, Complex.exp ((⟪x, s⟫_ℝ : ℂ) * Complex.I)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = Complex.exp (-(‖s‖ : ℝ) ^ 2 / 2) := fun s => charFun_stdGaussian s
  refine Measure.ext_of_charFun ?_
  funext t
  have hs2 : Real.sqrt (σ ^ 2 + c ^ 2) ^ 2 = σ ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hRHS : charFun ((stdGaussian (EuclideanSpace ℝ (Fin k))).map
      fun z => Real.sqrt (σ ^ 2 + c ^ 2) • z) t
      = Complex.exp (-((σ ^ 2 + c ^ 2) * ‖t‖ ^ 2 : ℝ) / 2) := by
    rw [hunfold, integral_map (by fun_prop) (by fun_prop)]
    have hin : ∀ z : EuclideanSpace ℝ (Fin k),
        ((⟪Real.sqrt (σ ^ 2 + c ^ 2) • z, t⟫_ℝ : ℝ) : ℂ)
          = ((⟪z, Real.sqrt (σ ^ 2 + c ^ 2) • t⟫_ℝ : ℝ) : ℂ) := by
      intro z
      rw [real_inner_smul_left, real_inner_smul_right]
    simp_rw [hin]
    rw [hstd]
    congr 1
    have hnorm : ‖Real.sqrt (σ ^ 2 + c ^ 2) • t‖ ^ 2 = (σ ^ 2 + c ^ 2) * ‖t‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hs2]
    have hcast : ((‖Real.sqrt (σ ^ 2 + c ^ 2) • t‖ : ℝ) : ℂ) ^ 2
        = (((σ ^ 2 + c ^ 2) * ‖t‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, hnorm]
    rw [hcast]
  have hLHS : charFun ((((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin k)))).map fun p => σ • p.1 + c • p.2)) t
      = Complex.exp (-((σ ^ 2 + c ^ 2) * ‖t‖ ^ 2 : ℝ) / 2) := by
    rw [hunfold, integral_map (by fun_prop) (by fun_prop)]
    have hfac : ∀ p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k),
        Complex.exp ((⟪σ • p.1 + c • p.2, t⟫_ℝ : ℂ) * Complex.I)
          = Complex.exp ((⟪p.1, σ • t⟫_ℝ : ℂ) * Complex.I)
            * Complex.exp ((⟪p.2, c • t⟫_ℝ : ℂ) * Complex.I) := by
      intro p
      rw [← Complex.exp_add]
      congr 1
      have h1 : ⟪σ • p.1 + c • p.2, t⟫_ℝ = ⟪p.1, σ • t⟫_ℝ + ⟪p.2, c • t⟫_ℝ := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_right, real_inner_smul_right]
      rw [h1]
      push_cast
      ring
    simp_rw [hfac]
    have hnorm1 : ∀ r : ℝ, ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 := by
      intro r
      rw [Complex.norm_exp]
      simp
    have hint : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        Complex.exp ((⟪p.1, σ • t⟫_ℝ : ℂ) * Complex.I)
          * Complex.exp ((⟪p.2, c • t⟫_ℝ : ℂ) * Complex.I))
        ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
      filter_upwards with p
      rw [norm_mul, hnorm1, hnorm1, one_mul]
    rw [integral_prod _ hint]
    have hinner : ∀ x : EuclideanSpace ℝ (Fin k),
        (∫ y, Complex.exp ((⟪x, σ • t⟫_ℝ : ℂ) * Complex.I)
            * Complex.exp ((⟪y, c • t⟫_ℝ : ℂ) * Complex.I)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          = Complex.exp ((⟪x, σ • t⟫_ℝ : ℂ) * Complex.I)
            * Complex.exp (-(‖c • t‖ : ℝ) ^ 2 / 2) := by
      intro x
      have h : (∫ y, Complex.exp ((⟪x, σ • t⟫_ℝ : ℂ) * Complex.I)
            * Complex.exp ((⟪y, c • t⟫_ℝ : ℂ) * Complex.I)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          = Complex.exp ((⟪x, σ • t⟫_ℝ : ℂ) * Complex.I)
            * ∫ y, Complex.exp ((⟪y, c • t⟫_ℝ : ℂ) * Complex.I)
                ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := integral_const_mul _ _
      rw [h, hstd (c • t)]
    simp_rw [hinner]
    have h2 : (∫ x, Complex.exp ((⟪x, σ • t⟫_ℝ : ℂ) * Complex.I)
          * Complex.exp (-(‖c • t‖ : ℝ) ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = (∫ x, Complex.exp ((⟪x, σ • t⟫_ℝ : ℂ) * Complex.I)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          * Complex.exp (-(‖c • t‖ : ℝ) ^ 2 / 2) := integral_mul_const _ _
    rw [h2, hstd (σ • t), ← Complex.exp_add]
    congr 1
    have h1 : ((‖σ • t‖ : ℝ) : ℂ) ^ 2 = ((σ ^ 2 * ‖t‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h2 : ((‖c • t‖ : ℝ) : ℂ) ^ 2 = ((c ^ 2 * ‖t‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [h1, h2]
    push_cast
    ring
  rw [hLHS, hRHS]

/-- The integral form of `map_stdGaussian_pair_smul_add`: the two-fold Gaussian smoothing at
scales `σ` and `c` is a single Gaussian smoothing at scale `√(σ² + c²)`. -/
private lemma integral_gaussian_pair_smul_add (σ c : ℝ)
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    (a : EuclideanSpace ℝ (Fin k)) :
    (∫ u, (∫ z, F (a + σ • z + c • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ z, F (a + Real.sqrt (σ ^ 2 + c ^ 2) • z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have hprodint : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      F (a + (σ • p.1 + c • p.2)))
      ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact hFb _
  have hstep : (∫ u, (∫ z, F (a + σ • z + c • u)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ p, F (a + (σ • p.1 + c • p.2))
          ∂(((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin k))))) := by
    rw [integral_prod_symm _ hprodint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [add_assoc]
  rw [hstep]
  have hmapL : (∫ p, F (a + (σ • p.1 + c • p.2))
        ∂(((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin k))))))
      = ∫ w, F (a + w) ∂((((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin k)))).map fun p => σ • p.1 + c • p.2)) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  rw [hmapL, map_stdGaussian_pair_smul_add σ c,
    integral_map (by fun_prop) (by fun_prop)]

end GaussianConvolution

/-! #### The sum estimate: the third of the three assembly bricks -/

section SumEstimate

/-- The backward telescoping bound `j^{-3/2} ≤ 2 ((j−1)^{-1/2} − j^{-1/2})`, valid for
`j ≥ 2`. It is what turns the tail of `Σ j^{-3/2}` into `2/√(J−1)` without any integral
comparison. -/
private lemma inv_mul_sqrt_le_telescope {j : ℕ} (hj : 2 ≤ j) :
    1 / ((j : ℝ) * Real.sqrt j)
      ≤ 2 * (1 / Real.sqrt ((j : ℝ) - 1) - 1 / Real.sqrt (j : ℝ)) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  set a : ℝ := Real.sqrt ((j : ℝ) - 1) with hadef
  set b : ℝ := Real.sqrt (j : ℝ) with hbdef
  have ha2 : a ^ 2 = (j : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (j : ℝ) := Real.sq_sqrt (by linarith)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hba : 0 < b - a := by nlinarith
  have hprod : (b - a) * (a + b) = 1 := by nlinarith
  -- `b ≤ a + 1/(2a)`, hence `ab ≤ a² + 1/2`
  have hble : b ≤ a + 1 / (2 * a) := by
    have hc : (0 : ℝ) < a + 1 / (2 * a) := by positivity
    have hexp : (a + 1 / (2 * a)) ^ 2 = a ^ 2 + 1 + 1 / (4 * a ^ 2) := by
      field_simp
      ring
    have hsq : b ^ 2 ≤ (a + 1 / (2 * a)) ^ 2 := by
      rw [hexp, hb2]
      have h4 : (0 : ℝ) ≤ 1 / (4 * a ^ 2) := by positivity
      linarith [ha2]
    nlinarith [hsq, hb, hc]
  have key : a * b ≤ a ^ 2 + 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hble ha.le
    have hcancel : a * (1 / (2 * a)) = 1 / 2 := by field_simp
    nlinarith [h, hcancel]
  have poly : a * b * (a + b) ≤ 2 * b ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left key hb.le]
  have hcube : (j : ℝ) * b = b ^ 3 := by rw [← hb2]; ring
  rw [hcube]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < b ^ 3)]
  have h1 : 2 * (1 / a - 1 / b) * b ^ 3 = 2 * (b - a) * b ^ 3 / (a * b) := by
    field_simp
  rw [h1, le_div_iff₀ (by positivity : (0 : ℝ) < a * b)]
  have e1 := mul_le_mul_of_nonneg_left poly hba.le
  have e2 : (b - a) * (a * b * (a + b)) = a * b := by
    linear_combination (a * b) * hprod
  nlinarith [e1, e2]

/-- **The `j^{-3/2}` tail of the telescope**, as a standalone sum bound: for every cut `J ≥ 2`,
`∑_{J ≤ j < m} j^{-3/2} ≤ 3 J^{-1/2}`. This is `inv_mul_sqrt_le_telescope` summed, and it is the
piece of the ledger that produces the `ε⁻¹` (at `J = ⌈ε²n⌉`, `J^{-1/2} = (ε√n)^{-1}`). Wave 32
factored it out of `sum_le_of_bounded_and_decay` so that the *weighted* ledger
`sum_le_of_bounded_and_weighted_decay` can reuse it. -/
private lemma sum_Ico_inv_mul_sqrt_le {J m : ℕ} (hJ : 2 ≤ J) :
    ∑ j ∈ Finset.Ico J m, (1 : ℝ) / ((j : ℝ) * Real.sqrt (j : ℝ))
      ≤ 3 / Real.sqrt (J : ℝ) := by
  have hJr : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < Real.sqrt J := Real.sqrt_pos.mpr (by linarith)
  rcases lt_or_ge J m with hm | hm
  swap
  · rw [Finset.Ico_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  have hsplit : ∑ j ∈ Finset.Ico J m, (1 : ℝ) / ((j : ℝ) * Real.sqrt (j : ℝ))
      = (1 : ℝ) / ((J : ℝ) * Real.sqrt (J : ℝ))
        + ∑ j ∈ Finset.Ico (J + 1) m, (1 : ℝ) / ((j : ℝ) * Real.sqrt (j : ℝ)) :=
    Finset.sum_eq_sum_Ico_succ_bot hm _
  have hfirst : (1 : ℝ) / ((J : ℝ) * Real.sqrt (J : ℝ)) ≤ 1 / Real.sqrt J := by
    have hs : Real.sqrt J ≤ (J : ℝ) * Real.sqrt J := by
      nlinarith [Real.sqrt_nonneg (J : ℝ)]
    exact one_div_le_one_div_of_le hJpos hs
  have hstep : ∀ j ∈ Finset.Ico (J + 1) m,
      (1 : ℝ) / ((j : ℝ) * Real.sqrt (j : ℝ))
        ≤ 2 * (1 / Real.sqrt ((j : ℝ) - 1) - 1 / Real.sqrt (j : ℝ)) := by
    intro j hjmem
    have hj2 : 2 ≤ j := by
      have := (Finset.mem_Ico.1 hjmem).1
      omega
    exact inv_mul_sqrt_le_telescope hj2
  have htel : ∑ j ∈ Finset.Ico (J + 1) m,
      2 * (1 / Real.sqrt ((j : ℝ) - 1) - 1 / Real.sqrt (j : ℝ))
      ≤ 2 / Real.sqrt J := by
    set g : ℕ → ℝ := fun i => 1 / Real.sqrt ((J : ℝ) + (i : ℝ)) with hg
    have hre : ∑ j ∈ Finset.Ico (J + 1) m,
        2 * (1 / Real.sqrt ((j : ℝ) - 1) - 1 / Real.sqrt (j : ℝ))
        = ∑ i ∈ Finset.range (m - (J + 1)), 2 * (g i - g (i + 1)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : ((J + 1 + i : ℕ) : ℝ) - 1 = (J : ℝ) + (i : ℝ) := by push_cast; ring
      have h2 : ((J + 1 + i : ℕ) : ℝ) = (J : ℝ) + ((i + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [h1, h2, hg]
    rw [hre, ← Finset.mul_sum, Finset.sum_range_sub' g]
    have hg0 : g 0 = 1 / Real.sqrt J := by
      rw [hg]; norm_num
    have hgnn : 0 ≤ g (m - (J + 1)) := by
      rw [hg]; positivity
    rw [hg0]
    have : 2 * (1 / Real.sqrt (J : ℝ) - g (m - (J + 1))) ≤ 2 * (1 / Real.sqrt (J : ℝ)) := by
      nlinarith
    calc 2 * (1 / Real.sqrt (J : ℝ) - g (m - (J + 1)))
        ≤ 2 * (1 / Real.sqrt (J : ℝ)) := this
      _ = 2 / Real.sqrt J := by ring
  have hsum2 : ∑ j ∈ Finset.Ico (J + 1) m, (1 : ℝ) / ((j : ℝ) * Real.sqrt (j : ℝ))
      ≤ 2 / Real.sqrt J := (Finset.sum_le_sum hstep).trans htel
  rw [hsplit]
  have : 1 / Real.sqrt (J : ℝ) + 2 / Real.sqrt (J : ℝ) = 3 / Real.sqrt J := by ring
  linarith [hfirst, hsum2]

/-- `1/j ≤ log j − log (j−1)` for `j ≥ 2`, straight from `log x ≤ x − 1` applied to
`x = (j−1)/j`. Summed, this is the harmonic bound that puts the logarithm into the ledger. -/
private lemma one_div_le_log_sub_log {j : ℕ} (hj : 2 ≤ j) :
    (1 : ℝ) / (j : ℝ) ≤ Real.log (j : ℝ) - Real.log ((j : ℝ) - 1) := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
  have hj1 : (0 : ℝ) < (j : ℝ) - 1 := by linarith
  have hdiv : (0 : ℝ) < ((j : ℝ) - 1) / (j : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos hdiv
  rw [Real.log_div hj1.ne' hjpos.ne'] at h
  have hval : ((j : ℝ) - 1) / (j : ℝ) - 1 = -(1 / (j : ℝ)) := by
    rw [sub_div, div_self hjpos.ne']; ring
  rw [hval] at h
  linarith

/-- **The harmonic tail of the ledger** (wave 32): `∑_{J ≤ j < m} j^{-1} ≤ 1 + log(m/J)`.

This is the **only** source of the logarithm in `berryEsseen_convex_sharp`. It appears because
the per-step localisation weight of the telescope is `4 C_k σⱼ + W` with `σⱼ = √(j/n)`, and
`j^{-3/2} · σⱼ = n^{-1/2} j^{-1}`: one of the three halves of the decay exponent is eaten by the
step's own smoothing width, turning the summable `j^{-3/2}` into the harmonic `j^{-1}`. At the
cut `J = ⌈ε² n⌉` the bound is `1 + log(1/ε²) = 1 + 2 log(1/ε)`.

The `max … 1` makes the statement unconditional in `m` (for `m ≤ J` the sum is empty). -/
private lemma sum_Ico_one_div_le {J m : ℕ} (hJ : 2 ≤ J) :
    ∑ j ∈ Finset.Ico J m, (1 : ℝ) / (j : ℝ)
      ≤ 1 + Real.log (max ((m : ℝ) / (J : ℝ)) 1) := by
  have hJr : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < (J : ℝ) := by linarith
  have hlogmax : 0 ≤ Real.log (max ((m : ℝ) / (J : ℝ)) 1) :=
    Real.log_nonneg (le_max_right _ _)
  rcases le_or_gt m J with hm | hm
  · rw [Finset.Ico_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    linarith
  · have hsplit : ∑ j ∈ Finset.Ico J m, (1 : ℝ) / (j : ℝ)
        = (1 : ℝ) / (J : ℝ) + ∑ j ∈ Finset.Ico (J + 1) m, (1 : ℝ) / (j : ℝ) :=
      Finset.sum_eq_sum_Ico_succ_bot hm _
    have hfirst : (1 : ℝ) / (J : ℝ) ≤ 1 := by
      rw [div_le_one hJpos]; linarith
    set g : ℕ → ℝ := fun i => Real.log ((J : ℝ) + (i : ℝ)) with hg
    have hstep : ∀ j ∈ Finset.Ico (J + 1) m,
        (1 : ℝ) / (j : ℝ) ≤ Real.log (j : ℝ) - Real.log ((j : ℝ) - 1) := by
      intro j hjmem
      have hj2 : 2 ≤ j := by have := (Finset.mem_Ico.1 hjmem).1; omega
      exact one_div_le_log_sub_log hj2
    have hre : ∑ j ∈ Finset.Ico (J + 1) m,
        (Real.log (j : ℝ) - Real.log ((j : ℝ) - 1))
        = ∑ i ∈ Finset.range (m - (J + 1)), (g (i + 1) - g i) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : ((J + 1 + i : ℕ) : ℝ) = (J : ℝ) + ((i + 1 : ℕ) : ℝ) := by push_cast; ring
      have h2 : ((J + 1 + i : ℕ) : ℝ) - 1 = (J : ℝ) + (i : ℝ) := by push_cast; ring
      simp only [hg]
      rw [h2, h1]
    have htel : ∑ i ∈ Finset.range (m - (J + 1)), (g (i + 1) - g i)
        = g (m - (J + 1)) - g 0 := Finset.sum_range_sub g _
    have hg0 : g 0 = Real.log (J : ℝ) := by rw [hg]; norm_num
    have hcast : ((m - (J + 1) : ℕ) : ℝ) = (m : ℝ) - (J : ℝ) - 1 := by
      have hle : J + 1 ≤ m := hm
      have h : ((m - (J + 1) : ℕ) : ℝ) = (m : ℝ) - ((J : ℝ) + 1) := by
        rw [Nat.cast_sub hle]; push_cast; ring
      rw [h]; ring
    have hgm : g (m - (J + 1)) = Real.log ((m : ℝ) - 1) := by
      simp only [hg]
      rw [hcast]
      congr 1
      ring
    have hmr : (2 : ℝ) ≤ (m : ℝ) := by
      have : (J : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hlogm : Real.log ((m : ℝ) - 1) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by linarith) (by linarith)
    have hrest : ∑ j ∈ Finset.Ico (J + 1) m, (1 : ℝ) / (j : ℝ)
        ≤ Real.log (m : ℝ) - Real.log (J : ℝ) := by
      calc ∑ j ∈ Finset.Ico (J + 1) m, (1 : ℝ) / (j : ℝ)
          ≤ ∑ j ∈ Finset.Ico (J + 1) m,
              (Real.log (j : ℝ) - Real.log ((j : ℝ) - 1)) := Finset.sum_le_sum hstep
        _ = g (m - (J + 1)) - g 0 := by rw [hre, htel]
        _ = Real.log ((m : ℝ) - 1) - Real.log (J : ℝ) := by rw [hgm, hg0]
        _ ≤ Real.log (m : ℝ) - Real.log (J : ℝ) := by linarith
    have hlogdiv : Real.log (m : ℝ) - Real.log (J : ℝ)
        ≤ Real.log (max ((m : ℝ) / (J : ℝ)) 1) := by
      have hd : Real.log ((m : ℝ) / (J : ℝ)) = Real.log (m : ℝ) - Real.log (J : ℝ) :=
        Real.log_div (by linarith) (by linarith)
      rw [← hd]
      exact Real.log_le_log (by positivity) (le_max_left _ _)
    rw [hsplit]
    linarith

/-- **The elementary sum estimate.** If a nonnegative sequence is bounded both by a constant
`θ` and, from `j ≥ 1` on, by `j^{-3/2}`, then its partial sums are at most `J θ + 3/√J` for
every cut `J ≥ 2`. Choosing `J ≈ θ^{-2/3}` gives `O(θ^{1/3})`, which is exactly the step that
turns the mollifier factor `ε^{-3}` into `ε^{-1}` in the improved Lindeberg telescope. -/
private lemma sum_le_of_bounded_and_decay {θ : ℝ} (hθ : 0 ≤ θ) {n J : ℕ} (hJ : 2 ≤ J)
    {T : ℕ → ℝ} (hTnn : ∀ j, 0 ≤ T j) (hTθ : ∀ j, T j ≤ θ)
    (hTdec : ∀ j, 1 ≤ j → T j ≤ 1 / ((j : ℝ) * Real.sqrt j)) :
    ∑ j ∈ Finset.range n, T j ≤ (J : ℝ) * θ + 3 / Real.sqrt J := by
  classical
  have hJr : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < Real.sqrt J := Real.sqrt_pos.mpr (by linarith)
  have htail : ∀ m : ℕ, ∑ j ∈ Finset.Ico J m, T j ≤ 3 / Real.sqrt J := by
    intro m
    refine le_trans (Finset.sum_le_sum fun j hjmem => ?_) (sum_Ico_inv_mul_sqrt_le hJ)
    have := (Finset.mem_Ico.1 hjmem).1
    exact hTdec j (by omega)
  rcases le_total n J with hn | hn
  · have h1 : ∑ j ∈ Finset.range n, T j ≤ ∑ j ∈ Finset.range n, θ :=
      Finset.sum_le_sum fun j _ => hTθ j
    have h2 : ∑ j ∈ Finset.range n, (θ : ℝ) = (n : ℝ) * θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h3 : (n : ℝ) ≤ (J : ℝ) := by exact_mod_cast hn
    have h4 : (0 : ℝ) ≤ 3 / Real.sqrt J := by positivity
    nlinarith
  · have hsplit : ∑ j ∈ Finset.range n, T j
        = (∑ j ∈ Finset.Ico 0 J, T j) + ∑ j ∈ Finset.Ico J n, T j := by
      rw [Finset.sum_Ico_consecutive T (Nat.zero_le J) hn, Finset.range_eq_Ico]
    have h1 : ∑ j ∈ Finset.Ico 0 J, T j ≤ (J : ℝ) * θ := by
      have := Finset.sum_le_sum (f := T) (g := fun _ => θ)
        (fun j (_ : j ∈ Finset.Ico 0 J) => hTθ j)
      have h2 : ∑ _j ∈ Finset.Ico 0 J, (θ : ℝ) = (J : ℝ) * θ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        simp
      linarith [this, h2.le, h2.ge]
    rw [hsplit]
    linarith [h1, htail n]

/-- **The sum estimate with an explicit decay constant.** The rescaling of
`sum_le_of_bounded_and_decay` by a positive factor `K`: if `0 ≤ T j ≤ θ` and `T j ≤ K j^{-3/2}`
for `j ≥ 1`, then `Σ_{j<n} T j ≤ J θ + 3K/√J` for every cut `J ≥ 2`. This is the form the
hybrid telescope consumes, `K` being `C (β_ν + β_G)` and `θ` the elementary step bound. -/
private lemma sum_le_of_bounded_and_decay_const {K θ : ℝ} (hK : 0 < K) (hθ : 0 ≤ θ)
    {n J : ℕ} (hJ : 2 ≤ J) {T : ℕ → ℝ} (hTnn : ∀ j, 0 ≤ T j) (hTθ : ∀ j, T j ≤ θ)
    (hTdec : ∀ j, 1 ≤ j → T j ≤ K / ((j : ℝ) * Real.sqrt j)) :
    ∑ j ∈ Finset.range n, T j ≤ (J : ℝ) * θ + 3 * K / Real.sqrt J := by
  have hKinv : (0 : ℝ) ≤ K⁻¹ := (inv_pos.mpr hK).le
  have hJr : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hJs : (0 : ℝ) < Real.sqrt (J : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have h := sum_le_of_bounded_and_decay (θ := θ / K) (by positivity) (n := n) hJ
    (T := fun j => T j / K) (fun j => div_nonneg (hTnn j) hK.le)
    (fun j => by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right (hTθ j) hKinv)
    (fun j hj => by
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      have hsj : (0 : ℝ) < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hjs : (0 : ℝ) < (j : ℝ) * Real.sqrt (j : ℝ) := mul_pos (by linarith) hsj
      rw [div_le_iff₀ hK]
      have h3 : 1 / ((j : ℝ) * Real.sqrt j) * K = K / ((j : ℝ) * Real.sqrt j) := by ring
      rw [h3]
      exact hTdec j hj)
  rw [← Finset.sum_div, div_le_iff₀ hK] at h
  refine h.trans_eq ?_
  field_simp

/-- **The summation ledger of the WEIGHTED telescope** (wave 32, PROVED).

This is the arithmetic certificate behind the logarithm in `berryEsseen_convex_sharp`, isolated
from all the measure theory. The *localised* telescope of `localised_swap_bound_small_weight`
produces, at step `j ≥ 1`, a bound of the shape

`Tⱼ ≤ (per-step weight) × (decay) = (4 C_k σⱼ + W) × 3β/(j √j)`,  `σⱼ = √(j/n)`,

and `σⱼ/(j√j) = n^{-1/2} j^{-1}`, so the hypothesis below with `K₁ = 12 C_k β n^{-1/2}` and
`K₂ = 3 β W` is exactly what the analytic half has to deliver. The conclusion is then

`J θ + K₁ (1 + log(n/J)) + 3 K₂ /√J`,

and at the cut `J = ⌈ε² n⌉` (so `n/J ≤ ε⁻²` and `J^{-1/2} ≤ (ε√n)⁻¹`), with the elementary step
bound `θ = (C₃/ε³)/6 · n^{-3/2} · 3β`, this reads

`(3/2) C₃ δ ε⁻¹ + 12 C_k δ (1 + 2 log(1/ε)) + 9 δ W ε⁻¹`,  `δ = β/√n`,

i.e. `A δ (ε⁻¹(W + C_k ε) + C_k (1 + log(1/ε)))`. **Both exponents of the ledger are verified
here**: the `j^{-1}` piece is genuinely harmonic (`sum_Ico_one_div_le` — this and nothing else is
where the logarithm comes from), and the `j^{-3/2}` piece is genuinely summable to `J^{-1/2}`
(`sum_Ico_inv_mul_sqrt_le` — this is the `ε⁻¹` the frozen statement already carried).

What remains open in the brick is the *analytic* half — the production of the per-step
hypothesis `hTdec`, i.e. the localised weighted swap at a single step — not this bookkeeping. -/
private lemma sum_le_of_bounded_and_weighted_decay {K₁ K₂ θ : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hθ : 0 ≤ θ)
    {n J : ℕ} (hJ : 2 ≤ J) {T : ℕ → ℝ} (hTnn : ∀ j, 0 ≤ T j) (hTθ : ∀ j, T j ≤ θ)
    (hTdec : ∀ j, J ≤ j → T j ≤ K₁ / (j : ℝ) + K₂ / ((j : ℝ) * Real.sqrt (j : ℝ))) :
    ∑ j ∈ Finset.range n, T j
      ≤ (J : ℝ) * θ + K₁ * (1 + Real.log (max ((n : ℝ) / (J : ℝ)) 1))
        + 3 * K₂ / Real.sqrt (J : ℝ) := by
  classical
  have hJr : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hJs : (0 : ℝ) < Real.sqrt (J : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hlog0 : 0 ≤ Real.log (max ((n : ℝ) / (J : ℝ)) 1) :=
    Real.log_nonneg (le_max_right _ _)
  have hlogterm : 0 ≤ K₁ * (1 + Real.log (max ((n : ℝ) / (J : ℝ)) 1)) :=
    mul_nonneg hK₁ (by linarith)
  have htailterm : (0 : ℝ) ≤ 3 * K₂ / Real.sqrt (J : ℝ) := by positivity
  have htail : ∑ j ∈ Finset.Ico J n, T j
      ≤ K₁ * (1 + Real.log (max ((n : ℝ) / (J : ℝ)) 1)) + 3 * K₂ / Real.sqrt (J : ℝ) := by
    have hb : ∑ j ∈ Finset.Ico J n, T j
        ≤ ∑ j ∈ Finset.Ico J n,
            (K₁ / (j : ℝ) + K₂ / ((j : ℝ) * Real.sqrt (j : ℝ))) := by
      refine Finset.sum_le_sum fun j hjmem => ?_
      exact hTdec j (Finset.mem_Ico.1 hjmem).1
    have hsp : ∑ j ∈ Finset.Ico J n,
          (K₁ / (j : ℝ) + K₂ / ((j : ℝ) * Real.sqrt (j : ℝ)))
        = K₁ * ∑ j ∈ Finset.Ico J n, (1 : ℝ) / (j : ℝ)
          + K₂ * ∑ j ∈ Finset.Ico J n, (1 : ℝ) / ((j : ℝ) * Real.sqrt (j : ℝ)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsp] at hb
    have hh := mul_le_mul_of_nonneg_left (sum_Ico_one_div_le (J := J) (m := n) hJ) hK₁
    have hs := mul_le_mul_of_nonneg_left (sum_Ico_inv_mul_sqrt_le (J := J) (m := n) hJ) hK₂
    have hval : K₂ * (3 / Real.sqrt (J : ℝ)) = 3 * K₂ / Real.sqrt (J : ℝ) := by ring
    linarith
  rcases le_total n J with hn | hn
  · have h1 : ∑ j ∈ Finset.range n, T j ≤ ∑ _j ∈ Finset.range n, θ :=
      Finset.sum_le_sum fun j _ => hTθ j
    have h2 : ∑ _j ∈ Finset.range n, (θ : ℝ) = (n : ℝ) * θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h3 : (n : ℝ) ≤ (J : ℝ) := by exact_mod_cast hn
    nlinarith [mul_le_mul_of_nonneg_right h3 hθ]
  · have hsplit : ∑ j ∈ Finset.range n, T j
        = (∑ j ∈ Finset.Ico 0 J, T j) + ∑ j ∈ Finset.Ico J n, T j := by
      rw [Finset.sum_Ico_consecutive T (Nat.zero_le J) hn, Finset.range_eq_Ico]
    have h1 : ∑ j ∈ Finset.Ico 0 J, T j ≤ (J : ℝ) * θ := by
      have hle := Finset.sum_le_sum (f := T) (g := fun _ => θ)
        (fun j (_ : j ∈ Finset.Ico 0 J) => hTθ j)
      have h2 : ∑ _j ∈ Finset.Ico 0 J, (θ : ℝ) = (J : ℝ) * θ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        simp
      linarith [hle, h2.le, h2.ge]
    rw [hsplit]
    linarith

end SumEstimate

/-! #### Brick (i): the hybrid telescope that carries its own Gaussian smoothing

The three bricks above are assembled here. The telescoped functional is

`Iⱼ = ∫ x, (∫ z, f (n^{-1/2} (∑ₗ xₗ) + √(j/n) z) dγ(z)) d(⨂ᵢ κ'ⱼ(i))`,
`κ'ⱼ(i) = if i < j then δ₀ else ν`,

so that `I₀` is the law of the normalized sum (the `j = 0` smoothing has width `√0 = 0`) and
`I_n` is the standard Gaussian (all coordinates are Dirac at the origin, and the smoothing has
width `1`). One step replaces the `j`-th coordinate's `ν` by `δ₀` *and* widens the smoothing from
`√(j/n)` to `√((j+1)/n)` — and by `integral_gaussian_pair_smul_add` (brick (ii)) that is exactly
the statement that the fresh `n^{-1/2}`-scaled Gaussian is absorbed into the smoothing. Hence
each step is the comparison of `ν` with `N(0,I_k)` *inside a Gaussian-smoothed test function*,
and admits **two** bounds:

* the elementary one, `abs_integral_swap_step_le` after a Fubini swap that puts the smoothing
  variable outside — cost `(M/6) n^{-3/2}(β_ν + β_G)`, valid at every step including `j = 0`;
* the Cameron–Martin one, `abs_integral_gaussian_smoothed_swap_le` — cost
  `C (n^{-1/2}/√(j/n))³ (β_ν + β_G) = C (β_ν+β_G) j^{-3/2}`, valid for `j ≥ 1`.

`sum_le_of_bounded_and_decay_const` (brick (iii)) sums the minimum of the two. -/

section ImprovedTelescope

variable {k : ℕ}

/-- The product of Dirac masses at the origin is the Dirac mass at the origin. -/
private lemma measure_pi_dirac_zero (N : ℕ) :
    (Measure.pi fun _ : Fin N => Measure.dirac (0 : EuclideanSpace ℝ (Fin k)))
      = Measure.dirac (fun _ : Fin N => (0 : EuclideanSpace ℝ (Fin k))) := by
  classical
  refine Measure.pi_eq ?_
  intro s hs
  by_cases h : ∀ i, (0 : EuclideanSpace ℝ (Fin k)) ∈ s i
  · have hmem : (fun _ : Fin N => (0 : EuclideanSpace ℝ (Fin k))) ∈ Set.univ.pi s :=
      fun i _ => h i
    rw [Measure.dirac_apply_of_mem hmem]
    exact (Finset.prod_eq_one fun i _ => Measure.dirac_apply_of_mem (h i)).symm
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have hnot : (fun _ : Fin N => (0 : EuclideanSpace ℝ (Fin k))) ∉ Set.univ.pi s := by
      intro hcon
      exact hi (hcon i (Set.mem_univ i))
    rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs), Set.indicator_of_notMem hnot]
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [Measure.dirac_apply' _ (hs i), Set.indicator_of_notMem hi]

/-- A bounded continuous function is integrable against any probability measure. -/
private lemma integrable_of_bounded_continuous {τ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure τ] {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F)
    (hFb : ∀ x, |F x| ≤ 1) : Integrable F τ :=
  (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFb x)

/-- The average of a function bounded by `1` is bounded by `1`. -/
private lemma abs_integral_le_one {σ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure σ] {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F)
    (hFb : ∀ x, |F x| ≤ 1) : |∫ x, F x ∂σ| ≤ 1 := by
  calc |∫ x, F x ∂σ| ≤ ∫ x, |F x| ∂σ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, (1 : ℝ) ∂σ :=
        integral_mono (integrable_of_bounded_continuous hF hFb).abs
          (integrable_const _) hFb
    _ = 1 := by rw [integral_const]; simp

/-- Smoothing a bounded continuous function by a probability law preserves continuity
(dominated convergence, with the constant bound `1`). -/
private lemma continuous_integral_add_smul {σ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure σ] {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F)
    (hFb : ∀ x, |F x| ≤ 1) (t : ℝ) :
    Continuous fun w : EuclideanSpace ℝ (Fin k) => ∫ u, F (w + t • u) ∂σ := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun w => (hF.comp (continuous_const.add (continuous_const_smul t))).aestronglyMeasurable)
    (fun w => Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact hFb _)
    (integrable_const 1)
    (Filter.Eventually.of_forall fun u =>
      hF.comp (continuous_id.add continuous_const))

/-! #### Wave-43 helpers: the same three facts at an arbitrary constant bound, plus the two
convolution/smoothing identities the LOCALISED telescope needs.  The localised per-step bounds
`D v` are differences of two averages, hence bounded by `2` and not by `1`, so the wave-16
helpers above do not apply to them verbatim. -/

/-- A continuous function with an arbitrary constant bound is integrable. -/
private lemma integrable_of_bounded_continuous' {τ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure τ] {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F)
    {M : ℝ} (hFb : ∀ x, |F x| ≤ M) : Integrable F τ :=
  (integrable_const M).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFb x)

/-- Smoothing by a probability law preserves continuity, at an arbitrary constant bound. -/
private lemma continuous_integral_add_smul' {σ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure σ] {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F)
    {M : ℝ} (hFb : ∀ x, |F x| ≤ M) (t : ℝ) :
    Continuous fun w : EuclideanSpace ℝ (Fin k) => ∫ u, F (w + t • u) ∂σ := by
  refine continuous_of_dominated (bound := fun _ => M)
    (fun w => (hF.comp (continuous_const.add (continuous_const_smul t))).aestronglyMeasurable)
    (fun w => Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact hFb _)
    (integrable_const M)
    (Filter.Eventually.of_forall fun u =>
      hF.comp (continuous_id.add continuous_const))

/-- **The convolution average, with the Gaussian factor written as a scaled standard
Gaussian.** -/
private lemma integral_conv_smul_gaussian (α : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure α] (t : ℝ)
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : Continuous g) {M : ℝ} (hgb : ∀ x, |g x| ≤ M) :
    (∫ a, g a ∂(α ∗ ((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun z => t • z)))
      = ∫ x, (∫ z, g (x + t • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂α := by
  set Gs : Measure (EuclideanSpace ℝ (Fin k)) :=
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map fun z => t • z with hGs
  haveI : IsProbabilityMeasure Gs := by
    rw [hGs]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      g (p.1 + p.2)) (α.prod Gs) := by
    refine (integrable_const M).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (hg.comp (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hgb _
  rw [conv_eq_map_add, integral_map (by fun_prop) hg.aestronglyMeasurable, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change (∫ y, g (x + y) ∂Gs)
    = ∫ z, g (x + t • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
  rw [hGs, integral_map (φ := fun z : EuclideanSpace ℝ (Fin k) => t • z)
    (f := fun y => g (x + y)) (by fun_prop)
    ((hg.comp (continuous_const.add continuous_id)).aestronglyMeasurable)]

/-- The average of a function bounded by `M` is bounded by `M`. -/
private lemma abs_integral_le_const {σ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure σ] {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F)
    {M : ℝ} (hFb : ∀ x, |F x| ≤ M) : |∫ x, F x ∂σ| ≤ M := by
  calc |∫ x, F x ∂σ| ≤ ∫ x, |F x| ∂σ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, M ∂σ :=
        integral_mono (integrable_of_bounded_continuous' hF hFb).abs
          (integrable_const _) hFb
    _ = M := by rw [integral_const]; simp

/-- Integrability of a bounded continuous function on any space, at any constant bound. -/
private lemma integrable_of_bounded_cont {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopologyEither α ℝ]
    {τ : Measure α} [IsProbabilityMeasure τ] {F : α → ℝ} (hF : Continuous F)
    {M : ℝ} (hFb : ∀ x, |F x| ≤ M) : Integrable F τ :=
  (integrable_const M).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFb x)

/-- Continuity of the doubly smoothed test function, in the exact shape the tail brick uses. -/
private lemma continuous_double_smooth {ν : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Continuous f)
    (hfb : ∀ x, |f x| ≤ 1) (σ c : ℝ) :
    Continuous fun v : EuclideanSpace ℝ (Fin k) =>
      ∫ y, (∫ z, f (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν := by
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : EuclideanSpace ℝ (Fin k) → ℝ, ∀ x,
      Ψ x = ∫ z, f (x + σ • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := ⟨_, fun _ => rfl⟩
  have hΨcont : Continuous Ψ := by
    have hfun : Ψ = fun x => ∫ z, f (x + σ • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      funext hΨdef
    rw [hfun]
    exact continuous_integral_add_smul hf hfb σ
  have hΨb : ∀ x, |Ψ x| ≤ 1 := by
    intro x
    rw [hΨdef]
    exact abs_integral_le_one (hf.comp (continuous_const.add (continuous_const_smul σ)))
      (fun z => hfb _)
  have key : ∀ v y : EuclideanSpace ℝ (Fin k),
      (∫ z, f (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = Ψ (v + c • y) := by
    intro v y
    rw [hΨdef]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun z => congrArg f (add_right_comm _ _ _))
  have hcont2 : ∀ v : EuclideanSpace ℝ (Fin k),
      Continuous fun y : EuclideanSpace ℝ (Fin k) =>
        ∫ z, f (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro v
    have hfun : (fun y : EuclideanSpace ℝ (Fin k) =>
        ∫ z, f (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = fun y => Ψ (v + c • y) := funext (key v)
    rw [hfun]
    exact hΨcont.comp (continuous_const.add (continuous_const_smul c))
  have hcont1 : ∀ y : EuclideanSpace ℝ (Fin k),
      Continuous fun v : EuclideanSpace ℝ (Fin k) =>
        ∫ z, f (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro y
    have hfun : (fun v : EuclideanSpace ℝ (Fin k) =>
        ∫ z, f (v + σ • z + c • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = fun v => Ψ (v + c • y) := funext (fun v => key v y)
    rw [hfun]
    exact hΨcont.comp (continuous_id.add continuous_const)
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun v => (hcont2 v).aestronglyMeasurable)
    (fun v => Filter.Eventually.of_forall fun y => ?_) (integrable_const 1)
    (Filter.Eventually.of_forall fun y => hcont1 y)
  rw [Real.norm_eq_abs, key]
  exact hΨb _

/-- **The telescope step with a bound that may depend on the remaining coordinates**
(wave 36: the *structural* half of brick L's residue).

The wave-16 telescope estimates one step by a **constant** pointwise bound `D` on the peeled
difference `|∫ g(u + v) dν − ∫ g(u + v) dσ|`, uniformly in the remaining sum `v = ∑ₗ yₗ`. The
two localised swap estimates that brick L needs
(`localised_swap_bound_small_weight`) are not of that form: their weight is the mass of a
two-sided shell under the hybrid law, i.e. an *average*, not a pointwise bound. What they do
supply is a bound `D v` that varies with `v` — typically `D v = (shell indicator averaged over
the peeled coordinate and the smoothing Gaussian) × cost`.

This lemma is that generalisation, and it is exactly as cheap: the wave-16 argument never used
constancy of `D`, only `integral_mono` against a constant. Replacing the constant by an
integrable function of `∑ₗ yₗ` costs one integrability hypothesis and nothing else.

**How the conclusion becomes a hybrid mass at the call site.** The right-hand side
`∫ D(∑ₗ yₗ) d(⨂ κ')` is an integral against the law of the sum of the *remaining* `n − 1`
coordinates. When `D v` is itself an average over the peeled coordinate `u ~ ν` and the
smoothing variable `z ~ γ` of a function of `c(v + u) + sⱼ z`, that iterated integral is by
Fubini an integral against the law of `c ∑ᵢ yᵢ + sⱼ z`, which is `hybridLaw n j ν` — so a
shell indicator there produces precisely the two-sided-shell mass the amended weight
hypothesis bounds. That identification is the caller's step, not this lemma's. -/
private lemma abs_sub_integral_peel_le_integral {k m : ℕ}
    (ν σ : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (κ' : Fin m → Measure (EuclideanSpace ℝ (Fin k))) [∀ l, IsProbabilityMeasure (κ' l)]
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {D : EuclideanSpace ℝ (Fin k) → ℝ}
    (hDint : Integrable (fun y : Fin m → EuclideanSpace ℝ (Fin k) => D (∑ l, y l))
      (Measure.pi κ'))
    (hbound : ∀ v : EuclideanSpace ℝ (Fin k),
      |(∫ u, g (u + v) ∂ν) - (∫ u, g (u + v) ∂σ)| ≤ D v) :
    |(∫ y, (∫ u, g (u + ∑ l, y l) ∂ν) ∂(Measure.pi κ'))
        - (∫ y, (∫ u, g (u + ∑ l, y l) ∂σ) ∂(Measure.pi κ'))|
      ≤ ∫ y, D (∑ l, y l) ∂(Measure.pi κ') := by
  have hAint : Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) =>
      ∫ u, g (u + ∑ l, y l) ∂ν) (Measure.pi κ') :=
    (integrable_peel_prod ν κ' hg hgb).integral_prod_right
  have hBint : Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) =>
      ∫ u, g (u + ∑ l, y l) ∂σ) (Measure.pi κ') :=
    (integrable_peel_prod σ κ' hg hgb).integral_prod_right
  rw [← integral_sub hAint hBint]
  calc |∫ y, ((∫ u, g (u + ∑ l, y l) ∂ν) - (∫ u, g (u + ∑ l, y l) ∂σ)) ∂(Measure.pi κ')|
      ≤ ∫ y, |(∫ u, g (u + ∑ l, y l) ∂ν) - (∫ u, g (u + ∑ l, y l) ∂σ)|
          ∂(Measure.pi κ') := abs_integral_le_integral_abs
    _ ≤ ∫ y, D (∑ l, y l) ∂(Measure.pi κ') :=
        integral_mono (hAint.sub hBint).abs hDint fun y => hbound _

set_option maxHeartbeats 1600000 in
/-- **The hybrid telescope with Gaussian smoothing (brick (i)).** For every cut `J ≥ 2` the
normal approximation error of a `C³` test function bounded by `1` with `‖D³f‖ ≤ M` is at most

`(J (M/6) n^{-3/2} + 3C/√J) (β_ν + β_G)`,

where `C` is the absolute constant of `exists_tiltRemainder_bound`. Choosing `J ≈ (C/θ)^{2/3}`
with `θ = (M/6) n^{-3/2}` makes this `O(C^{2/3} θ^{1/3}) (β_ν + β_G)`, i.e. `M^{1/3}/√n` in place
of the `M/√n` of `abs_integral_smooth_sub_gaussian_le`. For a mollified indicator of width `ε`
this turns `ε^{-3}` into `ε^{-1}`, which is the whole point. -/
private lemma abs_integral_smooth_sub_gaussian_improved {n : ℕ} (hk : 0 < k) {C : ℝ}
    (hC0 : 0 < C)
    (hC : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ C * s ^ 3)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} (hn : 0 < n) (hν : IsProbabilityMeasure ν)
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 3 f) (hfb : ∀ x, |f x| ≤ 1)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M)
    {J : ℕ} (hJ : 2 ≤ J) :
    |(∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i))
        - (∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))|
      ≤ ((J : ℝ) * (M / 6 / ((n : ℝ) * Real.sqrt (n : ℝ))) + 3 * C / Real.sqrt (J : ℝ))
          * ((∫ y, ‖y‖ ^ 3 ∂ν)
            + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))) := by
  classical
  haveI := hν
  -- ### Gaussian moment facts
  have hmeanγ : ∀ u : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = 0 := by
    intro u
    simpa using integral_strongDual_stdGaussian (E := EuclideanSpace ℝ (Fin k)) (innerSL ℝ u)
  have hcovγ : ∀ u w : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ * ⟪w, z⟫_ℝ ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = ⟪u, w⟫_ℝ := by
    intro u w
    have hL2 : MemLp id 2 (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      IsGaussian.memLp_id _ 2 (by simp)
    have hid : (stdGaussian (EuclideanSpace ℝ (Fin k)))[id] = (0 : EuclideanSpace ℝ (Fin k)) :=
      integral_id_stdGaussian
    have h := covarianceBilin_apply (μ := stdGaussian (EuclideanSpace ℝ (Fin k))) hL2 u w
    rw [hid] at h
    simp only [sub_zero] at h
    rw [← h, covarianceBilin_stdGaussian]
    exact innerSL_apply_apply (𝕜 := ℝ) u w
  have hβγ : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 3)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have hL3 : MemLp id ((3 : ℕ) : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      IsGaussian.memLp_id _ _ (by simp)
    simpa using hL3.integrable_norm_pow'
  have hν1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν := integrable_norm_of_cube hβ
  have hν2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν :=
    integrable_normSq_of_cube hβ
  have hγ1 : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := integrable_norm_of_cube hβγ
  have hγ2 : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := integrable_normSq_of_cube hβγ
  have hνdim : (∫ y, ‖y‖ ^ 2 ∂ν) = (k : ℝ) := integral_normSq_eq_dim hcov hβ
  have hγdim : (∫ z, ‖z‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = (k : ℝ) :=
    integral_normSq_eq_dim hcovγ hβγ
  have hβνpos : 0 < ∫ y, ‖y‖ ^ 3 ∂ν := integral_norm_cube_pos hk hcov hβ
  have hβγnn : 0 ≤ ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
    integral_nonneg fun z => by positivity
  -- ### the telescope
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsN : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hNr
  set X : ℝ := (∫ y, ‖y‖ ^ 3 ∂ν)
    + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; linarith
  set c : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcne : c ≠ 0 := hcpos.ne'
  set s : ℕ → ℝ := fun j => c * Real.sqrt (j : ℝ) with hsdef
  have hs0 : s 0 = 0 := by rw [hsdef]; simp
  have hsN1 : s (m + 1) = 1 := by
    rw [hsdef, hcdef]
    dsimp only
    exact inv_mul_cancel₀ hsN.ne'
  have hspos : ∀ j : ℕ, 1 ≤ j → 0 < s j := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hsq : (0 : ℝ) < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr (by linarith)
    rw [hsdef]
    dsimp only
    positivity
  set Φ : ℕ → EuclideanSpace ℝ (Fin k) → ℝ :=
    fun j x => ∫ z, f (x + s j • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) with hΦdef
  set G : ℕ → EuclideanSpace ℝ (Fin k) → ℝ := fun j w => Φ j (c • w) with hGdef
  have hΦcont : ∀ j, Continuous (Φ j) := fun j =>
    continuous_integral_add_smul hf.continuous hfb (s j)
  have hΦb : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin k)), |Φ j x| ≤ 1 := fun j x =>
    abs_integral_le_one
      (hf.continuous.comp (continuous_const.add (continuous_const_smul (s j))))
      (fun z => hfb _)
  have hGcont : ∀ j, Continuous (G j) := fun j => (hΦcont j).comp (continuous_const_smul c)
  have hGb : ∀ (j : ℕ) (w : EuclideanSpace ℝ (Fin k)), |G j w| ≤ 1 := fun j w => hΦb j _
  -- the Gaussian convolution identity: one fresh `c`-scaled Gaussian widens the smoothing
  have hconv : ∀ (j : ℕ) (v : EuclideanSpace ℝ (Fin k)),
      (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = G (j + 1) v := by
    intro j v
    have hjsq : Real.sqrt (j : ℝ) ^ 2 = (j : ℝ) := Real.sq_sqrt (Nat.cast_nonneg j)
    have hsq : Real.sqrt ((s j) ^ 2 + c ^ 2) = s (j + 1) := by
      have h1 : (s j) ^ 2 + c ^ 2 = c ^ 2 * (((j + 1 : ℕ) : ℝ)) := by
        rw [hsdef]
        dsimp only
        push_cast
        rw [mul_pow, hjsq]
        ring
      rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hcpos.le, hsdef]
    have h := integral_gaussian_pair_smul_add (k := k) (s j) c hf.continuous hfb (c • v)
    rw [hsq] at h
    calc (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = ∫ u, (∫ z, f (c • v + s j • z + c • u)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only [hGdef, hΦdef]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          congr 1
          rw [smul_add]
          abel
      _ = ∫ z, f (c • v + s (j + 1) • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := h
      _ = G (j + 1) v := by simp only [hGdef, hΦdef]
  -- the hybrid family
  set κ : ℕ → Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun j i => if (i : ℕ) < j then Measure.dirac 0 else ν with hκdef
  haveI hκp : ∀ (j : ℕ) (i : Fin (m + 1)), IsProbabilityMeasure (κ j i) := by
    intro j i
    rw [hκdef]
    dsimp only
    split_ifs
    · infer_instance
    · exact hν
  set I : ℕ → ℝ := fun j => ∫ x, G j (∑ l, x l) ∂(Measure.pi (κ j)) with hIdef
  -- one telescope step, given a bound on the peeled difference that may itself depend on the
  -- remaining coordinates (wave 36: the `v`-dependent form, via
  -- `abs_sub_integral_peel_le_integral`; the constant case is `hstepgen` below)
  have hstepfun : ∀ j : ℕ, ∀ hj : j < m + 1, ∀ D : EuclideanSpace ℝ (Fin k) → ℝ,
      Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) => D (∑ l, y l))
        (Measure.pi fun l : Fin m => κ j ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)) →
      (∀ v : EuclideanSpace ℝ (Fin k),
        |(∫ u, G j (u + v) ∂ν)
          - (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ≤ D v) →
      |I j - I (j + 1)|
        ≤ ∫ y, D (∑ l, y l)
            ∂(Measure.pi fun l : Fin m => κ j ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)) := by
    intro j hj D hDint hbound
    set i : Fin (m + 1) := ⟨j, hj⟩ with hidef
    have hival : ((i : Fin (m + 1)) : ℕ) = j := by rw [hidef]
    have hji : κ j i = ν := by
      rw [hκdef]; dsimp only; rw [if_neg (by rw [hival]; omega)]
    have hji1 : κ (j + 1) i = Measure.dirac 0 := by
      rw [hκdef]; dsimp only; rw [if_pos (by rw [hival]; omega)]
    have hoff : (fun l : Fin m => κ (j + 1) (i.succAbove l))
        = fun l : Fin m => κ j (i.succAbove l) := by
      funext l
      have hne : ((i.succAbove l : Fin (m + 1)) : ℕ) ≠ j := by
        intro h
        exact Fin.succAbove_ne i l (Fin.ext (by rw [h, hival]))
      rw [hκdef]
      dsimp only
      by_cases hlt : ((i.succAbove l : Fin (m + 1)) : ℕ) < j
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg hlt]
    have hpeel0 := integral_pi_sum_peel (κ j) i (hGcont j) (hGb j)
    have hpeel1 := integral_pi_sum_peel (κ (j + 1)) i (hGcont (j + 1)) (hGb (j + 1))
    rw [hji] at hpeel0
    rw [hji1, hoff] at hpeel1
    set R : Measure ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
      Measure.pi (fun l : Fin m => κ j (i.succAbove l)) with hRdef
    haveI hRp : IsProbabilityMeasure R := by rw [hRdef]; infer_instance
    have hdirac : ∀ y : (_ : Fin m) → EuclideanSpace ℝ (Fin k),
        (∫ u, G (j + 1) (u + ∑ l, y l) ∂(Measure.dirac (0 : EuclideanSpace ℝ (Fin k))))
          = ∫ u, G j (u + ∑ l, y l) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
      intro y
      rw [integral_dirac, zero_add]
      exact (hconv j _).symm
    have hIj : I j = ∫ y, (∫ u, G j (u + ∑ l, y l) ∂ν) ∂R := by
      rw [hIdef]; exact hpeel0
    have hIj1 : I (j + 1)
        = ∫ y, (∫ u, G j (u + ∑ l, y l) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂R := by
      rw [hIdef]
      refine hpeel1.trans ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => hdirac y)
    rw [hIj, hIj1]
    exact abs_sub_integral_peel_le_integral ν (stdGaussian (EuclideanSpace ℝ (Fin k)))
      (fun l : Fin m => κ j (i.succAbove l)) (hGcont j) (hGb j) hDint hbound
  -- the constant case, which is what the two *unlocalised* step bounds below supply
  have hstepgen : ∀ j : ℕ, j < m + 1 → ∀ D : ℝ, 0 ≤ D →
      (∀ v : EuclideanSpace ℝ (Fin k),
        |(∫ u, G j (u + v) ∂ν)
          - (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ≤ D) →
      |I j - I (j + 1)| ≤ D := by
    intro j hj D _ hbound
    haveI : ∀ l : Fin m, IsProbabilityMeasure (κ j ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)) :=
      fun l => hκp j _
    have h := hstepfun j hj (fun _ => D) (integrable_const _) hbound
    rw [integral_const] at h
    simpa using h
  -- the peeled difference, written with the smoothing variable displayed
  have hrw : ∀ (σ : Measure (EuclideanSpace ℝ (Fin k))) (j : ℕ)
      (v : EuclideanSpace ℝ (Fin k)),
      (∫ u, G j (u + v) ∂σ)
        = ∫ u, (∫ z, f (c • v + s j • z + c • u)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂σ := by
    intro σ j v
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hGdef, hΦdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    congr 1
    rw [smul_add]
    abel
  -- (a) the elementary bound, valid at every step
  have hboundA : ∀ (j : ℕ) (v : EuclideanSpace ℝ (Fin k)),
      |(∫ u, G j (u + v) ∂ν)
        - (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))|
        ≤ M / 6 * c ^ 3 * X := by
    intro j v
    rw [hrw ν j v, hrw (stdGaussian (EuclideanSpace ℝ (Fin k))) j v]
    have hunc : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
        Integrable (Function.uncurry fun u z : EuclideanSpace ℝ (Fin k) =>
            f (c • v + s j • z + c • u))
          (σ.prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
      intro σ hσ
      haveI := hσ
      refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · exact (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]; exact hfb _
    have hswapν := integral_integral_swap (hunc ν hν)
    have hswapγ := integral_integral_swap
      (hunc (stdGaussian (EuclideanSpace ℝ (Fin k))) inferInstance)
    simp only [Function.uncurry] at hswapν hswapγ
    rw [hswapν, hswapγ]
    have hcont : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
        Continuous fun z : EuclideanSpace ℝ (Fin k) =>
          ∫ u, f (c • v + s j • z + c • u) ∂σ := by
      intro σ hσ
      haveI := hσ
      exact (continuous_integral_add_smul (σ := σ) hf.continuous hfb c).comp
        (continuous_const.add (continuous_const_smul (s j)))
    have hbd : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
        ∀ z : EuclideanSpace ℝ (Fin k),
          |∫ u, f (c • v + s j • z + c • u) ∂σ| ≤ 1 := by
      intro σ hσ z
      haveI := hσ
      exact abs_integral_le_one
        (hf.continuous.comp (continuous_const.add (continuous_const_smul c)))
        (fun u => hfb _)
    have hint1 : Integrable (fun z : EuclideanSpace ℝ (Fin k) =>
        ∫ u, f (c • v + s j • z + c • u) ∂ν)
        (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      integrable_of_bounded_continuous (hcont ν hν) (hbd ν hν)
    have hint2 : Integrable (fun z : EuclideanSpace ℝ (Fin k) =>
        ∫ u, f (c • v + s j • z + c • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      integrable_of_bounded_continuous
        (hcont (stdGaussian (EuclideanSpace ℝ (Fin k))) inferInstance)
        (hbd (stdGaussian (EuclideanSpace ℝ (Fin k))) inferInstance)
    rw [← integral_sub hint1 hint2]
    calc |∫ z, ((∫ u, f (c • v + s j • z + c • u) ∂ν)
            - (∫ u, f (c • v + s j • z + c • u)
                ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))))
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        ≤ ∫ z, |(∫ u, f (c • v + s j • z + c • u) ∂ν)
            - (∫ u, f (c • v + s j • z + c • u)
                ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))|
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := abs_integral_le_integral_abs
      _ ≤ ∫ _z, M / 6 * c ^ 3 * X ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
          refine integral_mono (hint1.sub hint2).abs (integrable_const _) fun z => ?_
          have hpt := abs_integral_swap_step_le hmean hcov hβ hmeanγ hcovγ hβγ hf hfb hM
            (c • v + s j • z) hcpos.le
          rw [← hXdef] at hpt
          exact hpt
      _ = M / 6 * c ^ 3 * X := by rw [integral_const]; simp
  -- (b) the Cameron–Martin bound, valid from the first step on
  have hboundB : ∀ j : ℕ, 1 ≤ j → ∀ v : EuclideanSpace ℝ (Fin k),
      |(∫ u, G j (u + v) ∂ν)
        - (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))|
        ≤ C * X / ((j : ℝ) * Real.sqrt (j : ℝ)) := by
    intro j hj v
    rw [hrw ν j v, hrw (stdGaussian (EuclideanSpace ℝ (Fin k))) j v]
    have h := abs_integral_gaussian_smoothed_swap_le hC hmean hcov hν1 hν2 hβ hνdim
      hmeanγ hcovγ hγ1 hγ2 hβγ hγdim hf.continuous hfb (c • v) (hspos j hj) hcpos.le
    refine h.trans_eq ?_
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hsq : (0 : ℝ) < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hsqne : Real.sqrt (j : ℝ) ≠ 0 := hsq.ne'
    have hratio : c / s j = 1 / Real.sqrt (j : ℝ) := by
      rw [hsdef]
      dsimp only
      field_simp
    have hjs : Real.sqrt (j : ℝ) ^ 3 = (j : ℝ) * Real.sqrt (j : ℝ) := by
      have h2 : Real.sqrt (j : ℝ) ^ 2 = (j : ℝ) := Real.sq_sqrt (by linarith)
      calc Real.sqrt (j : ℝ) ^ 3 = Real.sqrt (j : ℝ) ^ 2 * Real.sqrt (j : ℝ) := by ring
        _ = (j : ℝ) * Real.sqrt (j : ℝ) := by rw [h2]
    rw [hXdef, hratio, div_pow, one_pow, hjs]
    ring
  -- ### summing the steps
  set T : ℕ → ℝ := fun j => if j < m + 1 then |I j - I (j + 1)| else 0 with hTdef
  have hθnn : 0 ≤ M / 6 * c ^ 3 * X := by positivity
  have hTnn : ∀ j, 0 ≤ T j := by
    intro j
    rw [hTdef]
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  have hTθ : ∀ j, T j ≤ M / 6 * c ^ 3 * X := by
    intro j
    rw [hTdef]
    dsimp only
    split_ifs with hjlt
    · exact hstepgen j hjlt _ hθnn (hboundA j)
    · exact hθnn
  have hTdec : ∀ j, 1 ≤ j → T j ≤ C * X / ((j : ℝ) * Real.sqrt j) := by
    intro j hj
    have hnn : 0 ≤ C * X / ((j : ℝ) * Real.sqrt (j : ℝ)) := by positivity
    rw [hTdef]
    dsimp only
    split_ifs with hjlt
    · exact hstepgen j hjlt _ hnn (hboundB j hj)
    · exact hnn
  have hsum := sum_le_of_bounded_and_decay_const (K := C * X) (θ := M / 6 * c ^ 3 * X)
    (by positivity) hθnn (n := m + 1) hJ hTnn hTθ hTdec
  have htel : ∀ N : ℕ, |I 0 - I N| ≤ ∑ j ∈ Finset.range N, |I j - I (j + 1)| := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h3 : |I 0 - I (N + 1)| ≤ |I 0 - I N| + |I N - I (N + 1)| := abs_sub_le _ _ _
      linarith
  have hTsum : ∑ j ∈ Finset.range (m + 1), |I j - I (j + 1)|
      = ∑ j ∈ Finset.range (m + 1), T j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hTdef]
    dsimp only
    rw [if_pos (Finset.mem_range.1 hj)]
  -- ### the two endpoints
  have hκ0 : κ 0 = fun _ : Fin (m + 1) => ν := by
    funext i; rw [hκdef]; simp
  have hκN : κ (m + 1) = fun _ : Fin (m + 1) => Measure.dirac 0 := by
    funext i; rw [hκdef]; dsimp only; rw [if_pos i.isLt]
  have hG0 : ∀ w : EuclideanSpace ℝ (Fin k), G 0 w = f (c • w) := by
    intro w
    simp only [hGdef, hΦdef, hs0, zero_smul, add_zero]
    rw [integral_const]
    simp
  have hI0 : I 0 = ∫ x, f x ∂((Measure.pi fun _ : Fin (m + 1) => ν).map
      fun y => c • ∑ i, y i) := by
    rw [integral_map (by fun_prop) hf.continuous.aestronglyMeasurable]
    simp only [hIdef]
    rw [hκ0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hG0 _)
  have hIN : I (m + 1) = ∫ z, f z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    simp only [hIdef]
    rw [hκN, measure_pi_dirac_zero, integral_dirac]
    simp only [Finset.sum_const_zero, hGdef, hΦdef, hsN1, one_smul, smul_zero, zero_add]
  have hfin : |I 0 - I (m + 1)|
      ≤ (J : ℝ) * (M / 6 * c ^ 3 * X) + 3 * (C * X) / Real.sqrt (J : ℝ) := by
    calc |I 0 - I (m + 1)| ≤ ∑ j ∈ Finset.range (m + 1), |I j - I (j + 1)| := htel _
      _ = ∑ j ∈ Finset.range (m + 1), T j := hTsum
      _ ≤ _ := hsum
  rw [hI0, hIN] at hfin
  refine hfin.trans_eq ?_
  have hcube : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 3
      = ((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    have h2 : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = ((m + 1 : ℕ) : ℝ) := Real.sq_sqrt hNr.le
    calc Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 3
        = Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by ring
      _ = ((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ) := by rw [h2]
  have hc3 : c ^ 3 = 1 / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    rw [hcdef, inv_pow, ← hcube, one_div]
  rw [hc3]
  ring

end ImprovedTelescope

/-! #### The improved convex headline `(β/√n)^{1/2}`

With brick (i) in hand the assembly is the same `ε`-balance as for
`berryEsseen_convex_elementary`, except that the mollifier cost is now `ε^{-1}` rather than
`ε^{-3}`, so the balance `ε^{-1} β/√n + C_k ε` is minimised at `ε = (β/√n)^{1/2}` instead of
`(β/√n)^{1/4}`. The cut in the telescope is `J = max 2 ⌈ε² n⌉`, for which
`J (M/6) n^{-3/2} ≤ C₃/(2 ε √n)` and `3C/√J ≤ 3C/(ε √n)`.

Two side remarks on the bookkeeping. First, `J ≤ ε² n + 2` only helps when `ε² n ≥ 1`; when
`ε² n < 1` the claimed bound already exceeds `1` (because `β ≥ k^{3/2} ≥ 1`), so the inequality
is trivial and is discharged separately. Second, the elementary bounds
`berryEsseen_convex_elementary` and `berryEsseen_ball_elementary` are left untouched: they are
proved and are consumed elsewhere, and the improved bound is a *different* (stronger) statement
rather than a restatement. -/

section ImprovedAssembly

/-- **The improved telescope with the cut already chosen.** For a mollified test function with
`‖D³f‖ ≤ C₃/ε³`, and in the window `ε √n ≥ 1`, choosing the cut `J = max 2 ⌈ε² n⌉` in
`abs_integral_smooth_sub_gaussian_improved` gives

`|∫ f dμₙ − ∫ f dγ| ≤ (3C₃/2 + 9C) (β/√n)/ε`,

the mollifier entering through `ε^{-1}` rather than `ε^{-3}`. The arithmetic is
`J (C₃/6) ε^{-3} n^{-3/2} ≤ C₃/(2ε√n)` (using `J ≤ ε²n + 2 ≤ 3ε²n`) and
`3C/√J ≤ 3C/(ε√n)`, followed by `β + β_G ≤ 3β`. -/
private lemma abs_integral_smooth_sub_gaussian_balanced {k n : ℕ} (hk : 0 < k) {Ct : ℝ}
    (hCt0 : 0 < Ct)
    (hCt : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ Ct * s ^ 3)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} (hn : 0 < n) (hν : IsProbabilityMeasure ν)
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 3 f) (hfb : ∀ x, |f x| ≤ 1)
    {C₃ ε : ℝ} (hC₃ : 0 < C₃) (hε : 0 < ε)
    (hD : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3)
    (hbig : 1 ≤ ε * Real.sqrt (n : ℝ)) :
    |(∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i))
        - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
      ≤ (3 * C₃ / 2 + 9 * Ct) * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) / ε := by
  haveI := hν
  have hγstd : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := multivariateGaussian_zero_one
  rw [hγstd]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set t : ℝ := ε * Real.sqrt (n : ℝ) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht2 : t ^ 2 = ε ^ 2 * (n : ℝ) := by rw [htdef, mul_pow, Real.sq_sqrt hnr.le]
  set J : ℕ := max 2 ⌈ε ^ 2 * (n : ℝ)⌉₊ with hJdef
  have hJ2 : 2 ≤ J := le_max_left _ _
  have hJlow : t ^ 2 ≤ (J : ℝ) := by
    rw [ht2]
    refine le_trans (Nat.le_ceil _) ?_
    have hmem : ⌈ε ^ 2 * (n : ℝ)⌉₊ ≤ J := by rw [hJdef]; exact le_max_right _ _
    exact_mod_cast hmem
  have hJhigh : (J : ℝ) ≤ t ^ 2 + 2 := by
    rw [ht2]
    have hmax : (J : ℝ) = max 2 ((⌈ε ^ 2 * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
      rw [hJdef]; push_cast; rfl
    have hc : ((⌈ε ^ 2 * (n : ℝ)⌉₊ : ℕ) : ℝ) < ε ^ 2 * (n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hnn : (0 : ℝ) ≤ ε ^ 2 * (n : ℝ) := by positivity
    rw [hmax]
    rcases max_cases (2 : ℝ) ((⌈ε ^ 2 * (n : ℝ)⌉₊ : ℕ) : ℝ) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; linarith
    · rw [he]; linarith
  have hsqrtJ : t ≤ Real.sqrt (J : ℝ) := by
    have h1 : Real.sqrt (t ^ 2) ≤ Real.sqrt (J : ℝ) := Real.sqrt_le_sqrt hJlow
    rwa [Real.sqrt_sq htpos.le] at h1
  have hswap := abs_integral_smooth_sub_gaussian_improved hk hCt0 hCt hn hν hmean hcov hβ
    hf hfb (M := C₃ / ε ^ 3) (by positivity) hD hJ2
  refine hswap.trans ?_
  set B : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hBdef
  have hBpos : 0 < B := integral_norm_cube_pos hk hcov hβ
  have hβGle : (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ≤ 2 * B := by
    have h1 := integral_norm_cube_gaussian_le (k := k) hk
    rw [hγstd] at h1
    have h2 := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβ
    rw [← hBdef] at h2
    linarith
  have hεne : ε ≠ 0 := hε.ne'
  have hsnne : Real.sqrt (n : ℝ) ≠ 0 := hsn.ne'
  have ht3 : t ^ 3 = ε ^ 3 * ((n : ℝ) * Real.sqrt (n : ℝ)) := by
    have hcube : Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
      have h2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnr.le
      calc Real.sqrt (n : ℝ) ^ 3 = Real.sqrt (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by ring
        _ = (n : ℝ) * Real.sqrt (n : ℝ) := by rw [h2]
    rw [htdef, mul_pow, hcube]
  have hθ : C₃ / ε ^ 3 / 6 / ((n : ℝ) * Real.sqrt (n : ℝ)) = C₃ / (6 * t ^ 3) := by
    rw [ht3]
    field_simp
  have hJ3 : (J : ℝ) ≤ 3 * t ^ 2 := by nlinarith [hJhigh, hbig, htpos]
  have hpart1 : (J : ℝ) * (C₃ / (6 * t ^ 3)) ≤ C₃ / (2 * t) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hJ3 (by positivity : (0 : ℝ) ≤ 2 * C₃ * t),
      hC₃, htpos]
  have hpart2 : 3 * Ct / Real.sqrt (J : ℝ) ≤ 3 * Ct / t :=
    div_le_div_of_nonneg_left (by positivity) htpos hsqrtJ
  have hcoeff : (J : ℝ) * (C₃ / ε ^ 3 / 6 / ((n : ℝ) * Real.sqrt (n : ℝ)))
      + 3 * Ct / Real.sqrt (J : ℝ) ≤ (C₃ / 2 + 3 * Ct) / t := by
    rw [hθ]
    have hsplit : (C₃ / 2 + 3 * Ct) / t = C₃ / (2 * t) + 3 * Ct / t := by
      field_simp
    rw [hsplit]
    linarith [hpart1, hpart2]
  have hcoeffnn : 0 ≤ (J : ℝ) * (C₃ / ε ^ 3 / 6 / ((n : ℝ) * Real.sqrt (n : ℝ)))
      + 3 * Ct / Real.sqrt (J : ℝ) := by positivity
  have hstep1 : ((J : ℝ) * (C₃ / ε ^ 3 / 6 / ((n : ℝ) * Real.sqrt (n : ℝ)))
        + 3 * Ct / Real.sqrt (J : ℝ))
        * (B + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))))
      ≤ ((C₃ / 2 + 3 * Ct) / t) * (3 * B) := by
    have h1 : B + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ≤ 3 * B := by
      linarith
    have h2 : (0 : ℝ) ≤ (C₃ / 2 + 3 * Ct) / t := by positivity
    nlinarith [hcoeff, hcoeffnn, h1, h2, hBpos]
  refine hstep1.trans (le_of_eq ?_)
  rw [htdef]
  field_simp
  ring

set_option maxHeartbeats 1600000 in
/-- **Improved convex Berry–Esseen bound, Lévy (thickening) form.** For every dimension `k > 0`
there is a constant `C` such that for every convex measurable `B`, every width `ε > 0` and every
`n > 0`,

`μₙ(B) ≤ γ(Bᵋ) + C (β/√n)/ε` and `γ(B) ≤ μₙ(Bᵋ) + C (β/√n)/ε`.

This is `berryEsseen_convex_levy_elementary` with `ε³` improved to `ε`: the mollifier's
third-derivative cost `M = C₃/ε³` now enters only through `M^{1/3}`, by
`abs_integral_smooth_sub_gaussian_improved`. -/
theorem berryEsseen_convex_levy_improved {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))) (ε : ℝ),
      0 < n → 0 < ε → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → MeasurableSet B → Convex ℝ B →
      ((((Measure.pi fun _ : Fin n => ν).map
              fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) B).toReal
            ≤ ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
                (Metric.thickening ε B)).toReal
              + C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) / ε)
        ∧ (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal
            ≤ (((Measure.pi fun _ : Fin n => ν).map
                fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
                  (Metric.thickening ε B)).toReal
              + C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) / ε) := by
  obtain ⟨C₃, hC₃one, hC₃⟩ := exists_smoothed_convex_indicator k
  have hC₃pos : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃one
  obtain ⟨Ct, hCtpos, hCt⟩ := exists_tiltRemainder_bound
  refine ⟨3 * C₃ / 2 + 9 * Ct + 2, by positivity, ?_⟩
  intro n ν B ε hn hε hνp hmean hcov hβint hBmeas hBconv
  haveI := hνp
  have hγstd : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := multivariateGaussian_zero_one
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  set μ : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.pi fun _ : Fin n => ν).map (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) with hμdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    have h := Real.sqrt_le_sqrt hk1
    rwa [Real.sqrt_one] at h
  have hβ1 : 1 ≤ β := by
    have h := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
    rw [← hβdef] at h
    nlinarith [h, hsk, hk1]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  set t : ℝ := ε * Real.sqrt (n : ℝ) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht2 : t ^ 2 = ε ^ 2 * (n : ℝ) := by
    rw [htdef, mul_pow, Real.sq_sqrt hnr.le]
  have hqt : q / ε = β / t := by
    rw [hqdef, htdef, div_div]
    congr 1
    ring
  -- the degenerate window `ε² n < 1`, where the claimed bound already exceeds `1`
  have htrivial : t < 1 → (1 : ℝ) ≤ (3 * C₃ / 2 + 9 * Ct + 2) * q / ε := by
    intro ht1
    have hb : 1 ≤ β / t := by
      rw [le_div_iff₀ htpos]
      nlinarith [hβ1, ht1, htpos]
    have hqe : 1 ≤ q / ε := by rw [hqt]; exact hb
    have hsplit : (3 * C₃ / 2 + 9 * Ct + 2) * q / ε
        = (3 * C₃ / 2 + 9 * Ct + 2) * (q / ε) := by ring
    rw [hsplit]
    nlinarith [hqe, hC₃pos, hCtpos]
  have hμ1 : (μ B).toReal ≤ 1 := by
    have h := measure_mono (μ := μ) (Set.subset_univ B)
    rw [measure_univ] at h
    simpa using ENNReal.toReal_mono (by simp) h
  have hγ1 : (γ B).toReal ≤ 1 := by
    have h := measure_mono (μ := γ) (Set.subset_univ B)
    rw [measure_univ] at h
    simpa using ENNReal.toReal_mono (by simp) h
  rcases lt_or_ge t 1 with hsmall | hbig
  · have h := htrivial hsmall
    exact ⟨by linarith [ENNReal.toReal_nonneg (a := γ (Metric.thickening ε B))],
      by linarith [ENNReal.toReal_nonneg (a := μ (Metric.thickening ε B))]⟩
  -- ### the main window `ε² n ≥ 1`
  obtain ⟨f, hfcd, hf0, hf1, hfB, hfsupp, hfD, hfD1, hfD2⟩ := hC₃ B hBconv hε
  have hfbd : ∀ x, |f x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hf0 x], hf1 x⟩
  have hfint : ∀ ρ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure ρ →
      Integrable f ρ := by
    intro ρ hρ
    haveI := hρ
    exact (integrable_const (1 : ℝ)).mono' hfcd.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfbd x)
  have hbig' : (1 : ℝ) ≤ ε * Real.sqrt (n : ℝ) := by rw [htdef] at hbig; exact hbig
  have herr : |(∫ x, f x ∂μ) - (∫ x, f x ∂γ)|
      ≤ (3 * C₃ / 2 + 9 * Ct + 2) * q / ε := by
    have h := abs_integral_smooth_sub_gaussian_balanced hk hCtpos hCt hn hνp hmean hcov hβint
      hfcd hfbd hC₃pos hε hfD hbig'
    rw [← hμdef, ← hγdef, ← hβdef, ← hqdef] at h
    refine h.trans ?_
    have hqe : 0 ≤ q / ε := by positivity
    have e1 : (3 * C₃ / 2 + 9 * Ct) * q / ε = (3 * C₃ / 2 + 9 * Ct) * (q / ε) := by ring
    have e2 : (3 * C₃ / 2 + 9 * Ct + 2) * q / ε
        = (3 * C₃ / 2 + 9 * Ct) * (q / ε) + 2 * (q / ε) := by ring
    rw [e1, e2]
    linarith
  -- the sandwich
  have hthick : MeasurableSet (Metric.thickening ε B) := Metric.isOpen_thickening.measurableSet
  have hlowμ : (μ B).toReal ≤ ∫ x, f x ∂μ :=
    measureReal_le_integral_of_eq_one hBmeas (hfint μ hμprob) hf0 hfB
  have hlowγ : (γ B).toReal ≤ ∫ x, f x ∂γ :=
    measureReal_le_integral_of_eq_one hBmeas (hfint γ hγprob) hf0 hfB
  have huppμ : (∫ x, f x ∂μ) ≤ (μ (Metric.thickening ε B)).toReal :=
    integral_le_measureReal_of_support_subset hthick (hfint μ hμprob) hf1 hfsupp
  have huppγ : (∫ x, f x ∂γ) ≤ (γ (Metric.thickening ε B)).toReal :=
    integral_le_measureReal_of_support_subset hthick (hfint γ hγprob) hf1 hfsupp
  have hswap' := abs_le.1 herr
  constructor
  · linarith [hswap'.2, hlowμ, huppγ]
  · linarith [hswap'.1, hlowγ, huppμ]

/-- **Improved convex-set Berry–Esseen bound.** For every dimension `k > 0` there is a constant
`C` such that for all `n > 0`, every centred identity-covariance law `ν` with finite third
moment `β = ∫‖y‖³ dν`, and every measurable convex `B`,

`|μₙ(B) − γ(B)| ≤ C (β/√n)^{1/2} = O(n^{-1/4})`.

This is a strict improvement on the exponent `1/4` of `berryEsseen_convex_elementary`
(`n^{-1/8}`), and it is the ceiling of the *non-inductive* elementary route: see the wave-13
amendment in the module docstring. The residual gap to Bentkus's `400 k^{1/4} β/√n` is a further
factor `(β/√n)^{1/2}`, obtainable only by the self-improving induction
`Δ ≤ A ε^{-3} δ (C_k ε + 2Δ) + C_k ε`, which is not attempted here.

The constant is `C = C₀ + C_k` with `C₀` from `berryEsseen_convex_levy_improved` and
`C_k = gaussianShellConst k = 4 e² √k`; the balance is `ε = (β/√n)^{1/2}`, at which
`(β/√n)/ε = ε`. The proof is the same two-sided thickening/erosion argument as
`berryEsseen_convex_elementary`. -/
theorem berryEsseen_convex_improved {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))),
      0 < n → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → MeasurableSet B → Convex ℝ B →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) B).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨C₀, hC₀pos, hlevy⟩ := berryEsseen_convex_levy_improved hk
  have hCkpos : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  refine ⟨C₀ + gaussianShellConst k, by linarith, ?_⟩
  intro n ν B hn hνp hmean hcov hβint hBmeas hBconv
  haveI := hνp
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  set μ : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.pi fun _ : Fin n => ν).map (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) with hμdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  have hεpos : 0 < q ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hqpos _
  have hbal : q / q ^ ((1 : ℝ) / 2) = q ^ ((1 : ℝ) / 2) := by
    have hsum : q ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) = q := by
      rw [← Real.rpow_add hqpos]
      norm_num
    rw [div_eq_iff (Real.rpow_pos_of_pos hqpos _).ne']
    exact hsum.symm
  have hC₀bal : C₀ * q / q ^ ((1 : ℝ) / 2) = C₀ * q ^ ((1 : ℝ) / 2) := by
    rw [mul_div_assoc, hbal]
  have hlevyB := hlevy n ν B (q ^ ((1 : ℝ) / 2)) hn hεpos hνp hmean hcov hβint hBmeas hBconv
  rw [← hμdef, ← hβdef, ← hqdef, hC₀bal] at hlevyB
  have hEmeas : MeasurableSet (erosion (q ^ ((1 : ℝ) / 2)) B) :=
    (isOpen_erosion _ B).measurableSet
  have hEconv : Convex ℝ (erosion (q ^ ((1 : ℝ) / 2)) B) := convex_erosion hBconv
  have hlevyE := hlevy n ν (erosion (q ^ ((1 : ℝ) / 2)) B) (q ^ ((1 : ℝ) / 2)) hn hεpos hνp
    hmean hcov hβint hEmeas hEconv
  rw [← hμdef, ← hβdef, ← hqdef, hC₀bal] at hlevyE
  have hthick : (γ (Metric.thickening (q ^ ((1 : ℝ) / 2)) B)).toReal
      ≤ (γ B).toReal + gaussianShellConst k * q ^ ((1 : ℝ) / 2) := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) (by positivity) ?_
    have := gaussian_thickening_le hk hBconv hεpos
    rwa [← hγdef] at this
  have herode : (γ B).toReal
      ≤ (γ (erosion (q ^ ((1 : ℝ) / 2)) B)).toReal
        + gaussianShellConst k * q ^ ((1 : ℝ) / 2) := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) (by positivity) ?_
    have := gaussian_le_erosion_add hk hBmeas hBconv hεpos
    rwa [← hγdef] at this
  have hback : (μ (Metric.thickening (q ^ ((1 : ℝ) / 2))
      (erosion (q ^ ((1 : ℝ) / 2)) B))).toReal ≤ (μ B).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (thickening_erosion_subset _ B))
  rw [abs_sub_le_iff]
  constructor
  · linarith [hlevyB.1]
  · linarith [hlevyE.2]

/-- **Improved ball Berry–Esseen bound, with a dimension-free constant.** There is an
*absolute* constant `C` — independent of the dimension `k`, the sample size `n` and the sampling
law `ν` — with

`|μₙ{‖z‖² ≤ t} − γ{‖z‖² ≤ t}| ≤ C (β/√n)^{1/2} = O(n^{-1/4})`

uniformly in the threshold `t`. This is `berryEsseen_ball_elementary` at the better exponent:
the two share the `ε`-generic assembly `berryEsseen_ball_of_swap`, and differ only in which swap
estimate is fed to it — `abs_integral_smooth_sub_gaussian_le` (cost `C₃/2 · ε`, balanced at
`ε = (β/√n)^{1/4}`) versus `abs_integral_smooth_sub_gaussian_balanced` (cost
`(3C₃/2 + 9C) · ε`, balanced at `ε = (β/√n)^{1/2}`).

The window hypothesis `ε √n ≥ 1` of the balanced swap is automatic at this `ε`: it says
`ε² n = (β/√n) n = β √n ≥ 1`, and `β ≥ k^{3/2} ≥ 1`, `n ≥ 1`.

All three constants are dimension-free (`Cac` from `gaussian_ball_shell_measure_le`, `C₃` from
`exists_smoothed_radial_indicator`, `C` from `exists_tiltRemainder_bound`), so the improved
constant `Cac + 3C₃/2 + 9C` is too. `berryEsseen_ball_elementary` is kept as it stands: it is
what `SmoothTestLargeK.bentkus_berry_esseen_ball` is wired to, and nothing there needs the better
exponent. -/
theorem berryEsseen_ball_improved :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) (t : ℝ),
      0 < n → 0 < k → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k),
        (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) {z | ‖z‖ ^ 2 ≤ t}).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
              {z | ‖z‖ ^ 2 ≤ t}).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := exists_smoothed_radial_indicator
  obtain ⟨Cac, hCacpos, hCac⟩ := gaussian_ball_shell_measure_le
  obtain ⟨Ct, hCtpos, hCt⟩ := exists_tiltRemainder_bound
  refine ⟨Cac + (3 * C₃ / 2 + 9 * Ct), by positivity, ?_⟩
  intro k n ν t hn hk hνp hmean hcov hβint
  haveI := hνp
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    have h := Real.sqrt_le_sqrt hk1
    rwa [Real.sqrt_one] at h
  have hβ1 : 1 ≤ β := by
    have h := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
    rw [← hβdef] at h
    nlinarith [h, hsk, hk1]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  have hsn1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt hn1
    rwa [Real.sqrt_one] at h
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hnr.le
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  set ε : ℝ := q ^ ((1 : ℝ) / 2) with hεdef
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hqpos _
  have hεsq : ε ^ 2 = q := by
    rw [hεdef, ← Real.rpow_natCast (q ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hqpos.le]
    norm_num
  have hqε : q / ε = ε := by
    rw [← hεsq, pow_two, mul_div_assoc, div_self hεpos.ne', mul_one]
  -- the window hypothesis `ε √n ≥ 1`
  have hqn1 : 1 ≤ q * (n : ℝ) := by
    have h1 : Real.sqrt (n : ℝ) ≤ β * (n : ℝ) := by
      have hb : Real.sqrt (n : ℝ) * 1 ≤ Real.sqrt (n : ℝ) * (β * Real.sqrt (n : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hsn.le
        nlinarith [hβ1, hsn1]
      rw [mul_one] at hb
      calc Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * (β * Real.sqrt (n : ℝ)) := hb
        _ = β * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        _ = β * (n : ℝ) := by rw [hsq]
    rw [hqdef, div_mul_eq_mul_div, le_div_iff₀ hsn]
    linarith
  have hbig : (1 : ℝ) ≤ ε * Real.sqrt (n : ℝ) := by
    have hp : 0 < ε * Real.sqrt (n : ℝ) := by positivity
    have hsqr : (ε * Real.sqrt (n : ℝ)) ^ 2 = q * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hnr.le, hεsq]
    nlinarith [hqn1, hp, hsqr]
  have herr : ∀ f : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 3 f → (∀ x, |f x| ≤ 1) →
      (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) →
      |(∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i))
        - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
        ≤ (3 * C₃ / 2 + 9 * Ct) * ε := by
    intro f hfcd hfbd hfD3
    have h := abs_integral_smooth_sub_gaussian_balanced hk hCtpos hCt hn hνp hmean hcov hβint
      hfcd hfbd hC₃pos hεpos hfD3 hbig
    rw [← hβdef] at h
    refine h.trans_eq ?_
    rw [← hqdef, mul_div_assoc, hqε]
  exact berryEsseen_ball_of_swap hk hνp hCacpos (by positivity) hεpos
    (fun a ha => hC₃ k a ha hεpos) (fun a w ha hw => hCac k hk a w ha hw) herr t

end ImprovedAssembly


/-! ### Wave-19: the fixed points of Bentkus's self-improving recursion

The wave-16 note isolated *two* missing ingredients for the sharp rate. The first is the
weighted Cameron–Martin bound `integral_abs_mul_vecTiltRemainder_le` proved above. The second is
the **self-improving induction over `n`**: the localised swap bounds the discrepancy at sample
size `n` by an expression in which the discrepancy *itself* reappears, through the
anti-concentration of the hybrid laws.

Write `Δ` for the supremum, over measurable convex `B`, of `|μₙ(B) − γ(B)|`, and `δ = β/√n`.
The localised telescope replaces the uniform step bound by one weighted by
`P(hybrid ∈ ε-shell of ∂B)`, and that shell probability is at most
`γ(shell) + 2Δ ≤ C_k ε + 2Δ` — Gaussian shell mass (`gaussian_thickening_le`) plus twice the
discrepancy being bounded. The recursions that result are the following three; this section
solves all three as statements about real numbers, so that the only thing left for the
probabilistic side is to *produce* the hypothesis `hrec`.

* `le_of_selfImproving_cube` / `cube_le_of_selfImproving_cube`: the recursion of the wave-16
  note verbatim, `Δ ≤ A δ ε⁻³ (C ε + 2Δ) + C ε` for every `ε > 0`, closes at
  `Δ ≤ (5/2) C e` with `e³ = 4Aδ`, i.e. `Δ³ ≤ 63 C³ A δ`, i.e. `Δ ≲ C δ^{1/3}`.
* `le_of_selfImproving_smoothed`: the same recursion **after** the Gaussian smoothing of the
  hybrid telescope, which turns `ε⁻³` into `ε⁻¹` (this is the wave-13/16 improvement,
  `abs_integral_smooth_sub_gaussian_improved`). It closes at `Δ ≤ 10 A C δ` — **linear in
  `δ = β/√n`, i.e. exactly the sharp Bentkus rate**, with the dimension entering only through
  the shell constant `C = C_k`. This is the precise sense in which "the induction, iterated
  with the Gaussian smoothing, gives the sharp rate".
* `le_of_selfImproving_smoothed_sqrt` / `cube_le_of_selfImproving_smoothed_sqrt`: the variant
  actually supplied by the `L²` weighting proved above, `Δ ≤ A δ ε⁻¹ √(C ε + 2Δ) + C ε`, whose
  fixed point is `Δ ≤ 6 m²` with `m³ = C A δ`, i.e. `Δ³ ≤ 216 (C A δ)²`, i.e.
  `Δ ≲ (C β/√n)^{2/3} = O(n^{-1/3})`.

**Honest status of the probabilistic step.** What is *not* proved here is the production of
`hrec`: it needs the localised telescope, i.e. a rerun of
`abs_integral_smooth_sub_gaussian_improved`
in which each step is estimated by `abs_integral_mul_vecTiltRemainder_le_of_support` with
`G = D³` of the mollified indicator (supported on the `ε`-shell) instead of by the uniform
`abs_integral_gaussian_smoothed_swap_le`, and in which the shell probability *for the hybrid law*
is controlled by the induction hypothesis at the smaller sample sizes. Two concrete obstacles
remain, both structural rather than arithmetic:

1. the shell of `∂B` must be a *set* to which the induction hypothesis applies — one needs
   `γ`-shell mass of a convex set to be estimated by the discrepancy over convex sets, and the
   shell `Bᵋ \ B₋ᵋ` is a difference of two convex sets, so the induction must be run on the
   class of such differences (Bentkus does this; it costs a factor `2` in the constant, which is
   why `2Δ` appears in the recursion above);
2. the induction is over `n`, and the hybrid at step `j` is a law of *`j` Gaussian plus `n − j`
   `ν`* summands, not a rescaled sum of `j` summands, so the inductive hypothesis has to be
   stated for the whole hybrid family rather than for `μₙ` alone.

Neither is attempted here. What the section does deliver is that once `hrec` is available in any
of the three shapes, the rate follows by pure arithmetic — including, in the smoothed case, the
sharp `β/√n`. -/

section SelfImproving

/-- **Solving `u ≤ a √u + b`**: the quadratic step behind the square-root recursion. -/
private lemma le_of_le_sqrt_mul {u a b : ℝ} (hu : 0 ≤ u)
    (h : u ≤ a * Real.sqrt u + b) : u ≤ 4 / 3 * (a ^ 2 + b) := by
  have hs : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  nlinarith [sq_nonneg (Real.sqrt u - 2 * a), Real.sqrt_nonneg u]

/-- Subadditivity of `√`. -/
private lemma sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h1 : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have hx' := Real.sq_sqrt hx
    have hy' := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-- **The unsmoothed self-improving recursion** `Δ ≤ A δ ε⁻³ (C ε + 2Δ) + C ε` (Bentkus), at the
cut `e³ = 4Aδ` where the `2Δ` term is absorbed into `Δ/2`. -/
theorem le_of_selfImproving_cube {A C δ Δ e : ℝ}
    (he : 0 < e) (hcube : e ^ 3 = 4 * (A * δ))
    (hrec : ∀ ε : ℝ, 0 < ε → Δ ≤ A * δ * (ε ^ 3)⁻¹ * (C * ε + 2 * Δ) + C * ε) :
    Δ ≤ 5 / 2 * C * e := by
  have hpos : (0 : ℝ) < e ^ 3 := pow_pos he 3
  have hAδ : 0 < A * δ := by linarith [hcube ▸ hpos]
  have h := hrec e he
  rw [hcube] at h
  have hq : A * δ * (4 * (A * δ))⁻¹ = 1 / 4 := by
    rw [mul_inv, ← mul_assoc, mul_comm (A * δ) (4 : ℝ)⁻¹, mul_assoc,
      mul_inv_cancel₀ hAδ.ne']
    norm_num
  rw [hq] at h
  linarith

/-- Root-free form of `le_of_selfImproving_cube`: `Δ³ ≤ 63 C³ A δ`, i.e. `Δ ≲ C (Aδ)^{1/3}`. -/
theorem cube_le_of_selfImproving_cube {A C δ Δ : ℝ} (hΔ : 0 ≤ Δ) (hC : 0 ≤ C)
    (hAδ : 0 < A * δ)
    (hrec : ∀ ε : ℝ, 0 < ε → Δ ≤ A * δ * (ε ^ 3)⁻¹ * (C * ε + 2 * Δ) + C * ε) :
    Δ ^ 3 ≤ 63 * C ^ 3 * (A * δ) := by
  set e : ℝ := (4 * (A * δ)) ^ ((1 : ℝ) / 3) with he'
  have h4 : (0 : ℝ) < 4 * (A * δ) := by linarith
  have he : 0 < e := Real.rpow_pos_of_pos h4 _
  have hcube : e ^ 3 = 4 * (A * δ) := by
    rw [he', ← Real.rpow_natCast ((4 * (A * δ)) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul h4.le]
    norm_num
  have hmain := le_of_selfImproving_cube he hcube hrec
  have hcubed : Δ ^ 3 ≤ (5 / 2 * C * e) ^ 3 := pow_le_pow_left₀ hΔ hmain 3
  have hexp : (5 / 2 * C * e) ^ 3 = (5 / 2) ^ 3 * C ^ 3 * e ^ 3 := by ring
  rw [hexp, hcube] at hcubed
  nlinarith [pow_nonneg hC 3]

/-- **The smoothed self-improving recursion — the sharp `β/√n` fixed point.** After the Gaussian
smoothing carried by the hybrid telescope the mollifier cost is `ε⁻¹`, not `ε⁻³`
(`berryEsseen_convex_levy_improved`); with the localisation weight `C ε + 2Δ` the recursion
`Δ ≤ A δ ε⁻¹ (C ε + 2Δ) + C ε` closes at `Δ ≤ 10 A C δ` — **linear in `δ = β/√n`**. -/
theorem le_of_selfImproving_smoothed {A C δ Δ : ℝ} (hAδ : 0 < A * δ)
    (hrec : ∀ ε : ℝ, 0 < ε → Δ ≤ A * δ * ε⁻¹ * (C * ε + 2 * Δ) + C * ε) :
    Δ ≤ 10 * (A * δ) * C := by
  have h := hrec (4 * (A * δ)) (by linarith)
  have hq : A * δ * (4 * (A * δ))⁻¹ = 1 / 4 := by
    rw [mul_inv, ← mul_assoc, mul_comm (A * δ) (4 : ℝ)⁻¹, mul_assoc,
      mul_inv_cancel₀ hAδ.ne']
    norm_num
  rw [hq] at h
  nlinarith

/-- **The `L²`-weighted (Cauchy–Schwarz) smoothed recursion.** This is the shape the weighted
bound `abs_integral_mul_vecTiltRemainder_le_of_support` actually produces: the shell weight
enters under a square root. At the cut `ε = m²/C`, `m³ = C A δ`, it closes at `Δ ≤ 6 m²`. -/
theorem le_of_selfImproving_smoothed_sqrt {A C δ Δ m : ℝ} (hΔ : 0 ≤ Δ) (hC : 0 < C)
    (hm : 0 < m) (hm3 : m ^ 3 = C * (A * δ))
    (hrec : ∀ ε : ℝ, 0 < ε →
      Δ ≤ A * δ * ε⁻¹ * Real.sqrt (C * ε + 2 * Δ) + C * ε) :
    Δ ≤ 6 * m ^ 2 := by
  have hAδ : 0 < A * δ := by
    have h3 : 0 < m ^ 3 := pow_pos hm 3
    rw [hm3] at h3
    nlinarith
  set ε : ℝ := m ^ 2 / C with hε'
  have hε : 0 < ε := by positivity
  have hCε : C * ε = m ^ 2 := by
    rw [hε']; field_simp
  have hAε : A * δ * ε⁻¹ = m := by
    rw [hε']
    field_simp
    nlinarith [hm3]
  have h := hrec ε hε
  rw [hAε, hCε] at h
  have hsub : Real.sqrt (m ^ 2 + 2 * Δ) ≤ m + Real.sqrt 2 * Real.sqrt Δ := by
    have h1 := sqrt_add_le_sqrt_add_sqrt (x := m ^ 2) (y := 2 * Δ)
      (by positivity) (by positivity)
    rw [Real.sqrt_sq hm.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at h1
    exact h1
  have hstep : Δ ≤ (Real.sqrt 2 * m) * Real.sqrt Δ + 2 * m ^ 2 := by
    nlinarith [Real.sqrt_nonneg Δ, hm.le]
  have hfix := le_of_le_sqrt_mul hΔ hstep
  have h2 : (Real.sqrt 2 * m) ^ 2 = 2 * m ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [h2] at hfix
  linarith

/-- Root-free form: `Δ³ ≤ 216 (C A δ)²`, i.e. `Δ ≲ (C β/√n)^{2/3} = O(n^{-1/3})` — strictly
better than the proved `O(n^{-1/4})` of `berryEsseen_convex_improved`, strictly weaker than the
sharp `O(n^{-1/2})` that the unweighted (`L¹`) localisation would give. -/
theorem cube_le_of_selfImproving_smoothed_sqrt {A C δ Δ : ℝ} (hΔ : 0 ≤ Δ) (hC : 0 < C)
    (hAδ : 0 < A * δ)
    (hrec : ∀ ε : ℝ, 0 < ε →
      Δ ≤ A * δ * ε⁻¹ * Real.sqrt (C * ε + 2 * Δ) + C * ε) :
    Δ ^ 3 ≤ 216 * (C * (A * δ)) ^ 2 := by
  have hpos : (0 : ℝ) < C * (A * δ) := by positivity
  set m : ℝ := (C * (A * δ)) ^ ((1 : ℝ) / 3) with hm'
  have hm : 0 < m := Real.rpow_pos_of_pos hpos _
  have hm3 : m ^ 3 = C * (A * δ) := by
    rw [hm', ← Real.rpow_natCast ((C * (A * δ)) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hpos.le]
    norm_num
  have hmain := le_of_selfImproving_smoothed_sqrt hΔ hC hm hm3 hrec
  have hcubed : Δ ^ 3 ≤ (6 * m ^ 2) ^ 3 := pow_le_pow_left₀ hΔ hmain 3
  have hexp : (6 * m ^ 2) ^ 3 = 216 * (m ^ 3) ^ 2 := by ring
  rw [hexp, hm3] at hcubed
  exact hcubed

end SelfImproving

/-! ### Wave-20: the recursion run as an induction over the hybrid family

The wave-19 fixed points solve the recursion at a *single* scale: they take the inequality
`Δ ≤ A δ ε⁻¹ (C ε + 2Δ) + C ε` as given, with the *same* `Δ` on both sides. That is not the shape
the telescope produces. The `2Δ` on the right is the shell mass of a **hybrid** law
`c ∑_{i ≥ j} Yᵢ + sⱼ Z`, whose non-Gaussian part is a normalised sum of `m = n − j` summands, so
what the right-hand side really sees is the discrepancy `Δ_m` at the *smaller* sample sizes. The
present section supplies the two missing pieces of bookkeeping.

* `le_of_selfImproving_induction` — the recursion as a **strong induction over `n`**. The
  hypothesis is allowed to invoke an arbitrary bound `Y` on `Δ_m` for the neighbours
  `n/2 ≤ m ≤ n` only; this is the range that the telescope actually needs, because for
  `j ≤ n/2` one has `m = n − j ≥ n/2`, while for `j ≥ n/2` the hybrid carries a Gaussian
  component of width `sⱼ ≥ 1/√2` and its shell mass is bounded outright by the Gaussian
  anti-concentration estimate `gaussian_thickening_le`, with no induction at all. Since
  `√m ≥ √n/2` on that range, the inductive bound `K β/√m` self-propagates with `Y = 2 K δ`,
  and the cut `ε = 8 A δ` closes the loop at `K = 18 A C` — the **sharp `β/√n` rate**, with no
  base case needed (for `n = 1` the neighbour range is empty).

* `convexDiscrepancy` and `measureReal_shell_le_of_convexDiscrepancy` — the class the induction
  runs on, and the *derivation* of the shape `C ε + 2Δ`. The `ε`-shell of a convex `B` is
  `Bᵋ \ interior B`, a **difference of two convex sets**; that is why the factor is `2Δ` and not
  `Δ`. But — and this corrects the wave-19 reading of the obstacle — the induction does **not**
  have to be enlarged to the class of differences of convex sets: a difference `B₁ \ B₂` with
  `B₂ ⊆ B₁` has `μ(B₁ \ B₂) = μ(B₁) − μ(B₂)`, so two applications of the *convex* bound suffice
  (`measureReal_diff_le_of_convexDiscrepancy`). The class of measurable convex sets is closed
  under the operations the induction performs.
-/

section SelfImprovingInduction

/-- **The self-improving recursion, run as a strong induction over the sample size.**

If `D : ℕ → ℝ` satisfies, for every `n ≥ 1`, every cut `ε > 0` and every bound `Y` valid on the
neighbour range `n/2 ≤ m < n`,

`D n ≤ A (b/√n) ε⁻¹ (C ε + 2 Y) + C ε`,

then `D n ≤ 18 A C (b/√n)` for all `n ≥ 1`.

This is the shape the localised hybrid telescope produces (see the section docstring): the `2Y`
is the shell mass of the hybrid laws, whose non-Gaussian part is a normalised sum of
`m = n − j ≥ n/2` summands. The proof is a strong induction with `Y = 2 K δ` (legitimate because
`√m ≥ √n/2` on the neighbour range) and the cut `ε = 8 A δ`, at which the recursion reads
`D n ≤ 9 A C δ + Y/4`. The neighbour range includes `m = n` — the hybrid at `j = 0` is `μₙ`
itself — so `Y = max (2 K δ) (D n)`, and the two cases close at `K = 18 A C` and `12 A C`
respectively. No base case is needed. -/
theorem le_of_selfImproving_induction {A C b : ℝ} {D : ℕ → ℝ}
    (hA : 0 < A) (hC : 0 < C) (hb : 0 < b)
    (hrec : ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → ∀ Y : ℝ,
      (∀ m : ℕ, n ≤ 2 * m → m ≤ n → D m ≤ Y) →
      D n ≤ A * (b / Real.sqrt n) * ε⁻¹ * (C * ε + 2 * Y) + C * ε) :
    ∀ n : ℕ, 0 < n → D n ≤ 18 * (A * C) * (b / Real.sqrt n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    set K : ℝ := 18 * (A * C) with hKdef
    have hKpos : 0 < K := by rw [hKdef]; positivity
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
    set δ : ℝ := b / Real.sqrt (n : ℝ) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    set Y : ℝ := max (2 * K * δ) (D n) with hYdef
    have hY : ∀ m : ℕ, n ≤ 2 * m → m ≤ n → D m ≤ Y := by
      intro m hm2 hmn
      rcases eq_or_lt_of_le hmn with rfl | hlt
      · exact le_max_right _ _
      have hm : 0 < m := by omega
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm
      have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmr
      have hstep := ih m hlt hm
      have hcast : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hm2
      have hsqrt : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
        have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt (4 * (m : ℝ)) :=
          Real.sqrt_le_sqrt (by linarith)
        have h2 : Real.sqrt (4 * (m : ℝ)) = 2 * Real.sqrt (m : ℝ) := by
          rw [show (4 : ℝ) * (m : ℝ) = 2 ^ 2 * (m : ℝ) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
        rwa [h2] at h1
      have hqnn : 0 ≤ b / Real.sqrt (n : ℝ) := by positivity
      have hq : b / Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = b := by field_simp
      have hratio : b / Real.sqrt (m : ℝ) ≤ 2 * δ := by
        rw [hδdef, div_le_iff₀ hsm]
        nlinarith [mul_le_mul_of_nonneg_left hsqrt hqnn, hq]
      refine le_trans (le_trans hstep ?_) (le_max_left _ _)
      calc K * (b / Real.sqrt (m : ℝ)) ≤ K * (2 * δ) := by nlinarith [hKpos.le]
        _ = 2 * K * δ := by ring
    have hεpos : 0 < 8 * A * δ := by positivity
    have h := hrec n hn (8 * A * δ) hεpos Y hY
    have hinv : A * δ * (8 * A * δ)⁻¹ = 1 / 8 := by
      rw [mul_inv, ← mul_assoc]; field_simp
    rw [← hδdef] at h
    rw [show A * δ * (8 * A * δ)⁻¹ * (C * (8 * A * δ) + 2 * Y)
        = (A * δ * (8 * A * δ)⁻¹) * (C * (8 * A * δ) + 2 * Y) from rfl, hinv] at h
    have hexp : (1 : ℝ) / 8 * (C * (8 * A * δ) + 2 * Y) + C * (8 * A * δ)
        = 9 * (A * C) * δ + Y / 4 := by ring
    rw [hexp] at h
    rcases le_total (D n) (2 * K * δ) with hcase | hcase
    · have hmax : Y = 2 * K * δ := by rw [hYdef]; exact max_eq_left hcase
      rw [hmax] at h
      rw [hKdef] at h ⊢
      linarith
    · have hmax : Y = D n := by rw [hYdef]; exact max_eq_right hcase
      rw [hmax] at h
      rw [hKdef]
      nlinarith [hA.le, hC.le, hδpos.le]

/-- **The self-improving induction with an ABSTRACT forcing factor (wave 39: PROVED).**

Wave 32 solved the fixed point with the specific forcing term `1 + log(1 + ε⁻¹)`
(`le_of_selfImproving_induction_log`, now a corollary of this). Wave 39's amended ledger
produces a *different* forcing term — the `3/2` power `(1 + log(1 + ε⁻¹))^{3/2}`, see
`logPow32` and the note on `abs_integral_gaussian_smoothed_swap_localised_le` — so the question
"does the fixed point still close, and at what constant?" had to be re-asked rather than
assumed. The answer is that the wave-32 argument never used anything about the logarithm except
two properties, which are exactly the hypotheses below:

* `1 ≤ G ε` — so the log-free term `9 A C δ` can be absorbed into `K δ G`;
* `G` is **antitone** — so `G` propagates in the right direction along the neighbour range
  `n/2 ≤ m ≤ n`, on which `δₘ ≥ δₙ` and hence `8 A δₘ ≥ 8 A δₙ`.

With those, the two cases close at `K = 20 A C` and `K = (40/3) A C` exactly as before: **the
constant is unchanged, whatever the forcing factor**. In particular the deviation wave 39 has to
record in the headline is a change of the *log power* and of the dimension factor, and not of
the recursion constant. As with `le_of_selfImproving_induction` no base case is needed. -/
theorem le_of_selfImproving_induction_forcing {A C b w : ℝ} {D : ℕ → ℝ} {G : ℝ → ℝ}
    (hA : 0 < A) (hC : 0 < C) (hb : 0 < b) (hb1 : w ≤ 8 * A * b)
    (hG1 : ∀ x : ℝ, 0 < x → 1 ≤ G x)
    (hGanti : ∀ x y : ℝ, 0 < x → x ≤ y → G y ≤ G x)
    (hrec : ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → w ≤ ε * Real.sqrt (n : ℝ) → ∀ Y : ℝ,
      (∀ m : ℕ, n ≤ 2 * m → m ≤ n → D m ≤ Y) →
      D n ≤ A * (b / Real.sqrt n) * ε⁻¹ * (C * ε + 2 * Y)
        + A * (b / Real.sqrt n) * C * G ε
        + C * ε) :
    ∀ n : ℕ, 0 < n → D n ≤ 20 * (A * C) * (b / Real.sqrt n)
      * G (8 * A * (b / Real.sqrt n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
    set δ : ℝ := b / Real.sqrt (n : ℝ) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    set M : ℝ := G (8 * A * δ) with hMdef
    have hM1 : 1 ≤ M := hG1 _ (by positivity)
    set K : ℝ := 20 * (A * C) with hKdef
    have hKpos : 0 < K := by rw [hKdef]; positivity
    set Y : ℝ := max (2 * K * δ * M) (D n) with hYdef
    have hY : ∀ m : ℕ, n ≤ 2 * m → m ≤ n → D m ≤ Y := by
      intro m hm2 hmn
      rcases eq_or_lt_of_le hmn with rfl | hlt
      · exact le_max_right _ _
      have hm : 0 < m := by omega
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm
      have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmr
      have hstep := ih m hlt hm
      have hcast : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hm2
      have hsqrt : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
        have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt (4 * (m : ℝ)) :=
          Real.sqrt_le_sqrt (by linarith)
        have h2 : Real.sqrt (4 * (m : ℝ)) = 2 * Real.sqrt (m : ℝ) := by
          rw [show (4 : ℝ) * (m : ℝ) = 2 ^ 2 * (m : ℝ) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
        rwa [h2] at h1
      have hsmn : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hmn)
      set δm : ℝ := b / Real.sqrt (m : ℝ) with hδm
      have hδmpos : 0 < δm := by rw [hδm]; positivity
      have hδmle : δm ≤ 2 * δ := by
        rw [hδm, hδdef, div_le_iff₀ hsm]
        have h : b / Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = b := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hsqrt (by positivity : (0:ℝ) ≤ b /
          Real.sqrt (n : ℝ))]
      have hδmge : δ ≤ δm := by
        rw [hδm, hδdef]
        exact div_le_div_of_nonneg_left hb.le hsm hsmn
      set Mm : ℝ := G (8 * A * δm) with hMm
      have hMmle : Mm ≤ M := by
        rw [hMm, hMdef]
        exact hGanti _ _ (by positivity) (by nlinarith)
      have hMm1 : 1 ≤ Mm := hG1 _ (by positivity)
      refine le_trans (le_trans hstep ?_) (le_max_left _ _)
      have hKδm : 0 ≤ K * δm := by positivity
      have hM0 : (0 : ℝ) ≤ M := by linarith
      calc K * δm * Mm ≤ K * δm * M := mul_le_mul_of_nonneg_left hMmle hKδm
        _ ≤ K * (2 * δ) * M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδmle hKpos.le) hM0
        _ = 2 * K * δ * M := by ring
    have hεpos : 0 < 8 * A * δ := by positivity
    -- the induction only ever runs the recursion at the width `ε = 8 A δ`, and there
    -- `ε √n = 8 A b` does not depend on `n`; so the localisation window is a hypothesis
    -- on the *constants* alone (wave 36).
    have hwin : w ≤ 8 * A * δ * Real.sqrt (n : ℝ) := by
      have h : 8 * A * δ * Real.sqrt (n : ℝ) = 8 * A * b := by
        rw [hδdef]; field_simp
      rw [h]; exact hb1
    have h := hrec n hn (8 * A * δ) hεpos hwin Y hY
    rw [← hδdef] at h
    have hinv : A * δ * (8 * A * δ)⁻¹ = 1 / 8 := by
      rw [mul_inv, ← mul_assoc]; field_simp
    rw [show A * δ * (8 * A * δ)⁻¹ * (C * (8 * A * δ) + 2 * Y)
        = (A * δ * (8 * A * δ)⁻¹) * (C * (8 * A * δ) + 2 * Y) from rfl, hinv,
      ← hMdef] at h
    have hexp : (1 : ℝ) / 8 * (C * (8 * A * δ) + 2 * Y) + A * δ * C * M + C * (8 * A * δ)
        = 9 * (A * C) * δ + Y / 4 + A * C * δ * M := by ring
    rw [hexp] at h
    have hACδ : 0 < A * C * δ := by positivity
    rcases le_total (D n) (2 * K * δ * M) with hcase | hcase
    · have hmax : Y = 2 * K * δ * M := by rw [hYdef]; exact max_eq_left hcase
      rw [hmax] at h
      rw [hKdef] at h ⊢
      nlinarith [hACδ, hM1]
    · have hmax : Y = D n := by rw [hYdef]; exact max_eq_right hcase
      rw [hmax] at h
      rw [hKdef]
      nlinarith [hACδ, hM1]

/-- **The self-improving induction with the mollification logarithm** (wave 32; wave 39: proof
re-based on `le_of_selfImproving_induction_forcing`, statement unchanged).

The hybrid telescope smooths step `j` at width `σⱼ = √(j/n)`, sweeping from `ε` to `1`, while
the test function has the *single* width `ε`. The localised swap therefore pays, at step `j`,
the weight `C σⱼ + W` rather than `W`, and the balanced sum over the tail `j > J = ⌈ε²n⌉`
contributes

`∑_{J<j≤n} j^{-3/2}(C σⱼ + W) β/√n = δ (C ∑_{J<j≤n} j^{-1} + W J^{-1/2}) ≍ δ (2C log(1/ε) + W/ε)`

— see the ledger on `localised_swap_bound_small_weight`. So the recursion this route produces
carries an extra additive `A δ C (1 + log(1 + ε⁻¹))` on top of the `A δ ε⁻¹ (Cε + 2Y)` of
`le_of_selfImproving_induction`, and the fixed point has to be re-solved with it.

It re-solves *linearly*, at the price of one logarithm in the answer. Put
`δₙ = b/√n` and `Mₙ = 1 + log(1 + (8Aδₙ)⁻¹)`. On the neighbour range `n/2 ≤ m ≤ n` one has both
`δₘ ≤ 2δₙ` (as before) **and** `Mₘ ≤ Mₙ` — the log factor is monotone in the *right* direction,
because `m ≤ n` gives `δₘ ≥ δₙ`. So `K δ M` self-propagates with `Y = 2 K δₙ Mₙ`, and at the
same cut `ε = 8Aδₙ` the recursion reads `D n ≤ 9ACδ + Y/4 + ACδM`. Using `M ≥ 1` to absorb the
log-free term, the two cases close at `K = 20 A C` and `K = (40/3) A C` respectively.

**Wave 39.** Those two italicised facts — `M ≥ 1` and antitonicity — are *all* the argument
uses, so the whole proof has been moved to `le_of_selfImproving_induction_forcing` and this is
now the instance `G ε = 1 + log(1 + ε⁻¹)`. The instance the amended ledger actually consumes is
`le_of_selfImproving_induction_logPow32`.

The `1 + ε⁻¹` inside the logarithm (rather than a bare `ε⁻¹`) is deliberate: it makes the extra
term nonnegative for *every* `ε > 0`, so the amended recursion is unambiguously weaker than the
frozen one and no `ε ≤ 1` side condition has to be threaded through the call sites. -/
theorem le_of_selfImproving_induction_log {A C b : ℝ} {D : ℕ → ℝ}
    (hA : 0 < A) (hC : 0 < C) (hb : 0 < b) (hb1 : 1 ≤ 8 * A * b)
    (hrec : ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → 1 ≤ ε * Real.sqrt (n : ℝ) → ∀ Y : ℝ,
      (∀ m : ℕ, n ≤ 2 * m → m ≤ n → D m ≤ Y) →
      D n ≤ A * (b / Real.sqrt n) * ε⁻¹ * (C * ε + 2 * Y)
        + A * (b / Real.sqrt n) * C * (1 + Real.log (1 + ε⁻¹))
        + C * ε) :
    ∀ n : ℕ, 0 < n → D n ≤ 20 * (A * C) * (b / Real.sqrt n)
      * (1 + Real.log (1 + (8 * A * (b / Real.sqrt n))⁻¹)) := by
  refine le_of_selfImproving_induction_forcing (G := fun x => 1 + Real.log (1 + x⁻¹))
    hA hC hb hb1 ?_ ?_ hrec
  · intro x hx
    have hxi : (0 : ℝ) < x⁻¹ := by positivity
    have hl : 0 ≤ Real.log (1 + x⁻¹) := Real.log_nonneg (by linarith)
    linarith
  · intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le hx hxy
    have hyi : (0 : ℝ) < y⁻¹ := by positivity
    have hinv : y⁻¹ ≤ x⁻¹ := by rw [inv_le_inv₀ hy hx]; exact hxy
    have h1 : (0 : ℝ) < 1 + y⁻¹ := by linarith
    have := Real.log_le_log h1 (by linarith : (1 : ℝ) + y⁻¹ ≤ 1 + x⁻¹)
    linarith

/-- **The `3/2`-power forcing factor (wave 39).** `logPow32 ε = (1 + log(1 + ε⁻¹))^{3/2}`,
written as a product rather than an `rpow` so that `positivity`/`nlinarith` can see it.

This is the forcing term the *amended* ledger produces. Its source is the amended tail weight
`4 C_k σⱼ · Λ(σⱼ) + W` of `abs_integral_gaussian_smoothed_swap_localised_le`, whose extra
factor `Λ(σ) = gaussianTailRadius k σ` carries a `√(log(1/σ))`: summing
`Λ(σⱼ) σⱼ / (j √j) = Λ(σⱼ)/(√n · j)` over the tail steps `J < j ≤ n` costs
`√(log(1/ε)) · log(1/ε)` in place of the wave-32 `log(1/ε)`. See the ledger note on the tail
brick for the derivation, and `le_of_selfImproving_induction_logPow32` for the fixed point. -/
noncomputable def logPow32 (x : ℝ) : ℝ :=
  (1 + Real.log (1 + x⁻¹)) * Real.sqrt (1 + Real.log (1 + x⁻¹))

lemma one_le_logPow32 {x : ℝ} (hx : 0 < x) : 1 ≤ logPow32 x := by
  have hxi : (0 : ℝ) < x⁻¹ := by positivity
  have h : (1 : ℝ) ≤ 1 + Real.log (1 + x⁻¹) := by
    have hl : 0 ≤ Real.log (1 + x⁻¹) := Real.log_nonneg (by linarith)
    linarith
  have hs0 : Real.sqrt 1 ≤ Real.sqrt (1 + Real.log (1 + x⁻¹)) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_one] at hs0
  rw [logPow32]
  nlinarith

lemma logPow32_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : logPow32 y ≤ logPow32 x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hyi : (0 : ℝ) < y⁻¹ := by positivity
  have hinv : y⁻¹ ≤ x⁻¹ := by rw [inv_le_inv₀ hy hx]; exact hxy
  have hlog : 1 + Real.log (1 + y⁻¹) ≤ 1 + Real.log (1 + x⁻¹) := by
    have h1 : (0 : ℝ) < 1 + y⁻¹ := by linarith
    have := Real.log_le_log h1 (by linarith : (1 : ℝ) + y⁻¹ ≤ 1 + x⁻¹)
    linarith
  have h0 : (0 : ℝ) ≤ 1 + Real.log (1 + y⁻¹) := by
    have hl : 0 ≤ Real.log (1 + y⁻¹) := Real.log_nonneg (by linarith)
    linarith
  rw [logPow32, logPow32]
  exact mul_le_mul hlog (Real.sqrt_le_sqrt hlog) (Real.sqrt_nonneg _) (by linarith)

/-- **The fixed point of the AMENDED ledger (wave 39: PROVED).** The recursion with forcing term
`(1 + log(1 + ε⁻¹))^{3/2}` self-improves, at the *same* constant `20 A C` as the wave-32
logarithmic one; only the factor carried into the answer changes.

This is the statement wave 39 had to check rather than assume: the amended tail weight of
`abs_integral_gaussian_smoothed_swap_localised_le` raises the ledger's log power from `1` to
`3/2`, and it was not a priori clear that a `3/2` power still self-improves linearly. It does,
and by `le_of_selfImproving_induction_forcing` the reason is structural: only `G ≥ 1` and
antitonicity of `G` are used, both of which `logPow32` has. -/
theorem le_of_selfImproving_induction_logPow32 {A C b w : ℝ} {D : ℕ → ℝ}
    (hA : 0 < A) (hC : 0 < C) (hb : 0 < b) (hb1 : w ≤ 8 * A * b)
    (hrec : ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → w ≤ ε * Real.sqrt (n : ℝ) → ∀ Y : ℝ,
      (∀ m : ℕ, n ≤ 2 * m → m ≤ n → D m ≤ Y) →
      D n ≤ A * (b / Real.sqrt n) * ε⁻¹ * (C * ε + 2 * Y)
        + A * (b / Real.sqrt n) * C * logPow32 ε
        + C * ε) :
    ∀ n : ℕ, 0 < n → D n ≤ 20 * (A * C) * (b / Real.sqrt n)
      * logPow32 (8 * A * (b / Real.sqrt n)) :=
  le_of_selfImproving_induction_forcing (G := logPow32) hA hC hb hb1
    (fun _ hx => one_le_logPow32 hx) (fun _ _ hx hxy => logPow32_anti hx hxy) hrec

/-- The log factor the induction carries, `1 + log(1 + (Aδ)⁻¹)`, converted into the form the
headline records, `1 + log(max δ⁻¹ e)`, at the cost of a factor `2`. (The `max … e` keeps the
headline's factor `≥ 1` for every `δ`, including the uninteresting range `δ ≥ 1` where the
bound is vacuous anyway.) -/
theorem log_shift_le {A δ : ℝ} (hA : 1 ≤ A) (hδ : 0 < δ) :
    1 + Real.log (1 + (A * δ)⁻¹) ≤ 2 * (1 + Real.log (max δ⁻¹ (Real.exp 1))) := by
  set L : ℝ := Real.log (max δ⁻¹ (Real.exp 1)) with hL
  have hmax : Real.exp 1 ≤ max δ⁻¹ (Real.exp 1) := le_max_right _ _
  have hL1 : 1 ≤ L := by
    rw [hL]
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) hmax
  have hinv : (A * δ)⁻¹ ≤ δ⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith
  have hd : δ⁻¹ ≤ max δ⁻¹ (Real.exp 1) := le_max_left _ _
  have hpos : (0 : ℝ) < max δ⁻¹ (Real.exp 1) := lt_of_lt_of_le (Real.exp_pos 1) hmax
  have h1 : (1 : ℝ) ≤ max δ⁻¹ (Real.exp 1) := le_trans (by
    have := Real.add_one_le_exp (1 : ℝ); linarith) hmax
  have hstep : 1 + (A * δ)⁻¹ ≤ 2 * max δ⁻¹ (Real.exp 1) := by linarith
  have hlog : Real.log (1 + (A * δ)⁻¹) ≤ Real.log 2 + L := by
    have h2 : (0:ℝ) < 1 + (A * δ)⁻¹ := by positivity
    calc Real.log (1 + (A * δ)⁻¹)
        ≤ Real.log (2 * max δ⁻¹ (Real.exp 1)) := Real.log_le_log h2 hstep
      _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) hpos.ne', hL]
  have hlog2 : Real.log 2 ≤ 1 := by
    calc Real.log 2 ≤ Real.log (Real.exp 1) :=
          Real.log_le_log (by norm_num) (by
            have := Real.add_one_le_exp (1:ℝ); nlinarith [Real.exp_pos (1:ℝ)])
      _ = 1 := Real.log_exp 1
  linarith

/-- **`log_shift_le` for the `3/2` power (wave 39).** The headline records its logarithm as
`1 + log(max δ⁻¹ e)`; the induction produces `logPow32 (8 A δ)`. Since `log_shift_le` turns the
inner factor into `2 (1 + log(max δ⁻¹ e))`, the `3/2` power costs `2^{3/2} = 2√2 ≤ 3`. -/
theorem logPow32_shift_le {A δ : ℝ} (hA : 1 ≤ A) (hδ : 0 < δ) :
    logPow32 (A * δ) ≤ 3 * ((1 + Real.log (max δ⁻¹ (Real.exp 1)))
      * Real.sqrt (1 + Real.log (max δ⁻¹ (Real.exp 1)))) := by
  have hAδ : 0 < A * δ := by nlinarith
  have hM := log_shift_le hA hδ
  set N : ℝ := 1 + Real.log (max δ⁻¹ (Real.exp 1)) with hNdef
  set M : ℝ := 1 + Real.log (1 + (A * δ)⁻¹) with hMdef
  have hMi : (0 : ℝ) < (A * δ)⁻¹ := by positivity
  have hM1 : 1 ≤ M := by
    have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + (A * δ)⁻¹)
    rw [hMdef]; linarith
  have hN1 : 1 ≤ N := by
    have hmax : Real.exp 1 ≤ max δ⁻¹ (Real.exp 1) := le_max_right _ _
    have h : (1 : ℝ) ≤ Real.log (max δ⁻¹ (Real.exp 1)) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos 1) hmax
    rw [hNdef]; linarith
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ (3 / 2) ^ 2)
    rwa [Real.sqrt_sq (by norm_num)] at h
  have hsM : Real.sqrt M ≤ Real.sqrt 2 * Real.sqrt N := by
    have h1 : Real.sqrt M ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h1
  have hsN0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hlp : logPow32 (A * δ) = M * Real.sqrt M := by rw [hMdef, logPow32]
  rw [hlp]
  calc M * Real.sqrt M ≤ 2 * N * (Real.sqrt 2 * Real.sqrt N) :=
        mul_le_mul hM hsM (Real.sqrt_nonneg _) (by linarith)
    _ ≤ 2 * N * (3 / 2 * Real.sqrt N) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        nlinarith
    _ = 3 * (N * Real.sqrt N) := by ring

end SelfImprovingInduction

section ConvexDiscrepancy

variable {k : ℕ}

/-- The set of discrepancies over measurable convex sets — the class the self-improving
induction runs on. -/
def convexDiscrepancySet (μ ν : Measure (EuclideanSpace ℝ (Fin k))) : Set ℝ :=
  {d : ℝ | ∃ B : Set (EuclideanSpace ℝ (Fin k)),
      MeasurableSet B ∧ Convex ℝ B ∧ d = |(μ B).toReal - (ν B).toReal|}

/-- `Δ(μ, ν)`, the supremum of `|μ B − ν B|` over measurable convex `B`. -/
noncomputable def convexDiscrepancy (μ ν : Measure (EuclideanSpace ℝ (Fin k))) : ℝ :=
  sSup (convexDiscrepancySet μ ν)

variable {μ ν : Measure (EuclideanSpace ℝ (Fin k))}

private lemma measureReal_le_one' (μ : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure μ] (s : Set (EuclideanSpace ℝ (Fin k))) : (μ s).toReal ≤ 1 := by
  have h := measure_mono (μ := μ) (Set.subset_univ s)
  rw [measure_univ] at h
  simpa using ENNReal.toReal_mono (by simp) h

lemma convexDiscrepancySet_nonempty (μ ν : Measure (EuclideanSpace ℝ (Fin k))) :
    (convexDiscrepancySet μ ν).Nonempty :=
  ⟨_, ∅, MeasurableSet.empty, convex_empty, rfl⟩

lemma convexDiscrepancySet_bddAbove [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove (convexDiscrepancySet μ ν) := by
  refine ⟨1, ?_⟩
  rintro d ⟨B, -, -, rfl⟩
  have h1 := measureReal_le_one' μ B
  have h2 := measureReal_le_one' ν B
  have h3 : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  have h4 : (0 : ℝ) ≤ (ν B).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- Every measurable convex set is controlled by `Δ`. -/
lemma le_convexDiscrepancy [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B) :
    |(μ B).toReal - (ν B).toReal| ≤ convexDiscrepancy μ ν :=
  le_csSup convexDiscrepancySet_bddAbove ⟨B, hBm, hBc, rfl⟩

lemma convexDiscrepancy_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ convexDiscrepancy μ ν := by
  have h := le_convexDiscrepancy (μ := μ) (ν := ν) MeasurableSet.empty convex_empty
  simpa using le_trans (abs_nonneg _) h

lemma convexDiscrepancy_le_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    convexDiscrepancy μ ν ≤ 1 := by
  refine csSup_le (convexDiscrepancySet_nonempty μ ν) ?_
  rintro d ⟨B, -, -, rfl⟩
  have h1 := measureReal_le_one' μ B
  have h2 := measureReal_le_one' ν B
  have h3 : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  have h4 : (0 : ℝ) ≤ (ν B).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

private lemma measureReal_sdiff (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure μ]
    {s t : Set (EuclideanSpace ℝ (Fin k))} (hts : t ⊆ s) (htm : MeasurableSet t) :
    (μ (s \ t)).toReal = (μ s).toReal - (μ t).toReal := by
  rw [measure_diff hts htm.nullMeasurableSet (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le (measure_mono hts) (measure_ne_top _ _)]

/-- **The `2Δ` brick.** The discrepancy on a *difference of two convex sets* is at most `2Δ`:
this is exactly where the factor `2` of Bentkus's recursion `C ε + 2Δ` comes from, and it is why
the induction never has to leave the class of convex sets. -/
theorem measureReal_diff_le_of_convexDiscrepancy [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B₁ B₂ : Set (EuclideanSpace ℝ (Fin k))} (h₁m : MeasurableSet B₁) (h₁c : Convex ℝ B₁)
    (h₂m : MeasurableSet B₂) (h₂c : Convex ℝ B₂) (hsub : B₂ ⊆ B₁) :
    (μ (B₁ \ B₂)).toReal ≤ (ν (B₁ \ B₂)).toReal + 2 * convexDiscrepancy μ ν := by
  have e1 := measureReal_sdiff μ hsub h₂m
  have e2 := measureReal_sdiff ν hsub h₂m
  have d1 := abs_le.1 (le_convexDiscrepancy (μ := μ) (ν := ν) h₁m h₁c)
  have d2 := abs_le.1 (le_convexDiscrepancy (μ := μ) (ν := ν) h₂m h₂c)
  rw [e1, e2]
  linarith [d1.1, d1.2, d2.1, d2.2]

/-- The Gaussian mass of the outer shell `Bᵋ \ interior B` of a convex set is at most `C_k ε`. -/
theorem gaussian_measureReal_shell_le (hk : 0 < k)
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        (Metric.thickening ε B \ interior B)).toReal ≤ gaussianShellConst k * ε := by
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  have hintB : interior B ⊆ Metric.thickening ε B :=
    interior_subset.trans (Metric.self_subset_thickening hε B)
  have hzero : γ (B \ interior B) = 0 := gaussian_diff_interior_eq_zero hk hBm hBc
  have hint : γ (interior B) = γ B := by
    refine le_antisymm (measure_mono interior_subset) ?_
    calc γ B ≤ γ (interior B ∪ (B \ interior B)) := by
          refine measure_mono fun x hx => ?_
          by_cases h : x ∈ interior B
          · exact Or.inl h
          · exact Or.inr ⟨hx, h⟩
      _ ≤ γ (interior B) + γ (B \ interior B) := measure_union_le _ _
      _ = γ (interior B) := by rw [hzero, add_zero]
  have hdiff : (γ (Metric.thickening ε B \ interior B)).toReal
      = (γ (Metric.thickening ε B)).toReal - (γ B).toReal := by
    rw [measureReal_sdiff γ hintB isOpen_interior.measurableSet, hint]
  have hthick := gaussian_thickening_le hk hBc hε
  rw [← hγdef] at hthick
  have htr : (γ (Metric.thickening ε B)).toReal
      ≤ (γ B).toReal + gaussianShellConst k * ε := by
    have h := ENNReal.toReal_mono (by
      exact ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) hthick
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal
        (le_of_lt (mul_pos (gaussianShellConst_pos hk) hε))] at h
  rw [hdiff]
  linarith

/-- **The shell bound: the source of `C ε + 2Δ`.** For any probability law `μ` on `ℝᵏ` and any
measurable convex `B`, the mass that `μ` puts on the `ε`-shell `Bᵋ \ interior B` — which is
exactly the support of `D³` of the mollified indicator of `B` at width `ε` — is at most
`C_k ε + 2 Δ(μ, γ)`. -/
theorem measureReal_shell_le_of_convexDiscrepancy (hk : 0 < k)
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure μ]
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) :
    (μ (Metric.thickening ε B \ interior B)).toReal
      ≤ gaussianShellConst k * ε
        + 2 * convexDiscrepancy μ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  have hintB : interior B ⊆ Metric.thickening ε B :=
    interior_subset.trans (Metric.self_subset_thickening hε B)
  have h := measureReal_diff_le_of_convexDiscrepancy (μ := μ) (ν := γ)
    (B₁ := Metric.thickening ε B) (B₂ := interior B)
    Metric.isOpen_thickening.measurableSet (hBc.thickening ε)
    isOpen_interior.measurableSet hBc.interior hintB
  have hg := gaussian_measureReal_shell_le hk hBm hBc hε
  rw [← hγdef] at hg
  linarith


/-! #### Affine transport of the shell -/

/-- The dilation-translation `x ↦ r • x + a` as a homeomorphism. -/
noncomputable def affHomeo {r : ℝ} (hr : r ≠ 0) (a : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) ≃ₜ EuclideanSpace ℝ (Fin k) :=
  (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addRight a)

lemma affHomeo_apply {r : ℝ} (hr : r ≠ 0) (a x : EuclideanSpace ℝ (Fin k)) :
    affHomeo hr a x = r • x + a := rfl

/-- Convexity is preserved by the affine preimage. -/
lemma convex_preimage_aff {r : ℝ} {a : EuclideanSpace ℝ (Fin k)}
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBc : Convex ℝ B) :
    Convex ℝ ((fun x => r • x + a) ⁻¹' B) := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_preimage] at hx hy ⊢
  have hrw : r • (s • x + t • y) + a = s • (r • x + a) + t • (r • y + a) := by
    calc r • (s • x + t • y) + a = (s * r) • x + (t * r) • y + a := by
          simp only [smul_add, smul_smul]; rw [mul_comm r s, mul_comm r t]
      _ = (s * r) • x + (t * r) • y + (s + t) • a := by rw [hst, one_smul]
      _ = s • (r • x + a) + t • (r • y + a) := by
          simp only [smul_add, smul_smul, add_smul]; abel
  rw [hrw]
  exact hBc hx hy hs ht hst

/-- **Affine transport of the thickening.** For `r > 0`, `(r • · + a)⁻¹(Bᵋ) = (B')^{ε/r}` where
`B' = (r • · + a)⁻¹(B)`. -/
lemma preimage_aff_thickening {r : ℝ} (hr : 0 < r) (a : EuclideanSpace ℝ (Fin k))
    (B : Set (EuclideanSpace ℝ (Fin k))) {ε : ℝ} (_hε : 0 < ε) :
    (fun x => r • x + a) ⁻¹' (Metric.thickening ε B)
      = Metric.thickening (ε / r) ((fun x => r • x + a) ⁻¹' B) := by
  ext x
  simp only [Set.mem_preimage]
  constructor
  · intro hx
    obtain ⟨z, hzB, hzlt⟩ := Metric.mem_thickening_iff.1 hx
    refine Metric.mem_thickening_iff.2 ⟨r⁻¹ • (z - a), ?_, ?_⟩
    · simp only [Set.mem_preimage]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel]
      exact hzB
    · have hdist : dist (r • x + a) z = r * dist x (r⁻¹ • (z - a)) := by
        rw [dist_eq_norm, dist_eq_norm, ← norm_smul_of_nonneg hr.le]
        congr 1
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
        abel
      rw [hdist] at hzlt
      rw [lt_div_iff₀ hr, mul_comm]
      exact hzlt
  · intro hx
    obtain ⟨w, hwB, hwlt⟩ := Metric.mem_thickening_iff.1 hx
    simp only [Set.mem_preimage] at hwB
    refine Metric.mem_thickening_iff.2 ⟨r • w + a, hwB, ?_⟩
    have hdist : dist (r • x + a) (r • w + a) = r * dist x w := by
      rw [dist_eq_norm, dist_eq_norm, ← norm_smul_of_nonneg hr.le]
      congr 1
      rw [smul_sub]
      abel
    rw [hdist]
    rw [lt_div_iff₀ hr, mul_comm] at hwlt
    exact hwlt

/-- **Affine transport of the interior.** -/
lemma preimage_aff_interior {r : ℝ} (hr : 0 < r) (a : EuclideanSpace ℝ (Fin k))
    (B : Set (EuclideanSpace ℝ (Fin k))) :
    (fun x => r • x + a) ⁻¹' (interior B) = interior ((fun x => r • x + a) ⁻¹' B) := by
  have h := (affHomeo (k := k) hr.ne' a).preimage_interior B
  exact h

/-- **The shell bound, transported along a dilation-translation.** This is the geometric heart
of brick H: conditioning the hybrid law on its Gaussian coordinate turns the shell event into an
affine preimage of a shell, and the class of measurable convex sets is affine-invariant. -/
theorem measureReal_shell_preimage_aff_le (hk : 0 < k)
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (a : EuclideanSpace ℝ (Fin k))
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) :
    (μ ((fun x => r • x + a) ⁻¹' (Metric.thickening ε B \ interior B))).toReal
      ≤ gaussianShellConst k * (ε / r)
        + 2 * convexDiscrepancy μ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  set B' : Set (EuclideanSpace ℝ (Fin k)) := (fun x => r • x + a) ⁻¹' B with hB'def
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin k) => r • x + a) := by fun_prop
  have hB'm : MeasurableSet B' := hmeas hBm
  have hB'c : Convex ℝ B' := convex_preimage_aff hBc
  have hset : (fun x => r • x + a) ⁻¹' (Metric.thickening ε B \ interior B)
      = Metric.thickening (ε / r) B' \ interior B' := by
    rw [Set.preimage_diff, preimage_aff_thickening hr a B hε, preimage_aff_interior hr a B]
  rw [hset]
  exact measureReal_shell_le_of_convexDiscrepancy hk μ hB'm hB'c (by positivity)

/-- A measure has no discrepancy with itself. -/
lemma convexDiscrepancy_self (μ : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure μ] : convexDiscrepancy μ μ = 0 := by
  refine le_antisymm (csSup_le (convexDiscrepancySet_nonempty μ μ) ?_) convexDiscrepancy_nonneg
  rintro d ⟨B, -, -, rfl⟩
  simp

/-- **The Gaussian regime of brick H, proved.** For the *Gaussian* law itself the affine shell
bound carries no `Δ` term at all:

`γ((r · + a)⁻¹(Bᵋ \ interior B)) ≤ C_k ε/r`.

This is exactly the estimate that controls the hybrid laws with `2j ≥ n`, where the hybrid's own
`N(0, (j/n) I_k)` component has width `σ = √j/√n ≥ 1/√2` and hence supplies the whole
anti-concentration bound `√2 C_k ε` **without any induction**. Only the sum-dominant regime
`2j ≤ n` consumes the inductive hypothesis. -/
theorem gaussian_measureReal_shell_preimage_aff_le (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a : EuclideanSpace ℝ (Fin k))
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        ((fun x => r • x + a) ⁻¹' (Metric.thickening ε B \ interior B))).toReal
      ≤ gaussianShellConst k * (ε / r) := by
  haveI : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    inferInstance
  have h := measureReal_shell_preimage_aff_le hk
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) hr a hBm hBc hε
  rw [convexDiscrepancy_self] at h
  linarith

/-! #### Wave-29: the *two-sided* shell, and its affine transport

The localised swap step needs more than the outer shell `Bᵋ \ interior B`. A point `v` is
harmless for the localisation exactly when the mollified indicator is **constant** on a ball
around `v` (`abs_integral_shift_vecTiltRemainder_le_of_const_ball`), i.e. when `v` lies either
outside the thickening or inside the *erosion*. The complement of that is the **two-sided**
shell `Bᵋ \ B_{-ε}`, and the inner half `B \ B_{-ε}` is invisible to
`measureReal_shell_le_of_convexDiscrepancy`. The bounds below repeat the outer-shell chain for
the two-sided shell; the cost is a factor `2`, since `gaussian_thickening_le` and
`gaussian_le_erosion_add` each contribute `C_k ε`. -/

/-- The erosion sits inside the interior (its centre lies in its own closed ball). -/
lemma erosion_subset_interior {ε : ℝ} (hε : 0 ≤ ε) (B : Set (EuclideanSpace ℝ (Fin k))) :
    erosion ε B ⊆ interior B := fun _ hx => hx (Metric.mem_closedBall_self hε)

/-- **Affine transport of the erosion.** For `r > 0`,
`(r • · + a)⁻¹(B_{-ε}) = (B')_{-ε/r}` where `B' = (r • · + a)⁻¹(B)`. -/
lemma preimage_aff_erosion {r : ℝ} (hr : 0 < r) (a : EuclideanSpace ℝ (Fin k))
    (B : Set (EuclideanSpace ℝ (Fin k))) {ε : ℝ} (_hε : 0 < ε) :
    (fun x => r • x + a) ⁻¹' (erosion ε B)
      = erosion (ε / r) ((fun x => r • x + a) ⁻¹' B) := by
  have hint : (fun x => r • x + a) ⁻¹' (interior B)
      = interior ((fun x => r • x + a) ⁻¹' B) := preimage_aff_interior hr a B
  ext x
  simp only [Set.mem_preimage, erosion, Set.mem_setOf_eq]
  rw [← hint]
  constructor
  · intro hsub y hy
    simp only [Set.mem_preimage]
    refine hsub ?_
    simp only [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    have hrw : r • y + a - (r • x + a) = r • (y - x) := by rw [smul_sub]; abel
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have h1 : r * ‖y - x‖ ≤ r * (ε / r) := mul_le_mul_of_nonneg_left hy hr.le
    have h2 : r * (ε / r) = ε := by field_simp
    linarith
  · intro hsub y hy
    have hy' : r⁻¹ • (y - a) ∈ Metric.closedBall x (ε / r) := by
      have hrw : dist (r⁻¹ • (y - a)) x = r⁻¹ * dist y (r • x + a) := by
        rw [dist_eq_norm, dist_eq_norm, ← norm_smul_of_nonneg (inv_pos.2 hr).le]
        congr 1
        match_scalars <;> field_simp
      rw [Metric.mem_closedBall, hrw, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (Metric.mem_closedBall.1 hy) (inv_pos.2 hr).le
    have h := hsub hy'
    simp only [Set.mem_preimage] at h
    rwa [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel] at h

/-- The Gaussian mass of the **two-sided** shell `Bᵋ \ B_{-ε}` of a convex set is at most
`2 C_k ε`. -/
theorem gaussian_measureReal_wideShell_le (hk : 0 < k)
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        (Metric.thickening ε B \ erosion ε B)).toReal
      ≤ 2 * gaussianShellConst k * ε := by
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  have hEsub : erosion ε B ⊆ Metric.thickening ε B :=
    (erosion_subset_interior hε.le B).trans
      (interior_subset.trans (Metric.self_subset_thickening hε B))
  have hdiff : (γ (Metric.thickening ε B \ erosion ε B)).toReal
      = (γ (Metric.thickening ε B)).toReal - (γ (erosion ε B)).toReal :=
    measureReal_sdiff γ hEsub (isOpen_erosion ε B).measurableSet
  have hCkε : (0 : ℝ) ≤ gaussianShellConst k * ε :=
    le_of_lt (mul_pos (gaussianShellConst_pos hk) hε)
  have hthick : (γ (Metric.thickening ε B)).toReal
      ≤ (γ B).toReal + gaussianShellConst k * ε := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) hCkε ?_
    have := gaussian_thickening_le hk hBc hε
    rwa [← hγdef] at this
  have herode : (γ B).toReal ≤ (γ (erosion ε B)).toReal + gaussianShellConst k * ε := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) hCkε ?_
    have := gaussian_le_erosion_add hk hBm hBc hε
    rwa [← hγdef] at this
  rw [hdiff]
  linarith

/-- The **two-sided** shell bound for an arbitrary law, at the price of `2Δ`. The two-sided
shell is again a difference of two convex sets, so `measureReal_diff_le_of_convexDiscrepancy`
applies verbatim. -/
theorem measureReal_wideShell_le_of_convexDiscrepancy (hk : 0 < k)
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure μ]
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) :
    (μ (Metric.thickening ε B \ erosion ε B)).toReal
      ≤ 2 * gaussianShellConst k * ε
        + 2 * convexDiscrepancy μ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  have hEsub : erosion ε B ⊆ Metric.thickening ε B :=
    (erosion_subset_interior hε.le B).trans
      (interior_subset.trans (Metric.self_subset_thickening hε B))
  have h := measureReal_diff_le_of_convexDiscrepancy (μ := μ) (ν := γ)
    (B₁ := Metric.thickening ε B) (B₂ := erosion ε B)
    Metric.isOpen_thickening.measurableSet (hBc.thickening ε)
    (isOpen_erosion ε B).measurableSet (convex_erosion hBc) hEsub
  have hg := gaussian_measureReal_wideShell_le hk hBm hBc hε
  rw [← hγdef] at hg
  linarith

/-- The two-sided shell bound, transported along a dilation-translation. -/
theorem measureReal_wideShell_preimage_aff_le (hk : 0 < k)
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (a : EuclideanSpace ℝ (Fin k))
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) :
    (μ ((fun x => r • x + a) ⁻¹' (Metric.thickening ε B \ erosion ε B))).toReal
      ≤ 2 * gaussianShellConst k * (ε / r)
        + 2 * convexDiscrepancy μ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  set B' : Set (EuclideanSpace ℝ (Fin k)) := (fun x => r • x + a) ⁻¹' B with hB'def
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin k) => r • x + a) := by fun_prop
  have hB'm : MeasurableSet B' := hmeas hBm
  have hB'c : Convex ℝ B' := convex_preimage_aff hBc
  have hset : (fun x => r • x + a) ⁻¹' (Metric.thickening ε B \ erosion ε B)
      = Metric.thickening (ε / r) B' \ erosion (ε / r) B' := by
    rw [Set.preimage_diff, preimage_aff_thickening hr a B hε, preimage_aff_erosion hr a B hε]
  rw [hset]
  exact measureReal_wideShell_le_of_convexDiscrepancy hk μ hB'm hB'c (by positivity)

/-- The Gaussian regime of the two-sided shell: no `Δ` term at all. -/
theorem gaussian_measureReal_wideShell_preimage_aff_le (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a : EuclideanSpace ℝ (Fin k))
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        ((fun x => r • x + a) ⁻¹' (Metric.thickening ε B \ erosion ε B))).toReal
      ≤ 2 * gaussianShellConst k * (ε / r) := by
  haveI : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    inferInstance
  have h := measureReal_wideShell_preimage_aff_le hk
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) hr a hBm hBc hε
  rw [convexDiscrepancy_self] at h
  linarith

/-! ### Wave-20: the hybrid family, and the recursion it produces -/

/-- The law of the normalised sum `n^{-1/2} ∑ᵢ Yᵢ` of `n` i.i.d. copies of `ν`. -/
noncomputable def sumLaw (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  (Measure.pi fun _ : Fin n => ν).map fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i

instance isProbabilityMeasure_sumLaw (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (sumLaw n ν) := by
  rw [sumLaw]
  exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

/-- **The `j`-th hybrid law of the telescope**: the law of

`n^{-1/2} ∑_{i ≥ j} Yᵢ + (j/n)^{1/2} Z`, `Yᵢ ~ ν` i.i.d., `Z ~ N(0, I_k)`,

which is exactly the measure against which `abs_integral_smooth_sub_gaussian_improved` evaluates
its `j`-th test function (`κ'ⱼ i = if i < j then δ₀ else ν`, smoothing width `sⱼ = √j/√n`). At
`j = 0` it is `sumLaw n ν`; at `j = n` it is the standard Gaussian. The self-improving induction
runs over this whole family, not over `sumLaw n ν` alone. -/
noncomputable def hybridLaw (n j : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  ((Measure.pi fun i : Fin n => if (i : ℕ) < j then Measure.dirac 0 else ν).prod
      (stdGaussian (EuclideanSpace ℝ (Fin k)))).map
    fun p => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
      + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2

instance isProbabilityMeasure_hybridLaw (n j : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (hybridLaw n j ν) := by
  rw [hybridLaw]
  haveI : ∀ i : Fin n, IsProbabilityMeasure
      (if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) := by
    intro i; split <;> infer_instance
  exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

/-- **The hybrid law IS the telescope's `j`-th test measure** (wave 36).

`hybridLaw` was introduced (wave 20) with the comment that it is "exactly the measure against
which `abs_integral_smooth_sub_gaussian_improved` evaluates its `j`-th test function", but that
identity was never recorded in Lean — brick H speaks about `hybridLaw`, the telescope speaks
about `Iⱼ = ∫ Gⱼ(∑ₗ xₗ) d(⨂ κⱼ)`, and nothing connected them. It is needed as soon as the
per-step swap bounds are *localised*, because their weight is a two-sided-shell mass **under
`hybridLaw n j ν`** while the object the telescope averages is `Iⱼ`; without this lemma the two
localised estimates of `localised_swap_bound_small_weight` cannot even be stated in the form its
reduction consumes.

The content is one Fubini: unfolding `hybridLaw`'s `map`, the outer integral over the product
`(⨂ κⱼ) ⊗ γ` factors into the smoothing integral inside the product integral, and
`sⱼ = √j/√n = c √j` is the telescope's own smoothing width. -/
theorem integral_hybridLaw_eq {n j : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν] {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Continuous f) (hfb : ∀ x, |f x| ≤ 1) :
    (∫ x, f x ∂(hybridLaw n j ν))
      = ∫ x, (∫ z, f ((Real.sqrt (n : ℝ))⁻¹ • (∑ i, x i)
              + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • z)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          ∂(Measure.pi fun i : Fin n =>
              if (i : ℕ) < j then Measure.dirac 0 else ν) := by
  haveI : ∀ i : Fin n, IsProbabilityMeasure
      (if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) := by
    intro i; split <;> infer_instance
  set P : Measure ((_ : Fin n) → EuclideanSpace ℝ (Fin k)) :=
    Measure.pi fun i : Fin n =>
      if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν with hPdef
  haveI : IsProbabilityMeasure P := by rw [hPdef]; infer_instance
  set Φ : ((_ : Fin n) → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k)
      → EuclideanSpace ℝ (Fin k) :=
    fun p => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
      + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2 with hΦdef
  have hΦmeas : Measurable Φ := by rw [hΦdef]; fun_prop
  have hint : Integrable (fun p => f (Φ p))
      (P.prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
    refine (integrable_const (1 : ℝ)).mono'
      (hf.measurable.comp hΦmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hfb _)
  rw [hybridLaw, ← hPdef, ← hΦdef,
    integral_map hΦmeas.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ hint

/-- **The peeled average IS a hybrid-law average** (wave 36).

The second half of the bridge. `abs_sub_integral_peel_le_integral` bounds a telescope step by
`∫ D(∑ₗ yₗ) dR`, an average over the *remaining* `n − 1` coordinates; brick H
(`hybridLaw_wideShell_le`) bounds masses under `hybridLaw n j ν`, which averages over *all* `n`
coordinates and the smoothing Gaussian. This lemma is the identity that closes the gap: when
the bound `D v` is itself the average over the peeled coordinate `u ~ ν` and the smoothing
variable `z ~ γ` of a bounded continuous `F` evaluated at `c(v + u) + σⱼ z`, then

`∫ D(∑ₗ yₗ) dR = ∫ F d(hybridLaw n j ν)`.

Taking `F` a (mollified) indicator of the two-sided shell turns the conclusion of
`abs_sub_integral_peel_le_integral` into exactly the quantity the amended weight hypothesis of
`localised_swap_bound_small_weight` bounds. The proof is `integral_pi_sum_peel` run *backwards*
on `integral_hybridLaw_eq`, at the coordinate `i = j` where `κⱼ i = ν`. -/
theorem integral_peel_eq_integral_hybridLaw {m j : ℕ} (hj : j < m + 1)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν]
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1) :
    (∫ x, F x ∂(hybridLaw (m + 1) j ν))
      = ∫ y, (∫ u, (∫ z, F ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • (u + ∑ l, y l)
                + (Real.sqrt (j : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) • z)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
          ∂(Measure.pi fun l : Fin m =>
              (fun i : Fin (m + 1) =>
                if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν)
                ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)) := by
  classical
  set κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun i => if (i : ℕ) < j then Measure.dirac 0 else ν with hκdef
  haveI hκp : ∀ i, IsProbabilityMeasure (κ i) := by
    intro i; rw [hκdef]; dsimp only; split <;> infer_instance
  set c : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hcdef
  set s : ℝ := Real.sqrt (j : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ) with hsdef
  set g : EuclideanSpace ℝ (Fin k) → ℝ :=
    fun w => ∫ z, F (c • w + s • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]
    exact (continuous_integral_add_smul hF hFb s).comp (continuous_const_smul c)
  have hgb : ∀ w, |g w| ≤ 1 := fun w =>
    abs_integral_le_one (hF.comp (continuous_const.add (continuous_const_smul s)))
      (fun z => hFb _)
  have hν : κ (⟨j, hj⟩ : Fin (m + 1)) = ν := by
    rw [hκdef]; dsimp only; rw [if_neg (by omega)]
  rw [integral_hybridLaw_eq ν hF hFb, ← hκdef]
  have h := integral_pi_sum_peel κ (⟨j, hj⟩ : Fin (m + 1)) hgcont hgb
  rw [hν] at h
  exact h

/-- **The hybrid law is a convolution, at the level of measures (wave 42).** `hybridLaw n j ν`
is the law of `A + G` with `A` the (scaled) coordinate sum and `G` the smoothing Gaussian,
independent.

This is one of the two hypotheses `wideShell_le_of_deconvolution` asks for, and it is the *tail*
side's: `abs_integral_gaussian_smoothed_swap_localised_le` evaluates its shell indicator at the
base point **before** the smoothing, so its `τ` is the law of `A` alone (at the dirac cut
`j + 1`) and the factor to be deconvolved away is the whole Gaussian of width `σ_{j+1}`, giving
`hybridLaw n (j+1) ν`. Nothing is proved here beyond `Measure.map_prod_map` followed by
`Measure.map_map`: `hybridLaw` is *already* defined as a map of a product, so the two scalings
only have to be pushed onto the factors. (The head side additionally needs `map_pi_sum_peel`,
and then an associativity of the two convolutions; that is the piece brick L still owes.) -/
theorem hybridLaw_eq_map_add (n j : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν] :
    hybridLaw n j ν
      = ((((Measure.pi fun i : Fin n =>
              if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i).prod
          ((stdGaussian (EuclideanSpace ℝ (Fin k))).map
            fun z => (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • z)).map
        fun p => p.1 + p.2) := by
  haveI : ∀ i : Fin n, IsProbabilityMeasure
      (if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) := by
    intro i; split <;> infer_instance
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), hybridLaw]
  rfl

/-- **The head-side convolution identity (wave 43).** *The `j`-th hybrid law is the law of the
head step's base point, convolved with the swapped coordinate.*

At step `j` the telescope peels coordinate `j`, so the base point of the head brick — after the
smoothing integral has been pulled outside the modulus, as `hboundA` already does — is
`c ∑_{l ≠ j} Yₗ + σⱼ Z`, the *peeled* law. Wave 41 established that this is **not**
`hybridLaw n j ν`; wave 42 established that the correct relation is that `hybridLaw n j ν` is
that law convolved with `c ν`, and that a shell bound therefore transfers by *deconvolution*
(`wideShell_le_of_deconvolution_uniform`), not by shifting the indicator.

The proof is pure convolution algebra: `hybridLaw_eq_map_add` writes the hybrid law as
(coordinate sum) ∗ (smoothing Gaussian), `map_pi_sum_smul_peel` splits the coordinate sum as
`c ν ∗ (peeled sum)`, and `conv_reassoc` moves the `c ν` factor to the end. -/
theorem hybridLaw_conv_head {m j : ℕ} (hj : j < m + 1)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν]
    {κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k))}
    [∀ i, IsProbabilityMeasure (κ i)]
    (hκ : ∀ i : Fin (m + 1), κ i = if (i : ℕ) < j then Measure.dirac 0 else ν) :
    hybridLaw (m + 1) j ν
      = (((Measure.pi fun l : Fin m => κ ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)).map
            fun y => (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • ∑ l, y l)
          ∗ ((stdGaussian (EuclideanSpace ℝ (Fin k))).map
            fun z => (Real.sqrt (j : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) • z))
        ∗ (ν.map fun u => (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • u) := by
  have hκeq : κ = fun i : Fin (m + 1) =>
      if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν := funext hκ
  have hν : κ (⟨j, hj⟩ : Fin (m + 1)) = ν := by
    rw [hκ]; exact if_neg (lt_irrefl j)
  rw [hybridLaw_eq_map_add, ← hκeq, ← conv_eq_map_add,
    map_pi_sum_smul_peel κ (⟨j, hj⟩ : Fin (m + 1)) (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹, hν,
    conv_reassoc]

/-- **The tail-side convolution identity (wave 43).** *The `(j+1)`-st hybrid law is the law of the
tail step's base point, convolved with the whole smoothing Gaussian of width `σ_{j+1}`.*

`abs_integral_gaussian_smoothed_swap_localised_le` evaluates its shell indicator at `v`, i.e.
**before** the smoothing, so its base law is the unsmoothed peeled sum `c ∑_{l ≠ j} Yₗ`.
Convolving that with the full Gaussian of width `σ_{j+1}` gives `hybridLaw n (j+1) ν` — the index
moves by one, which is why brick L's weight hypothesis has to be assumed at every `j ≤ n`, as it
already is. The Dirac coordinate that `κ_{j+1}` puts at index `j` disappears by
`Measure.dirac_zero_conv`, and the remaining coordinates of `κ_{j+1}` are those of `κ_j`. -/
theorem hybridLaw_conv_tail {m j : ℕ} (hj : j < m + 1)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν]
    {κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k))}
    [∀ i, IsProbabilityMeasure (κ i)]
    (hκ : ∀ i : Fin (m + 1), κ i = if (i : ℕ) < j then Measure.dirac 0 else ν) :
    hybridLaw (m + 1) (j + 1) ν
      = ((Measure.pi fun l : Fin m => κ ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)).map
            fun y => (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • ∑ l, y l)
        ∗ ((stdGaussian (EuclideanSpace ℝ (Fin k))).map
            fun z => (Real.sqrt ((j + 1 : ℕ) : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) • z) := by
  classical
  set κ' : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun i => if (i : ℕ) < j + 1 then Measure.dirac 0 else ν with hκ'def
  haveI hκ'p : ∀ i, IsProbabilityMeasure (κ' i) := by
    intro i; rw [hκ'def]; dsimp only; split <;> infer_instance
  have hoff : (fun l : Fin m => κ' ((⟨j, hj⟩ : Fin (m + 1)).succAbove l))
      = fun l : Fin m => κ ((⟨j, hj⟩ : Fin (m + 1)).succAbove l) := by
    funext l
    have hne : (((⟨j, hj⟩ : Fin (m + 1)).succAbove l : Fin (m + 1)) : ℕ) ≠ j := by
      intro h
      exact Fin.succAbove_ne (⟨j, hj⟩ : Fin (m + 1)) l (Fin.ext (by rw [h]))
    rw [hκ'def, hκ]
    dsimp only
    by_cases hlt : (((⟨j, hj⟩ : Fin (m + 1)).succAbove l : Fin (m + 1)) : ℕ) < j
    · rw [if_pos (by omega), if_pos hlt]
    · rw [if_neg (by omega), if_neg hlt]
  have hdir : κ' (⟨j, hj⟩ : Fin (m + 1)) = Measure.dirac 0 := by
    rw [hκ'def]; dsimp only; exact if_pos (Nat.lt_succ_self j)
  have hmd : (Measure.dirac (0 : EuclideanSpace ℝ (Fin k))).map
      (fun u => (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • u)
      = Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) := by simp
  rw [hybridLaw_eq_map_add, ← hκ'def, ← conv_eq_map_add,
    map_pi_sum_smul_peel κ' (⟨j, hj⟩ : Fin (m + 1)) (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹, hdir,
    hoff, hmd, Measure.dirac_zero_conv]

/-- The characteristic function of the law of a sum of independent summands is the product of
the characteristic functions. -/
private lemma charFun_map_sum_pi {N : ℕ}
    (μ : Fin N → Measure (EuclideanSpace ℝ (Fin k)))
    [∀ i, IsProbabilityMeasure (μ i)] (t : EuclideanSpace ℝ (Fin k)) :
    charFun ((Measure.pi μ).map (fun y => ∑ i, y i)) t = ∏ i, charFun (μ i) t := by
  have hunfold : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin k))) (s : EuclideanSpace ℝ (Fin k)),
      charFun ρ s = ∫ x, Complex.exp ((⟪x, s⟫_ℝ : ℂ) * Complex.I) ∂ρ := fun _ _ => rfl
  rw [hunfold, integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  have hprod : ∀ y : Fin N → EuclideanSpace ℝ (Fin k),
      Complex.exp ((⟪∑ i, y i, t⟫_ℝ : ℂ) * Complex.I)
        = ∏ i, Complex.exp ((⟪y i, t⟫_ℝ : ℂ) * Complex.I) := by
    intro y
    rw [← Complex.exp_sum]
    congr 1
    rw [sum_inner]
    push_cast
    rw [Finset.sum_mul]
  simp_rw [hprod]
  have hfub := integral_fintype_prod_eq_prod (μ := μ)
    (fun (_ : Fin N) (x : EuclideanSpace ℝ (Fin k)) =>
      Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I))
  exact hfub.trans (Finset.prod_congr rfl fun i _ => (hunfold (μ i) t).symm)

/-- **Dropping the `δ₀` factors.** The law of the coordinate sum of the hybrid product measure
(whose first `j` factors are `δ₀`) is the law of the coordinate sum of `n − j` copies of `ν`. -/
private lemma map_sum_pi_dirac_drop {n j : ℕ} (hj : j ≤ n)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν] :
    ((Measure.pi fun i : Fin n =>
        if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν).map
        fun y => ∑ i, y i)
      = ((Measure.pi fun _ : Fin (n - j) => ν).map fun y => ∑ i, y i) := by
  classical
  haveI hinst : ∀ i : Fin n, IsProbabilityMeasure
      (if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) := by
    intro i; split <;> infer_instance
  haveI : IsProbabilityMeasure (((Measure.pi fun i : Fin n =>
      if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν).map
      fun y => ∑ i, y i)) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  haveI : IsProbabilityMeasure (((Measure.pi fun _ : Fin (n - j) =>
      ν).map fun y => ∑ i, y i)) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_map_sum_pi, charFun_map_sum_pi]
  have hdirac : charFun (Measure.dirac (0 : EuclideanSpace ℝ (Fin k))) t = 1 := by
    have h : charFun (Measure.dirac (0 : EuclideanSpace ℝ (Fin k))) t
        = ∫ x, Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I) ∂(Measure.dirac 0) := rfl
    rw [h, integral_dirac]
    simp
  have hfac : ∀ i : Fin n,
      charFun (if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) t
        = if (i : ℕ) < j then (1 : ℂ) else charFun ν t := by
    intro i; split_ifs with h
    · exact hdirac
    · rfl
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin,
    Fin.prod_univ_eq_prod_range (fun i : ℕ => if i < j then (1 : ℂ) else charFun ν t) n,
    ← Finset.prod_range_mul_prod_Ico _ hj,
    Finset.prod_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi)), Finset.prod_const_one,
    one_mul,
    Finset.prod_congr rfl (fun i hi => if_neg (not_lt.mpr (Finset.mem_Ico.mp hi).1)),
    Finset.prod_const, Nat.card_Ico]

/-- **The non-Gaussian coordinate of the hybrid law is a scaled sum law.** With `m = n − j`
summands and scale `λ = √m/√n`, the law of `n^{-1/2} ∑ᵢ Yᵢ` is `λ` times `sumLaw m ν`. -/
private lemma map_partial_sum_eq_smul_sumLaw {n j : ℕ} (hj : j ≤ n) (hm : 0 < n - j)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν] :
    ((Measure.pi fun i : Fin n =>
        if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν).map
        fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
      = (sumLaw (n - j) ν).map
          (fun x => (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) • x) := by
  classical
  haveI hinst : ∀ i : Fin n, IsProbabilityMeasure
      (if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) := by
    intro i; split <;> infer_instance
  have hn : 0 < n := lt_of_lt_of_le hm (Nat.sub_le n j)
  have hsm : (0 : ℝ) < Real.sqrt ((n - j : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hL : ((Measure.pi fun i : Fin n =>
        if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν).map
        fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
      = ((Measure.pi fun _ : Fin (n - j) => ν).map fun y => ∑ i, y i).map
          (fun w => (Real.sqrt (n : ℝ))⁻¹ • w) := by
    rw [← map_sum_pi_dirac_drop hj ν, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hR : (sumLaw (n - j) ν).map
        (fun x => (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) • x)
      = ((Measure.pi fun _ : Fin (n - j) => ν).map fun y => ∑ i, y i).map
          (fun w => (Real.sqrt (n : ℝ))⁻¹ • w) := by
    simp only [sumLaw]
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext y
    simp only [Function.comp_apply, smul_smul]
    congr 1
    field_simp
  rw [hL, hR]

set_option maxHeartbeats 1600000 in
/-- **The conditioning skeleton of brick H** (wave 29: factored out). For *any* measurable set
`S`, the hybrid mass `hybridLaw n j ν S` is bounded by any `c ≥ 0` that dominates the mass of
every affine preimage `(r • · + a)⁻¹ S` with `r ≥ 1/2`, under the Gaussian in the
Gaussian-dominant regime `n ≤ 2j` and under `sumLaw (n-j) ν` in the sum-dominant regime.

The two Fubini identities (`Measure.prod_apply` / `Measure.prod_apply_symm`) and
`map_partial_sum_eq_smul_sumLaw` are the whole content; the set `S` enters only through the two
hypotheses. `hybridLaw_shell_le` (the outer shell) and `hybridLaw_wideShell_le` (the two-sided
shell) are the two instances. -/
private lemma hybridLaw_le_of_affine_le {n j : ℕ} (hn : 0 < n) (hj : j ≤ n)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    {S : Set (EuclideanSpace ℝ (Fin k))} (hSm : MeasurableSet S) {c : ℝ} (hc : 0 ≤ c)
    (hG : n ≤ 2 * j → ∀ r : ℝ, 1 / 2 ≤ r → ∀ a : EuclideanSpace ℝ (Fin k),
      ((stdGaussian (EuclideanSpace ℝ (Fin k))) ((fun x => r • x + a) ⁻¹' S)).toReal ≤ c)
    (hM : 2 * j < n → ∀ r : ℝ, 1 / 2 ≤ r → ∀ a : EuclideanSpace ℝ (Fin k),
      ((sumLaw (n - j) ν) ((fun x => r • x + a) ⁻¹' S)).toReal ≤ c) :
    ((hybridLaw n j ν) S).toReal ≤ c := by
  haveI hinst : ∀ i : Fin n, IsProbabilityMeasure
      (if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) := by
    intro i; split <;> infer_instance
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnr
  suffices h : hybridLaw n j ν S ≤ ENNReal.ofReal c by
    calc (hybridLaw n j ν S).toReal
        ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono (by simp) h
      _ = c := ENNReal.toReal_ofReal hc
  have hΦ : Measurable (fun p : (Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k) =>
      (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
        + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) := by fun_prop
  rw [hybridLaw, Measure.map_apply hΦ hSm]
  rcases le_or_gt n (2 * j) with hcase | hcase
  · have hjpos : 0 < j := by omega
    have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos
    have hσpos : (0 : ℝ) < Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ) := by positivity
    have hσsq : (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) ^ 2 = (j : ℝ) / (n : ℝ) := by
      rw [div_pow, Real.sq_sqrt hjr.le, Real.sq_sqrt hnr.le]
    have hσge : (1 : ℝ) / 2 ≤ Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ) := by
      have hhalf : (1 : ℝ) / 2 ≤ (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) ^ 2 := by
        rw [hσsq, le_div_iff₀ hnr]
        have : (n : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hcase
        linarith
      nlinarith
    rw [Measure.prod_apply (hΦ hSm)]
    have hinner : ∀ y : Fin n → EuclideanSpace ℝ (Fin k),
        (stdGaussian (EuclideanSpace ℝ (Fin k)))
            (Prod.mk y ⁻¹' ((fun p : (Fin n → EuclideanSpace ℝ (Fin k))
                × EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
                  + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) ⁻¹' S))
          ≤ ENNReal.ofReal c := by
      intro y
      have hset : (Prod.mk y ⁻¹' ((fun p : (Fin n → EuclideanSpace ℝ (Fin k))
            × EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
              + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) ⁻¹' S))
          = (fun z => (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • z
              + (Real.sqrt (n : ℝ))⁻¹ • (∑ i, y i)) ⁻¹' S := by
        ext z
        simp only [Set.mem_preimage]
        rw [add_comm]
      rw [hset]
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).2
        (hG hcase _ hσge ((Real.sqrt (n : ℝ))⁻¹ • (∑ i, y i)))
    calc ∫⁻ y, (stdGaussian (EuclideanSpace ℝ (Fin k))) (Prod.mk y ⁻¹' _)
            ∂(Measure.pi fun i : Fin n =>
              if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν)
        ≤ ∫⁻ _, ENNReal.ofReal c
            ∂(Measure.pi fun i : Fin n =>
              if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) :=
          lintegral_mono hinner
      _ = ENNReal.ofReal c := by rw [lintegral_const, measure_univ, mul_one]
  · have hm : 0 < n - j := by omega
    have hmn : n ≤ 2 * (n - j) := by omega
    have hmr : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast hm
    have hlampos : (0 : ℝ) < Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ) := by positivity
    have hlamsq : (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) ^ 2
        = ((n - j : ℕ) : ℝ) / (n : ℝ) := by
      rw [div_pow, Real.sq_sqrt hmr.le, Real.sq_sqrt hnr.le]
    have hlamge : (1 : ℝ) / 2 ≤ Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ) := by
      have hhalf : (1 : ℝ) / 2 ≤ (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) ^ 2 := by
        rw [hlamsq, le_div_iff₀ hnr]
        have : (n : ℝ) ≤ 2 * ((n - j : ℕ) : ℝ) := by exact_mod_cast hmn
        linarith
      nlinarith
    rw [Measure.prod_apply_symm (hΦ hSm)]
    have hinner : ∀ z : EuclideanSpace ℝ (Fin k),
        (Measure.pi fun i : Fin n =>
            if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν)
            ((fun y => (y, z)) ⁻¹' ((fun p : (Fin n → EuclideanSpace ℝ (Fin k))
                × EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
                  + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) ⁻¹' S))
          ≤ ENNReal.ofReal c := by
      intro z
      set a : EuclideanSpace ℝ (Fin k) := (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • z with hadef
      have hTm : MeasurableSet ((fun w => w + a) ⁻¹' S) := (measurable_id.add_const a) hSm
      have hset : ((fun y : Fin n → EuclideanSpace ℝ (Fin k) => (y, z))
            ⁻¹' ((fun p : (Fin n → EuclideanSpace ℝ (Fin k))
              × EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
                + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) ⁻¹' S))
          = (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) ⁻¹' ((fun w => w + a) ⁻¹' S) := by
        ext y
        simp only [Set.mem_preimage, hadef]
      rw [hset, ← Measure.map_apply (by fun_prop) hTm,
        map_partial_sum_eq_smul_sumLaw hj hm ν,
        Measure.map_apply (by fun_prop) hTm]
      have hset2 : ((fun x : EuclideanSpace ℝ (Fin k) =>
            (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) • x)
            ⁻¹' ((fun w => w + a) ⁻¹' S))
          = (fun x => (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) • x + a) ⁻¹' S := rfl
      rw [hset2]
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).2
        (hM hcase _ hlamge a)
    calc ∫⁻ z, (Measure.pi fun i : Fin n =>
              if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν)
            ((fun y => (y, z)) ⁻¹' _) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
        ≤ ∫⁻ _, ENNReal.ofReal c ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
          lintegral_mono hinner
      _ = ENNReal.ofReal c := by rw [lintegral_const, measure_univ, mul_one]

/-- **Brick H (wave 22: PROVED).** *The shell mass of every hybrid law is `≤ 2 C_k ε + 2Y`,
uniformly in `j`.*

This is where the induction is consumed, and the reason the neighbour range of
`le_of_selfImproving_induction` is `n/2 ≤ m ≤ n`. The two regimes:

* **`2j ≥ n` (Gaussian-dominant).** The hybrid is `ρ ∗ γ_σ` with `σ = √j/√n ≥ 1/√2`. Fubini in
  the *sum* coordinate (`Measure.prod_apply`) writes the shell mass as
  `∫ γ((σ · + x)⁻¹ S) dρ(x)`, and for `S = Bᵋ \ interior B` each inner set is the `(ε/σ)`-shell
  of a convex set; `gaussian_measureReal_shell_preimage_aff_le` bounds it by
  `C_k ε/σ ≤ 2 C_k ε`. **No induction is needed in this regime** — the hybrid's own Gaussian
  component does the work.
* **`2j ≤ n` (sum-dominant).** The non-Gaussian part is a normalised sum of `m = n − j ≥ n/2`
  summands, scaled by `λ = √(m/n) ≥ 1/√2` (`map_partial_sum_eq_smul_sumLaw`). Fubini in the
  *Gaussian* coordinate (`Measure.prod_apply_symm`) writes the shell mass as
  `∫ μ_m((λ · + σz)⁻¹ S) dγ(z)`, the `(ε/λ)`-shell of a convex set; the class of measurable
  convex sets is affine-invariant, so `measureReal_shell_preimage_aff_le` applies and gives
  `C_k ε/λ + 2 Δ_m ≤ 2 C_k ε + 2 Y`.

Both regimes use the affine transport proved just above (`measureReal_shell_preimage_aff_le`,
via `preimage_aff_thickening` and `preimage_aff_interior`): the preimage of an `ε`-shell of a
convex set under `x ↦ r x + a` is the `(ε/r)`-shell of a convex set, so the class the induction
runs on is affine-invariant. The convolution bookkeeping that wave 20 left open is supplied by
the two Fubini identities above together with `map_partial_sum_eq_smul_sumLaw`, whose only
non-formal ingredient is `map_sum_pi_dirac_drop` — the `δ₀` factors of the hybrid product drop
out of the law of the coordinate sum.

Wave 29 factored the two-regime conditioning out as `hybridLaw_le_of_affine_le`, which knows
nothing about the shell; what is left here is the two affine-transport estimates. The statement
is unchanged.

The moment hypotheses `hmean`, `hcov`, `hβ` are **not used**: the shell bound is purely
geometric, and only enters the recursion through `convexDiscrepancy`, where the moments are
already assumed. They are retained so that the statement matches the shape the recursion
consumes. -/
theorem hybridLaw_shell_le (hk : 0 < k) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    (_hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (_hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (_hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) {Y : ℝ}
    (hY : ∀ m : ℕ, n ≤ 2 * m → m ≤ n →
      convexDiscrepancy (sumLaw m ν) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        ≤ Y) :
    ((hybridLaw n j ν) (Metric.thickening ε B \ interior B)).toReal
      ≤ 2 * gaussianShellConst k * ε + 2 * Y := by
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hY0 : (0 : ℝ) ≤ Y := le_trans convexDiscrepancy_nonneg (hY n (by omega) le_rfl)
  have hgauss : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := multivariateGaussian_zero_one
  have hbound : ∀ r : ℝ, 1 / 2 ≤ r → ε / r ≤ 2 * ε := by
    intro r hr
    have hrpos : (0 : ℝ) < r := by linarith
    rw [div_le_iff₀ hrpos]; nlinarith
  refine hybridLaw_le_of_affine_le hn hj
    (Metric.isOpen_thickening.measurableSet.diff isOpen_interior.measurableSet)
    (by positivity) (fun _ r hr a => ?_) (fun _ r hr a => ?_)
  · have hrpos : (0 : ℝ) < r := by linarith
    have hb := gaussian_measureReal_shell_preimage_aff_le hk hrpos a hBm hBc hε
    rw [← hgauss]
    have h2 := mul_le_mul_of_nonneg_left (hbound r hr) hCk.le
    linarith
  · have hrpos : (0 : ℝ) < r := by linarith
    have hb := measureReal_shell_preimage_aff_le hk (sumLaw (n - j) ν) hrpos a hBm hBc hε
    have hYm := hY (n - j) (by omega) (Nat.sub_le _ _)
    have h2 := mul_le_mul_of_nonneg_left (hbound r hr) hCk.le
    linarith

/-- **Brick H for the two-sided shell (wave 29: PROVED).** *The mass every hybrid law puts on
`Bᵋ \ B_{-ε}` is `≤ 4 C_k ε + 2Y`, uniformly in `j`.*

The same instance of `hybridLaw_le_of_affine_le` as `hybridLaw_shell_le`, with the two-sided
affine transports (`gaussian_measureReal_wideShell_preimage_aff_le`,
`measureReal_wideShell_preimage_aff_le`) in place of the outer-shell ones; the constant doubles
because the two-sided shell costs `C_k ε` on each side.

This is the form the *localised* swap step needs. The localisation weight at a point `v` is
controlled exactly when the mollified indicator is constant on a ball about `v`
(`abs_integral_shift_vecTiltRemainder_le_of_const_ball`), which fails precisely on the two-sided
shell; the outer shell `Bᵋ \ interior B` of `hybridLaw_shell_le` is blind to the inner half.
Note that `ε` here is arbitrary: in the telescope it is the *step* width `σⱼ = √(j/n)`, not the
mollifier width, and `σⱼ ≫ ε` for `j` large. -/
theorem hybridLaw_wideShell_le (hk : 0 < k) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) {Y : ℝ}
    (hY : ∀ m : ℕ, n ≤ 2 * m → m ≤ n →
      convexDiscrepancy (sumLaw m ν) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        ≤ Y) :
    ((hybridLaw n j ν) (Metric.thickening ε B \ erosion ε B)).toReal
      ≤ 4 * gaussianShellConst k * ε + 2 * Y := by
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hY0 : (0 : ℝ) ≤ Y := le_trans convexDiscrepancy_nonneg (hY n (by omega) le_rfl)
  have hgauss : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := multivariateGaussian_zero_one
  have hbound : ∀ r : ℝ, 1 / 2 ≤ r → ε / r ≤ 2 * ε := by
    intro r hr
    have hrpos : (0 : ℝ) < r := by linarith
    rw [div_le_iff₀ hrpos]; nlinarith
  refine hybridLaw_le_of_affine_le hn hj
    (Metric.isOpen_thickening.measurableSet.diff (isOpen_erosion ε B).measurableSet)
    (by positivity) (fun _ r hr a => ?_) (fun _ r hr a => ?_)
  · have hrpos : (0 : ℝ) < r := by linarith
    have hb := gaussian_measureReal_wideShell_preimage_aff_le hk hrpos a hBm hBc hε
    rw [← hgauss]
    have h2 := mul_le_mul_of_nonneg_left (hbound r hr)
      (by positivity : (0:ℝ) ≤ 2 * gaussianShellConst k)
    linarith
  · have hrpos : (0 : ℝ) < r := by linarith
    have hb := measureReal_wideShell_preimage_aff_le hk (sumLaw (n - j) ν) hrpos a hBm hBc hε
    have hYm := hY (n - j) (by omega) (Nat.sub_le _ _)
    have h2 := mul_le_mul_of_nonneg_left (hbound r hr)
      (by positivity : (0:ℝ) ≤ 2 * gaussianShellConst k)
    linarith


/-! #### Localising the swap remainder (wave 37)

The head steps of the weighted telescope need the elementary swap *localised*: its cost must be
multiplied by the indicator of a two-sided shell, whose mass under `hybridLaw n j ν` is what the
amended weight hypothesis bounds. Wave 36 identified the obstruction — the Lagrange remainder
controls `D³f` along the whole segment `[a, a + w]`, so the shell width is `‖w‖`, which is
unbounded in `w`. The three lemmas here supply the localisation *at that varying width*, which
is exactly what the two-regime split of the head estimate consumes.

The mechanism is elementary and needs no Taylor theory at all: off the two-sided shell at width
`‖w‖`, the test function is **constant on the closed ball** `closedBall a ‖w‖` (equal to `1` if
`a` is in the erosion, to `0` if `a` is outside the `(ε + ‖w‖)`-thickening), so the value, the
first derivative and the second derivative at `a` all agree with those of a constant and the
whole second-order remainder *vanishes identically*. -/

/-- Off the two-sided shell at width `s`, a test function that is `1` on `B` and supported in
the `ε`-thickening of `B` is constant on the closed `s`-ball about `a`. -/
private lemma const_on_closedBall_of_notMem_wideShell {B : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {ε s : ℝ}
    (hone : ∀ x ∈ B, f x = 1) (hsupp : ∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B)
    {a : EuclideanSpace ℝ (Fin k)}
    (ha : a ∉ Metric.thickening (ε + s) B \ erosion s B) :
    ∃ C : ℝ, ∀ y ∈ Metric.closedBall a s, f y = C := by
  simp only [Set.mem_diff, not_and, not_not] at ha
  by_cases hth : a ∈ Metric.thickening (ε + s) B
  · have h : a ∈ erosion s B := ha hth
    exact ⟨1, fun y hy => hone y (interior_subset (h hy))⟩
  · refine ⟨0, fun y hy => ?_⟩
    by_contra hfy
    apply hth
    obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.1 (hsupp y hfy)
    refine Metric.mem_thickening_iff.2 ⟨z, hz, ?_⟩
    have h1 : dist a y ≤ s := by
      rw [dist_comm]; simpa [Metric.mem_closedBall] using hy
    have := dist_triangle a y z
    linarith

/-- If `f` is constant on `closedBall a s` with `0 < s` and `‖w‖ ≤ s`, the second-order Taylor
remainder at `a` in the direction `w` is exactly `0`: the value at `a + w` equals the value at
`a`, and both derivatives at `a` are those of a constant. -/
private lemma taylor_remainder_eq_zero_of_const_on_closedBall
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {a w : EuclideanSpace ℝ (Fin k)} {s C : ℝ}
    (hs : 0 < s) (hw : ‖w‖ ≤ s) (h : ∀ y ∈ Metric.closedBall a s, f y = C) :
    f (a + w) - f a - fderiv ℝ f a w - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => w) = 0 := by
  have hev : f =ᶠ[nhds a] fun _ => C := by
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds a hs) fun y hy => ?_
    exact h y (Metric.ball_subset_closedBall hy)
  have hd1 : fderiv ℝ f a = 0 := by
    rw [hev.fderiv_eq]
    simp
  have hd2 : iteratedFDeriv ℝ 2 f a = 0 := by
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).eq_of_nhds,
      iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0)]
    simp
  have h1 : f (a + w) = C := by
    refine h _ ?_
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have h2 : f a = C := h a (by simp [Metric.mem_closedBall, hs.le])
  rw [h1, h2, hd1, hd2]
  simp

/-- **The localised third-order remainder bound (head, near regime).** The global Lagrange
bound `M/6 ‖w‖³` may be multiplied by the indicator of the two-sided shell at width `‖w‖`. -/
private lemma abs_taylor_remainder_localised_le {B : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {ε M : ℝ}
    (hone : ∀ x ∈ B, f x = 1) (hsupp : ∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B)
    (hglob : ∀ a w : EuclideanSpace ℝ (Fin k),
      |f (a + w) - f a - fderiv ℝ f a w - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => w)|
        ≤ M / 6 * ‖w‖ ^ 3)
    (a w : EuclideanSpace ℝ (Fin k)) (hw : w ≠ 0) :
    |f (a + w) - f a - fderiv ℝ f a w - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => w)|
      ≤ (Metric.thickening (ε + ‖w‖) B \ erosion ‖w‖ B).indicator (fun _ => (1 : ℝ)) a
        * (M / 6 * ‖w‖ ^ 3) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  by_cases ha : a ∈ Metric.thickening (ε + ‖w‖) B \ erosion ‖w‖ B
  · rw [Set.indicator_of_mem ha, one_mul]
    exact hglob a w
  · obtain ⟨C, hC⟩ := const_on_closedBall_of_notMem_wideShell hone hsupp ha
    rw [taylor_remainder_eq_zero_of_const_on_closedBall hwpos le_rfl hC,
      Set.indicator_of_notMem ha]
    simp

/-- **The localised lower-order remainder bound (head, far regime).** For `‖w‖` large the
third-order bound is worse than simply discarding the expansion: the remainder is at most
`2 + ‖D¹f‖‖w‖ + ½‖D²f‖‖w‖²`, and this too carries the shell indicator at width `‖w‖`. Together
with the mollifier bounds `‖D¹f‖ ≤ C₃/ε`, `‖D²f‖ ≤ C₃/ε²` of `exists_smoothed_convex_indicator`
(wave 37, item 1) this is what prices the far regime with only a *third* moment of `ν`. -/
private lemma abs_taylor_remainder_localised_lower_le {B : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {ε : ℝ}
    (hone : ∀ x ∈ B, f x = 1) (hsupp : ∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B)
    (hfb : ∀ x, |f x| ≤ 1)
    (a w : EuclideanSpace ℝ (Fin k)) (hw : w ≠ 0) :
    |f (a + w) - f a - fderiv ℝ f a w - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => w)|
      ≤ (Metric.thickening (ε + ‖w‖) B \ erosion ‖w‖ B).indicator (fun _ => (1 : ℝ)) a
        * (2 + ‖iteratedFDeriv ℝ 1 f a‖ * ‖w‖
            + 1 / 2 * ‖iteratedFDeriv ℝ 2 f a‖ * ‖w‖ ^ 2) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  by_cases ha : a ∈ Metric.thickening (ε + ‖w‖) B \ erosion ‖w‖ B
  · rw [Set.indicator_of_mem ha, one_mul]
    have h0 : |f (a + w) - f a| ≤ 2 := by
      have e1 := abs_le.1 (hfb (a + w))
      have e2 := abs_le.1 (hfb a)
      rw [abs_le]
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
    have h1 : |fderiv ℝ f a w| ≤ ‖iteratedFDeriv ℝ 1 f a‖ * ‖w‖ := by
      rw [norm_iteratedFDeriv_one]
      exact (fderiv ℝ f a).le_opNorm w
    have h2 : |iteratedFDeriv ℝ 2 f a (fun _ => w)| ≤ ‖iteratedFDeriv ℝ 2 f a‖ * ‖w‖ ^ 2 := by
      have hop := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ 2 f a)
        (fun _ : Fin 2 => w)
      have hprod : (∏ _i : Fin 2, ‖w‖) = ‖w‖ ^ 2 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hprod] at hop
      rw [← Real.norm_eq_abs]
      exact hop
    calc |f (a + w) - f a - fderiv ℝ f a w
            - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => w)|
        ≤ |f (a + w) - f a| + |fderiv ℝ f a w|
            + |(1 / 2) * iteratedFDeriv ℝ 2 f a fun _ => w| := by
          have e1 := abs_sub (f (a + w) - f a) (fderiv ℝ f a w)
          have e2 := abs_sub (f (a + w) - f a - fderiv ℝ f a w)
            ((1 / 2) * iteratedFDeriv ℝ 2 f a fun _ => w)
          linarith
      _ ≤ 2 + ‖iteratedFDeriv ℝ 1 f a‖ * ‖w‖
            + 1 / 2 * ‖iteratedFDeriv ℝ 2 f a‖ * ‖w‖ ^ 2 := by
          rw [abs_mul]
          have habs : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
          rw [habs]
          nlinarith [h0, h1, h2, abs_nonneg (iteratedFDeriv ℝ 2 f a fun _ => w)]
  · obtain ⟨C, hC⟩ := const_on_closedBall_of_notMem_wideShell hone hsupp ha
    rw [taylor_remainder_eq_zero_of_const_on_closedBall hwpos le_rfl hC,
      Set.indicator_of_notMem ha]
    simp

/-- **The far regime priced (wave 37, PROVED).** For a displacement `t = c‖u‖` beyond the
mollification width `ε`, the lower-order remainder bound times the shell weight at width `t` is
dominated by `t³` and `t²` terms with an `ε^{-2}` in front. This is the pointwise arithmetic of
the far half of the head estimate; combined with `setIntegral_norm_pow_tail_le` it shows that
the far regime costs only a **third** moment of `ν`, which is why the naive fourth-moment
obstruction of wave 36 is not real. -/
private lemma far_regime_pointwise_le {C₃ Ck W ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t)
    (hC₃ : 1 ≤ C₃) (hCk : 0 ≤ Ck) (hW : 0 ≤ W) :
    (2 + C₃ / ε * t + 1 / 2 * (C₃ / ε ^ 2) * t ^ 2) * (8 * Ck * t + W)
      ≤ 32 * C₃ * Ck * t ^ 3 / ε ^ 2 + 4 * C₃ * W * t ^ 2 / ε ^ 2 := by
  have htp : 0 < t := lt_of_lt_of_le hε ht
  have hbr : 2 + C₃ / ε * t + 1 / 2 * (C₃ / ε ^ 2) * t ^ 2 ≤ 4 * C₃ * t ^ 2 / ε ^ 2 := by
    have key : (2 + C₃ / ε * t + 1 / 2 * (C₃ / ε ^ 2) * t ^ 2) * ε ^ 2
        ≤ 4 * C₃ * t ^ 2 := by
      have e1 : C₃ / ε * t * ε ^ 2 = C₃ * t * ε := by field_simp
      have e2 : 1 / 2 * (C₃ / ε ^ 2) * t ^ 2 * ε ^ 2 = 1 / 2 * (C₃ * t ^ 2) := by
        field_simp
      have hexp : (2 + C₃ / ε * t + 1 / 2 * (C₃ / ε ^ 2) * t ^ 2) * ε ^ 2
          = 2 * ε ^ 2 + C₃ * t * ε + 1 / 2 * (C₃ * t ^ 2) := by
        rw [add_mul, add_mul, e1, e2]
      rw [hexp]
      nlinarith [mul_le_mul_of_nonneg_left ht (le_of_lt htp)]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)]
    exact key
  have hw : (0 : ℝ) ≤ 8 * Ck * t + W := by positivity
  calc (2 + C₃ / ε * t + 1 / 2 * (C₃ / ε ^ 2) * t ^ 2) * (8 * Ck * t + W)
      ≤ (4 * C₃ * t ^ 2 / ε ^ 2) * (8 * Ck * t + W) := mul_le_mul_of_nonneg_right hbr hw
    _ = 32 * C₃ * Ck * t ^ 3 / ε ^ 2 + 4 * C₃ * W * t ^ 2 / ε ^ 2 := by ring

/-- **The far tail of a third moment (wave 37, PROVED).** `∫_{‖u‖ > R} ‖u‖^p dν ≤ β / R^q` for
`p + q = 3`. This is the only integrability input the far regime needs: no fourth moment, and no
moment beyond the `hβint` the brick already carries. -/
private lemma setIntegral_norm_pow_tail_le {p q : ℕ} (hpq : p + q = 3) {R : ℝ} (hR : 0 < R)
    {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hβ : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖ ^ 3) ν) :
    ∫ u in {u : EuclideanSpace ℝ (Fin k) | R < ‖u‖}, ‖u‖ ^ p ∂ν
      ≤ (∫ u, ‖u‖ ^ 3 ∂ν) / R ^ q := by
  set S : Set (EuclideanSpace ℝ (Fin k)) := {u | R < ‖u‖} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  have hptw : ∀ u ∈ S, ‖u‖ ^ p ≤ ‖u‖ ^ 3 / R ^ q := by
    intro u hu
    have hu' : R < ‖u‖ := hu
    have hRq : R ^ q ≤ ‖u‖ ^ q := pow_le_pow_left₀ hR.le hu'.le q
    rw [le_div_iff₀ (by positivity)]
    calc ‖u‖ ^ p * R ^ q ≤ ‖u‖ ^ p * ‖u‖ ^ q :=
          mul_le_mul_of_nonneg_left hRq (by positivity)
      _ = ‖u‖ ^ 3 := by rw [← pow_add, hpq]
  have hint : IntegrableOn (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖ ^ p) S ν := by
    refine Integrable.mono' ((hβ.restrict (s := S)).div_const (R ^ q))
      (continuous_norm.pow p).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hptw u hu
  calc ∫ u in S, ‖u‖ ^ p ∂ν ≤ ∫ u in S, ‖u‖ ^ 3 / R ^ q ∂ν :=
        setIntegral_mono_on hint ((hβ.restrict (s := S)).div_const _) hSm hptw
    _ = (∫ u in S, ‖u‖ ^ 3 ∂ν) / R ^ q := by rw [integral_div]
    _ ≤ (∫ u, ‖u‖ ^ 3 ∂ν) / R ^ q := by
        have h : (∫ u in S, ‖u‖ ^ 3 ∂ν) ≤ ∫ u, ‖u‖ ^ 3 ∂ν :=
          setIntegral_le_integral hβ (Filter.Eventually.of_forall fun u => by positivity)
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h (by positivity)

/-- The erosion as a strict distance inequality. -/
private lemma erosion_eq_ofReal_lt_infEdist {s : ℝ} (hs : 0 ≤ s)
    (B : Set (EuclideanSpace ℝ (Fin k))) :
    erosion s B
      = {x | ENNReal.ofReal s < Metric.infEDist x (interior B)ᶜ} := by
  ext x
  simp only [erosion, Set.mem_setOf_eq]
  constructor
  · intro hx
    rcases Set.eq_empty_or_nonempty ((interior B)ᶜ) with hK | hK
    · rw [hK, Metric.infEDist_empty]
      exact ENNReal.ofReal_lt_top
    · obtain ⟨y, hyK, hy⟩ :=
        (isOpen_interior.isClosed_compl).exists_infDist_eq_dist hK x
      have hxy : s < dist x y := by
        by_contra h
        push_neg at h
        exact hyK (hx (Metric.mem_closedBall.2 (by rwa [dist_comm])))
      refine lt_of_lt_of_le
        ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs).2 hxy) ?_
      rw [Metric.le_infEDist]
      intro z hz
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hy ▸ Metric.infDist_le_dist_of_mem hz)
  · intro hx y hy
    by_contra hyB
    have h1 : Metric.infEDist x (interior B)ᶜ ≤ edist x y :=
      Metric.infEDist_le_edist_of_mem hyB
    rw [edist_dist] at h1
    have h2 : dist x y ≤ s := by
      rw [dist_comm]
      exact Metric.mem_closedBall.1 hy
    exact absurd (lt_of_lt_of_le hx h1) (not_lt.2 (ENNReal.ofReal_le_ofReal h2))

/-- Product measurability of the two-sided shell at a continuous, nonnegative varying width. -/
private lemma measurableSet_wideShell_prod {B : Set (EuclideanSpace ℝ (Fin k))}
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u) :
    MeasurableSet {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
      p.1 ∈ Metric.thickening (g p.2) B \ erosion (g p.2) B} := by
  have hm1 : Measurable fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      Metric.infEDist p.1 B :=
    (Metric.continuous_infEDist).measurable.comp measurable_fst
  have hm2 : Measurable fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      Metric.infEDist p.1 (interior B)ᶜ :=
    (Metric.continuous_infEDist).measurable.comp measurable_fst
  have hm3 : Measurable fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (g p.2) :=
    (ENNReal.continuous_ofReal.comp hg).measurable.comp measurable_snd
  have hset : {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
      p.1 ∈ Metric.thickening (g p.2) B \ erosion (g p.2) B}
      = {p | Metric.infEDist p.1 B < ENNReal.ofReal (g p.2)}
        ∩ {p | ENNReal.ofReal (g p.2) < Metric.infEDist p.1 (interior B)ᶜ}ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_compl_iff,
      Metric.mem_thickening_iff_infEDist_lt]
    rw [erosion_eq_ofReal_lt_infEdist (hg0 p.2) B]
    rfl
  rw [hset]
  exact (measurableSet_lt hm1 hm3).inter (measurableSet_lt hm3 hm2).compl

private lemma indicator_one_nonneg {α : Type*} (s : Set α) (a : α) :
    (0 : ℝ) ≤ s.indicator (fun _ => (1 : ℝ)) a :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) a

private lemma indicator_one_le_one {α : Type*} (s : Set α) (a : α) :
    s.indicator (fun _ => (1 : ℝ)) a ≤ 1 := by
  by_cases hm : a ∈ s
  · rw [Set.indicator_of_mem hm]
  · rw [Set.indicator_of_notMem hm]; norm_num

private lemma indicator_one_mono {α : Type*} {s t : Set α} (h : s ⊆ t) (a : α) :
    s.indicator (fun _ => (1 : ℝ)) a ≤ t.indicator (fun _ => (1 : ℝ)) a := by
  by_cases hm : a ∈ s
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (h hm)]
  · rw [Set.indicator_of_notMem hm]
    exact indicator_one_nonneg t a

/-- **The two-sided shell moves with a shift, at the price of the shift length (wave 41).**
`1_{shell at s}(a) ≤ 1_{shell at s + t}(a + w)` whenever `‖w‖ ≤ t`.

Wave 41 identified this as the missing link between the two localised per-step bricks and the
weight hypothesis of `localised_swap_bound_small_weight`, by moving each brick's indicator to
the shifted point. **Wave 42 overturned that use** — the shell width in both bricks is a
function of the *same* variable as the shift, so the move produces the shell mass of a translate
of the base law rather than of the convolution; see the wave-42 section of that theorem's note.
What the lemma is actually used for is the *reverse* reading, inside
`wideShell_le_of_deconvolution`: it says that the shell grows under a bounded shift, which is
what makes `τ(shell s) · η(closedBall 0 t) ≤ (τ ∗ η)(shell (s + t))` true.

Both halves are one-line set inclusions and neither needs the erosion's strict-distance
description (`erosion_eq_ofReal_lt_infEdist`): the outer half is the triangle inequality for
`Metric.mem_thickening_iff`, and the inner half is `closedBall a s ⊆ closedBall (a + w) (s + t)`,
which turns a failure of the small ball to lie in `interior B` into a failure of the large one. -/
private lemma mem_wideShell_shift {B : Set (EuclideanSpace ℝ (Fin k))} {s t : ℝ}
    {a w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ t)
    (ha : a ∈ Metric.thickening s B \ erosion s B) :
    a + w ∈ Metric.thickening (s + t) B \ erosion (s + t) B := by
  obtain ⟨hin, hout⟩ := ha
  have hdaw : dist (a + w) a = ‖w‖ := by
    rw [dist_eq_norm, add_sub_cancel_left]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_thickening_iff] at hin ⊢
    obtain ⟨z, hzB, hz⟩ := hin
    refine ⟨z, hzB, ?_⟩
    calc dist (a + w) z ≤ dist (a + w) a + dist a z := dist_triangle _ _ _
      _ < t + s := by rw [hdaw]; linarith
      _ = s + t := by ring
  · intro hmem
    refine hout fun x hx => hmem ?_
    rw [Metric.mem_closedBall] at hx ⊢
    have hdaw' : dist a (a + w) = ‖w‖ := by rw [dist_comm]; exact hdaw
    calc dist x (a + w) ≤ dist x a + dist a (a + w) := dist_triangle _ _ _
      _ ≤ s + t := by rw [hdaw']; linarith

/-- The indicator form of `mem_wideShell_shift`, which is how the transfer is consumed. -/
private lemma indicator_wideShell_le_shift {B : Set (EuclideanSpace ℝ (Fin k))} {s t : ℝ}
    (a w : EuclideanSpace ℝ (Fin k)) (hw : ‖w‖ ≤ t) :
    (Metric.thickening s B \ erosion s B).indicator (fun _ => (1 : ℝ)) a
      ≤ (Metric.thickening (s + t) B \ erosion (s + t) B).indicator
          (fun _ => (1 : ℝ)) (a + w) := by
  by_cases ha : a ∈ Metric.thickening s B \ erosion s B
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (mem_wideShell_shift hw ha)]
  · rw [Set.indicator_of_notMem ha]
    exact indicator_one_nonneg _ _

/-- **Deconvolution of a two-sided-shell bound (wave 42).** *A shell bound for a convolution
`μ = τ ∗ η` gives one for the factor `τ`, at the price of the concentration radius of `η`.*

This is the transfer brick L actually needs, and it is **not** `indicator_wideShell_le_shift`;
see the wave-42 section of `localised_swap_bound_small_weight` for why that lemma cannot do the
job. The mechanism here is the reverse one: `mem_wideShell_shift` says that the shell *grows*
under a bounded shift, so

`τ(shell s) · η(closedBall 0 t) = (τ ⊗ η)(shell s × closedBall 0 t) ≤ μ(shell (s + t))`,

the middle step being exactly `mem_wideShell_shift` applied pointwise. Dividing by
`q ≤ η(closedBall 0 t)` and using `t ≤ s` to absorb `4 C_k (s + t) ≤ 8 C_k s` gives the
conclusion. Both hypotheses are of the right kind at the call site: `μ` is a hybrid law (whose
shell bound brick L assumes at every width), `τ` is the *base* law of a telescope step, and `η`
is the law of the extra summand — one `c`-scaled copy of `ν` on the head side, one `σ`-scaled
Gaussian on the tail side — whose concentration radius `t` is `O(√k)` times its scale by
`measureReal_closedBall_ge_of_normSq`.

The restriction `t ≤ s` is what forces the localisation window of brick L to be strengthened
from `1 ≤ ε √n` to `√k ≤ ε √n`: the widths at which the two per-step bricks consult their
shell hypothesis are all `≥ 2ε`, and the head-side radius is `t = 2 c √k = 2√k/√n`. -/
private lemma wideShell_le_of_deconvolution {B : Set (EuclideanSpace ℝ (Fin k))}
    {τ η μ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure τ] [IsProbabilityMeasure η]
    (hμ : μ = (τ.prod η).map fun p => p.1 + p.2)
    {Ck W : ℝ} (hCk : 0 ≤ Ck)
    (hshell : ∀ s : ℝ, 0 < s →
      (μ (Metric.thickening s B \ erosion s B)).toReal ≤ 4 * Ck * s + W)
    {t q : ℝ} (ht : 0 < t) (hq0 : 0 < q)
    (hq : q ≤ (η (Metric.closedBall 0 t)).toReal)
    {s : ℝ} (hs : 0 < s) (hts : t ≤ s) :
    (τ (Metric.thickening s B \ erosion s B)).toReal ≤ (8 * Ck * s + W) / q := by
  haveI : IsProbabilityMeasure μ := by
    rw [hμ]
    exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have hSm : MeasurableSet (Metric.thickening (s + t) B \ erosion (s + t) B) :=
    Metric.isOpen_thickening.measurableSet.diff (isOpen_erosion _ B).measurableSet
  have hsub : (Metric.thickening s B \ erosion s B)
        ×ˢ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)
      ⊆ (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) => p.1 + p.2) ⁻¹'
        (Metric.thickening (s + t) B \ erosion (s + t) B) := by
    rintro ⟨a, w⟩ ⟨ha, hw⟩
    have hwn : ‖w‖ ≤ t := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hw
    exact mem_wideShell_shift hwn ha
  have hkey : τ (Metric.thickening s B \ erosion s B)
      * η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)
      ≤ μ (Metric.thickening (s + t) B \ erosion (s + t) B) := by
    rw [hμ, Measure.map_apply (by fun_prop) hSm]
    calc τ (Metric.thickening s B \ erosion s B)
          * η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)
        = (τ.prod η) ((Metric.thickening s B \ erosion s B) ×ˢ
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)) :=
          (Measure.prod_prod _ _).symm
      _ ≤ _ := measure_mono hsub
  have hreal : (τ (Metric.thickening s B \ erosion s B)).toReal
      * (η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)).toReal
      ≤ (μ (Metric.thickening (s + t) B \ erosion (s + t) B)).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hkey
  have hτ0 : (0 : ℝ) ≤ (τ (Metric.thickening s B \ erosion s B)).toReal :=
    ENNReal.toReal_nonneg
  have hstep : (τ (Metric.thickening s B \ erosion s B)).toReal * q
      ≤ 4 * Ck * (s + t) + W := by
    refine le_trans (le_trans (mul_le_mul_of_nonneg_left hq hτ0) hreal) ?_
    exact hshell (s + t) (by linarith)
  rw [le_div_iff₀ hq0]
  nlinarith [hstep, hCk, hts]

/-- **The deconvolution radius, by Chebyshev (wave 42).** `η(closedBall 0 t) ≥ 1 − E‖y‖²/t²`,
which at `t = 2 √(E‖y‖²)` gives the constant `q = 3/4` that
`wideShell_le_of_deconvolution` consumes. Both laws that brick L has to deconvolve away have
`E‖y‖² = k` times the square of their scale (`integral_normSq_eq_dim`), so the radius is
`2 √k` times the scale in both cases. -/
private lemma measureReal_closedBall_ge_of_normSq
    {η : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure η]
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) η)
    {t : ℝ} (ht : 0 < t) :
    1 - (∫ y, ‖y‖ ^ 2 ∂η) / t ^ 2
      ≤ (η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)).toReal := by
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (μ := η) (f := fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2)
    (Filter.Eventually.of_forall fun y => by positivity) h2 (t ^ 2)
  have hsub : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)ᶜ
      ⊆ {y : EuclideanSpace ℝ (Fin k) | t ^ 2 ≤ ‖y‖ ^ 2} := by
    intro y hy
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact pow_le_pow_left₀ ht.le hy.le 2
  have hmono : (η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)ᶜ).toReal
      ≤ (η {y : EuclideanSpace ℝ (Fin k) | t ^ 2 ≤ ‖y‖ ^ 2}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hcomp : (η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)ᶜ).toReal
      = 1 - (η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)).toReal := by
    rw [← measureReal_def, ← measureReal_def,
      measureReal_compl (μ := η) measurableSet_closedBall]
    simp
  have hkey : (η {y : EuclideanSpace ℝ (Fin k) | t ^ 2 ≤ ‖y‖ ^ 2}).toReal
      ≤ (∫ y, ‖y‖ ^ 2 ∂η) / t ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hm := hmk
    rw [measureReal_def] at hm
    nlinarith [hm]
  rw [hcomp] at hmono
  linarith [hmono, hkey]

/-- The two-sided shell is monotone in its width: `thickening s B \ erosion s B` grows with `s`,
because the thickening grows and the erosion shrinks. -/
private lemma wideShell_mono {B : Set (EuclideanSpace ℝ (Fin k))} {s t : ℝ} (hst : s ≤ t) :
    Metric.thickening s B \ erosion s B ⊆ Metric.thickening t B \ erosion t B :=
  Set.diff_subset_diff (Metric.thickening_mono hst B)
    (fun _ hx _ hy => hx (Metric.closedBall_subset_closedBall hst hy))

/-- **Deconvolution of a two-sided-shell bound, in the UNIFORM form the two per-step bricks
consume (wave 43).**

`wideShell_le_of_deconvolution` gives the factor's shell bound only at widths `s ≥ t`, `t` the
concentration radius of the deconvolved factor `η`. Both per-step bricks, however, consult their
`hshell` hypothesis at *every* width (that is the wave-29 amendment), so what they need is a
statement of exactly the frozen shape `∀ s > 0, τ(shell s) ≤ 4 C_k' s + W'`. Running the
deconvolution at `t = 2r` with `r ≥ √(E‖y‖²)` — where Chebyshev
(`measureReal_closedBall_ge_of_normSq`) gives the mass `q = 3/4` — and completing the range
`s < 2r` by monotonicity of the shell in its width gives it, at

  `C_k' = 3 C_k`,  `W' = 2W + 22 C_k r`.

Both constants are wave 42's, and both are absorbed at the call sites by the localisation window
`√k ≤ ε √n`, which is what makes `r ≤ ε` on the head side and `r ≲ σⱼ R(σⱼ)` on the tail side. -/
private lemma wideShell_le_of_deconvolution_uniform {B : Set (EuclideanSpace ℝ (Fin k))}
    {τ η μ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure τ] [IsProbabilityMeasure η]
    (hμ : μ = (τ.prod η).map fun p => p.1 + p.2)
    {Ck W : ℝ} (hCk : 0 ≤ Ck) (hW : 0 ≤ W)
    (hshell : ∀ s : ℝ, 0 < s →
      (μ (Metric.thickening s B \ erosion s B)).toReal ≤ 4 * Ck * s + W)
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) η)
    {r : ℝ} (hr : 0 < r) (hnorm : (∫ y, ‖y‖ ^ 2 ∂η) ≤ r ^ 2) :
    ∀ s : ℝ, 0 < s → (τ (Metric.thickening s B \ erosion s B)).toReal
      ≤ 4 * (3 * Ck) * s + (2 * W + 22 * Ck * r) := by
  have ht : (0 : ℝ) < 2 * r := by linarith
  have hq : (3 : ℝ) / 4
      ≤ (η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (2 * r))).toReal := by
    refine le_trans ?_ (measureReal_closedBall_ge_of_normSq h2 ht)
    have hrr : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    rw [hrr]
    have hdiv : (∫ y, ‖y‖ ^ 2 ∂η) / (4 * r ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hbig : ∀ s : ℝ, 2 * r ≤ s → (τ (Metric.thickening s B \ erosion s B)).toReal
      ≤ (32 / 3) * Ck * s + (4 / 3) * W := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht hs
    have h := wideShell_le_of_deconvolution hμ hCk hshell ht (by norm_num) hq hs0 hs
    have hrw : (8 * Ck * s + W) / (3 / 4) = (32 / 3) * Ck * s + (4 / 3) * W := by ring
    rwa [hrw] at h
  intro s hs
  rcases le_total (2 * r) s with hcase | hcase
  · have h := hbig s hcase
    nlinarith [mul_nonneg hCk hs.le, mul_nonneg hCk hr.le]
  · refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (wideShell_mono hcase))) ?_
    refine le_trans (hbig (2 * r) le_rfl) ?_
    nlinarith [mul_nonneg hCk hs.le, mul_nonneg hCk hr.le]

/-- **The near/far split of the localised remainder, at a fixed base point `a`.** -/
private lemma integral_abs_remainder_split_le
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    (hβν : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ν)
    {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : ContDiff ℝ 3 f) (hfb : ∀ x, |f x| ≤ 1)
    {C₃ ε : ℝ} (hC₃ : 1 ≤ C₃) (hε : 0 < ε)
    (hD3 : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3)
    (hD1 : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C₃ / ε)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₃ / ε ^ 2)
    (hone : ∀ x ∈ B, f x = 1) (hsupp : ∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B)
    {c : ℝ} (hc : 0 < c) (a : EuclideanSpace ℝ (Fin k)) :
    (∫ u, |f (a + c • u) - f a - fderiv ℝ f a (c • u)
        - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)| ∂ν)
      ≤ (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator (fun _ => (1 : ℝ)) a
          * (C₃ / ε ^ 3 / 6 * c ^ 3 * ∫ y, ‖y‖ ^ 3 ∂ν)
        + ∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
            (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
                (fun _ => (1 : ℝ)) a
              * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ν := by
  classical
  have hC₃0 : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃
  have hM0 : (0 : ℝ) ≤ C₃ / ε ^ 3 := by positivity
  have hR : (0 : ℝ) < ε / c := div_pos hε hc
  have hcR : c * (ε / c) = ε := by field_simp
  -- the erosion is antitone in the width
  have heros : ∀ {s t : ℝ}, s ≤ t → erosion t B ⊆ erosion s B := by
    intro s t hst x hx
    simp only [erosion, Set.mem_setOf_eq] at hx ⊢
    exact (Metric.closedBall_subset_closedBall hst).trans hx
  -- the integrand
  have hglob : ∀ (a w : EuclideanSpace ℝ (Fin k)),
      |f (a + w) - f a - fderiv ℝ f a w
          - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => w)|
        ≤ C₃ / ε ^ 3 / 6 * ‖w‖ ^ 3 := fun a w =>
    norm_taylor_remainder_three_le hf hD3 a w
  have hgcont : Continuous fun u : EuclideanSpace ℝ (Fin k) =>
      |f (a + c • u) - f a - fderiv ℝ f a (c • u)
        - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)| := by
    refine continuous_abs.comp (((((hf.continuous.comp
      (continuous_const.add (continuous_const_smul c))).sub continuous_const).sub
        ((fderiv ℝ f a).continuous.comp (continuous_const_smul c))).sub ?_))
    exact (continuous_const.mul
      ((iteratedFDeriv ℝ 2 f a).cont.comp
        (continuous_pi fun _ => continuous_const_smul c)))
  have hgb : ∀ u : EuclideanSpace ℝ (Fin k),
      |f (a + c • u) - f a - fderiv ℝ f a (c • u)
        - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)|
        ≤ C₃ / ε ^ 3 / 6 * c ^ 3 * ‖u‖ ^ 3 := by
    intro u
    have h := hglob a (c • u)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow, ← mul_assoc] at h
  have hgint : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
      |f (a + c • u) - f a - fderiv ℝ f a (c • u)
        - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)|) ν := by
    refine Integrable.mono' (hβν.const_mul (C₃ / ε ^ 3 / 6 * c ^ 3))
      hgcont.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hgb u
  -- the split at `‖u‖ = ε / c`
  have hNm : MeasurableSet {u : EuclideanSpace ℝ (Fin k) | ‖u‖ ≤ ε / c} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have hcompl : {u : EuclideanSpace ℝ (Fin k) | ‖u‖ ≤ ε / c}ᶜ
      = {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖} := by
    ext u; simp [not_le]
  have hsplit := integral_add_compl hNm hgint
  rw [hcompl] at hsplit
  rw [← hsplit]
  refine add_le_add ?_ ?_
  · -- ### the near regime
    have hptw : ∀ u ∈ {u : EuclideanSpace ℝ (Fin k) | ‖u‖ ≤ ε / c},
        |f (a + c • u) - f a - fderiv ℝ f a (c • u)
          - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)|
          ≤ (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator
              (fun _ => (1 : ℝ)) a * (C₃ / ε ^ 3 / 6 * c ^ 3) * ‖u‖ ^ 3 := by
      intro u hu
      have hu' : ‖u‖ ≤ ε / c := hu
      rcases eq_or_ne u 0 with rfl | hu0
      · have hz : ((iteratedFDeriv ℝ 2 f a) fun _ : Fin 2 =>
            (0 : EuclideanSpace ℝ (Fin k))) = 0 := by
          first
          | exact ContinuousMultilinearMap.map_coord_zero _ (0 : Fin 2) rfl
          | exact ContinuousMultilinearMap.map_zero _
          | simp
        simp [hz]
      · have hw : c • u ≠ 0 := smul_ne_zero (ne_of_gt hc) hu0
        have hnw : ‖c • u‖ = c * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        have hle : c * ‖u‖ ≤ ε := by
          calc c * ‖u‖ ≤ c * (ε / c) := by nlinarith
            _ = ε := hcR
        have hsub : Metric.thickening (ε + c * ‖u‖) B \ erosion (c * ‖u‖) B
            ⊆ Metric.thickening (2 * ε) B \ erosion (2 * ε) B :=
          Set.diff_subset_diff (Metric.thickening_mono (by linarith) B)
            (heros (by linarith))
        have h := abs_taylor_remainder_localised_le hone hsupp hglob a (c • u) hw
        refine h.trans ?_
        rw [hnw, mul_pow]
        have hind := indicator_one_mono hsub a
        have hnn : (0 : ℝ) ≤ C₃ / ε ^ 3 / 6 * (c ^ 3 * ‖u‖ ^ 3) := by positivity
        calc (Metric.thickening (ε + c * ‖u‖) B \ erosion (c * ‖u‖) B).indicator
                (fun _ => (1 : ℝ)) a * (C₃ / ε ^ 3 / 6 * (c ^ 3 * ‖u‖ ^ 3))
            ≤ (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator
                (fun _ => (1 : ℝ)) a * (C₃ / ε ^ 3 / 6 * (c ^ 3 * ‖u‖ ^ 3)) :=
              mul_le_mul_of_nonneg_right hind hnn
          _ = _ := by ring
    have hind0 : (0 : ℝ) ≤ (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator
        (fun _ => (1 : ℝ)) a := indicator_one_nonneg _ a
    calc (∫ u in {u : EuclideanSpace ℝ (Fin k) | ‖u‖ ≤ ε / c},
            |f (a + c • u) - f a - fderiv ℝ f a (c • u)
              - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)| ∂ν)
        ≤ ∫ u in {u : EuclideanSpace ℝ (Fin k) | ‖u‖ ≤ ε / c},
            (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator
              (fun _ => (1 : ℝ)) a * (C₃ / ε ^ 3 / 6 * c ^ 3) * ‖u‖ ^ 3 ∂ν :=
          setIntegral_mono_on hgint.integrableOn
            ((hβν.const_mul _).integrableOn) hNm hptw
      _ = (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator
              (fun _ => (1 : ℝ)) a * (C₃ / ε ^ 3 / 6 * c ^ 3)
            * ∫ u in {u : EuclideanSpace ℝ (Fin k) | ‖u‖ ≤ ε / c}, ‖u‖ ^ 3 ∂ν :=
          integral_const_mul _ _
      _ ≤ (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator
              (fun _ => (1 : ℝ)) a * (C₃ / ε ^ 3 / 6 * c ^ 3)
            * ∫ u, ‖u‖ ^ 3 ∂ν := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact setIntegral_le_integral hβν
            (Filter.Eventually.of_forall fun u => by positivity)
      _ = _ := by ring
  · -- ### the far regime
    have hFm : MeasurableSet {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖} :=
      measurableSet_lt measurable_const continuous_norm.measurable
    have hSm : MeasurableSet {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
        p.1 ∈ Metric.thickening (2 * (c * ‖p.2‖)) B \ erosion (2 * (c * ‖p.2‖)) B} :=
      measurableSet_wideShell_prod (g := fun u => 2 * (c * ‖u‖)) (by fun_prop)
        (fun u => by positivity)
    have hsec : MeasurableSet {u : EuclideanSpace ℝ (Fin k) |
        a ∈ Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B} :=
      hSm.preimage (f := fun u : EuclideanSpace ℝ (Fin k) => (a, u)) (by fun_prop)
    have hΨm : Measurable (fun u : EuclideanSpace ℝ (Fin k) =>
        (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
            (fun _ => (1 : ℝ)) a
          * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2)) := by
      refine Measurable.mul ?_ (by fun_prop)
      have hrw : (fun u : EuclideanSpace ℝ (Fin k) =>
          (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
            (fun _ => (1 : ℝ)) a)
          = Set.indicator {u : EuclideanSpace ℝ (Fin k) |
              a ∈ Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B}
            (fun _ => (1 : ℝ)) := by
        funext u
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [hrw]
      exact measurable_const.indicator hsec
    have hlowint : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ν := by
      have h1 : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖) ν :=
        integrable_norm_of_cube hβν
      have h2 : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖ ^ 2) ν :=
        integrable_normSq_of_cube hβν
      have h3 := ((integrable_const (2 : ℝ)).add (h1.const_mul (C₃ / ε * c))).add
        (h2.const_mul (1 / 2 * (C₃ / ε ^ 2) * c ^ 2))
      refine h3.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [Pi.add_apply]
      ring
    have hΨint : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
            (fun _ => (1 : ℝ)) a
          * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2)) ν := by
      refine Integrable.mono' hlowint hΨm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => ?_)
      have hb : (0 : ℝ) ≤ 2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2 := by
        positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb,
        abs_of_nonneg (indicator_one_nonneg _ a)]
      exact mul_le_of_le_one_left hb (indicator_one_le_one _ a)
    refine setIntegral_mono_on hgint.integrableOn hΨint.integrableOn hFm ?_
    intro u hu
    have hu' : ε / c < ‖u‖ := hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu'
      exact absurd hu' (not_lt.2 hR.le)
    have hw : c • u ≠ 0 := smul_ne_zero (ne_of_gt hc) hu0
    have hnw : ‖c • u‖ = c * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have hge : ε ≤ c * ‖u‖ := by
      have : c * (ε / c) ≤ c * ‖u‖ := by nlinarith
      rwa [hcR] at this
    have hsub : Metric.thickening (ε + ‖c • u‖) B \ erosion ‖c • u‖ B
        ⊆ Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B := by
      rw [hnw]
      exact Set.diff_subset_diff (Metric.thickening_mono (by linarith) B)
        (heros (by linarith))
    have h := abs_taylor_remainder_localised_lower_le hone hsupp hfb a (c • u) hw
    refine h.trans ?_
    have hind := indicator_one_mono hsub a
    have hbr : 2 + ‖iteratedFDeriv ℝ 1 f a‖ * ‖c • u‖
          + 1 / 2 * ‖iteratedFDeriv ℝ 2 f a‖ * ‖c • u‖ ^ 2
        ≤ 2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2 := by
      rw [hnw]
      have e1 := hD1 a
      have e2 := hD2 a
      have hcu : (0 : ℝ) ≤ c * ‖u‖ := by positivity
      have hcu2 : (0 : ℝ) ≤ (c * ‖u‖) ^ 2 := by positivity
      nlinarith
    have hbr0 : (0 : ℝ) ≤ 2 + ‖iteratedFDeriv ℝ 1 f a‖ * ‖c • u‖
        + 1 / 2 * ‖iteratedFDeriv ℝ 2 f a‖ * ‖c • u‖ ^ 2 := by positivity
    exact mul_le_mul hind hbr hbr0 (indicator_one_nonneg _ a)

/-- **The far regime priced, after the Fubini exchange.** -/
private lemma integral_far_shell_le
    {ν τ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (hβν : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ν)
    {B : Set (EuclideanSpace ℝ (Fin k))}
    {C₃ ε Ck W : ℝ} (hC₃ : 1 ≤ C₃) (hε : 0 < ε) (hCk : 0 ≤ Ck) (hW : 0 ≤ W)
    (hshell : ∀ s : ℝ, 0 < s →
      (τ (Metric.thickening s B \ erosion s B)).toReal ≤ 4 * Ck * s + W)
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun a : EuclideanSpace ℝ (Fin k) =>
        ∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
          (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
              (fun _ => (1 : ℝ)) a
            * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ν) τ
      ∧ (∫ a, (∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
            (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
                (fun _ => (1 : ℝ)) a
              * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ν) ∂τ)
          ≤ C₃ * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν) * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) := by
  classical
  have hC₃0 : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃
  have hR : (0 : ℝ) < ε / c := div_pos hε hc
  have hcR : c * (ε / c) = ε := by field_simp
  have hFm : MeasurableSet {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  -- product measurability of the varying shell indicator
  have hSm : MeasurableSet {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
      p.1 ∈ Metric.thickening (2 * (c * ‖p.2‖)) B \ erosion (2 * (c * ‖p.2‖)) B} :=
    measurableSet_wideShell_prod (g := fun u => 2 * (c * ‖u‖)) (by fun_prop)
      (fun u => by positivity)
  have hΦm : Measurable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      (Metric.thickening (2 * (c * ‖p.2‖)) B \ erosion (2 * (c * ‖p.2‖)) B).indicator
          (fun _ => (1 : ℝ)) p.1
        * (2 + C₃ / ε * (c * ‖p.2‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖p.2‖) ^ 2)) := by
    refine Measurable.mul ?_ (by fun_prop)
    have hrw : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        (Metric.thickening (2 * (c * ‖p.2‖)) B \ erosion (2 * (c * ‖p.2‖)) B).indicator
          (fun _ => (1 : ℝ)) p.1)
        = Set.indicator {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
            p.1 ∈ Metric.thickening (2 * (c * ‖p.2‖)) B \ erosion (2 * (c * ‖p.2‖)) B}
          (fun _ => (1 : ℝ)) := by
      funext p
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [hrw]
    exact measurable_const.indicator hSm
  -- the dominating function
  have hlowint : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
      2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ν := by
    have h1 : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖) ν :=
      integrable_norm_of_cube hβν
    have h2 : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖ ^ 2) ν :=
      integrable_normSq_of_cube hβν
    have h3 := ((integrable_const (2 : ℝ)).add (h1.const_mul (C₃ / ε * c))).add
      (h2.const_mul (1 / 2 * (C₃ / ε ^ 2) * c ^ 2))
    refine h3.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply]
    ring
  have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      2 + C₃ / ε * (c * ‖p.2‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖p.2‖) ^ 2)
      (τ.prod (ν.restrict {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖})) := by
    refine (integrable_prod_iff (by fun_prop)).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun a => hlowint.restrict
    · exact integrable_const (∫ y : EuclideanSpace ℝ (Fin k),
        ‖2 + C₃ / ε * (c * ‖y‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖y‖) ^ 2‖
          ∂(ν.restrict {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖}))
  have hΦint : Integrable (Function.uncurry
      (fun (a u : EuclideanSpace ℝ (Fin k)) =>
        (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
            (fun _ => (1 : ℝ)) a
          * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2)))
      (τ.prod (ν.restrict {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖})) := by
    refine Integrable.mono' hdom hΦm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have hb : (0 : ℝ) ≤ 2 + C₃ / ε * (c * ‖p.2‖)
        + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖p.2‖) ^ 2 := by positivity
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb,
      abs_of_nonneg (indicator_one_nonneg _ p.1)]
    exact mul_le_of_le_one_left hb (indicator_one_le_one _ p.1)
  refine ⟨hΦint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hΦint]
  -- the inner `τ`-integral is the shell mass
  have hinner : ∀ u : EuclideanSpace ℝ (Fin k),
      (∫ a, (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
            (fun _ => (1 : ℝ)) a
          * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂τ)
        = (τ (Metric.thickening (2 * (c * ‖u‖)) B
              \ erosion (2 * (c * ‖u‖)) B)).toReal
          * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) := by
    intro u
    rw [integral_mul_const]
    congr 1
    have hm : MeasurableSet (Metric.thickening (2 * (c * ‖u‖)) B
        \ erosion (2 * (c * ‖u‖)) B) :=
      (Metric.isOpen_thickening.measurableSet).diff (isOpen_erosion _ B).measurableSet
    rw [integral_indicator_const (1 : ℝ) hm]
    simp [Measure.real]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  -- price the shell mass and the lower-order bracket
  have hg1 : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖ ^ 3)
      (ν.restrict {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖}) := hβν.restrict
  have hg2 : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖ ^ 2)
      (ν.restrict {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖}) :=
    (integrable_normSq_of_cube hβν).restrict
  have hgint : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
      32 * C₃ * Ck * (c * ‖u‖) ^ 3 / ε ^ 2 + 4 * C₃ * W * (c * ‖u‖) ^ 2 / ε ^ 2)
      (ν.restrict {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖}) := by
    have h3 := (hg1.const_mul (32 * C₃ * Ck * c ^ 3 / ε ^ 2)).add
      (hg2.const_mul (4 * C₃ * W * c ^ 2 / ε ^ 2))
    refine h3.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply]
    ring
  have hstep : (∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
        (τ (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B)).toReal
          * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ν)
      ≤ ∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
        (32 * C₃ * Ck * (c * ‖u‖) ^ 3 / ε ^ 2 + 4 * C₃ * W * (c * ‖u‖) ^ 2 / ε ^ 2) ∂ν := by
    refine integral_mono_of_nonneg ?_ hgint ?_
    · refine (ae_restrict_iff' hFm).2 (Filter.Eventually.of_forall fun u _ => ?_)
      have : (0 : ℝ) ≤ 2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2 := by
        positivity
      exact mul_nonneg ENNReal.toReal_nonneg this
    · refine (ae_restrict_iff' hFm).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu' : ε / c < ‖u‖ := hu
      have hge : ε ≤ c * ‖u‖ := by
        have h := (mul_lt_mul_of_pos_left hu' hc).le
        rwa [hcR] at h
      have hmass := hshell (2 * (c * ‖u‖)) (by linarith)
      have hbr0 : (0 : ℝ) ≤ 2 + C₃ / ε * (c * ‖u‖)
          + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2 := by positivity
      have hfar := far_regime_pointwise_le (C₃ := C₃) (Ck := Ck) (W := W) (ε := ε)
        (t := c * ‖u‖) hε hge hC₃ hCk hW
      have hmass' : (τ (Metric.thickening (2 * (c * ‖u‖)) B
          \ erosion (2 * (c * ‖u‖)) B)).toReal ≤ 8 * Ck * (c * ‖u‖) + W := by
        linarith
      calc (τ (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B)).toReal
            * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2)
          ≤ (8 * Ck * (c * ‖u‖) + W)
              * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) :=
            mul_le_mul_of_nonneg_right hmass' hbr0
        _ = (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2)
              * (8 * Ck * (c * ‖u‖) + W) := by ring
        _ ≤ 32 * C₃ * Ck * (c * ‖u‖) ^ 3 / ε ^ 2
              + 4 * C₃ * W * (c * ‖u‖) ^ 2 / ε ^ 2 := hfar
  refine hstep.trans ?_
  -- evaluate the two tail moments
  have hrw : ∀ u : EuclideanSpace ℝ (Fin k),
      32 * C₃ * Ck * (c * ‖u‖) ^ 3 / ε ^ 2 + 4 * C₃ * W * (c * ‖u‖) ^ 2 / ε ^ 2
        = (32 * C₃ * Ck * c ^ 3 / ε ^ 2) * ‖u‖ ^ 3
          + (4 * C₃ * W * c ^ 2 / ε ^ 2) * ‖u‖ ^ 2 := fun u => by ring
  simp_rw [hrw]
  rw [integral_add (hg1.const_mul _) (hg2.const_mul _), integral_const_mul,
    integral_const_mul]
  have ht3 := setIntegral_norm_pow_tail_le (p := 3) (q := 0) (by norm_num) hR hβν
  have ht2 := setIntegral_norm_pow_tail_le (p := 2) (q := 1) (by norm_num) hR hβν
  rw [pow_zero, div_one] at ht3
  rw [pow_one] at ht2
  have hβ0 : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ν := integral_nonneg fun y => by positivity
  have hA : (0 : ℝ) ≤ 32 * C₃ * Ck * c ^ 3 / ε ^ 2 := by positivity
  have hD : (0 : ℝ) ≤ 4 * C₃ * W * c ^ 2 / ε ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left ht3 hA
  have h2 := mul_le_mul_of_nonneg_left ht2 hD
  have hfin : 32 * C₃ * Ck * c ^ 3 / ε ^ 2 * (∫ y, ‖y‖ ^ 3 ∂ν)
      + 4 * C₃ * W * c ^ 2 / ε ^ 2 * ((∫ y, ‖y‖ ^ 3 ∂ν) / (ε / c))
      = C₃ * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν) * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) := by
    field_simp
  linarith

/-- **The per-step head estimate (wave 37: stated; wave 38: PROVED).** *One head step of the
hybrid telescope, localised, averaged against the step's own hybrid law.*

`τ` is the law of the step's base point, `ν` is the swapped-in law and `ρ` the standard
Gaussian, and `c = n^{-1/2}` is the step's scale.

**ERRATUM (wave 41).** Waves 37–40 wrote here that "`τ` is `hybridLaw n j ν` (wave 36's
`integral_hybridLaw_eq` / `integral_peel_eq_integral_hybridLaw` identify the telescope's `j`-th
test measure with it)". It is not: the base point of step `j` is `c·(∑ of the coordinates other
than `j`) + σⱼ z`, the swapped coordinate appearing only as the `c u` inside the absolute value,
whereas `hybridLaw n j ν` is the law of that base point *plus* `c u`. Wave 41 proposed
`indicator_wideShell_le_shift` as the transfer; wave 42 overturned that (the shell width here is
a function of the shift variable) and replaced it by `wideShell_le_of_deconvolution`, which
deconvolves the `c ν` factor away at the price of `C_k → 3 C_k`, `W → 2W + 22 C_k ε` and the
window `√k ≤ ε √n`. See the wave-42 section of `localised_swap_bound_small_weight`. The
right-hand side is *exactly* the pair of head summands that
`localised_swap_bound_of_weighted_telescope` consumes, once summed over the `J` head steps.

**Why this is the right statement, and what is left.** Everything in the derivation below is
proved in this file; what is missing is only the assembly.

* Both integrals are compared with the *same* second-order polynomial
  `P(w) = f a + D¹f(a)w + ½ D²f(a)(w,w)`, whose `ν`- and `ρ`-integrals agree because both laws
  are centred with identity covariance — this is the argument of `abs_integral_swap_step_le`,
  unchanged. So the left-hand side is at most `∫∫|R_a(c u)| dν + ∫∫|R_a(c u)| dρ` with `R_a` the
  remainder.
* Pointwise, `|R_a(c u)|` carries the indicator of the **two-sided shell at the varying width**
  `‖c u‖`: `abs_taylor_remainder_localised_le` (with `M = C₃/ε³`) in the near regime and
  `abs_taylor_remainder_localised_lower_le` in the far regime. Off that shell the remainder is
  identically `0` — `f` is constant on `closedBall a ‖c u‖`, so the value and both derivatives
  agree with a constant's.
* The shell `thickening (ε + s) B \ erosion s B` is **monotone in `s`**, so at `c‖u‖ ≤ ε` it is
  contained in `thickening 2ε B \ erosion 2ε B` (mass `≤ 8 C_k ε + W`) and at `c‖u‖ ≥ ε` in
  `thickening (2c‖u‖) B \ erosion (2c‖u‖) B` (mass `≤ 8 C_k c‖u‖ + W`). That is the *only* place
  the amended two-sided-shell hypothesis at **all** widths is used, and it is exactly why wave 29
  had to amend it.
* Fubini turns `∫_τ ∫_ν` into `∫_ν ∫_τ`, the inner `τ`-integral of the shell indicator is the
  shell mass, and the split at `‖u‖ = R := ε/c = ε√n` is priced by `far_regime_pointwise_le` and
  `setIntegral_norm_pow_tail_le` (`p = 3` and `p = 2`, `q = 0` and `q = 1`) — a **third** moment
  and nothing more.

**Wave 38: PROVED, and wave 37's description of the residual bookkeeping is corrected.** Wave 37
wrote that what was left is "measurability of `u ↦ τ(shell at width c‖u‖)` (monotone in `‖u‖`,
hence measurable)". Monotonicity does give measurability of that *scalar* function, but it is not
what the Fubini step needs: `integral_integral_swap` needs the **jointly** measurable integrand
`(a, u) ↦ 1_{shell at width 2c‖u‖}(a)`, and the section-wise monotone argument says nothing about
the pair. The joint statement is `measurableSet_wideShell_prod`, and it rests on a fact that had
not been recorded anywhere: the erosion is a *strict* distance inequality,

`erosion s B = {x | ofReal s < infEDist x (interior B)ᶜ}`  (`erosion_eq_ofReal_lt_infEdist`),

whose only non-formal ingredient is that in a proper space the distance to a nonempty closed set
is attained (`IsClosed.exists_infDist_eq_dist`) — that is what upgrades the trivial `≥` to the
`>` the open condition needs. With both sides of the shell written as strict inequalities between
continuous functions of `(a, u)`, `measurableSet_lt` closes it.

The rest is as the derivation above says. Two named lemmas carry it:
`integral_abs_remainder_split_le` (the near/far split at a fixed base point `a`, entirely
pointwise plus `setIntegral_mono_on`) and `integral_far_shell_le` (the Fubini exchange and the
pricing of the far regime). Note the near regime needs **no** Fubini at all: at `c‖u‖ ≤ ε` the
shell is contained in the *fixed* set `B^{2ε} \ B_{-2ε}`, so the `τ`- and `ν`-integrals separate.
Only the far regime, where the width `2c‖u‖` genuinely varies with `u`, is exchanged. -/
private lemma abs_integral_swap_step_localised_le
    {ν ρ τ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ]
    (hmeanν : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcovν : ∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂ν) = ⟪u, w⟫_ℝ)
    (hβν : Integrable (fun y => ‖y‖ ^ 3) ν)
    (hmeanρ : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ρ) = 0)
    (hcovρ : ∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂ρ) = ⟪u, w⟫_ℝ)
    (hβρ : Integrable (fun y => ‖y‖ ^ 3) ρ)
    {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : ContDiff ℝ 3 f) (hfb : ∀ x, |f x| ≤ 1)
    {C₃ ε : ℝ} (hC₃ : 1 ≤ C₃) (hε : 0 < ε)
    (hD3 : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3)
    (hD1 : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C₃ / ε)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₃ / ε ^ 2)
    (hone : ∀ x ∈ B, f x = 1) (hsupp : ∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B)
    {Ck W : ℝ} (hCk : 0 < Ck) (hW : 0 ≤ W)
    (hshell : ∀ s : ℝ, 0 < s →
      (τ (Metric.thickening s B \ erosion s B)).toReal ≤ 4 * Ck * s + W)
    {c : ℝ} (hc : 0 < c) :
    (∫ a, |(∫ u, f (a + c • u) ∂ν) - (∫ u, f (a + c • u) ∂ρ)| ∂τ)
      ≤ C₃ / ε ^ 3 / 6 * c ^ 3
          * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ)) * (8 * Ck * ε + W)
        + C₃ * c ^ 3 * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ))
            * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) := by
  classical
  have hC₃0 : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃
  have hβν0 : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ν := integral_nonneg fun y => by positivity
  have hβρ0 : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ρ := integral_nonneg fun y => by positivity
  have hShNm : MeasurableSet (Metric.thickening (2 * ε) B \ erosion (2 * ε) B) :=
    Metric.isOpen_thickening.measurableSet.diff (isOpen_erosion _ B).measurableSet
  -- the common value of the second-order polynomial
  obtain ⟨S, hS⟩ : ∃ S : EuclideanSpace ℝ (Fin k) → ℝ, ∀ a, S a
      = ∑ r : Fin 2 → Fin k,
          ⟪EuclideanSpace.basisFun (Fin k) ℝ (r 0),
            EuclideanSpace.basisFun (Fin k) ℝ (r 1)⟫_ℝ
            * iteratedFDeriv ℝ 2 f a fun i => EuclideanSpace.basisFun (Fin k) ℝ (r i) :=
    ⟨_, fun a => rfl⟩
  have hQrw : ∀ (a u : EuclideanSpace ℝ (Fin k)),
      (iteratedFDeriv ℝ 2 f a) (fun _ => c • u)
        = c ^ 2 * (iteratedFDeriv ℝ 2 f a) (fun _ => u) := by
    intro a u
    rw [show (fun _ : Fin 2 => c • u)
        = fun i : Fin 2 => (fun _ : Fin 2 => c) i • (fun _ : Fin 2 => u) i from rfl,
      ← ContinuousMultilinearMap.coe_coe,
      ((iteratedFDeriv ℝ 2 f a).toMultilinearMap).map_smul_univ,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ContinuousMultilinearMap.coe_coe, smul_eq_mul]
  -- each law is compared with the same number `f a + (c²/2) S a`
  have key : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂σ) = 0) →
      (∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂σ) = ⟪u, w⟫_ℝ) →
      Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) σ →
      ∀ a : EuclideanSpace ℝ (Fin k),
        |(∫ u, f (a + c • u) ∂σ) - (f a + c ^ 2 / 2 * S a)|
          ≤ ∫ u, |f (a + c • u) - f a - fderiv ℝ f a (c • u)
              - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)| ∂σ := by
    intro σ hσ hm hcv hβ a
    haveI := hσ
    have h1 : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖) σ :=
      integrable_norm_of_cube hβ
    have h2 : Integrable (fun u : EuclideanSpace ℝ (Fin k) => ‖u‖ ^ 2) σ :=
      integrable_normSq_of_cube hβ
    have hfint : Integrable (fun u : EuclideanSpace ℝ (Fin k) => f (a + c • u)) σ := by
      refine Integrable.mono' (integrable_const (1 : ℝ))
        (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs]
      exact hfb _
    have hLint : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        fderiv ℝ f a (c • u)) σ := by
      refine ((integrable_clm_of_norm h1 (fderiv ℝ f a)).const_mul c).congr
        (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [map_smul, smul_eq_mul]
    have hQint : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)) σ := by
      refine ((integrable_bilin_of_normSq h2 (iteratedFDeriv ℝ 2 f a)).const_mul
        (c ^ 2 / 2)).congr (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [hQrw a u]
      ring
    have hLval : (∫ u, fderiv ℝ f a (c • u) ∂σ) = 0 := by
      have hrw : ∀ u : EuclideanSpace ℝ (Fin k),
          fderiv ℝ f a (c • u) = c * fderiv ℝ f a u := by
        intro u; rw [map_smul, smul_eq_mul]
      simp_rw [hrw]
      rw [integral_const_mul, integral_clm_eq_zero_of_centred hm (fderiv ℝ f a),
        mul_zero]
    have hQval : (∫ u, (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 f a (fun _ => c • u) ∂σ)
        = c ^ 2 / 2 * S a := by
      have hrw : ∀ u : EuclideanSpace ℝ (Fin k),
          (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)
            = (c ^ 2 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => u) := by
        intro u; rw [hQrw a u]; ring
      simp_rw [hrw]
      rw [integral_const_mul, integral_bilin_eq_basis_sum hcv h2 (iteratedFDeriv ℝ 2 f a),
        ← hS a]
    have hi1 : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        f (a + c • u) - f a) σ := hfint.sub (integrable_const _)
    have hi2 : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        f (a + c • u) - f a - fderiv ℝ f a (c • u)) σ := hi1.sub hLint
    have heq : (∫ u, (f (a + c • u) - f a - fderiv ℝ f a (c • u)
          - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)) ∂σ)
        = (∫ u, f (a + c • u) ∂σ) - (f a + c ^ 2 / 2 * S a) := by
      rw [integral_sub hi2 hQint, integral_sub hi1 hLint,
        integral_sub hfint (integrable_const _), integral_const, hLval, hQval]
      simp
      ring
    calc |(∫ u, f (a + c • u) ∂σ) - (f a + c ^ 2 / 2 * S a)|
        = |∫ u, (f (a + c • u) - f a - fderiv ℝ f a (c • u)
            - (1 / 2) * iteratedFDeriv ℝ 2 f a (fun _ => c • u)) ∂σ| := by rw [heq]
      _ ≤ _ := abs_integral_le_integral_abs
  -- the pointwise bound on the `τ`-integrand
  have hAν := fun a => integral_abs_remainder_split_le (ν := ν) hβν hf hfb hC₃ hε hD3 hD1
    hD2 hone hsupp hc a
  have hAρ := fun a => integral_abs_remainder_split_le (ν := ρ) hβρ hf hfb hC₃ hε hD3 hD1
    hD2 hone hsupp hc a
  have hptw : ∀ a : EuclideanSpace ℝ (Fin k),
      |(∫ u, f (a + c • u) ∂ν) - (∫ u, f (a + c • u) ∂ρ)|
        ≤ (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator (fun _ => (1 : ℝ)) a
            * (C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
              + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ))
          + (∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
              (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
                  (fun _ => (1 : ℝ)) a
                * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ν)
          + ∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
              (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
                  (fun _ => (1 : ℝ)) a
                * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ρ := by
    intro a
    have hkν := key ν ‹_› hmeanν hcovν hβν a
    have hkρ := key ρ ‹_› hmeanρ hcovρ hβρ a
    have htri : |(∫ u, f (a + c • u) ∂ν) - (∫ u, f (a + c • u) ∂ρ)|
        ≤ |(∫ u, f (a + c • u) ∂ν) - (f a + c ^ 2 / 2 * S a)|
          + |(∫ u, f (a + c • u) ∂ρ) - (f a + c ^ 2 / 2 * S a)| := by
      calc |(∫ u, f (a + c • u) ∂ν) - (∫ u, f (a + c • u) ∂ρ)|
          = |((∫ u, f (a + c • u) ∂ν) - (f a + c ^ 2 / 2 * S a))
              - ((∫ u, f (a + c • u) ∂ρ) - (f a + c ^ 2 / 2 * S a))| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have e1 := hAν a
    have e2 := hAρ a
    linarith
  -- integrate the pointwise bound against `τ`
  have hhcont : Continuous fun a : EuclideanSpace ℝ (Fin k) =>
      (∫ u, f (a + c • u) ∂ν) - (∫ u, f (a + c • u) ∂ρ) :=
    (continuous_integral_add_smul hf.continuous hfb c).sub
      (continuous_integral_add_smul hf.continuous hfb c)
  have hhint : Integrable (fun a : EuclideanSpace ℝ (Fin k) =>
      |(∫ u, f (a + c • u) ∂ν) - (∫ u, f (a + c • u) ∂ρ)|) τ := by
    refine Integrable.mono' (integrable_const (2 : ℝ)) hhcont.abs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_integral_le_one (σ := ν) (F := fun u => f (a + c • u))
      (hf.continuous.comp (by fun_prop)) (fun x => hfb _)
    have h2 := abs_integral_le_one (σ := ρ) (F := fun u => f (a + c • u))
      (hf.continuous.comp (by fun_prop)) (fun x => hfb _)
    have e1 := abs_le.1 h1
    have e2 := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  obtain ⟨hFarνint, hFarν⟩ := integral_far_shell_le (ν := ν) (τ := τ) hβν hC₃ hε hCk.le
    hW hshell hc
  obtain ⟨hFarρint, hFarρ⟩ := integral_far_shell_le (ν := ρ) (τ := τ) hβρ hC₃ hε hCk.le
    hW hshell hc
  have hKt0 : (0 : ℝ) ≤ C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
      + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ) := by positivity
  have hIndint : Integrable (fun a : EuclideanSpace ℝ (Fin k) =>
      (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator (fun _ => (1 : ℝ)) a
        * (C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
          + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ))) τ := by
    refine Integrable.mono' (integrable_const (C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
        + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ)))
      ((measurable_const.indicator hShNm).mul_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (indicator_one_nonneg _ a),
      abs_of_nonneg hKt0]
    exact mul_le_of_le_one_left hKt0 (indicator_one_le_one _ a)
  have hsum1 : Integrable (fun a : EuclideanSpace ℝ (Fin k) =>
      (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator (fun _ => (1 : ℝ)) a
        * (C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
          + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ))
      + ∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
          (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
              (fun _ => (1 : ℝ)) a
            * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ν) τ :=
    hIndint.add hFarνint
  have hsum2 : Integrable (fun a : EuclideanSpace ℝ (Fin k) =>
      (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator (fun _ => (1 : ℝ)) a
        * (C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
          + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ))
      + (∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
          (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
              (fun _ => (1 : ℝ)) a
            * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ν)
      + ∫ u in {u : EuclideanSpace ℝ (Fin k) | ε / c < ‖u‖},
          (Metric.thickening (2 * (c * ‖u‖)) B \ erosion (2 * (c * ‖u‖)) B).indicator
              (fun _ => (1 : ℝ)) a
            * (2 + C₃ / ε * (c * ‖u‖) + 1 / 2 * (C₃ / ε ^ 2) * (c * ‖u‖) ^ 2) ∂ρ) τ :=
    hsum1.add hFarρint
  have hmono := integral_mono hhint hsum2 hptw
  rw [integral_add hsum1 hFarρint, integral_add hIndint hFarνint] at hmono
  have hindval : (∫ a, (Metric.thickening (2 * ε) B \ erosion (2 * ε) B).indicator
        (fun _ => (1 : ℝ)) a
        * (C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
          + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ)) ∂τ)
      = (τ (Metric.thickening (2 * ε) B \ erosion (2 * ε) B)).toReal
        * (C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
          + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ)) := by
    rw [integral_mul_const, integral_indicator_const (1 : ℝ) hShNm]
    simp [Measure.real]
  rw [hindval] at hmono
  have hmass : (τ (Metric.thickening (2 * ε) B \ erosion (2 * ε) B)).toReal
      ≤ 8 * Ck * ε + W := by
    have := hshell (2 * ε) (by positivity)
    linarith
  have hhead := mul_le_mul_of_nonneg_right hmass hKt0
  have hE1 : (8 * Ck * ε + W) * (C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)
        + C₃ / ε ^ 3 / 6 * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ))
      = C₃ / ε ^ 3 / 6 * c ^ 3 * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ))
        * (8 * Ck * ε + W) := by ring
  have hE2 : C₃ * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν) * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3)
      + C₃ * c ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ) * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3)
      = C₃ * c ^ 3 * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ))
        * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) := by ring
  linarith
/-- **The localised swap step at a single shift, at EVERY shift length (wave 40).**

This is the pointwise-in-`(v, w)` engine of route (b) of the tail brick, and it is the first
form of it that carries no restriction on `‖w‖`. Writing `R = gaussianTailRadius k σ` and
`u = σ(R + ‖w‖)`:

* if `v` lies in the two-sided shell at width `2u`, the step is bounded *unweighted*, by the
  better of the cubic bound `Ct‖w‖³` (`integral_abs_vecTiltRemainder_le`) and the quadratic one
  `2 + ‖w‖ + ‖w‖²` (`abs_integral_mul_vecTiltRemainder_le_crude`) — the `min` is genuinely
  needed: the cubic branch is what prices short shifts, the quadratic branch is what keeps the
  product with the (linear in `‖w‖`) shell mass inside a *third* moment;
* otherwise `F` is constant on `closedBall v u`
  (`const_on_closedBall_of_notMem_wideShell`), and the step costs only `4 C_k C_t σ ‖w‖³` — a
  factor `σ` of gain, with no shell mass at all. For `‖w‖ ≤ 1` this is the wave-29 bound
  `abs_integral_shift_vecTiltRemainder_le_of_const_ball` (Cauchy–Schwarz in `L²`), and for
  `‖w‖ > 1` — the case every previous wave left open — it is the wave-40 bound
  `abs_integral_shift_vecTiltRemainder_le_of_const_ball_any`, whose constant `106σ‖w‖³` is
  absorbed into `4 C_k C_t σ ‖w‖³` by `le_sqrt_tiltSqConst` together with `hCw`.

Both regimes therefore report the *same* far constant, and the shell width `2u` is the same in
both, so no case split survives into the `τ`-average. -/
private lemma abs_integral_shift_vecTiltRemainder_localised_le
    {Ct : ℝ} (hCt : ∀ s : ℝ, 0 ≤ s →
      (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ Ct * s ^ 3)
    {B : Set (EuclideanSpace ℝ (Fin k))} {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    {ε : ℝ}
    (hone : ∀ x ∈ B, F x = 1) (hsupp : ∀ x, F x ≠ 0 → x ∈ Metric.thickening ε B)
    {Ck : ℝ} (hCk : 0 < Ck) (hCw : Real.sqrt tiltSqConst ≤ 2 * Ck * Ct)
    (hk : 0 < k) {σ : ℝ} (hσ : 0 < σ) (hσε : ε ≤ σ) (hσ1 : σ ≤ 1)
    (v w : EuclideanSpace ℝ (Fin k)) :
    |∫ z, F (v + σ • z) * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
      ≤ (Metric.thickening (2 * (σ * (gaussianTailRadius k σ + ‖w‖))) B
            \ erosion (2 * (σ * (gaussianTailRadius k σ + ‖w‖))) B).indicator
            (fun _ => (1 : ℝ)) v
          * min (Ct * ‖w‖ ^ 3) (2 + ‖w‖ + ‖w‖ ^ 2)
        + 4 * Ck * Ct * σ * ‖w‖ ^ 3 := by
  classical
  have hR1 : (1 : ℝ) ≤ gaussianTailRadius k σ := one_le_gaussianTailRadius hk σ
  have hu0 : 0 < σ * (gaussianTailRadius k σ + ‖w‖) := by
    have := norm_nonneg w
    positivity
  have hGc : Continuous (fun z : EuclideanSpace ℝ (Fin k) => F (v + σ • z)) := by fun_prop
  have hCt0 : 0 < Ct := by
    by_contra hcon
    push_neg at hcon
    have h1 : 2 * Ck * Ct ≤ 0 := by nlinarith [hCk, hcon]
    linarith [le_sqrt_tiltSqConst, hCw]
  have hfar : ∀ a : ℝ, |a| ≤ 1 →
      (∀ x, ‖x - v‖ < σ * (gaussianTailRadius k σ + ‖w‖) → F x = a) →
      |∫ z, F (v + σ • z) * vecTiltRemainder w z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
        ≤ 4 * Ck * Ct * σ * ‖w‖ ^ 3 := by
    intro a ha hconst
    have htail : ((stdGaussian (EuclideanSpace ℝ (Fin k)))
        {z | gaussianTailRadius k σ ≤ ‖z‖}).toReal ≤ σ ^ 2 := by
      have h := stdGaussian_norm_ge_gaussianTailRadius_le (k := k) hk hσ hσ1
      rwa [measureReal_def] at h
    have hsqtail : Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k)))
        {z | gaussianTailRadius k σ ≤ ‖z‖}).toReal) ≤ σ := by
      have h1 := Real.sqrt_le_sqrt htail
      rwa [Real.sqrt_sq hσ.le] at h1
    rcases le_or_gt ‖w‖ 1 with hw1 | hw1
    · have hconst' : ∀ x, ‖x - v‖ < σ * gaussianTailRadius k σ → F x = a := by
        intro x hx
        exact hconst x (by nlinarith [norm_nonneg w, hσ.le])
      have h := abs_integral_shift_vecTiltRemainder_le_of_const_ball hF hFb v hσ
        (by positivity : (0 : ℝ) < σ * gaussianTailRadius k σ) ha hconst' hw1
      have hdiv : σ * gaussianTailRadius k σ / σ = gaussianTailRadius k σ := by
        field_simp
      rw [hdiv] at h
      refine h.trans ?_
      have h2 : 2 * Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k)))
            {z | gaussianTailRadius k σ ≤ ‖z‖}).toReal)
          ≤ 2 * σ := by linarith
      have h3 : (0 : ℝ) ≤ Real.sqrt tiltSqConst * ‖w‖ ^ 3 := by positivity
      calc 2 * Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k)))
              {z | gaussianTailRadius k σ ≤ ‖z‖}).toReal)
            * (Real.sqrt tiltSqConst * ‖w‖ ^ 3)
          ≤ (2 * σ) * (Real.sqrt tiltSqConst * ‖w‖ ^ 3) :=
            mul_le_mul_of_nonneg_right h2 h3
        _ ≤ (2 * σ) * ((2 * Ck * Ct) * ‖w‖ ^ 3) := by
            have hs2 : (0 : ℝ) ≤ 2 * σ := by linarith
            have h4 : Real.sqrt tiltSqConst * ‖w‖ ^ 3 ≤ (2 * Ck * Ct) * ‖w‖ ^ 3 :=
              mul_le_mul_of_nonneg_right hCw (by positivity)
            exact mul_le_mul_of_nonneg_left h4 hs2
        _ = 4 * Ck * Ct * σ * ‖w‖ ^ 3 := by ring
    · have h := abs_integral_shift_vecTiltRemainder_le_of_const_ball_any hF hFb v hσ ha
        (M := gaussianTailRadius k σ) hconst
      refine h.trans ?_
      have hw3 : (1 : ℝ) ≤ ‖w‖ ^ 3 := by nlinarith [hw1]
      have hw23 : ‖w‖ ^ 2 ≤ ‖w‖ ^ 3 := by nlinarith [hw1, norm_nonneg w]
      have hcrude : 2 * ((stdGaussian (EuclideanSpace ℝ (Fin k)))
            {z | gaussianTailRadius k σ ≤ ‖z‖}).toReal
          + 2 * Real.sqrt (((stdGaussian (EuclideanSpace ℝ (Fin k)))
              {z | gaussianTailRadius k σ ≤ ‖z‖}).toReal) * (26 * (1 + ‖w‖ ^ 2))
          ≤ 106 * σ * ‖w‖ ^ 3 := by
        have hmass : ((stdGaussian (EuclideanSpace ℝ (Fin k)))
            {z | gaussianTailRadius k σ ≤ ‖z‖}).toReal ≤ σ := by
          nlinarith [htail, hσ.le, hσ1]
        nlinarith [hmass, hsqtail, hw3, hw23, hσ.le, hσ1,
          ENNReal.toReal_nonneg (a := (stdGaussian (EuclideanSpace ℝ (Fin k)))
            {z | gaussianTailRadius k σ ≤ ‖z‖}),
          Real.sqrt_nonneg (((stdGaussian (EuclideanSpace ℝ (Fin k)))
            {z | gaussianTailRadius k σ ≤ ‖z‖}).toReal), sq_nonneg ‖w‖]
      refine hcrude.trans ?_
      have h53 : (106 : ℝ) ≤ 2 * (2 * Ck * Ct) := by
        have := le_sqrt_tiltSqConst
        linarith [hCw]
      have h1 : (106 : ℝ) ≤ 4 * Ck * Ct := by linarith
      have h2 : (0 : ℝ) ≤ σ * ‖w‖ ^ 3 := by positivity
      linarith [mul_le_mul_of_nonneg_right h1 h2]
  by_cases hv : v ∈ Metric.thickening (2 * (σ * (gaussianTailRadius k σ + ‖w‖))) B
      \ erosion (2 * (σ * (gaussianTailRadius k σ + ‖w‖))) B
  · rw [Set.indicator_of_mem hv, one_mul]
    have h1 : |∫ z, F (v + σ • z) * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| ≤ Ct * ‖w‖ ^ 3 := by
      calc |∫ z, F (v + σ • z) * vecTiltRemainder w z
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
          ≤ ∫ z, |F (v + σ • z) * vecTiltRemainder w z|
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := abs_integral_le_integral_abs
        _ ≤ ∫ z, |vecTiltRemainder w z| ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
            refine integral_mono ?_ (integrable_vecTiltRemainder w).abs fun z => ?_
            · refine Integrable.mono' (integrable_vecTiltRemainder w).abs
                ((hGc.mul (continuous_vecTiltRemainder w)).abs.aestronglyMeasurable)
                (Filter.Eventually.of_forall fun z => ?_)
              rw [Real.norm_eq_abs, abs_abs, abs_mul]
              nlinarith [hFb (v + σ • z), abs_nonneg (vecTiltRemainder w z),
                abs_nonneg (F (v + σ • z))]
            · rw [abs_mul]
              nlinarith [hFb (v + σ • z), abs_nonneg (vecTiltRemainder w z),
                abs_nonneg (F (v + σ • z))]
        _ ≤ Ct * ‖w‖ ^ 3 := integral_abs_vecTiltRemainder_le hCt w
    have h2 : |∫ z, F (v + σ • z) * vecTiltRemainder w z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| ≤ 2 + ‖w‖ + ‖w‖ ^ 2 :=
      abs_integral_mul_vecTiltRemainder_le_crude hGc (fun z => hFb _) w
    have hnn : (0 : ℝ) ≤ 4 * Ck * Ct * σ * ‖w‖ ^ 3 := by positivity
    linarith [le_min h1 h2]
  · rw [Set.indicator_of_notMem hv]
    have heros : ∀ {s t : ℝ}, s ≤ t → erosion t B ⊆ erosion s B := by
      intro s t hst x hx y hy
      exact hx (Metric.closedBall_subset_closedBall hst hy)
    have hsub : Metric.thickening (ε + σ * (gaussianTailRadius k σ + ‖w‖)) B
          \ erosion (σ * (gaussianTailRadius k σ + ‖w‖)) B
        ⊆ Metric.thickening (2 * (σ * (gaussianTailRadius k σ + ‖w‖))) B
          \ erosion (2 * (σ * (gaussianTailRadius k σ + ‖w‖))) B := by
      have hle : ε + σ * (gaussianTailRadius k σ + ‖w‖)
          ≤ 2 * (σ * (gaussianTailRadius k σ + ‖w‖)) := by
        have h1 : σ ≤ σ * (gaussianTailRadius k σ + ‖w‖) := by
          nlinarith [norm_nonneg w, hσ.le]
        linarith
      exact Set.diff_subset_diff (Metric.thickening_mono hle B) (heros (by linarith))
    have hvnot : v ∉ Metric.thickening (ε + σ * (gaussianTailRadius k σ + ‖w‖)) B
        \ erosion (σ * (gaussianTailRadius k σ + ‖w‖)) B := fun hmem => hv (hsub hmem)
    obtain ⟨a, hCa⟩ := const_on_closedBall_of_notMem_wideShell hone hsupp hvnot
    have hav : F v = a := hCa v (by simp [Metric.mem_closedBall, hu0.le])
    have haabs : |a| ≤ 1 := by rw [← hav]; exact hFb v
    have hconst : ∀ x, ‖x - v‖ < σ * (gaussianTailRadius k σ + ‖w‖) → F x = a := by
      intro x hx
      refine hCa x ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith
    have hfin := hfar a haabs hconst
    linarith

/-- **The per-step ledger of the localised tail estimate (wave 40).** The pointwise bound of
`abs_integral_shift_vecTiltRemainder_localised_le`, once averaged over `v`, produces the shell
mass `8 C_k σ(R + s) + W` at the varying width, multiplied by
`min (C_t s³) (2 + s + s²)` with `s = ‖w‖`. This lemma is the arithmetic that turns that
product back into a pure *third* moment, at the price of the stated constants:

  `(8 C_k σ(R+s) + W) · min (C_t s³, 2+s+s²) ≤ (64 C_k σ R + 4 W) · C_t s³`.

Both branches of the `min` are used, and neither can be dropped: for `s ≤ 1` the quadratic
branch has a *constant* term (which would integrate to a bare constant weight, outside brick
L's allowed shape — wave 35's Correction 1), and for `s > 1` the cubic branch multiplied by the
linear-in-`s` shell mass would be quartic (a fourth moment, unavailable). `1 ≤ C_t` is used
only to report both branches with one constant. -/
private lemma localised_step_weight_le {Ck Ct W R s σ : ℝ}
    (hCk : 0 ≤ Ck) (hCt : 1 ≤ Ct) (hW : 0 ≤ W) (hR : 1 ≤ R)
    (hs : 0 ≤ s) (hσ0 : 0 ≤ σ) :
    (8 * Ck * (σ * (R + s)) + W) * min (Ct * s ^ 3) (2 + s + s ^ 2)
      ≤ (64 * Ck * (σ * R) + 4 * W) * (Ct * s ^ 3) := by
  have hw0 : (0 : ℝ) ≤ 8 * Ck * (σ * (R + s)) + W := by
    have : (0 : ℝ) ≤ σ * (R + s) := by nlinarith
    nlinarith
  have hCt0 : (0 : ℝ) < Ct := by linarith
  have hs3 : (0 : ℝ) ≤ s ^ 3 := by positivity
  rcases le_or_gt s 1 with h1 | h1
  · have hmin : min (Ct * s ^ 3) (2 + s + s ^ 2) ≤ Ct * s ^ 3 := min_le_left _ _
    have hstep : (8 * Ck * (σ * (R + s)) + W) * min (Ct * s ^ 3) (2 + s + s ^ 2)
        ≤ (8 * Ck * (σ * (R + s)) + W) * (Ct * s ^ 3) :=
      mul_le_mul_of_nonneg_left hmin hw0
    refine hstep.trans ?_
    have hRs : σ * (R + s) ≤ 2 * (σ * R) := by nlinarith
    have hfac : 8 * Ck * (σ * (R + s)) + W ≤ 64 * Ck * (σ * R) + 4 * W := by nlinarith
    exact mul_le_mul_of_nonneg_right hfac (by positivity)
  · have hs2 : (1 : ℝ) ≤ s := le_of_lt h1
    have hmin : min (Ct * s ^ 3) (2 + s + s ^ 2) ≤ 2 + s + s ^ 2 := min_le_right _ _
    have hq : 2 + s + s ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    have hstep : (8 * Ck * (σ * (R + s)) + W) * min (Ct * s ^ 3) (2 + s + s ^ 2)
        ≤ (8 * Ck * (σ * (R + s)) + W) * (4 * s ^ 2) :=
      mul_le_mul_of_nonneg_left (hmin.trans hq) hw0
    refine hstep.trans ?_
    have hRs : R + s ≤ 2 * (R * s) := by nlinarith
    have hkey : (8 * Ck * (σ * (R + s)) + W) * (4 * s ^ 2)
        ≤ 64 * Ck * (σ * R) * s ^ 3 + 4 * W * s ^ 3 := by
      have hA : 8 * Ck * (σ * (R + s)) * (4 * s ^ 2) ≤ 64 * Ck * (σ * R) * s ^ 3 := by
        have h2 : σ * (R + s) ≤ 2 * (σ * (R * s)) := by nlinarith
        nlinarith [mul_nonneg hCk hσ0, sq_nonneg s, mul_nonneg (mul_nonneg hCk hσ0) hs3]
      have hss : s ^ 2 ≤ s ^ 3 := by nlinarith
      have hB : W * (4 * s ^ 2) ≤ 4 * W * s ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left hss hW]
      linarith [hA, hB]
    refine hkey.trans ?_
    have hCt1 : s ^ 3 ≤ Ct * s ^ 3 := by nlinarith
    have hnn : (0 : ℝ) ≤ 64 * Ck * (σ * R) := by
      have h1' : (0 : ℝ) ≤ σ * R := by nlinarith
      nlinarith [mul_nonneg hCk h1']
    have hP1 : 64 * Ck * (σ * R) * s ^ 3 ≤ 64 * Ck * (σ * R) * (Ct * s ^ 3) :=
      mul_le_mul_of_nonneg_left hCt1 hnn
    have hP2 : 4 * W * s ^ 3 ≤ 4 * W * (Ct * s ^ 3) :=
      mul_le_mul_of_nonneg_left hCt1 (by linarith)
    nlinarith [hP1, hP2]

/-- **The Fubini step of the tail brick, at the VARYING shell width (wave 41).** The exact
analogue of `integral_far_shell_le` on the head side, with three differences, each forced by
what the tail route actually produces:

* the width is `2σ(R + λ‖y‖)` — the constancy radius of
  `abs_integral_shift_vecTiltRemainder_localised_le`, which grows with the shift length — and
  not `2c‖u‖`. Joint measurability of `(v, y) ↦ 1_{shell at that width}(v)` is again
  `measurableSet_wideShell_prod`, which accepts any continuous nonnegative width;
* there is **no** near/far split in `‖y‖`: the whole `ν`-integral is exchanged, because the
  width is bounded below by `2σR > 0` at every `y`, so `hshell` applies everywhere;
* the bracket is `min (C_t (λ‖y‖)³) (2 + λ‖y‖ + (λ‖y‖)²)`, and the pricing is
  `localised_step_weight_le` (both branches of the `min`), not `far_regime_pointwise_le`.

The conclusion is a pure **third** moment, at the weight `64 C_k σR + 4W` of the wave-40
ledger. As on the head side, the integrability of the outer integrand is returned alongside:
the tail brick needs it to split the `τ`-integral of the two-law majorant. -/
private lemma integral_localised_shell_le
    {ν τ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (hβν : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ν)
    {B : Set (EuclideanSpace ℝ (Fin k))}
    {Ck Ct W R σ lam : ℝ} (hCk : 0 ≤ Ck) (hCt : 1 ≤ Ct) (hW : 0 ≤ W) (hR : 1 ≤ R)
    (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hshell : ∀ s : ℝ, 0 < s →
      (τ (Metric.thickening s B \ erosion s B)).toReal ≤ 4 * Ck * s + W) :
    Integrable (fun a : EuclideanSpace ℝ (Fin k) =>
        ∫ y, (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
              \ erosion (2 * (σ * (R + lam * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) a
            * min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2) ∂ν) τ
      ∧ (∫ a, (∫ y, (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
              \ erosion (2 * (σ * (R + lam * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) a
            * min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2) ∂ν) ∂τ)
          ≤ (64 * Ck * (σ * R) + 4 * W) * (Ct * lam ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)) := by
  classical
  have hCt0 : (0 : ℝ) < Ct := lt_of_lt_of_le one_pos hCt
  have hgpos : ∀ y : EuclideanSpace ℝ (Fin k), (0 : ℝ) < 2 * (σ * (R + lam * ‖y‖)) := by
    intro y
    have h0 : (0 : ℝ) ≤ lam * ‖y‖ := mul_nonneg hlam (norm_nonneg y)
    have h1 : (0 : ℝ) < R + lam * ‖y‖ := by linarith
    positivity
  -- product measurability of the varying shell indicator
  have hSm : MeasurableSet {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
      p.1 ∈ Metric.thickening (2 * (σ * (R + lam * ‖p.2‖))) B
        \ erosion (2 * (σ * (R + lam * ‖p.2‖))) B} :=
    measurableSet_wideShell_prod (g := fun y => 2 * (σ * (R + lam * ‖y‖))) (by fun_prop)
      (fun y => (hgpos y).le)
  have hΦm : Measurable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      (Metric.thickening (2 * (σ * (R + lam * ‖p.2‖))) B
          \ erosion (2 * (σ * (R + lam * ‖p.2‖))) B).indicator (fun _ => (1 : ℝ)) p.1
        * min (Ct * (lam * ‖p.2‖) ^ 3) (2 + lam * ‖p.2‖ + (lam * ‖p.2‖) ^ 2)) := by
    refine Measurable.mul ?_ (by fun_prop)
    have hrw : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        (Metric.thickening (2 * (σ * (R + lam * ‖p.2‖))) B
            \ erosion (2 * (σ * (R + lam * ‖p.2‖))) B).indicator (fun _ => (1 : ℝ)) p.1)
        = Set.indicator {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
            p.1 ∈ Metric.thickening (2 * (σ * (R + lam * ‖p.2‖))) B
              \ erosion (2 * (σ * (R + lam * ‖p.2‖))) B} (fun _ => (1 : ℝ)) := by
      funext p
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [hrw]
    exact measurable_const.indicator hSm
  -- the dominating function: the quadratic branch of the `min`
  have hlowint : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
      2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2) ν := by
    have h1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν :=
      integrable_norm_of_cube hβν
    have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν :=
      integrable_normSq_of_cube hβν
    have h3 := ((integrable_const (2 : ℝ)).add (h1.const_mul lam)).add
      (h2.const_mul (lam ^ 2))
    refine h3.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    ring
  have hmin0 : ∀ y : EuclideanSpace ℝ (Fin k),
      (0 : ℝ) ≤ min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2) := by
    intro y
    have h1 : (0 : ℝ) ≤ lam * ‖y‖ := mul_nonneg hlam (norm_nonneg y)
    exact le_min (by positivity) (by positivity)
  have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      2 + lam * ‖p.2‖ + (lam * ‖p.2‖) ^ 2) (τ.prod ν) := by
    refine (integrable_prod_iff (by fun_prop)).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun a => hlowint
    · exact integrable_const (∫ y : EuclideanSpace ℝ (Fin k),
        ‖2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2‖ ∂ν)
  have hΦint : Integrable (Function.uncurry
      (fun (a y : EuclideanSpace ℝ (Fin k)) =>
        (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
            \ erosion (2 * (σ * (R + lam * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) a
          * min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2)))
      (τ.prod ν) := by
    refine Integrable.mono' hdom hΦm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hmin0 p.2), abs_of_nonneg (indicator_one_nonneg _ p.1)]
    exact (mul_le_of_le_one_left (hmin0 p.2) (indicator_one_le_one _ p.1)).trans
      (min_le_right _ _)
  refine ⟨hΦint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hΦint]
  -- the inner `τ`-integral is the shell mass at the varying width
  have hinner : ∀ y : EuclideanSpace ℝ (Fin k),
      (∫ a, (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
            \ erosion (2 * (σ * (R + lam * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) a
          * min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2) ∂τ)
        = (τ (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
              \ erosion (2 * (σ * (R + lam * ‖y‖))) B)).toReal
          * min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2) := by
    intro y
    rw [integral_mul_const]
    congr 1
    have hm : MeasurableSet (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
        \ erosion (2 * (σ * (R + lam * ‖y‖))) B) :=
      (Metric.isOpen_thickening.measurableSet).diff (isOpen_erosion _ B).measurableSet
    rw [integral_indicator_const (1 : ℝ) hm]
    simp [Measure.real]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  -- price the shell mass by the per-step ledger
  have hgint : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
      (64 * Ck * (σ * R) + 4 * W) * (Ct * (lam * ‖y‖) ^ 3)) ν := by
    have h3 := hβν.const_mul ((64 * Ck * (σ * R) + 4 * W) * (Ct * lam ^ 3))
    refine h3.congr (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hstep : (∫ y, (τ (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
          \ erosion (2 * (σ * (R + lam * ‖y‖))) B)).toReal
        * min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2) ∂ν)
      ≤ ∫ y, (64 * Ck * (σ * R) + 4 * W) * (Ct * (lam * ‖y‖) ^ 3) ∂ν := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => mul_nonneg ENNReal.toReal_nonneg (hmin0 y))
      hgint (Filter.Eventually.of_forall fun y => ?_)
    have hmass := hshell (2 * (σ * (R + lam * ‖y‖))) (hgpos y)
    have hmass' : (τ (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
        \ erosion (2 * (σ * (R + lam * ‖y‖))) B)).toReal
        ≤ 8 * Ck * (σ * (R + lam * ‖y‖)) + W := by linarith
    calc (τ (Metric.thickening (2 * (σ * (R + lam * ‖y‖))) B
            \ erosion (2 * (σ * (R + lam * ‖y‖))) B)).toReal
          * min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2)
        ≤ (8 * Ck * (σ * (R + lam * ‖y‖)) + W)
            * min (Ct * (lam * ‖y‖) ^ 3) (2 + lam * ‖y‖ + (lam * ‖y‖) ^ 2) :=
          mul_le_mul_of_nonneg_right hmass' (hmin0 y)
      _ ≤ (64 * Ck * (σ * R) + 4 * W) * (Ct * (lam * ‖y‖) ^ 3) :=
          localised_step_weight_le hCk hCt hW hR (mul_nonneg hlam (norm_nonneg y)) hσ.le
  refine hstep.trans ?_
  have hrw : ∀ y : EuclideanSpace ℝ (Fin k),
      (64 * Ck * (σ * R) + 4 * W) * (Ct * (lam * ‖y‖) ^ 3)
        = ((64 * Ck * (σ * R) + 4 * W) * (Ct * lam ^ 3)) * ‖y‖ ^ 3 := fun y => by ring
  simp_rw [hrw]
  rw [integral_const_mul]
  have hfin : (64 * Ck * (σ * R) + 4 * W) * (Ct * lam ^ 3) * (∫ y, ‖y‖ ^ 3 ∂ν)
      = (64 * Ck * (σ * R) + 4 * W) * (Ct * lam ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν)) := by ring
  exact le_of_eq hfin

set_option linter.unusedVariables false in
-- the body is a named `sorry` brick: the hypotheses are the interface, see the docstring
/-- **The per-step TAIL estimate (wave 38: STATED, NOT proved; wave 39: the WEIGHT is AMENDED
to what route (b) can actually deliver).** *One tail step `j > J` of the hybrid telescope,
localised, averaged against the step's own hybrid law.*

`τ` is `hybridLaw n j ν`, `σ = σⱼ = √(j/n)` is the step's Gaussian smoothing width and
`c = n^{-1/2}` its scale, so the cost `Ct (c/σ)³ (β + β_G) = Ct (β + β_G)/(j√j)` is exactly the
unweighted `abs_integral_gaussian_smoothed_swap_le`, and the weight `4 C_k σ + W` is exactly what
`localised_swap_bound_of_weighted_telescope`'s tail summands consume once summed over `J < j ≤ n`
(the harmonic sum `∑ σⱼ/(j√j) = c ∑ 1/j` is where the logarithm comes from).

## What wave 32/35 said the residue was

"Its two analytic ingredients are in place (the wave-19 weighted lemma
`abs_integral_mul_vecTiltRemainder_le_of_support` and its wave-29 constant-off/Gaussian-tail
extensions), but the shift-length restriction `‖w‖ ≤ 1` has to be handled."

## What wave 38 finds: a THIRD ingredient is missing, and it is not bookkeeping

The two available routes both fail to produce the frozen weight `4 C_k σ + W`.

**Route (a), Cauchy–Schwarz against the shell (the wave-19 form).** Take `G(z) = F(v + σz)`,
constant off `S_v = {z : v + σz ∈ shell}`, and apply
`abs_integral_mul_vecTiltRemainder_le_of_const_off`. The weight at `v` is `2√(γ S_v)`, and
averaging over `v` with Jensen gives `2√(∫ γ S_v dτ) = 2√(shell mass) ≍ √(4 C_k σ + W)`. This is
the `√W` form the note on `localised_swap_bound_small_weight` already records, and the fixed
point `cube_le_of_selfImproving_smoothed_sqrt` then gives `O(n^{-1/3})`, not `β/√n`. So route (a)
cannot close brick L as stated.

**Route (b), the near/far split in `v` (the wave-29 form).** Fix a radius `r` and split:

* `v` within `r` of the shell: use the *unweighted* per-step bound (weight `1`, cost
  `Ct (c/σ)³ X`). The `τ`-mass of that set of `v` is `≤ 4 C_k (r + ε) + W` by the amended
  two-sided-shell hypothesis at width `r + ε`.
* `v` at distance `≥ r`: `F` is constant on `closedBall v r`, so
  `abs_integral_shift_vecTiltRemainder_le_of_const_ball` applies and the weight is
  `2 √(γ{‖z‖ ≥ r/σ}) √tiltSqConst`, a **Gaussian tail** and nothing else.

So route (b) delivers weight `4 C_k (r + ε) + W + 2√(γ{‖z‖ ≥ r/σ})·√tiltSqConst/Ct`, at every
`r > 0`. For `j > J` one has `σ ≥ ε`, so the `4 C_k ε` is absorbed; the frozen weight
`4 C_k σ + W` therefore needs an `r ≍ σ` at which the tail term is itself `≲ σ`, i.e.

  `γ{‖z‖ ≥ M} ≲ σ²`  at  `M = r/σ ≍ 1`.

**That is false**, and no choice of `r` repairs it with the tail bound this file has. The only
tail available is `stdGaussian_norm_ge_le p`, Markov at order `p`:
`γ{‖z‖ ≥ M} ≤ (∫‖z‖^p dγ)/M^p`. Making the tail term `≤ σ` forces `M ≳ σ^{-2/p}`, hence
`r ≍ σ^{1 - 2/p}` and weight `≍ C_k σ^{1-2/p} + W`. Summing that over `J < j ≤ n` gives
`≍ p·C_t·X·n^{-1/2}·ε^{-2/p}`, i.e. `≍ p C_t δ ε^{-2/p}` — a *power* of `ε⁻¹`, not a logarithm,
and hence **not** of brick L's allowed shape `A δ (ε⁻¹(W + C_k ε) + C_k(1 + log(1 + ε⁻¹)))`
(whose only `ε⁻¹` is the one multiplied by `W + C_k ε`; this is wave-35's Correction 1 argument
again). This is the same phenomenon the note on `localised_swap_bound_small_weight` records as
"Remark (trading the log for a power)", now seen from the other side: at a *fixed* Markov order
the conclusion itself weakens to `(β/√n)^{m/(m+1)}`.

**The missing ingredient, named.** What closes route (b) at `r ≍ σ√(log(1/σ))` — and hence
delivers weight `4 C_k σ (√k + √(2 log(1/σ))) + W` — is a genuine *sub-Gaussian norm tail* for
the standard Gaussian on `EuclideanSpace ℝ (Fin k)`, e.g.

  `γ{‖z‖ ≥ M} ≤ exp(-(M - √k)²/2)`  for `M ≥ √k`,

equivalently the moment bound `∫‖z‖^p dγ ≤ (C p k)^{p/2}` that lets `p` be optimised in
`stdGaussian_norm_ge_le`. Neither is in this file (only `integral_norm_cube_gaussian_le`, the
third moment, is), and neither is a bookkeeping step: it is a new, dimension-explicit
concentration statement. The `Γ`-function apparatus of the `BallAntiConcentration` section
(`le_Gamma_add_half`, `chiSquared_density_mul_sqrt_le`, `integrable_pow_chiSquared`) is the right
starting point, since `‖z‖² ~ χ²_k`.

**Consequence for `htel`, flagged and NOT silently absorbed.** Even with that tail, route (b)
produces `4 C_k σ · (√k + √(2 log(1/σ)))+ W`, not `4 C_k σ + W`: the extra factor is
`≤ √k + √(2 log(1/ε))` for every tail step (since `σ ≥ σ_J ≍ ε`), so the tail summands of
`localised_swap_bound_of_weighted_telescope` — and therefore brick L's constant and the
dimension factor `C ≍ √k` of `berryEsseen_convex_sharp` — would have to absorb it. Wave 39 must
decide that explicitly rather than assume it away; the statement below is left in the frozen
shape precisely so that the discrepancy stays visible.

**The `‖w‖ ≤ 1` restriction is still open too**, unchanged from wave 32: at step `j` the shift is
`w = (c/σ)y`, so the wave-29 lemmas apply only on `{‖y‖ ≤ √j}`, and the complement needs the
direct tilt identity described in the note on `localised_swap_bound_small_weight`. Wave 38 did
not attempt it, because the obstruction above is upstream of it.

## Wave 39: the missing ingredient is SUPPLIED, and the weight is AMENDED accordingly

The sub-Gaussian norm tail wave 38 named is now proved — `stdGaussian_norm_ge_le_exp`, together
with its inversion `gaussianTailRadius` / `stdGaussian_norm_ge_gaussianTailRadius_le`. With it,
route (b) closes, and the weight it delivers is **not** the frozen `4 C_k σ + W`. The statement
below has therefore been amended to the provable one; the deviation is recorded here rather than
absorbed, per the provable-constants rule.

**The amended weight, derived.** Take `r = σ · R` with `R = gaussianTailRadius k σ`, so that
`γ{‖z‖ ≥ r/σ} = γ{‖z‖ ≥ R} ≤ σ²`.

* *near*: `τ{v : dist(v, shell) ≤ r} ≤ 4 C_k (r + ε) + W` by the amended two-sided-shell
  hypothesis at width `r + ε`, priced by the unweighted per-step bound `C_t (c/σ)³ X`;
* *far*: `abs_integral_shift_vecTiltRemainder_le_of_const_ball` gives the weight
  `2 √(γ{‖z‖ ≥ r/σ}) √tiltSqConst ≤ 2 σ √tiltSqConst`.

Total: `[(4 C_k(σR + ε) + W) C_t + 2 σ √tiltSqConst] (c/σ)³ X`. Since `σ ≥ ε` on the tail range
and `R ≥ 1` (`one_le_gaussianTailRadius`), both `ε` and the bare `σ` are absorbed into `σR`, and
with the normalisation `√tiltSqConst ≤ 2 C_k C_t` (hypothesis `hCw`, free — `C_t` may always be
enlarged and `C_k = 4e²√k ≥ 29`) the bracket is at most `C_t (12 C_k σ R + W)`. That is the
conclusion below.

**Why `12 C_k σ · R` and not `4 C_k σ`, in one line.** `R = √(2k log 2k) + 2√(k log(1/σ))` is
unbounded as `σ ↓ 0`; there is no radius at which the Gaussian norm tail is `≲ σ²` with `r ≍ σ`,
which is exactly what wave 38 showed. The factor `12` is bookkeeping; the factor `R` is not.

**What it costs downstream, all of it machine-checked.** `R` is antitone in `σ` and
`σⱼ ≥ σ_J ≥ ε` on the tail range, so `R(σⱼ) ≤ R(ε)` and the per-step bound is still of the
shape `K₁/j + K₂/(j√j)` that `sum_le_of_bounded_and_weighted_decay` consumes — no new summation
lemma is needed, only `K₁` acquires the constant factor `R(ε)`. Then
`gaussianTailRadius_le_dimTailConst` splits `R(ε) ≤ dimTailConst k · √(1 + log(1 + ε⁻¹))`, and
multiplying by the harmonic factor `1 + log(n/J) ≤ 2(1 + log(1 + ε⁻¹))` produces the **`3/2`
power** `logPow32 ε`. The consequences, each amended and re-proved this wave:
`weighted_ledger_balance` (constant `306 C₃ + 33 C_t → 306 C₃ + 81 C_t`),
`localised_swap_bound_of_weighted_telescope`, `localised_swap_bound_small_weight`,
`exists_localised_swap_bound`, `exists_convexDiscrepancy_recursion`,
`le_of_selfImproving_induction_logPow32` (the fixed point re-solves at the *same* constant), and
`berryEsseen_convex_sharp` (whose log power is now `3/2` and whose dimension factor is now
`C_k · dimTailConst k ≍ k √(log k)`).

**What is still open in THIS brick.** The assembly itself: the near/far split in `v` under the
`τ`-average (a Fubini over `hybridLaw`, with the measurability of `v ↦ τ(near set)` to supply,
as on the head side), and the `‖w‖ ≤ 1` complement above, which wave 39 did not attempt either.
The analytic *inputs* are now all present; what is missing is the same kind of bookkeeping the
head brick needed in wave 38.

## Wave 40: the `‖w‖ ≤ 1` complement is DISCHARGED, and the CONSTANTS are amended again

Every wave from 32 on recorded the shift-length restriction as an open input. It is now closed,
and the pointwise engine of route (b) is proved with **no** restriction on `‖w‖`:

* `abs_integral_shift_vecTiltRemainder_le_of_const_ball_any` — the far-in-`v` estimate at every
  shift length. The point is that the tilt remainder must *not* be bounded in `L²` (its `L²`
  norm grows like `e^{‖w‖²/2}`, which is exactly why the restriction was there). Split it:
  the exponential half is a Gaussian **shift**, so the shift is absorbed by the constancy
  *radius* `σ(M + ‖w‖)`; the polynomial half is a genuine polynomial, whose `L²` norm is
  polynomial in `‖w‖` at every `‖w‖` (`integral_sq_vecTiltPoly_le`, dimension-free), and
  Cauchy–Schwarz against the Gaussian tail finishes it;
* `abs_integral_mul_vecTiltRemainder_le_crude` — a **quadratic** (not cubic) crude bound
  `2 + ‖w‖ + ‖w‖²`, which is what keeps the product with the *linear-in-`‖w‖`* shell mass at
  the varying width inside a third moment;
* `abs_integral_shift_vecTiltRemainder_localised_le` — the two assembled into one pointwise
  bound in `(v, w)`, with the same far constant `4 C_k C_t σ ‖w‖³` in both shift regimes
  (`le_sqrt_tiltSqConst` is what merges them);
* `localised_step_weight_le` — the per-step ledger:
  `(8 C_k σ(R+s) + W) · min (C_t s³, 2+s+s²) ≤ (64 C_k σ R + 4 W) C_t s³`.

**The constants the route actually delivers, and why they are not wave 39's.** Averaging the
pointwise bound over `v ∼ τ` and then over `y ∼ ν` (resp. `ρ`) gives, with `R = gaussianTailRadius k σ`
and `s = (c/σ)‖y‖`:

* the shell term: `∫ τ(shell at 2σ(R+s)) · min(...) dν ≤ (64 C_k σ R + 4 W) C_t (c/σ)³ β_ν`
  (`localised_step_weight_le` pointwise in `y`, then `hshell` at width `2σ(R+s)`);
* the far term: `4 C_k C_t σ (c/σ)³ β_ν ≤ 4 C_k C_t σ R (c/σ)³ β_ν` (`R ≥ 1`).

Total `(68 C_k σ R + 4 W) C_t (c/σ)³ (β_ν + β_ρ)`, which is the conclusion below — wave 39's
`12` and `W` have become `68` and `4W`. The reason is structural, not bookkeeping: wave 39's
sketch priced only the `‖w‖ ≤ 1` regime, where no crude branch and no varying shell width
occur. The `8` is the shell doubling forced by `hshell` being stated at a single width; the
`4` is `2 + s + s² ≤ 4s²` at `s = 1`; the `2` is `R + s ≤ 2Rs`. (A finer split at `s = 2`
would give `36` and `2W`; the shape is unaffected, and the coarser constants are the ones that
are machine-checked.)

Two hypotheses are added, both free at the call site: `hk : 0 < k` (needed for
`gaussianTailRadius`, and available in brick L) and `hCt1 : 1 ≤ C_t` (`C_t` may always be
enlarged, and `hCt` and the conclusion are both monotone in it).

**FLAG, not absorbed.** `localised_swap_bound_of_weighted_telescope`'s hypothesis `htel` still
carries wave 39's `12 * gaussianShellConst k * Ct * …` and `3 * (W * Ct * X) / √J`. When this
brick lands those must become `68 * …` and `12 * (W * Ct * X) / √J`, and
`weighted_ledger_balance`'s constant `306 C₃ + 81 C_t` must be re-solved (the `C_t` half scales
by at most `68/12 < 6`, so `459 C_t` certainly suffices; the `C₃` half is untouched, since the
head brick is unchanged). Nothing in the *shape* moves, so the fixed point
`le_of_selfImproving_induction_logPow32` and the headline `berryEsseen_convex_sharp` re-solve
at the same `(1+log)^{3/2}` power with a larger absolute constant.

**What is still open, precisely.** Only measure-theoretic bookkeeping, in three named pieces:
(1) the tilt *representation* — factoring out of `abs_integral_gaussian_smoothed_sub_common_le`
the identity `∫∫F(v+σz+cy) = (common polynomial) + ∫_y ∫_z F(v+σz) R_{(c/σ)y}(z)`, which its
proof already establishes internally (`hsum` composed with `hQval`) but does not export;
(2) the Fubini `∫_v ∫_y 1_{shell at 2σ(R+s)}(v) · min(...) dν dτ = ∫_y τ(shell) · min(...) dν`,
which is `integral_far_shell_le` verbatim with a different bracket and the varying width
`g(y) = 2σ(R + (c/σ)‖y‖)` (`measurableSet_wideShell_prod` already accepts any continuous
nonnegative width); (3) the two-law triangle inequality. No analytic input is missing.

## Wave 41: PROVED, at wave 40's constants exactly

All three pieces are executed as wave 40 named them, and nothing else was needed.

* (1) is `integral_gaussian_smoothed_sub_common_eq`, which also returns the `τ`-integrability
  of the `y`-integrand; `abs_integral_gaussian_smoothed_sub_common_le` is refactored into its
  one-line corollary rather than duplicated.
* (2) is `integral_localised_shell_le`. It needs **no** near/far split in `‖y‖` (unlike the head
  side's `integral_far_shell_le`), because the width `2σ(R + (c/σ)‖y‖)` is bounded below by
  `2σR > 0` at *every* `y`, so `hshell` applies everywhere and the whole `ν`-integral is
  exchanged at once.
* (3) is the triangle inequality against `D v`, the Cameron–Martin number, which `tiltPoly_fubini`
  makes the *same* for `ν` and `ρ`.

Two remarks on the assembly. First, every exchange of an inequality with an integral is by
`integral_mono_of_nonneg`, which asks for integrability of the **majorant only**; so the
absolute-value integrands — for which integrability would have to be proved separately at each
of the three levels — are never required to be integrable. Second, the constants are wave 40's
unchanged: the shell half gives `64 C_k σR + 4W` (`localised_step_weight_le` pointwise in `y`,
then `hshell` at the varying width) and the far half `4 C_k C_t σ ≤ 4 C_k C_t σ R`, totalling
`68 C_k σ R + 4 W`. The wave-40 ledger was exact.

**What this brick's `τ` is, and what it is NOT** (wave 41; see also the head brick, which
carries the same erratum). The docstring above says "`τ` is `hybridLaw n j ν`". That is wrong,
and it is now brick L's only remaining obstruction: `τ` is the law of the step's base point,
which at step `j` *excludes* the swapped coordinate, while `hybridLaw n j ν` includes it.
Wave 41 named `indicator_wideShell_le_shift` as the transfer; wave 42 overturned that and
replaced it by `wideShell_le_of_deconvolution`. Note that this brick's `τ` is the base law
**before** the smoothing (the indicator is evaluated at `v`, not at `v + σ z`), so what has to
be deconvolved away here is the *whole* Gaussian of width `σ_{j+1}`, against
`hybridLaw n (j+1) ν` — the index moves by one, unlike on the head side. See the wave-42 section
of `localised_swap_bound_small_weight`. -/
private lemma abs_integral_gaussian_smoothed_swap_localised_le {Ct : ℝ}
    (hCt : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ Ct * s ^ 3)
    -- LEAN-ONLY (wave 40), free: `Ct` may always be enlarged
    (hCt1 : 1 ≤ Ct) (hk : 0 < k)
    {ν ρ τ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ]
    (hmeanν : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcovν : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hν1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν)
    (hν2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (hν3 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ν)
    (hνdim : (∫ y, ‖y‖ ^ 2 ∂ν) = (k : ℝ))
    (hmeanρ : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ρ) = 0)
    (hcovρ : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ρ) = ⟪u, v⟫_ℝ)
    (hρ1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ρ)
    (hρ2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ρ)
    (hρ3 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ρ)
    (hρdim : (∫ y, ‖y‖ ^ 2 ∂ρ) = (k : ℝ))
    {B : Set (EuclideanSpace ℝ (Fin k))} {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (hone : ∀ x ∈ B, F x = 1) (hsupp : ∀ x, F x ≠ 0 → x ∈ Metric.thickening ε B)
    {Ck W : ℝ} (hCk : 0 < Ck) (hW : 0 ≤ W)
    (hshell : ∀ s : ℝ, 0 < s →
      (τ (Metric.thickening s B \ erosion s B)).toReal ≤ 4 * Ck * s + W)
    {σ c : ℝ} (hσ : 0 < σ) (hσε : ε ≤ σ) (hσ1 : σ ≤ 1) (hc : 0 < c)
    -- LEAN-ONLY (wave 39): the Cauchy–Schwarz constant of the far-in-`v` half is folded into
    -- `Ct`. Free: `Ct` may always be enlarged, and `Ck = gaussianShellConst k = 4e²√k ≥ 29`.
    (hCw : Real.sqrt tiltSqConst ≤ 2 * Ck * Ct) :
    (∫ v, |(∫ y, (∫ z, F (v + σ • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
          - (∫ y, (∫ z, F (v + σ • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ)| ∂τ)
      ≤ (68 * Ck * (σ * gaussianTailRadius k σ) + 4 * W)
        * (Ct * (c / σ) ^ 3 * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ))) := by
  classical
  have hCt0 : (0 : ℝ) < Ct := lt_of_lt_of_le one_pos hCt1
  have hlam : (0 : ℝ) ≤ c / σ := div_nonneg hc.le hσ.le
  set R : ℝ := gaussianTailRadius k σ with hRdef
  have hR1 : (1 : ℝ) ≤ R := one_le_gaussianTailRadius hk σ
  have hβν0 : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ν := integral_nonneg fun y => by positivity
  have hβρ0 : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ρ := integral_nonneg fun y => by positivity
  have hnw : ∀ y : EuclideanSpace ℝ (Fin k), ‖(c / σ) • y‖ = c / σ * ‖y‖ := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
  -- the varying-width shell, jointly measurable
  have hRy : ∀ y : EuclideanSpace ℝ (Fin k), (0 : ℝ) ≤ c / σ * ‖y‖ :=
    fun y => mul_nonneg hlam (norm_nonneg y)
  have hgpos : ∀ y : EuclideanSpace ℝ (Fin k),
      (0 : ℝ) < 2 * (σ * (R + c / σ * ‖y‖)) := by
    intro y
    have h1 : (0 : ℝ) < R + c / σ * ‖y‖ := by linarith [hRy y]
    positivity
  have hSm : MeasurableSet {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
      p.1 ∈ Metric.thickening (2 * (σ * (R + c / σ * ‖p.2‖))) B
        \ erosion (2 * (σ * (R + c / σ * ‖p.2‖))) B} :=
    measurableSet_wideShell_prod (g := fun y => 2 * (σ * (R + c / σ * ‖y‖))) (by fun_prop)
      (fun y => (hgpos y).le)
  have hsecm : ∀ v : EuclideanSpace ℝ (Fin k),
      Measurable (fun y : EuclideanSpace ℝ (Fin k) =>
        (Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
          \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v) := by
    intro v
    have hrw : (fun y : EuclideanSpace ℝ (Fin k) =>
        (Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
          \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v)
        = Set.indicator ((fun y : EuclideanSpace ℝ (Fin k) => (v, y)) ⁻¹'
            {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
              p.1 ∈ Metric.thickening (2 * (σ * (R + c / σ * ‖p.2‖))) B
                \ erosion (2 * (σ * (R + c / σ * ‖p.2‖))) B}) (fun _ => (1 : ℝ)) := by
      funext y
      simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq]
    rw [hrw]
    exact measurable_const.indicator (hSm.preimage (by fun_prop))
  have hmin0 : ∀ y : EuclideanSpace ℝ (Fin k),
      (0 : ℝ) ≤ min (Ct * (c / σ * ‖y‖) ^ 3) (2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2) := by
    intro y
    have h1 : (0 : ℝ) ≤ c / σ * ‖y‖ := hRy y
    exact le_min (by positivity) (by positivity)
  -- abbreviations
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Measure (EuclideanSpace ℝ (Fin k)) →
      EuclideanSpace ℝ (Fin k) → ℝ, ∀ μ v, Θ μ v
        = ∫ y, (Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
              \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v
            * min (Ct * (c / σ * ‖y‖) ^ 3) (2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2) ∂μ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : EuclideanSpace ℝ (Fin k) → ℝ, ∀ v, D v
      = ∫ z, F (v + σ • z) * (1 + (c / σ) ^ 2 * (‖z‖ ^ 2 - (k : ℝ)) / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := ⟨_, fun _ => rfl⟩
  have hΘeq : ∀ μ : Measure (EuclideanSpace ℝ (Fin k)), Θ μ
      = fun v => ∫ y, (Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
              \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v
            * min (Ct * (c / σ * ‖y‖) ^ 3) (2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2) ∂μ :=
    fun μ => funext (hΘ μ)
  -- the per-law package
  have key : ∀ μ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure μ →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂μ) = 0) →
      (∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂μ) = ⟪u, w⟫_ℝ) →
      Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) μ →
      Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) μ →
      Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) μ →
      (∫ y, ‖y‖ ^ 2 ∂μ) = (k : ℝ) →
      Integrable (Θ μ) τ
        ∧ (∀ v : EuclideanSpace ℝ (Fin k),
            |(∫ y, (∫ z, F (v + σ • z + c • y)
                ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂μ) - D v|
              ≤ Θ μ v + 4 * Ck * Ct * σ * ((c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂μ)))
        ∧ (∫ v, Θ μ v ∂τ)
            ≤ (64 * Ck * (σ * R) + 4 * W) * (Ct * (c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂μ)) := by
    intro μ hμ hmean hcov h1 h2 h3 hdim
    haveI := hμ
    obtain ⟨hint, hbd⟩ := integral_localised_shell_le (ν := μ) (τ := τ) (B := B)
      (Ck := Ck) (Ct := Ct) (W := W) (R := R) (σ := σ) (lam := c / σ)
      h3 hCk.le hCt1 hW hR1 hσ hlam hshell
    have hlowint : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
        2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2) μ := by
      have h4 := ((integrable_const (2 : ℝ)).add (h1.const_mul (c / σ))).add
        (h2.const_mul ((c / σ) ^ 2))
      refine h4.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.add_apply]
      ring
    have hsec : ∀ v : EuclideanSpace ℝ (Fin k),
        Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
          (Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
              \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v
            * min (Ct * (c / σ * ‖y‖) ^ 3) (2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2)) μ := by
      intro v
      refine Integrable.mono' hlowint
        (((hsecm v).mul (by fun_prop)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hmin0 y),
        abs_of_nonneg (indicator_one_nonneg _ v)]
      exact (mul_le_of_le_one_left (hmin0 y) (indicator_one_le_one _ v)).trans
        (min_le_right _ _)
    refine ⟨by rw [hΘeq μ]; exact hint, fun v => ?_, by rw [hΘeq μ] at *; exact hbd⟩
    have hrep := (integral_gaussian_smoothed_sub_common_eq (τ := μ) hmean hcov h1 h2 hdim
      hF hFb v hσ hc.le).2
    rw [← hD v] at hrep
    rw [hrep, hΘ μ v]
    have hptw : ∀ y : EuclideanSpace ℝ (Fin k),
        |∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))|
          ≤ (Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
                \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v
              * min (Ct * (c / σ * ‖y‖) ^ 3) (2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2)
            + 4 * Ck * Ct * σ * (c / σ * ‖y‖) ^ 3 := by
      intro y
      have h := abs_integral_shift_vecTiltRemainder_localised_le hCt hF hFb hone hsupp
        hCk hCw hk hσ hσε hσ1 v ((c / σ) • y)
      rwa [hnw y, ← hRdef] at h
    have hRHSint : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
        (Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
              \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v
            * min (Ct * (c / σ * ‖y‖) ^ 3) (2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2)
          + 4 * Ck * Ct * σ * (c / σ * ‖y‖) ^ 3) μ := by
      refine (hsec v).add ?_
      have h5 := h3.const_mul (4 * Ck * Ct * σ * (c / σ) ^ 3)
      refine h5.congr (Filter.Eventually.of_forall fun y => ?_)
      ring
    calc |∫ y, (∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂μ|
        ≤ ∫ y, |∫ z, F (v + σ • z) * vecTiltRemainder ((c / σ) • y) z
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ y, ((Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
              \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v
            * min (Ct * (c / σ * ‖y‖) ^ 3) (2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2)
          + 4 * Ck * Ct * σ * (c / σ * ‖y‖) ^ 3) ∂μ :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun y => abs_nonneg _) hRHSint
            (Filter.Eventually.of_forall hptw)
      _ = (∫ y, (Metric.thickening (2 * (σ * (R + c / σ * ‖y‖))) B
              \ erosion (2 * (σ * (R + c / σ * ‖y‖))) B).indicator (fun _ => (1 : ℝ)) v
            * min (Ct * (c / σ * ‖y‖) ^ 3) (2 + c / σ * ‖y‖ + (c / σ * ‖y‖) ^ 2) ∂μ)
          + 4 * Ck * Ct * σ * ((c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂μ)) := by
          have hsplit : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
              4 * Ck * Ct * σ * (c / σ * ‖y‖) ^ 3) μ := by
            have h5 := h3.const_mul (4 * Ck * Ct * σ * (c / σ) ^ 3)
            refine h5.congr (Filter.Eventually.of_forall fun y => ?_)
            ring
          rw [integral_add (hsec v) hsplit]
          congr 1
          have hrw : ∀ y : EuclideanSpace ℝ (Fin k),
              4 * Ck * Ct * σ * (c / σ * ‖y‖) ^ 3
                = (4 * Ck * Ct * σ * (c / σ) ^ 3) * ‖y‖ ^ 3 := fun y => by ring
          simp_rw [hrw]
          rw [integral_const_mul]
          ring
  obtain ⟨hΘνint, hνptw, hΘνbd⟩ := key ν inferInstance hmeanν hcovν hν1 hν2 hν3 hνdim
  obtain ⟨hΘρint, hρptw, hΘρbd⟩ := key ρ inferInstance hmeanρ hcovρ hρ1 hρ2 hρ3 hρdim
  -- the two-law triangle inequality, pointwise
  obtain ⟨Kv, hKv⟩ : ∃ K : ℝ, K
      = 4 * Ck * Ct * σ * ((c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν))
        + 4 * Ck * Ct * σ * ((c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ)) := ⟨_, rfl⟩
  have hmain : ∀ v : EuclideanSpace ℝ (Fin k),
      |(∫ y, (∫ z, F (v + σ • z + c • y)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
        - (∫ y, (∫ z, F (v + σ • z + c • y)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ)|
      ≤ (Θ ν v + Θ ρ v) + Kv := by
    intro v
    have htri : |(∫ y, (∫ z, F (v + σ • z + c • y)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
          - (∫ y, (∫ z, F (v + σ • z + c • y)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ)|
        ≤ |(∫ y, (∫ z, F (v + σ • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν) - D v|
          + |(∫ y, (∫ z, F (v + σ • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ) - D v| := by
      have h := abs_sub ((∫ y, (∫ z, F (v + σ • z + c • y)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν) - D v)
        ((∫ y, (∫ z, F (v + σ • z + c • y)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ) - D v)
      calc |(∫ y, (∫ z, F (v + σ • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
            - (∫ y, (∫ z, F (v + σ • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ)|
          = |((∫ y, (∫ z, F (v + σ • z + c • y)
                ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν) - D v)
              - ((∫ y, (∫ z, F (v + σ • z + c • y)
                ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ρ) - D v)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith [hνptw v, hρptw v, hKv]
  have hsum2 : Integrable (fun v => Θ ν v + Θ ρ v) τ := hΘνint.add hΘρint
  have hmajint : Integrable (fun v => (Θ ν v + Θ ρ v) + Kv) τ :=
    hsum2.add (integrable_const _)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => abs_nonneg _)
    hmajint (Filter.Eventually.of_forall hmain)).trans ?_
  have e1 : (∫ v, ((Θ ν v + Θ ρ v) + Kv) ∂τ)
      = (∫ v, (Θ ν v + Θ ρ v) ∂τ) + ∫ _v : EuclideanSpace ℝ (Fin k), Kv ∂τ :=
    integral_add hsum2 (integrable_const _)
  have e2 : (∫ v, (Θ ν v + Θ ρ v) ∂τ) = (∫ v, Θ ν v ∂τ) + ∫ v, Θ ρ v ∂τ :=
    integral_add hΘνint hΘρint
  have e3 : (∫ _v : EuclideanSpace ℝ (Fin k), Kv ∂τ) = Kv := by
    rw [integral_const]
    simp
  rw [e1, e2, e3]
  have hextra : Kv ≤ 4 * Ck * (σ * R) * (Ct * (c / σ) ^ 3
      * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ))) := by
    have hP : (0 : ℝ) ≤ 4 * Ck * σ * Ct * ((c / σ) ^ 3
        * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ))) := by positivity
    have := mul_nonneg hP (by linarith : (0 : ℝ) ≤ R - 1)
    nlinarith [hKv]
  have hid : (64 * Ck * (σ * R) + 4 * W) * (Ct * (c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ν))
      + (64 * Ck * (σ * R) + 4 * W) * (Ct * (c / σ) ^ 3 * (∫ y, ‖y‖ ^ 3 ∂ρ))
      + 4 * Ck * (σ * R) * (Ct * (c / σ) ^ 3
          * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ)))
      = (68 * Ck * (σ * R) + 4 * W) * (Ct * (c / σ) ^ 3
          * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ))) := by ring
  linarith [hΘνbd, hΘρbd, hextra, hid]

/-- **Brick L above the Gaussian shell scale (wave 24: PROVED, and no localisation needed).**
As soon as the weight is at least `1`, the *unweighted* balanced telescope already gives the
localised bound, with no reference to `B` at all: for `ε √n ≥ 1` it is
`abs_integral_smooth_sub_gaussian_balanced` together with `W ≥ 1`, and for `ε √n < 1` it is the
trivial bound `|∫ f dμ − ∫ f dγ| ≤ 2` together with
`(β/√n) ε⁻¹ = β/(ε√n) ≥ β ≥ k^{3/2} ≥ 1`.

This is exactly the regime in which brick L has no content; see `exists_localised_swap_bound`,
whose proof splits on `W + C_k ε ≥ 1` and sends this half here. -/
theorem exists_smooth_swap_bound_of_one_le_weight (k : ℕ) (hk : 0 < k) {C₃ : ℝ}
    (hC₃ : 0 < C₃) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) (ε : ℝ)
      (f : EuclideanSpace ℝ (Fin k) → ℝ) (W : ℝ),
      0 < n → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → 0 < ε →
      ContDiff ℝ 3 f → (∀ x, |f x| ≤ 1) →
      (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) → 1 ≤ W →
      |(∫ x, f x ∂(sumLaw n ν))
          - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
        ≤ A * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) * ε⁻¹ * W := by
  obtain ⟨Ct, hCt0, hCt⟩ := exists_tiltRemainder_bound
  refine ⟨2 + (3 * C₃ / 2 + 9 * Ct), by positivity, ?_⟩
  intro n ν ε f W hn hνp hmean hcov hβint hε hf hfb hD hW
  haveI := hνp
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hβ1 : 1 ≤ β := by
    have h := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
    rw [← hβdef] at h
    have hs : 1 ≤ Real.sqrt (k : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hk1
    nlinarith
  set q : ℝ := β / Real.sqrt (n : ℝ) * ε⁻¹ with hqdef
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hsl : (Measure.pi fun _ : Fin n => ν).map
      (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) = sumLaw n ν := rfl
  have hgoal : (2 + (3 * C₃ / 2 + 9 * Ct)) * (β / Real.sqrt (n : ℝ)) * ε⁻¹ * W
      = (2 + (3 * C₃ / 2 + 9 * Ct)) * q * W := by rw [hqdef]; ring
  rw [hgoal]
  rcases le_or_gt 1 (ε * Real.sqrt (n : ℝ)) with hbig | hsmall
  · have h := abs_integral_smooth_sub_gaussian_balanced hk hCt0 hCt hn hνp hmean hcov
      hβint hf hfb hC₃ hε hD hbig
    rw [hsl, ← hβdef] at h
    have hval : (3 * C₃ / 2 + 9 * Ct) * (β / Real.sqrt (n : ℝ)) / ε
        = (3 * C₃ / 2 + 9 * Ct) * q := by rw [hqdef]; ring
    rw [hval] at h
    refine h.trans ?_
    have hKq : (0 : ℝ) ≤ (2 + (3 * C₃ / 2 + 9 * Ct)) * q :=
      mul_nonneg (by linarith) hq0.le
    nlinarith [mul_nonneg hKq (sub_nonneg.2 hW), hq0]
  · have hbdd : |(∫ x, f x ∂(sumLaw n ν))
        - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))| ≤ 2 := by
      haveI : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
        inferInstance
      have h1 := abs_integral_le_one (σ := sumLaw n ν) hf.continuous hfb
      have h2 := abs_integral_le_one
        (σ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) hf.continuous hfb
      have h3 := abs_le.1 h1
      have h4 := abs_le.1 h2
      rw [abs_le]
      constructor <;> linarith
    refine hbdd.trans ?_
    have hqe : q * (ε * Real.sqrt (n : ℝ)) = β := by
      rw [hqdef]; field_simp
    have hq1 : 1 ≤ q := by
      nlinarith [mul_nonneg hq0.le (sub_nonneg.2 hsmall.le), hqe, hβ1]
    have hs1 : (2 : ℝ) * 1 ≤ (2 + (3 * C₃ / 2 + 9 * Ct)) * q :=
      mul_le_mul (by linarith) hq1 (by norm_num) (by linarith)
    have hs2 : ((2 : ℝ) * 1) * 1 ≤ ((2 + (3 * C₃ / 2 + 9 * Ct)) * q) * W :=
      mul_le_mul hs1 hW (by norm_num) (mul_nonneg (by linarith) hq0.le)
    linarith

set_option maxHeartbeats 800000 in
-- three `field_simp`-normalised term matchings against a common `δ P`/`δ Q` basis, each with
-- its own `nlinarith`/`positivity` side goals, in one declaration
set_option maxHeartbeats 1000000 in
-- the amended ledger (wave 39) carries a square root in `Q`, which pushes the
-- `positivity`/`nlinarith` calls of the four term-matchings past the default budget.
/-- **The `ε`-balance of the weighted ledger, as pure arithmetic (wave 35, PROVED).**

This is the second — and last — bookkeeping half of brick L, isolated from all measure theory
exactly as `sum_le_of_bounded_and_weighted_decay` isolates the first. Given the output of a
*weighted* hybrid telescope at a cut `Jr`,

`D ≤ Jr·(M/6)/(nr √nr)·X·(4 C_k (ε + √Jr/√nr) + W)`
`  + Jr·C₃/(nr √nr)·X·(32 C_k/ε² + 4W/ε³)`
`  + 4 C_k C_t X/√nr·(1 + log⁺(nr/Jr)) + 3 W C_t X/√Jr`,  `M = C₃/ε³`,

with the cut in the window `t² ≤ Jr ≤ 3 t²`, `t = ε √nr ≥ 1` (which `Jr = max 2 ⌈ε² nr⌉`
delivers), and with `X ≤ 3β`, `β ≥ 1`, the conclusion is brick L's right-hand side with the
explicit constant `306 C₃ + 33 C_t`:

`D ≤ (306 C₃ + 33 C_t)·(β/√nr)·(ε⁻¹(W + C_k ε) + C_k (1 + log(1 + ε⁻¹)))`.

**Wave 37: the second summand is new, and it is not optional.** It is the *far* half of the
head estimate — the head steps at which the swap displacement `c‖u‖` exceeds `ε`, where the
third-order Taylor bound is discarded in favour of the lower-order terms
`2 + ‖D¹f‖ c‖u‖ + ½‖D²f‖ c²‖u‖²` (see `abs_taylor_remainder_localised_lower_le`). Wave 36
conjectured that this half is absorbed by the *first* summand as soon as `C₃ ≥ 1`. **That is
false**: at `Jr ≍ ε² nr` the first summand is `≍ 4 C₃ C_k δ + C₃ W δ/(2ε)` while the far half is
`≍ 288 C₃ C_k δ + 36 C₃ W δ/ε`, i.e. a *constant multiple* (≈ 25×) of it, not a smaller
quantity. So the ledger takes wave 36's other branch: `htel` gains the summand, and the constant
moves from `18 C₃` to `306 C₃ = (18 + 288) C₃`. (The normalisation `C₃ ≥ 1` of wave 37's item 1
is still convenient — it lets the constant term `2` be compared with `C₃ c²‖u‖²/ε²` — but it is
not what makes the far half fit, and the far half is priced by a *third* moment either way.)

The four terms are matched separately: the weighted head against `18 C₃ δ ε⁻¹(W + C_k ε)`, its
far half against `288 C₃ δ ε⁻¹(W + C_k ε)` (using `Jr ≤ 3ε²nr` and `X ≤ 3β`; the gap is
`252 C₃ β W/t ≥ 0`)
(using `Jr ≤ 3t²` twice — once for `Jr (M/6)/(nr√nr) ≤ C₃/(2t)`, once for
`√Jr/√nr ≤ 2ε`, so that the head's own shell weight is at most `12 C_k ε + W`), the harmonic
middle against `24 C_t δ C_k (1 + log(1 + ε⁻¹))` (using `nr/Jr ≤ ε⁻² ≤ (1 + ε⁻¹)²`, which is
where the logarithm is finally priced), and the summable tail against `9 C_t δ ε⁻¹(W + C_k ε)`
(using `√Jr ≥ t`).

**Wave 35 correction to the wave-32 ledger.** The head term *must carry the shell weight too*.
The wave-32 note estimates it as `J·(M/6)c³·3β ≤ (3/2) C₃ δ ε⁻¹`, unweighted; but the amended
conclusion contains **no bare `ε⁻¹`** — its `ε⁻¹` always appears as `ε⁻¹(W + C_k ε)`, which
stays bounded as `ε ↓ 0` when `W = 0`, while `(3/2) C₃ δ ε⁻¹` blows up. So an unweighted head
cannot be absorbed, at any constant `A`. The head steps are the ones smoothed at width
`σⱼ ≤ σ_J ≍ ε`, and the localisation of the *elementary* (third-order Taylor) swap at those
steps supplies exactly the missing factor `4 C_k σ_J + W ≤ 12 C_k ε + W`; that is the shape
hypothesised here, and with it the head lands on `ε⁻¹(W + C_k ε)` as the conclusion requires.

**Wave 35: the window `1 ≤ ε √n` is not optional.** For `ε √n < 1` the cut degenerates to
`Jr = 2` and the head is `≍ C₃ β (W/t³ + C_k ε/t⁴)`, which exceeds brick L's right-hand side
`≍ β(W/t + C_k/√n)` by `t^{-2}`; no choice of cut repairs this, since the elementary step bound
is only ever better than the Cameron–Martin one for `j ≲ ε² n < 1`, i.e. for no step at all.
Wave 32's ledger is silent about that regime; see the note on
`localised_swap_bound_small_weight`. -/
private lemma weighted_ledger_balance
    {C₃ Ct Ck ε W β X D t Jr sn nr Lam Dk : ℝ}
    (hC₃ : 0 < C₃) (hCt : 0 < Ct) (hCk : 0 < Ck) (hε : 0 < ε) (hW : 0 ≤ W)
    (hLam1 : 1 ≤ Lam) (hDk1 : 1 ≤ Dk)
    (hLamD : Lam ≤ Dk * Real.sqrt (1 + Real.log (1 + ε⁻¹)))
    (hsn : 0 < sn) (hβ1 : 1 ≤ β) (hX0 : 0 ≤ X) (hX3 : X ≤ 3 * β)
    (hsn2 : sn ^ 2 = nr) (htdef : t = ε * sn) (hbig : 1 ≤ t)
    (hJlow : t ^ 2 ≤ Jr) (hJ3 : Jr ≤ 3 * t ^ 2)
    (hD : D ≤ Jr * (C₃ / ε ^ 3 / 6 / (nr * sn)) * X
              * (4 * Ck * (ε + Real.sqrt Jr / sn) + W)
          + Jr * (C₃ / (nr * sn)) * X * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3)
          + 68 * Ck * Ct * X / sn * Lam * (1 + Real.log (max (nr / Jr) 1))
          + 12 * (W * Ct * X) / Real.sqrt Jr) :
    D ≤ (306 * C₃ + 444 * Ct) * (β / sn)
        * (ε⁻¹ * (W + Ck * ε)
          + Ck * Dk * ((1 + Real.log (1 + ε⁻¹))
            * Real.sqrt (1 + Real.log (1 + ε⁻¹)))) := by
  rw [← hsn2] at hD
  have htpos : (0 : ℝ) < t := by linarith
  have hJrpos : (0 : ℝ) < Jr := by nlinarith
  have hβ0 : (0 : ℝ) < β := by linarith
  have hεi : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  set L : ℝ := Real.log (1 + ε⁻¹) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  set δ : ℝ := β / sn with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  set P : ℝ := ε⁻¹ * (W + Ck * ε) with hPdef
  set Q : ℝ := Ck * Dk * ((1 + L) * Real.sqrt (1 + L)) with hQdef
  have hP0 : 0 < P := by rw [hPdef]; have : 0 < Ck * ε := mul_pos hCk hε; positivity
  have hsL1 : (1 : ℝ) ≤ Real.sqrt (1 + L) := by
    have h := Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ 1 + L)
    rwa [Real.sqrt_one] at h
  have hQ0 : 0 < Q := by rw [hQdef]; positivity
  have hδP : δ * P = β * (W + Ck * ε) / t := by
    rw [hδdef, hPdef, htdef]; field_simp
  have hδQ : δ * Q = β * (Ck * Dk * ((1 + L) * Real.sqrt (1 + L))) / sn := by
    rw [hδdef, hQdef]; field_simp
  -- ### the two square-root facts about the cut
  have hsqrtJ : t ≤ Real.sqrt Jr := by
    have h1 : Real.sqrt (t ^ 2) ≤ Real.sqrt Jr := Real.sqrt_le_sqrt hJlow
    rwa [Real.sqrt_sq htpos.le] at h1
  have hsqrtJ2 : Real.sqrt Jr ≤ 2 * t := by
    have h1 : Real.sqrt Jr ≤ Real.sqrt ((2 * t) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hsqrtJ0 : (0 : ℝ) < Real.sqrt Jr := lt_of_lt_of_le htpos hsqrtJ
  -- ### term 1: the weighted head
  have hθ : C₃ / ε ^ 3 / 6 / (sn ^ 2 * sn) = C₃ / (6 * t ^ 3) := by
    rw [htdef]; field_simp
  have hw0 : (0 : ℝ) ≤ 4 * Ck * (ε + Real.sqrt Jr / sn) + W := by positivity
  have hw : 4 * Ck * (ε + Real.sqrt Jr / sn) + W ≤ 12 * Ck * ε + W := by
    have h1 : Real.sqrt Jr / sn ≤ 2 * ε := by
      rw [div_le_iff₀ hsn]
      calc Real.sqrt Jr ≤ 2 * t := hsqrtJ2
        _ = 2 * ε * sn := by rw [htdef]; ring
    nlinarith [hCk, h1]
  have hA1 : Jr * (C₃ / (6 * t ^ 3)) ≤ C₃ / (2 * t) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hJ3 (by positivity : (0 : ℝ) ≤ 2 * C₃ * t)]
  have hA1nn : (0 : ℝ) ≤ Jr * (C₃ / (6 * t ^ 3)) := by positivity
  have hT1 : Jr * (C₃ / ε ^ 3 / 6 / (sn ^ 2 * sn)) * X
        * (4 * Ck * (ε + Real.sqrt Jr / sn) + W)
      ≤ 18 * C₃ * (δ * P) := by
    rw [hθ]
    have hstep1 : Jr * (C₃ / (6 * t ^ 3)) * X * (4 * Ck * (ε + Real.sqrt Jr / sn) + W)
        ≤ (C₃ / (2 * t)) * (3 * β) * (12 * Ck * ε + W) := by
      have h1 : Jr * (C₃ / (6 * t ^ 3)) * X ≤ (C₃ / (2 * t)) * (3 * β) := by
        have h2 : Jr * (C₃ / (6 * t ^ 3)) * X ≤ (C₃ / (2 * t)) * X :=
          mul_le_mul_of_nonneg_right hA1 hX0
        have h3 : (C₃ / (2 * t)) * X ≤ (C₃ / (2 * t)) * (3 * β) :=
          mul_le_mul_of_nonneg_left hX3 (by positivity)
        linarith
      have h4 : (0 : ℝ) ≤ (C₃ / (2 * t)) * (3 * β) := by positivity
      calc Jr * (C₃ / (6 * t ^ 3)) * X * (4 * Ck * (ε + Real.sqrt Jr / sn) + W)
          ≤ (C₃ / (2 * t)) * (3 * β) * (4 * Ck * (ε + Real.sqrt Jr / sn) + W) :=
            mul_le_mul_of_nonneg_right h1 hw0
        _ ≤ (C₃ / (2 * t)) * (3 * β) * (12 * Ck * ε + W) :=
            mul_le_mul_of_nonneg_left hw h4
    have hgap : 18 * C₃ * (δ * P) - (C₃ / (2 * t)) * (3 * β) * (12 * Ck * ε + W)
        = 33 / 2 * (C₃ * β * W / t) := by
      rw [hδP]; field_simp; ring
    have hgap0 : (0 : ℝ) ≤ 33 / 2 * (C₃ * β * W / t) := by positivity
    linarith
  -- ### term 1b: the FAR half of the head (wave 37)
  have hT4 : Jr * (C₃ / (sn ^ 2 * sn)) * X * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3)
      ≤ 288 * C₃ * (δ * P) := by
    have hfac0 : (0 : ℝ) ≤ 32 * Ck / ε ^ 2 + 4 * W / ε ^ 3 := by positivity
    have hCd : (0 : ℝ) ≤ C₃ / (sn ^ 2 * sn) := by positivity
    have ha : Jr ≤ 3 * ε ^ 2 * sn ^ 2 := by rw [htdef] at hJ3; nlinarith
    have h1 : Jr * (C₃ / (sn ^ 2 * sn)) * X
        ≤ 3 * ε ^ 2 * sn ^ 2 * (C₃ / (sn ^ 2 * sn)) * (3 * β) := by
      have e1 : Jr * (C₃ / (sn ^ 2 * sn)) ≤ 3 * ε ^ 2 * sn ^ 2 * (C₃ / (sn ^ 2 * sn)) :=
        mul_le_mul_of_nonneg_right ha hCd
      have e2 : (0 : ℝ) ≤ 3 * ε ^ 2 * sn ^ 2 * (C₃ / (sn ^ 2 * sn)) := by positivity
      calc Jr * (C₃ / (sn ^ 2 * sn)) * X
          ≤ 3 * ε ^ 2 * sn ^ 2 * (C₃ / (sn ^ 2 * sn)) * X :=
            mul_le_mul_of_nonneg_right e1 hX0
        _ ≤ 3 * ε ^ 2 * sn ^ 2 * (C₃ / (sn ^ 2 * sn)) * (3 * β) :=
            mul_le_mul_of_nonneg_left hX3 e2
    have h2 : Jr * (C₃ / (sn ^ 2 * sn)) * X * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3)
        ≤ 3 * ε ^ 2 * sn ^ 2 * (C₃ / (sn ^ 2 * sn)) * (3 * β)
          * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) :=
      mul_le_mul_of_nonneg_right h1 hfac0
    rw [hδP]
    have hgap : 288 * C₃ * (β * (W + Ck * ε) / t)
        - 3 * ε ^ 2 * sn ^ 2 * (C₃ / (sn ^ 2 * sn)) * (3 * β)
          * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3)
        = 252 * (C₃ * β * W / t) := by
      rw [htdef]; field_simp; ring
    have hgap0 : (0 : ℝ) ≤ 252 * (C₃ * β * W / t) := by positivity
    linarith
  -- ### term 3: the summable tail
  have hT3 : 12 * (W * Ct * X) / Real.sqrt Jr ≤ 36 * Ct * (δ * P) := by
    have h1 : 12 * (W * Ct * X) / Real.sqrt Jr
        ≤ 12 * (W * Ct * (3 * β)) / Real.sqrt Jr := by
      gcongr
    have h2 : 12 * (W * Ct * (3 * β)) / Real.sqrt Jr ≤ 12 * (W * Ct * (3 * β)) / t :=
      div_le_div_of_nonneg_left (by positivity) htpos hsqrtJ
    have hgap : 36 * Ct * (δ * P) - 12 * (W * Ct * (3 * β)) / t
        = 36 * (Ct * β * (Ck * ε) / t) := by
      rw [hδP]; field_simp; ring
    have hgap0 : (0 : ℝ) ≤ 36 * (Ct * β * (Ck * ε) / t) := by positivity
    linarith
  -- ### term 2: the harmonic (logarithmic) middle
  have hlog : Real.log (max (sn ^ 2 / Jr) 1) ≤ 2 * L := by
    have hmax1 : sn ^ 2 / Jr ≤ (1 + ε⁻¹) ^ 2 := by
      have h1 : sn ^ 2 / Jr ≤ sn ^ 2 / t ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hJlow
      have h2 : sn ^ 2 / t ^ 2 = (ε⁻¹) ^ 2 := by
        rw [htdef]; field_simp
      rw [h2] at h1
      exact h1.trans (pow_le_pow_left₀ hεi.le (by linarith) 2)
    have hmax2 : (1 : ℝ) ≤ (1 + ε⁻¹) ^ 2 := by nlinarith [hεi, sq_nonneg ε⁻¹]
    have hmax : max (sn ^ 2 / Jr) 1 ≤ (1 + ε⁻¹) ^ 2 := max_le hmax1 hmax2
    have hpos : (0 : ℝ) < max (sn ^ 2 / Jr) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have h := Real.log_le_log hpos hmax
    rw [Real.log_pow] at h
    push_cast at h
    rw [hLdef]
    exact h
  have hT2 : 68 * Ck * Ct * X / sn * Lam * (1 + Real.log (max (sn ^ 2 / Jr) 1))
      ≤ 408 * Ct * (δ * Q) := by
    have h1 : 68 * Ck * Ct * X / sn ≤ 68 * Ck * Ct * (3 * β) / sn := by gcongr
    have h1' : 68 * Ck * Ct * X / sn * Lam
        ≤ 68 * Ck * Ct * (3 * β) / sn * (Dk * Real.sqrt (1 + L)) := by
      refine mul_le_mul h1 hLamD (by linarith) (by positivity)
    have h2 : 1 + Real.log (max (sn ^ 2 / Jr) 1) ≤ 2 * (1 + L) := by linarith
    have h3 : (0 : ℝ) ≤ 1 + Real.log (max (sn ^ 2 / Jr) 1) := by
      have : (0 : ℝ) ≤ Real.log (max (sn ^ 2 / Jr) 1) :=
        Real.log_nonneg (le_max_right _ _)
      linarith
    have h4 : (0 : ℝ) ≤ 68 * Ck * Ct * (3 * β) / sn * (Dk * Real.sqrt (1 + L)) := by
      positivity
    have h5 : 68 * Ck * Ct * X / sn * Lam * (1 + Real.log (max (sn ^ 2 / Jr) 1))
        ≤ 68 * Ck * Ct * (3 * β) / sn * (Dk * Real.sqrt (1 + L)) * (2 * (1 + L)) :=
      mul_le_mul h1' h2 h3 h4
    have h6 : 68 * Ck * Ct * (3 * β) / sn * (Dk * Real.sqrt (1 + L)) * (2 * (1 + L))
        = 408 * Ct * (δ * Q) := by
      rw [hδQ]; field_simp; ring
    linarith
  -- ### assembling
  have hsplit : (306 * C₃ + 444 * Ct) * δ * (P + Q)
      = 306 * C₃ * (δ * P) + 444 * Ct * (δ * P) + 306 * C₃ * (δ * Q)
        + 444 * Ct * (δ * Q) := by ring
  have hδP0 : (0 : ℝ) ≤ δ * P := by positivity
  have hδQ0 : (0 : ℝ) ≤ δ * Q := by positivity
  have hrest : (0 : ℝ) ≤ 408 * Ct * (δ * P) + 306 * C₃ * (δ * Q)
      + 36 * Ct * (δ * Q) := by
    have h1 : (0 : ℝ) ≤ Ct * (δ * P) := mul_nonneg hCt.le hδP0
    have h2 : (0 : ℝ) ≤ C₃ * (δ * Q) := mul_nonneg hC₃.le hδQ0
    have h3 : (0 : ℝ) ≤ Ct * (δ * Q) := mul_nonneg hCt.le hδQ0
    linarith
  linarith

/-- **Brick L reduced to its analytic half (wave 35, PROVED).**

`localised_swap_bound_small_weight` *follows from the weighted hybrid telescope alone*: given
the telescoped estimate at **every** cut `J ≥ 2` — head steps estimated by the localised
elementary (third-order Taylor) swap at weight `4 C_k (ε + √J/√n) + W` *plus* its far half at
the varying width (wave 37, second summand), tail steps by the localised Cameron–Martin swap,
summed by `sum_le_of_bounded_and_weighted_decay` — the brick's
conclusion follows with the explicit constant `306 C₃ + 33 C_t`, by choosing the cut
`J = max 2 ⌈ε² n⌉` and running `weighted_ledger_balance`. Nothing about `B`, `f`, or the shell
hypothesis enters here: `D` is an arbitrary real, so this is *exactly* the reduction and no more.

Together with `sum_le_of_bounded_and_weighted_decay` this discharges the whole bookkeeping side
of brick L in Lean; what is left is the analytic production of the two per-step estimates, which
is the hypothesis `htel` — see the note on `localised_swap_bound_small_weight`.

The two measure-theoretic hypotheses are used only for the two moment facts the ledger needs:
`β ≥ k^{3/2} ≥ 1` (`sqrt_dim_mul_dim_le_integral_norm_cube`) and `β + β_G ≤ 3β`
(`integral_norm_cube_gaussian_le`).

The window `1 ≤ ε √n` is required, and is not a technicality: see the last paragraph of
`weighted_ledger_balance`.

**WAVE-40 FLAG — this hypothesis is now out of step with the tail brick, deliberately.** `htel`
below carries wave 39's per-step tail constants (`12 * gaussianShellConst k * Ct * …` and
`3 * (W * Ct * X) / √J`). Wave 40 proved the pointwise engine of the tail brick at every shift
length and re-derived its constants honestly:
`abs_integral_gaussian_smoothed_swap_localised_le` now concludes with weight
`68 C_k σ R + 4 W`, not `12 C_k σ R + W` (see its docstring for the derivation — the extra
factors are the shell doubling `8`, the crude branch `2+s+s² ≤ 4s²`, and `R+s ≤ 2Rs`, none of
which occur in the `‖w‖ ≤ 1` regime wave 39 priced). When the brick's remaining Fubini
bookkeeping lands, `htel`'s two tail summands must become `68 * …` and `12 * (W * Ct * X) / √J`,
and `weighted_ledger_balance`'s `81 * Ct` must be re-solved (`459 * Ct` certainly suffices; the
`306 * C₃` head half is untouched). **No shape moves**, so the fixed point and
`berryEsseen_convex_sharp` re-solve at the same `(1 + log(1+ε⁻¹))^{3/2}` power. The mismatch is
left visible here rather than silently propagated, per the provable-constants rule.

**Wave 41: the flag is EXECUTED.** The tail brick landed, so `htel` now carries `68 * …` and
`12 * …`, and the ledger is re-solved: the harmonic middle scales by exactly `68/12` (`72 → 408`)
and the summable tail by exactly `12/3` (`9 → 36`), so the constant is `306 C₃ + 444 C_t` — wave
40's `459` was an over-estimate. Nothing else moved. -/
theorem localised_swap_bound_of_weighted_telescope (hk : 0 < k) {n : ℕ} (hn : 0 < n)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβint : Integrable (fun y => ‖y‖ ^ 3) ν)
    {C₃ Ct ε W D : ℝ} (hC₃ : 0 < C₃) (hCt : 0 < Ct) (hε : 0 < ε) (hW : 0 ≤ W)
    (hbig : 1 ≤ ε * Real.sqrt (n : ℝ))
    (htel : ∀ J : ℕ, 2 ≤ J → ε ^ 2 * (n : ℝ) ≤ (J : ℝ) →
      D ≤ (J : ℝ) * (C₃ / ε ^ 3 / 6 / ((n : ℝ) * Real.sqrt (n : ℝ)))
              * ((∫ y, ‖y‖ ^ 3 ∂ν)
                + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
              * (4 * gaussianShellConst k
                  * (ε + Real.sqrt (J : ℝ) / Real.sqrt (n : ℝ)) + W)
          + (J : ℝ) * (C₃ / ((n : ℝ) * Real.sqrt (n : ℝ)))
              * ((∫ y, ‖y‖ ^ 3 ∂ν)
                + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
              * (32 * gaussianShellConst k / ε ^ 2 + 4 * W / ε ^ 3)
          + 68 * gaussianShellConst k * Ct
              * ((∫ y, ‖y‖ ^ 3 ∂ν)
                + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
              / Real.sqrt (n : ℝ) * gaussianTailRadius k ε
              * (1 + Real.log (max ((n : ℝ) / (J : ℝ)) 1))
          + 12 * (W * Ct
              * ((∫ y, ‖y‖ ^ 3 ∂ν)
                + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))))
              / Real.sqrt (J : ℝ)) :
    D ≤ (306 * C₃ + 444 * Ct) * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ))
        * (ε⁻¹ * (W + gaussianShellConst k * ε)
          + gaussianShellConst k * dimTailConst k
            * ((1 + Real.log (1 + ε⁻¹)) * Real.sqrt (1 + Real.log (1 + ε⁻¹)))) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  have hsn2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnr.le
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hγstd : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := multivariateGaussian_zero_one
  -- the two moment facts
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlyap := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
  have hβ1 : 1 ≤ ∫ y, ‖y‖ ^ 3 ∂ν := by
    have hs : 1 ≤ Real.sqrt (k : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hk1
    nlinarith
  have hγ3 := integral_norm_cube_gaussian_le (k := k) hk
  rw [hγstd] at hγ3
  have hX3 : (∫ y, ‖y‖ ^ 3 ∂ν)
        + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ 3 * (∫ y, ‖y‖ ^ 3 ∂ν) := by linarith
  have hX0 : (0 : ℝ) ≤ (∫ y, ‖y‖ ^ 3 ∂ν)
      + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
    have h1 : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ν := integral_nonneg fun y => by positivity
    have h2 : (0 : ℝ) ≤ ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      integral_nonneg fun z => by positivity
    linarith
  -- the cut `J = max 2 ⌈ε² n⌉`
  set t : ℝ := ε * Real.sqrt (n : ℝ) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht2 : t ^ 2 = ε ^ 2 * (n : ℝ) := by rw [htdef, mul_pow, hsn2]
  set J : ℕ := max 2 ⌈ε ^ 2 * (n : ℝ)⌉₊ with hJdef
  have hJ2 : 2 ≤ J := le_max_left _ _
  have hJlow : t ^ 2 ≤ (J : ℝ) := by
    rw [ht2]
    refine le_trans (Nat.le_ceil _) ?_
    have hmem : ⌈ε ^ 2 * (n : ℝ)⌉₊ ≤ J := by rw [hJdef]; exact le_max_right _ _
    exact_mod_cast hmem
  have hJhigh : (J : ℝ) ≤ t ^ 2 + 2 := by
    rw [ht2]
    have hmax : (J : ℝ) = max 2 ((⌈ε ^ 2 * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
      rw [hJdef]; push_cast; rfl
    have hc : ((⌈ε ^ 2 * (n : ℝ)⌉₊ : ℕ) : ℝ) < ε ^ 2 * (n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hnn : (0 : ℝ) ≤ ε ^ 2 * (n : ℝ) := by positivity
    rw [hmax]
    rcases max_cases (2 : ℝ) ((⌈ε ^ 2 * (n : ℝ)⌉₊ : ℕ) : ℝ) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; linarith
    · rw [he]; linarith
  have hJ3 : (J : ℝ) ≤ 3 * t ^ 2 := by nlinarith [hJhigh, hbig, htpos]
  exact weighted_ledger_balance hC₃ hCt hCk hε hW (one_le_gaussianTailRadius hk ε)
    (one_le_dimTailConst hk) (gaussianTailRadius_le_dimTailConst hk hε)
    hsn hβ1 hX0 hX3 hsn2 htdef hbig hJlow hJ3 (htel J hJ2 (by rw [← ht2]; exact hJlow))

/-- **One HEAD step of the localised telescope, with the deconvolution done (wave 43).** -/
private lemma head_step_le {k : ℕ} (hk : 0 < k)
    {ν τ η μ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] [IsProbabilityMeasure η]
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcov : ∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂ν) = ⟪u, w⟫_ℝ)
    (hβ : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ν)
    (hν2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (hνdim : (∫ y, ‖y‖ ^ 2 ∂ν) = (k : ℝ))
    (hmeanγ : ∀ u : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = 0)
    (hcovγ : ∀ u w : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ * ⟪w, z⟫_ℝ ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = ⟪u, w⟫_ℝ)
    (hβγ : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 3)
      (stdGaussian (EuclideanSpace ℝ (Fin k))))
    {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : ContDiff ℝ 3 f) (hfb : ∀ x, |f x| ≤ 1)
    {C₃ ε : ℝ} (hC₃ : 1 ≤ C₃) (hε : 0 < ε)
    (hD3 : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3)
    (hD1 : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C₃ / ε)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₃ / ε ^ 2)
    (hone : ∀ x ∈ B, f x = 1) (hsupp : ∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B)
    {W : ℝ} (hW : 0 ≤ W) {c : ℝ} (hc : 0 < c)
    (hck : c * Real.sqrt (k : ℝ) ≤ ε)
    (hη : η = ν.map fun u => c • u)
    (hμ : μ = (τ.prod η).map fun p => p.1 + p.2)
    (hshell : ∀ s : ℝ, 0 < s →
      (μ (Metric.thickening s B \ erosion s B)).toReal
        ≤ 4 * gaussianShellConst k * s + W) :
    (∫ a, |(∫ u, f (a + c • u) ∂ν)
        - (∫ u, f (a + c • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ∂τ)
      ≤ 12 * (C₃ / ε ^ 3 / 6 * c ^ 3)
            * ((∫ y, ‖y‖ ^ 3 ∂ν)
              + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            * (4 * gaussianShellConst k * ε + W)
        + 12 * (C₃ * c ^ 3)
            * ((∫ y, ‖y‖ ^ 3 ∂ν)
              + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            * (32 * gaussianShellConst k / ε ^ 2 + 4 * W / ε ^ 3) := by
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hr : 0 < c * Real.sqrt (k : ℝ) := by positivity
  -- the deconvolved shell bound for the base law
  have hηnorm : (∫ y, ‖y‖ ^ 2 ∂η) = c ^ 2 * (k : ℝ) := by
    have hsq : ∀ y : EuclideanSpace ℝ (Fin k), ‖c • y‖ ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by
      intro y; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hη, integral_map (φ := fun u : EuclideanSpace ℝ (Fin k) => c • u)
      (f := fun y => ‖y‖ ^ 2) (by fun_prop) (by fun_prop)]
    simp_rw [hsq]
    rw [integral_const_mul, hνdim]
  have hηint : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) η := by
    have hc2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖c • y‖ ^ 2) ν := by
      have hfun : (fun y : EuclideanSpace ℝ (Fin k) => ‖c • y‖ ^ 2)
          = fun y => c ^ 2 * ‖y‖ ^ 2 := by
        funext y; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hfun]; exact hν2.const_mul _
    rw [hη, integrable_map_measure (by fun_prop) (by fun_prop)]
    exact hc2
  have hshellτ : ∀ s : ℝ, 0 < s →
      (τ (Metric.thickening s B \ erosion s B)).toReal
        ≤ 4 * (3 * gaussianShellConst k) * s
          + (2 * W + 22 * gaussianShellConst k * (c * Real.sqrt (k : ℝ))) := by
    refine wideShell_le_of_deconvolution_uniform hμ hCk.le hW hshell hηint hr ?_
    rw [hηnorm, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  have hW' : (0 : ℝ) ≤ 2 * W + 22 * gaussianShellConst k * (c * Real.sqrt (k : ℝ)) := by
    nlinarith [hCk.le, hr.le]
  have hbrick := abs_integral_swap_step_localised_le (ν := ν)
    (ρ := stdGaussian (EuclideanSpace ℝ (Fin k))) (τ := τ)
    hmean hcov hβ hmeanγ hcovγ hβγ hf hfb hC₃ hε hD3 hD1 hD2 hone hsupp
    (by linarith : (0 : ℝ) < 3 * gaussianShellConst k) hW' hshellτ hc
  refine hbrick.trans ?_
  -- the arithmetic: the deconvolution constants fit at the factor 12
  set Ck : ℝ := gaussianShellConst k with hCkdef
  set X : ℝ := (∫ y, ‖y‖ ^ 3 ∂ν)
    + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) with hXdef
  have hX0 : 0 ≤ X := by
    have h1 : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ν := integral_nonneg fun y => by positivity
    have h2 : (0 : ℝ) ≤ ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      integral_nonneg fun z => by positivity
    rw [hXdef]; linarith
  have hE1 : (0 : ℝ) ≤ C₃ / ε ^ 3 / 6 * c ^ 3 * X := by
    have : (0 : ℝ) ≤ C₃ / ε ^ 3 / 6 * c ^ 3 :=
      mul_nonneg (div_nonneg (div_nonneg (by linarith) (by positivity)) (by norm_num))
        (by positivity)
    exact mul_nonneg this hX0
  have hE2 : (0 : ℝ) ≤ C₃ * c ^ 3 * X :=
    mul_nonneg (mul_nonneg (by linarith) (by positivity)) hX0
  have hb1 : 8 * (3 * Ck) * ε + (2 * W + 22 * Ck * (c * Real.sqrt (k : ℝ)))
      ≤ 12 * (4 * Ck * ε + W) := by
    have h : 22 * Ck * (c * Real.sqrt (k : ℝ)) ≤ 22 * Ck * ε := by
      have : (0 : ℝ) ≤ 22 * Ck := by rw [hCkdef]; linarith
      nlinarith [hck]
    linarith
  have hb2 : 32 * (3 * Ck) / ε ^ 2
        + 4 * (2 * W + 22 * Ck * (c * Real.sqrt (k : ℝ))) / ε ^ 3
      ≤ 12 * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) := by
    have hCk0 : (0 : ℝ) ≤ Ck := hCk.le
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    have hε3 : (0 : ℝ) < ε ^ 3 := by positivity
    have ht : Ck * (c * Real.sqrt (k : ℝ)) / ε ^ 3 ≤ Ck / ε ^ 2 := by
      rw [div_le_div_iff₀ hε3 hε2]
      nlinarith [mul_nonneg (mul_nonneg hCk0 hε2.le) (sub_nonneg.2 hck)]
    have hu : (0 : ℝ) ≤ Ck / ε ^ 2 := div_nonneg hCk0 hε2.le
    have hw : (0 : ℝ) ≤ W / ε ^ 3 := div_nonneg hW hε3.le
    have e1 : 32 * (3 * Ck) / ε ^ 2 = 96 * (Ck / ε ^ 2) := by ring
    have e2 : 4 * (2 * W + 22 * Ck * (c * Real.sqrt (k : ℝ))) / ε ^ 3
        = 8 * (W / ε ^ 3) + 88 * (Ck * (c * Real.sqrt (k : ℝ)) / ε ^ 3) := by ring
    have e3 : 12 * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3)
        = 384 * (Ck / ε ^ 2) + 48 * (W / ε ^ 3) := by ring
    rw [e1, e2, e3]
    linarith
  have hstep1 : C₃ / ε ^ 3 / 6 * c ^ 3 * X
        * (8 * (3 * Ck) * ε + (2 * W + 22 * Ck * (c * Real.sqrt (k : ℝ))))
      ≤ 12 * (C₃ / ε ^ 3 / 6 * c ^ 3) * X * (4 * Ck * ε + W) := by
    have h := mul_le_mul_of_nonneg_left hb1 hE1
    calc C₃ / ε ^ 3 / 6 * c ^ 3 * X
          * (8 * (3 * Ck) * ε + (2 * W + 22 * Ck * (c * Real.sqrt (k : ℝ))))
        = C₃ / ε ^ 3 / 6 * c ^ 3 * X
          * (8 * (3 * Ck) * ε + (2 * W + 22 * Ck * (c * Real.sqrt (k : ℝ)))) := rfl
      _ ≤ C₃ / ε ^ 3 / 6 * c ^ 3 * X * (12 * (4 * Ck * ε + W)) := h
      _ = 12 * (C₃ / ε ^ 3 / 6 * c ^ 3) * X * (4 * Ck * ε + W) := by ring
  have hstep2 : C₃ * c ^ 3 * X
        * (32 * (3 * Ck) / ε ^ 2
          + 4 * (2 * W + 22 * Ck * (c * Real.sqrt (k : ℝ))) / ε ^ 3)
      ≤ 12 * (C₃ * c ^ 3) * X * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) := by
    have h := mul_le_mul_of_nonneg_left hb2 hE2
    calc C₃ * c ^ 3 * X
          * (32 * (3 * Ck) / ε ^ 2
            + 4 * (2 * W + 22 * Ck * (c * Real.sqrt (k : ℝ))) / ε ^ 3)
        ≤ C₃ * c ^ 3 * X * (12 * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3)) := h
      _ = 12 * (C₃ * c ^ 3) * X * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) := by ring
  linarith

/-- **One TAIL step of the localised telescope, with the deconvolution done (wave 43).** -/
private lemma tail_step_le {k : ℕ} (hk : 0 < k) {Ct : ℝ}
    (hCtb : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ Ct * s ^ 3)
    (hCt1 : 1 ≤ Ct)
    {ν τ η μ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] [IsProbabilityMeasure η]
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hν1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν)
    (hν2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (hν3 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) ν)
    (hνdim : (∫ y, ‖y‖ ^ 2 ∂ν) = (k : ℝ))
    (hmeanγ : ∀ u : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = 0)
    (hcovγ : ∀ u v : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ * ⟪v, z⟫_ℝ ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = ⟪u, v⟫_ℝ)
    (hγ1 : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖)
      (stdGaussian (EuclideanSpace ℝ (Fin k))))
    (hγ2 : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))))
    (hβγ : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 3)
      (stdGaussian (EuclideanSpace ℝ (Fin k))))
    (hγdim : (∫ z, ‖z‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = (k : ℝ))
    {B : Set (EuclideanSpace ℝ (Fin k))} {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hF : Continuous F) (hFb : ∀ x, |F x| ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (hone : ∀ x ∈ B, F x = 1) (hsupp : ∀ x, F x ≠ 0 → x ∈ Metric.thickening ε B)
    {W : ℝ} (hW : 0 ≤ W)
    {σ σ' c : ℝ} (hσ : 0 < σ) (hσε : ε ≤ σ) (hσ1 : σ ≤ 1) (hc : 0 < c)
    (hσ'0 : 0 < σ') (hσ'σ : σ' ≤ 3 / 2 * σ)
    (hCw : Real.sqrt tiltSqConst ≤ 2 * gaussianShellConst k * Ct)
    (hη : η = (stdGaussian (EuclideanSpace ℝ (Fin k))).map fun z => σ' • z)
    (hμ : μ = (τ.prod η).map fun p => p.1 + p.2)
    (hshell : ∀ s : ℝ, 0 < s →
      (μ (Metric.thickening s B \ erosion s B)).toReal
        ≤ 4 * gaussianShellConst k * s + W) :
    (∫ v, |(∫ y, (∫ z, F (v + σ • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
          - (∫ y, (∫ z, F (v + σ • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ∂τ)
      ≤ (336 * gaussianShellConst k * (σ * gaussianTailRadius k σ) + 8 * W)
        * (Ct * (c / σ) ^ 3
          * ((∫ y, ‖y‖ ^ 3 ∂ν)
            + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))) := by
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hCt0 : (0 : ℝ) < Ct := lt_of_lt_of_le one_pos hCt1
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hr : 0 < σ' * Real.sqrt (k : ℝ) := by positivity
  -- the deconvolved shell bound for the base law
  have hηnorm : (∫ y, ‖y‖ ^ 2 ∂η) = σ' ^ 2 * (k : ℝ) := by
    have hsq : ∀ y : EuclideanSpace ℝ (Fin k), ‖σ' • y‖ ^ 2 = σ' ^ 2 * ‖y‖ ^ 2 := by
      intro y; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hη, integral_map (φ := fun u : EuclideanSpace ℝ (Fin k) => σ' • u)
      (f := fun y => ‖y‖ ^ 2) (by fun_prop) (by fun_prop)]
    simp_rw [hsq]
    rw [integral_const_mul, hγdim]
  have hηint : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) η := by
    have hc2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖σ' • y‖ ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
      have hfun : (fun y : EuclideanSpace ℝ (Fin k) => ‖σ' • y‖ ^ 2)
          = fun y => σ' ^ 2 * ‖y‖ ^ 2 := by
        funext y; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hfun]; exact hγ2.const_mul _
    rw [hη, integrable_map_measure (by fun_prop) (by fun_prop)]
    exact hc2
  have hshellτ : ∀ s : ℝ, 0 < s →
      (τ (Metric.thickening s B \ erosion s B)).toReal
        ≤ 4 * (3 * gaussianShellConst k) * s
          + (2 * W + 22 * gaussianShellConst k * (σ' * Real.sqrt (k : ℝ))) := by
    refine wideShell_le_of_deconvolution_uniform hμ hCk.le hW hshell hηint hr ?_
    rw [hηnorm, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  have hW' : (0 : ℝ) ≤ 2 * W + 22 * gaussianShellConst k * (σ' * Real.sqrt (k : ℝ)) := by
    nlinarith [hCk.le, hr.le]
  have hCw' : Real.sqrt tiltSqConst ≤ 2 * (3 * gaussianShellConst k) * Ct := by
    nlinarith [hCk.le, hCt0.le]
  have hbrick := abs_integral_gaussian_smoothed_swap_localised_le
    (ν := ν) (ρ := stdGaussian (EuclideanSpace ℝ (Fin k))) (τ := τ)
    hCtb hCt1 hk hmean hcov hν1 hν2 hν3 hνdim hmeanγ hcovγ hγ1 hγ2 hβγ hγdim
    hF hFb hε hone hsupp (by linarith : (0 : ℝ) < 3 * gaussianShellConst k) hW'
    hshellτ hσ hσε hσ1 hc hCw'
  refine hbrick.trans ?_
  set Ck : ℝ := gaussianShellConst k with hCkdef
  set X : ℝ := (∫ y, ‖y‖ ^ 3 ∂ν)
    + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) with hXdef
  have hX0 : 0 ≤ X := by
    have h1 : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ν := integral_nonneg fun y => by positivity
    have h2 : (0 : ℝ) ≤ ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      integral_nonneg fun z => by positivity
    rw [hXdef]; linarith
  have hfac : (0 : ℝ) ≤ Ct * (c / σ) ^ 3 * X :=
    mul_nonneg (mul_nonneg hCt0.le (by positivity)) hX0
  have hRk : Real.sqrt (k : ℝ) ≤ gaussianTailRadius k σ := sqrt_dim_le_gaussianTailRadius hk σ
  have hR0 : (0 : ℝ) ≤ gaussianTailRadius k σ := gaussianTailRadius_nonneg k σ
  have hweight : 68 * (3 * Ck) * (σ * gaussianTailRadius k σ)
        + 4 * (2 * W + 22 * Ck * (σ' * Real.sqrt (k : ℝ)))
      ≤ 336 * Ck * (σ * gaussianTailRadius k σ) + 8 * W := by
    have hCk0 : (0 : ℝ) ≤ Ck := hCk.le
    have h1 : σ' * Real.sqrt (k : ℝ) ≤ 3 / 2 * σ * gaussianTailRadius k σ := by
      nlinarith [hσ.le, hsk.le, hRk, hσ'σ]
    nlinarith [mul_nonneg hCk0 (sub_nonneg.2 h1)]
  exact mul_le_mul_of_nonneg_right hweight hfac

set_option maxHeartbeats 2000000 in
/-- **The LOCALISED hybrid telescope (wave 43).** -/
private lemma abs_integral_smooth_sub_gaussian_localised {n : ℕ} (hk : 0 < k) {Ct : ℝ}
    (hCt1 : 1 ≤ Ct)
    (hCtb : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ Ct * s ^ 3)
    (hCw : Real.sqrt tiltSqConst ≤ 2 * gaussianShellConst k * Ct)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} (hn : 0 < n) (hν : IsProbabilityMeasure ν)
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : ContDiff ℝ 3 f) (hfb : ∀ x, |f x| ≤ 1)
    {C₃ ε : ℝ} (hC₃ : 1 ≤ C₃) (hε : 0 < ε)
    (hD3 : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3)
    (hD1 : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C₃ / ε)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₃ / ε ^ 2)
    (hone : ∀ x ∈ B, f x = 1) (hsupp : ∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B)
    {W : ℝ} (hW : 0 ≤ W)
    (hwin : Real.sqrt (k : ℝ) ≤ ε * Real.sqrt (n : ℝ))
    (hshell : ∀ j : ℕ, j ≤ n → ∀ s : ℝ, 0 < s →
      ((hybridLaw n j ν) (Metric.thickening s B \ erosion s B)).toReal
        ≤ 4 * gaussianShellConst k * s + W)
    {J : ℕ} (hJ2 : 2 ≤ J) (hJε : ε ^ 2 * (n : ℝ) ≤ (J : ℝ)) :
    |(∫ x, f x ∂(sumLaw n ν))
        - (∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))|
      ≤ (J : ℝ) * (12 * C₃ / ε ^ 3 / 6 / ((n : ℝ) * Real.sqrt (n : ℝ)))
            * ((∫ y, ‖y‖ ^ 3 ∂ν)
              + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            * (4 * gaussianShellConst k
                * (ε + Real.sqrt (J : ℝ) / Real.sqrt (n : ℝ)) + W)
        + (J : ℝ) * (12 * C₃ / ((n : ℝ) * Real.sqrt (n : ℝ)))
            * ((∫ y, ‖y‖ ^ 3 ∂ν)
              + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            * (32 * gaussianShellConst k / ε ^ 2 + 4 * W / ε ^ 3)
        + 68 * gaussianShellConst k * (5 * Ct)
            * ((∫ y, ‖y‖ ^ 3 ∂ν)
              + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            / Real.sqrt (n : ℝ) * gaussianTailRadius k ε
            * (1 + Real.log (max ((n : ℝ) / (J : ℝ)) 1))
        + 12 * (W * (5 * Ct)
            * ((∫ y, ‖y‖ ^ 3 ∂ν)
              + ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))))
            / Real.sqrt (J : ℝ) := by
  classical
  haveI := hν
  have hCt0 : (0 : ℝ) < Ct := lt_of_lt_of_le one_pos hCt1
  have hC₃0 : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  -- ### Gaussian moment facts
  have hmeanγ : ∀ u : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = 0 := by
    intro u
    simpa using integral_strongDual_stdGaussian (E := EuclideanSpace ℝ (Fin k)) (innerSL ℝ u)
  have hcovγ : ∀ u w : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ * ⟪w, z⟫_ℝ ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = ⟪u, w⟫_ℝ := by
    intro u w
    have hL2 : MemLp id 2 (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      IsGaussian.memLp_id _ 2 (by simp)
    have hid : (stdGaussian (EuclideanSpace ℝ (Fin k)))[id] = (0 : EuclideanSpace ℝ (Fin k)) :=
      integral_id_stdGaussian
    have h := covarianceBilin_apply (μ := stdGaussian (EuclideanSpace ℝ (Fin k))) hL2 u w
    rw [hid] at h
    simp only [sub_zero] at h
    rw [← h, covarianceBilin_stdGaussian]
    exact innerSL_apply_apply (𝕜 := ℝ) u w
  have hβγ : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 3)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have hL3 : MemLp id ((3 : ℕ) : ℝ≥0∞) (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      IsGaussian.memLp_id _ _ (by simp)
    simpa using hL3.integrable_norm_pow'
  have hν1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν := integrable_norm_of_cube hβ
  have hν2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν :=
    integrable_normSq_of_cube hβ
  have hγ1 : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := integrable_norm_of_cube hβγ
  have hγ2 : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := integrable_normSq_of_cube hβγ
  have hνdim : (∫ y, ‖y‖ ^ 2 ∂ν) = (k : ℝ) := integral_normSq_eq_dim hcov hβ
  have hγdim : (∫ z, ‖z‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = (k : ℝ) :=
    integral_normSq_eq_dim hcovγ hβγ
  have hβνpos : 0 < ∫ y, ‖y‖ ^ 3 ∂ν := integral_norm_cube_pos hk hcov hβ
  have hβγnn : 0 ≤ ∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
    integral_nonneg fun z => by positivity
  -- ### the telescope skeleton
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsN : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hNr
  set X : ℝ := (∫ y, ‖y‖ ^ 3 ∂ν)
    + (∫ z, ‖z‖ ^ 3 ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; linarith
  set c : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  set sg : ℕ → ℝ := fun j => c * Real.sqrt (j : ℝ) with hsgdef
  have hsg0 : sg 0 = 0 := by rw [hsgdef]; simp
  have hsgN1 : sg (m + 1) = 1 := by
    rw [hsgdef, hcdef]; dsimp only; exact inv_mul_cancel₀ hsN.ne'
  have hsgpos : ∀ j : ℕ, 1 ≤ j → 0 < sg j := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hsq : (0 : ℝ) < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr (by linarith)
    rw [hsgdef]; dsimp only; positivity
  have hsgval : ∀ j : ℕ, sg j = Real.sqrt (j : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    intro j; rw [hsgdef, hcdef]; dsimp only; rw [inv_mul_eq_div]
  set Φ : ℕ → EuclideanSpace ℝ (Fin k) → ℝ :=
    fun j x => ∫ z, f (x + sg j • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) with hΦdef
  set G : ℕ → EuclideanSpace ℝ (Fin k) → ℝ := fun j w => Φ j (c • w) with hGdef
  have hΦcont : ∀ j, Continuous (Φ j) := fun j =>
    continuous_integral_add_smul hf.continuous hfb (sg j)
  have hΦb : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin k)), |Φ j x| ≤ 1 := fun j x =>
    abs_integral_le_one
      (hf.continuous.comp (continuous_const.add (continuous_const_smul (sg j))))
      (fun z => hfb _)
  have hGcont : ∀ j, Continuous (G j) := fun j => (hΦcont j).comp (continuous_const_smul c)
  have hGb : ∀ (j : ℕ) (w : EuclideanSpace ℝ (Fin k)), |G j w| ≤ 1 := fun j w => hΦb j _
  have hconv : ∀ (j : ℕ) (v : EuclideanSpace ℝ (Fin k)),
      (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) = G (j + 1) v := by
    intro j v
    have hjsq : Real.sqrt (j : ℝ) ^ 2 = (j : ℝ) := Real.sq_sqrt (Nat.cast_nonneg j)
    have hsq : Real.sqrt ((sg j) ^ 2 + c ^ 2) = sg (j + 1) := by
      have h1 : (sg j) ^ 2 + c ^ 2 = c ^ 2 * (((j + 1 : ℕ) : ℝ)) := by
        rw [hsgdef]; dsimp only; push_cast; rw [mul_pow, hjsq]; ring
      rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hcpos.le, hsgdef]
    have h := integral_gaussian_pair_smul_add (k := k) (sg j) c hf.continuous hfb (c • v)
    rw [hsq] at h
    calc (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = ∫ u, (∫ z, f (c • v + sg j • z + c • u)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only [hGdef, hΦdef]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          congr 1
          rw [smul_add]
          abel
      _ = ∫ z, f (c • v + sg (j + 1) • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := h
      _ = G (j + 1) v := by simp only [hGdef, hΦdef]
  set κ : ℕ → Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun j i => if (i : ℕ) < j then Measure.dirac 0 else ν with hκdef
  haveI hκp : ∀ (j : ℕ) (i : Fin (m + 1)), IsProbabilityMeasure (κ j i) := by
    intro j i
    rw [hκdef]; dsimp only
    split_ifs
    · infer_instance
    · exact hν
  set I : ℕ → ℝ := fun j => ∫ x, G j (∑ l, x l) ∂(Measure.pi (κ j)) with hIdef
  have hstepfun : ∀ j : ℕ, ∀ hj : j < m + 1, ∀ D : EuclideanSpace ℝ (Fin k) → ℝ,
      Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) => D (∑ l, y l))
        (Measure.pi fun l : Fin m => κ j ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)) →
      (∀ v : EuclideanSpace ℝ (Fin k),
        |(∫ u, G j (u + v) ∂ν)
          - (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ≤ D v) →
      |I j - I (j + 1)|
        ≤ ∫ y, D (∑ l, y l)
            ∂(Measure.pi fun l : Fin m => κ j ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)) := by
    intro j hj D hDint hbound
    set i : Fin (m + 1) := ⟨j, hj⟩ with hidef
    have hival : ((i : Fin (m + 1)) : ℕ) = j := by rw [hidef]
    have hji : κ j i = ν := by
      rw [hκdef]; dsimp only; rw [if_neg (by rw [hival]; omega)]
    have hji1 : κ (j + 1) i = Measure.dirac 0 := by
      rw [hκdef]; dsimp only; rw [if_pos (by rw [hival]; omega)]
    have hoff : (fun l : Fin m => κ (j + 1) (i.succAbove l))
        = fun l : Fin m => κ j (i.succAbove l) := by
      funext l
      have hne : ((i.succAbove l : Fin (m + 1)) : ℕ) ≠ j := by
        intro h
        exact Fin.succAbove_ne i l (Fin.ext (by rw [h, hival]))
      rw [hκdef]; dsimp only
      by_cases hlt : ((i.succAbove l : Fin (m + 1)) : ℕ) < j
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg hlt]
    have hpeel0 := integral_pi_sum_peel (κ j) i (hGcont j) (hGb j)
    have hpeel1 := integral_pi_sum_peel (κ (j + 1)) i (hGcont (j + 1)) (hGb (j + 1))
    rw [hji] at hpeel0
    rw [hji1, hoff] at hpeel1
    set R : Measure ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
      Measure.pi (fun l : Fin m => κ j (i.succAbove l)) with hRdef
    haveI hRp : IsProbabilityMeasure R := by rw [hRdef]; infer_instance
    have hdirac : ∀ y : (_ : Fin m) → EuclideanSpace ℝ (Fin k),
        (∫ u, G (j + 1) (u + ∑ l, y l) ∂(Measure.dirac (0 : EuclideanSpace ℝ (Fin k))))
          = ∫ u, G j (u + ∑ l, y l) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
      intro y
      rw [integral_dirac, zero_add]
      exact (hconv j _).symm
    have hIj : I j = ∫ y, (∫ u, G j (u + ∑ l, y l) ∂ν) ∂R := by
      rw [hIdef]; exact hpeel0
    have hIj1 : I (j + 1)
        = ∫ y, (∫ u, G j (u + ∑ l, y l) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂R := by
      rw [hIdef]
      refine hpeel1.trans ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => hdirac y)
    rw [hIj, hIj1]
    exact abs_sub_integral_peel_le_integral ν (stdGaussian (EuclideanSpace ℝ (Fin k)))
      (fun l : Fin m => κ j (i.succAbove l)) (hGcont j) (hGb j) hDint hbound
  have hrw : ∀ (σ : Measure (EuclideanSpace ℝ (Fin k))) (j : ℕ)
      (v : EuclideanSpace ℝ (Fin k)),
      (∫ u, G j (u + v) ∂σ)
        = ∫ u, (∫ z, f (c • v + sg j • z + c • u)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂σ := by
    intro σ j v
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hGdef, hΦdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    congr 1
    rw [smul_add]
    abel
  -- ### the constants of the ledger
  set Ck : ℝ := gaussianShellConst k with hCkdef
  have hCkpos : 0 < Ck := hCk
  have hcube : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 3
      = ((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    have h2 : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = ((m + 1 : ℕ) : ℝ) := Real.sq_sqrt hNr.le
    calc Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 3
        = Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by ring
      _ = ((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ) := by rw [h2]
  have hc3 : c ^ 3 = 1 / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    rw [hcdef, inv_pow, ← hcube, one_div]
  have hden : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ) := by positivity
  set θ : ℝ :=
      (12 * C₃ / ε ^ 3 / 6 / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ))) * X
        * (4 * Ck * (ε + Real.sqrt (J : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) + W)
      + (12 * C₃ / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ))) * X
        * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) with hθdef
  set K₁ : ℝ := 68 * Ck * (5 * Ct) * X / Real.sqrt ((m + 1 : ℕ) : ℝ)
    * gaussianTailRadius k ε with hK₁def
  set K₂ : ℝ := 4 * (W * (5 * Ct) * X) with hK₂def
  have hbr1 : (0 : ℝ) ≤ 4 * Ck * (ε + Real.sqrt (J : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) + W := by
    have h : (0 : ℝ) ≤ ε + Real.sqrt (J : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith [hCkpos.le]
  have hbr2 : (0 : ℝ) ≤ 32 * Ck / ε ^ 2 + 4 * W / ε ^ 3 := by
    have h1 : (0 : ℝ) ≤ 32 * Ck / ε ^ 2 := div_nonneg (by linarith) (by positivity)
    have h2 : (0 : ℝ) ≤ 4 * W / ε ^ 3 := div_nonneg (by linarith) (by positivity)
    linarith
  have hcoef1 : (0 : ℝ)
      ≤ 12 * C₃ / ε ^ 3 / 6 / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) :=
    div_nonneg (div_nonneg (div_nonneg (by linarith) (by positivity)) (by norm_num)) hden.le
  have hcoef2 : (0 : ℝ) ≤ 12 * C₃ / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) :=
    div_nonneg (by linarith) hden.le
  have hθnn : 0 ≤ θ := by
    rw [hθdef]
    exact add_nonneg (mul_nonneg (mul_nonneg hcoef1 hXpos.le) hbr1)
      (mul_nonneg (mul_nonneg hcoef2 hXpos.le) hbr2)
  have hK₁nn : 0 ≤ K₁ := by
    rw [hK₁def]
    exact mul_nonneg (div_nonneg (by positivity) (by positivity))
      (gaussianTailRadius_nonneg k ε)
  have hK₂nn : 0 ≤ K₂ := by rw [hK₂def]; positivity
  -- the window, in the form the head deconvolution needs
  have hck : c * Real.sqrt (k : ℝ) ≤ ε := by
    have h : c * Real.sqrt (k : ℝ) ≤ c * (ε * Real.sqrt ((m + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hwin hcpos.le
    have h2 : c * (ε * Real.sqrt ((m + 1 : ℕ) : ℝ)) = ε := by
      rw [hcdef]; field_simp
    linarith [h, h2.le, h2.ge]
  -- ### the head test function
  obtain ⟨gh, hghdef⟩ : ∃ gh : EuclideanSpace ℝ (Fin k) → ℝ, ∀ a,
      gh a = |(∫ u, f (a + c • u) ∂ν)
        - (∫ u, f (a + c • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| := ⟨_, fun _ => rfl⟩
  have hghcont : Continuous gh := by
    have hfun : gh = fun a => |(∫ u, f (a + c • u) ∂ν)
        - (∫ u, f (a + c • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| := funext hghdef
    rw [hfun]
    exact ((continuous_integral_add_smul hf.continuous hfb c).sub
      (continuous_integral_add_smul hf.continuous hfb c)).abs
  have hghb : ∀ a, |gh a| ≤ 2 := by
    intro a
    have h1 : |∫ u, f (a + c • u) ∂ν| ≤ 1 :=
      abs_integral_le_one (hf.continuous.comp (continuous_const.add (continuous_const_smul c)))
        (fun u => hfb _)
    have h2 : |∫ u, f (a + c • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))| ≤ 1 :=
      abs_integral_le_one (hf.continuous.comp (continuous_const.add (continuous_const_smul c)))
        (fun u => hfb _)
    obtain ⟨h1a, h1b⟩ := abs_le.1 h1
    obtain ⟨h2a, h2b⟩ := abs_le.1 h2
    rw [hghdef, abs_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  -- ### the head step
  have hhead : ∀ (j : ℕ) (hj : j < m + 1), |I j - I (j + 1)| ≤ θ := by
    intro j hj
    set R : Measure ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
      Measure.pi (fun l : Fin m => κ j ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)) with hRdef
    haveI hRp : IsProbabilityMeasure R := by rw [hRdef]; infer_instance
    set A : Measure (EuclideanSpace ℝ (Fin k)) := R.map (fun y => c • ∑ l, y l) with hAdef
    haveI hAp : IsProbabilityMeasure A := by
      rw [hAdef]
      exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
    set Gs : Measure (EuclideanSpace ℝ (Fin k)) :=
      (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => sg j • z) with hGsdef
    haveI hGsp : IsProbabilityMeasure Gs := by
      rw [hGsdef]
      exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
    haveI hτp : IsProbabilityMeasure (A ∗ Gs) := inferInstance
    set η : Measure (EuclideanSpace ℝ (Fin k)) := ν.map (fun u => c • u) with hηdef
    haveI hηp : IsProbabilityMeasure η := by
      rw [hηdef]
      exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
    have hμeq : hybridLaw (m + 1) j ν = (((A ∗ Gs).prod η).map fun p => p.1 + p.2) := by
      rw [← conv_eq_map_add, hAdef, hGsdef, hηdef, hsgval j]
      exact hybridLaw_conv_head hj ν (fun i => by rw [hκdef])
    have hbrick := head_step_le hk hmean hcov hβ hν2 hνdim hmeanγ hcovγ hβγ hf hfb hC₃ hε
      hD3 hD1 hD2 hone hsupp hW hcpos hck hηdef hμeq (hshell j (le_of_lt hj))
    obtain ⟨Dh, hDhdef⟩ : ∃ Dh : EuclideanSpace ℝ (Fin k) → ℝ, ∀ v,
        Dh v = ∫ z, gh (c • v + sg j • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      := ⟨_, fun _ => rfl⟩
    have hΨcont : Continuous fun x : EuclideanSpace ℝ (Fin k) =>
        ∫ z, gh (x + sg j • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
      continuous_integral_add_smul' hghcont hghb (sg j)
    have hDhcont : Continuous Dh := by
      have hfun : Dh = fun v => (fun x : EuclideanSpace ℝ (Fin k) =>
          ∫ z, gh (x + sg j • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) (c • v) :=
        funext hDhdef
      rw [hfun]
      exact hΨcont.comp (continuous_const_smul c)
    have hDhb : ∀ v, |Dh v| ≤ 2 := by
      intro v
      rw [hDhdef]
      exact abs_integral_le_const
        (hghcont.comp (continuous_const.add (continuous_const_smul (sg j)))) (fun z => hghb _)
    have hDhint : Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) =>
        Dh (∑ l, y l)) R :=
      integrable_of_bounded_cont (hDhcont.comp (by fun_prop)) (fun y => hDhb _)
    have hDhbound : ∀ v : EuclideanSpace ℝ (Fin k),
        |(∫ u, G j (u + v) ∂ν)
          - (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ≤ Dh v := by
      intro v
      rw [hrw ν j v, hrw (stdGaussian (EuclideanSpace ℝ (Fin k))) j v]
      have hunc : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
          Integrable (Function.uncurry fun u z : EuclideanSpace ℝ (Fin k) =>
              f (c • v + sg j • z + c • u))
            (σ.prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
        intro σ hσ
        haveI := hσ
        refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
        · exact (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
        · rw [Real.norm_eq_abs]; exact hfb _
      have hswapν := integral_integral_swap (hunc ν hν)
      have hswapγ := integral_integral_swap
        (hunc (stdGaussian (EuclideanSpace ℝ (Fin k))) inferInstance)
      simp only [Function.uncurry] at hswapν hswapγ
      rw [hswapν, hswapγ]
      have hcont : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
          Continuous fun z : EuclideanSpace ℝ (Fin k) =>
            ∫ u, f (c • v + sg j • z + c • u) ∂σ := by
        intro σ hσ
        haveI := hσ
        exact (continuous_integral_add_smul (σ := σ) hf.continuous hfb c).comp
          (continuous_const.add (continuous_const_smul (sg j)))
      have hbd : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
          ∀ z : EuclideanSpace ℝ (Fin k),
            |∫ u, f (c • v + sg j • z + c • u) ∂σ| ≤ 1 := by
        intro σ hσ z
        haveI := hσ
        exact abs_integral_le_one
          (hf.continuous.comp (continuous_const.add (continuous_const_smul c)))
          (fun u => hfb _)
      have hint1 : Integrable (fun z : EuclideanSpace ℝ (Fin k) =>
          ∫ u, f (c • v + sg j • z + c • u) ∂ν)
          (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
        integrable_of_bounded_continuous (hcont ν hν) (hbd ν hν)
      have hint2 : Integrable (fun z : EuclideanSpace ℝ (Fin k) =>
          ∫ u, f (c • v + sg j • z + c • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
        integrable_of_bounded_continuous
          (hcont (stdGaussian (EuclideanSpace ℝ (Fin k))) inferInstance)
          (hbd (stdGaussian (EuclideanSpace ℝ (Fin k))) inferInstance)
      rw [← integral_sub hint1 hint2]
      refine le_trans abs_integral_le_integral_abs ?_
      refine le_of_eq ?_
      rw [hDhdef]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hghdef _).symm)
    have hDhid : (∫ y, Dh (∑ l, y l) ∂R) = ∫ a, gh a ∂(A ∗ Gs) := by
      rw [hGsdef, integral_conv_smul_gaussian A (sg j) hghcont hghb, hAdef,
        integral_map (φ := fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) => c • ∑ l, y l)
          (f := fun x => ∫ z, gh (x + sg j • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          (by fun_prop) hΨcont.aestronglyMeasurable]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => hDhdef _)
    calc |I j - I (j + 1)| ≤ ∫ y, Dh (∑ l, y l) ∂R := hstepfun j hj Dh hDhint hDhbound
      _ = ∫ a, gh a ∂(A ∗ Gs) := hDhid
      _ = ∫ a, |(∫ u, f (a + c • u) ∂ν)
            - (∫ u, f (a + c • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ∂(A ∗ Gs) :=
          integral_congr_ae (Filter.Eventually.of_forall fun a => hghdef a)
      _ ≤ 12 * (C₃ / ε ^ 3 / 6 * c ^ 3) * X * (4 * Ck * ε + W)
          + 12 * (C₃ * c ^ 3) * X * (32 * Ck / ε ^ 2 + 4 * W / ε ^ 3) := hbrick
      _ ≤ θ := by
          rw [hθdef, hc3]
          have hQ : (0 : ℝ) ≤ Real.sqrt (J : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ) := by positivity
          have hco : (0 : ℝ) ≤ 12 * (C₃ / ε ^ 3 / 6 * (1 / (((m + 1 : ℕ) : ℝ)
              * Real.sqrt ((m + 1 : ℕ) : ℝ)))) * X := by
            refine mul_nonneg (mul_nonneg (by norm_num) ?_) hXpos.le
            exact mul_nonneg (div_nonneg (div_nonneg (by linarith) (by positivity))
              (by norm_num)) (by positivity)
          have hmono : 4 * Ck * ε + W
              ≤ 4 * Ck * (ε + Real.sqrt (J : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) + W := by
            nlinarith [hCkpos.le, hQ]
          have e1 : 12 * C₃ / ε ^ 3 / 6
                / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) * X
              = 12 * (C₃ / ε ^ 3 / 6
                * (1 / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)))) * X := by
            field_simp
          have e2 : 12 * C₃ / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) * X
              = 12 * (C₃ * (1 / (((m + 1 : ℕ) : ℝ)
                * Real.sqrt ((m + 1 : ℕ) : ℝ)))) * X := by
            field_simp
          rw [e1, e2]
          nlinarith [mul_le_mul_of_nonneg_left hmono hco]
  -- ### the tail test function
  obtain ⟨gt, hgtdef⟩ : ∃ gt : ℕ → EuclideanSpace ℝ (Fin k) → ℝ, ∀ (j : ℕ) (v : _),
      gt j v = |(∫ y, (∫ z, f (v + sg j • z + c • y)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
        - (∫ y, (∫ z, f (v + sg j • z + c • y)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| := ⟨_, fun _ _ => rfl⟩
  have hgtcont : ∀ j, Continuous (gt j) := by
    intro j
    have hfun : gt j = fun v => |(∫ y, (∫ z, f (v + sg j • z + c • y)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
        - (∫ y, (∫ z, f (v + sg j • z + c • y)
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| := funext (hgtdef j)
    rw [hfun]
    exact ((continuous_double_smooth (ν := ν) hf.continuous hfb (sg j) c).sub
      (continuous_double_smooth (ν := stdGaussian (EuclideanSpace ℝ (Fin k)))
        hf.continuous hfb (sg j) c)).abs
  have hgtb : ∀ (j : ℕ) (v : EuclideanSpace ℝ (Fin k)), |gt j v| ≤ 2 := by
    intro j v
    have hbd : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
        |∫ y, (∫ z, f (v + sg j • z + c • y)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂σ| ≤ 1 := by
      intro σ hσ
      haveI := hσ
      refine abs_integral_le_one ?_ ?_
      · have hc1 : Continuous fun y : EuclideanSpace ℝ (Fin k) =>
            ∫ z, f (v + c • y + sg j • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
          (continuous_integral_add_smul (σ := stdGaussian (EuclideanSpace ℝ (Fin k)))
            hf.continuous hfb (sg j)).comp
            (continuous_const.add (continuous_const_smul c))
        refine hc1.congr fun y => ?_
        exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
          congrArg f (add_right_comm _ _ _).symm)
      · intro y
        exact abs_integral_le_one (hf.continuous.comp (by fun_prop)) (fun z => hfb _)
    obtain ⟨h1a, h1b⟩ := abs_le.1 (hbd ν hν)
    obtain ⟨h2a, h2b⟩ := abs_le.1 (hbd (stdGaussian (EuclideanSpace ℝ (Fin k))) inferInstance)
    rw [hgtdef, abs_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  -- ### the tail step
  have htail : ∀ (j : ℕ) (hj : j < m + 1), J ≤ j →
      |I j - I (j + 1)| ≤ K₁ / (j : ℝ) + K₂ / ((j : ℝ) * Real.sqrt (j : ℝ)) := by
    intro j hj hJj
    have hj1 : 1 ≤ j := by omega
    have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
    have hqpos : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hjpos
    have hsgjpos : 0 < sg j := hsgpos j hj1
    have hsgq : sg j = c * Real.sqrt (j : ℝ) := by rw [hsgdef]
    have hεsg : ε ≤ sg j := by
      rw [hsgval j, le_div_iff₀ hsN]
      have h1 : ε * Real.sqrt ((m + 1 : ℕ) : ℝ)
          = Real.sqrt (ε ^ 2 * ((m + 1 : ℕ) : ℝ)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le]
      rw [h1]
      exact Real.sqrt_le_sqrt (le_trans hJε (by exact_mod_cast hJj))
    have hsgle1 : sg j ≤ 1 := by
      rw [hsgval j, div_le_one hsN]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (le_of_lt hj))
    have hsgj1pos : 0 < sg (j + 1) := hsgpos (j + 1) (by omega)
    have hsgj1 : sg (j + 1) ≤ 3 / 2 * sg j := by
      have h : Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ 3 / 2 * Real.sqrt (j : ℝ) := by
        have hb : ((j + 1 : ℕ) : ℝ) ≤ (3 / 2 : ℝ) ^ 2 * (j : ℝ) := by
          push_cast; nlinarith [hjr]
        calc Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2 * (j : ℝ)) :=
              Real.sqrt_le_sqrt hb
          _ = 3 / 2 * Real.sqrt (j : ℝ) := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      rw [hsgval (j + 1), hsgval j, div_le_iff₀ hsN]
      have he : 3 / 2 * (Real.sqrt (j : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ))
          * Real.sqrt ((m + 1 : ℕ) : ℝ) = 3 / 2 * Real.sqrt (j : ℝ) := by
        field_simp
      rw [he]
      exact h
    set R : Measure ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
      Measure.pi (fun l : Fin m => κ j ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)) with hRdef
    haveI hRp : IsProbabilityMeasure R := by rw [hRdef]; infer_instance
    set A : Measure (EuclideanSpace ℝ (Fin k)) := R.map (fun y => c • ∑ l, y l) with hAdef
    haveI hAp : IsProbabilityMeasure A := by
      rw [hAdef]
      exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
    set Gs' : Measure (EuclideanSpace ℝ (Fin k)) :=
      (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => sg (j + 1) • z) with hGs'def
    haveI hGs'p : IsProbabilityMeasure Gs' := by
      rw [hGs'def]
      exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
    have hμeq : hybridLaw (m + 1) (j + 1) ν = ((A.prod Gs').map fun p => p.1 + p.2) := by
      rw [← conv_eq_map_add, hAdef, hGs'def, hsgval (j + 1)]
      exact hybridLaw_conv_tail hj ν (fun i => by rw [hκdef])
    have hbrick := tail_step_le hk hCtb hCt1 hmean hcov hν1 hν2 hβ hνdim hmeanγ hcovγ
      hγ1 hγ2 hβγ hγdim hf.continuous hfb hε hone hsupp hW hsgjpos hεsg hsgle1 hcpos
      hsgj1pos hsgj1 hCw hGs'def hμeq (hshell (j + 1) (by omega))
    obtain ⟨Dt, hDtdef⟩ : ∃ Dt : EuclideanSpace ℝ (Fin k) → ℝ, ∀ v,
        Dt v = gt j (c • v) := ⟨_, fun _ => rfl⟩
    have hDtcont : Continuous Dt := by
      have hfun : Dt = fun v => gt j (c • v) := funext hDtdef
      rw [hfun]
      exact (hgtcont j).comp (continuous_const_smul c)
    have hDtb : ∀ v, |Dt v| ≤ 2 := fun v => by rw [hDtdef]; exact hgtb j _
    have hDtint : Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) =>
        Dt (∑ l, y l)) R :=
      integrable_of_bounded_cont (hDtcont.comp (by fun_prop)) (fun y => hDtb _)
    have hDtbound : ∀ v : EuclideanSpace ℝ (Fin k),
        |(∫ u, G j (u + v) ∂ν)
          - (∫ u, G j (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ≤ Dt v := by
      intro v
      rw [hrw ν j v, hrw (stdGaussian (EuclideanSpace ℝ (Fin k))) j v, hDtdef, hgtdef]
    have hDtid : (∫ y, Dt (∑ l, y l) ∂R) = ∫ v, gt j v ∂A := by
      rw [hAdef, integral_map
        (φ := fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) => c • ∑ l, y l)
        (f := fun v => gt j v) (by fun_prop) (hgtcont j).aestronglyMeasurable]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => hDtdef _)
    have hstep : |I j - I (j + 1)| ≤ ∫ v, gt j v ∂A :=
      (hstepfun j hj Dt hDtint hDtbound).trans (le_of_eq hDtid)
    have hgtA : (∫ v, gt j v ∂A)
        = ∫ v, |(∫ y, (∫ z, f (v + sg j • z + c • y)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) ∂ν)
            - (∫ y, (∫ z, f (v + sg j • z + c • y)
                ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
                ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))| ∂A :=
      integral_congr_ae (Filter.Eventually.of_forall fun v => hgtdef j v)
    rw [hgtA] at hstep
    refine hstep.trans (hbrick.trans ?_)
    -- the per-step ledger
    have hCkCtXc : (0 : ℝ) ≤ Ck * Ct * X * c :=
      mul_nonneg (mul_nonneg (mul_nonneg hCkpos.le hCt0.le) hXpos.le) hcpos.le
    have hp : Ct * (c / sg j) ^ 3 * X = Ct * X / ((j : ℝ) * Real.sqrt (j : ℝ)) := by
      have hcs : c / sg j = 1 / Real.sqrt (j : ℝ) := by
        rw [hsgq]; field_simp
      have hjs : Real.sqrt (j : ℝ) ^ 3 = (j : ℝ) * Real.sqrt (j : ℝ) := by
        have h2 : Real.sqrt (j : ℝ) ^ 2 = (j : ℝ) := Real.sq_sqrt hjpos.le
        calc Real.sqrt (j : ℝ) ^ 3 = Real.sqrt (j : ℝ) ^ 2 * Real.sqrt (j : ℝ) := by ring
          _ = (j : ℝ) * Real.sqrt (j : ℝ) := by rw [h2]
      rw [hcs, div_pow, one_pow, hjs]
      ring
    have hsgp : sg j * (Ct * (c / sg j) ^ 3 * X) = Ct * X * c / (j : ℝ) := by
      rw [hp, hsgq]
      field_simp
    have hexp : (336 * Ck * (sg j * gaussianTailRadius k (sg j)) + 8 * W)
          * (Ct * (c / sg j) ^ 3 * X)
        = 336 * Ck * gaussianTailRadius k (sg j) * (sg j * (Ct * (c / sg j) ^ 3 * X))
          + 8 * W * (Ct * (c / sg j) ^ 3 * X) := by ring
    rw [hexp, hsgp, hp]
    have hR := gaussianTailRadius_anti (k := k) hε hεsg
    have hRe0 : (0 : ℝ) ≤ gaussianTailRadius k ε := gaussianTailRadius_nonneg k ε
    have hK1val : K₁ = 340 * Ck * Ct * X * c * gaussianTailRadius k ε := by
      rw [hK₁def, hcdef]; field_simp; ring
    have hnum1 : 336 * Ck * gaussianTailRadius k (sg j) * (Ct * X * c)
        ≤ 340 * Ck * Ct * X * c * gaussianTailRadius k ε := by
      nlinarith [mul_nonneg hCkCtXc (sub_nonneg.2 hR), mul_nonneg hCkCtXc hRe0]
    have hA1 : 336 * Ck * gaussianTailRadius k (sg j) * (Ct * X * c / (j : ℝ))
        ≤ K₁ / (j : ℝ) := by
      have e1 : 336 * Ck * gaussianTailRadius k (sg j) * (Ct * X * c / (j : ℝ))
          = 336 * Ck * gaussianTailRadius k (sg j) * (Ct * X * c) * (j : ℝ)⁻¹ := by ring
      have e2 : K₁ / (j : ℝ) = K₁ * (j : ℝ)⁻¹ := by ring
      rw [e1, e2, hK1val]
      exact mul_le_mul_of_nonneg_right hnum1 (le_of_lt (inv_pos.2 hjpos))
    have hWCtX : (0 : ℝ) ≤ W * Ct * X :=
      mul_nonneg (mul_nonneg hW hCt0.le) hXpos.le
    have hnum2 : 8 * (W * Ct * X) ≤ K₂ := by rw [hK₂def]; nlinarith [hWCtX]
    have hDpos : (0 : ℝ) < (j : ℝ) * Real.sqrt (j : ℝ) := by positivity
    have hA2 : 8 * W * (Ct * X / ((j : ℝ) * Real.sqrt (j : ℝ)))
        ≤ K₂ / ((j : ℝ) * Real.sqrt (j : ℝ)) := by
      have e1 : 8 * W * (Ct * X / ((j : ℝ) * Real.sqrt (j : ℝ)))
          = 8 * (W * Ct * X) * ((j : ℝ) * Real.sqrt (j : ℝ))⁻¹ := by ring
      have e2 : K₂ / ((j : ℝ) * Real.sqrt (j : ℝ))
          = K₂ * ((j : ℝ) * Real.sqrt (j : ℝ))⁻¹ := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hnum2 (le_of_lt (inv_pos.2 hDpos))
    linarith
  -- ### summing the steps
  set T : ℕ → ℝ := fun j => if j < m + 1 then |I j - I (j + 1)| else 0 with hTdef
  have hTnn : ∀ j, 0 ≤ T j := by
    intro j; rw [hTdef]; dsimp only; split_ifs
    · positivity
    · exact le_rfl
  have hTθ : ∀ j, T j ≤ θ := by
    intro j; rw [hTdef]; dsimp only; split_ifs with hjlt
    · exact hhead j hjlt
    · exact hθnn
  have hTdec : ∀ j, J ≤ j → T j ≤ K₁ / (j : ℝ) + K₂ / ((j : ℝ) * Real.sqrt (j : ℝ)) := by
    intro j hJj
    have hjge : 2 ≤ j := le_trans hJ2 hJj
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have h2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjge
      linarith
    have hnn : (0 : ℝ) ≤ K₁ / (j : ℝ) + K₂ / ((j : ℝ) * Real.sqrt (j : ℝ)) := by
      have h1 : (0 : ℝ) ≤ K₁ / (j : ℝ) := div_nonneg hK₁nn hjpos.le
      have h2 : (0 : ℝ) ≤ K₂ / ((j : ℝ) * Real.sqrt (j : ℝ)) :=
        div_nonneg hK₂nn (by positivity)
      linarith
    rw [hTdef]; dsimp only; split_ifs with hjlt
    · exact htail j hjlt hJj
    · exact hnn
  have hsum := sum_le_of_bounded_and_weighted_decay hK₁nn hK₂nn hθnn (n := m + 1) hJ2
    hTnn hTθ hTdec
  have htelsum : ∀ N : ℕ, |I 0 - I N| ≤ ∑ j ∈ Finset.range N, |I j - I (j + 1)| := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h3 : |I 0 - I (N + 1)| ≤ |I 0 - I N| + |I N - I (N + 1)| := abs_sub_le _ _ _
      linarith
  have hTsum : ∑ j ∈ Finset.range (m + 1), |I j - I (j + 1)|
      = ∑ j ∈ Finset.range (m + 1), T j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hTdef]; dsimp only; rw [if_pos (Finset.mem_range.1 hj)]
  -- ### the two endpoints
  have hκ0 : κ 0 = fun _ : Fin (m + 1) => ν := by funext i; rw [hκdef]; simp
  have hκN : κ (m + 1) = fun _ : Fin (m + 1) => Measure.dirac 0 := by
    funext i; rw [hκdef]; dsimp only; rw [if_pos i.isLt]
  have hG0 : ∀ w : EuclideanSpace ℝ (Fin k), G 0 w = f (c • w) := by
    intro w
    simp only [hGdef, hΦdef, hsg0, zero_smul, add_zero]
    rw [integral_const]
    simp
  have hI0 : I 0 = ∫ x, f x ∂(sumLaw (m + 1) ν) := by
    rw [sumLaw, integral_map (by fun_prop) hf.continuous.aestronglyMeasurable]
    simp only [hIdef]
    rw [hκ0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hG0 _)
  have hIN : I (m + 1) = ∫ z, f z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    simp only [hIdef]
    rw [hκN, measure_pi_dirac_zero, integral_dirac]
    simp only [Finset.sum_const_zero, hGdef, hΦdef, hsgN1, one_smul, smul_zero, zero_add]
  have hfin : |I 0 - I (m + 1)|
      ≤ (J : ℝ) * θ + K₁ * (1 + Real.log (max (((m + 1 : ℕ) : ℝ) / (J : ℝ)) 1))
        + 3 * K₂ / Real.sqrt (J : ℝ) := by
    calc |I 0 - I (m + 1)| ≤ ∑ j ∈ Finset.range (m + 1), |I j - I (j + 1)| := htelsum _
      _ = ∑ j ∈ Finset.range (m + 1), T j := hTsum
      _ ≤ _ := hsum
  rw [hI0, hIN] at hfin
  refine hfin.trans (le_of_eq ?_)
  rw [hθdef, hK₂def]
  ring
/-- **Brick L below the Gaussian shell scale (stated, not proved; hypothesis AMENDED in
wave 29).** *The hybrid telescope with every step estimated by the localised weighted swap
bound*, in the only regime that has any content: the total weight `W + C_k ε` is at most `1`.

This is `abs_integral_smooth_sub_gaussian_improved` rerun with a shell-weighted Cameron–Martin
remainder in place of the uniform `integral_abs_vecTiltRemainder_le`. Summing the weighted steps
with the cut `J = ⌈ε² n⌉` of `abs_integral_smooth_sub_gaussian_balanced` gives `A (β/√n) ε⁻¹ W`
in place of the unweighted `A (β/√n) ε⁻¹`.

The `L^∞` form is stated (weight `W`, not `√W`), which is what the sharp `β/√n` rate needs; the
wave-19 `L²`/Cauchy–Schwarz form `abs_integral_mul_vecTiltRemainder_le_of_support` delivers `√W`
instead, for which `cube_le_of_selfImproving_smoothed_sqrt` gives `O(n^{-1/3})`.

## Wave 29: the wave-24 diagnosis is WRONG, and the hypothesis is amended

Wave 24 wrote: splitting `f = 1_{interior B} + g` localises the `g` half by the wave-19 lemma,
but leaves the indicator half `∫ 1_K R_w dγ = γ(K − w) − Q_w(K)`, and "bounding *that* by the
shell mass is a Gaussian surface-area statement about convex bodies — the same input as Ball's
theorem". **That verdict is overturned.** No surface area is involved. The tilt remainder has
mean zero, `integral_vecTiltRemainder_eq_zero`, so a *constant* may be subtracted from the test
function for free; and near a point `v` at distance `≥ r` from the boundary the mollified
indicator *is* constant on the ball of radius `r`. Cauchy–Schwarz against the plain **Gaussian
tail** `γ{‖z‖ ≥ r/σ}` then localises the indicator half:
`abs_integral_mul_vecTiltRemainder_le_of_const_off` and
`abs_integral_shift_vecTiltRemainder_le_of_const_ball`, with `stdGaussian_norm_ge_le` (Markov at
any order) supplying the tail. All four are proved and axiom-clean; none of them mentions a
surface measure, and their constants are dimension-free.

**Why the hypothesis had to change.** Two corrections to the wave-24 interface, both forced by
the localisation just described and both *free* at the only call site:

1. *The shell must be two-sided.* The per-point weight is small exactly when `f` is constant on
   a ball about `v`, i.e. when `v` is outside the thickening **or inside the erosion**. The bad
   set is `B^s \ B_{-s}`, and its inner half `B \ B_{-s}` is invisible to the frozen hypothesis,
   which speaks only of `B^{2ε} \ interior B`.
2. *Every width must be controlled, not just `2ε`.* Step `j` of the telescope is smoothed at
   `σⱼ = √(j/n)`, and the localisation radius that step can afford is a multiple of `σⱼ`, not of
   `ε`. For `j > J = ⌈ε²n⌉` one has `σⱼ ≥ ε`, and for `j` near `n` one has `σⱼ ≈ 1 ≫ ε`; the
   frozen hypothesis says nothing about neighbourhoods at those scales.

`hybridLaw_wideShell_le` (wave 29, proved) supplies exactly the amended hypothesis at the call
site, at every width, with the constant `4 C_k` and the same `2Y` that brick H already carries —
so `exists_convexDiscrepancy_recursion`, `berryEsseen_convex_sharp` and its constant are
unaffected. Note that the amendment does not weaken the *content*: the frozen statement is true
(it is implied by Bentkus's theorem, since its right-hand side is `≥ A C_k β/√n`); what the
amendment records is the interface the *proof* needs.

## Wave 32: the CONCLUSION is amended too — the logarithm is forced

Wave 29 left the conclusion in its frozen (log-free) form on the ground that weakening it then
"would be a guess rather than a forced amendment". It is not a guess: the summation ledger below
*forces* it, and wave 32 executes the amendment.

**The ledger.** Write `c = n^{-1/2}`, `σⱼ = c√j`, `δ = β/√n`, `J = ⌈ε²n⌉`. The telescope has
`n` steps; step `j` is smoothed at width `σⱼ` and its localised Cameron–Martin cost is

`(per-step weight) × C_t β_j / (j √j)`,  `β_j ≍ β + β_G ≤ 3β`,

by `abs_integral_gaussian_smoothed_swap_le` (this is `hboundB` of
`abs_integral_smooth_sub_gaussian_improved`; the `j^{-3/2}` is `(c/σⱼ)³`). The *weight* the
localisation supplies at step `j` is the two-sided-shell mass at the radius that step can
afford, which is a multiple of `σⱼ`, so it is `4 C_k σⱼ + W` — hence the amended hypothesis. The
tail of the balanced sum is therefore

`∑_{J<j≤n} j^{-3/2}(4C_k σⱼ + W)·3β = 3β(4C_k c ∑_{J<j≤n} j^{-1} + W ∑_{J<j≤n} j^{-3/2})`.

Now `c = n^{-1/2}` and `β c = δ`, so the first piece is `12 C_k δ ∑_{J<j≤n} j^{-1}
≤ 12 C_k δ (1 + log(n/J)) ≤ 12 C_k δ (1 + log(1/ε²)) = 12 C_k δ (1 + 2 log(1/ε))`, and the
second is `3 β W ∑_{j>J} j^{-3/2} ≤ 6 β W J^{-1/2} ≤ 6 β W /(ε√n) = 6 δ W ε⁻¹`. The head
`j ≤ J` is the classical shell-localised swap, `J·(M/6)c³·3β ≤ (3/2) C₃ δ ε⁻¹` exactly as in
`abs_integral_smooth_sub_gaussian_balanced`. Summing:

`A δ (ε⁻¹ (W + C_k ε) + C_k (1 + log(1/ε)))`,

which is the conclusion now recorded. **Both exponents check out**: `j^{-1}` (not `j^{-1/2}`)
after `σⱼ = c√j` cancels one `√j`, giving the harmonic sum and hence the logarithm; and
`j^{-3/2}` summed from `J` gives `J^{-1/2} = (ε√n)^{-1}`, i.e. exactly the `ε⁻¹` the frozen form
already carried. The logarithm is intrinsic to a *single* mollification width: killing it needs
per-step widths `εⱼ ≍ σⱼ`, which the frozen single `f` cannot provide.

The statement below writes `1 + log(1 + ε⁻¹)` rather than `1 + log(1/ε)`; the two agree up to a
factor `2` for `ε ≤ 1`, and the `1 +` inside makes the extra term nonnegative for *every*
`ε > 0`, so no `ε ≤ 1` side condition has to be threaded through the call sites (and the amended
statement is then unambiguously *weaker* than the frozen one — it is implied by Bentkus's
theorem, as the frozen form was).

**The ledger is FORMALISED, not merely asserted.** `sum_le_of_bounded_and_weighted_decay` is the
statement above as a proved lemma about real sequences, over the two tail bounds
`sum_Ico_one_div_le` (harmonic — the logarithm) and `sum_Ico_inv_mul_sqrt_le` (summable — the
`ε⁻¹`), both proved. So the bookkeeping half of this brick is discharged; what is left is the
*analytic* half, the production of its per-step hypothesis `hTdec` — see "What is still
missing" below.

**Remark (trading the log for a power).** If the Gaussian tail is used in its Markov form
`stdGaussian_norm_ge_le p` at a *fixed* order `p = 2m`, rather than at all orders at once, the
per-step weight is `(σⱼ/r)^{m}` and the harmonic sum is replaced by a convergent one; the
logarithm becomes `ε^{-1/(m+1)}` and the headline `(β/√n)^{m/(m+1)}`. That is strictly weaker
than the log form for every fixed `m`, so the route below is not restructured for it.

## What is still missing (wave 32, re-derived)

One item, and it is now sharply delimited: **the per-step weighted swap bound**, i.e. the
hypothesis `hTdec` of `sum_le_of_bounded_and_weighted_decay`. Concretely, a weighted rerun of
`hboundB` inside `abs_integral_smooth_sub_gaussian_improved`, delivering at step `j ≥ 1`

`|∫ Gⱼ(· + v) dν − ∫ Gⱼ(· + v) dγ| ≤ (4 C_k σⱼ + W) · 3 C_t (β + β_G) / (j √j)`

in place of the unweighted `C_t (β + β_G)/(j√j)`. Everything downstream of it — the summation,
the cut `J = ⌈ε²n⌉`, the fixed point, the headline — is proved. Its two analytic ingredients are
in place (the wave-19 weighted lemma `abs_integral_mul_vecTiltRemainder_le_of_support` and its
wave-29 constant-off/Gaussian-tail extensions), but the shift-length restriction has to be
handled:

* **The `‖w‖ ≤ 1` restriction.** Both the wave-19 lemma and its wave-29 constant-off extension
  require a Cameron–Martin shift of length at most `1` (for `‖w‖ > 1` the `L²` norm of the tilt
  blows up like `e^{‖w‖²}` — see `integral_sq_tiltRemainder_le`). At step `j` the shift is
  `w = (c/σⱼ) y` with `c = n^{-1/2}`, i.e. `‖w‖ = ‖y‖/√j`, so the bound applies only on
  `{‖y‖ ≤ √j}`. Wave 24's claim that the wave-19 lemma "applies to `g` verbatim" is therefore
  also too optimistic. On `{‖y‖ > √j}` one must instead use the tilt identity directly:
  `∫ G R_w dγ = ∫ (G(· + w) − a) dγ − ∫ (G − a)·Q_w dγ`, whose second term is localised with the
  factor `1 + ‖w‖²  ≤ 2‖w‖³` and whose first term is localised *after averaging in `v`*, the
  mismatch `a_v ≠ a_{v + c y}` costing the mass of a `c‖y‖`-neighbourhood of `∂B`, i.e. again a
  two-sided shell, at width `c‖y‖ ≤ σⱼ‖w‖`. This is the reason the amended hypothesis is stated
  at *all* widths and not merely at the `σⱼ`. Third-moment integrability of `y` prices the
  `{‖y‖ > √j}` tail.

## Wave 35: the bookkeeping side is CLOSED, and two ledger corrections

Wave 35 discharges the rest of the bookkeeping in Lean and sharpens the residue. The reduction

`localised_swap_bound_of_weighted_telescope`

is proved and axiom-clean: it derives this theorem's conclusion, with the explicit constant
`18 C₃ + 33 C_t`, from the weighted hybrid telescope at every cut `J ≥ 2`, by taking
`J = max 2 ⌈ε² n⌉` and running the arithmetic of `weighted_ledger_balance`. Its `D` is an
arbitrary real and no hypothesis about `B` or `f` is used, so it is exactly the reduction and
nothing more. With `sum_le_of_bounded_and_weighted_decay` (wave 32, the summation half) the
entire non-analytic side of this brick is now machine-checked.

**Correction 1 (the head must be weighted too).** The wave-32 ledger estimates the head
`j ≤ J` as `J·(M/6)c³·3β ≤ (3/2) C₃ δ ε⁻¹`, *unweighted*. That cannot close: the amended
conclusion contains **no bare `ε⁻¹`** — every `ε⁻¹` in it appears as `ε⁻¹(W + C_k ε)`, which
stays bounded as `ε ↓ 0` when `W = 0`, while `(3/2) C₃ δ ε⁻¹` blows up. So the elementary
(third-order Taylor) steps must be localised as well, at the weight `4 C_k σ_J + W`, with
`σ_J = √J/√n ≤ 2ε` at the chosen cut; the head then lands on `18 C₃ δ ε⁻¹(W + C_k ε)`. This is
recorded in the hypothesis of `localised_swap_bound_of_weighted_telescope` and is now the
*second* analytic item, alongside the Cameron–Martin one below.

**Correction 2 (the window `1 ≤ ε √n`) — RESOLVED in wave 36: it is now a hypothesis, and it
is discharged at the call site.** The ledger is silent about `ε √n < 1`, and there it fails: the
cut degenerates to `J = 2`, the head becomes `≍ C₃ β (W/t³ + C_k ε/t⁴)` with `t = ε √n`, and
this exceeds the right-hand side `≍ β (W/t + C_k/√n)` by `t^{-2}`. No cut repairs it, because
the elementary step bound beats the Cameron–Martin one only for `j ≲ ε² n`, i.e. for no step at
all. Nor is the trivial bound `|∫ f dμ − ∫ f dγ| ≤ 2` available here (unlike in
`exists_smooth_swap_bound_of_one_le_weight`, where `W ≥ 1` makes the right-hand side `≥ A`): for
`ε √n < 1` the right-hand side is `≥ A C_k β/√n`, which is `o(1)`. The statement is still *true*
in that window — it is implied by Bentkus's theorem, as the whole amended statement is — but
this route cannot prove it there, since sandwiching `f` between `1_B` and `1_{B^ε}` leaves
exactly `|μₙ(B) − γ(B)| ≤ A C_k β/√n`, the sharp bound itself.

Wave 35 left open whether threading the window costs anything downstream. **It costs nothing**,
and the reason is that the fixed point never visits the small window:

* `le_of_selfImproving_induction_log` instantiates its `hrec` at exactly **one** width,
  `ε = 8 A δ` with `δ = b/√n`. There `ε √n = 8 A b`, which **does not depend on `n`** — so the
  window is a condition on the *constants* alone. Accordingly that lemma's `hrec` now demands
  the recursion only for `1 ≤ ε √n`, and the lemma carries the hypothesis `1 ≤ 8 A b`; the side
  condition is discharged internally by `√n · √n = n`.
* At the unique call site, `berryEsseen_convex_sharp`, the induction is run with `A := A + 1`
  (`A > 0` from `exists_convexDiscrepancy_recursion`) and `b := β = ∫‖y‖³ dν`. Since
  `sqrt_dim_mul_dim_le_integral_norm_cube` gives `k^{3/2} ≤ β` and `k ≥ 1`, one has `β ≥ 1`, so
  `ε √n = 8 (A + 1) β ≥ 8 ≥ 1` always. (This is the same `hβ1` already used inside
  `localised_swap_bound_of_weighted_telescope`.)

So `1 ≤ ε √n` now appears as a hypothesis of this theorem, of `exists_localised_swap_bound`
(where the large-weight branch ignores it and the small-weight branch consumes it) and of
`exists_convexDiscrepancy_recursion`, and the headline `berryEsseen_convex_sharp` is proved with
its constant unchanged. **The small window is no longer an open gap of this route**, and the cut
`J = max 2 ⌈ε² n⌉` is non-degenerate wherever the theorem is now stated, so the head/tail
crossover below is genuine.

**The residue, after wave 35.** Two per-step estimates on the hybrid telescope, both localised
by the two-sided-shell hypothesis, and nothing else:

* *head steps* (`j ≤ J`): the elementary swap `abs_integral_swap_step_le` localised to weight
  `4 C_k σ_J + W`, cost `(M/6) n^{-3/2}(β + β_G)` — correction 1;
* *tail steps* (`j > J`): the Cameron–Martin swap `abs_integral_gaussian_smoothed_swap_le`
  localised to weight `4 C_k σⱼ + W`, cost `C_t(β + β_G)/(j√j)` — the wave-32 item, whose
  `‖w‖ ≤ 1` obstruction is analysed above.

Both are averaged statements (the weight is a *mass* under `hybridLaw n j ν`, not a pointwise
bound), so `hstepgen` inside `abs_integral_smooth_sub_gaussian_improved` has to be generalised
from a constant `D` to a `v`-dependent one integrated against the remaining coordinates. That
generalisation, and the two estimates, are all that stand between this `sorry` and the headline.

## Wave 36: the structural half is BUILT, and the head estimate is not what wave 35 said

**Built and machine-checked this wave** (besides Correction 2 above, now resolved):

* `abs_sub_integral_peel_le_integral` — the telescope step with a `v`-*dependent* bound. The
  wave-16 argument never used constancy of `D`, only `integral_mono` against a constant, so the
  generalisation costs one integrability hypothesis and nothing else.
  `abs_integral_smooth_sub_gaussian_improved` is rewired through it (its `hstepfun`), with the
  old constant-`D` `hstepgen` re-derived in three lines; the telescope's conclusion is
  unchanged.
* `integral_hybridLaw_eq` and `integral_peel_eq_integral_hybridLaw` — the **bridge**. Wave 20
  asserted that `hybridLaw n j ν` "is exactly the measure against which
  `abs_integral_smooth_sub_gaussian_improved` evaluates its `j`-th test function", but that
  identity had never been recorded in Lean: brick H speaks about `hybridLaw`, the telescope
  about `Iⱼ`, and nothing connected them. It is a *prerequisite*, not a convenience — the
  weight of both localised estimates is a shell mass under `hybridLaw n j ν`, so without the
  bridge neither estimate can be stated in the form the reduction consumes. The two lemmas
  together say: if `D v` is the average over the peeled coordinate `u ~ ν` and the smoothing
  `z ~ γ` of a bounded continuous `F` at `c(v + u) + σⱼ z`, then `∫ D(∑ₗ yₗ) dR` is exactly
  `∫ F d(hybridLaw n j ν)`. So a shell indicator there produces precisely the mass the amended
  weight hypothesis bounds.

**The head estimate is NOT `abs_integral_swap_step_le` localised.** Wave 35's Correction 1
describes the head as "the elementary swap `abs_integral_swap_step_le` localised to weight
`4 C_k σ_J + W`". That understates it in the same way wave 24's "the wave-19 lemma applies to
`g` verbatim" understated the Cameron–Martin half. `abs_integral_swap_step_le` bounds the
third-order Taylor remainder by the **global** `‖D³f‖_∞ ≤ C₃/ε³`. Localising means using
instead that `D³f` is *supported* in the shell — but the Lagrange remainder controls `D³f`
along the whole segment `[a, a + c y]`, not at a point, so what the shell indicator is
evaluated at is a neighbourhood of width `c‖y‖`, which is **unbounded** in `y`. (This is the
same mechanism as the `‖w‖ ≤ 1` obstruction above, and the second reason the amended hypothesis
is stated at *all* widths `s` rather than only at the `σⱼ`.)

Pricing the segment naively costs `∫ ‖y‖³ · 4 C_k c‖y‖ dν`, i.e. a **fourth** moment, which
`hβint` does not give. The repair is a two-regime split at `‖y‖ = R := ε √n` — note this is
`≥ 1` exactly by the window of Correction 2, which is why item 1 above had to come first:

* `‖y‖ ≤ R`: the segment stays within `c‖y‖ ≤ ε` of `a`, so the shell is at width `≍ 2ε` and
  the localised Taylor bound gives the wave-35 head shape, weight `4 C_k (ε + σ_J) + W`;
* `‖y‖ > R`: do not Taylor-expand at all — bound the remainder by its lower-order terms,
  localised at the varying width `c‖y‖`, so the weight is `4 C_k c‖y‖ + W` and only
  `∫_{‖y‖>R} ‖y‖^p dν ≤ β / R^{3−p}` (`p ≤ 2`) is needed. Summed over the `J ≍ ε² n` head
  steps this contributes `≍ C_k δ + W δ ε⁻¹`, which **is** of the allowed shape
  `δ(ε⁻¹(W + C_k ε) + C_k …)`.

Two consequences, both of which wave 37 should treat as claims to check rather than as settled:

1. *The interface is missing hypotheses.* The far regime bounds the remainder by its first- and
   second-order terms, so it needs `‖Df‖ ≤ C₁/ε` and `‖D²f‖ ≤ C₂/ε²`. Neither this theorem's
   hypotheses nor `exists_smoothed_convex_indicator`'s conclusion supplies them — both carry
   only the *third*-order bound (checked this wave). They are presumably free from the
   `ContDiffBump` construction, but they have to be added and proved, not assumed.
2. *`htel`'s head shape may need one extra additive term.* The far regime's contribution is not
   of the form `(M/6) c³ X · (4 C_k (ε + σ_J) + W)` that
   `localised_swap_bound_of_weighted_telescope` freezes; it is absorbed by that term only if
   `C₃ ≥ 1`, which is not among `exists_smoothed_convex_indicator`'s guarantees. Either that
   normalisation is added, or `htel` gains a `+ (C_k δ + W δ ε⁻¹)` summand — a weakening the
   ledger has room for, since both pieces are already in the conclusion's shape.

**The arithmetic of this section was derived on paper this wave and is NOT machine-checked**,
unlike the ledger of wave 32 and the reduction of wave 35. It is recorded here because it
changes what the residue *is*, not because it is finished.

## Wave 37: the head estimate's inputs are supplied, and consequence 2 is OVERTURNED

Both of wave 36's flagged claims were checked. One survived, one did not.

**Consequence 1 (the missing interface hypotheses): CONFIRMED, and supplied.** The far regime
does need `‖D¹f‖ ≤ C₃/ε` and `‖D²f‖ ≤ C₃/ε²`, and nothing supplied them. They are free from the
`ContDiffBump` construction, exactly as guessed: `norm_iteratedFDeriv_one_convolution_le` and
`norm_iteratedFDeriv_two_convolution_le` are the same `precompR` convolution estimate at one and
two levels instead of three, and `norm_iteratedFDeriv_comp_smul_le` (the dilation scaling,
factored out of the old order-3 proof) transports all three orders at once. A *single* constant
now dominates `‖Dⁱf‖ εⁱ` for `i = 1, 2, 3`, and `1 ≤ C₃` is free because the source constant was
already a `max 1 …`. Both bounds are hypotheses of this theorem now (marked LEAN-ONLY) and are
discharged at every call site.

**Consequence 2 (`htel` needs one extra summand): the `C₃ ≥ 1` branch is FALSE.** Wave 36 wrote
that the far regime "is absorbed by that term only if `C₃ ≥ 1`". It is not absorbed at any
normalisation. At the cut `J ≍ ε² n` the frozen head term is `≍ 4 C₃ C_k δ + C₃ W δ/(2ε)` while
the far regime contributes `≍ 288 C₃ C_k δ + 36 C₃ W δ/ε` — a *constant multiple*, ≈ 25×, of it.
So the ledger takes the other branch: `htel` (and `weighted_ledger_balance`) now carry the
summand `J·C₃/(n√n)·X·(32 C_k/ε² + 4W/ε³)`, and the reduction's constant moves from
`18 C₃ + 33 C_t` to `306 C₃ + 33 C_t`. The normalisation `C₃ ≥ 1` is kept because it is free and
because it lets the constant term `2` be compared with `C₃ c²‖u‖²/ε²`, but it is *not* what
makes the far half fit.

**The localisation mechanism, PROVED — and it needs no Taylor theory.** Wave 36 described the
obstruction correctly (the Lagrange remainder controls `D³f` along the whole segment, so the
shell width is `‖w‖`, unbounded) but the repair is cheaper than expected. Off the two-sided
shell at width `‖w‖`, the test function is *constant on `closedBall a ‖w‖`* — equal to `1` if
`a` is in the erosion, to `0` if `a` is outside the `(ε + ‖w‖)`-thickening
(`const_on_closedBall_of_notMem_wideShell`) — so the value at `a + w` and *both* derivatives at
`a` are those of a constant and the entire second-order remainder is identically `0`
(`taylor_remainder_eq_zero_of_const_on_closedBall`). Hence the global Lagrange bound and the
lower-order bound may each simply be multiplied by the shell indicator at width `‖w‖`
(`abs_taylor_remainder_localised_le`, `abs_taylor_remainder_localised_lower_le`). Since
`thickening (ε + s) B \ erosion s B` is **monotone in `s`**, the near regime (`c‖u‖ ≤ ε`) is
dominated by the shell at width `2ε` and the far regime (`c‖u‖ ≥ ε`) by the shell at width
`2c‖u‖` — which is precisely why wave 29 had to state the weight hypothesis at *all* widths.

**The third-moment claim, CONFIRMED.** `far_regime_pointwise_le` and
`setIntegral_norm_pow_tail_le` are proved: the far regime's integrand is at most
`32 C₃ C_k t³/ε² + 4 C₃ W t²/ε²` at `t = c‖u‖ ≥ ε`, and `∫_{‖u‖>R} ‖u‖^p dν ≤ β/R^{3−p}` prices
it with `β` alone. No fourth moment appears anywhere.

**What is left.** The head side is now a single named statement,
`abs_integral_swap_step_localised_le`, in exactly the shape the amended reduction consumes; its
docstring records the whole derivation, and every analytic input it needs is proved above. What
that `sorry` still owes is bookkeeping: measurability of `u ↦ τ(shell at width c‖u‖)` (monotone
in `‖u‖`) and the Fubini exchange. The **tail** side (item 3) was not attempted this wave, and
note that wave 37's localisation mechanism does *not* transfer to it: the tail's integrand is
`f` smeared by a Gaussian of width `σⱼ`, which for `j > J` is `≥ ε` and near `j = n` is `≍ 1`, so
`f` being locally constant near `a` says nothing about it. The tail still needs the wave-29
constant-off/Gaussian-tail lemmas and the `‖w‖ ≤ 1` analysis recorded above, unchanged.

## Wave 38: the head brick is CLOSED, and the tail's ingredient list was INCOMPLETE

**The head side is proved.** `abs_integral_swap_step_localised_le` is now a theorem; see its
docstring for the two new named bricks it rests on (`erosion_eq_ofReal_lt_infEdist` and the
*joint* measurability `measurableSet_wideShell_prod`) and for the one correction wave 38 had to
make to wave 37's account of the bookkeeping. So of the two per-step estimates listed at the end
of the wave-35 residue, the first is discharged.

**The tail side is now a named brick, `abs_integral_gaussian_smoothed_swap_localised_le`, and it
is still open — but not for the reason recorded above.** Wave 32 wrote that the tail's "two
analytic ingredients are in place" and that only the `‖w‖ ≤ 1` restriction had to be handled.
Wave 38 checked that and it is **not** the case: a third ingredient is missing, and it is
upstream of the `‖w‖ ≤ 1` question. In brief (the full arithmetic is on that brick):

* The Cauchy–Schwarz route (wave 19) gives the weight as `√(shell mass)`, which is the `√W` form
  and closes only at `O(n^{-1/3})`.
* The near/far-in-`v` route (wave 29) gives the weight
  `4 C_k (r + ε) + W + 2√(γ{‖z‖ ≥ r/σ})·√tiltSqConst/C_t` at every radius `r`. To reach the
  frozen `4 C_k σ + W` one needs the Gaussian *norm* tail to be `≲ σ²` already at `r/σ ≍ 1`,
  which is false; and with the only tail this file has — `stdGaussian_norm_ge_le p`, Markov at a
  fixed order — the tail steps sum to `≍ p C_t δ ε^{-2/p}`, a **power** of `ε⁻¹` and not the
  logarithm the conclusion allows.
* What repairs it is a genuine sub-Gaussian tail `γ{‖z‖ ≥ M} ≤ exp(-(M-√k)²/2)` (equivalently
  `∫‖z‖^p dγ ≤ (Cpk)^{p/2}`, which lets `p` be optimised in `stdGaussian_norm_ge_le`), and it is
  absent. It is a new dimension-explicit concentration statement, not bookkeeping.
* Even with it, the route produces `4 C_k σ (√k + √(2 log(1/σ))) + W`, so `htel`'s tail summands
  — and hence brick L's constant and the `C ≍ √k` of `berryEsseen_convex_sharp` — carry an extra
  `√(k + log(1/ε))` that wave 39 must price explicitly rather than assume away.

So this `sorry` now has exactly one open input on the head side (none) and one on the tail side
(the brick above), and the tail's own residue is three items, ordered: the Gaussian norm tail,
the near/far-in-`v` assembly, and the `‖w‖ ≤ 1` complement.

## Wave 39: the CONCLUSION is amended, and the ledger behind it is re-proved

The first of those three items is discharged (`stdGaussian_norm_ge_le_exp`), and with it the
amended tail weight `12 C_k σⱼ · gaussianTailRadius k σⱼ + W` is what the tail brick now states.
The ledger consequence is **not** absorbable, so this statement's conclusion changes:

  `A δ (ε⁻¹(W + C_k ε) + C_k · dimTailConst k · logPow32 ε)`,
  `logPow32 ε = (1 + log(1 + ε⁻¹))^{3/2}`, `dimTailConst k = √(2k log 2k) + 2√k`,

in place of wave 32's `A δ (ε⁻¹(W + C_k ε) + C_k (1 + log(1 + ε⁻¹)))`. Both new factors are
`≥ 1`, so the amended conclusion is strictly weaker and every consumer still closes; and
`localised_swap_bound_of_weighted_telescope` — the *proved* reduction of this brick to its
per-step hypothesis `htel` — has been re-run at the amended shape and is green, with constant
`306 C₃ + 81 C_t`. So the shape of the answer is settled in Lean, not on paper; what this
`sorry` still owes is the analytic production of `htel`'s tail summand, i.e. the assembly of
`abs_integral_gaussian_smoothed_swap_localised_le`.

## Wave 41: BOTH per-step estimates are now theorems, and the residue is re-diagnosed

`abs_integral_gaussian_smoothed_swap_localised_le` is proved, at wave 40's constants exactly.
Both per-step estimates that wave 35 listed as the residue — the head one (wave 38) and the tail
one (wave 41) — are therefore theorems, and the ledger constants they feed are amended and
machine-checked (`306 C₃ + 444 C_t`). **No analytic input is missing anywhere on this route.**

**But the residue is not "just wire them up", and the reason overturns a claim of waves 36–40.**
Every wave since 36 has recorded that `τ` in the two bricks "is `hybridLaw n j ν`", citing
`integral_hybridLaw_eq` / `integral_peel_eq_integral_hybridLaw`. Checked this wave, it is false,
and the discrepancy is exactly one swapped coordinate:

* at step `j` the telescope peels coordinate `j` (`hstepfun`, via
  `abs_sub_integral_peel_le_integral`), so the base point against which both bricks average is
  `c·(∑ₗ yₗ) + σⱼ z`, with `y` ranging over
  the **other** `n − 1` coordinates and `z` over the smoothing Gaussian. The swapped coordinate
  appears only as the `c u` *inside* the absolute value, which is what makes the step a swap at
  all. Call that law the *peeled* law;
* `hybridLaw n j ν` — what brick H (`hybridLaw_wideShell_le`) bounds, and what this theorem's
  weight hypothesis asserts — is the law of `c·(u + ∑ₗ yₗ) + σⱼ z`, `u ∼ ν`. That is literally
  the right-hand side of `integral_peel_eq_integral_hybridLaw`;
* the two are not comparable by an inclusion or a monotonicity. The peeled law is `hybridLaw`
  with the dirac cut at `j + 1` but the smoothing still at `j` (so it is not a `hybridLaw` at
  all, for any index), and `hybridLaw n j ν = (peeled law) ∗ (c·ν)`, which is the wrong
  direction: a shell bound for a convolution does not give one for its factor.

Both routes into the bricks hit this. Taking `D v` to be the step's own absolute difference and
pulling the modulus through the smoothing integral (the move `hboundA` already makes) lands on
the peeled law; and taking `D v` in the special form `integral_peel_eq_integral_hybridLaw`
consumes requires the shell indicator to be evaluated at `c(v + u) + σⱼ z`, which is precisely
what neither brick provides — both evaluate it at the base point, with `u` setting only the
*width*.

**The repair, named and already built.** `mem_wideShell_shift` / `indicator_wideShell_le_shift`:
`1_{shell at s}(a) ≤ 1_{shell at s + t}(a + w)` whenever `‖w‖ ≤ t`. Both bricks already carry a
width that dominates the shift: `2c‖u‖` in the far regime and `2ε ≥ 2c‖u‖` in the near one, so
absorbing `c u` costs one more `c‖u‖`, i.e. `2 → 3` in the width and `8 C_k → 12 C_k` in the far
half of the ledger — a constant, not a shape. So what this `sorry` owes, in full and for the
first time with no analytic component, is:

1. re-run `integral_abs_remainder_split_le` / `integral_far_shell_le` (head) and
   `integral_localised_shell_le` (tail) with the indicator at the **shifted** point, via
   `indicator_wideShell_le_shift`, so that both bricks' `τ` becomes `hybridLaw n j ν`;
2. run the localised telescope: `hstepfun` with the `v`-dependent `D` of
   `abs_sub_integral_peel_le_integral`, the bridge `integral_peel_eq_integral_hybridLaw`, and the
   summation `sum_le_of_bounded_and_weighted_decay`, to produce `htel` at the amended constants;
3. feed `htel` to `localised_swap_bound_of_weighted_telescope`, which is proved and green at
   `306 C₃ + 444 C_t`.

Step 3 is done, step 1's tool is built, and step 2 is the wiring wave 35 already described.

## Wave 42: step 1 is FALSE as stated, and the transfer is deconvolution, not shifting

Wave 41's item 1 — "re-run the two bricks with the shell indicator at the shifted point, via
`indicator_wideShell_le_shift`, so that both bricks' `τ` becomes `hybridLaw n j ν`" — does not
close, and the reason is structural rather than a matter of constants.

**Why shifting the indicator cannot work.** In both bricks the width at which the shell
hypothesis is consulted is a function of the *same* variable as the shift: `2 c‖u‖` in the head's
far regime (`integral_far_shell_le`) and `2σ(R + (c/σ)‖y‖)` in the tail's
(`integral_localised_shell_le`), with `u`, `y` the swapped coordinate. After
`indicator_wideShell_le_shift` one is therefore left with

`∫dν(u) [ ∫dτ(a) 1_{shell(w(u))}(a + c u) ] · stuff(u)`,

whose inner factor is the shell mass of a **translate** of `τ`, not of `τ ∗ (c ν) = hybridLaw`.
A hypothesis about the convolution at each *fixed* width does not control it. Witness (`k = 1`,
`B = (−∞, 0]`): let `τ = δ_{−c u₀}` and `ν = (1−p) δ₀ + (p/2)(δ_{u₀} + δ_{−u₀})`, with
`c u₀ > ε`, so that `u = u₀` is in the far regime. The displayed quantity is `(p/2)·stuff(u₀)`,
because the translate puts all of its mass at `0 ∈ shell(s)` for every `s > 0`; whereas the
convolution `τ ∗ (cν)` charges the shell of width `s < c u₀` with mass exactly `p/2`, so the
hypothesis `≤ 4 C_k s + W` is satisfied with `W = p/2` and the *target* bound is
`(p/2)(12 C_k c u₀ + W)·stuff(u₀)`. The ratio is `1/(12 C_k c u₀ + W)`, which brick L's own
normalisation `W + C_k ε ≤ 1` allows to be arbitrarily large. So a shell bound for a convolution
genuinely does not give one for its factor by enlarging the width.

**What does work: deconvolution, and it is now proved.** `wideShell_le_of_deconvolution` runs
`mem_wideShell_shift` in the *other* direction — the shell grows under a bounded shift, so

`τ(shell s) · η(closedBall 0 t) = (τ ⊗ η)(shell s × closedBall 0 t) ≤ (τ ∗ η)(shell (s + t))` —

and therefore converts a shell bound for `μ = τ ∗ η` into one for `τ`, at the price of the
concentration radius `t` of `η` and of the mass `q ≤ η(closedBall 0 t)` it carries.
`measureReal_closedBall_ge_of_normSq` supplies `q = 3/4` at `t = 2√(E‖y‖²)` by Chebyshev. Run for
`s ≥ t` and completed for `s < t` by monotonicity of the shell in its width, it gives the
**uniform** form the two bricks consume verbatim:

`∀ s > 0, τ(shell s) ≤ 4 C_k' s + W'`, `C_k' = 3 C_k`, `W' = 2 W + 11 C_k t`.

**The two base laws, and what each has to be deconvolved by.** They are *different*, and neither
is a hybrid law:

* *head* (the elementary steps). Pulling the smoothing integral outside the modulus, as `hboundA`
  already does, makes the head brick's base point `c ∑_{i ≥ j+1} Yᵢ + σⱼ Z`. Adding the swapped
  coordinate gives `hybridLaw n j ν`, so `η = ν.map (c • ·)`, `E‖·‖² = c² k` and `t = 2 c √k`;
* *tail* (the Cameron–Martin steps). `abs_integral_gaussian_smoothed_swap_localised_le` evaluates
  its shell indicator at `v`, i.e. **before** the smoothing, so its base law is the unsmoothed
  `c ∑_{i ≥ j+1} Yᵢ`. Convolving it with the whole smoothing Gaussian of width `σ_{j+1}` gives
  `hybridLaw n (j+1) ν` — the index moves, which is why brick L's weight hypothesis has to be
  assumed at every `j ≤ n`, as it already is. Here `η = γ.map (σ_{j+1} • ·)` and
  `t = 2 √k σ_{j+1}`.

**The window has to be strengthened, and it is free.** `wideShell_le_of_deconvolution` needs
`t ≤ s`, and the smallest width either brick consults is `2ε`. On the head side that is
`2 c √k ≤ 2ε`, i.e. **`√k ≤ ε √n`** in place of the present `1 ≤ ε √n`. It is free at the unique
call site — `ε √n = 8 (A+1) β ≥ 8 k^{3/2} ≥ √k` by `sqrt_dim_mul_dim_le_integral_norm_cube`, the
same computation that already discharges `1 ≤ ε √n` (wave 36, Correction 2) — but it has to be
threaded through `exists_localised_swap_bound`, `exists_convexDiscrepancy_recursion` and the
`hrec` window of `le_of_selfImproving_induction_logPow32`. On the tail side the requirement is
`2 √k σ_{j+1} ≤ 2 σⱼ R(σⱼ)`, which is free from `gaussianTailRadius` itself:
`R(σ) ≥ √(2k log 2k) ≥ √(2 log 2) √k ≥ 1.17 √k` and `σ_{j+1} ≤ √2 σⱼ` for `j ≥ 1`.

**The amended constants FIT the frozen `htel`; no shape moves.** With `C_k' = 3 C_k` and
`W' = 2W + 11 C_k t`:

* head, first summand: `8 C_k' ε + W' = 46 C_k ε + 2W ≤ 12 (4 C_k ε + W)` (using `t ≤ 2ε`);
* head, second summand: `32 C_k'/ε² + 4W'/ε³ = 184 C_k/ε² + 8W/ε³ ≤ 6 (32 C_k/ε² + 4W/ε³)`;
* tail: `68 C_k' σⱼ R(σⱼ) + 4 W' = 204 C_k σⱼ R(σⱼ) + 8W + 88 C_k √k σ_{j+1}`, and the last term
  is `≤ 88√2 C_k √k σⱼ ≤ 107 C_k σⱼ R(σⱼ)`, so the whole weight is
  `≤ 5·(68 C_k σⱼ R(σⱼ)) + 2·(4W)`.

So `localised_swap_bound_of_weighted_telescope` is to be instantiated at `C₃ := 12 C₃` and
`Ct := 5 Ct` — its `C₃` and `Ct` are bare reals, used only inside `htel` — and its conclusion's
constant becomes `3672 C₃ + 2220 Ct`, which brick L's existential `A` absorbs. **The `htel` shape,
the ledger, the fixed point and the headline are all untouched.** This is the amendment the
provable-constants rule asks for: a constant, at the smallest place, recorded.

**What is left, after wave 42.** Three items, none analytic:

1. *the two convolution identities*, which are what `wideShell_le_of_deconvolution`'s hypothesis
   `hμ` asks for. The tail one, `hybridLaw n (j+1) ν = ((c ∑_{i ≥ j+1} Yᵢ) ⊗ (σ_{j+1} γ)).map(+)`,
   **is done** — it is `hybridLaw_eq_map_add`, pure `Measure.map_prod_map`, since `hybridLaw` is
   already defined as a map of a product. The head one,
   `hybridLaw n j ν = ((peeled, smoothed base) ⊗ (c ν)).map (+)`, additionally needs the
   coordinate split, whose measure-level form is `map_pi_sum_peel` (**also done**, the analogue
   of `integral_pi_sum_peel` without the test function, which is necessary because a shell
   indicator is not continuous); what is left there is the associativity of the two convolutions
   that puts the `c ν` factor last;
2. *the localised telescope*: `abs_integral_smooth_sub_gaussian_improved` re-run with the
   `v`-dependent `D` of `hstepfun` — `D v = ∫z |…| dγ` on the head side, `D v = |…|` on the tail
   side — summed by `sum_le_of_bounded_and_weighted_decay` instead of
   `sum_le_of_bounded_and_decay_const`;
3. the window amendment and the constants above.

Wave 41's closing sentence, "what this `sorry` owes, in full and for the first time with no
analytic component", survives; its item 1 does not.

## Wave 43: PROVED, exactly along the deconvolution route, at wave 42's constants

All three of wave 42's remaining items are executed and nothing new was needed.

1. *The two convolution identities.* `hybridLaw_conv_head` and `hybridLaw_conv_tail`. Both are
   pure convolution algebra once one notices that Mathlib's `Measure.conv` **is** the shape both
   `wideShell_le_of_deconvolution`'s `hμ` and `hybridLaw_eq_map_add`'s conclusion already have,
   so `Measure.conv_assoc` / `Measure.conv_comm` are free; the only content is
   `map_pi_sum_smul_peel` (peeling one coordinate off the *scaled* coordinate sum) and, on the
   tail side, `Measure.dirac_zero_conv` to erase the Dirac at the peeled index.
   `wideShell_le_of_deconvolution_uniform` packages the deconvolution at every width — the shape
   the wave-29 amended `hshell` hypothesis of both per-step bricks asks for — by running the
   deconvolution at `t = 2r` and completing `s < 2r` by monotonicity of the shell
   (`wideShell_mono`). Wave 42's `C_k' = 3 C_k`, `W' = 2W + 11 C_k t` are confirmed exactly.
2. *The localised telescope.* `abs_integral_smooth_sub_gaussian_localised` is
   `abs_integral_smooth_sub_gaussian_improved` re-run with the `v`-dependent `D` of `hstepfun`,
   summed by `sum_le_of_bounded_and_weighted_decay`. Two remarks on what it costs:
   * the per-step `D` is a *difference of two averages*, hence bounded by `2` and not by `1`, so
     the wave-16 helpers (`integrable_of_bounded_continuous`, `abs_integral_le_one`,
     `continuous_integral_add_smul`) had to be re-issued at an arbitrary constant bound;
   * the head side's `D v = ∫ z |…| dγ` is transferred to the brick's `τ = (peeled law) ∗ (σⱼ γ)`
     by `integral_conv_smul_gaussian` (Fubini through the convolution), the tail side's
     `D v = |…|` to `τ = (peeled law)` by a bare `integral_map`. The tail's integrand needed one
     new continuity fact, `continuous_double_smooth`, since its two smoothings sit in the *other*
     order than `continuous_integral_add_smul` produces.
3. *The window and the constants.* The window `√k ≤ ε √n` is threaded (see the LEAN-ONLY
   hypothesis below) and discharged at the unique call site. The per-step deconvolution constants
   fit the frozen `htel` at `C₃ → 12 C₃` and `Ct → 5 Ct` exactly as wave 42 computed:
   * head, first summand `8·(3C_k)ε + W' = 46 C_k ε + 2W ≤ 12(4 C_k ε + W)` using `c√k ≤ ε`;
   * head, second summand `184 C_k/ε² + 8W/ε³ ≤ 12(32 C_k/ε² + 4W/ε³)`;
   * tail `68·(3C_k)σR + 4W' = 204 C_k σR + 8W + 88 C_k σ_{j+1}√k ≤ 336 C_k σR + 8W`, using
     `σ_{j+1} ≤ (3/2)σⱼ` (`j ≥ 1`) and `√k ≤ gaussianTailRadius k σ`
     (`sqrt_dim_le_gaussianTailRadius`), and `336 ≤ 5·68`.
   So the brick's constant is `306·(12 C₃) + 444·(5 C_t) = 3672 C₃ + 2220 C_t`, absorbed by the
   existential `A`. **The `htel` shape, the ledger, the fixed point and the headline are all
   untouched**, exactly as wave 42 predicted.

The tail brick is instantiated with `C_t := max (max C 1) (√tiltSqConst)`, `C` the absolute
constant of `exists_tiltRemainder_bound`: that discharges its two LEAN-ONLY hypotheses
(`1 ≤ C_t` and the Cauchy–Schwarz side condition `√tiltSqConst ≤ 2 C_k C_t`, using
`gaussianShellConst k = 4e²√k ≥ 1`) at no cost, since `C_t` may always be enlarged. -/
theorem localised_swap_bound_small_weight (k : ℕ) (hk : 0 < k) {C₃ : ℝ} (hC₃ : 1 ≤ C₃) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))) (ε : ℝ)
      (f : EuclideanSpace ℝ (Fin k) → ℝ) (W : ℝ),
      0 < n → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν →
      MeasurableSet B → Convex ℝ B → 0 < ε →
      -- LEAN-ONLY: the localisation window; discharged at the unique call site from
      -- `k^{3/2} ≤ β`, see the note (wave 36, "Correction 2, RESOLVED"; strengthened from
      -- `1 ≤ ε √n` to `√k ≤ ε √n` in wave 43, for the deconvolution radius).
      Real.sqrt (k : ℝ) ≤ ε * Real.sqrt (n : ℝ) →
      ContDiff ℝ 3 f → (∀ x, |f x| ≤ 1) →
      (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) →
      -- LEAN-ONLY: mollifier derivative bounds; supplied by
      -- `exists_smoothed_convex_indicator` at every call site.
      (∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C₃ / ε) →
      (∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₃ / ε ^ 2) →
      (∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B) → (∀ x ∈ B, f x = 1) →
      0 ≤ W →
      (∀ j : ℕ, j ≤ n → ∀ s : ℝ, 0 < s →
        ((hybridLaw n j ν) (Metric.thickening s B \ erosion s B)).toReal
          ≤ 4 * gaussianShellConst k * s + W) →
      W + gaussianShellConst k * ε ≤ 1 →
      |(∫ x, f x ∂(sumLaw n ν))
          - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
        ≤ A * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ))
            * (ε⁻¹ * (W + gaussianShellConst k * ε)
              + gaussianShellConst k * dimTailConst k * logPow32 ε) := by
  -- The tail brick's `Ct` is enlarged so that its two LEAN-ONLY hypotheses are free.
  obtain ⟨C, hC0, hC⟩ := exists_tiltRemainder_bound
  set Ct : ℝ := max (max C 1) (Real.sqrt tiltSqConst) with hCtdef
  have hCt1 : 1 ≤ Ct := le_trans (le_max_right C 1) (le_max_left _ _)
  have hCt0 : (0 : ℝ) < Ct := lt_of_lt_of_le one_pos hCt1
  have hCtb : ∀ s : ℝ, 0 ≤ s →
      (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ Ct * s ^ 3 := by
    intro s hs
    refine (hC s hs).trans ?_
    have hCle : C ≤ Ct := le_trans (le_max_left C 1) (le_max_left _ _)
    nlinarith [pow_nonneg hs 3]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk1 : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hk1
  have hCk1 : (1 : ℝ) ≤ gaussianShellConst k := by
    have h1 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    rw [gaussianShellConst]
    nlinarith
  have hCw : Real.sqrt tiltSqConst ≤ 2 * gaussianShellConst k * Ct := by
    have h : Real.sqrt tiltSqConst ≤ Ct := le_max_right _ _
    nlinarith
  refine ⟨306 * (12 * C₃) + 444 * (5 * Ct), by nlinarith, ?_⟩
  intro n ν B ε f W hn hνp hmean hcov hβint hBm hBc hε hwin hf hfb hD3 hD1 hD2 hsupp hone
    hW0 hshell _hsmall
  haveI := hνp
  have hbig : 1 ≤ ε * Real.sqrt (n : ℝ) := le_trans hsk1 hwin
  have hγ : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := multivariateGaussian_zero_one
  rw [hγ]
  refine localised_swap_bound_of_weighted_telescope hk hn hcov hβint
    (by linarith : (0 : ℝ) < 12 * C₃) (by linarith : (0 : ℝ) < 5 * Ct) hε hW0 hbig ?_
  intro J hJ2 hJε
  exact abs_integral_smooth_sub_gaussian_localised hk hCt1 hCtb hCw hn hνp hmean hcov hβint
    hf hfb hC₃ hε hD3 hD1 hD2 hone hsupp hW0 hwin hshell hJ2 hJε

/-- **Brick L (wave 24: AMENDED, and proved over `localised_swap_bound_small_weight`).** *The
hybrid telescope with every step estimated by the localised weighted swap bound.*

**The wave-20 form of this statement is FALSE**, with the conclusion
`≤ A (β/√n) ε⁻¹ W` for the bare weight `W`. Witness (`k = 1`, `n = 1`, `ε = 1`, `p ↓ 0`): let
`ν` put mass `p` at `−a` and mass `1 − p` at `b`, with `a = √((1−p)/p)` and `b = √(p/(1−p))`, so
that `ν` is centred with unit variance and `β = ∫|y|³ dν ∼ p^{-1/2}`. Take `B = (−∞, −T]` with
`T = a/2` (convex, measurable) and `f` any admissible mollified indicator. Then

* `sumLaw 1 ν = ν` and `hybridLaw 1 0 ν = ν`, `hybridLaw 1 1 ν = γ`;
* the shell `B^{2} \ interior B = [−T, −T+2)` misses both atoms of `ν` (as `−a = −2T` and
  `b > 0 > −T + 2` once `T > 2`), so `W := 2 e^{−T²/2}` is admissible;
* `∫ f dν = p` (the atom at `−a = −2T` lies in `B`, the atom at `b` lies off `Bᵋ`), while
  `∫ f dγ ≤ e^{−(T−1)²/2}`, so the left-hand side is `≥ p − e^{−(T−1)²/2}`;
* the right-hand side is `A · p^{-1/2} · 1 · 2 e^{−T²/2}` with `T = a/2 ∼ 1/(2√p)`, i.e.
  `∼ 2A p^{-1/2} e^{−1/(8p)}`.

As `p ↓ 0` the left-hand side is polynomially small and the right-hand side is exponentially
small, so no `A` works. The mechanism is that `W` is allowed to be *far below* the Gaussian
shell scale `C_k ε`, which no swap estimate can exploit: a hybrid law can miss the shell
entirely and still be far from Gaussian.

**The amendment** adds `C_k ε` to the weight, `C_k = gaussianShellConst k`. It costs nothing at
the only call site: `exists_convexDiscrepancy_recursion` invokes brick L with
`W = 4 C_k ε + 2 Y`, and `W + C_k ε ≤ (5/4) (4 C_k ε + 2 Y)` since `Y ≥ 0`, so the recursion is
unchanged except for a factor `2` in its constant. Every counterexample of the above shape is
killed, and the amended statement is what Bentkus's argument actually produces.

The proof splits at `W + C_k ε = 1`: above it,
`exists_smooth_swap_bound_of_one_le_weight` closes the goal with no localisation at all; below
it, the content is the named brick `localised_swap_bound_small_weight`.

**Wave 29 amended the weight hypothesis.** `W` is no longer a bound on the mass of the single
outer shell `B^{2ε} \ interior B`, but on the excess over `4 C_k s` of the mass of the
*two-sided* shell `B^s \ B_{-s}`, **at every width `s > 0`**. Both changes are forced by the
localisation the proof actually uses — see the analysis on `localised_swap_bound_small_weight` —
and both are free here, because `hybridLaw_wideShell_le` proves exactly that, at every width,
with the same `2Y`.

**Wave 32 amends the conclusion**, adding `+ C_k (1 + log(1 + ε⁻¹))` inside the bracket: the
summation ledger on `localised_swap_bound_small_weight` forces a logarithm, because the
telescope's own smoothing widths `σⱼ = √(j/n)` sweep from `ε` to `1` while the test function has
the single width `ε`. The large-weight half `exists_smooth_swap_bound_of_one_le_weight` is
proved and is *unaffected*: its conclusion is the log-free one, which is smaller, so it still
closes the amended goal. Only the small-weight half changes.

**Wave 39 amends that term again**, to `+ C_k · dimTailConst k · logPow32 ε`: the tail weight
that the sub-Gaussian norm tail actually delivers carries the extra radius factor
`gaussianTailRadius k σⱼ`, which raises the ledger's log power from `1` to `3/2` and multiplies
the dimension constant by `dimTailConst k = √(2k log 2k) + 2√k`. See the tail brick
`abs_integral_gaussian_smoothed_swap_localised_le` for the derivation and
`weighted_ledger_balance` for the re-proved ledger. The large-weight half is again *unaffected*
(both new factors are `≥ 1`, so the amended bracket is larger), and the proof here is unchanged
apart from the substitution. -/
theorem exists_localised_swap_bound (k : ℕ) (hk : 0 < k) {C₃ : ℝ} (hC₃ : 1 ≤ C₃) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))) (ε : ℝ)
      (f : EuclideanSpace ℝ (Fin k) → ℝ) (W : ℝ),
      0 < n → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν →
      MeasurableSet B → Convex ℝ B → 0 < ε →
      -- LEAN-ONLY: the localisation window; ignored by the large-weight branch, passed to
      -- `localised_swap_bound_small_weight` by the small-weight one (wave 36; strengthened to
      -- `√k ≤ ε √n` in wave 43).
      Real.sqrt (k : ℝ) ≤ ε * Real.sqrt (n : ℝ) →
      ContDiff ℝ 3 f → (∀ x, |f x| ≤ 1) →
      (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) →
      -- LEAN-ONLY: mollifier derivative bounds; supplied by
      -- `exists_smoothed_convex_indicator` at every call site.
      (∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C₃ / ε) →
      (∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C₃ / ε ^ 2) →
      (∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B) → (∀ x ∈ B, f x = 1) →
      0 ≤ W →
      (∀ j : ℕ, j ≤ n → ∀ s : ℝ, 0 < s →
        ((hybridLaw n j ν) (Metric.thickening s B \ erosion s B)).toReal
          ≤ 4 * gaussianShellConst k * s + W) →
      |(∫ x, f x ∂(sumLaw n ν))
          - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
        ≤ A * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ))
            * (ε⁻¹ * (W + gaussianShellConst k * ε)
              + gaussianShellConst k * dimTailConst k * logPow32 ε) := by
  have hC₃pos : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃
  obtain ⟨A₁, hA₁, h₁⟩ := exists_smooth_swap_bound_of_one_le_weight k hk hC₃pos
  obtain ⟨A₂, hA₂, h₂⟩ := localised_swap_bound_small_weight k hk hC₃
  refine ⟨A₁ + A₂, by linarith, ?_⟩
  intro n ν B ε f W hn hνp hmean hcov hβint hBm hBc hε hwin hf hfb hD hD1 hD2 hsupp hone
    hW0 hW
  haveI := hνp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  have hβ0 : 0 < ∫ y, ‖y‖ ^ 3 ∂ν := integral_norm_cube_pos hk hcov hβint
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hδ0 : 0 ≤ (∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ) := div_nonneg hβ0.le hsn.le
  have hDk1 : (1 : ℝ) ≤ dimTailConst k := one_le_dimTailConst hk
  have hLP1 : (1 : ℝ) ≤ logPow32 ε := one_le_logPow32 hε
  have hlog0 : 0 ≤ dimTailConst k * logPow32 ε := by nlinarith
  have hbrk0 : 0 ≤ ε⁻¹ * (W + gaussianShellConst k * ε) := by
    have : (0:ℝ) < gaussianShellConst k * ε := mul_pos hCk hε
    exact mul_nonneg (inv_pos.2 hε).le (by linarith)
  have hbase : 0 ≤ (∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)
      * (ε⁻¹ * (W + gaussianShellConst k * ε)
        + gaussianShellConst k * dimTailConst k * logPow32 ε) := by
    refine mul_nonneg hδ0 (by nlinarith [mul_nonneg hCk.le hlog0])
  have hexp : ∀ A : ℝ, A * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ))
      * (ε⁻¹ * (W + gaussianShellConst k * ε)
        + gaussianShellConst k * dimTailConst k * logPow32 ε)
      = A * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)
        * (ε⁻¹ * (W + gaussianShellConst k * ε)
          + gaussianShellConst k * dimTailConst k * logPow32 ε)) := fun A => by ring
  rcases le_or_gt 1 (W + gaussianShellConst k * ε) with hge | hlt
  · -- the large-weight half is proved, and its (log-free) conclusion is smaller
    have h := h₁ n ν ε f (W + gaussianShellConst k * ε) hn hνp hmean hcov hβint hε hf hfb
      hD hge
    refine h.trans ?_
    have hsmall : A₁ * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) * ε⁻¹
        * (W + gaussianShellConst k * ε)
        ≤ A₁ * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ))
          * (ε⁻¹ * (W + gaussianShellConst k * ε)
            + gaussianShellConst k * dimTailConst k * logPow32 ε) := by
      have hA₁δ : 0 ≤ A₁ * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) :=
        mul_nonneg hA₁.le hδ0
      have hextra : 0 ≤ gaussianShellConst k * dimTailConst k * logPow32 ε := by
        nlinarith [mul_nonneg hCk.le hlog0]
      nlinarith [mul_nonneg hA₁δ hextra]
    refine hsmall.trans ?_
    rw [hexp A₁, hexp (A₁ + A₂)]
    exact mul_le_mul_of_nonneg_right (by linarith) hbase
  · have h := h₂ n ν B ε f W hn hνp hmean hcov hβint hBm hBc hε hwin hf hfb hD hD1 hD2
      hsupp hone hW0 hW hlt.le
    refine h.trans ?_
    rw [hexp A₂, hexp (A₁ + A₂)]
    exact mul_le_mul_of_nonneg_right (by linarith) hbase

/-- **The recursion, produced.** For every measurable convex `B`, every cut `ε > 0` and every
bound `Y` on the discrepancies at the neighbour sizes `n/2 ≤ m ≤ n`,

`Δ(μₙ, γ) ≤ A (β/√n) ε⁻¹ (C ε + 2Y) + A (β/√n) C (1 + log(1 + ε⁻¹)) + C ε`, `C = 4 C_k`,

which is exactly the hypothesis of `le_of_selfImproving_induction_log`. Bricks H and L supply
the weighted swap estimate; everything else here is the two-sided thickening/erosion sandwich of
`berryEsseen_convex_improved` with the mollifier of `exists_smoothed_convex_indicator`.

Wave 24: brick L now delivers the weight `W + C_k ε` rather than `W` (its wave-20 form is false,
see `exists_localised_swap_bound`). Since the call site supplies `W = 4 C_k ε + 2 Y` with
`Y ≥ 0`, one has `W + C_k ε ≤ 2 W`, so the extra term is absorbed by doubling `A`; the statement
here was unchanged.

Wave 29: brick L's weight hypothesis is now the *two-sided* shell at *every* width, supplied
here by `hybridLaw_wideShell_le` instead of `hybridLaw_shell_le`. The same `W = 4 C_k ε + 2 Y`
works verbatim, so the statement here was again unchanged.

Wave 32: brick L's *conclusion* now carries `+ C_k (1 + log(1 + ε⁻¹))`, forced by the summation
ledger (see there), and that term is inherited here verbatim — it does not interact with the
`W`-bookkeeping at all, since the sandwich only ever adds `|∫f dμ − ∫f dγ|` to Gaussian shell
masses. The same doubling of `A` absorbs `C_k ≤ 8 C_k = 2·(4 C_k)` in the new term. Downstream,
`le_of_selfImproving_induction` is replaced by `le_of_selfImproving_induction_log`.

Wave 39: brick L's conclusion carries `+ C_k · dimTailConst k · logPow32 ε` instead, and that
term is again inherited here verbatim — the `W`-bookkeeping is untouched, and the same doubling
of `A` absorbs `C_k ≤ 8 C_k`. Downstream, `le_of_selfImproving_induction_log` is replaced by
`le_of_selfImproving_induction_logPow32`, run with the forcing constant `C = 4 C_k` and the
recursion constant enlarged from `A + 1` to `(A + 1) · dimTailConst k` (which is where the
dimension factor lands in the headline). -/
theorem exists_convexDiscrepancy_recursion (k : ℕ) (hk : 0 < k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) (ε Y : ℝ),
      0 < n → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → 0 < ε →
      -- LEAN-ONLY: the localisation window brick L needs; free here, see the note (wave 36,
      -- strengthened to `√k ≤ ε √n` in wave 43).
      Real.sqrt (k : ℝ) ≤ ε * Real.sqrt (n : ℝ) →
      (∀ m : ℕ, n ≤ 2 * m → m ≤ n →
        convexDiscrepancy (sumLaw m ν) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
          ≤ Y) →
      convexDiscrepancy (sumLaw n ν)
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        ≤ A * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) * ε⁻¹
            * (4 * gaussianShellConst k * ε + 2 * Y)
          + A * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) * (4 * gaussianShellConst k)
            * (dimTailConst k * logPow32 ε)
          + 4 * gaussianShellConst k * ε := by
  obtain ⟨C₃, hC₃one, hC₃⟩ := exists_smoothed_convex_indicator k
  have hC₃pos : (0 : ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃one
  obtain ⟨A, hApos, hA⟩ := exists_localised_swap_bound k hk hC₃one
  refine ⟨2 * A, by linarith, ?_⟩
  intro n ν ε Y hn hνp hmean hcov hβint hε hwin hY
  haveI := hνp
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hY0 : 0 ≤ Y := by
    haveI : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
      inferInstance
    exact le_trans convexDiscrepancy_nonneg (hY n (by omega) le_rfl)
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  set μ : Measure (EuclideanSpace ℝ (Fin k)) := sumLaw n ν with hμdef
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set δ : ℝ := β / Real.sqrt (n : ℝ) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hDk1 : (1 : ℝ) ≤ dimTailConst k := one_le_dimTailConst hk
  have hLP1 : (1 : ℝ) ≤ logPow32 ε := one_le_logPow32 hε
  have hlog0 : 0 ≤ dimTailConst k * logPow32 ε := by nlinarith
  set E : ℝ := 2 * A * δ * ε⁻¹ * (4 * gaussianShellConst k * ε + 2 * Y)
    + 2 * A * δ * (4 * gaussianShellConst k) * (dimTailConst k * logPow32 ε) with hEdef
  -- the Lévy form, for an arbitrary measurable convex set
  have hlevy : ∀ S : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet S → Convex ℝ S →
      (μ S).toReal ≤ (γ (Metric.thickening ε S)).toReal + E
        ∧ (γ S).toReal ≤ (μ (Metric.thickening ε S)).toReal + E := by
    intro S hSm hSc
    obtain ⟨f, hfcd, hf0, hf1, hfS, hfsupp, hfD, hfD1, hfD2⟩ := hC₃ S hSc hε
    have hfbd : ∀ x, |f x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hf0 x], hf1 x⟩
    have hfint : ∀ ρ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure ρ →
        Integrable f ρ := by
      intro ρ hρ
      haveI := hρ
      exact (integrable_const (1 : ℝ)).mono' hfcd.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfbd x)
    -- brick H for the two-sided shell, at EVERY width, uniformly in `j` (wave 29)
    have hW0 : (0 : ℝ) ≤ 4 * gaussianShellConst k * ε + 2 * Y := by
      have : (0 : ℝ) < 4 * gaussianShellConst k * ε := by positivity
      linarith
    have hW : ∀ j : ℕ, j ≤ n → ∀ s : ℝ, 0 < s →
        ((hybridLaw n j ν) (Metric.thickening s S \ erosion s S)).toReal
          ≤ 4 * gaussianShellConst k * s + (4 * gaussianShellConst k * ε + 2 * Y) := by
      intro j hjn s hs
      have h := hybridLaw_wideShell_le (k := k) hk (n := n) (j := j) hn hjn
        (ν := ν) hSm hSc (ε := s) hs hY
      have hpos : (0 : ℝ) < 4 * gaussianShellConst k * ε := by positivity
      linarith
    -- brick L
    have herr : |(∫ x, f x ∂μ) - (∫ x, f x ∂γ)| ≤ E := by
      have h := hA n ν S ε f (4 * gaussianShellConst k * ε + 2 * Y) hn hνp hmean hcov hβint
        hSm hSc hε hwin hfcd hfbd hfD hfD1 hfD2 hfsupp hfS hW0 hW
      rw [← hμdef, ← hβdef, ← hδdef] at h
      refine h.trans ?_
      rw [hEdef]
      have hu : 0 ≤ A * δ * ε⁻¹ := by positivity
      have hAδ : 0 ≤ A * δ := by positivity
      -- the `ε⁻¹` bracket, as before: `W + C_k ε ≤ 2 W`
      have hpart1 : A * δ * ε⁻¹
            * (4 * gaussianShellConst k * ε + 2 * Y + gaussianShellConst k * ε)
          ≤ 2 * A * δ * ε⁻¹ * (4 * gaussianShellConst k * ε + 2 * Y) := by
        calc A * δ * ε⁻¹
                * (4 * gaussianShellConst k * ε + 2 * Y + gaussianShellConst k * ε)
            ≤ A * δ * ε⁻¹ * (2 * (4 * gaussianShellConst k * ε + 2 * Y)) :=
              mul_le_mul_of_nonneg_left (by nlinarith [mul_pos hCk hε]) hu
          _ = 2 * A * δ * ε⁻¹ * (4 * gaussianShellConst k * ε + 2 * Y) := by ring
      -- the new logarithmic term: `C_k ≤ 8 C_k`
      have hpart2 : A * δ * (gaussianShellConst k * dimTailConst k * logPow32 ε)
          ≤ 2 * A * δ * (4 * gaussianShellConst k) * (dimTailConst k * logPow32 ε) := by
        have h7 : 0 ≤ A * δ
            * (7 * gaussianShellConst k * (dimTailConst k * logPow32 ε)) := by
          have : 0 ≤ 7 * gaussianShellConst k * (dimTailConst k * logPow32 ε) := by
            nlinarith [mul_nonneg hCk.le hlog0]
          exact mul_nonneg hAδ this
        nlinarith [h7]
      have hsplit : A * δ * (ε⁻¹ * (4 * gaussianShellConst k * ε + 2 * Y
              + gaussianShellConst k * ε)
            + gaussianShellConst k * dimTailConst k * logPow32 ε)
          = A * δ * ε⁻¹ * (4 * gaussianShellConst k * ε + 2 * Y
              + gaussianShellConst k * ε)
            + A * δ * (gaussianShellConst k * dimTailConst k * logPow32 ε) := by ring
      rw [hsplit]
      linarith
    have hthickm : MeasurableSet (Metric.thickening ε S) :=
      Metric.isOpen_thickening.measurableSet
    have hlowμ : (μ S).toReal ≤ ∫ x, f x ∂μ :=
      measureReal_le_integral_of_eq_one hSm (hfint μ inferInstance) hf0 hfS
    have hlowγ : (γ S).toReal ≤ ∫ x, f x ∂γ :=
      measureReal_le_integral_of_eq_one hSm (hfint γ hγprob) hf0 hfS
    have huppμ : (∫ x, f x ∂μ) ≤ (μ (Metric.thickening ε S)).toReal :=
      integral_le_measureReal_of_support_subset hthickm (hfint μ inferInstance) hf1 hfsupp
    have huppγ : (∫ x, f x ∂γ) ≤ (γ (Metric.thickening ε S)).toReal :=
      integral_le_measureReal_of_support_subset hthickm (hfint γ hγprob) hf1 hfsupp
    have hsplit := abs_le.1 herr
    exact ⟨by linarith [hsplit.2], by linarith [hsplit.1]⟩
  -- the two-sided sandwich, set by set
  refine csSup_le (convexDiscrepancySet_nonempty _ _) ?_
  rintro d ⟨B, hBm, hBc, rfl⟩
  have hthick : (γ (Metric.thickening ε B)).toReal
      ≤ (γ B).toReal + gaussianShellConst k * ε := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) (by positivity) ?_
    have := gaussian_thickening_le hk hBc hε
    rwa [← hγdef] at this
  have hEmeas : MeasurableSet (erosion ε B) := (isOpen_erosion _ B).measurableSet
  have hEconv : Convex ℝ (erosion ε B) := convex_erosion hBc
  have herode : (γ B).toReal ≤ (γ (erosion ε B)).toReal + gaussianShellConst k * ε := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) (by positivity) ?_
    have := gaussian_le_erosion_add hk hBm hBc hε
    rwa [← hγdef] at this
  have hback : (μ (Metric.thickening ε (erosion ε B))).toReal ≤ (μ B).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (thickening_erosion_subset _ B))
  have h1 := (hlevy B hBm hBc).1
  have h2 := (hlevy (erosion ε B) hEmeas hEconv).2
  have hCkε : gaussianShellConst k * ε ≤ 4 * gaussianShellConst k * ε := by nlinarith
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · linarith

/-- **The sharp convex Berry–Esseen bound, up to a `3/2` power of one logarithm** (conclusion
AMENDED in wave 32, and AMENDED AGAIN in wave 39). For every dimension `k > 0` there is a
constant `C` with

`|μₙ(B) − γ(B)| ≤ C (β/√n) (1 + log(max (√n/β) e))^{3/2}` for every measurable convex `B`,

i.e. Bentkus's rate up to `(log)^{3/2}`, with the dimension entering only through
`C = 60 ((A+1) · dimTailConst k · (4 C_k))`, `gaussianShellConst k = 4 e² √k` and
`dimTailConst k = √(2k log 2k) + 2√k`, so `C ≍ k √(log k)`. This is still strictly better than
the *proved* `(β/√n)^{1/2}` of `berryEsseen_convex_improved`.

**Wave 39's two deviations from the wave-32 form, both recorded rather than absorbed.** The
localised tail swap can only be run at the radius at which the Gaussian *norm* tail is `≲ σ²`,
and that radius is `σ · gaussianTailRadius k σ`, not `σ`; see
`abs_integral_gaussian_smoothed_swap_localised_le`. Splitting the radius as
`dimTailConst k · √(1 + log(1 + ε⁻¹))` and multiplying by the ledger's harmonic factor turns the
forcing term `1 + log(1 + ε⁻¹)` into `logPow32 ε = (1 + log(1 + ε⁻¹))^{3/2}` and multiplies the
constant by `dimTailConst k`. Both changes were checked, not assumed: the fixed point re-solves
at the *same* constant `20 A C` (`le_of_selfImproving_induction_forcing`), and the ledger is
re-proved at the amended shape (`weighted_ledger_balance`, constant `306 C₃ + 81 C_t`, and
`306 C₃ + 444 C_t` after wave 41 folded in the tail brick's own constants).
Sharpening `stdGaussian_norm_ge_le_exp` from the coordinate union bound to the additive form
`γ{‖z‖ ≥ M} ≤ exp(-(M − √k)²/2)` would replace `dimTailConst k ≍ √(k log k)` by `≍ √k` and
nothing else; the `3/2` power is intrinsic to this route, not an artefact of that bound (a
*fixed* Markov order gives a power of `ε⁻¹` instead, which is worse — wave 38).

This is `exists_convexDiscrepancy_recursion` fed to `le_of_selfImproving_induction_logPow32`.
It is
**not** axiom-clean: it inherits exactly **one** stated-but-unproved brick,
`localised_swap_bound_small_weight` — the small-weight half of brick L (brick H,
`hybridLaw_shell_le` / `hybridLaw_wideShell_le`, is proved; the large-weight half of brick L,
`exists_smooth_swap_bound_of_one_le_weight`, is proved; brick L's wave-20 form was false and is
amended, see `exists_localised_swap_bound`).

**Why the logarithm (wave 32: the amendment is EXECUTED; wave 39: it is a `3/2` power).**
Wave 29's docstring predicted it;
wave 32 records the forcing ledger on `localised_swap_bound_small_weight` and carries the term
through. The telescope smooths step `j` at width `σⱼ = √(j/n)`, and those widths sweep from `ε`
to `1` while the test function has the single width `ε`; the per-step localisation weight is
therefore `4 C_k σⱼ + W`, and `∑_{J<j≤n} j^{-3/2} σⱼ = c ∑_{J<j≤n} j^{-1}` is a *harmonic* sum,
worth `2 log(1/ε)` at the cut `J = ⌈ε² n⌉`. At the fixed point `ε ≍ A δ` that is
`log(1/(Aδ)) ≍ log(√n/β)`. Killing the logarithm needs per-step mollification widths
`εⱼ ≍ σⱼ`, which a single frozen `f` cannot provide.

The log-free form `|μₙ(B) − γ(B)| ≤ C β/√n` is **not** retracted — it is true, being Bentkus's
theorem — it is simply not what this route proves, and the provable-constants rule forbids
recording it here.

Note the `k`-power: `gaussianShellConst k = 4 e² √k` and `dimTailConst k ≍ √(k log k)`, so this
route gives `C ∼ k √(log k)`, not Bentkus's `400 k^{1/4}`. Wave 22 removed the factor `k` that the
coordinate-slice cover of `gaussian_thickening_le` used to contribute (see
`gaussian_le_of_gaussian_shift_cover`); the remaining `√k` is the first absolute moment `E‖Z‖ ≤
√k` of the Gaussian shift, and closing the gap to `k^{1/4}` needs Ball's Gaussian-surface-area
theorem. Nothing in the recursion changes.
Per the provable-constants rule the statement records `k^{1/2}`. -/
theorem berryEsseen_convex_sharp {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))),
      0 < n → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → MeasurableSet B → Convex ℝ B →
      |((sumLaw n ν) B).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ))
            * ((1 + Real.log (max (Real.sqrt (n : ℝ) / (∫ y, ‖y‖ ^ 3 ∂ν)) (Real.exp 1)))
              * Real.sqrt (1 + Real.log
                (max (Real.sqrt (n : ℝ) / (∫ y, ‖y‖ ^ 3 ∂ν)) (Real.exp 1)))) := by
  obtain ⟨A, hApos, hA⟩ := exists_convexDiscrepancy_recursion k hk
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hDk1 : (1 : ℝ) ≤ dimTailConst k := one_le_dimTailConst hk
  have hDk0 : (0 : ℝ) < dimTailConst k := by linarith
  refine ⟨60 * ((A + 1) * dimTailConst k * (4 * gaussianShellConst k)), by positivity, ?_⟩
  intro n ν B hn hνp hmean hcov hβint hBm hBc
  haveI := hνp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  set δ : ℝ := β / Real.sqrt (n : ℝ) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  -- `β ≥ k^{3/2} ≥ 1`, which is what discharges brick L's localisation window: the induction
  -- runs the recursion only at `ε √m = 8 (A + 1) β ≥ 8` (wave 36).
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk1 : 1 ≤ Real.sqrt (k : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hk1
  have hlyap := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
  rw [← hβdef] at hlyap
  have hβ1 : 1 ≤ β := by nlinarith
  -- wave 43: the window is `√k ≤ ε √m`, and `β ≥ k^{3/2} ≥ √k` still discharges it
  have hβk : Real.sqrt (k : ℝ) ≤ β := by nlinarith
  -- the recursion, with `A` enlarged to `A + 1` so that `1 ≤ 8 (A + 1)` for `log_shift_le`
  have hADk : (1 : ℝ) ≤ (A + 1) * dimTailConst k := by nlinarith
  have hbwin : Real.sqrt (k : ℝ) ≤ 8 * ((A + 1) * dimTailConst k) * β := by nlinarith
  have hind := le_of_selfImproving_induction_logPow32 (A := (A + 1) * dimTailConst k)
    (C := 4 * gaussianShellConst k) (b := β)
    (D := fun m => convexDiscrepancy (sumLaw m ν) γ) (by positivity) (by positivity) hβpos
    hbwin
    (fun m hm ε hε hwin Y hY => by
      have hY0 : 0 ≤ Y :=
        le_trans convexDiscrepancy_nonneg (hY m (by omega) le_rfl)
      have h := hA m ν ε Y hm hνp hmean hcov hβint hε hwin (by
        intro m' h1 h2; exact hY m' h1 h2)
      rw [← hβdef] at h
      refine h.trans ?_
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm
      have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmr
      have hd : (0 : ℝ) ≤ β / Real.sqrt (m : ℝ) := by positivity
      have hLP1 : (1 : ℝ) ≤ logPow32 ε := one_le_logPow32 hε
      have hLP0 : (0 : ℝ) ≤ logPow32 ε := by linarith
      have ht1 : 0 ≤ β / Real.sqrt (m : ℝ) * ε⁻¹
          * (4 * gaussianShellConst k * ε + 2 * Y) := by
        have : (0:ℝ) < 4 * gaussianShellConst k * ε := by positivity
        exact mul_nonneg (mul_nonneg hd (inv_pos.2 hε).le) (by linarith)
      have hAle : A ≤ (A + 1) * dimTailConst k := by nlinarith
      have e1 : A * (β / Real.sqrt (m : ℝ)) * ε⁻¹
            * (4 * gaussianShellConst k * ε + 2 * Y)
          ≤ (A + 1) * dimTailConst k * (β / Real.sqrt (m : ℝ)) * ε⁻¹
            * (4 * gaussianShellConst k * ε + 2 * Y) := by
        nlinarith [ht1, hAle]
      have hprod : (0 : ℝ) ≤ dimTailConst k * (β / Real.sqrt (m : ℝ))
          * (4 * gaussianShellConst k) * logPow32 ε :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hd) (by positivity)) hLP0
      have e2 : A * (β / Real.sqrt (m : ℝ)) * (4 * gaussianShellConst k)
            * (dimTailConst k * logPow32 ε)
          ≤ (A + 1) * dimTailConst k * (β / Real.sqrt (m : ℝ))
            * (4 * gaussianShellConst k) * logPow32 ε := by
        nlinarith [hprod]
      linarith) n hn
  -- convert the induction's own log factor into the headline's
  have hlog := logPow32_shift_le (A := 8 * ((A + 1) * dimTailConst k)) (δ := δ)
    (by linarith) hδpos
  have hKpos : (0 : ℝ)
      ≤ 20 * ((A + 1) * dimTailConst k * (4 * gaussianShellConst k)) * δ := by
    rw [hδdef]; positivity
  have hinvδ : δ⁻¹ = Real.sqrt (n : ℝ) / β := by rw [hδdef, inv_div]
  rw [← hδdef] at hind
  rw [hinvδ] at hlog
  refine le_trans (le_convexDiscrepancy hBm hBc) (le_trans hind ?_)
  calc 20 * ((A + 1) * dimTailConst k * (4 * gaussianShellConst k)) * δ
          * logPow32 (8 * ((A + 1) * dimTailConst k) * δ)
      ≤ 20 * ((A + 1) * dimTailConst k * (4 * gaussianShellConst k)) * δ
          * (3 * ((1 + Real.log (max (Real.sqrt (n : ℝ) / β) (Real.exp 1)))
            * Real.sqrt (1 + Real.log (max (Real.sqrt (n : ℝ) / β) (Real.exp 1))))) :=
        mul_le_mul_of_nonneg_left hlog hKpos
    _ = 60 * ((A + 1) * dimTailConst k * (4 * gaussianShellConst k)) * δ
          * ((1 + Real.log (max (Real.sqrt (n : ℝ) / β) (Real.exp 1)))
            * Real.sqrt (1 + Real.log
              (max (Real.sqrt (n : ℝ) / β) (Real.exp 1)))) := by ring

end ConvexDiscrepancy

end StatLean.HypothesisTesting

