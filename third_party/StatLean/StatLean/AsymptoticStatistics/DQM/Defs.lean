module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

/-!
# Differentiability in Quadratic Mean (DQM)

A statistical model $\{P_\theta\}$ with densities $p_\theta$ relative to a
dominating measure $\mu$ is **differentiable in quadratic mean** at the parameter
$\theta$ if there is a (vector-valued) score function $\ell$ such that the
Hellinger residual of $\sqrt{p_\theta}$ vanishes faster than $\|h\|$ in
$L^2(\mu)$ as $h \to 0$:
$$\int \left( \sqrt{p_{\theta+h}} - \sqrt{p_\theta}
  - \tfrac12 \langle h, \ell\rangle \sqrt{p_\theta} \right)^2 \, d\mu
  = o\!\left(\|h\|^2\right).$$
This is the central regularity condition behind Local Asymptotic Normality (LAN):
it is exactly the requirement that the root density map $h \mapsto \sqrt{p_{\theta+h}}$
be Fréchet-differentiable in $L^2(\mu)$ at $h = 0$, with derivative
$\tfrac12 \langle \cdot, \ell\rangle \sqrt{p_\theta}$.

**Added hypothesis (deviation from the book).** Our formalisation states the
condition as a *conjunction* of an $L^2$-membership clause and the little-$o$
rate, rather than as the single integral condition printed in the book. This is
not a strengthening: see the proof formalization notes below for why the
membership clause is implicit in van der Vaart's Lebesgue-integral reading and
must be made explicit once the Bochner integral is used.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 7 (Local Asymptotic Normality), §7.2 (Differentiable in Quadratic Mean),
Eq. (7.1). Consequences and discharges of DQM auxiliary hypotheses live in
`DQM/Properties.lean`.

**Proof formalization notes.** In van der Vaart's definition the displayed
integral is the Lebesgue integral of a non-negative function, where finiteness of
the integral is *equivalent* to $L^2(\mu)$-membership of the residual. When
formalising with Lean's Bochner integral, that equivalence breaks: a
non-integrable non-negative function has Bochner integral $0$ by convention, so
the $o(\|h\|^2)$ rate condition would be *trivially* satisfied for pathological
models whose residual is never in $L^2(\mu)$. We therefore record the implicit
"residual is eventually in $L^2(\mu)$" content of the book's definition as a
separate conjunct (`mem`), so that the formal definition is *equivalent* to the
book's informal one — no stronger, no weaker.

**Bibliographic comments.** Differentiability in quadratic mean originates with
L. Le Cam, "On the assumptions used to prove asymptotic normality of maximum
likelihood estimates," *The Annals of Mathematical Statistics* 41 (1970), no. 3,
802–828. Le Cam introduced this $L^2$/Hellinger differentiability of the root
density as the minimal regularity replacing the classical pointwise
smoothness-and-domination conditions, and used it to establish local asymptotic
normality and the asymptotic normality of maximum likelihood estimators without
the cumbersome third-derivative hypotheses of the Cramér–Wald approach.
-/

open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
variable {μ : Measure 𝓧}

/-- Differentiability in quadratic mean (DQM).

The model `M` is **DQM at `θ`** with score `ℓ : 𝓧 → Θ` w.r.t. the dominating measure `μ`
if the L²(μ) Hellinger residual is `o(‖h‖²)` as `h → 0`:
`∫ (√p_{θ+h} − √p_θ − ½⟨h, ℓ(x)⟩√p_θ)² dμ(x) = o(‖h‖²)`.

This is the central regularity condition of LAN (Local Asymptotic Normality);
see van der Vaart §7.2 (Eq. 7.1).

**Note on the conjunction.** In van der Vaart's definition the integral is the
Lebesgue integral of a non-negative function, where finiteness of the integral
is *the same as* `MemLp 2 μ`-membership of the residual.  When formalising with
Lean's Bochner integral `∫`, that equivalence breaks: a non-integrable
non-negative function has Bochner integral `0` by convention, so the
`o(‖h‖²)` rate condition is *trivially* satisfied for pathological models in
which the residual is never in `L²(μ)`.  We therefore record the implicit
"residual is eventually in `L²(μ)`" content of vdV's definition as a separate
conjunct (`mem`), so that our formal definition is *equivalent* to vdV's
informal one — no stronger, no weaker. -/
structure DifferentiableQuadraticMean
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ : Θ)
    (ℓ : 𝓧 → Θ) : Prop where
  /-- The Hellinger residual is in `L²(μ)` for every `h` in some neighbourhood
  of `0`. (Implicit in vdV via the Lebesgue interpretation of the integral.) -/
  mem : ∀ᶠ h in 𝓝 (0 : Θ),
    MemLp (fun x => M.sqrtDensity (θ + h) x - M.sqrtDensity θ x
                    - (1/2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ x) 2 μ
  /-- The L²(μ) norm of the Hellinger residual is `o(‖h‖²)` as `h → 0`. -/
  isLittleO :
    (fun h : Θ =>
      ∫ x, (M.sqrtDensity (θ + h) x
            - M.sqrtDensity θ x
            - (1/2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ x) ^ 2 ∂μ)
    =o[𝓝 (0 : Θ)] (fun h : Θ => ‖h‖ ^ 2)

end AsymptoticStatistics
