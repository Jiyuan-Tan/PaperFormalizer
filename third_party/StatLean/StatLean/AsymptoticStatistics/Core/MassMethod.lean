module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Core.Pathwise
public import StatLean.AsymptoticStatistics.Core.CandidateIF
public import StatLean.AsymptoticStatistics.Core.EIF
public import StatLean.AsymptoticStatistics.ForMathlib.MassMethodUtilities

@[expose] public section

/-!
# Point-mass Gâteaux equivalence for the efficient influence function

This file verifies that a candidate raw influence function is the **efficient
influence function** (EIF) of a parameter functional, by way of the
point-mass / mixture-Gâteaux heuristic that practitioners use to *guess* the
influence function.

Setup and statement. Let $P$ be a probability measure and $\Psi$ a real-valued
functional of probability measures, pathwise differentiable at $P$ over the
full tangent space with derivative $\dot\psi$. A candidate influence function
$\varphi$ lies in $L^2_0(P)$ — the square-integrable, mean-zero functions
(i.e. $\int \varphi\,dP = 0$). Say $\varphi$ is the **mixture-Gâteaux
representer** of $\Psi$ if, for every probability measure $Q \ll P$ with
bounded density $dQ/dP$, the directional derivative along the convex mixture
path $P_t := (1-t)P + tQ$ exists and equals the $Q$-mean of $\varphi$:
$$
  \left.\frac{d}{dt}\,\Psi\big((1-t)P + tQ\big)\right|_{t=0^+}
    \;=\; \int \varphi \, dQ .
$$
The main theorem `gateaux_representer_eq_pathwise_derivative` shows that such a
$\varphi$ is an influence function for $\dot\psi$: for every tangent direction
$g$,
$$
  \langle \varphi, g\rangle_{L^2(P)} \;=\; \dot\psi(g),
$$
so $\varphi$ is precisely the efficient influence function. Operationally, the
user computes a candidate EIF by symbolic differentiation of the point-mass-
evaluated functional ($\frac{d}{dt}\Psi((1-t)P + t\delta_x)|_{t=0} = \varphi(x)$,
extended linearly to $Q$ via $\int \varphi\,dQ$), asserts in Lean that the
formula is the mixture-Gâteaux representer, and the library closes the EIF
claim. Convenience wrappers (`eif_via_Gateaux`, `eif_via_TV_frechet`,
`eif_via_Point_mass`) package the result for the different forms in which the
user can supply the directional-derivative computation (mixture-Gâteaux
representer, TV-Fréchet expansion, or a one-dimensional point-mass derivative).

Two supporting lemmas carry the analytic content. `boundedDensityPath`
constructs, for each essentially bounded mean-zero score $g$ bounded below by
$-1$, a differentiable-in-quadratic-mean (QMD) curve from the affine density
family $p_t = 1 + t\,g$ with score $g$; this realizes the convex mixture path
as a QMD path, so the QMD-curve pathwise derivative and the mixture-Gâteaux
limit refer to the same scalar. `bounded_score_span_dense` shows the linear
span of these bounded scores is dense in $L^2_0(P)$, which extends the
identity $\langle\varphi,g\rangle = \dot\psi(g)$ from the bounded class to all
of $L^2_0(P)$ by inner-product continuity.

The Lean statement matches the informal one with one explicit restriction: the
mixture-Gâteaux representer hypothesis is stated only for $Q \ll P$ with
*bounded* Radon–Nikodym derivative $dQ/dP$ (not for arbitrary signed-measure
perturbations or point masses $\delta_x$, which would require the full
TV-Fréchet machinery on the signed-measure Banach space). The point-mass
formula $\frac{d}{dt}\Psi((1-t)P + t\delta_x)|_{t=0} = \varphi(x)$ is the
heuristic motivation; the bounded-RN-mixture form is what the proof uses.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series
in Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information).
See also the project note `ref/mass/mass.tex` (Equivalence of the Point-Mass
Gâteaux Derivative and the Efficient Influence Function), whose two supporting
lemmas are formalised here as `boundedDensityPath` and
`bounded_score_span_dense`.

**Proof formalization notes.**

`boundedDensityPath` (mass.tex Lemma 1, DQM of bounded mixture paths). For
$g \in B$, the density family $p_t = 1 + t\,g$ defines a `QMDPath P` with
score $g$:

- Let $M$ be an essential bound for $g$; set $\delta := 1/(M+1)$. For
  $t \in (-\delta, \delta)$, $1 + t\,g > 0$ a.e. (since $g \ge -1$ and
  $|t\,g| < 1$). Define `curve t := if |t| < δ then P.withDensity (1 + t·g)
  else P`; then `curve 0 = P`, each `curve t` is a probability measure (the
  density integrates to $1 + t\int g\,dP = 1$ since $g \in L^2_0(P)$), and the
  curve is absolutely continuous w.r.t. $P$.
- `qmd_limit` is the substantive content: for $t \in (0,\delta)$ the pointwise
  bound $\big|(\sqrt{1+t g}-1)/t - g/2\big|^2 \le t^2 g^4/4$ follows from
  $\sqrt{1+u}-1 = u/(\sqrt{1+u}+1)$ with $u := t\,g$ and $\sqrt{1+u}+1 \ge 1$.
  Integrating gives $\mathrm{eLpNorm}^2 \le t^2\|g\|_\infty^4/4$, hence
  $\mathrm{eLpNorm}^2/t^2 \to 0$ as $t \to 0$. The $t<0$ case follows by
  replacing $t$ with $|t|$; outside $(-\delta,\delta)$ the curve is $P$, so
  only small-$t$ behavior matters for the `𝓝[≠] 0` limit. The algebraic
  Lipschitz inequality is closed by `nlinarith` after `field_simp`; the
  integral squeeze uses `tendsto_of_tendsto_of_tendsto_of_le_of_le`.

`gateaux_representer_eq_pathwise_derivative` (mass.tex main theorem). For
$g \in B$, `boundedDensityPath g hg` is a QMD path with score $g$ whose curve
at $t \in (0,1)$ agrees with the convex mixture $(1-t)P + tQ$ for
$Q := P.\mathrm{withDensity}(1+g)$. Therefore the QMD-curve limit
(`PathwiseDifferentiableAt`) and the mixture-Gâteaux limit
(`IsMixtureGateauxRepresenter`) are the same scalar. The Gâteaux side gives
$\int \varphi\,dQ = \int \varphi(1+g)\,dP = \langle\varphi,g\rangle$ (using
$\int\varphi\,dP = 0$); the QMD side gives $\dot\psi(g)$; equating yields
$\langle\varphi,g\rangle = \dot\psi(g)$ for $g \in B$. By bilinearity this
extends to $\mathrm{span}(B)$, and by `bounded_score_span_dense` plus
inner-product continuity to all of $L^2_0(P) = \top$. Mechanically: both sides
are continuous linear maps in $g$; `ContinuousLinearMap.ext_on` lets two CLMs
agreeing on a dense set agree everywhere.

The file also exposes intermediate definitions (`IsEssBoundedMixtureScore`,
`IsBoundedMixtureScore`, `IsTangentBoundedDense`, `IsMixtureGateauxRepresenter`,
`IsTVFrechetMixtureExpansion`, `IsTVFrechetExpansion`) and helper lemmas on the
truncation radius and the curve's Radon–Nikodym derivative; their per-
declaration docstrings record the precise book-vs-Lean correspondences,
including the deliberate restriction to bounded-RN convex mixtures noted above.

**Bibliographic comments.** This is a folklore result in
semiparametric statistics, with no single seminal theorem to cite. The
"influence function as a Gâteaux derivative" viewpoint originates in the
von Mises calculus of differentiable statistical functionals — R. von Mises,
"On the asymptotic distribution of differentiable statistical functions,"
*Annals of Mathematical Statistics* 18 (1947), 309–348 — and in the influence
curve of robust statistics, defined as the Gâteaux derivative of a functional
in the direction of a point mass $\delta_x$: F. R. Hampel, "The influence
curve and its role in robust estimation," *Journal of the American Statistical
Association* 69 (1974), 383–393. The packaging as an *equivalence* between this
point-mass Gâteaux derivative and the efficient influence function — via
pathwise (QMD-path) differentiability over the tangent space — is the standard
modern treatment of van der Vaart, *Asymptotic Statistics* (1998), Chapter 25;
no original research paper states this exact equivalence under these
hypotheses.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.MassMethod

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIF

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Integrability via dominated measure.*

If `f ∈ L¹(P)` and `Q ≪ P` has bounded RN-derivative `dQ/dP ≤ M`
a.e.-`P`, then `f ∈ L¹(Q)`. The proof works at the measure level:
`Q ≤ M • P` by `withDensity_rnDeriv_eq` + `withDensity_mono`, and
`Integrable.mono_measure` transfers `Integrable f (M • P)` to
`Integrable f Q`.

Dropping the `f` boundedness assumption keeps the verification entry
points free of an unnecessarily strong essential-boundedness hypothesis
on `f`. -/
lemma integrable_of_rnDeriv_bound {f : Ω → ℝ} {Q : Measure Ω}
    [IsFiniteMeasure Q]
    (hf_int : Integrable f P) (h_ac : Q ≪ P)
    (h_bdd : ∃ M : ℝ, ∀ᵐ ω ∂P, (Q.rnDeriv P ω).toReal ≤ M) :
    Integrable f Q := by
  obtain ⟨M, hM⟩ := h_bdd
  -- Convert real bound to ENNReal bound a.e.-P (using rnDeriv < ⊤ a.e.).
  have h_le_ae : ∀ᵐ ω ∂P, Q.rnDeriv P ω ≤ ENNReal.ofReal M := by
    filter_upwards [hM, Measure.rnDeriv_lt_top Q P] with ω h_le h_top
    rw [← ENNReal.ofReal_toReal h_top.ne]
    exact ENNReal.ofReal_le_ofReal h_le
  -- Q ≤ (ENNReal.ofReal M) • P as measures.
  have hQ_le : Q ≤ (ENNReal.ofReal M) • P := by
    calc Q
        = P.withDensity (Q.rnDeriv P) :=
          (Measure.withDensity_rnDeriv_eq Q P h_ac).symm
      _ ≤ P.withDensity (fun _ => ENNReal.ofReal M) :=
          MeasureTheory.withDensity_mono h_le_ae
      _ = (ENNReal.ofReal M) • P := MeasureTheory.withDensity_const _
  -- f ∈ L¹(M·P), then transfer via `mono_measure`.
  have h_int_smul : Integrable f ((ENNReal.ofReal M) • P) :=
    hf_int.smul_measure (by exact ENNReal.ofReal_ne_top)
  exact h_int_smul.mono_measure hQ_le

/-- Essentially bounded mean-zero functions in `L²₀(P)`.

This is the relaxed score class for the truncated `boundedDensityPath`
construction: only the M-bound `|g| ≤ M a.e.` is needed for the curve
`(1 + t·g)·P` to be a probability measure on `|t| < 1/(M+1)` (the
`g ≥ -1` clause of `IsBoundedMixtureScore` is only required for the
*global* `(1 + g)·P` form used by `boundedDensityPath_curve_eq_mixture_eventually`,
not for the truncated curve, QMD limit, DQM, or LAN expansion).

The convex-combination vector `c_inf := Σⱼ ⟨IF_eff, gⱼ⟩ • gⱼ` is
generically L²(P) but unbounded; truncating it yields essentially-bounded
approximants which satisfy `IsEssBoundedMixtureScore` but not
`IsBoundedMixtureScore`. -/
def IsEssBoundedMixtureScore (g : ↥(L2ZeroMean P)) : Prop :=
  ∃ M : ℝ, ∀ᵐ ω ∂P, |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M

/-- The set `B` of `ref/mass/mass.tex` §2: essentially bounded
mean-zero functions in `L²₀(P)` with values bounded below by `-1`.

Lemma 1 of mass.tex shows that for `g ∈ B`, the density family
`p_t = 1 + t·g` defines a QMD curve with score `g` for `t ∈ [0, 1)`.
Lemma 2 shows the linear span of `B` is dense in `L²₀(P)`. -/
def IsBoundedMixtureScore (g : ↥(L2ZeroMean P)) : Prop :=
  (∃ M : ℝ, ∀ᵐ ω ∂P, |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M) ∧
  ∀ᵐ ω ∂P, -1 ≤ ((g : Lp ℝ 2 P) : Ω → ℝ) ω

/-- The M-bound projection: `IsBoundedMixtureScore` is strictly stronger
than `IsEssBoundedMixtureScore` (it adds the `g ≥ -1` clause). -/
lemma IsBoundedMixtureScore.toEss
    {g : ↥(L2ZeroMean P)} (hg : IsBoundedMixtureScore g) :
    IsEssBoundedMixtureScore g := hg.1

/-- Regularity hypothesis on a tangent specification: every element of the
closed-linear-span tangent space `tangentSpace T_set` is the L²(P)-limit
of an essentially bounded sequence still in `tangentSpace T_set`.

The convex-combination vector `c_inf := Σⱼ ⟨IF_eff, gⱼ⟩ • gⱼ` lies in
`tangentSpace T_set` (closed span of an orthonormal basis taken from
there) but is generically L²(P)-only, not essentially bounded. To apply
the LAN expansion along an approximating ray (which requires
`IsEssBoundedMixtureScore`), we need an essentially-bounded approximant of
`c_inf` *that is itself in `tangentSpace T_set`*.

Bounded vectors are dense in *full* L²(P, σ-finite), but not generally
in an arbitrary closed subspace. This regularity hypothesis is what
characterises tangent specifications for which the standard
mass-method-based LAN closure of vdV §25.3.2 succeeds. -/
def IsTangentBoundedDense
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : AsymptoticStatistics.Core.TangentAbstract.TangentSpec P) : Prop :=
  ∀ g, g ∈ AsymptoticStatistics.Core.TangentAbstract.tangentSpace T_set →
    ∃ g_n : ℕ → ↥(L2ZeroMean P),
      (∀ n, g_n n ∈ AsymptoticStatistics.Core.TangentAbstract.tangentSpace T_set) ∧
      (∀ n, IsEssBoundedMixtureScore (g_n n)) ∧
      Filter.Tendsto (fun n => ‖g_n n - g‖) Filter.atTop (nhds 0)

/-- The user's mixture-Gâteaux-representer assertion: the candidate
`φ ∈ L²₀(P)` represents the directional derivative of `Ψ` along every
convex-mixture path `(1−t)·P + t·Q` for any probability measure
`Q ≪ P` with bounded `dQ/dP`.

This is the formal statement of `ref/mass/mass.tex` Definition 3
(Mixture Gâteaux Differentiability). The natural output of point-mass
symbolic differentiation: `(d/dt) Ψ((1−t)·P + t·δ_x)|_{t=0} = φ(x)`
extends linearly to `Q` via `∫ φ dQ`.

The user supplies this assertion together with the candidate `φ`. The
library closes the EIF claim via `eif_via_Gateaux`. -/
def IsMixtureGateauxRepresenter
    (Ψ : Measure Ω → ℝ) (φ : ↥(L2ZeroMean P)) : Prop :=
  ∀ (Q : Measure Ω) [IsProbabilityMeasure Q] (_h_ac : Q ≪ P)
    (_h_bdd : ∃ M : ℝ, ∀ᵐ ω ∂P, (Q.rnDeriv P ω).toReal ≤ M),
    Filter.Tendsto (fun t : ℝ =>
      (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) - Ψ P) / t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ ω, ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂Q))

/-- The bounded-RN-mixture form of TV-Fréchet differentiability
(`ref/mass/point_mass.tex` Assumption 1, restricted to bounded
absolutely-continuous perturbations).

`Ψ` admits a TV-Fréchet expansion at `P` with representer
`f : Ω → ℝ` if for every probability measure `Q ≪ P` with bounded
`dQ/dP` the directional derivative along the convex mixture
`(1−t)·P + t·Q` evaluates to `∫ f dQ − ∫ f dP`:

  `lim_{t↓0} (Ψ((1−t)P + tQ) − Ψ(P)) / t = ∫ f dQ − ∫ f dP`.

This is the practical specialization of TV-Fréchet differentiability
that the `point_mass.tex` Theorem 1 proof actually uses (Lemma 1's
point-mass calculation `δ_x` is heuristic only — it requires a
strictly stronger TV-Fréchet hypothesis on signed measures, not
covered here). The full TV-Fréchet hypothesis on the signed-measure
Banach space implies this form for all bounded-RN paths but is not
required for the EIF conclusion: the candidate
`φ(x) := f(x) − ∫ f dP` already lies in `L²₀(P)` after centering, and
the bridge `tv_frechet_imp_mixture_gateaux` shows the limit form
matches `IsMixtureGateauxRepresenter` for that centered candidate.

The user supplies the representer `f` and proves this expansion either
by hand (TV-Fréchet derivative calculation against signed-measure
perturbations) or by invoking a Fréchet-calculus tool. In contrast to
`IsMixtureGateauxRepresenter`,
the limit value here is the integral *pair* `∫f dQ − ∫f dP`, not
the centered single-integral form `∫φ dQ` — which is the natural
output of the book's Fréchet expansion `Ψ(Q)−Ψ(P) = L(Q−P) + o(‖Q−P‖)`
specialised at `Q = (1−t)P + tQ_0`. -/
def IsTVFrechetMixtureExpansion
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : Measure Ω → ℝ) (f : Ω → ℝ) : Prop :=
  ∀ (Q : Measure Ω) [IsProbabilityMeasure Q] (_h_ac : Q ≪ P)
    (_h_bdd : ∃ M : ℝ, ∀ᵐ ω ∂P, (Q.rnDeriv P ω).toReal ≤ M),
    Filter.Tendsto (fun t : ℝ =>
      (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) - Ψ P) / t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ ω, f ω ∂Q - ∫ ω, f ω ∂P))

/-- The DQM-path form of TV-Fréchet differentiability — the strictly
stronger hypothesis whose conclusion is `point_mass.tex` Theorem 1's
full claim (without separately requiring `PathwiseDifferentiableAt`).

For every QMD path `γ` at `P`, the directional derivative of `Ψ`
along `γ` exists and equals `∫ f · γ.score dP`. This is what
`point_mass.tex` Theorem 1 establishes as a *consequence* of the
full signed-measure TV-Fréchet hypothesis (DQM ⇒ TV-differentiable).
We take it directly here, sidestepping the need to formalize
`MeasureTheory.SignedMeasure`'s TV-norm Banach machinery while still
capturing the book's main analytical content.

Strictly stronger than `IsTVFrechetMixtureExpansion` (which only
covers bounded-RN convex mixtures); strictly weaker than
formal-signed-measure TV-Fréchet (no point-mass coverage). The
right "middle hypothesis" for the EIF conclusion via the
`pathwiseDifferentiableAt_of_TVFrechet` constructor.

The user supplies the integral identity directly along DQM paths.
This is the natural form when the user can compute the directional
derivative `(d/dt) Ψ(γ.curve t)|_{t=0}` against an arbitrary score
function. -/
def IsTVFrechetExpansion
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : Measure Ω → ℝ) (f : Ω → ℝ) : Prop :=
  ∀ (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P),
    Filter.Tendsto (fun t : ℝ => (Ψ (γ.curve t) - Ψ P) / t)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (∫ ω, f ω * ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω ∂P))

/-- Lemma 1 of `ref/mass/mass.tex` (DQM of bounded mixture paths).

For `g ∈ B`, the density family `p_t = 1 + t·g` (with respect to `P`)
defines a `QMDPath P` with score `g`.

Construction (mass.tex Lemma 1):

- Let `M` be an essential bound for `g` (from `hg.1`); set
  `δ := 1 / (M + 1)`. For `t ∈ (-δ, δ)`, the density `1 + t·g` is
  strictly positive a.e. (since `g ≥ -1` and `|t·g| < 1`).
- Define `curve t := if |t| < δ then P.withDensity (1 + t·g) else P`.
- `curve 0 = P` since `1 + 0·g = 1` a.e. (using
  `Measure.withDensity_one`).
- `curve_isProbability ∀ t`: for `|t| < δ`, the density integrates to
  `1 + t·∫g dP = 1 + 0 = 1` (using `g ∈ L²₀(P)`); for `|t| ≥ δ`,
  `curve t = P`. ✓
- `dominating := P`; `curve_absContinuous` from
  `MeasureTheory.withDensity_absolutelyContinuous`.
- `score := g`.
- `qmd_limit`: the substantive content. For `t ∈ (0, δ)`, the
  pointwise bound `|((√(1+t·g) − 1)/t − g/2)|² ≤ t² g⁴ / 4` follows
  from the algebraic identity
  `√(1+u) − 1 = u / (√(1+u) + 1)` with `u := t·g` and the lower bound
  `√(1+u) + 1 ≥ 1`. Integrating gives `eLpNorm² ≤ t² · ‖g‖_∞⁴ / 4`,
  hence `eLpNorm² / t² ≤ t² · ‖g‖_∞⁴ / 4 → 0` as `t → 0`. The
  symmetric bound for `t < 0` follows by replacing `t` with `|t|` in
  the algebraic identity. Outside `(-δ, δ)` the curve is `P` so
  the bound's RHS dominates; only the small-t behavior matters for
  the Tendsto in `𝓝[≠] 0`.

The algebraic Lipschitz inequality is closed by `nlinarith` after
`field_simp` against `√(1+u) + 1 ≥ 1`; the integral squeeze uses
`tendsto_of_tendsto_of_tendsto_of_le_of_le`. -/
noncomputable def boundedDensityPath
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) :
    QMDPath P :=
  let M : ℝ := max 0 (Classical.choose hg)
  let δ : ℝ := 1 / (M + 1)
  let f : ℝ → Ω → ℝ := fun t ω =>
    1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω
  let curve : ℝ → Measure Ω := fun t =>
    if |t| < δ then P.withDensity (fun ω => ENNReal.ofReal (f t ω)) else P
  { curve := curve
    curve_at_zero := by
      -- δ > 0 since M ≥ 0; |0| = 0 < δ; density at t=0 is constant 1.
      have hM_nn : (0 : ℝ) ≤ M := le_max_left _ _
      have hδ_pos : (0 : ℝ) < δ := by
        change 0 < 1 / (M + 1)
        apply div_pos one_pos
        linarith
      change (if |(0 : ℝ)| < δ then P.withDensity
             (fun ω => ENNReal.ofReal (f 0 ω)) else P) = P
      rw [abs_zero, if_pos hδ_pos]
      -- f 0 ω = 1 + 0 * g_ω = 1, ENNReal.ofReal 1 = 1
      have h_const :
          (fun ω => ENNReal.ofReal (f 0 ω)) = (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        change ENNReal.ofReal (1 + (0 : ℝ) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
            = (1 : ℝ≥0∞)
        rw [zero_mul, add_zero, ENNReal.ofReal_one]
      rw [h_const]
      exact MeasureTheory.withDensity_one
    curve_isProbability := fun t => by
      by_cases h : |t| < δ
      · -- For |t| < δ: density 1+t·g is a.e. ≥ 0 (since g ≥ -1 and |t·g| ≤ |t|·M < 1)
        -- and integrates to 1.
        simp only [curve, h, if_true]
        -- Goal: IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal (f t ω)))
        refine ⟨?_⟩
        -- Standing facts about M and δ.
        have hM_nn : (0 : ℝ) ≤ M := le_max_left _ _
        have hδ_pos : (0 : ℝ) < δ := by
          change 0 < 1 / (M + 1); apply div_pos one_pos; linarith
        have hδM : δ * M < 1 := by
          have : δ * M = M / (M + 1) := by
            change (1 / (M + 1)) * M = M / (M + 1)
            field_simp
          rw [this]; rw [div_lt_one (by linarith : (0 : ℝ) < M + 1)]; linarith
        -- |g ω| ≤ M almost everywhere (using `M ≥ Classical.choose hg.1`).
        have h_abs_g_le_M : ∀ᵐ ω ∂P, |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M := by
          have hChoose : ∀ᵐ ω ∂P,
              |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ Classical.choose hg :=
            Classical.choose_spec hg
          filter_upwards [hChoose] with ω hω
          exact hω.trans (le_max_right _ _)
        -- Pointwise non-negativity of f t under |t| < δ.
        have h_f_nn : ∀ᵐ ω ∂P, 0 ≤ f t ω := by
          filter_upwards [h_abs_g_le_M] with ω hω
          have hbound : |t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω| < 1 := by
            rw [abs_mul]
            calc |t| * |((g : Lp ℝ 2 P) : Ω → ℝ) ω|
                ≤ |t| * M := by
                  apply mul_le_mul_of_nonneg_left hω (abs_nonneg _)
              _ ≤ δ * M := mul_le_mul_of_nonneg_right (le_of_lt h) hM_nn
              _ < 1 := hδM
          have h1 : -1 < t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by
            have := abs_lt.mp hbound
            linarith [this.1]
          change 0 ≤ 1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω
          linarith
        -- Integrability of f t under P.
        have hg_int : Integrable (((g : Lp ℝ 2 P) : Ω → ℝ)) P :=
          (Lp.memLp (g : Lp ℝ 2 P)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        have h_f_int : Integrable (f t) P := by
          change Integrable (fun ω => 1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω) P
          exact (integrable_const _).add (hg_int.const_mul t)
        -- Compute ∫ f t dP = 1 using mean-zero of g.
        have h_integral_g : ∫ ω, ((g : Lp ℝ 2 P) : Ω → ℝ) ω ∂P = 0 := by
          have h_mem : (g : Lp ℝ 2 P) ∈ L2ZeroMean P := g.2
          change (g : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at h_mem
          rw [LinearMap.mem_ker] at h_mem
          -- integralL2 P (g.val) = ⟪oneL2 P, g.val⟫ = 0
          have h_inner : ⟪oneL2 P, (g : Lp ℝ 2 P)⟫_ℝ = 0 := h_mem
          -- Convert ⟪oneL2 P, g.val⟫ = ∫ g dP via L2.inner_def + identification.
          rw [MeasureTheory.L2.inner_def] at h_inner
          have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
            MemLp.coeFn_toLp (memLp_const (1 : ℝ))
          have h_int_eq :
              ∫ a, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
                    ((g : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ ∂P
                = ∫ a, ((g : Lp ℝ 2 P) : Ω → ℝ) a ∂P := by
            apply integral_congr_ae
            filter_upwards [h_one_ae] with a ha
            have hcomm :
                ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
                  ((g : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
                  = ((g : Lp ℝ 2 P) : Ω → ℝ) a
                      * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
            rw [hcomm, ha, mul_one]
          rw [h_int_eq] at h_inner
          exact h_inner
        have h_integral_f : ∫ ω, f t ω ∂P = 1 := by
          change ∫ ω, 1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω ∂P = 1
          rw [integral_add (integrable_const _) (hg_int.const_mul t),
              integral_const, integral_const_mul, h_integral_g]
          simp
        -- Now: (P.withDensity ofReal(f t)) Set.univ = ∫⁻ ω, ofReal (f t ω) ∂P
        -- = ENNReal.ofReal (∫ f t dP) = ENNReal.ofReal 1 = 1.
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        rw [← ofReal_integral_eq_lintegral_ofReal h_f_int h_f_nn,
            h_integral_f, ENNReal.ofReal_one]
      · -- For |t| ≥ δ: curve = P.
        simp only [curve, h, if_false]; infer_instance
    dominating := P
    dominating_sigmaFinite := inferInstance
    curve_absContinuous := fun t => by
      by_cases h : |t| < δ
      · simp only [curve, h, if_true]
        exact MeasureTheory.withDensity_absolutelyContinuous _ _
      · simp only [curve, h, if_false]
        exact Measure.AbsolutelyContinuous.refl P
    score := g
    qmd_limit := by
      -- Strategy: For |t| < δ, dᵗ := (curve t).rnDeriv P =ᵐ ENNReal.ofReal (f t),
      -- and (curve 0).rnDeriv P =ᵐ 1. So LSE_t =ᵐ √(1+t·g) − 1 − (t/2)·g.
      -- Pointwise (a.e.): |LSE_t ω| ≤ t²·g(ω)²/2 ≤ t²·M²/2. Hence
      -- eLpNorm LSE_t 2 P ≤ ofReal(t²·M²/2) (universe = 1). For t ≠ 0:
      -- eLpNorm / ofReal|t| ≤ ofReal(t²·M²/2) / ofReal|t| = ofReal(|t|·M²/2)
      -- → 0 as t → 0. Squeeze with lower bound 0.
      -- Helper: generalisation of `dqm_integrand_bound` to any sign of `t`,
      -- conditioned on `0 ≤ 1 + t·u`.
      have dqm_general : ∀ {t u : ℝ}, 0 ≤ 1 + t * u →
          |Real.sqrt (1 + t * u) - 1 - (t / 2) * u| ≤ t ^ 2 * u ^ 2 / 2 := by
        intro t u h_nn
        set s := Real.sqrt (1 + t * u) with hs_def
        have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
        have hs_sq : s * s = 1 + t * u := Real.mul_self_sqrt h_nn
        have h_lhs_eq : s - 1 - (t / 2) * u = -((s - 1) ^ 2) / 2 := by
          have h_tu : t * u = s * s - 1 := by linarith [hs_sq]
          nlinarith [h_tu, sq_nonneg (s - 1)]
        rw [h_lhs_eq, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_nonneg (sq_nonneg _)]
        have h_step : (s - 1) ^ 2 ≤ t ^ 2 * u ^ 2 := by
          have h_tu_sq : t ^ 2 * u ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by
            have h_tu : t * u = s * s - 1 := by linarith [hs_sq]
            have hsq_factor : (s * s - 1) = (s - 1) * (s + 1) := by ring
            nlinarith [h_tu, hsq_factor, sq_nonneg ((s - 1) * (s + 1))]
          rw [h_tu_sq]
          have h_splus_one : (1 : ℝ) ≤ (s + 1) ^ 2 := by nlinarith [hs_nonneg]
          have h_lhs_nn : 0 ≤ (s - 1) ^ 2 := sq_nonneg _
          nlinarith [h_lhs_nn, h_splus_one]
        linarith [h_step]
      -- Standing facts.
      have hM_nn : (0 : ℝ) ≤ M := le_max_left _ _
      have hδ_pos : (0 : ℝ) < δ := by
        change 0 < 1 / (M + 1); apply div_pos one_pos; linarith
      have hδM_lt_one : δ * M < 1 := by
        have hsplit : δ * M = M / (M + 1) := by
          change (1 / (M + 1)) * M = M / (M + 1); field_simp
        rw [hsplit, div_lt_one (by linarith : (0 : ℝ) < M + 1)]; linarith
      -- |g ω| ≤ M almost everywhere.
      have h_abs_g_le_M : ∀ᵐ ω ∂P, |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M := by
        have hChoose : ∀ᵐ ω ∂P,
            |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ Classical.choose hg :=
          Classical.choose_spec hg
        filter_upwards [hChoose] with ω hω
        exact hω.trans (le_max_right _ _)
      -- Squeeze: lower bound 0, upper bound `t² · M⁴ / 4`.
      have h_lower_tendsto :
          Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
        tendsto_const_nhds
      have h_upper_tendsto :
          Tendsto (fun t : ℝ => ENNReal.ofReal (|t| * M ^ 2 / 2))
            (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
        have h_ambient :
            Tendsto (fun t : ℝ => |t| * M ^ 2 / 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
          have hcont : Continuous (fun t : ℝ => |t| * M ^ 2 / 2) := by
            continuity
          have := hcont.tendsto 0
          simpa using this
        have h_ennreal :
            Tendsto (fun t : ℝ => ENNReal.ofReal (|t| * M ^ 2 / 2))
              (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
          have : ENNReal.ofReal (0 : ℝ) = 0 := ENNReal.ofReal_zero
          rw [← this]
          exact (ENNReal.continuous_ofReal.tendsto _).comp h_ambient
        exact h_ennreal.mono_left nhdsWithin_le_nhds
      -- Apply squeeze.
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_tendsto
              h_upper_tendsto
      · -- Lower bound: ∀ᶠ t in 𝓝[≠] 0, 0 ≤ eLpNorm / ofReal|t|.
        refine Eventually.of_forall (fun t => zero_le)
      · -- Upper bound: eventually `eLpNorm / ofReal|t| ≤ ofReal(|t|·M²/2)`.
        -- Use the open neighborhood `Set.Ioo (-δ) δ ∈ 𝓝 0`, restricted to
        -- `𝓝[≠] 0`, and require `t ≠ 0`.
        have h_open : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) :=
          Ioo_mem_nhds (by linarith) hδ_pos
        have h_open_ne : Set.Ioo (-δ) δ ∈ 𝓝[≠] (0 : ℝ) :=
          mem_nhdsWithin_of_mem_nhds h_open
        have h_self_ne : {x : ℝ | x ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := self_mem_nhdsWithin
        filter_upwards [h_open_ne, h_self_ne] with t ht_in ht_ne
        -- Extract `|t| < δ` from `t ∈ Ioo (-δ) δ`.
        have ht_abs : |t| < δ := abs_lt.mpr ⟨ht_in.1, ht_in.2⟩
        -- |t| > 0
        have ht_abs_pos : 0 < |t| := abs_pos.mpr ht_ne
        -- Set up density a.e. equalities.
        -- (curve t).rnDeriv P =ᵐ[P] ENNReal.ofReal (1 + t·g)
        --   and (curve 0).rnDeriv P =ᵐ[P] 1.
        have h_curve_t_eq :
            (curve t) = P.withDensity (fun ω => ENNReal.ofReal (f t ω)) := by
          simp only [curve, ht_abs, if_true]
        have h_curve_0_eq : (curve 0) = P := by
          have h0_lt : |(0 : ℝ)| < δ := by rw [abs_zero]; exact hδ_pos
          simp only [curve, h0_lt, if_true]
          have h_const :
              (fun ω => ENNReal.ofReal (f 0 ω)) = (fun _ => (1 : ℝ≥0∞)) := by
            funext ω
            change ENNReal.ofReal (1 + (0 : ℝ) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
                = (1 : ℝ≥0∞)
            rw [zero_mul, add_zero, ENNReal.ofReal_one]
          rw [h_const]
          exact MeasureTheory.withDensity_one
        have h_g_meas : AEMeasurable (((g : Lp ℝ 2 P) : Ω → ℝ)) P :=
          (Lp.aestronglyMeasurable (g : Lp ℝ 2 P)).aemeasurable
        have h_density_meas :
            AEMeasurable (fun ω => ENNReal.ofReal (f t ω)) P := by
          have : AEMeasurable (fun ω => 1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω) P :=
            ((aemeasurable_const).add ((aemeasurable_const).mul h_g_meas))
          exact this.ennreal_ofReal
        have h_rn_t : (curve t).rnDeriv P
              =ᵐ[P] fun ω => ENNReal.ofReal (f t ω) := by
          rw [h_curve_t_eq]
          exact Measure.rnDeriv_withDensity₀ P h_density_meas
        have h_rn_0 : (curve 0).rnDeriv P =ᵐ[P] fun _ => (1 : ℝ≥0∞) := by
          rw [h_curve_0_eq]; exact Measure.rnDeriv_self P
        -- Pointwise rewrite: LSE_t ω = √(1+t·g(ω)) - 1 - (t/2)·g(ω).
        -- Let's denote the integrand by `LSE`.
        set LSE : Ω → ℝ := fun ω =>
          Real.sqrt ((curve t).rnDeriv P ω).toReal
            - Real.sqrt ((curve 0).rnDeriv P ω).toReal
            - (t / 2) * ((g : Ω → ℝ)) ω
                * Real.sqrt ((curve 0).rnDeriv P ω).toReal with hLSE_def
        -- Pointwise non-negativity of `1 + t·g(ω)` from the bound.
        have h_f_nn : ∀ᵐ ω ∂P, 0 ≤ 1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by
          filter_upwards [h_abs_g_le_M] with ω hω
          have hbound : |t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω| < 1 := by
            rw [abs_mul]
            calc |t| * |((g : Lp ℝ 2 P) : Ω → ℝ) ω|
                ≤ |t| * M :=
                  mul_le_mul_of_nonneg_left hω (abs_nonneg _)
              _ ≤ δ * M := mul_le_mul_of_nonneg_right (le_of_lt ht_abs) hM_nn
              _ < 1 := hδM_lt_one
          linarith [(abs_lt.mp hbound).1]
        -- LSE =ᵐ[P] (fun ω => √(1+t·g(ω)) - 1 - (t/2)·g(ω)).
        set LSE' : Ω → ℝ := fun ω =>
          Real.sqrt (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
            - 1 - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω with hLSE'_def
        have h_LSE_eq : LSE =ᵐ[P] LSE' := by
          filter_upwards [h_rn_t, h_rn_0, h_f_nn] with ω hωt hω0 hω_nn
          change Real.sqrt ((curve t).rnDeriv P ω).toReal
                - Real.sqrt ((curve 0).rnDeriv P ω).toReal
                - (t / 2) * ((g : Ω → ℝ)) ω
                    * Real.sqrt ((curve 0).rnDeriv P ω).toReal
              = Real.sqrt (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
                - 1 - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω
          rw [hωt, hω0, ENNReal.toReal_one, Real.sqrt_one, mul_one,
              ENNReal.toReal_ofReal hω_nn]
        -- Pointwise bound: |LSE'(ω)| ≤ t² · M² / 2 a.e.
        have h_LSE_bound : ∀ᵐ ω ∂P, ‖LSE' ω‖ ≤ t ^ 2 * M ^ 2 / 2 := by
          filter_upwards [h_abs_g_le_M, h_f_nn] with ω hω_M hω_nn
          have hbound := dqm_general (t := t)
              (u := ((g : Lp ℝ 2 P) : Ω → ℝ) ω) hω_nn
          change |Real.sqrt (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
              - 1 - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω|
              ≤ t ^ 2 * M ^ 2 / 2
          calc |Real.sqrt (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
                  - 1 - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω|
              ≤ t ^ 2 * (((g : Lp ℝ 2 P) : Ω → ℝ) ω) ^ 2 / 2 := hbound
            _ ≤ t ^ 2 * M ^ 2 / 2 := by
                have h_g_sq_le : (((g : Lp ℝ 2 P) : Ω → ℝ) ω) ^ 2 ≤ M ^ 2 := by
                  have h_abs : |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ |M| := by
                    rw [abs_of_nonneg hM_nn]; exact hω_M
                  have := sq_le_sq.mpr h_abs
                  simpa [sq_abs] using this
                have ht2_nn : 0 ≤ t ^ 2 := sq_nonneg _
                have h_two_nn : (0 : ℝ) ≤ 2 := by norm_num
                exact div_le_div_of_nonneg_right
                        (mul_le_mul_of_nonneg_left h_g_sq_le ht2_nn) h_two_nn
        -- eLpNorm LSE 2 P ≤ ENNReal.ofReal (t²·M²/2) via eLpNorm_le_of_ae_bound.
        have h_LSE'_bound : eLpNorm LSE' 2 P ≤ ENNReal.ofReal (t ^ 2 * M ^ 2 / 2) := by
          have := eLpNorm_le_of_ae_bound (μ := P) (p := (2 : ℝ≥0∞)) h_LSE_bound
          have h_univ : P Set.univ = 1 := measure_univ
          rw [h_univ] at this
          have h_pow : (1 : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal⁻¹) = 1 := by
            rw [ENNReal.one_rpow]
          rw [h_pow, one_mul] at this
          exact this
        have h_LSE_bound_eLp : eLpNorm LSE 2 P ≤ ENNReal.ofReal (t ^ 2 * M ^ 2 / 2) := by
          rw [eLpNorm_congr_ae h_LSE_eq]; exact h_LSE'_bound
        -- (eLpNorm LSE 2 P).toReal ≤ t² · M² / 2.
        -- Goal: eLpNorm LSE 2 P / ofReal|t| ≤ ofReal(|t| · M² / 2).
        -- Use the bound eLpNorm LSE 2 P ≤ ofReal(t² · M² / 2) and divide.
        have hofreal_t_pos : 0 < ENNReal.ofReal |t| :=
          ENNReal.ofReal_pos.mpr ht_abs_pos
        have hofreal_t_ne_zero : ENNReal.ofReal |t| ≠ 0 := hofreal_t_pos.ne'
        have hofreal_t_ne_top : ENNReal.ofReal |t| ≠ ⊤ := ENNReal.ofReal_ne_top
        -- Algebraic identity: ofReal(t² · M² / 2) = ofReal|t| * ofReal(|t| · M² / 2).
        have h_t_M_split :
            ENNReal.ofReal (t ^ 2 * M ^ 2 / 2)
              = ENNReal.ofReal |t| * ENNReal.ofReal (|t| * M ^ 2 / 2) := by
          rw [← ENNReal.ofReal_mul ht_abs_pos.le]
          congr 1
          have hsq : t ^ 2 = |t| * |t| := by
            have := sq_abs t  -- |t|^2 = t^2
            nlinarith [this, sq_abs t]
          rw [hsq]; ring
        -- Use div_le_iff equivalence in ℝ≥0∞.
        rw [ENNReal.div_le_iff hofreal_t_ne_zero hofreal_t_ne_top]
        calc eLpNorm LSE 2 P
            ≤ ENNReal.ofReal (t ^ 2 * M ^ 2 / 2) := h_LSE_bound_eLp
          _ = ENNReal.ofReal |t| * ENNReal.ofReal (|t| * M ^ 2 / 2) := h_t_M_split
          _ = ENNReal.ofReal (|t| * M ^ 2 / 2) * ENNReal.ofReal |t| := by ring
  }

/-- Lemma 1 corollary: the score of `boundedDensityPath g hg` is `g`. -/
theorem boundedDensityPath_score
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) :
    (boundedDensityPath g hg).score = g := rfl

/-! ### Public helpers for the 1D LAN expansion route

These expose the `M` and `δ = 1/(M+1)` cutoffs from `boundedDensityPath`'s
internal `let`-bindings, plus the Radon-Nikodym density formula for the
curve and the explicit `eLpNorm` bound on the QMD residual that is
established inline in `boundedDensityPath`'s `qmd_limit` proof. -/

/-- Essential bound for `g` chosen via `Classical.choose` and clamped at
zero so that `0 ≤ essBound`. -/
noncomputable def IsEssBoundedMixtureScore.essBound
    {g : ↥(L2ZeroMean P)} (hg : IsEssBoundedMixtureScore g) : ℝ :=
  max 0 (Classical.choose hg)

lemma IsEssBoundedMixtureScore.essBound_nonneg
    {g : ↥(L2ZeroMean P)} (hg : IsEssBoundedMixtureScore g) :
    0 ≤ hg.essBound :=
  le_max_left _ _

lemma IsEssBoundedMixtureScore.essBound_spec
    {g : ↥(L2ZeroMean P)} (hg : IsEssBoundedMixtureScore g) :
    ∀ᵐ ω ∂P, |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ hg.essBound := by
  filter_upwards [Classical.choose_spec hg] with ω hω
  exact hω.trans (le_max_right _ _)

/-- Scaling preserves essential boundedness: if `g` is essentially bounded
in `L²₀(P)` then so is `s • g` for any real `s`, with bound `|s| · M`. -/
lemma IsEssBoundedMixtureScore.smul
    {g : ↥(L2ZeroMean P)} (hg : IsEssBoundedMixtureScore g) (s : ℝ) :
    IsEssBoundedMixtureScore (s • g) := by
  obtain ⟨M, hM⟩ := hg
  refine ⟨|s| * M, ?_⟩
  -- The Lp coercion of `(s • g : ↥(L2ZeroMean P))` equals `s • (g : Lp ℝ 2 P)`
  -- in `Lp`, hence a.e. equals `s · g(ω)`.
  have h_smul_ae :
      ((((s • g) : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] fun ω => s * ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by
    have h_coe : (((s • g) : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                 = s • (g : Lp ℝ 2 P) := by
      rfl
    rw [h_coe]
    filter_upwards [Lp.coeFn_smul s (g : Lp ℝ 2 P)] with ω hω
    simpa [Pi.smul_apply, smul_eq_mul] using hω
  filter_upwards [hM, h_smul_ae] with ω hω hsmul
  rw [hsmul]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)

/-- Addition preserves essential boundedness: if `g` and `h` are essentially
bounded in `L²₀(P)` then so is `g + h`, with bound `M_g + M_h`. -/
lemma IsEssBoundedMixtureScore.add
    {g h : ↥(L2ZeroMean P)} (hg : IsEssBoundedMixtureScore g)
    (hh : IsEssBoundedMixtureScore h) :
    IsEssBoundedMixtureScore (g + h) := by
  obtain ⟨Mg, hMg⟩ := hg
  obtain ⟨Mh, hMh⟩ := hh
  refine ⟨Mg + Mh, ?_⟩
  have h_add_ae :
      ((((g + h) : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] fun ω => ((g : Lp ℝ 2 P) : Ω → ℝ) ω
                        + ((h : Lp ℝ 2 P) : Ω → ℝ) ω := by
    have h_coe : (((g + h) : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                 = (g : Lp ℝ 2 P) + (h : Lp ℝ 2 P) := rfl
    rw [h_coe]
    filter_upwards [Lp.coeFn_add (g : Lp ℝ 2 P) (h : Lp ℝ 2 P)] with ω hω
    simpa [Pi.add_apply] using hω
  filter_upwards [hMg, hMh, h_add_ae] with ω hgω hhω hadd
  rw [hadd]
  exact (abs_add_le _ _).trans (add_le_add hgω hhω)

/-- Finite sums preserve essential boundedness. -/
lemma IsEssBoundedMixtureScore.finsetSum
    {ι : Type*} (s : Finset ι) (g : ι → ↥(L2ZeroMean P))
    (hg : ∀ i ∈ s, IsEssBoundedMixtureScore (g i)) :
    IsEssBoundedMixtureScore (∑ i ∈ s, g i) := by
  classical
  -- We induct on `s` with the hypothesis universally-quantified inside the motive.
  revert hg
  refine Finset.induction_on s ?_ ?_
  · intro _
    -- Empty sum = 0.
    refine ⟨0, ?_⟩
    have h0 : (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] (fun _ => (0 : ℝ)) :=
      Lp.coeFn_zero _ _ _
    filter_upwards [h0] with ω h0ω
    simp []
  · intro j t hjt ih hg
    rw [Finset.sum_insert hjt]
    have hgj : IsEssBoundedMixtureScore (g j) :=
      hg j (Finset.mem_insert_self j t)
    have ih' : IsEssBoundedMixtureScore (∑ i ∈ t, g i) :=
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    exact hgj.add ih'

/-- Essential bound for `g` (delegates to `IsEssBoundedMixtureScore.essBound`). -/
noncomputable def IsBoundedMixtureScore.essBound
    {g : ↥(L2ZeroMean P)} (hg : IsBoundedMixtureScore g) : ℝ :=
  hg.toEss.essBound

lemma IsBoundedMixtureScore.essBound_nonneg
    {g : ↥(L2ZeroMean P)} (hg : IsBoundedMixtureScore g) :
    0 ≤ hg.essBound :=
  hg.toEss.essBound_nonneg

lemma IsBoundedMixtureScore.essBound_spec
    {g : ↥(L2ZeroMean P)} (hg : IsBoundedMixtureScore g) :
    ∀ᵐ ω ∂P, |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ hg.essBound :=
  hg.toEss.essBound_spec

/-- Truncation radius `δ = 1/(essBound + 1)` for the `boundedDensityPath`
construction: the curve agrees with the affine mixture density
`1 + t·g` exactly when `|t| < truncRadius`. -/
noncomputable def boundedDensityPath_truncRadius
    {g : ↥(L2ZeroMean P)} (hg : IsEssBoundedMixtureScore g) : ℝ :=
  1 / (hg.essBound + 1)

lemma boundedDensityPath_truncRadius_pos
    {g : ↥(L2ZeroMean P)} (hg : IsEssBoundedMixtureScore g) :
    0 < boundedDensityPath_truncRadius hg := by
  unfold boundedDensityPath_truncRadius
  apply div_pos one_pos
  linarith [hg.essBound_nonneg]

/-- For `|t| < truncRadius`, `(boundedDensityPath g hg).curve t` equals
`P.withDensity (fun ω ↦ ENNReal.ofReal (1 + t·g(ω)))`. This is the
direct unfold of the `if`-branch in `boundedDensityPath`'s definition. -/
theorem boundedDensityPath_curve_eq_withDensity
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) {t : ℝ}
    (ht : |t| < boundedDensityPath_truncRadius hg) :
    (boundedDensityPath g hg).curve t =
      P.withDensity (fun ω => ENNReal.ofReal
        (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
  -- Unfold the `if`-then-else in the constructor body.
  change (if |t| < boundedDensityPath_truncRadius hg then
            P.withDensity (fun ω => ENNReal.ofReal
              (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω))
          else P) = _
  rw [if_pos ht]

/-- Radon–Nikodym derivative of `(boundedDensityPath g hg).curve t`
w.r.t. `P` for `|t| < truncRadius`: a.e. equals
`ENNReal.ofReal (1 + t·g(ω))`. -/
theorem boundedDensityPath_curve_rnDeriv
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) {t : ℝ}
    (ht : |t| < boundedDensityPath_truncRadius hg) :
    ((boundedDensityPath g hg).curve t).rnDeriv P
      =ᵐ[P] fun ω => ENNReal.ofReal
        (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω) := by
  have h_g_meas : AEMeasurable (((g : Lp ℝ 2 P) : Ω → ℝ)) P :=
    (Lp.aestronglyMeasurable (g : Lp ℝ 2 P)).aemeasurable
  have h_density_meas :
      AEMeasurable (fun ω => ENNReal.ofReal
        (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) P := by
    have : AEMeasurable
        (fun ω => 1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω) P :=
      ((aemeasurable_const).add ((aemeasurable_const).mul h_g_meas))
    exact this.ennreal_ofReal
  rw [boundedDensityPath_curve_eq_withDensity g hg ht]
  exact Measure.rnDeriv_withDensity₀ P h_density_meas

/-- The QMD residual for `boundedDensityPath g hg` at parameter `t`:
`√(p_t/p_0) - √(p_0/p_0) - (t/2)·g·√(p_0/p_0)` evaluated using the
`P`-RN-derivative form. With `p_0 = P` we have `√(p_0).rnDeriv P = 1`
a.e., so this reduces to `√(1+t·g) - 1 - (t/2)·g` a.e. -/
noncomputable def boundedDensityPath_residual
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g)
    (t : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt (((boundedDensityPath g hg).curve t).rnDeriv P ω).toReal
    - Real.sqrt (((boundedDensityPath g hg).curve 0).rnDeriv P ω).toReal
    - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω
        * Real.sqrt (((boundedDensityPath g hg).curve 0).rnDeriv P ω).toReal

/-- Pointwise sqrt-Taylor inequality: `|√(1+u) - 1 - u/2| ≤ u²/2` whenever
`0 ≤ 1+u`. Lifted from the inline `dqm_general` helper inside
`boundedDensityPath`'s `qmd_limit` body. -/
private lemma sqrt_one_add_residual_bound {t u : ℝ} (h_nn : 0 ≤ 1 + t * u) :
    |Real.sqrt (1 + t * u) - 1 - (t / 2) * u| ≤ t ^ 2 * u ^ 2 / 2 := by
  set s := Real.sqrt (1 + t * u) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s * s = 1 + t * u := Real.mul_self_sqrt h_nn
  have h_lhs_eq : s - 1 - (t / 2) * u = -((s - 1) ^ 2) / 2 := by
    have h_tu : t * u = s * s - 1 := by linarith [hs_sq]
    nlinarith [h_tu, sq_nonneg (s - 1)]
  rw [h_lhs_eq, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg _)]
  have h_step : (s - 1) ^ 2 ≤ t ^ 2 * u ^ 2 := by
    have h_tu_sq : t ^ 2 * u ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by
      have h_tu : t * u = s * s - 1 := by linarith [hs_sq]
      have hsq_factor : (s * s - 1) = (s - 1) * (s + 1) := by ring
      nlinarith [h_tu, hsq_factor, sq_nonneg ((s - 1) * (s + 1))]
    rw [h_tu_sq]
    have h_splus_one : (1 : ℝ) ≤ (s + 1) ^ 2 := by nlinarith [hs_nonneg]
    have h_lhs_nn : 0 ≤ (s - 1) ^ 2 := sq_nonneg _
    nlinarith [h_lhs_nn, h_splus_one]
  linarith [h_step]

/-- The QMD residual is in `MemLp 2 P` for `|t| < truncRadius`, with
explicit eLpNorm bound `≤ ENNReal.ofReal (t²·M²/2)` where
`M = hg.essBound`.

This is exactly the `h_LSE_bound_eLp` step inside `boundedDensityPath`'s
`qmd_limit` body, exposed publicly so the LAN expansion route can use it. -/
theorem boundedDensityPath_residual_eLpNorm_le
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) {t : ℝ}
    (ht : |t| < boundedDensityPath_truncRadius hg) :
    eLpNorm (boundedDensityPath_residual g hg t) 2 P
      ≤ ENNReal.ofReal (t ^ 2 * hg.essBound ^ 2 / 2) := by
  set M : ℝ := hg.essBound
  set δ : ℝ := boundedDensityPath_truncRadius hg
  have hM_nn : (0 : ℝ) ≤ M := hg.essBound_nonneg
  have hδ_pos : 0 < δ := boundedDensityPath_truncRadius_pos hg
  -- δ * M < 1 (since δ = 1/(M+1)).
  have hδM_lt_one : δ * M < 1 := by
    have hsplit : δ * M = M / (M + 1) := by
      change (1 / (M + 1)) * M = M / (M + 1)
      field_simp
    rw [hsplit, div_lt_one (by linarith : (0 : ℝ) < M + 1)]; linarith
  -- a.e. |g| ≤ M.
  have h_abs_g_le_M : ∀ᵐ ω ∂P,
      |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M := hg.essBound_spec
  -- a.e. 0 ≤ 1 + t·g.
  have h_f_nn : ∀ᵐ ω ∂P, 0 ≤ 1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by
    filter_upwards [h_abs_g_le_M] with ω hω
    have hbound : |t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω| < 1 := by
      rw [abs_mul]
      calc |t| * |((g : Lp ℝ 2 P) : Ω → ℝ) ω|
          ≤ |t| * M :=
            mul_le_mul_of_nonneg_left hω (abs_nonneg _)
        _ ≤ δ * M := mul_le_mul_of_nonneg_right (le_of_lt ht) hM_nn
        _ < 1 := hδM_lt_one
    linarith [(abs_lt.mp hbound).1]
  -- residual a.e. equals `√(1+t·g) - 1 - (t/2)·g`.
  have h_rn_t := boundedDensityPath_curve_rnDeriv g hg ht
  have h_rn_0 :
      ((boundedDensityPath g hg).curve 0).rnDeriv P =ᵐ[P]
      (fun _ => (1 : ℝ≥0∞)) := by
    have h_curve_0 : (boundedDensityPath g hg).curve 0 = P :=
      (boundedDensityPath g hg).curve_at_zero
    rw [h_curve_0]; exact Measure.rnDeriv_self P
  set RES' : Ω → ℝ := fun ω =>
    Real.sqrt (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
      - 1 - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω
  have h_RES_eq :
      boundedDensityPath_residual g hg t =ᵐ[P] RES' := by
    filter_upwards [h_rn_t, h_rn_0, h_f_nn] with ω hωt hω0 hω_nn
    change Real.sqrt (((boundedDensityPath g hg).curve t).rnDeriv P ω).toReal
          - Real.sqrt (((boundedDensityPath g hg).curve 0).rnDeriv P ω).toReal
          - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω
              * Real.sqrt (((boundedDensityPath g hg).curve 0).rnDeriv P ω).toReal
        = Real.sqrt (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
          - 1 - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω
    rw [hωt, hω0, ENNReal.toReal_one, Real.sqrt_one, mul_one,
        ENNReal.toReal_ofReal hω_nn]
  -- Pointwise bound on |RES'|.
  have h_RES'_bound : ∀ᵐ ω ∂P, ‖RES' ω‖ ≤ t ^ 2 * M ^ 2 / 2 := by
    filter_upwards [h_abs_g_le_M, h_f_nn] with ω hω_M hω_nn
    have hbound := sqrt_one_add_residual_bound (t := t)
        (u := ((g : Lp ℝ 2 P) : Ω → ℝ) ω) hω_nn
    change |Real.sqrt (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
          - 1 - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω|
        ≤ t ^ 2 * M ^ 2 / 2
    calc |Real.sqrt (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
            - 1 - (t / 2) * ((g : Lp ℝ 2 P) : Ω → ℝ) ω|
        ≤ t ^ 2 * (((g : Lp ℝ 2 P) : Ω → ℝ) ω) ^ 2 / 2 := hbound
      _ ≤ t ^ 2 * M ^ 2 / 2 := by
          have h_g_sq_le : (((g : Lp ℝ 2 P) : Ω → ℝ) ω) ^ 2 ≤ M ^ 2 := by
            have h_abs : |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ |M| := by
              rw [abs_of_nonneg hM_nn]; exact hω_M
            have := sq_le_sq.mpr h_abs
            simpa [sq_abs] using this
          have ht2_nn : 0 ≤ t ^ 2 := sq_nonneg _
          have h_two_nn : (0 : ℝ) ≤ 2 := by norm_num
          exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h_g_sq_le ht2_nn) h_two_nn
  -- eLpNorm RES' 2 P ≤ ENNReal.ofReal (t²·M²/2) via eLpNorm_le_of_ae_bound.
  have h_RES'_eLp : eLpNorm RES' 2 P ≤ ENNReal.ofReal (t ^ 2 * M ^ 2 / 2) := by
    have := eLpNorm_le_of_ae_bound (μ := P) (p := (2 : ℝ≥0∞)) h_RES'_bound
    have h_univ : P Set.univ = 1 := measure_univ
    rw [h_univ] at this
    have h_pow : (1 : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal⁻¹) = 1 := by
      rw [ENNReal.one_rpow]
    rw [h_pow, one_mul] at this
    exact this
  rw [eLpNorm_congr_ae h_RES_eq]
  exact h_RES'_eLp

theorem boundedDensityPath_residual_memLp
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) {t : ℝ}
    (ht : |t| < boundedDensityPath_truncRadius hg) :
    MemLp (boundedDensityPath_residual g hg t) 2 P := by
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable.
    unfold boundedDensityPath_residual
    have h_meas_t : AEStronglyMeasurable
        (fun ω => Real.sqrt (((boundedDensityPath g hg).curve t).rnDeriv P ω).toReal) P :=
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt).aestronglyMeasurable
    have h_meas_0 : AEStronglyMeasurable
        (fun ω => Real.sqrt (((boundedDensityPath g hg).curve 0).rnDeriv P ω).toReal) P :=
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt).aestronglyMeasurable
    have h_meas_g : AEStronglyMeasurable (((g : Lp ℝ 2 P) : Ω → ℝ)) P :=
      (Lp.aestronglyMeasurable (g : Lp ℝ 2 P))
    exact ((h_meas_t.sub h_meas_0).sub
      (((aestronglyMeasurable_const).mul h_meas_g).mul h_meas_0))
  · -- eLpNorm < ⊤.
    exact lt_of_le_of_lt (boundedDensityPath_residual_eLpNorm_le g hg ht)
      ENNReal.ofReal_lt_top

/-- **`P`-AE positive-and-finite Radon-Nikodym derivative**, valid for
all `t : ℝ`.

The rnDeriv `((boundedDensityPath g hg).curve t).rnDeriv P` is `P`-AE
strictly positive and finite for **every** `t : ℝ`. Two regimes:

* `|t| < truncRadius`: from `boundedDensityPath_curve_rnDeriv`, the
  rnDeriv equals `ENNReal.ofReal (1 + t·g(ω))` `P`-a.e. For `|t·g(ω)|
  < 1` (which follows from `|t|·essBound < truncRadius·essBound =
  M/(M+1) < 1`), the inner real is positive and finite.
* `|t| ≥ truncRadius`: the constructor's `if`-fallback gives
  `curve t = P`, so `rnDeriv = P.rnDeriv P = 1` `P`-a.e. -/
theorem boundedDensityPath_curve_rnDeriv_pos_finite_ae
    (g : ↥(L2ZeroMean P)) (hg : IsEssBoundedMixtureScore g) (t : ℝ) :
    ∀ᵐ ω ∂P,
      0 < ((boundedDensityPath g hg).curve t).rnDeriv P ω
      ∧ ((boundedDensityPath g hg).curve t).rnDeriv P ω < ⊤ := by
  by_cases ht : |t| < boundedDensityPath_truncRadius hg
  · -- Small-`t` regime: rnDeriv = ofReal(1 + t·g) AE; positive and finite.
    have h_rnDeriv := boundedDensityPath_curve_rnDeriv g hg ht
    have h_g_bd := hg.essBound_spec
    filter_upwards [h_rnDeriv, h_g_bd] with ω h_eq h_g
    set M : ℝ := hg.essBound with hM_def
    have hM_nn : 0 ≤ M := hg.essBound_nonneg
    have h_density_pos : 0 < 1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by
      have h_abs_le : |t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ |t| * M := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left h_g (abs_nonneg _)
      have h_tM_le : |t| * M ≤ boundedDensityPath_truncRadius hg * M :=
        mul_le_mul_of_nonneg_right ht.le hM_nn
      have h_δM : boundedDensityPath_truncRadius hg * M < 1 := by
        unfold boundedDensityPath_truncRadius
        rw [show (1 : ℝ) / (M + 1) * M = M / (M + 1) by ring]
        rw [div_lt_one (by linarith : (0 : ℝ) < M + 1)]
        linarith
      have h_abs_lt_one : |t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω| < 1 :=
        lt_of_le_of_lt (h_abs_le.trans h_tM_le) h_δM
      have h_neg_abs : -|t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω|
          ≤ t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω := neg_abs_le _
      linarith
    refine ⟨?_, ?_⟩
    · rw [h_eq]; exact ENNReal.ofReal_pos.mpr h_density_pos
    · rw [h_eq]; exact ENNReal.ofReal_lt_top
  · -- Large-`t` regime: curve t = P (else branch of the `if` in
    -- `boundedDensityPath`); rnDeriv P P = 1 a.e.
    have h_curve_P : (boundedDensityPath g hg).curve t = P := by
      change (if |t| < boundedDensityPath_truncRadius hg then
                P.withDensity (fun ω => ENNReal.ofReal
                  (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω))
              else P) = P
      rw [if_neg ht]
    rw [h_curve_P]
    filter_upwards [P.rnDeriv_self] with ω hω
    rw [hω]
    exact ⟨zero_lt_one, ENNReal.one_lt_top⟩

/-- Lemma 1 corollary (eventually-form): on a neighborhood of `0` in
`(0, ∞)`, the curve agrees with the convex mixture
`(1−t)·P + t·Q` where `Q := P.withDensity (1 + g)`.

This identification is the bridge between the QMD-curve-based
pathwise-differentiability route (`PathwiseDifferentiableAt` over
`QMDPath`) and the mixture-Gâteaux route
(`IsMixtureGateauxRepresenter` over `(1−t)·P + t·Q`) inside the
proof of `gateaux_representer_eq_pathwise_derivative`.

Eventually-form (rather than `0 < t < 1`) because the construction
uses an `|t| < δ` cutoff with `δ` depending on `g`'s essential
bound; `eventually` is exactly what `Tendsto.congr'` consumes. -/
theorem boundedDensityPath_curve_eq_mixture_eventually
    (g : ↥(L2ZeroMean P)) (hg : IsBoundedMixtureScore g) :
    ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (boundedDensityPath g hg.toEss).curve t =
        ENNReal.ofReal (1 - t) • P
          + ENNReal.ofReal t • P.withDensity (fun ω =>
              ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
  -- Reconstruct M and δ from the constructor body.
  set M : ℝ := max 0 (Classical.choose hg.1) with hM_def
  set δ : ℝ := 1 / (M + 1) with hδ_def
  have hM_nn : (0 : ℝ) ≤ M := le_max_left _ _
  have hδ_pos : (0 : ℝ) < δ := by
    change 0 < 1 / (M + 1); apply div_pos one_pos; linarith
  have hδ_le_one : δ ≤ 1 := by
    change 1 / (M + 1) ≤ 1
    rw [div_le_one (by linarith : (0 : ℝ) < M + 1)]; linarith
  -- |g ω| ≤ M almost everywhere.
  have h_abs_g_le_M : ∀ᵐ ω ∂P, |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M := by
    have hChoose : ∀ᵐ ω ∂P,
        |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ Classical.choose hg.1 :=
      Classical.choose_spec hg.1
    filter_upwards [hChoose] with ω hω
    exact hω.trans (le_max_right _ _)
  -- The eventually-set: Set.Ioo 0 δ ∈ 𝓝[>] 0.
  have h_nhds : Set.Ioo (0 : ℝ) δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio δ, Iio_mem_nhds hδ_pos, ?_⟩
    intro x hx
    exact ⟨hx.2, hx.1⟩
  -- Now show ∀ t ∈ Set.Ioo 0 δ, the equation holds.
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo 0 δ, h_nhds, ?_⟩
  intro t ht
  obtain ⟨ht_pos, ht_lt_δ⟩ := ht
  have ht_nn : (0 : ℝ) ≤ t := le_of_lt ht_pos
  have ht_le_one : t ≤ 1 := le_of_lt (lt_of_lt_of_le ht_lt_δ hδ_le_one)
  have ht_abs : |t| < δ := by rw [abs_of_pos ht_pos]; exact ht_lt_δ
  -- Unfold curve t via the if-then-else branch.
  have h_curve_t :
      (boundedDensityPath g hg.toEss).curve t =
        P.withDensity (fun ω =>
          ENNReal.ofReal (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
    change (if |t| < δ then
            P.withDensity (fun ω => ENNReal.ofReal
              (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω))
          else P) = _
    rw [if_pos ht_abs]
  rw [h_curve_t]
  -- Pointwise mixture decomposition (a.e. via g ≥ -1).
  have h_g_ge : ∀ᵐ ω ∂P, -1 ≤ ((g : Lp ℝ 2 P) : Ω → ℝ) ω := hg.2
  have h_density_ae :
      (fun ω => ENNReal.ofReal (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω))
        =ᵐ[P]
      (fun ω => ENNReal.ofReal (1 - t) +
        ENNReal.ofReal t * ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
    filter_upwards [h_g_ge] with ω hω
    exact AsymptoticStatistics.ForMathlib.MassMethodUtilities.ENNReal_ofReal_mixture
      ht_nn ht_le_one hω
  rw [MeasureTheory.withDensity_congr_ae h_density_ae]
  -- Decompose the sum-density via withDensity_add_left.
  -- The "left" function is constant `ENNReal.ofReal (1-t)` (measurable).
  have h_meas_const : Measurable (fun _ : Ω => ENNReal.ofReal (1 - t)) :=
    measurable_const
  have h_split :
      (fun ω => ENNReal.ofReal (1 - t) +
        ENNReal.ofReal t * ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω))
      = (fun _ => ENNReal.ofReal (1 - t)) +
        (fun ω => ENNReal.ofReal t *
          ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
    funext ω; rfl
  rw [h_split, MeasureTheory.withDensity_add_left h_meas_const]
  -- Constant-density piece: P.withDensity (fun _ => c) = c • P.
  rw [MeasureTheory.withDensity_const]
  -- Scalar-multiple-density piece: P.withDensity (c • f) = c • P.withDensity f.
  -- First express the second density as a smul.
  have h_smul_eq :
      (fun ω => ENNReal.ofReal t *
        ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω))
      = (ENNReal.ofReal t) •
        (fun ω => ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
    funext ω
    change ENNReal.ofReal t *
        ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
      = ENNReal.ofReal t •
        ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)
    rw [smul_eq_mul]
  rw [h_smul_eq]
  -- `withDensity_smul'` requires only `r ≠ ∞`, no measurability of `f`.
  rw [MeasureTheory.withDensity_smul' _ _ ENNReal.ofReal_ne_top]

/-- Lemma 2 of `ref/mass/mass.tex` (Density of bounded scores).

The linear span of `IsBoundedMixtureScore` is dense in `L²₀(P)`.

**Mathematical sketch.** Let `f ∈ L²₀(P)` be arbitrary. We exhibit a
sequence `tₙ ∈ span(B)` with `tₙ → f` in L².

*Stage A — density of bounded ∩ L²₀ in L²₀.* For each `n`, pick a
simple function `sₙ` with `‖f − sₙ‖_{L²} < 1/(n+1)`
(`MemLp.exists_simpleFunc_eLpNorm_sub_lt`). Simple functions take
finitely many values, so each `sₙ` is bounded pointwise. Recenter
`tₙ := sₙ − cₙ · 1` where `cₙ := ∫ sₙ dP`. Then `tₙ ∈ L²₀(P) ∩ L^∞(P)`
(mean-zero by construction; bounded by `‖sₙ‖_∞ + |cₙ|`).

*Stage B — bounded ∩ L²₀ ⊆ span(B).* For an essentially bounded
`h ∈ L²₀(P)` with bound `M₀`, set `M := |M₀| + 1 > 0` and
`g := (1/M) · h`. Then `|g| ≤ 1` a.e., hence `g ≥ -1` a.e., hence
`g ∈ B`. Therefore `h = M · g ∈ span(B)`.

*Convergence via Pythagoras.* The recentered map `s ↦ s − (∫s dP) · 1`
is the orthogonal projection of `Lp ℝ 2 P` onto `L²₀(P)` (since
`L²₀(P) = ker⟨1, ·⟩ = (span{1})ᗮ`). Decomposing
`sₙ − f = (tₙ − f) + (cₙ · 1)` into orthogonal summands — the first
in `L²₀(P)`, the second in `(L²₀)ᗮ` — Pythagoras yields
  `‖tₙ − f‖² ≤ ‖tₙ − f‖² + ‖cₙ · 1‖² = ‖sₙ − f‖² < 1/(n+1)²`.
So `‖tₙ − f‖ ≤ 1/(n+1) → 0`. -/
theorem bounded_score_span_dense :
    (Submodule.span ℝ
        {g : ↥(L2ZeroMean P) | IsBoundedMixtureScore g}).topologicalClosure
      = ⊤ := by
  set B : Set ↥(L2ZeroMean P) := {g | IsBoundedMixtureScore g} with hBdef
  -- ===========================================================================
  -- Proof structure (high-level natural-language summary):
  --
  -- We need every f ∈ L²₀(P) to lie in the closure of span(B).
  --
  -- bounded h ∈ L²₀(P) is in span(B). Witness: rescale h by 1/(|‖h‖_∞|+1)
  -- so |g| ≤ 1, hence g ≥ -1 a.e., so g ∈ B; recover h = M • g.
  --
  --   • Use MemLp.exists_simpleFunc_eLpNorm_sub_lt to get simple
  --     functions sₙ with ‖f − sₙ‖_{L²} < 1/(n+1).
  --   • Each sₙ is pointwise bounded (Finset sup over its finite range).
  --   • Recenter: tₙ := sₙ − cₙ · 1 where cₙ := ∫ sₙ dP. Then tₙ is
  --     mean-zero (in L²₀(P)) and still bounded.
  --   • Convergence: the map s ↦ s − (∫s dP) · 1 is the orthogonal
  --     projection onto L²₀(P) (because L²₀(P) = ker⟨1, ·⟩ is the
  --     orthogonal complement of span{1}). So
  --       sₙ − f = (tₙ − f) + (cₙ · 1)
  --     is an orthogonal decomposition; Pythagoras gives
  --       ‖tₙ − f‖² ≤ ‖sₙ − f‖² < 1/(n+1)² → 0.
  -- ===========================================================================
  -- For h ∈ L²₀(P) essentially bounded by some M₀, scale by M := |M₀|+1
  -- so g := (1/M)·h has |g| ≤ 1 a.e., hence g ≥ -1 a.e., so g ∈ B.
  -- Then h = M • g ∈ span B.
  have stageB :
      ∀ (h : ↥(L2ZeroMean P)),
        (∃ M : ℝ, ∀ᵐ ω ∂P, |((h : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M) →
        h ∈ Submodule.span ℝ B := by
    intro h ⟨M₀, hM₀⟩
    set M : ℝ := |M₀| + 1 with hM_def
    have hM_pos : (0 : ℝ) < M := by
      have : (0 : ℝ) ≤ |M₀| := abs_nonneg _
      linarith
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    have hM_abs_le : ∀ᵐ ω ∂P, |((h : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ M := by
      filter_upwards [hM₀] with ω hω
      have h0 : M₀ ≤ |M₀| := le_abs_self _
      linarith
    set g : ↥(L2ZeroMean P) := (1 / M) • h with hg_def
    have hg_coe_ae :
        ((g : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
          fun ω => (1 / M) * ((h : Lp ℝ 2 P) : Ω → ℝ) ω := by
      have hsmul :
          ((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) = (1 / M) • (h : Lp ℝ 2 P) := rfl
      rw [hsmul]
      filter_upwards [Lp.coeFn_smul (1 / M) (h : Lp ℝ 2 P)] with ω hω
      simpa [Pi.smul_apply, smul_eq_mul] using hω
    have hg_abs_le_one : ∀ᵐ ω ∂P, |((g : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ 1 := by
      filter_upwards [hg_coe_ae, hM_abs_le] with ω hg_eq h_abs
      rw [hg_eq, abs_mul, abs_of_pos (one_div_pos.mpr hM_pos)]
      have h_le : (1 / M) * |((h : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ (1 / M) * M :=
        mul_le_mul_of_nonneg_left h_abs (le_of_lt (one_div_pos.mpr hM_pos))
      rwa [div_mul_cancel₀ 1 hM_ne] at h_le
    have hg_lb : ∀ᵐ ω ∂P, -1 ≤ ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by
      filter_upwards [hg_abs_le_one] with ω hω
      have := neg_le_of_abs_le hω
      linarith
    have hg_mem : g ∈ B := ⟨⟨1, hg_abs_le_one⟩, hg_lb⟩
    have hg_span : g ∈ Submodule.span ℝ B := Submodule.subset_span hg_mem
    have h_eq : h = M • g := by
      change h = M • ((1 / M) • h)
      rw [smul_smul, mul_one_div_cancel hM_ne, one_smul]
    rw [h_eq]
    exact Submodule.smul_mem _ M hg_span
  -- Closure: simpleFunc-density + recenter argument.
  -- Strategy: get s_n simpleFuncs → f in Lp. Each s_n is bounded
  -- (simpleFunc takes finitely many values). Recenter:
  -- t_n := s_n - (∫s_n dP) · oneL2P. Then t_n ∈ L²₀ ∩ L^∞,
  -- and ‖t_n - f‖ ≤ ‖s_n - f‖ + |c_n| with c_n → 0 (because L²
  -- convergence on probability ⇒ L¹ convergence ⇒ ∫ s_n → ∫ f = 0).
  apply Submodule.eq_top_iff'.mpr
  intro f
  -- Show f ∈ topologicalClosure.
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      mem_closure_iff_seq_limit]
  -- Approach: simple-function approximation + recentering by integral.
  -- For each n, get a simple function `sn : Ω →ₛ ℝ` with
  -- `eLpNorm (f.coeFn - sn) 2 P < 1/(n+1)`. Each `sn` is essentially
  -- bounded (it takes finitely many values). Define the centered
  -- raw function `tn ω := sn ω - cn` where `cn := ∫ sn dP`. Then
  -- `tn` is a.e. bounded, in L², mean-zero, hence `tn ∈ L²₀(P)`,
  -- inequality + Cauchy–Schwarz on a probability measure gives
  -- `‖tn - f.coeFn‖_{L²} ≤ ‖sn - f.coeFn‖_{L²} + |cn| ≤ 2/(n+1) → 0`.
  -- Step 1: extract a sequence of simple functions approximating f.coeFn in L².
  have hf_memLp : MemLp ((f : Lp ℝ 2 P) : Ω → ℝ) 2 P := Lp.memLp _
  have h_eps_ne : ∀ n : ℕ, ((1 : ℝ≥0∞) / (n + 1)) ≠ 0 := by
    intro n
    apply ENNReal.div_ne_zero.mpr ⟨one_ne_zero, ?_⟩
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩
  have h_simpleFunc :
      ∀ n : ℕ, ∃ g : MeasureTheory.SimpleFunc Ω ℝ,
        eLpNorm (((f : Lp ℝ 2 P) : Ω → ℝ) - ⇑g) 2 P < (1 : ℝ≥0∞) / (n + 1)
        ∧ MemLp (g : Ω → ℝ) 2 P := by
    intro n
    exact hf_memLp.exists_simpleFunc_eLpNorm_sub_lt
      (by simp : (2 : ℝ≥0∞) ≠ ∞) (h_eps_ne n)
  -- Pick the simple-function sequence and its memLp / eLpNorm bounds.
  let sn : ℕ → MeasureTheory.SimpleFunc Ω ℝ := fun n => Classical.choose (h_simpleFunc n)
  have hsn_spec : ∀ n,
      eLpNorm (((f : Lp ℝ 2 P) : Ω → ℝ) - ⇑(sn n)) 2 P < (1 : ℝ≥0∞) / (n + 1)
      ∧ MemLp ((sn n) : Ω → ℝ) 2 P := fun n =>
    Classical.choose_spec (h_simpleFunc n)
  have hsn_eLp : ∀ n,
      eLpNorm (((f : Lp ℝ 2 P) : Ω → ℝ) - ⇑(sn n)) 2 P < (1 : ℝ≥0∞) / (n + 1) :=
    fun n => (hsn_spec n).1
  have hsn_memLp : ∀ n, MemLp ((sn n) : Ω → ℝ) 2 P :=
    fun n => (hsn_spec n).2
  -- Step 2: each sn is essentially (in fact pointwise) bounded by some Mn.
  -- We use Ω nonempty (forced by IsProbabilityMeasure P) so (sn n).range is
  -- nonempty, then take the sup of |·| on the finite range.
  have hΩ_ne : Nonempty Ω := MeasureTheory.nonempty_of_isProbabilityMeasure P
  have hsn_bound : ∀ n, ∃ M : ℝ, ∀ ω : Ω, |(sn n) ω| ≤ M := by
    intro n
    set s := sn n
    have h_ne : s.range.Nonempty := ⟨s (Classical.arbitrary Ω), s.mem_range_self _⟩
    refine ⟨s.range.sup' h_ne (fun r => |r|), ?_⟩
    intro ω
    exact Finset.le_sup' (fun r => |r|) (s.mem_range_self ω)
  -- Step 3: define cn := ∫ sn dP and the centered raw function.
  -- cn is well-defined since simple functions on a probability measure are
  -- integrable (bounded with finite measure).
  let cn : ℕ → ℝ := fun n => ∫ ω, ((sn n) : Ω → ℝ) ω ∂P
  -- The centered raw function tn ω := sn ω - cn. (Essentially bounded.)
  let tn_raw : ℕ → Ω → ℝ := fun n ω => ((sn n) : Ω → ℝ) ω - cn n
  -- Step 4: tn_raw n ∈ L² and mean-zero, so it lifts to L²₀(P).
  have htn_memLp : ∀ n, MemLp (tn_raw n) 2 P := by
    intro n
    have h_const : MemLp (fun _ : Ω => cn n) 2 P := memLp_const _
    exact (hsn_memLp n).sub h_const
  have h_sn_int : ∀ n, Integrable ((sn n) : Ω → ℝ) P :=
    fun n => (hsn_memLp n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htn_zero_int : ∀ n, ∫ ω, tn_raw n ω ∂P = 0 := by
    intro n
    change ∫ ω, ((sn n) : Ω → ℝ) ω - cn n ∂P = 0
    rw [integral_sub (h_sn_int n) (integrable_const _), integral_const]
    simp [cn]
  -- Step 5: lift to ↥(L2ZeroMean P).
  have htn_lp_memZero : ∀ n,
      (htn_memLp n).toLp (tn_raw n) ∈ L2ZeroMean P := by
    intro n
    change (htn_memLp n).toLp (tn_raw n) ∈
        LinearMap.ker (integralL2 P).toLinearMap
    rw [LinearMap.mem_ker]
    change integralL2 P ((htn_memLp n).toLp (tn_raw n)) = 0
    -- integralL2 P (toLp f) = ∫ f dP, which is 0.
    have h_unfold :
        integralL2 P ((htn_memLp n).toLp (tn_raw n))
          = ∫ ω, tn_raw n ω ∂P := by
      change ⟪oneL2 P, (htn_memLp n).toLp (tn_raw n)⟫_ℝ = _
      rw [MeasureTheory.L2.inner_def]
      have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      have h_f_ae : (((htn_memLp n).toLp (tn_raw n) : Lp ℝ 2 P) : Ω → ℝ)
            =ᵐ[P] tn_raw n :=
        MemLp.coeFn_toLp (htn_memLp n)
      apply integral_congr_ae
      filter_upwards [h_one_ae, h_f_ae] with a ha hb
      have hcomm :
          ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
            (((htn_memLp n).toLp (tn_raw n) : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
            = (((htn_memLp n).toLp (tn_raw n) : Lp ℝ 2 P) : Ω → ℝ) a
                * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
      rw [hcomm, ha, hb]
      ring
    rw [h_unfold, htn_zero_int]
  let tn : ℕ → ↥(L2ZeroMean P) := fun n =>
    ⟨(htn_memLp n).toLp (tn_raw n), htn_lp_memZero n⟩
  have htn_in_span : ∀ n, tn n ∈ Submodule.span ℝ B := by
    intro n
    apply stageB
    obtain ⟨Mn, hMn⟩ := hsn_bound n
    refine ⟨Mn + |cn n|, ?_⟩
    have h_coeFn :
        (((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] tn_raw n :=
      MemLp.coeFn_toLp (htn_memLp n)
    filter_upwards [h_coeFn] with ω hω
    rw [hω]
    change |((sn n) : Ω → ℝ) ω - cn n| ≤ Mn + |cn n|
    calc |((sn n) : Ω → ℝ) ω - cn n|
        ≤ |((sn n) : Ω → ℝ) ω| + |cn n| := abs_sub _ _
      _ ≤ Mn + |cn n| := by linarith [hMn ω]
  -- ===========================================================================
  -- Step 7: convergence `Tendsto tn atTop (𝓝 f)` via Pythagoras.
  --
  -- Mathematical content:
  --   • Lift sₙ : Ω →ₛ ℝ to sn_lp n : Lp ℝ 2 P via MemLp.toLp.
  --   • Show in Lp the algebraic identity
  --       sn_lp n  =  ↑(tn n)  +  cₙ • oneL2 P                 (h_decomp)
  --     i.e. sₙ = tₙ + cₙ · 1, the recentering identity lifted to Lp
  --     via Lp.coeFn_add + Lp.coeFn_smul + MemLp.coeFn_toLp.
  --   • Subtracting ↑f gives the orthogonal decomposition
  --       sn_lp n − ↑f  =  (↑(tn n) − ↑f)  +  (cₙ • oneL2 P).
  --   • The two summands are orthogonal:
  --       - ↑(tn n) − ↑f ∈ L²₀(P) since both ↑(tn n) and ↑f are in
  --         L²₀(P) = ker⟨oneL2 P, ·⟩.
  --       - cₙ • oneL2 P is a scalar multiple of oneL2 P.
  --       - The inner product of an L²₀-vector against any scalar
  --         multiple of oneL2 P vanishes (h_orth).
  --   • Pythagoras (norm_add_sq_eq_norm_sq_add_norm_sq_real) on the
  --     orthogonal pair gives
  --       ‖↑(tn n) − ↑f‖² + ‖cₙ • oneL2 P‖² = ‖sn_lp n − ↑f‖²
  --     hence ‖↑(tn n) − ↑f‖² ≤ ‖sn_lp n − ↑f‖²; taking square roots
  --     (abs_le_of_sq_le_sq', both norms nonneg) yields
  --       ‖↑(tn n) − ↑f‖ ≤ ‖sn_lp n − ↑f‖.
  --   • The Lp norm ‖sn_lp n − ↑f‖ equals (eLpNorm (f.coeFn − sₙ) 2 P).toReal
  --     up to AE-rewrites + a sign flip (eLpNorm_neg).
  --   • By construction `eLpNorm (f.coeFn − sₙ) 2 P < 1/(n+1)`; cast to
  --     ℝ via ENNReal.toReal_lt_toReal (with finiteness witnesses).
  --   • The subtype norm `‖tn n − f‖` in `↥(L2ZeroMean P)` equals the
  --     ambient `‖↑(tn n) − ↑f‖` by `rfl` (subtype norm = restricted norm).
  --   • Squeeze with `tendsto_one_div_add_atTop_nhds_zero_nat` closes
  --     the Tendsto.
  -- ===========================================================================
  refine ⟨tn, htn_in_span, ?_⟩
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  -- Step 7.0: ∫ f.coeFn dP = 0 (f ∈ L²₀(P) reduces ⟨oneL2, f⟩ = 0 to ∫ f dP = 0).
  have h_int_f_zero : ⟪oneL2 P, (f : Lp ℝ 2 P)⟫_ℝ = 0 := by
    have hf_mem : (f : Lp ℝ 2 P) ∈ L2ZeroMean P := f.2
    change (f : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at hf_mem
    rw [LinearMap.mem_ker] at hf_mem
    exact hf_mem
  -- Lift each sn n to an Lp element.
  let sn_lp : ℕ → Lp ℝ 2 P := fun n => (hsn_memLp n).toLp ⇑(sn n)
  -- Inner product ⟨oneL2, sn_lp n⟩ = cn n.
  have h_inner_sn : ∀ n, ⟪oneL2 P, sn_lp n⟫_ℝ = cn n := by
    intro n
    rw [MeasureTheory.L2.inner_def]
    have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_sn_ae : ((sn_lp n : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] ⇑(sn n) :=
      MemLp.coeFn_toLp (hsn_memLp n)
    change ∫ ω, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
              ((sn_lp n : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ ∂P = cn n
    rw [show ∫ ω, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
              ((sn_lp n : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ ∂P
        = ∫ ω, ((sn n) : Ω → ℝ) ω ∂P from ?_]
    apply integral_congr_ae
    filter_upwards [h_one_ae, h_sn_ae] with ω h1 hsn
    have hcomm :
        ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
          ((sn_lp n : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ
          = ((sn_lp n : Lp ℝ 2 P) : Ω → ℝ) ω
              * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω := rfl
    rw [hcomm, h1, hsn, mul_one]
  -- Decomposition: sn_lp n = ↑(tn n) + cn n • oneL2 P (Lp equality via ae).
  have h_decomp : ∀ n,
      sn_lp n = ((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) + cn n • oneL2 P := by
    intro n
    apply Lp.ext
    have h_tn_ae :
        (((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] tn_raw n :=
      MemLp.coeFn_toLp (htn_memLp n)
    have h_sn_ae : ((sn_lp n : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] ⇑(sn n) :=
      MemLp.coeFn_toLp (hsn_memLp n)
    have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_add_ae := Lp.coeFn_add ((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
        (cn n • oneL2 P)
    have h_smul_ae := Lp.coeFn_smul (cn n) (oneL2 P)
    filter_upwards [h_tn_ae, h_sn_ae, h_one_ae, h_add_ae, h_smul_ae]
      with ω h_tn h_sn h_one h_add h_smul
    rw [h_sn]
    rw [h_add]
    simp only [Pi.add_apply]
    rw [h_tn, h_smul]
    simp only [Pi.smul_apply]
    rw [h_one]
    change ((sn n) : Ω → ℝ) ω
        = ((sn n) ω - cn n) + cn n • (1 : ℝ)
    rw [smul_eq_mul, mul_one]
    ring
  -- Orthogonality: ⟨↑(tn n) - ↑f, cn n • oneL2 P⟩ = 0.
  have h_orth : ∀ n,
      ⟪((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) - (f : Lp ℝ 2 P),
        cn n • oneL2 P⟫_ℝ = 0 := by
    intro n
    -- ⟨a - b, c • d⟩ = c * ⟨a - b, d⟩ = c * (⟨a, d⟩ - ⟨b, d⟩).
    rw [inner_smul_right]
    -- Both ⟨↑(tn n), oneL2 P⟩ and ⟨↑f, oneL2 P⟩ are 0 (mem L²₀ ⇒ kernel of integralL2).
    have h_tn_mem : ((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) ∈ L2ZeroMean P :=
      (tn n).2
    change ((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
        ∈ LinearMap.ker (integralL2 P).toLinearMap at h_tn_mem
    rw [LinearMap.mem_ker] at h_tn_mem
    have h_inner_tn : ⟪oneL2 P, ((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P)⟫_ℝ = 0 :=
      h_tn_mem
    rw [inner_sub_left]
    -- ⟨tn, oneL2⟩ = ⟨oneL2, tn⟩ via real_inner_comm (oneL2 P) tn.
    rw [real_inner_comm (oneL2 P) (((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P)),
        h_inner_tn,
        real_inner_comm (oneL2 P) ((f : Lp ℝ 2 P)),
        h_int_f_zero]
    ring
  -- Pythagoras gives the bound on ‖↑(tn n) - ↑f‖.
  have h_norm_le_sn_lp : ∀ n,
      ‖((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) - (f : Lp ℝ 2 P)‖
        ≤ ‖sn_lp n - (f : Lp ℝ 2 P)‖ := by
    intro n
    -- sn_lp n - ↑f = (↑(tn n) - ↑f) + (cn n • oneL2 P).
    have h_sub_eq :
        sn_lp n - (f : Lp ℝ 2 P)
          = (((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) - (f : Lp ℝ 2 P))
              + cn n • oneL2 P := by
      rw [h_decomp n]; abel
    rw [h_sub_eq]
    -- Pythagoras on the orthogonal pair.
    have h_pyth :=
      norm_add_sq_eq_norm_sq_add_norm_sq_real (h_orth n)
    -- ‖a‖² ≤ ‖a‖² + ‖b‖² = ‖a + b‖² (h_pyth uses * form, convert via pow_two).
    have h_le_sq :
        ‖((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) - (f : Lp ℝ 2 P)‖ ^ 2
          ≤ ‖(((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) - (f : Lp ℝ 2 P))
              + cn n • oneL2 P‖ ^ 2 := by
      rw [pow_two, pow_two, h_pyth]
      have hb : 0 ≤
          ‖(cn n : ℝ) • oneL2 P‖ * ‖(cn n : ℝ) • oneL2 P‖ :=
        mul_self_nonneg _
      linarith
    -- Take sqrt: ‖a‖ ≤ ‖a + b‖ via abs_le_of_sq_le_sq'.
    exact (abs_le_of_sq_le_sq' h_le_sq (norm_nonneg _)).2
  -- ‖sn_lp n - ↑f‖ in Lp = (eLpNorm (sn_lp n - ↑f).coeFn 2 P).toReal
  --                      = (eLpNorm (sn n - ↑f.coeFn) 2 P).toReal     (via h_sn_ae)
  --                      = (eLpNorm (↑f.coeFn - sn n) 2 P).toReal     (via eLpNorm_neg).
  have h_sn_lp_norm : ∀ n,
      ‖sn_lp n - (f : Lp ℝ 2 P)‖
        = (eLpNorm (((f : Lp ℝ 2 P) : Ω → ℝ) - ⇑(sn n)) 2 P).toReal := by
    intro n
    rw [Lp.norm_def]
    congr 1
    have h_diff_ae :
        ((sn_lp n - (f : Lp ℝ 2 P) : Lp ℝ 2 P) : Ω → ℝ)
          =ᵐ[P] fun ω => -(((f : Lp ℝ 2 P) : Ω → ℝ) ω - ((sn n) : Ω → ℝ) ω) := by
      filter_upwards [Lp.coeFn_sub (sn_lp n) (f : Lp ℝ 2 P),
          MemLp.coeFn_toLp (hsn_memLp n)] with ω h_sub h_sn
      rw [h_sub]
      simp only [Pi.sub_apply]
      rw [h_sn]
      ring
    rw [eLpNorm_congr_ae h_diff_ae]
    have h_neg_eq :
        (fun ω : Ω => -(((f : Lp ℝ 2 P) : Ω → ℝ) ω - ((sn n) : Ω → ℝ) ω))
          = -((((f : Lp ℝ 2 P) : Ω → ℝ) - ⇑(sn n))) := by
      funext ω; simp
    rw [h_neg_eq, eLpNorm_neg]
  -- ‖tn n - f‖ = ‖↑(tn n) - ↑f‖ (subtype norm = restricted Lp norm).
  have h_subtype_norm : ∀ n,
      ‖tn n - f‖
        = ‖((tn n : ↥(L2ZeroMean P)) : Lp ℝ 2 P) - (f : Lp ℝ 2 P)‖ :=
    fun _ => rfl
  -- Combine: ‖tn n - f‖ ≤ (eLpNorm ...).toReal < 1/(n+1).
  have h_top : ∀ n, eLpNorm (((f : Lp ℝ 2 P) : Ω → ℝ) - ⇑(sn n)) 2 P ≠ ⊤ := by
    intro n
    exact (hf_memLp.sub (hsn_memLp n)).eLpNorm_lt_top.ne
  have h_one_top : ∀ n : ℕ, ((1 : ℝ≥0∞) / (n + 1)) ≠ ⊤ := by
    intro n
    apply ENNReal.div_ne_top ENNReal.one_ne_top
    exact_mod_cast Nat.succ_ne_zero n
  have h_eLp_lt_R : ∀ n,
      (eLpNorm (((f : Lp ℝ 2 P) : Ω → ℝ) - ⇑(sn n)) 2 P).toReal
        < (((1 : ℝ≥0∞) / (n + 1)).toReal) := by
    intro n
    exact (ENNReal.toReal_lt_toReal (h_top n) (h_one_top n)).mpr (hsn_eLp n)
  have h_norm_le : ∀ n,
      ‖tn n - f‖ ≤ (((1 : ℝ≥0∞) / (n + 1)).toReal) := by
    intro n
    rw [h_subtype_norm]
    exact (h_norm_le_sn_lp n).trans
      ((h_sn_lp_norm n) ▸ le_of_lt (h_eLp_lt_R n))
  -- Final squeeze.
  have h_to_zero : Tendsto (fun n : ℕ => (((1 : ℝ≥0∞) / (n + 1)).toReal))
      atTop (𝓝 0) := by
    have h_inv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine h_inv.congr' ?_
    refine Filter.Eventually.of_forall (fun n => ?_)
    change 1 / ((n : ℝ) + 1) = ((1 : ℝ≥0∞) / ((n : ℕ) + 1)).toReal
    rw [ENNReal.toReal_div,
        ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top]
    simp
  exact squeeze_zero (fun n => norm_nonneg _) h_norm_le h_to_zero

/-- *Main mass theorem* (`ref/mass/mass.tex` Theorem). If `Ψ` is
pathwise differentiable at `P` over the full tangent `⊤` with
derivative `dψ`, and `φ ∈ L²₀(P)` is the mixture-Gâteaux representer
of `Ψ`, then for every `g ∈ ⊤` the inner product `⟪φ, g⟫_ℝ` equals
`dψ g`. In other words, `φ` is an influence function for `dψ`.

Proof outline: For `g ∈ B`, `boundedDensityPath g hg` is a `QMDPath`
with score `g`; its curve at `t ∈ (0, 1)` agrees with the convex
mixture `(1−t)·P + t·Q` for `Q := P.withDensity (1 + g)`
(`boundedDensityPath_curve_eq_mixture_pos`). Therefore the QMD-curve
limit (`PathwiseDifferentiableAt`) and the mixture-Gâteaux limit
(`IsMixtureGateauxRepresenter`) refer to the same scalar limit.
The Gâteaux side gives `∫ φ dQ = ∫ φ·(1+g) dP = ⟪φ, g⟫_ℝ` (since
`∫ φ dP = 0` by `φ ∈ L²₀(P)`). The QMD side gives `dψ ⟨g, mem_top⟩`.
Equating yields `⟪φ, g⟫_ℝ = dψ ⟨g, _⟩` for `g ∈ B`. By bilinearity
this extends to `span(B)`; by `bounded_score_span_dense` and
inner-product continuity it extends to all of `L²₀(P) = ⊤`. -/
theorem gateaux_representer_eq_pathwise_derivative
    {Ψ : Measure Ω → ℝ}
    (hPath : PathwiseDifferentiableAt P
              (⊤ : Submodule ℝ ↥(L2ZeroMean P)) Ψ)
    {φ : ↥(L2ZeroMean P)}
    (hGat : IsMixtureGateauxRepresenter Ψ φ) :
    ∀ g : (⊤ : Submodule ℝ ↥(L2ZeroMean P)),
      ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ = hPath.derivative g := by
  -- ===========================================================================
  -- Proof structure (high-level natural-language summary):
  --
  -- Both sides are continuous-linear maps in g. By
  -- `ContinuousLinearMap.ext_on`, two continuous linear maps that agree
  -- on a dense set agree everywhere. Strategy in three steps:
  --
  -- (1) Express both sides as CLMs on the ambient `↥(L2ZeroMean P)`:
  --       lhs_clm := innerSL ℝ φ                    — Riesz form
  --       rhs_clm := hPath.derivative.comp inclTop  — pathwise-derivative
  --                                                   precomposed with
  --                                                   codRestrict-to-⊤.
  --
  -- (2) Show lhs_clm = rhs_clm on B (bounded mixture scores). This is
  --     the substantive content (heq_on_B), and is proved by the chain:
  --       • Construct the QMD path γ := boundedDensityPath h _hh whose
  --         curve is `(1-t)·P + t·Q` where Q := P.withDensity (1+h).
  --       • The pathwise-derivative side gives a Tendsto-limit
  --         (PathwiseDifferentiableAt) along the curve.
  --       • The mixture-Gâteaux side (hGat applied to Q) gives a
  --         Tendsto-limit `→ ∫ φ dQ` along the same convex mixture.
  --       • Eventually the two curves agree
  --         (boundedDensityPath_curve_eq_mixture_eventually), so the
  --         two limits coincide by `Tendsto.unique` at the
  --         `nhdsWithin 0 (Set.Ioi 0)` filter.
  --       • Compute `∫ φ dQ` via `integral_withDensity_eq_integral_toReal_smul₀`:
  --           ∫ φ dQ = ∫ (1+h)·φ dP = ∫ φ dP + ∫ h·φ dP = 0 + ⟪φ, h⟫_ℝ
  --         using `φ ∈ L²₀(P)` (so `∫ φ dP = 0`) and the L².inner_def
  --         unfolding.
  --
  -- (3) Apply `ContinuousLinearMap.ext_on hdense heq_on_B` where
  --     `hdense` follows from `bounded_score_span_dense`: span(B) is
  --     dense in `↥(L2ZeroMean P)`. This extends the equality from B
  --     to all of `↥(L2ZeroMean P) = ⊤`.
  -- ===========================================================================
  -- Build LHS and RHS as continuous linear maps on the ambient
  -- `↥(L2ZeroMean P)`, then use `ContinuousLinearMap.ext_on` with
  -- density from `bounded_score_span_dense` (Lemma 2).
  -- LHS: `g ↦ ⟪φ, g⟫_ℝ` is the inner-product CLM `innerSL ℝ φ`.
  -- RHS: `g ↦ hPath.derivative ⟨g, mem_top⟩` is `hPath.derivative`
  --      composed with the codRestrict-to-⊤ identity CLM.
  let inclTop : ↥(L2ZeroMean P) →L[ℝ] (⊤ : Submodule ℝ ↥(L2ZeroMean P)) :=
    (ContinuousLinearMap.id ℝ ↥(L2ZeroMean P)).codRestrict
      (⊤ : Submodule ℝ ↥(L2ZeroMean P)) (fun _ => Submodule.mem_top)
  set lhs_clm : ↥(L2ZeroMean P) →L[ℝ] ℝ := innerSL ℝ φ with hlhs_def
  set rhs_clm : ↥(L2ZeroMean P) →L[ℝ] ℝ := hPath.derivative.comp inclTop
    with hrhs_def
  -- *Step 1.* Identity on `B` (substantive Tendsto-equating step;
  -- and `boundedDensityPath_curve_eq_mixture_pos`, plus an
  -- `integral_withDensity` + `Tendsto.unique` argument). -/
  have heq_on_B : Set.EqOn lhs_clm rhs_clm
      ({h : ↥(L2ZeroMean P) | IsBoundedMixtureScore h}) := by
    intro h _hh
    -- (1) Set up the QMDPath γ from boundedDensityPath; γ.score = h.
    let γ : QMDPath P := boundedDensityPath h _hh.toEss
    have hscore : γ.score = h := boundedDensityPath_score h _hh.toEss
    -- (2) Pathwise Tendsto on `nhdsWithin 0 ({0}ᶜ)`, restricted to Ioi 0.
    have h_path_compl :=
      hPath.derivative_spec γ Submodule.mem_top
    have h_path_pos :
        Tendsto (fun t : ℝ => (Ψ (γ.curve t) - Ψ P) / t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (hPath.derivative ⟨γ.score, Submodule.mem_top⟩)) :=
      h_path_compl.mono_left
        AsymptoticStatistics.ForMathlib.MassMethodUtilities.nhdsWithin_Ioi_le_compl_zero
    -- (3) Construct Q := P.withDensity (1 + h.coeFn).
    -- The `boundedDensityPath_curve_eq_mixture_eventually` corollary
    -- expresses `γ.curve t` (for small `t > 0`) as the convex mixture
    -- `(1−t)·P + t·Q` with this exact `Q`.
    set Q : Measure Ω := P.withDensity (fun ω =>
        ENNReal.ofReal (1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω)) with hQ_def
    -- (3a) Standing facts: |h| ≤ M_h a.e., h ≥ -1 a.e., and h ∈ L¹.
    obtain ⟨M_h, h_abs_M⟩ := _hh.1
    have h_lb_h : ∀ᵐ ω ∂P, -1 ≤ ((h : Lp ℝ 2 P) : Ω → ℝ) ω := _hh.2
    have h_h_int : Integrable (((h : Lp ℝ 2 P) : Ω → ℝ)) P :=
      (Lp.memLp (h : Lp ℝ 2 P)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_one_plus_h_nn : ∀ᵐ ω ∂P,
        0 ≤ 1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω := by
      filter_upwards [h_lb_h] with ω hω
      linarith
    have h_one_plus_h_int : Integrable
        (fun ω => 1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω) P :=
      (integrable_const _).add h_h_int
    have h_h_meas : AEMeasurable (((h : Lp ℝ 2 P) : Ω → ℝ)) P :=
      (Lp.aestronglyMeasurable (h : Lp ℝ 2 P)).aemeasurable
    have h_density_meas : AEMeasurable
        (fun ω => ENNReal.ofReal (1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω)) P :=
      ((aemeasurable_const).add h_h_meas).ennreal_ofReal
    -- (3b) ∫ h dP = 0 from h ∈ L²₀(P).
    have h_int_h_zero : ∫ ω, ((h : Lp ℝ 2 P) : Ω → ℝ) ω ∂P = 0 := by
      have h_mem : (h : Lp ℝ 2 P) ∈ L2ZeroMean P := h.2
      change (h : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at h_mem
      rw [LinearMap.mem_ker] at h_mem
      have h_inner : ⟪oneL2 P, (h : Lp ℝ 2 P)⟫_ℝ = 0 := h_mem
      rw [MeasureTheory.L2.inner_def] at h_inner
      have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      have h_int_eq :
          ∫ a, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
                ((h : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ ∂P
            = ∫ a, ((h : Lp ℝ 2 P) : Ω → ℝ) a ∂P := by
        apply integral_congr_ae
        filter_upwards [h_one_ae] with a ha
        have hcomm :
            ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
              ((h : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
              = ((h : Lp ℝ 2 P) : Ω → ℝ) a
                  * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
        rw [hcomm, ha, mul_one]
      rw [h_int_eq] at h_inner
      exact h_inner
    -- (3c) IsProbabilityMeasure Q.
    have hQ_prob : IsProbabilityMeasure Q := by
      refine ⟨?_⟩
      rw [hQ_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rw [← ofReal_integral_eq_lintegral_ofReal h_one_plus_h_int h_one_plus_h_nn]
      have h_int_eq :
          ∫ ω, 1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω ∂P = 1 := by
        rw [integral_add (integrable_const _) h_h_int, integral_const,
            h_int_h_zero]
        simp
      rw [h_int_eq, ENNReal.ofReal_one]
    haveI : IsProbabilityMeasure Q := hQ_prob
    -- (3d) Q ≪ P from withDensity_absolutelyContinuous.
    have hQ_ac : Q ≪ P := by
      rw [hQ_def]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
    -- (3e) dQ/dP a.e. bounded by 1 + |M_h|.
    have hQ_bdd : ∃ M : ℝ, ∀ᵐ ω ∂P, (Q.rnDeriv P ω).toReal ≤ M := by
      refine ⟨1 + |M_h|, ?_⟩
      have h_rn : Q.rnDeriv P =ᵐ[P]
          fun ω => ENNReal.ofReal (1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω) := by
        rw [hQ_def]
        exact Measure.rnDeriv_withDensity₀ P h_density_meas
      filter_upwards [h_rn, h_abs_M, h_lb_h] with ω hω h_abs h_lb
      rw [hω]
      have h_nn : 0 ≤ 1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω := by linarith
      rw [ENNReal.toReal_ofReal h_nn]
      have h_M_le : ((h : Lp ℝ 2 P) : Ω → ℝ) ω ≤ |M_h| := by
        calc ((h : Lp ℝ 2 P) : Ω → ℝ) ω
            ≤ |((h : Lp ℝ 2 P) : Ω → ℝ) ω| := le_abs_self _
          _ ≤ M_h := h_abs
          _ ≤ |M_h| := le_abs_self _
      linarith
    -- (4) Apply hGat to get the mixture-Gâteaux limit.
    have h_gat :
        Tendsto (fun t : ℝ =>
          (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) - Ψ P) / t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ ω, ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂Q)) :=
      hGat Q hQ_ac hQ_bdd
    -- (5) The QMD-curve and the convex mixture agree eventually as t → 0⁺.
    have h_curves_eq : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        γ.curve t = ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q := by
      have h_eventually :=
        boundedDensityPath_curve_eq_mixture_eventually h _hh
      filter_upwards [h_eventually] with t ht
      -- ht has the explicit `P.withDensity (...)` form; unfold Q to match.
      change γ.curve t = ENNReal.ofReal (1 - t) • P
            + ENNReal.ofReal t • P.withDensity (fun ω =>
                ENNReal.ofReal (1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω))
      exact ht
    -- (6) Use Tendsto.congr' to align h_path_pos with the mixture-form filter.
    have h_path_mix :
        Tendsto (fun t : ℝ =>
          (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) - Ψ P) / t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (hPath.derivative ⟨γ.score, Submodule.mem_top⟩)) := by
      apply h_path_pos.congr'
      filter_upwards [h_curves_eq] with t ht
      rw [ht]
    -- (7) Two limits at the same filter (NeBot) ⇒ they are equal.
    have h_lim_eq :
        hPath.derivative ⟨γ.score, Submodule.mem_top⟩
          = ∫ ω, ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂Q :=
      tendsto_nhds_unique h_path_mix h_gat
    -- (8) Compute ∫ φ dQ = ⟪φ, h⟫_ℝ.
    -- Step A: ∫ φ dQ = ∫ (1 + h)·φ dP via integral_withDensity.
    have h_int_dQ_eq :
        ∫ ω, ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂Q
          = ∫ ω, (1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω)
              * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂P := by
      rw [hQ_def]
      have h_lt_top : ∀ᵐ ω ∂P,
          ENNReal.ofReal (1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω) < ∞ :=
        Eventually.of_forall (fun ω => ENNReal.ofReal_lt_top)
      rw [integral_withDensity_eq_integral_toReal_smul₀ h_density_meas h_lt_top]
      apply integral_congr_ae
      filter_upwards [h_one_plus_h_nn] with ω hω
      rw [ENNReal.toReal_ofReal hω, smul_eq_mul]
    -- Step B: ∫ (1+h)·φ dP = ∫ φ dP + ∫ h·φ dP.
    have h_φ_int : Integrable (((φ : Lp ℝ 2 P) : Ω → ℝ)) P :=
      (Lp.memLp (φ : Lp ℝ 2 P)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_h_φ_int : Integrable
        (fun ω => ((h : Lp ℝ 2 P) : Ω → ℝ) ω
                * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω) P := by
      have := (Lp.memLp (h : Lp ℝ 2 P)).integrable_mul
        (Lp.memLp (φ : Lp ℝ 2 P))
      exact this
    have h_split_int :
        ∫ ω, (1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω)
              * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂P
          = ∫ ω, ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂P
              + ∫ ω, ((h : Lp ℝ 2 P) : Ω → ℝ) ω
                    * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂P := by
      have h_pointwise :
          (fun ω => (1 + ((h : Lp ℝ 2 P) : Ω → ℝ) ω)
                  * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω)
            = (fun ω => ((φ : Lp ℝ 2 P) : Ω → ℝ) ω
                      + ((h : Lp ℝ 2 P) : Ω → ℝ) ω
                        * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω) := by
        funext ω; ring
      rw [h_pointwise, integral_add h_φ_int h_h_φ_int]
    -- Step C: ∫ φ dP = 0 (φ ∈ L²₀(P)).
    have h_int_φ_zero : ∫ ω, ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂P = 0 := by
      have hφ_mem : (φ : Lp ℝ 2 P) ∈ L2ZeroMean P := φ.2
      change (φ : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at hφ_mem
      rw [LinearMap.mem_ker] at hφ_mem
      have h_inner : ⟪oneL2 P, (φ : Lp ℝ 2 P)⟫_ℝ = 0 := hφ_mem
      rw [MeasureTheory.L2.inner_def] at h_inner
      have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      have h_int_eq :
          ∫ a, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
                ((φ : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ ∂P
            = ∫ a, ((φ : Lp ℝ 2 P) : Ω → ℝ) a ∂P := by
        apply integral_congr_ae
        filter_upwards [h_one_ae] with a ha
        have hcomm :
            ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
              ((φ : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
              = ((φ : Lp ℝ 2 P) : Ω → ℝ) a
                  * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
        rw [hcomm, ha, mul_one]
      rw [h_int_eq] at h_inner
      exact h_inner
    -- Step D: ∫ h·φ dP = ⟪φ, h⟫_ℝ via L2.inner_def + RCLike.inner_apply.
    have h_inner_eq :
        ∫ ω, ((h : Lp ℝ 2 P) : Ω → ℝ) ω
              * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂P
          = ⟪φ, h⟫_ℝ := by
      have h_inner_unfold :
          ⟪(φ : Lp ℝ 2 P), (h : Lp ℝ 2 P)⟫_ℝ
            = ∫ ω, ⟪((φ : Lp ℝ 2 P) : Ω → ℝ) ω,
                    ((h : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ ∂P :=
        MeasureTheory.L2.inner_def (φ : Lp ℝ 2 P) (h : Lp ℝ 2 P)
      have h_pointwise :
          ∀ ω, ⟪((φ : Lp ℝ 2 P) : Ω → ℝ) ω,
                ((h : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ
              = ((h : Lp ℝ 2 P) : Ω → ℝ) ω
                * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω := by
        intro ω; rfl
      have h_inner_eq_int :
          ⟪(φ : Lp ℝ 2 P), (h : Lp ℝ 2 P)⟫_ℝ
            = ∫ ω, ((h : Lp ℝ 2 P) : Ω → ℝ) ω
                  * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂P := by
        rw [h_inner_unfold]
        exact integral_congr_ae (Eventually.of_forall (fun ω => h_pointwise ω))
      change ∫ ω, ((h : Lp ℝ 2 P) : Ω → ℝ) ω
            * ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂P
          = ⟪(φ : Lp ℝ 2 P), (h : Lp ℝ 2 P)⟫_ℝ
      exact h_inner_eq_int.symm
    -- Combine: ∫ φ dQ = 0 + ⟪φ, h⟫_ℝ = ⟪φ, h⟫_ℝ.
    have h_int_dQ : ∫ ω, ((φ : Lp ℝ 2 P) : Ω → ℝ) ω ∂Q = ⟪φ, h⟫_ℝ := by
      rw [h_int_dQ_eq, h_split_int, h_int_φ_zero, zero_add, h_inner_eq]
    -- (9) Final calc: ⟪φ, h⟫_ℝ = ∫ φ dQ = hPath.derivative ⟨h, mem_top⟩.
    change ⟪φ, h⟫_ℝ = hPath.derivative (inclTop h)
    have h_inclTop_eq : inclTop h = ⟨h, Submodule.mem_top⟩ := by
      apply Subtype.ext; rfl
    have h_score_eq :
        hPath.derivative ⟨γ.score, Submodule.mem_top⟩
          = hPath.derivative ⟨h, Submodule.mem_top⟩ := by
      have : (⟨γ.score, Submodule.mem_top⟩ : (⊤ : Submodule ℝ ↥(L2ZeroMean P)))
              = ⟨h, Submodule.mem_top⟩ := Subtype.ext hscore
      rw [this]
    rw [h_inclTop_eq, ← h_score_eq, h_lim_eq, h_int_dQ]
  -- *Step 2.* Density of `Submodule.span ℝ B` in `↥(L2ZeroMean P)`,
  -- as a Set-level statement (extracted from `bounded_score_span_dense`).
  have hdense :
      Dense ((Submodule.span ℝ
          {h : ↥(L2ZeroMean P) | IsBoundedMixtureScore h}) :
            Set ↥(L2ZeroMean P)) := by
    have h_eq_top : (Submodule.span ℝ
        {h : ↥(L2ZeroMean P) | IsBoundedMixtureScore h}).topologicalClosure
        = ⊤ := bounded_score_span_dense
    -- `Submodule.topologicalClosure` carrier is the topological closure
    -- of the carrier; equal to `⊤` means the closure is the universe,
    -- which is the definition of dense.
    have h_carrier : closure ((Submodule.span ℝ
        {h : ↥(L2ZeroMean P) | IsBoundedMixtureScore h}) :
          Set ↥(L2ZeroMean P)) = Set.univ := by
      have := congrArg (fun S : Submodule ℝ ↥(L2ZeroMean P) =>
          (S : Set ↥(L2ZeroMean P))) h_eq_top
      simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe] using this
    exact dense_iff_closure_eq.mpr h_carrier
  -- *Step 3.* `ContinuousLinearMap.ext_on` from Mathlib gives equal
  -- CLMs on the whole space.
  have h_clm_eq : lhs_clm = rhs_clm :=
    ContinuousLinearMap.ext_on hdense heq_on_B
  -- *Step 4.* Apply pointwise.
  intro g
  have h_at_g : lhs_clm (g : ↥(L2ZeroMean P)) = rhs_clm (g : ↥(L2ZeroMean P)) :=
    by rw [h_clm_eq]
  -- LHS at g.val is `⟪φ, g.val⟫_ℝ`; RHS is `hPath.derivative g`
  -- (since `inclTop g.val = ⟨g.val, mem_top⟩ = g` by Subtype.ext).
  have h_lhs_apply : lhs_clm (g : ↥(L2ZeroMean P))
      = ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ := rfl
  have h_rhs_apply : rhs_clm (g : ↥(L2ZeroMean P)) = hPath.derivative g := by
    change hPath.derivative (inclTop (g : ↥(L2ZeroMean P))) = hPath.derivative g
    congr 1
  rw [h_lhs_apply, h_rhs_apply] at h_at_g
  exact h_at_g

/-- *Verification entry point: mass method.* Given the mass-method
inputs (a `PathwiseDifferentiableAt` instance for the parameter
functional plus a mixture-Gâteaux representer assertion for the
candidate), conclude that the candidate is the efficient influence
function over the full tangent `⊤`.

This is the third verification entry point alongside
`candidate_isEIF_of_full_tangent` and `candidate_isEIF_of_membership`,
preferred when the user has access to symbolic point-mass
differentiation tools. -/
theorem eif_via_Gateaux
    {Ψ : Measure Ω → ℝ}
    (hPath : PathwiseDifferentiableAt P
              (⊤ : Submodule ℝ ↥(L2ZeroMean P)) Ψ)
    {φ : AsymptoticStatistics.Core.CandidateIF P}
    (hGat : IsMixtureGateauxRepresenter Ψ φ.toL2ZeroMean) :
    IsEfficientInfluenceFunction P (⊤ : Submodule ℝ ↥(L2ZeroMean P))
      hPath.derivative φ.toL2ZeroMean :=
  candidate_isEIF_of_full_tangent rfl
    (gateaux_representer_eq_pathwise_derivative hPath hGat)

/-- *Centered candidate from a TV-Fréchet representer.*

Given an L²-integrable raw function `f : Ω → ℝ`, package its mean-zero
counterpart `f − ∫f dP` as a `CandidateIF P`. This is the centering
step of `point_mass.tex` Theorem 1: the candidate EIF formula is
`φ(x) := f(x) − ∫f dP`, so that `∫φ dP = 0`.

Both `MemLp` (subtraction of MemLp `f` and `memLp_const`) and
mean-zero (linearity of integral on a probability measure) flow
mechanically. -/
noncomputable def centeredCandidate
    (f : Ω → ℝ) (hf : MemLp f 2 P) :
    AsymptoticStatistics.Core.CandidateIF P where
  raw := fun ω => f ω - ∫ ω', f ω' ∂P
  memLp2 := hf.sub (memLp_const _)
  mean_zero := by
    have h_int_f : Integrable f P :=
      hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [integral_sub h_int_f (integrable_const _), integral_const,
        probReal_univ, one_smul, sub_self]

/-- Bridge: TV-Fréchet expansion ⇒ mixture-Gâteaux representer
(centered form).

Given `IsTVFrechetMixtureExpansion P Ψ f` for an essentially bounded,
L²-integrable representer `f`, the centered candidate
`φ := f − ∫f dP` is a `IsMixtureGateauxRepresenter` for `Ψ`.

Proof: TV-Fréchet asserts the convex-mixture limit equals
`∫ f dQ − ∫ f dP`. We show this matches `∫ φ.coeFn dQ`:

  `∫ φ.coeFn dQ = ∫ (f − ∫f dP) dQ`         (`MemLp.coeFn_toLp` + `Q ≪ P`)
                `= ∫ f dQ − ∫f dP · Q(univ)` (linearity, `integral_sub`)
                `= ∫ f dQ − ∫f dP`           (Q is a probability measure).

The two real-number limits coincide.

Integrability of `f` against `Q` is derived from `f ∈ L²(P) ⊂ L¹(P)`
plus `Q ≤ M·P` (since `dQ/dP ≤ M`), via
`integrable_of_rnDeriv_bound`. No separate boundedness hypothesis on
`f` is required. -/
theorem tv_frechet_imp_mixture_gateaux
    {Ψ : Measure Ω → ℝ} {f : Ω → ℝ} (hf : MemLp f 2 P)
    (hTVF : IsTVFrechetMixtureExpansion P Ψ f) :
    IsMixtureGateauxRepresenter Ψ
      ((centeredCandidate (P := P) f hf).toL2ZeroMean) := by
  intro Q _ hQ_ac hQ_bdd
  have h_TVF := hTVF Q hQ_ac hQ_bdd
  -- Integrability of f against Q via the dominated-measure helper.
  have h_int_f_P : Integrable f P :=
    hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_int_f_Q : Integrable f Q :=
    integrable_of_rnDeriv_bound h_int_f_P hQ_ac hQ_bdd
  -- centered.toL2ZeroMean.coeFn =ᵐ[P] (f - ∫f dP).
  have h_centered_ae_P :
      (((centeredCandidate (P := P) f hf).toL2ZeroMean : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] fun ω => f ω - ∫ ω', f ω' ∂P :=
    AsymptoticStatistics.Core.CandidateIF.coeFn_toL2ZeroMean _
  -- Lift to Q via Q ≪ P.
  have h_centered_ae_Q :
      (((centeredCandidate (P := P) f hf).toL2ZeroMean : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[Q] fun ω => f ω - ∫ ω', f ω' ∂P :=
    h_centered_ae_P.filter_mono hQ_ac.ae_le
  -- ∫ centered.coeFn dQ = ∫ (f - ∫f dP) dQ = ∫f dQ - ∫f dP · Q(univ) = ∫f dQ - ∫f dP.
  have h_int_eq :
      ∫ ω, (((centeredCandidate (P := P) f hf).toL2ZeroMean : Lp ℝ 2 P) : Ω → ℝ) ω ∂Q
        = ∫ ω, f ω ∂Q - ∫ ω, f ω ∂P := by
    rw [integral_congr_ae h_centered_ae_Q,
        integral_sub h_int_f_Q (integrable_const _),
        integral_const, probReal_univ, one_smul]
  rw [← h_int_eq] at h_TVF
  exact h_TVF

/-- *Verification entry point: TV-Fréchet method.*

Given:
- `hPath : PathwiseDifferentiableAt P ⊤ Ψ` (model regularity);
- `hf : MemLp f 2 P` (the representer is square-integrable);
- `hTVF : IsTVFrechetMixtureExpansion P Ψ f` (TV-Fréchet derivative
  of `Ψ` with representer `f`),

conclude that the centered candidate `φ := f − ∫f dP` is the
efficient influence function over the full tangent `⊤`.

This is the fourth verification entry point alongside
`candidate_isEIF_of_full_tangent`, `candidate_isEIF_of_membership`,
and `eif_via_Gateaux`. Preferred when the user has access to a
TV-Fréchet derivative formula (from a Fréchet-calculus tool or
analytical hand-calculation against signed-measure perturbations).
The library performs the centering automatically.

Reference: `ref/mass/point_mass.tex` Theorem 1 (Equivalence of the
Point-Mass Derivative and the EIF). This entry point keeps
`PathwiseDifferentiableAt` as a separate hypothesis; it can instead be
derived from a strengthened TV-Fréchet hypothesis on signed measures via
DQM ⇒ TV-differentiable (see `eif_via_TV_QMD`). -/
theorem eif_via_TV_frechet
    {Ψ : Measure Ω → ℝ}
    (hPath : PathwiseDifferentiableAt P
              (⊤ : Submodule ℝ ↥(L2ZeroMean P)) Ψ)
    {f : Ω → ℝ} (hf : MemLp f 2 P)
    (hTVF : IsTVFrechetMixtureExpansion P Ψ f) :
    IsEfficientInfluenceFunction P (⊤ : Submodule ℝ ↥(L2ZeroMean P))
      hPath.derivative
      ((centeredCandidate (P := P) f hf).toL2ZeroMean) :=
  eif_via_Gateaux hPath
    (tv_frechet_imp_mixture_gateaux hf hTVF)

/-- *Construction of pathwise differentiability from TV-Fréchet (DQM form).*

Given `IsTVFrechetExpansion P Ψ f` for an L²-integrable `f`, the
centered candidate `φ := f − ∫f dP` provides the pathwise derivative
as the inner-product CLM `g ↦ ⟪φ, g⟫_ℝ` precomposed with the
inclusion `↥⊤ ↪ ↥(L2ZeroMean P)`.

Key calculation: for `g ∈ L²₀(P)` (which `γ.score` is for any
QMDPath), the centering identity

  `∫ f · g dP = ∫ (f − ∫f dP) · g dP + (∫f dP) · ∫ g dP
             = ∫ φ · g dP + 0`

shows that the hypothesis's limit value `∫ f · γ.score dP` matches
the inner-product `⟪φ, γ.score⟫_ℝ` (via `L².inner_def` and
`RCLike.inner_apply`). This is exactly what
`PathwiseDifferentiableAt`'s `derivative_spec` field requires. -/
noncomputable def pathwiseDifferentiableAt_of_TVFrechet
    {Ψ : Measure Ω → ℝ} {f : Ω → ℝ} (hf : MemLp f 2 P)
    (hTVF : IsTVFrechetExpansion P Ψ f) :
    PathwiseDifferentiableAt P
      (⊤ : Submodule ℝ ↥(L2ZeroMean P)) Ψ where
  derivative :=
    (innerSL ℝ ((centeredCandidate (P := P) f hf).toL2ZeroMean)).comp
      (Submodule.subtypeL ⊤)
  derivative_spec := by
    intro γ h_in_T
    -- Step 1: γ.score has mean zero (it's in L²₀(P)).
    have h_int_score_zero :
        ∫ ω, ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω ∂P = 0 := by
      have h_mem : (γ.score : Lp ℝ 2 P) ∈ L2ZeroMean P := γ.score.2
      change (γ.score : Lp ℝ 2 P)
          ∈ LinearMap.ker (integralL2 P).toLinearMap at h_mem
      rw [LinearMap.mem_ker] at h_mem
      have h_inner : ⟪oneL2 P, (γ.score : Lp ℝ 2 P)⟫_ℝ = 0 := h_mem
      rw [MeasureTheory.L2.inner_def] at h_inner
      have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      have h_int_eq :
          ∫ a, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
                ((γ.score : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ ∂P
            = ∫ a, ((γ.score : Lp ℝ 2 P) : Ω → ℝ) a ∂P := by
        apply integral_congr_ae
        filter_upwards [h_one_ae] with a ha
        have hcomm :
            ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
              ((γ.score : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
              = ((γ.score : Lp ℝ 2 P) : Ω → ℝ) a
                  * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
        rw [hcomm, ha, mul_one]
      rw [h_int_eq] at h_inner
      exact h_inner
    -- Step 2: integrability witnesses.
    set c : ℝ := ∫ ω, f ω ∂P with hc_def
    have h_score_memLp : MemLp ((γ.score : Lp ℝ 2 P) : Ω → ℝ) 2 P :=
      Lp.memLp _
    have h_score_int : Integrable ((γ.score : Lp ℝ 2 P) : Ω → ℝ) P :=
      h_score_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_score_f_int : Integrable
        (fun ω => ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω * f ω) P :=
      h_score_memLp.integrable_mul hf
    have h_centered_ae :
        (((centeredCandidate (P := P) f hf).toL2ZeroMean
            : Lp ℝ 2 P) : Ω → ℝ)
          =ᵐ[P] fun ω => f ω - c :=
      AsymptoticStatistics.Core.CandidateIF.coeFn_toL2ZeroMean _
    -- Step 3: the limit value matches the inner-product evaluation.
    have h_eq_val :
        ∫ ω, f ω * ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω ∂P
          = ⟪((centeredCandidate (P := P) f hf).toL2ZeroMean
                : ↥(L2ZeroMean P)),
              γ.score⟫_ℝ := by
      -- Unfold L².inner_def: ⟪φ, γ.score⟫ = ∫ ⟪φ.coeFn ω, γ.score.coeFn ω⟫_ℝ
      --   = ∫ γ.score.coeFn ω · φ.coeFn ω (RCLike.inner_apply, swap)
      --   = ∫ γ.score.coeFn ω · (f ω - c)         (centered.coeFn =ᵐ f - c)
      --   = ∫ score · f - c · ∫ score             (linearity)
      --   = ∫ f · score - 0 = ∫ f · score.        (mul_comm + mean-zero)
      rw [show ⟪((centeredCandidate (P := P) f hf).toL2ZeroMean
                  : ↥(L2ZeroMean P)),
              γ.score⟫_ℝ
            = ⟪(((centeredCandidate (P := P) f hf).toL2ZeroMean
                : ↥(L2ZeroMean P)) : Lp ℝ 2 P),
                (γ.score : Lp ℝ 2 P)⟫_ℝ from rfl,
          MeasureTheory.L2.inner_def]
      have h_int_eq :
          ∫ ω, ⟪(((centeredCandidate (P := P) f hf).toL2ZeroMean
                : Lp ℝ 2 P) : Ω → ℝ) ω,
                ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ ∂P
            = ∫ ω, ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω * (f ω - c) ∂P := by
        apply integral_congr_ae
        filter_upwards [h_centered_ae] with ω hω
        have hcomm :
            ⟪(((centeredCandidate (P := P) f hf).toL2ZeroMean
                : Lp ℝ 2 P) : Ω → ℝ) ω,
                ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ
              = ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω
                * (((centeredCandidate (P := P) f hf).toL2ZeroMean
                  : Lp ℝ 2 P) : Ω → ℝ) ω := rfl
        rw [hcomm, hω]
      rw [h_int_eq]
      have h_pointwise :
          (fun ω => ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω * (f ω - c))
            = (fun ω => ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω * f ω
                - c * ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω) := by
        funext ω; ring
      rw [h_pointwise,
          integral_sub h_score_f_int (h_score_int.const_mul c),
          integral_const_mul, h_int_score_zero, mul_zero, sub_zero]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ω; ring
    -- Step 4: chain hypothesis Tendsto with the equality.
    have h_TVF_γ := hTVF γ
    -- The hypothesis provides Tendsto with limit `∫ f · γ.score dP`;
    -- by h_eq_val this equals `⟪centered, γ.score⟫_ℝ`,
    -- which by definition of `derivative` equals
    -- `derivative ⟨γ.score, h_in_T⟩`.
    rw [h_eq_val] at h_TVF_γ
    exact h_TVF_γ

/-- *Verification entry point: TV-Fréchet method, DQM-path form.*

Given:
- `hf : MemLp f 2 P`,
- `hTVF : IsTVFrechetExpansion P Ψ f` (DQM-path-level expansion;
  `point_mass.tex` Theorem 1's analytical form),

conclude that the centered candidate `φ := f − ∫f dP` is the
efficient influence function over the full tangent `⊤`.

This entry point drops the separate `PathwiseDifferentiableAt`
hypothesis required by `eif_via_TV_frechet`. The pathwise
differentiability is constructed from the DQM-path expansion via
`pathwiseDifferentiableAt_of_TVFrechet`; the EIF claim is then
discharged by `candidate_isEIF_of_full_tangent` since the derivative
is *by construction* the inner-product CLM against the centered
candidate.

(The "TV_QMD" mnemonic: this route consumes the *strict* TV-Fréchet
expansion *along all QMD paths*.) -/
noncomputable def eif_via_TV_QMD
    {Ψ : Measure Ω → ℝ} {f : Ω → ℝ} (hf : MemLp f 2 P)
    (hTVF : IsTVFrechetExpansion P Ψ f) :
    IsEfficientInfluenceFunction P (⊤ : Submodule ℝ ↥(L2ZeroMean P))
      (pathwiseDifferentiableAt_of_TVFrechet hf hTVF).derivative
      ((centeredCandidate (P := P) f hf).toL2ZeroMean) :=
  AsymptoticStatistics.Core.EIF.candidate_isEIF_of_full_tangent
    (T := (⊤ : Submodule ℝ ↥(L2ZeroMean P)))
    rfl (fun _ => rfl)

/-! ### Von Mises expansion entry point

Reference: `ref/mass/point_mass_vonMise.tex`. The textbook
formulation (vdV §25; BKRW §A) of the influence function
expansion: a candidate `f : Ω → ℝ` and an explicit remainder
`R : 𝒫 → ℝ` with
  `Ψ(Q) − Ψ(P) = ∫f d(Q − P) + R(Q)`
plus the requirement `R/t → 0` along **two** canonical path families
(point-mass and bounded-score). Distinct from
`IsTVFrechetMixtureExpansion` in that the user packages the remainder
as a single object and verifies vanishing along the two textbook
families separately — often just polynomial algebra in `t` for
concrete functionals (means, regression coefficients, ATE under
positivity). -/

/-- *First-order von Mises expansion at `P`.*

Stores the remainder mapping `R` together with three Prop fields
encoding the textbook von Mises hypothesis:

* `expansion` — the linear-in-`f` decomposition of `Ψ(Q) − Ψ(P)`
  with remainder `R(Q)`, valid at every probability measure `Q`
  against which `f` is integrable.
* `point_mass_remainder` — `R(P_{t,x})/t → 0` along point-mass
  paths `P_{t,x} := (1−t)P + tδ_x`.
* `score_remainder` — `R(P_{t,g})/t → 0` along bounded-score paths
  `P_{t,g} := P.withDensity(1 + t·g)` for any `g ∈
  IsBoundedMixtureScore`.

The user supplies the raw `f` together with this bundle. `R`'s
existence is forced by the definition `R(Q) := Ψ(Q) − Ψ(P) − ∫f d(Q−P)`
once the user picks `f`. The two remainder limits are proof
obligations — typically discharged by 1D polynomial algebra after
substituting the linear-mixture form of the path. -/
structure HasVonMisesExpansion
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : Measure Ω → ℝ) (f : Ω → ℝ) where
  /-- The remainder mapping, defined uniquely (up to values on `Q`
  where `f` is non-integrable) by `R(Q) := Ψ(Q) − Ψ(P) − ∫f d(Q−P)`. -/
  R : Measure Ω → ℝ
  /-- First-order expansion at every probability `Q` against which
  `f` is integrable. -/
  expansion : ∀ (Q : Measure Ω) [IsProbabilityMeasure Q],
    Integrable f Q →
    Ψ Q - Ψ P = ∫ ω, f ω ∂Q - ∫ ω, f ω ∂P + R Q
  /-- Remainder vanishes faster than `t` along point-mass paths
  `P_{t,x} := (1−t)P + tδ_x`. -/
  point_mass_remainder : ∀ x : Ω,
    Filter.Tendsto (fun t : ℝ =>
      R (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Measure.dirac x) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)
  /-- Remainder vanishes faster than `t` along bounded-score paths
  `P_{t,g} := P.withDensity(1 + t·g)`. -/
  score_remainder : ∀ (g : ↥(L2ZeroMean P)), IsBoundedMixtureScore g →
    Filter.Tendsto (fun t : ℝ =>
      R (P.withDensity (fun ω =>
        ENNReal.ofReal (1 + t * ((g : Lp ℝ 2 P) : Ω → ℝ) ω))) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)

/-- *Auxiliary:* the convex mixture `(1−t)P + tQ` is a probability
measure for `t ∈ [0, 1]` whenever `P` and `Q` are. Tucked here
because the expansion clause of `HasVonMisesExpansion` consumes a
`[IsProbabilityMeasure Q_t]` instance. -/
private lemma isProbabilityMeasure_convex_mixture
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {t : ℝ} (ht_nn : 0 ≤ t) (ht_le : t ≤ 1) :
    IsProbabilityMeasure
      (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) := by
  refine ⟨?_⟩
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  rw [← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1 - t) ht_nn]
  rw [show (1 - t) + t = (1 : ℝ) from by ring, ENNReal.ofReal_one]

/-- *Theorem 1, Part 1 of `point_mass_vonMise.tex`.* The point-mass
directional derivative of `Ψ` is exactly `f(x) − ∫f dP` (the centered
candidate evaluated at `x`).

Pure algebra on the von Mises expansion: at `Q = P_{t,x}` the linear
term `∫f dQ − ∫f dP` simplifies to `t·(f(x) − ∫f dP)`, and the
remainder vanishes faster than `t` by hypothesis. -/
theorem vonMises_pointMass_derivative
    {Ψ : Measure Ω → ℝ} {f : Ω → ℝ}
    (hf : MemLp f 2 P) (hf_meas : Measurable f)
    (h : HasVonMisesExpansion P Ψ f) (x : Ω) :
    Filter.Tendsto (fun t : ℝ =>
      (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Measure.dirac x)
        - Ψ P) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (f x - ∫ ω, f ω ∂P)) := by
  -- Strategy: rewrite (Ψ(P_{t,x}) − Ψ(P))/t as
  --   (∫f dP_{t,x} − ∫f dP)/t + R(P_{t,x})/t
  -- and show the first term is **constant** in t (= f(x) − ∫f dP)
  -- and the second tends to 0.
  set μ : ℝ := ∫ ω, f ω ∂P with hμ_def
  have hf_int_P : Integrable f P :=
    hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hf_strong : StronglyMeasurable f := hf_meas.stronglyMeasurable
  -- f integrable against Measure.dirac x: norm at x is finite real.
  have hf_int_dirac : Integrable f (Measure.dirac x) :=
    integrable_dirac' hf_strong (by simp [enorm_eq_nnnorm,
      ENNReal.coe_lt_top])
  -- ∫ f ∂(Measure.dirac x) = f x.
  have h_int_dirac : ∫ ω, f ω ∂(Measure.dirac x) = f x :=
    integral_dirac' f x hf_strong
  -- Eventually for t ∈ (0, 1), Q_t is a probability measure and
  -- the expansion holds.
  have h_ioo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio 1, Iio_mem_nhds one_pos, ?_⟩
    intro y hy; exact ⟨hy.2, hy.1⟩
  have hE : ∀ᶠ t : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0), t ∈ Set.Ioo (0:ℝ) 1 :=
    h_ioo
  have h_eventually : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (f x - μ) + h.R (ENNReal.ofReal (1 - t) • P
              + ENNReal.ofReal t • Measure.dirac x) / t
        = (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Measure.dirac x)
            - Ψ P) / t := by
    filter_upwards [hE] with t ht
    obtain ⟨ht_pos, ht_lt_one⟩ := ht
    have ht_nn : (0 : ℝ) ≤ t := ht_pos.le
    have ht_le : t ≤ 1 := ht_lt_one.le
    -- IsProbabilityMeasure Q_t.
    haveI : IsProbabilityMeasure
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Measure.dirac x) :=
      isProbabilityMeasure_convex_mixture _ ht_nn ht_le
    -- Integrability of f against Q_t.
    have h_smul_P_int : Integrable f (ENNReal.ofReal (1 - t) • P) :=
      hf_int_P.smul_measure (by exact ENNReal.ofReal_ne_top)
    have h_smul_dirac_int : Integrable f (ENNReal.ofReal t • Measure.dirac x) :=
      hf_int_dirac.smul_measure (by exact ENNReal.ofReal_ne_top)
    have hf_int_Q : Integrable f
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Measure.dirac x) :=
      h_smul_P_int.add_measure h_smul_dirac_int
    -- Expansion at Q_t.
    have h_exp := h.expansion
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Measure.dirac x)
        hf_int_Q
    -- ∫f dQ_t = (1-t)·∫f dP + t·f(x).
    have h_int_Qt :
        ∫ ω, f ω ∂(ENNReal.ofReal (1 - t) • P
                  + ENNReal.ofReal t • Measure.dirac x)
          = (1 - t) * μ + t * f x := by
      rw [integral_add_measure h_smul_P_int h_smul_dirac_int,
          integral_smul_measure, integral_smul_measure, h_int_dirac]
      simp [hμ_def, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - t),
            ENNReal.toReal_ofReal ht_nn]
    -- Reduce: divide both sides of h_exp by t.
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    rw [h_exp, h_int_Qt]
    field_simp
    ring
  -- Limit of the constant part is itself; remainder part tends to 0.
  have h_lim :
      Tendsto (fun t : ℝ => (f x - μ)
          + h.R (ENNReal.ofReal (1 - t) • P
                + ENNReal.ofReal t • Measure.dirac x) / t)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((f x - μ) + 0)) := by
    refine Tendsto.add tendsto_const_nhds ?_
    exact h.point_mass_remainder x
  simpa [add_zero] using h_lim.congr' h_eventually

/-- *Bridge: von Mises ⇒ TV-Fréchet (mixture form).*

The bounded-score remainder condition of `HasVonMisesExpansion`
controls the limit along every convex-mixture path `(1−t)P + tQ`
with `Q ≪ P` of bounded RN-derivative. Concretely: from `Q` we
construct the bounded mean-zero score `g := dQ/dP − 1 ∈ B`, identify
the score path `P.withDensity(1 + tg)` with the convex mixture
`(1−t)P + tQ` (eventually for `t > 0`) via
`boundedDensityPath_curve_eq_mixture_eventually`, and apply
`expansion` + `score_remainder`. -/
theorem vonMises_imp_TVFrechetMixture
    {Ψ : Measure Ω → ℝ} {f : Ω → ℝ}
    (hf : MemLp f 2 P)
    (h : HasVonMisesExpansion P Ψ f) :
    IsTVFrechetMixtureExpansion P Ψ f := by
  intro Q _hQ_inst hQ_ac hQ_bdd
  -- ===== Construction of bounded score g_L20 from Q =====
  obtain ⟨M_RN, hM_RN⟩ := hQ_bdd
  -- Repackage the bound for downstream use of `integrable_of_rnDeriv_bound`.
  have hQ_bdd' : ∃ M : ℝ, ∀ᵐ ω ∂P, (Q.rnDeriv P ω).toReal ≤ M :=
    ⟨M_RN, hM_RN⟩
  set h_RN : Ω → ℝ := fun ω => (Q.rnDeriv P ω).toReal with hh_RN_def
  set g_raw : Ω → ℝ := fun ω => h_RN ω - 1 with hg_raw_def
  -- Standing pointwise nonnegativity / bound on h_RN.
  have h_RN_nn : ∀ ω, 0 ≤ h_RN ω := fun ω => ENNReal.toReal_nonneg
  have h_RN_meas : Measurable h_RN :=
    (Measure.measurable_rnDeriv Q P).ennreal_toReal
  have hg_meas : Measurable g_raw := h_RN_meas.sub measurable_const
  -- Bound: |g_raw ω| ≤ |M_RN| + 1.
  have hg_bdd_ae : ∀ᵐ ω ∂P, |g_raw ω| ≤ |M_RN| + 1 := by
    filter_upwards [hM_RN] with ω hω
    have hh_nn : 0 ≤ h_RN ω := h_RN_nn ω
    have hh_le : h_RN ω ≤ |M_RN| := hω.trans (le_abs_self _)
    change |h_RN ω - 1| ≤ |M_RN| + 1
    have h3 : -(|M_RN| + 1) ≤ h_RN ω - 1 := by
      have : (0 : ℝ) ≤ |M_RN| := abs_nonneg _; linarith
    have h4 : h_RN ω - 1 ≤ |M_RN| + 1 := by linarith
    exact abs_le.mpr ⟨h3, h4⟩
  -- Lower bound: g_raw ≥ -1.
  have hg_lb : ∀ᵐ ω ∂P, -1 ≤ g_raw ω := by
    filter_upwards with ω
    have : 0 ≤ h_RN ω := h_RN_nn ω
    change -1 ≤ h_RN ω - 1; linarith
  -- MemLp g_raw 2 P (bounded function on a finite measure).
  have hg_memLp : MemLp g_raw 2 P := by
    refine MemLp.of_bound hg_meas.aestronglyMeasurable (|M_RN| + 1) ?_
    filter_upwards [hg_bdd_ae] with ω hω
    rw [Real.norm_eq_abs]; exact hω
  -- ∫ g_raw dP = 0  (since ∫ h_RN dP = Q(univ) = 1).
  have h_rn_lt_top : ∀ᵐ ω ∂P, Q.rnDeriv P ω < ⊤ :=
    Measure.rnDeriv_lt_top Q P
  have h_int_h_RN : ∫ ω, h_RN ω ∂P = 1 := by
    change ∫ ω, (Q.rnDeriv P ω).toReal ∂P = 1
    rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable
          h_rn_lt_top,
        Measure.lintegral_rnDeriv hQ_ac]
    simp
  have h_int_g_zero : ∫ ω, g_raw ω ∂P = 0 := by
    have hg_int : Integrable g_raw P :=
      hg_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hh_int : Integrable h_RN P := hg_int.add (integrable_const 1) |>.congr
      (by filter_upwards with ω; change g_raw ω + 1 = h_RN ω; simp [hg_raw_def])
    change ∫ ω, h_RN ω - 1 ∂P = 0
    rw [integral_sub hh_int (integrable_const 1), integral_const,
        h_int_h_RN]
    simp
  -- Build g as Lp ℝ 2 P element.
  set gLp : Lp ℝ 2 P := MemLp.toLp g_raw hg_memLp with hgLp_def
  have h_gLp_ae : (gLp : Ω → ℝ) =ᵐ[P] g_raw :=
    MemLp.coeFn_toLp hg_memLp
  -- g ∈ L2ZeroMean P.
  have hgLp_in_L20 : gLp ∈ L2ZeroMean P := by
    change gLp ∈ LinearMap.ker (integralL2 P).toLinearMap
    rw [LinearMap.mem_ker]
    change ⟪oneL2 P, gLp⟫_ℝ = 0
    rw [MeasureTheory.L2.inner_def]
    have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_int_eq :
        ∫ a, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a, (gLp : Ω → ℝ) a⟫_ℝ ∂P
          = ∫ a, g_raw a ∂P := by
      apply integral_congr_ae
      filter_upwards [h_one_ae, h_gLp_ae] with a ha hg
      have hcomm : ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
                    (gLp : Ω → ℝ) a⟫_ℝ
            = (gLp : Ω → ℝ) a * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
      rw [hcomm, ha, hg, mul_one]
    rw [h_int_eq, h_int_g_zero]
  set g_L20 : ↥(L2ZeroMean P) := ⟨gLp, hgLp_in_L20⟩ with hg_L20_def
  -- IsBoundedMixtureScore g_L20.
  have hg_bdd_score : IsBoundedMixtureScore g_L20 := by
    refine ⟨⟨|M_RN| + 1, ?_⟩, ?_⟩
    · filter_upwards [h_gLp_ae, hg_bdd_ae] with ω hω hω'
      change |((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ |M_RN| + 1
      rw [show ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω = (gLp : Ω → ℝ) ω from rfl,
          hω]
      exact hω'
    · filter_upwards [h_gLp_ae, hg_lb] with ω hω hω'
      change -1 ≤ ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω
      rw [show ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω = (gLp : Ω → ℝ) ω from rfl,
          hω]
      exact hω'
  -- ===== P.withDensity(1 + g_L20) = Q =====
  set Q_target : Measure Ω := P.withDensity (fun ω =>
      ENNReal.ofReal (1 + ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω))
    with hQ_target_def
  -- a.e.: 1 + g_L20 = h_RN.
  have h_one_plus_g_ae :
      (fun ω => 1 + ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω)
        =ᵐ[P] h_RN := by
    filter_upwards [h_gLp_ae] with ω hω
    rw [show ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω = (gLp : Ω → ℝ) ω from rfl,
        hω]
    change 1 + (h_RN ω - 1) = h_RN ω; ring
  -- a.e.: Q.rnDeriv P (which has values in ℝ≥0∞) is bounded, so finite a.e.
  -- (`h_rn_lt_top` was already established above as `Measure.rnDeriv_lt_top Q P`.)
  -- ENNReal.ofReal h_RN = Q.rnDeriv P  (a.e., where Q.rnDeriv < ⊤).
  have h_ofReal_h_RN_ae :
      (fun ω => ENNReal.ofReal (h_RN ω)) =ᵐ[P] Q.rnDeriv P := by
    filter_upwards [h_rn_lt_top] with ω hω
    change ENNReal.ofReal ((Q.rnDeriv P ω).toReal) = Q.rnDeriv P ω
    exact ENNReal.ofReal_toReal hω.ne
  -- Q_target = P.withDensity h_RN_eReal = P.withDensity (Q.rnDeriv P) = Q.
  have hQ_target_eq_Q : Q_target = Q := by
    rw [hQ_target_def]
    have h_density_ae :
        (fun ω => ENNReal.ofReal (1 + ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω))
          =ᵐ[P] Q.rnDeriv P := by
      filter_upwards [h_one_plus_g_ae, h_ofReal_h_RN_ae] with ω hω hω'
      rw [show 1 + ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω = h_RN ω from hω]
      exact hω'
    rw [withDensity_congr_ae h_density_ae,
        Measure.withDensity_rnDeriv_eq Q P hQ_ac]
  -- ===== Apply boundedDensityPath_curve_eq_mixture_eventually =====
  -- The existing lemma gives the curve identity with `Q_target` on the RHS;
  -- we substitute `Q` via `hQ_target_eq_Q` and unfold `curve t` to the
  -- explicit `withDensity` form on the LHS for small `t > 0`.
  have h_curves_eq : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      P.withDensity (fun ω => ENNReal.ofReal
          (1 + t * ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω))
        = ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q := by
    have hev := boundedDensityPath_curve_eq_mixture_eventually g_L20 hg_bdd_score
    -- Reconstruct δ from `boundedDensityPath` to detect when curve t
    -- unfolds to the withDensity branch.
    set M : ℝ := max 0 (Classical.choose hg_bdd_score.1) with hM_def
    set δ : ℝ := 1 / (M + 1) with hδ_def
    have hM_nn : (0 : ℝ) ≤ M := le_max_left _ _
    have hδ_pos : (0 : ℝ) < δ := by
      change 0 < 1 / (M + 1); apply div_pos one_pos; linarith
    have h_ioo_δ : Set.Ioo (0 : ℝ) δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio δ, Iio_mem_nhds hδ_pos, ?_⟩
      intro y hy; exact ⟨hy.2, hy.1⟩
    have hE_δ : ∀ᶠ t : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0),
        t ∈ Set.Ioo (0:ℝ) δ := h_ioo_δ
    filter_upwards [hev, hE_δ] with t ht_curve ht_δ
    obtain ⟨ht_pos, ht_lt_δ⟩ := ht_δ
    have ht_abs : |t| < δ := by rw [abs_of_pos ht_pos]; exact ht_lt_δ
    -- Unfold curve t at the if-then-else.
    have h_curve_eq :
        (boundedDensityPath g_L20 hg_bdd_score.toEss).curve t
          = P.withDensity (fun ω => ENNReal.ofReal
              (1 + t * ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω)) := by
      change (if |t| < δ then
              P.withDensity (fun ω => ENNReal.ofReal
                (1 + t * ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω))
            else P) = _
      rw [if_pos ht_abs]
    -- Now `ht_curve` says `curve t = (1-t)P + t·Q_target`; compose with
    -- `hQ_target_eq_Q` to get `(1-t)P + t·Q`.
    rw [← h_curve_eq, ht_curve, ← hQ_target_def, hQ_target_eq_Q]
  -- ===== Combine: expansion + score_remainder + path identity =====
  -- Score remainder along the score path.
  have h_rem_score :
      Tendsto (fun t : ℝ =>
        h.R (P.withDensity (fun ω => ENNReal.ofReal
              (1 + t * ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω))) / t)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    h.score_remainder g_L20 hg_bdd_score
  -- Transport via h_curves_eq: R((1-t)P + tQ)/t → 0.
  have h_rem_mix :
      Tendsto (fun t : ℝ =>
        h.R (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) / t)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    apply h_rem_score.congr'
    filter_upwards [h_curves_eq] with t ht
    rw [ht]
  -- f integrable against P (from MemLp f 2 P), then against Q via the
  -- dominated-measure helper.
  have hf_int_P : Integrable f P :=
    hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hf_int_Q : Integrable f Q :=
    integrable_of_rnDeriv_bound hf_int_P hQ_ac hQ_bdd'
  -- Eventually, the limit quotient simplifies to (∫f dQ - ∫f dP) + R/t.
  have h_ioo_unit : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio 1, Iio_mem_nhds one_pos, ?_⟩
    intro y hy; exact ⟨hy.2, hy.1⟩
  have hE_unit : ∀ᶠ t : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      t ∈ Set.Ioo (0:ℝ) 1 := h_ioo_unit
  have h_eventually : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ ω, f ω ∂Q - ∫ ω, f ω ∂P)
          + h.R (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) / t
        = (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) - Ψ P) / t := by
    filter_upwards [hE_unit] with t ht
    obtain ⟨ht_pos, ht_lt_one⟩ := ht
    have ht_nn : (0 : ℝ) ≤ t := ht_pos.le
    have ht_le : t ≤ 1 := ht_lt_one.le
    haveI : IsProbabilityMeasure
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) :=
      isProbabilityMeasure_convex_mixture _ ht_nn ht_le
    have h_smul_P_int : Integrable f (ENNReal.ofReal (1 - t) • P) :=
      hf_int_P.smul_measure (by exact ENNReal.ofReal_ne_top)
    have h_smul_Q_int : Integrable f (ENNReal.ofReal t • Q) :=
      hf_int_Q.smul_measure (by exact ENNReal.ofReal_ne_top)
    have hf_int_Qt : Integrable f
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) :=
      h_smul_P_int.add_measure h_smul_Q_int
    have h_exp := h.expansion
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) hf_int_Qt
    have h_int_Qt :
        ∫ ω, f ω ∂(ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q)
          = (1 - t) * (∫ ω, f ω ∂P) + t * (∫ ω, f ω ∂Q) := by
      rw [integral_add_measure h_smul_P_int h_smul_Q_int,
          integral_smul_measure, integral_smul_measure]
      simp [ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - t),
            ENNReal.toReal_ofReal ht_nn]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    rw [h_exp, h_int_Qt]
    field_simp
    ring
  -- Combine into the conclusion.
  have h_final :
      Tendsto (fun t : ℝ => (∫ ω, f ω ∂Q - ∫ ω, f ω ∂P)
          + h.R (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q) / t)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((∫ ω, f ω ∂Q - ∫ ω, f ω ∂P) + 0)) :=
    Tendsto.add tendsto_const_nhds h_rem_mix
  simpa [add_zero] using h_final.congr' h_eventually

/-- *Verification entry point: von Mises method.*

Given:
- `hPath : PathwiseDifferentiableAt P ⊤ Ψ` (model regularity);
- `hf : MemLp f 2 P` (the candidate is square-integrable);
- `h : HasVonMisesExpansion P Ψ f` (the textbook von Mises hypothesis
  with the two canonical remainder conditions),

conclude that the centered candidate `φ := f − ∫f dP` is the
efficient influence function over the full tangent `⊤`.

This is the fifth verification entry point alongside
`candidate_isEIF_of_full_tangent`, `candidate_isEIF_of_membership`,
`eif_via_Gateaux`, `eif_via_TV_frechet`, and `eif_via_TV_QMD`.
Preferred when the user has access to a textbook von Mises
expansion: a remainder formula `R(Q)` and a verification (typically
elementary 1D polynomial algebra in `t`) that `R(Q_t)/t → 0` along
the two canonical path families.

Reference: `ref/mass/point_mass_vonMise.tex` Theorem 1, Part 2. The
companion result `vonMises_pointMass_derivative` gives the explicit
point-mass formula `(d/dt) Ψ(P_{t,x})|_{t=0⁺} = f(x) − ∫f dP`. -/
theorem eif_via_vonMises
    {Ψ : Measure Ω → ℝ}
    (hPath : PathwiseDifferentiableAt P
              (⊤ : Submodule ℝ ↥(L2ZeroMean P)) Ψ)
    {f : Ω → ℝ} (hf : MemLp f 2 P)
    (h : HasVonMisesExpansion P Ψ f) :
    IsEfficientInfluenceFunction P (⊤ : Submodule ℝ ↥(L2ZeroMean P))
      hPath.derivative
      ((centeredCandidate (P := P) f hf).toL2ZeroMean) :=
  eif_via_TV_frechet hPath hf
    (vonMises_imp_TVFrechetMixture hf h)

/-! ### 1D pathwise derivative entry point

Reference: `ref/mass/point_mass_vonMise.tex` §4 (The Universal
Condition: 1D Pathwise Differentiability), Condition 5 + Lemma 7.

The user-facing hypothesis is the *one-dimensional* pathwise
right-derivative of `Ψ` along a linear-mixture path
`(1−t)P + tM`, asserting the limit equals the integral of the
candidate `ϕ` against the signed measure `M − P`. This bypasses
formalising Fréchet derivatives over the Banach space of signed
measures: per-model verification reduces to standard 1D calculus
on a scalar function `t ↦ Ψ((1−t)P + tM)`. Lemma 7 then shows the
von Mises remainder vanishes faster than `t` automatically. -/

/-- *1D pathwise right-derivative along the linear mixture
`(1−t)P + tM`.*

Captures the LaTeX Condition 5: the scalar function
`f_M(t) := Ψ((1−t)P + tM)` is right-differentiable at `t = 0`, with
1D derivative equal to `∫ϕ d(M − P)`.

The user supplies, for each target measure `M` of interest (a point
mass `δ_x` or a bounded-density measure `P.withDensity(1 + g)`), the
1D limit value. This is typically a direct application of Mathlib's
real-calculus library (`deriv`, `hasDerivAt`, `fun_prop`) once
`Ψ((1−t)P + tM)` is unfolded as a 1D scalar formula. -/
def Has1DPathwiseDeriv
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : Measure Ω → ℝ) (ϕ : Ω → ℝ) (M : Measure Ω) : Prop :=
  Filter.Tendsto (fun t : ℝ =>
      (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M) - Ψ P) / t)
    (nhdsWithin 0 (Set.Ioi 0))
    (𝓝 (∫ x, ϕ x ∂M - ∫ x, ϕ x ∂P))

/-- *Lemma 7 of `point_mass_vonMise.tex`: 1D pathwise differentiability ⇒
von Mises remainder decay.*

Given the von Mises expansion `Ψ(Q) − Ψ(P) = ∫ϕ d(Q−P) + R(Q)` and
the 1D pathwise derivative along `M`, the remainder `R(P_{t,M})/t → 0`
as `t ↓ 0` along the linear-mixture path `P_{t,M} := (1−t)P + tM`.

Proof: along the linear mixture, `∫ϕ dP_{t,M} − ∫ϕ dP = t·(∫ϕ dM − ∫ϕ dP)`
by integral-linearity over `add` + `smul` of measures. Therefore
  `R(P_{t,M})/t = (Ψ(P_{t,M}) − Ψ P)/t − (∫ϕ dM − ∫ϕ dP)`
which by `Has1DPathwiseDeriv` tends to `(∫ϕ dM − ∫ϕ dP) − (∫ϕ dM − ∫ϕ dP) = 0`. -/
theorem R_decay_of_1d_deriv
    {Ψ : Measure Ω → ℝ} {ϕ : Ω → ℝ} {M : Measure Ω}
    [IsProbabilityMeasure M]
    (h_int_P : Integrable ϕ P) (h_int_M : Integrable ϕ M)
    (h_1d : Has1DPathwiseDeriv P Ψ ϕ M)
    (R : Measure Ω → ℝ)
    (h_exp : ∀ (Q : Measure Ω) [IsProbabilityMeasure Q], Integrable ϕ Q →
              Ψ Q - Ψ P = ∫ x, ϕ x ∂Q - ∫ x, ϕ x ∂P + R Q) :
    Filter.Tendsto (fun t : ℝ =>
        R (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  -- Eventually for `t ∈ (0, 1)`, the linear mixture is a probability
  -- measure and the algebraic identity holds.
  have h_ioo_unit : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio 1, Iio_mem_nhds one_pos, ?_⟩
    intro y hy; exact ⟨hy.2, hy.1⟩
  have hE_unit : ∀ᶠ t : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      t ∈ Set.Ioo (0:ℝ) 1 := h_ioo_unit
  have h_eq : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M) - Ψ P) / t
          - (∫ x, ϕ x ∂M - ∫ x, ϕ x ∂P)
        = R (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M) / t := by
    filter_upwards [hE_unit] with t ht
    obtain ⟨ht_pos, ht_lt_one⟩ := ht
    have ht_nn : (0 : ℝ) ≤ t := ht_pos.le
    have ht_le : t ≤ 1 := ht_lt_one.le
    haveI : IsProbabilityMeasure
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M) :=
      isProbabilityMeasure_convex_mixture _ ht_nn ht_le
    have h_smul_P_int : Integrable ϕ (ENNReal.ofReal (1 - t) • P) :=
      h_int_P.smul_measure (by exact ENNReal.ofReal_ne_top)
    have h_smul_M_int : Integrable ϕ (ENNReal.ofReal t • M) :=
      h_int_M.smul_measure (by exact ENNReal.ofReal_ne_top)
    have hf_int_Qt : Integrable ϕ
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M) :=
      h_smul_P_int.add_measure h_smul_M_int
    have h_exp_Qt := h_exp
        (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M) hf_int_Qt
    have h_int_Qt :
        ∫ ω, ϕ ω ∂(ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M)
          = (1 - t) * (∫ ω, ϕ ω ∂P) + t * (∫ ω, ϕ ω ∂M) := by
      rw [integral_add_measure h_smul_P_int h_smul_M_int,
          integral_smul_measure, integral_smul_measure]
      simp [ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - t),
            ENNReal.toReal_ofReal ht_nn]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    rw [h_exp_Qt, h_int_Qt]
    field_simp
    ring
  -- (Ψ(Q_t) − Ψ P)/t → ∫ϕ dM − ∫ϕ dP, then subtract the constant.
  have h_sub :
      Tendsto (fun t : ℝ =>
          (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • M) - Ψ P) / t
          - (∫ x, ϕ x ∂M - ∫ x, ϕ x ∂P))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((∫ x, ϕ x ∂M - ∫ x, ϕ x ∂P) - (∫ x, ϕ x ∂M - ∫ x, ϕ x ∂P))) :=
    h_1d.sub tendsto_const_nhds
  simpa [sub_self] using h_sub.congr' h_eq

/-- *Verification entry point: 1D pathwise derivative method
(`ref/mass/point_mass_vonMise.tex` §4).*

Given:
- `hPath : PathwiseDifferentiableAt P ⊤ Ψ` (model regularity);
- `hf : MemLp f 2 P`;
- `R : Measure Ω → ℝ` (the user's chosen remainder mapping);
- `h_exp` — the von Mises expansion equation with this `R`;
- `h_1d` — for every `g ∈ IsBoundedMixtureScore`, the 1D pathwise
  right-derivative of `Ψ` along the bounded-density path
  `P.withDensity(1 + g)` exists and equals `∫f·g dP` (i.e.,
  `∫f d(P_g − P)`, since `g ∈ L²₀(P)` so `∫f dP_g − ∫f dP = ∫f·g dP`).

Conclude: the centered candidate `φ := f − ∫f dP` is the efficient
influence function over the full tangent `⊤`.

This is the **sixth** verification entry point alongside
`candidate_isEIF_of_full_tangent`, `candidate_isEIF_of_membership`,
`eif_via_Gateaux`, `eif_via_TV_frechet`, `eif_via_TV_QMD`, and
`eif_via_vonMises`. The hypothesis structure most closely matches
the textbook von Mises pipeline: the user computes `R` algebraically
from the expansion equation and verifies the 1D derivative formula
along bounded-density paths via Mathlib's standard real-calculus
toolbox.

Reference: `ref/mass/point_mass_vonMise.tex` §4 (Condition
"1D Pathwise Differentiability") + Lemma 7. -/
theorem eif_via_Point_mass
    {Ψ : Measure Ω → ℝ}
    (hPath : PathwiseDifferentiableAt P
              (⊤ : Submodule ℝ ↥(L2ZeroMean P)) Ψ)
    {f : Ω → ℝ} (hf : MemLp f 2 P)
    (h_1d : ∀ (g : ↥(L2ZeroMean P)), IsBoundedMixtureScore g →
              Has1DPathwiseDeriv P Ψ f
                (P.withDensity (fun ω =>
                  ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)))) :
    IsEfficientInfluenceFunction P (⊤ : Submodule ℝ ↥(L2ZeroMean P))
      hPath.derivative
      ((centeredCandidate (P := P) f hf).toL2ZeroMean) := by
  -- Strategy: build `IsTVFrechetMixtureExpansion P Ψ f` and chain
  -- through `eif_via_TV_frechet`.
  --
  -- Per-Q construction: from `Q ≪ P` with bounded RN-derivative, build
  -- the bounded score `g := dQ/dP − 1 ∈ B`, identify `withDensity(1+g)`
  -- with `Q`, and apply `h_1d g hg_bdd` after rewriting the limit value
  -- `∫f d(withDensity(1+g)) − ∫f dP = ∫f dQ − ∫f dP`.
  apply eif_via_TV_frechet hPath hf
  intro Q _hQ_inst hQ_ac hQ_bdd
  -- Reuse the construction from `vonMises_imp_TVFrechetMixture`.
  obtain ⟨M_RN, hM_RN⟩ := hQ_bdd
  set h_RN : Ω → ℝ := fun ω => (Q.rnDeriv P ω).toReal with hh_RN_def
  set g_raw : Ω → ℝ := fun ω => h_RN ω - 1 with hg_raw_def
  have h_RN_nn : ∀ ω, 0 ≤ h_RN ω := fun _ => ENNReal.toReal_nonneg
  have h_RN_meas : Measurable h_RN :=
    (Measure.measurable_rnDeriv Q P).ennreal_toReal
  have hg_meas : Measurable g_raw := h_RN_meas.sub measurable_const
  have hg_bdd_ae : ∀ᵐ ω ∂P, |g_raw ω| ≤ |M_RN| + 1 := by
    filter_upwards [hM_RN] with ω hω
    have hh_nn : 0 ≤ h_RN ω := h_RN_nn ω
    have hh_le : h_RN ω ≤ |M_RN| := hω.trans (le_abs_self _)
    change |h_RN ω - 1| ≤ |M_RN| + 1
    have h3 : -(|M_RN| + 1) ≤ h_RN ω - 1 := by
      have : (0 : ℝ) ≤ |M_RN| := abs_nonneg _; linarith
    have h4 : h_RN ω - 1 ≤ |M_RN| + 1 := by linarith
    exact abs_le.mpr ⟨h3, h4⟩
  have hg_lb : ∀ᵐ ω ∂P, -1 ≤ g_raw ω := by
    filter_upwards with ω
    have : 0 ≤ h_RN ω := h_RN_nn ω
    change -1 ≤ h_RN ω - 1; linarith
  have hg_memLp : MemLp g_raw 2 P := by
    refine MemLp.of_bound hg_meas.aestronglyMeasurable (|M_RN| + 1) ?_
    filter_upwards [hg_bdd_ae] with ω hω
    rw [Real.norm_eq_abs]; exact hω
  have h_rn_lt_top : ∀ᵐ ω ∂P, Q.rnDeriv P ω < ⊤ :=
    Measure.rnDeriv_lt_top Q P
  have h_int_h_RN : ∫ ω, h_RN ω ∂P = 1 := by
    change ∫ ω, (Q.rnDeriv P ω).toReal ∂P = 1
    rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable
          h_rn_lt_top,
        Measure.lintegral_rnDeriv hQ_ac]
    simp
  have h_int_g_zero : ∫ ω, g_raw ω ∂P = 0 := by
    have hg_int : Integrable g_raw P :=
      hg_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hh_int : Integrable h_RN P := hg_int.add (integrable_const 1) |>.congr
      (by filter_upwards with ω; change g_raw ω + 1 = h_RN ω; simp [hg_raw_def])
    change ∫ ω, h_RN ω - 1 ∂P = 0
    rw [integral_sub hh_int (integrable_const 1), integral_const,
        h_int_h_RN]
    simp
  set gLp : Lp ℝ 2 P := MemLp.toLp g_raw hg_memLp with hgLp_def
  have h_gLp_ae : (gLp : Ω → ℝ) =ᵐ[P] g_raw :=
    MemLp.coeFn_toLp hg_memLp
  have hgLp_in_L20 : gLp ∈ L2ZeroMean P := by
    change gLp ∈ LinearMap.ker (integralL2 P).toLinearMap
    rw [LinearMap.mem_ker]
    change ⟪oneL2 P, gLp⟫_ℝ = 0
    rw [MeasureTheory.L2.inner_def]
    have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_int_eq :
        ∫ a, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a, (gLp : Ω → ℝ) a⟫_ℝ ∂P
          = ∫ a, g_raw a ∂P := by
      apply integral_congr_ae
      filter_upwards [h_one_ae, h_gLp_ae] with a ha hg
      have hcomm : ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
                    (gLp : Ω → ℝ) a⟫_ℝ
            = (gLp : Ω → ℝ) a * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
      rw [hcomm, ha, hg, mul_one]
    rw [h_int_eq, h_int_g_zero]
  set g_L20 : ↥(L2ZeroMean P) := ⟨gLp, hgLp_in_L20⟩ with hg_L20_def
  have hg_bdd_score : IsBoundedMixtureScore g_L20 := by
    refine ⟨⟨|M_RN| + 1, ?_⟩, ?_⟩
    · filter_upwards [h_gLp_ae, hg_bdd_ae] with ω hω hω'
      change |((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω| ≤ |M_RN| + 1
      rw [show ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω = (gLp : Ω → ℝ) ω from rfl,
          hω]
      exact hω'
    · filter_upwards [h_gLp_ae, hg_lb] with ω hω hω'
      change -1 ≤ ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω
      rw [show ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω = (gLp : Ω → ℝ) ω from rfl,
          hω]
      exact hω'
  -- Q_target := P.withDensity(1+g_L20).
  set Q_target : Measure Ω := P.withDensity (fun ω =>
      ENNReal.ofReal (1 + ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω))
    with hQ_target_def
  have h_one_plus_g_ae :
      (fun ω => 1 + ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω)
        =ᵐ[P] h_RN := by
    filter_upwards [h_gLp_ae] with ω hω
    rw [show ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω = (gLp : Ω → ℝ) ω from rfl,
        hω]
    change 1 + (h_RN ω - 1) = h_RN ω; ring
  have h_ofReal_h_RN_ae :
      (fun ω => ENNReal.ofReal (h_RN ω)) =ᵐ[P] Q.rnDeriv P := by
    filter_upwards [h_rn_lt_top] with ω hω
    change ENNReal.ofReal ((Q.rnDeriv P ω).toReal) = Q.rnDeriv P ω
    exact ENNReal.ofReal_toReal hω.ne
  have hQ_target_eq_Q : Q_target = Q := by
    rw [hQ_target_def]
    have h_density_ae :
        (fun ω => ENNReal.ofReal (1 + ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω))
          =ᵐ[P] Q.rnDeriv P := by
      filter_upwards [h_one_plus_g_ae, h_ofReal_h_RN_ae] with ω hω hω'
      rw [show 1 + ((g_L20 : Lp ℝ 2 P) : Ω → ℝ) ω = h_RN ω from hω]
      exact hω'
    rw [withDensity_congr_ae h_density_ae,
        Measure.withDensity_rnDeriv_eq Q P hQ_ac]
  -- Apply h_1d g_L20 hg_bdd_score: gives `Has1DPathwiseDeriv P Ψ f Q_target`.
  have h_1d_target : Has1DPathwiseDeriv P Ψ f Q_target := h_1d g_L20 hg_bdd_score
  -- Identify Q_target = Q in both the path and the limit value.
  -- The limit value `∫f dQ_target - ∫f dP = ∫f dQ - ∫f dP`.
  rw [hQ_target_eq_Q] at h_1d_target
  exact h_1d_target

/-! ### Fréchet differentiability entry point

Reference: `ref/mass/clean_plan_vonMises.md` §2 (Fréchet
differentiability as a single subsuming hypothesis).

The user-facing hypothesis is the **operational form of
Fréchet-differentiability over the entire space of admissible signed
measures**: `Has1DPathwiseDeriv` along *every* probability target
measure `M` (with the candidate `ϕ` integrable against `M`). This
subsumes both the bounded-density-path 1D condition (used by
`eif_via_Point_mass`) AND the point-mass-path 1D condition
(giving the explicit formula `(d/dt) Ψ(P_{t,x})|_{t=0⁺} = f(x) − ∫f dP`
as a free corollary).

For the Riesz-representer interpretation: a Fréchet derivative
`dΨ_P : SignedMeasure Ω → ℝ` represented by integration against `ϕ`
gives `dΨ_P(M − P) = ∫ϕ d(M − P) = ∫ϕ dM − ∫ϕ dP`. The
linear-mixture path `(1−t)P + tM` then has 1D right-derivative
`dΨ_P(M − P)`, which is exactly `Has1DPathwiseDeriv` with this
target value. -/

/-- *Fréchet form:* `Has1DPathwiseDeriv` along every admissible
probability target measure `M`.

Operational form of "the candidate `ϕ : Ω → ℝ` is the Riesz
representer of the Fréchet derivative of `Ψ` at `P` over the space
of signed measures with `ϕ`-integrable perturbations".

The user supplies, for any probability `M` against which `ϕ` is
integrable, the 1D pathwise right-derivative along `(1−t)P + tM`. This
is typically discharged via Mathlib's real-calculus library after
expressing `Ψ((1−t)P + tM)` as a 1D scalar formula in `t`. -/
def HasFrechetDeriv (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : Measure Ω → ℝ) (ϕ : Ω → ℝ) : Prop :=
  ∀ (M : Measure Ω) [IsProbabilityMeasure M],
    Integrable ϕ M → Has1DPathwiseDeriv P Ψ ϕ M

/-- *Verification entry point: Fréchet method
(`ref/mass/clean_plan_vonMises.md` §2).*

Given:
- `hPath : PathwiseDifferentiableAt P ⊤ Ψ` (model regularity);
- `hf : MemLp f 2 P`;
- `h_Frechet : HasFrechetDeriv P Ψ f` (single subsuming hypothesis:
  `Has1DPathwiseDeriv` along every admissible probability target).

Conclude: the centered candidate `φ := f − ∫f dP` is the efficient
influence function over the full tangent `⊤`.

This entry point fronts **the strongest single-hypothesis
verification recipe**: the user supplies one Fréchet-style
derivative formula valid for all admissible target measures
(including point masses), and the library does the rest.

Proof: derive the per-bounded-score `Has1DPathwiseDeriv` (needed by
`eif_via_Point_mass`) from `HasFrechetDeriv` by instantiating at the
specific target measure `M := P.withDensity(1 + g)` with `g ∈ B`.
Integrability of `f` against this `M` follows from `Integrable f P`
plus the bounded RN-derivative `1 + g ≤ 1 + ‖g‖_∞` via
`integrable_of_rnDeriv_bound`. -/
theorem eif_via_Point_mass_Frechet
    {Ψ : Measure Ω → ℝ}
    (hPath : PathwiseDifferentiableAt P
              (⊤ : Submodule ℝ ↥(L2ZeroMean P)) Ψ)
    {f : Ω → ℝ} (hf : MemLp f 2 P)
    (h_Frechet : HasFrechetDeriv P Ψ f) :
    IsEfficientInfluenceFunction P (⊤ : Submodule ℝ ↥(L2ZeroMean P))
      hPath.derivative
      ((centeredCandidate (P := P) f hf).toL2ZeroMean) := by
  apply eif_via_Point_mass hPath hf
  intro g hg_bdd_score
  -- Target measure M := P.withDensity(1 + g).
  set M : Measure Ω := P.withDensity (fun ω =>
      ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) with hM_def
  -- Replicate the IsProbabilityMeasure construction from
  -- `gateaux_representer_eq_pathwise_derivative`.
  obtain ⟨M_g, h_abs_M⟩ := hg_bdd_score.1
  have h_lb_g : ∀ᵐ ω ∂P, -1 ≤ ((g : Lp ℝ 2 P) : Ω → ℝ) ω := hg_bdd_score.2
  have h_g_int : Integrable (((g : Lp ℝ 2 P) : Ω → ℝ)) P :=
    (Lp.memLp (g : Lp ℝ 2 P)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_one_plus_g_nn : ∀ᵐ ω ∂P,
      0 ≤ 1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by
    filter_upwards [h_lb_g] with ω hω; linarith
  have h_one_plus_g_int : Integrable
      (fun ω => 1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω) P :=
    (integrable_const _).add h_g_int
  have h_g_meas : AEMeasurable (((g : Lp ℝ 2 P) : Ω → ℝ)) P :=
    (Lp.aestronglyMeasurable (g : Lp ℝ 2 P)).aemeasurable
  have h_density_meas : AEMeasurable
      (fun ω => ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω)) P :=
    ((aemeasurable_const).add h_g_meas).ennreal_ofReal
  have h_int_g_zero : ∫ ω, ((g : Lp ℝ 2 P) : Ω → ℝ) ω ∂P = 0 := by
    have h_mem : (g : Lp ℝ 2 P) ∈ L2ZeroMean P := g.2
    change (g : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at h_mem
    rw [LinearMap.mem_ker] at h_mem
    have h_inner : ⟪oneL2 P, (g : Lp ℝ 2 P)⟫_ℝ = 0 := h_mem
    rw [MeasureTheory.L2.inner_def] at h_inner
    have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_int_eq :
        ∫ a, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
              ((g : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ ∂P
          = ∫ a, ((g : Lp ℝ 2 P) : Ω → ℝ) a ∂P := by
      apply integral_congr_ae
      filter_upwards [h_one_ae] with a ha
      have hcomm : ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
                    ((g : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
            = ((g : Lp ℝ 2 P) : Ω → ℝ) a
                * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
      rw [hcomm, ha, mul_one]
    rw [h_int_eq] at h_inner
    exact h_inner
  haveI hM_prob : IsProbabilityMeasure M := by
    refine ⟨?_⟩
    rw [hM_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal h_one_plus_g_int h_one_plus_g_nn]
    have h_int_eq :
        ∫ ω, 1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω ∂P = 1 := by
      rw [integral_add (integrable_const _) h_g_int, integral_const,
          h_int_g_zero]; simp
    rw [h_int_eq, ENNReal.ofReal_one]
  -- M ≪ P with bounded RN-derivative ≤ 1 + |M_g|.
  have hM_ac : M ≪ P := by
    rw [hM_def]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hM_bdd : ∃ MM : ℝ, ∀ᵐ ω ∂P, (M.rnDeriv P ω).toReal ≤ MM := by
    refine ⟨1 + |M_g|, ?_⟩
    have h_rn : M.rnDeriv P =ᵐ[P]
        fun ω => ENNReal.ofReal (1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω) := by
      rw [hM_def]
      exact Measure.rnDeriv_withDensity₀ P h_density_meas
    filter_upwards [h_rn, h_abs_M, h_lb_g] with ω hω h_abs h_lb
    rw [hω]
    have h_nn : 0 ≤ 1 + ((g : Lp ℝ 2 P) : Ω → ℝ) ω := by linarith
    rw [ENNReal.toReal_ofReal h_nn]
    have h_M_le : ((g : Lp ℝ 2 P) : Ω → ℝ) ω ≤ |M_g| :=
      (le_abs_self _).trans h_abs |>.trans (le_abs_self _)
    linarith
  -- Integrability of f against M.
  have hf_int_P : Integrable f P :=
    hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hf_int_M : Integrable f M :=
    integrable_of_rnDeriv_bound hf_int_P hM_ac hM_bdd
  -- Apply h_Frechet at this M.
  exact h_Frechet M hf_int_M

/-- *Bonus: explicit point-mass formula from Fréchet differentiability.*

Specialising `HasFrechetDeriv` to the point-mass target `M = δ_x`
recovers `vonMises_pointMass_derivative` for free: the 1D right
derivative along `(1−t)P + tδ_x` exists and equals `f(x) − ∫f dP`.

This is the `point_mass_vonMise.tex` Theorem 1, Part 1 conclusion,
delivered as an immediate corollary of the Fréchet hypothesis. -/
theorem hasFrechetDeriv_pointMass_value
    {Ψ : Measure Ω → ℝ} {f : Ω → ℝ}
    (hf_meas : Measurable f) (_hf_int_P : Integrable f P)
    (h_Frechet : HasFrechetDeriv P Ψ f) (x : Ω) :
    Filter.Tendsto (fun t : ℝ =>
      (Ψ (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Measure.dirac x)
        - Ψ P) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (f x - ∫ ω, f ω ∂P)) := by
  have hf_strong : StronglyMeasurable f := hf_meas.stronglyMeasurable
  have hf_int_dirac : Integrable f (Measure.dirac x) :=
    integrable_dirac' hf_strong (by simp [enorm_eq_nnnorm,
      ENNReal.coe_lt_top])
  have h_int_dirac_eq : ∫ ω, f ω ∂(Measure.dirac x) = f x :=
    integral_dirac' f x hf_strong
  have h_1d := h_Frechet (Measure.dirac x) hf_int_dirac
  -- Has1DPathwiseDeriv at M = δ_x has limit value `∫f dδ_x − ∫f dP`.
  -- Rewrite this to `f x − ∫f dP`.
  have h_eq : f x - ∫ ω, f ω ∂P
        = ∫ ω, f ω ∂(Measure.dirac x) - ∫ ω, f ω ∂P := by
    rw [h_int_dirac_eq]
  rw [h_eq]
  exact h_1d

end AsymptoticStatistics.Core.MassMethod
