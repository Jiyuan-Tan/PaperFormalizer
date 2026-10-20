module
public import StatLean.AsymptoticStatistics.Core.Hilbert
public import StatLean.AsymptoticStatistics.Core.CandidateIF
public import StatLean.AsymptoticStatistics.ForMathlib.QMDAnalytic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Quadratic-mean-differentiable paths (dominated case)

A one-parameter curve $t \mapsto Q_t$ of probability measures through $P$
(so $Q_0 = P$), all dominated by a fixed $\sigma$-finite measure $\mu$ with
densities $p_t := \mathrm{d}Q_t/\mathrm{d}\mu$, is *differentiable in
quadratic mean* (QMD) at $t = 0$ with *score function* $g$ when the
square-root densities admit the first-order expansion
$$
  \frac{1}{|t|}\,
  \Bigl\| \sqrt{p_t} - \sqrt{p_0} - \tfrac{t}{2}\, g \sqrt{p_0} \Bigr\|_{L^2(\mu)}
  \;\longrightarrow\; 0
  \qquad (t \to 0).
$$
The score $g$ then lies in $L^2_0(P)$: it has mean zero, $\int g \,\mathrm{d}P = 0$,
and is square-integrable, $\int g^2 \,\mathrm{d}P < \infty$ (the analytic
content of vdV Lemma 25.14). The companion lemma `score_in_L2ZeroMean`
proves the converse direction for users carrying a bare measurable score:
any measurable $g$ satisfying the QMD limit above agrees $P$-almost
everywhere with an element of $L^2_0(P)$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge
Series in Statistical and Probabilistic Mathematics, Cambridge University
Press, 1998. Chapter 25 (Semiparametric Models), §25.3, Eq (25.13) (the QMD
condition via square-root densities) and Lemma 25.14 (the score has mean
zero and is square-integrable).

**Proof formalization notes.**
We formalize the *dominated specialisation*: a fixed dominating measure
`μ`, densities `pₜ := dQₜ/dμ`, and the QMD condition stated as L²(μ)
convergence of `√pₜ - √p₀ - (t/2) g √p₀` to zero faster than `t`. vdV
§25.3 explicitly authorizes taking the model dominated "for simplicity";
the canonical nondominated form of Eq (25.13) uses formal `dP^{1/2}`
symbols, which Mathlib's RN-derivative + `eLpNorm` machinery cannot carry,
so the nondominated form is deferred.

The score field is typed `↥(L2ZeroMean P)`, so "mean zero +
square-integrable" (the analytic content of vdV Lemma 25.14) is enforced by
the Lean type system. The standalone `score_in_L2ZeroMean` lemma ships
separately as a consistency result for users with bare-function scores; its
proof outline (square-integrability via triangle inequality on the QMD
remainder plus `‖√pₜ‖²_{L²(μ)} = 1`; mean zero via Cauchy–Schwarz against
`√p₀` and the affinity bound `∫√pₜ√p₀ ≤ 1`) lives in that lemma's
docstring, with the two analytic engines in `ForMathlib/QMDAnalytic.lean`.
The QMD limit is stated in `ℝ≥0∞`-quotient form `eLpNorm … / ofReal |t| → 0`
rather than the classical `.toReal²/t² → 0` form: the latter would be
vacuously satisfied whenever the residual leaves `L²(μ)` (since
`(⊤ : ℝ≥0∞).toReal = 0`), whereas the `ℝ≥0∞` form genuinely forces
finiteness of the residual L²-norm near `t = 0`. The classical form and a
`MemLp` witness are recovered as corollaries `QMDPath.qmd_limit_toReal_sq`
and `QMDPath.residual_memLp_eventually`.

Headline declarations: `QMDPath`, `score_in_L2ZeroMean`.

**Bibliographic comments.** Differentiability in quadratic mean originates
with L. Le Cam, "On the assumptions used to prove asymptotic normality of
maximum likelihood estimates", *Annals of Mathematical Statistics* 41(3)
(1970), 802–828. Le Cam introduced the square-root-density (DQM) condition
precisely to replace the classical pointwise-differentiability and
domination hypotheses of Cramér with a single quadratic-mean condition,
under which asymptotic normality of the MLE still holds. van der Vaart's
Chapter 25 develops this for the more general semiparametric setting of
differentiable submodels (paths) and their score functions; the mean-zero
property of the score (Lemma 25.14) is a direct consequence of the DQM
expansion that Le Cam established for the parametric case.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

-- The structure name `QMDPath` matches the namespace; this is intentional —
-- the file is about exactly that one structure plus its consistency lemma.
set_option linter.dupNamespace false

namespace AsymptoticStatistics.Core.QMDPath

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A *dominated quadratic-mean-differentiable path* at the probability
measure `P`: a curve `t ↦ curve t : ℝ → Measure Ω` through `P` (at
`t = 0`) that is dominated by a fixed measure `dominating`, with score
function `score : ↥(L2ZeroMean P)` whose half is the L²(dominating)
derivative of the square-root density.

Reference: vdV §25.3, `eq:25.13`. This structure is the dominated
specialisation authorized by vdV's "for simplicity" footnote. The canonical
nondominated form, expressed with formal `dP^{1/2}` symbols, lies outside the
scope of this density-based API. -/
structure QMDPath (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- vdV §25.3, eq:25.13: the curve in the space of measures. -/
  curve : ℝ → Measure Ω
  /-- vdV §25.3: the curve passes through `P` at `t = 0`. -/
  curve_at_zero : curve 0 = P
  /-- vdV §25.3: each `curve t` is a probability measure. -/
  curve_isProbability : ∀ t, IsProbabilityMeasure (curve t)
  /-- A fixed dominating measure `μ` (vdV §25.3 footnote authorizes the
  dominated specialisation "for simplicity"). The canonical book form of
  eq 25.13 uses formal `dP^{1/2}` symbols and is *nondominated*; we
  specialise to the dominated case because Mathlib's RN-derivative +
  `eLpNorm` machinery operates on densities, not on
  square-roots-of-measures. -/
  dominating : Measure Ω
  /-- Each `curve t` is absolutely continuous w.r.t. `μ`. Vacuous in the
  nondominated form of eq 25.13. -/
  curve_absContinuous : ∀ t, curve t ≪ dominating
  /-- σ-finiteness of `dominating`, required by Mathlib's `Measure.rnDeriv`
  / `lintegral_rnDeriv`. (Probability ⇒ σ-finite, so `dominating := P`
  always satisfies it.) -/
  dominating_sigmaFinite : SigmaFinite dominating
  /-- The *score function* of the path at `P`. The type `↥(L2ZeroMean P)`
  enforces mean zero and square-integrability (the analytic half of vdV
  lem:25.14); the QMD limit below specifies *which* L²₀(P) function is the
  score. -/
  score : ↥(L2ZeroMean P)
  /-- vdV §25.3, eq:25.13: the QMD limit on square-root densities, in
  `ℝ≥0∞`-form. Writing
  `pₜ ω := ((curve t).rnDeriv dominating ω).toReal`, this asserts
    `‖√pₜ - √p₀ - (t/2) · score · √p₀‖_{L²(dominating)} / |t| → 0`
  in `ℝ≥0∞` as `t → 0` along `𝓝[≠] 0`.

  **Why `ℝ≥0∞`-form, not `.toReal`-form**: a `.toReal² / t² → 0`
  formulation would be *vacuously satisfied* whenever the residual lived
  outside `L²(dominating)` (since `(⊤ : ℝ≥0∞).toReal = 0`). The
  `ℝ≥0∞`-quotient form genuinely forces `eLpNorm residual 2 dominating < ⊤`
  for `t` in a punctured neighbourhood of `0`: otherwise the quotient
  evaluates to `⊤` and cannot tend to `0`. This matches the form used in
  the standalone `score_in_L2ZeroMean` consistency lemma (below) and in
  `ForMathlib.QMDAnalytic.IsQMDLimit`. The `MemLp` witness and the
  classical `.toReal²/t² → 0` formulation are recovered as corollaries
  `QMDPath.residual_memLp_eventually` and `QMDPath.qmd_limit_toReal_sq`. -/
  qmd_limit :
    Tendsto
      (fun t : ℝ =>
        eLpNorm (fun ω : Ω =>
          Real.sqrt ((curve t).rnDeriv dominating ω).toReal
            - Real.sqrt ((curve 0).rnDeriv dominating ω).toReal
            - (t / 2) * (score : Ω → ℝ) ω
                * Real.sqrt ((curve 0).rnDeriv dominating ω).toReal)
          2 dominating / ENNReal.ofReal |t|)
      (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞))

/-- Lift the `dominating_sigmaFinite` field of `QMDPath` to a typeclass
instance, so consumers can synthesize
`[SigmaFinite γ.dominating]` automatically. This is the gate that lets
Mathlib's RN-derivative integrability lemmas (`integral_toReal_rnDeriv`,
`lintegral_rnDeriv`, `withDensity_rnDeriv_eq`, ...) fire on `γ.dominating`
without manual instance hand-off. -/
instance {P : Measure Ω} [IsProbabilityMeasure P] (γ : QMDPath P) :
    SigmaFinite γ.dominating := γ.dominating_sigmaFinite

namespace QMDPath

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Corollary of the `ℝ≥0∞`-form `qmd_limit`: the QMD residual integrand
is in `L²(γ.dominating)` for `t` in a punctured neighbourhood of `0`.

`MemLp` follows from `qmd_limit` by the standard "if `eLpNorm / ofReal |t|
→ 0` then eventually `eLpNorm < ofReal |t|` which is `< ⊤`" pattern
(mirrors the `QMDAnalytic.IsQMDLimit ⇒ MemLp` chain in
`ForMathlib/QMDAnalytic.lean`). -/
theorem residual_memLp_eventually (γ : QMDPath P) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      MemLp (fun ω : Ω =>
        Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
          - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
          - (t / 2) * (γ.score : Ω → ℝ) ω
              * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
        2 γ.dominating := by
  -- The residual is AEStronglyMeasurable from the rnDeriv square root and
  -- the score-coercion measurability.
  have h_score_sm :
      AEStronglyMeasurable (((γ.score : Lp ℝ 2 P) : Ω → ℝ)) γ.dominating := by
    -- Score coercion is StronglyMeasurable on its own measure space; the
    -- target measure here is γ.dominating, which the score is not typed
    -- against. Use plain measurability of the underlying Lp representative,
    -- which is StronglyMeasurable on *any* MeasurableSpace structure.
    exact (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).aestronglyMeasurable
  have h_res_aesm : ∀ t : ℝ,
      AEStronglyMeasurable (fun ω : Ω =>
        Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
          - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
          - (t / 2) * (γ.score : Ω → ℝ) ω
              * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
        γ.dominating := fun t => by
    have h_meas_t : AEStronglyMeasurable
        (fun ω => Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal)
        γ.dominating :=
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt).aestronglyMeasurable
    have h_meas_0 : AEStronglyMeasurable
        (fun ω => Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
        γ.dominating :=
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt).aestronglyMeasurable
    exact (h_meas_t.sub h_meas_0).sub
      (((aestronglyMeasurable_const).mul h_score_sm).mul h_meas_0)
  -- From the ℝ≥0∞ QMD limit (tends to 0), eventually the quotient is < 1.
  have h_qmd := γ.qmd_limit
  have h_lt_one : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      eLpNorm (fun ω : Ω =>
        Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
          - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
          - (t / 2) * (γ.score : Ω → ℝ) ω
              * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
        2 γ.dominating / ENNReal.ofReal |t| < 1 := by
    have h_iso : Set.Iio (1 : ℝ≥0∞) ∈ 𝓝 (0 : ℝ≥0∞) :=
      Iio_mem_nhds (by norm_num)
    exact h_qmd h_iso
  -- The `𝓝[≠]` filter already excludes `t = 0`, so `|t| > 0` and
  -- `ofReal |t| > 0`. Multiply both sides to get `eLpNorm < ofReal |t| < ⊤`.
  have h_self_ne : {x : ℝ | x ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := self_mem_nhdsWithin
  filter_upwards [h_lt_one, h_self_ne] with t ht_lt ht_ne
  set RES : Ω → ℝ := fun ω =>
    Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
      - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
      - (t / 2) * (γ.score : Ω → ℝ) ω
          * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
  have habs : 0 < |t| := abs_pos.mpr ht_ne
  have hofreal_pos : 0 < ENNReal.ofReal |t| := ENNReal.ofReal_pos.mpr habs
  have hofreal_ne_zero : ENNReal.ofReal |t| ≠ 0 := hofreal_pos.ne'
  have hofreal_ne_top : ENNReal.ofReal |t| ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_eLp_lt : eLpNorm RES 2 γ.dominating < ENNReal.ofReal |t| := by
    calc eLpNorm RES 2 γ.dominating
        = eLpNorm RES 2 γ.dominating / ENNReal.ofReal |t|
            * ENNReal.ofReal |t| := by
          rw [ENNReal.div_mul_cancel hofreal_ne_zero hofreal_ne_top]
      _ < 1 * ENNReal.ofReal |t| :=
          ENNReal.mul_lt_mul_left hofreal_ne_zero hofreal_ne_top ht_lt
      _ = ENNReal.ofReal |t| := one_mul _
  exact ⟨h_res_aesm t, lt_trans h_eLp_lt ENNReal.ofReal_lt_top⟩

/-- Corollary of the `ℝ≥0∞`-form `qmd_limit`: the classical
`.toReal² / t² → 0` formulation. Used by downstream consumers that need
the ratio in `ℝ` rather than `ℝ≥0∞`. -/
theorem qmd_limit_toReal_sq (γ : QMDPath P) :
    Tendsto
      (fun t : ℝ =>
        (eLpNorm (fun ω : Ω =>
          Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
            - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
            - (t / 2) * (γ.score : Ω → ℝ) ω
                * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
          2 γ.dominating).toReal ^ 2 / t ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  -- Strategy: square the ℝ-valued quotient `(eLpNorm).toReal / |t|` and
  -- use `t² = |t|²` to identify it with `(eLpNorm).toReal² / t²`.
  -- The `(eLpNorm).toReal / |t|` quotient tends to 0 via toReal of the
  -- ℝ≥0∞ quotient (modulo eventual-finiteness handled by
  -- `residual_memLp_eventually`).
  have h_qmd := γ.qmd_limit
  -- Step 1: `Tendsto ((·).toReal ∘ ...)` from continuous_toReal.
  have h_toReal :
      Tendsto (fun t : ℝ =>
          (eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
              - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
              - (t / 2) * (γ.score : Ω → ℝ) ω
                  * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
            2 γ.dominating / ENNReal.ofReal |t|).toReal)
        (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have h_cont : ContinuousAt ENNReal.toReal (0 : ℝ≥0∞) :=
      ENNReal.continuousAt_toReal (by norm_num)
    exact (h_cont.tendsto.comp h_qmd)
  -- Step 2: rewrite `(eLpNorm / ofReal|t|).toReal = (eLpNorm).toReal / |t|`
  -- eventually (i.e., for `t ≠ 0`, where finiteness holds via
  -- `residual_memLp_eventually`).
  have h_self_ne : {x : ℝ | x ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := self_mem_nhdsWithin
  have h_mem := residual_memLp_eventually γ
  have h_ratio_eq :
      ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
        (eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
              - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
              - (t / 2) * (γ.score : Ω → ℝ) ω
                  * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
            2 γ.dominating / ENNReal.ofReal |t|).toReal
          = (eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
              - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
              - (t / 2) * (γ.score : Ω → ℝ) ω
                  * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
            2 γ.dominating).toReal / |t| := by
    filter_upwards [h_self_ne, h_mem] with t ht_ne ht_mem
    have habs : 0 < |t| := abs_pos.mpr ht_ne
    have hofreal_pos : 0 < ENNReal.ofReal |t| := ENNReal.ofReal_pos.mpr habs
    have h_eLp_ne_top : eLpNorm _ 2 γ.dominating ≠ ⊤ := ht_mem.2.ne
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal habs.le]
  have h_toReal' :
      Tendsto (fun t : ℝ =>
          (eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
              - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
              - (t / 2) * (γ.score : Ω → ℝ) ω
                  * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
            2 γ.dominating).toReal / |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ)) :=
    h_toReal.congr' h_ratio_eq
  -- Step 3: square the tendsto (continuity of `· ^ 2` at 0).
  have h_sq :
      Tendsto (fun t : ℝ =>
          ((eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
              - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
              - (t / 2) * (γ.score : Ω → ℝ) ω
                  * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
            2 γ.dominating).toReal / |t|) ^ 2)
        (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact this.comp h_toReal'
  -- Step 4: rewrite `(a/|t|)² = a² / t²` since `|t|² = t²`.
  have h_eq :
      (fun t : ℝ =>
        ((eLpNorm (fun ω : Ω =>
          Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
            - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
            - (t / 2) * (γ.score : Ω → ℝ) ω
                * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
          2 γ.dominating).toReal / |t|) ^ 2)
        = fun t : ℝ =>
          (eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
              - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
              - (t / 2) * (γ.score : Ω → ℝ) ω
                  * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
            2 γ.dominating).toReal ^ 2 / t ^ 2 := by
    funext t
    rw [div_pow, sq_abs]
  rw [← h_eq]
  exact h_sq

end QMDPath

/-- Analytic part of vdV lem:25.14 (consistency form). If a measurable
function `g : Ω → ℝ` satisfies the bare QMD limit on the square-root
density expansion, then `g` agrees `P`-a.e. with an element of
`↥(L2ZeroMean P)` — i.e., `g` has mean zero and is square-integrable
under `P`.

Reference: vdV §25.3, lem:25.14 (analytic part).

This lemma's hypothesis and the structure's `qmd_limit` field use the same
`ℝ≥0∞`-form `eLpNorm … / ENNReal.ofReal |t| → 0`, which genuinely forces
square-integrability of `g · √p₀` for small `t`.

We additionally assume `∀ t, IsProbabilityMeasure (curve t)` (the
`curve_isProbability` field of `QMDPath`); without it, `(curve t)(univ)`
need not equal `1` and the L²(μ)-norm bound on `√(curve t).rnDeriv μ`
fails.

Proof outline:
1. Square-integrability. Triangle inequality on the QMD remainder,
   together with `‖√(curve t).rnDeriv μ‖_{L²(μ)}² = (curve t)(univ) = 1`,
   bounds `‖(t/2) g √p₀‖_{L²(μ)}` for some specific small `t`, hence
   `g · √p₀ ∈ L²(μ)`. By `withDensity_rnDeriv_eq` + the
   integrable-with-density bridge, `g ∈ L²(P)`.
2. Mean zero. Cauchy–Schwarz against `√p₀` gives
   `|∫ rₜ · √p₀ dμ| ≤ ‖rₜ‖_{L²(μ)} · 1 = o(t)`, where
   `rₜ := √pₜ − √p₀ − (t/2) g √p₀`. Rearranging,
   `∫√pₜ√p₀ dμ − 1 − (t/2)∫g dP = o(t)`. Combined with the affinity
   bound `∫√pₜ√p₀ dμ ≤ 1` (Cauchy–Schwarz), `(t/2)∫g dP ≤ o(t)`;
   two-sided (`t ↘ 0` and `t ↗ 0`) forces `∫ g dP = 0`.
3. Package into `CandidateIF P` and apply `CandidateIF.toL2ZeroMean`.

The two analytic engines live in `ForMathlib/QMDAnalytic.lean`; their
density helpers in `ForMathlib/RnDerivSqrt.lean`. -/
theorem score_in_L2ZeroMean
    {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : Measure Ω} [SigmaFinite μ] (curve : ℝ → Measure Ω)
    (h_prob : ∀ t, IsProbabilityMeasure (curve t))
    (h_zero : curve 0 = P) (h_ac : ∀ t, curve t ≪ μ)
    (g : Ω → ℝ) (hg_meas : Measurable g)
    (h_qmd :
      Tendsto
        (fun t : ℝ =>
          eLpNorm (fun ω : Ω =>
            Real.sqrt ((curve t).rnDeriv μ ω).toReal
              - Real.sqrt ((curve 0).rnDeriv μ ω).toReal
              - (t / 2) * g ω
                  * Real.sqrt ((curve 0).rnDeriv μ ω).toReal)
            2 μ / ENNReal.ofReal |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞))) :
    ∃ g' : ↥(L2ZeroMean P), g =ᵐ[P] (g' : Ω → ℝ) := by
  -- The `h_qmd` hypothesis matches `IsQMDLimit curve μ g` definitionally
  -- (the inline lambda equals `qmdRem curve μ g t` by definition).
  have h_qmd' :
      AsymptoticStatistics.ForMathlib.QMDAnalytic.IsQMDLimit curve μ g := h_qmd
  -- Stage-1 engine: `g · √p_0 ∈ L²(μ)`.
  have h_g_sqrt :
      MemLp (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.QMDAnalytic.memLp_two_score_mul_sqrt_of_qmd
      h_prob h_ac hg_meas h_qmd'
  -- `P ≪ μ`, since `curve 0 = P` and `curve 0 ≪ μ`.
  have hP_ac : P ≪ μ := by rw [← h_zero]; exact h_ac 0
  -- Square-integrability under `P` (RnDerivSqrt bridge), with the
  -- pointwise rewrite `(curve 0).rnDeriv μ = P.rnDeriv μ` from `h_zero`.
  have h_g_memLp_P : MemLp g 2 P := by
    apply AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_two_of_memLp_two_mul_sqrt_rnDeriv
      hP_ac hg_meas.aestronglyMeasurable
    -- Rewrite `P.rnDeriv μ` as `(curve 0).rnDeriv μ` using `h_zero`.
    rw [← h_zero]; exact h_g_sqrt
  -- Stage-2 engine: `∫ g d(curve 0) = 0`.
  have h_mean_zero_curve0 : ∫ ω, g ω ∂(curve 0) = 0 :=
    AsymptoticStatistics.ForMathlib.QMDAnalytic.integral_score_eq_zero_of_qmd
      h_prob h_ac hg_meas h_g_sqrt h_qmd'
  -- Translate to `∫ g dP = 0`.
  have h_mean_zero_P : ∫ ω, g ω ∂P = 0 := by
    rw [← h_zero]; exact h_mean_zero_curve0
  -- Package into `CandidateIF P` and lift.
  refine ⟨(AsymptoticStatistics.Core.CandidateIF.mk g h_g_memLp_P
            h_mean_zero_P).toL2ZeroMean, ?_⟩
  -- The L² lift of `g` agrees `P`-a.e. with `g`.
  exact (AsymptoticStatistics.Core.CandidateIF.coeFn_toL2ZeroMean
          (P := P) ⟨g, h_g_memLp_P, h_mean_zero_P⟩).symm

namespace QMDPath

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The n-fold product likelihood ratio for the perturbation parameter
`t = (√n)⁻¹`, evaluated against the dominating measure. Used to factor
product integrals.

Formalizes the integrand `∏ⱼ (dQ_{tₙ}/dμ)(Xⱼ)` from vdV §25.6 (LAN
expansion) at the QMD-induced perturbation `tₙ := (√n)⁻¹`. The product
is taken over `Fin n`; downstream LAN results establish the required
positivity and logarithmic expansion. -/
noncomputable def lr_n (γ : QMDPath P) (n : ℕ) :
    (Fin n → Ω) → ℝ≥0∞ :=
  fun X => ∏ j : Fin n, (γ.curve ((Real.sqrt n)⁻¹)).rnDeriv γ.dominating (X j)

/-- Definitional unfolding of `QMDPath.lr_n` to its product form. -/
lemma lr_n_eq (γ : QMDPath P) (n : ℕ) (X : Fin n → Ω) :
    γ.lr_n n X
      = ∏ j : Fin n,
          (γ.curve ((Real.sqrt n)⁻¹)).rnDeriv γ.dominating (X j) := rfl

/-- `QMDPath.lr_n` is a measurable function on the product space, with
respect to the product σ-algebra on `Fin n → Ω`. Used downstream to
discharge the measurability side-conditions of `lintegral_map`,
`Measure.pi`-Fubini, and the LAN expansion.

Proof: pointwise product of `(γ.curve _).rnDeriv γ.dominating` composed
with each coordinate projection, each measurable by
`Measure.measurable_rnDeriv` and `measurable_pi_apply`. -/
lemma measurable_lr_n (γ : QMDPath P) (n : ℕ) : Measurable (γ.lr_n n) := by
  unfold lr_n
  exact Finset.measurable_prod _ (fun i _ =>
    (Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply i))

end QMDPath

end AsymptoticStatistics.Core.QMDPath
