module
public import StatLean.Bayesian.DirichletLaplace.PriorSmallBall
public import StatLean.Bayesian.DirichletLaplace.NormalMeansModel
public import StatLean.Bayesian.DirichletLaplace.DenominatorLowerBound
public import StatLean.Bayesian.DirichletLaplace.TestingBound
public import StatLean.Bayesian.ForMathlib.ExpOfRealCalc

@[expose] public section

/-!
# Dirichlet–Laplace posterior compressibility — the fixed-`n`, truth-`0` engine (C12)

The fixed-dimension core behind BPPD **Theorem 3.4** (posterior compressibility of the normal-means
model under the Dirichlet–Laplace prior). Working at the true parameter `θ₀ = 0` (the case the
`S₀ᶜ`-submodel reduction in `PosteriorCompressibility.lean` produces), we bound

`E_{θ₀=0} [ posterior mass of { θ : |supp_δ(θ)| > k } ]`

expressed on the un-normalized ratio `dlNumer / dlDenom` (the passage to the abstract posterior `κ†Π`
happens once, in `PosteriorCompressibility.lean`, via `NormalMeansModel`).

Objects:
* `compress_ratio_le` — the split bound: on the event `{ D ≥ dbar }` with `dbar = e^{−r²}·Π(B(0,r))` the
  ratio is `≤ dlNumer/dbar` and its `E_{θ₀=0}`-mean equals the prior mass (change-of-measure Tonelli,
  BPPD §6, `NormalMeansModel`); on `{ D < dbar }` the Castillo–van der Vaart denominator event
  (`DenominatorLowerBound`, a Jensen / one-dimensional-Gaussian argument) contributes `≤ e^{−r²/8}`.
* `compress_ratio_le_explicit` — plug the support-count MGF / Chernoff bound (`PriorSmallBall`,
  `Π{|supp_δ| > k}`) and the small-ball lower bound into `compress_ratio_le`, collapsing the RHS to a
  single exponential in the model size, the Chernoff parameter `c`, and the radius `r`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.4 (statement p. 9,
proof pp. 18–19); the denominator-event lemma is the analogue of Ghosal–Ghosh–van der Vaart /
Castillo–van der Vaart Lemma 5.2.

**Proof formalization notes.** The skeleton is *reduction → denominator event → Chernoff*: the ratio
integral is split at `dbar`, the denominator event handled by `measure_dlDenom_lt_le`, the numerator
mean identified with the prior mass, and the prior mass bounded by the count Chernoff bound.

**Deviations.**
* **D2 (regime-dependent `r`).** The engine keeps `r` free. The `β`-regime (`PosteriorCompressibility.lean`)
  instantiates `r² = qₙ log n`; the `1/n`-regime uses `r² = qₙ`. A fixed choice cannot serve both:
  `r² = qₙ` leaves the `β`-regime failure term `e^{−qₙ}` non-vanishing for bounded `qₙ`, while
  `r² = qₙ log n` breaks the `1/n`-regime Chernoff exponent. Hence the free-`r` statement here.
* **D3 (`1 ≤ qₙ`).** For an empty support the δ-support of a continuous prior is everything and the
  radius `r² → ∞` fails; the compressibility statement is vacuous. The dimensional hypotheses below
  are engine-internal regularity; the sequence-level `1 ≤ qₙ` is enforced in the assembly headline.

**Bibliographic comments.** Posterior contraction in the sense of Ghosal, Ghosh, and van der Vaart
(*Ann. Statist.* 28 (2000), 500–531); the sparse-sequence denominator-event technique follows
Castillo and van der Vaart (*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- `dlNumer θ₀ π C` is measurable in the data `y` (the numerator is an integral in `y`). -/
lemma measurable_dlNumer {ι : Type*} [Fintype ι] (θ₀ : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [SFinite π] (C : Set (EuclideanSpace ℝ ι)) :
    Measurable (fun y => dlNumer θ₀ π C y) := by
  have huc : Measurable (Function.uncurry
      (fun (y θ : EuclideanSpace ℝ ι) => dlLR θ₀ θ y)) := by
    unfold Function.uncurry dlLR; fun_prop
  show Measurable (fun y => ∫⁻ θ, dlLR θ₀ θ y ∂(π.restrict C))
  exact huc.lintegral_prod_right

/-- `dlDenom θ₀ π` is measurable in the data `y`. -/
lemma measurable_dlDenom {ι : Type*} [Fintype ι] (θ₀ : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [SFinite π] :
    Measurable (fun y => dlDenom θ₀ π y) := by
  have hEq : (fun y => dlDenom θ₀ π y) = predictiveDensity (dlLR θ₀) π := by
    funext y; rw [dlDenom, dlNumer, setLIntegral_univ]; rfl
  rw [hEq]; exact measurable_predictiveDensity (measurable_dlLR_uncurry _)

set_option maxHeartbeats 1000000 in
/-- **Compressibility split bound** (BPPD Thm 3.4 core). At the true parameter `θ₀ = 0`, the
`E_{θ₀=0}`-mean of the un-normalized posterior ratio for `{ |supp_δ(θ)| > k }` is at most the prior
mass of that set divided by `dbar = e^{−r²}·Π(B(0,r))`, plus the denominator-event error `e^{−r²/8}`.
The two summands are the `{D ≥ dbar}` (testing/numerator) and `{D < dbar}` (denominator-event) pieces. -/
theorem compress_ratio_le {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a — DL scale at a junk-free index; engine-internal regularity.
    (ha : 0 < a)
    -- LEAN-ONLY: 0 < r — working radius of the denominator small ball; engine-internal.
    (hr : 0 < r) (k : ℕ) :
    ∫⁻ y, dlNumer (0 : EuclideanSpace ℝ ι) (dlPrior a ι) {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y
          / dlDenom (0 : EuclideanSpace ℝ ι) (dlPrior a ι) y
        ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι))
      ≤ (dlPrior a ι) {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)}
            / (ENNReal.ofReal (Real.exp (- r ^ 2))
                * (dlPrior a ι) (Metric.closedBall (0 : EuclideanSpace ℝ ι) r))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
  set π := dlPrior a ι with hπ
  set C := {θ : EuclideanSpace ℝ ι | (k : ℝ) < (dlSuppCount δ θ : ℝ)} with hC
  set dbar := ENNReal.ofReal (Real.exp (- r ^ 2))
      * π (Metric.closedBall (0 : EuclideanSpace ℝ ι) r) with hdbar
  -- Measurability of the target set, the numerator, and the denominator.
  have hcast : Measurable (fun θ : EuclideanSpace ℝ ι => ((dlSuppCount δ θ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_dlSuppCount δ)
  have hCmeas : MeasurableSet C := measurableSet_lt measurable_const hcast
  have hnumer_meas :
      Measurable (fun y => dlNumer (0 : EuclideanSpace ℝ ι) π C y) :=
    measurable_dlNumer _ _ _
  have hdenom_meas : Measurable (fun y => dlDenom (0 : EuclideanSpace ℝ ι) π y) :=
    measurable_dlDenom _ _
  have hSmeas : MeasurableSet
      {y : EuclideanSpace ℝ ι | dbar ≤ dlDenom (0 : EuclideanSpace ℝ ι) π y} :=
    measurableSet_le measurable_const hdenom_meas
  -- Denominator-event bound (`{D < dbar}`) via Castillo–van der Vaart Lemma 5.2 (C7).
  have hMeasBound :
      (gaussShiftKernel ι (0 : EuclideanSpace ℝ ι))
          {y | dlDenom (0 : EuclideanSpace ℝ ι) π y < dbar}
        ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
    have h := measure_dlDenom_lt_le π (0 : EuclideanSpace ℝ ι) hr
    have he : (- r ^ 2 / 8 : ℝ) = -(r ^ 2 / 8) := by ring
    rw [he, hdbar]
    exact h
  -- Good-event bound (`{dbar ≤ D}`): drop `D` to `dbar` and integrate the numerator.
  have hIntBound :
      ∫⁻ y in {y | dbar ≤ dlDenom (0 : EuclideanSpace ℝ ι) π y},
          dlNumer (0 : EuclideanSpace ℝ ι) π C y / dlDenom (0 : EuclideanSpace ℝ ι) π y
        ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι))
      ≤ π C / dbar := by
    calc ∫⁻ y in {y | dbar ≤ dlDenom (0 : EuclideanSpace ℝ ι) π y},
            dlNumer (0 : EuclideanSpace ℝ ι) π C y / dlDenom (0 : EuclideanSpace ℝ ι) π y
          ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι))
        ≤ ∫⁻ y in {y | dbar ≤ dlDenom (0 : EuclideanSpace ℝ ι) π y},
            dlNumer (0 : EuclideanSpace ℝ ι) π C y / dbar
          ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι)) := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hSmeas]
          exact Filter.Eventually.of_forall fun y hy => ENNReal.div_le_div_left hy _
      _ ≤ ∫⁻ y, dlNumer (0 : EuclideanSpace ℝ ι) π C y / dbar
            ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι)) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = (∫⁻ y, dlNumer (0 : EuclideanSpace ℝ ι) π C y
            ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι))) / dbar := by
          simp_rw [div_eq_mul_inv]
          rw [lintegral_mul_const'' _ hnumer_meas.aemeasurable]
      _ = π C / dbar := by
          rw [lintegral_dlNumer_eq_prior (0 : EuclideanSpace ℝ ι) π hCmeas]
  refine (lintegral_ratio_split (0 : EuclideanSpace ℝ ι) π C dbar).trans ?_
  rw [add_comm (π C / dbar)]
  exact add_le_add hMeasBound hIntBound

set_option maxHeartbeats 1000000 in
/-- **Explicit compressibility bound** (BPPD Thm 3.4 core). Feeding the support-count Chernoff bound
(`PriorSmallBall`, MGF parameter `c > 1`) and the small-ball lower bound into `compress_ratio_le`
collapses the RHS to a single exponential (`m·ζ·(c−1) − k·log c` Chernoff exponent, `ζ ≤ e·a·(8+2log
(1/δ))` from `DensityBounds`, `m = card ι`, roomy small-ball slack) plus `e^{−r²/8}`.

**Deviation (D2/D3).** The frozen stub's placeholder exponent `card·ζ·(c−1) − k·log c + 3 r²` folds
the small-ball correction `2·card·w` into `2 r²` via an unprovable `card·w ≤ r²`; the honest engine
(this statement) keeps `ζ` and `w` as supplied C3/C5 bounds and carries the additive `2·card·w`. The
headline rate/threshold (`PosteriorCompressibility`) is unchanged. -/
theorem compress_ratio_le_explicit {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a — DL scale at a junk-free index; engine-internal.
    (ha : 0 < a)
    -- LEAN-ONLY: 0 < r — working radius; engine-internal.
    (hr : 0 < r) (k : ℕ)
    -- USER-INPUT: `z` bounds the per-coordinate δ-exceedance prob ζ(δ) (supplied by C3 Lemma 3.3).
    (z : ℝ) (hz : (dlMarginal a {x : ℝ | δ < |x|}).toReal ≤ z)
    -- USER-INPUT: `w` bounds the small-ball tail at the clamped threshold s = min(r/√m, 1/2) (C3 / D7).
    (w : ℝ)
    (hw : (dlMarginal a
        {x : ℝ | min (r / Real.sqrt (Fintype.card ι : ℝ)) (1 / 2) < |x|}).toReal ≤ w)
    -- USER-INPUT: `w ≤ 1/2` unlocks the small-ball per-coordinate bound (deviation D7).
    (hw2 : w ≤ 1 / 2)
    -- LEAN-ONLY: 1 < c — free Chernoff/MGF parameter for the support-count tail; engine-internal.
    (c : ℝ) (hc : 1 < c) :
    ∫⁻ y, dlNumer (0 : EuclideanSpace ℝ ι) (dlPrior a ι) {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y
          / dlDenom (0 : EuclideanSpace ℝ ι) (dlPrior a ι) y
        ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι))
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ) * z * (c - 1)
              - (k : ℝ) * Real.log c + r ^ 2 + 2 * (Fintype.card ι : ℝ) * w))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
  set π := dlPrior a ι with hπ
  set m := (Fintype.card ι : ℝ) with hm
  -- Numerator: support-count Chernoff bound (C5), on the slightly larger set `{k ≤ count}`.
  have hπC : π {θ : EuclideanSpace ℝ ι | (k : ℝ) < (dlSuppCount δ θ : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (m * z * (c - 1) - (k : ℝ) * Real.log c)) := by
    refine (measure_mono ?_).trans (dlPrior_count_ge_le hc k hz)
    intro θ hθ
    simp only [Set.mem_setOf_eq] at hθ ⊢
    exact le_of_lt (by exact_mod_cast hθ)
  -- Denominator: small-ball lower bound (C5, deviation D7).
  have hball : ENNReal.ofReal (Real.exp (-2 * m * w))
      ≤ π (Metric.closedBall (0 : EuclideanSpace ℝ ι) r) := dlPrior_ball_zero_ge hr hw hw2
  -- Combine into the first summand of `compress_ratio_le`.
  have hfirst :
      π {θ : EuclideanSpace ℝ ι | (k : ℝ) < (dlSuppCount δ θ : ℝ)}
          / (ENNReal.ofReal (Real.exp (- r ^ 2))
              * π (Metric.closedBall (0 : EuclideanSpace ℝ ι) r))
        ≤ ENNReal.ofReal (Real.exp (m * z * (c - 1)
            - (k : ℝ) * Real.log c + r ^ 2 + 2 * m * w)) := by
    refine ENNReal.div_le_of_le_mul ?_
    calc π {θ : EuclideanSpace ℝ ι | (k : ℝ) < (dlSuppCount δ θ : ℝ)}
        ≤ ENNReal.ofReal (Real.exp (m * z * (c - 1) - (k : ℝ) * Real.log c)) := hπC
      _ = ENNReal.ofReal (Real.exp (m * z * (c - 1)
              - (k : ℝ) * Real.log c + r ^ 2 + 2 * m * w))
            * (ENNReal.ofReal (Real.exp (- r ^ 2))
              * ENNReal.ofReal (Real.exp (-2 * m * w))) := by
          rw [ofReal_exp_mul, ofReal_exp_mul]
          exact congrArg (fun t => ENNReal.ofReal (Real.exp t)) (by ring)
      _ ≤ ENNReal.ofReal (Real.exp (m * z * (c - 1)
              - (k : ℝ) * Real.log c + r ^ 2 + 2 * m * w))
            * (ENNReal.ofReal (Real.exp (- r ^ 2))
              * π (Metric.closedBall (0 : EuclideanSpace ℝ ι) r)) := by
          gcongr
  refine (compress_ratio_le ha hr k).trans ?_
  exact add_le_add hfirst le_rfl

end StatLean.Bayesian
