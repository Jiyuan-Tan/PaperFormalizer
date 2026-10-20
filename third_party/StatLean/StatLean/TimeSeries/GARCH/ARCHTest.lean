module
public import StatLean.TimeSeries.GARCH.Estimation
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Testing for the ARCH effect (FY §4.2.6, eqs. (4.48)–(4.54))

`H₀ : b₁ = ⋯ = b_p = 0` (no ARCH effect) against `H₁` at least one `b_j > 0`, inside
the ARCH(p) family with iid noise. FY's key structural observation: **under `H₀` the
observations are iid**, so the three classical statistics have iid-likelihood
asymptotics and each has a `χ²_p` null limit.

* `archNullIsIID` — the structural fact that `H₀` collapses the ARCH model to iid
  scaled noise *(the printed setup (4.48)–(4.49) has two index/sign slips — "`a_j ≥ 0`"
  for `b_j ≥ 0`, and `b_j X_{t−i}²` for `b_j X_{t−j}²`; corrected here)*;
* `archLRStat` (**eq. (4.50)**), `archScoreStat` (**eq. (4.52)**), `archWaldStat`
  (**eq. (4.54)**) and Engle's `archTR2Stat` (**eq. (4.53)**), the auxiliary-regression
  form asymptotically equivalent to the score test for normal errors;
* the **Fisher information** (eq. (4.51)) of the ARCH likelihood at the null. The three
  `χ²_p` limit statements were carried here as named debts and have been removed; see
  **Removed** immediately below.

**Removed (2026-08-10, user directive).** The module's three sorried declarations were
deleted. Nothing consumed them, and every proved declaration in the file is kept — in
particular the whole χ² character apparatus and the entire `R²`/ANOVA algebra of the
auxiliary regression, which were built *for* these debts and remain available.
* `archLRStat_chiSq_debt` — FY eq. (4.50): the likelihood-ratio statistic has the `χ²_p`
  null limit (repaired, de-vacuated form with a variance floor and a compact search region).
* `archTR2Stat_chiSq_debt` — FY eqs. (4.52)–(4.53): Engle's `T·R²` / score statistic has
  the `χ²_p` null limit.
* `archWaldStat_chiSq_debt` — FY eq. (4.54): the Wald statistic, through the
  Schur-complement block `I²²` of the information matrix, has the `χ²_p` null limit.

Everything below this point — the analysis of why the in-repo trinity does not discharge
them, the de-vacuation record, and the brick lists — is kept verbatim as history.

Recover from `bdc8143f`.

The intended route had been to reuse the in-repo iid likelihood trinity,
`StatLean/HypothesisTesting/LikelihoodMethods/TrinityChiSquared.lean`; where the wiring
does not fit the ARCH parametrization the limits stayed as named debts.

**Boundary caveat (documented, not formalized).** The alternative constrains
`b_j ≥ 0`, so under `H₀` the parameter sits on the boundary of the admissible set and
the `χ²_p` approximation is *not* valid for the constrained versions of these tests;
FY notes this and cites the one-sided-testing literature. Our statements are for the
**unconstrained** parametrization, where the classical limits do hold.

## The three `χ²_p` debts: why the in-repo trinity does not discharge them

`IsARCH.iid_of_b_eq_zero` is proved, so the structural input FY relies on is available.
The intended follow-up — instantiating `logLR_tendsto_chiSquared_affine` (and its score /
Wald companions) of `HypothesisTesting/LikelihoodMethods/TrinityChiSquared.lean` at the
null `b = 0` — was examined and **rejected**. Two independent reasons, in order of
severity.

**(1) The three frozen statements are false as they stand, for every `p ≥ 1`, so no
proof of them exists.** None of them constrains its estimator arguments to the data:
the LR debt took `c0hat`, `bhat`, `c0null` merely measurable, the `TR²` debt took
`rss`, `tss` merely measurable, and the Wald debt took `bhat` measurable and `Ihat`
entirely free. Choosing the
constants `c0hat = c0null = c0`, `bhat = 0` (resp. `rss = tss = 1`, resp. `bhat = 0`)
makes each statistic *identically zero*, so its law is `δ₀`, whose characteristic
function is the constant `1`; the conclusion then forces `charFun chiSq u = 1` for
every `u`, while `hchi` at `u = 1/2` gives `‖(1 − i)^{−p/2}‖ = 2^{−p/4} < 1`. (Both
halves of this contradiction were machine-checked.) The repair is not a proof but a
*statement* amendment, which is out of scope here: each debt needs the missing
`USER-INPUT` hypothesis that its estimator sequence is the actual (quasi-)MLE — or,
in the trinity's currency, is asymptotically linear with the ARCH score and information.

**(2) Even after that repair the trinity's shape does not fit.** Ranked by how hard
each mismatch is to bridge:

* *Fatal — the ARCH likelihood is not an iid likelihood.* The trinity's statistic is
  `logLRStatistic M est est₀ n ω = 2 Σᵢ log(p_{θ̂}(ωᵢ) / p_{θ̂₀}(ωᵢ))`: one factor per
  observation, from a single `ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))`.
  `archLRStat` is built from `archLogLik = −½ · garchQuasiLik`, i.e.
  `−½ Σ_{t=ν}^{T−1} (log σ̃_t² + x_t²/σ̃_t²)` with `σ̃_t²` the truncated ARCH recursion
  `garchTruncVol`, which reads back `p` lags of the *same* sample. The `t`-th summand is
  a function of `x_{t−1}, …, x_{t−p}` as well as `x_t`, so it is not `log p_θ(x_t)` for
  any density family: the two are different functions of the data, not one function in
  two notations. This is intrinsic, not an artefact of the definitions — the likelihood
  ratio must be evaluated across the whole `(c₀, b)` space, where the ARCH observations
  are genuinely dependent; the iid collapse of `IsARCH.iid_of_b_eq_zero` holds only on
  the null slice `b = 0`. It is exactly why FY cites Serfling §4.4.4 as the source of the
  *limit law* rather than instantiating an iid-likelihood theorem: what the null iid
  structure makes classical is the behaviour of the score and information *averages* at
  `b = 0`, not the likelihood itself.
* *Fatal — no truncation parameter.* `archLRStat` carries the presample index `ν`, and
  the LR debt carried `νseq` with `ν → ∞`, `ν/T → 0`. The trinity has no such
  parameter, so the truncated-versus-exact conditional-likelihood bookkeeping that those
  hypotheses exist to control lies entirely outside its statement.
* *Serious — regularity currency.* The trinity consumes `IsPDFOf`, joint measurability of
  `(θ, x) ↦ p_θ(x)`, `DifferentiableQuadraticMean` at `θ₀` with an explicit score,
  a positive-definite Fisher matrix in the `⟪u, J v⟫` normalisation, `IsAsymptoticallyLinear`
  estimator sequences in the full *and* restricted charts, and the amended **two-point**
  second-order envelope `henv` with an integrable envelope `Menv`. The debts here supply
  only `MemLp (ε 0) 4 μ`. Nothing in this development establishes quadratic-mean
  differentiability of the ARCH family, and the Fisher information of eq. (4.51) is named
  in this docstring but never defined.
* *Bridgeable, but not free — the sample law.* The trinity concludes about
  `productMeasure M μ θ₀ n = Measure.pi …` on `Fin n → 𝓧`, whereas the debts push forward
  `μ` on the process space `Ω`. `IsARCH.iid_of_b_eq_zero` does give that the null law of
  `(X₁, …, X_T)` is such a product, so this mismatch alone would be honest work rather
  than an obstruction.
* *Bridgeable, but not free — the conclusion form.* The trinity concludes
  `WeakConverges … (MultipleTesting.chiSquared p)`; the debts ask for pointwise `charFun`
  convergence to an abstract `chiSq` pinned by `hchi`. Bridging needs both
  `WeakConverges → charFun` convergence and `charFun (MultipleTesting.chiSquared p) u =
  (1 − 2iu)^{−p/2}`, and the latter is not proved anywhere in the repo at present.

Only the affine-null *geometry* lines up cleanly: `k = p + 1` with coordinates
`(c₀, b₁, …, b_p)`, null subspace `a + range B` for `m = 1`, `B : ℝ → ℝ^{p+1}` the first
coordinate inclusion, giving exactly the `p` degrees of freedom FY reports (and, per the
boundary caveat above, the unconstrained parametrization the trinity needs). That
agreement is real but superficial: it fixes the degrees of freedom, not the statistic.

**Verdict: the trinity is not reusable here.** The three limits stay as named debts, and
closing them calls for a *time-series* likelihood theorem — a martingale CLT for the
conditional score of the ARCH quasi-likelihood, valid over the whole `(c₀, b)` space —
rather than an instance of the iid one.

## The `hMLE` vacuity and its repair (2026-08-09b) — EXECUTED

**The finding (retained).** The `2026-08-09` amendment above, added to repair the falsity
diagnosed in item (1), overshot: it pinned the estimators by requiring them to *globally
maximize* `archLogLik` over **all** of `ℝ × ℝᵖ`. No such maximizer exists, so `hMLE` and
`hMLE0` were unsatisfiable and the two statements carried no statistical content — both
were proved by deriving `False` from their own hypotheses.

The witness is `archLogLik_unbounded` (machine-checked, **kept below**): with `b = 0` the
truncated volatility is the *constant* `c₀` (`truncVol_const`, no positivity used, because
the presample value of `archLogLik` is `c₀` itself), so at `c₀ = −δ < 0`

  `archLogLik (−δ) 0 x ν = −½·(T−ν)·log δ + (Σ_{t=ν}^{T−1} x_t²)/(2δ) → +∞`  as `δ ↓ 0`,

using `Real.log (−δ) = Real.log δ` and the *sign flip* of the `x_t²/σ̃_t²` term at a
negative `σ̃_t²`: both summands of `−½(log σ̃_t² + x_t²/σ̃_t²)` diverge to `+∞` together.
`hνT` forces `νseq T < T` for all large `T`, so the sum is nonempty at some `T` and
`hMLE`/`hMLE0` are contradicted there (`false_of_bddAbove_archLogLik`). This is not an
artefact of `Real.log`'s totalization: restricting to `c₀ > 0` does not help either, since
negative `b` coordinates drive `σ̃_t² = c₀ + Σ b_i x_{t−i}²` negative just the same.
Both lemmas are retained below as the *justification* for the amendment that follows.

**The repair, as executed.** `hMLE`/`hMLE0` now demand maximization over the **feasible
set** `K ∩ archAdmissible κ`, where

* `archAdmissible κ x ν = {(c₀, b) : σ̃_t²(c₀, b) ≥ κ for all t ∈ Ico ν T}` is the
  *data-adapted* locus on which the criterion is even defined, and
* `K` is a compact search region with the truth `(c₀, 0)` in its **interior** — the
  `hargmin`-over-`K` pattern of `ARMA/Consistency.lean`'s `mle_consistent` (Hannan §2);
* the null problem is posed on the slice `archNullSlice K = K ∩ {b = 0}`;
* the floor is **strict**, `0 < κ < c₀`.

Three certificates make this a repair rather than another guess, all proved here:

1. `exists_isMaxOn_archLogLik` (and its null companion) — the maximum *is attained*:
   `archAdmissible` is closed because with `q = 0` the truncated volatility is **affine**
   in `(c₀, b)` (`continuous_truncVol` — no recursion estimate needed), so the feasible set
   is compact, and `continuousOn_archLogLik` gives continuity there off the singularity.
2. `exists_archMLE_sequences` — estimator sequences satisfying `hMLE` *and* `hMLE0`
   verbatim **exist**, jointly. This is the exact converse of
   `false_of_bddAbove_archLogLik` and is what removes the vacuity. (It builds them by
   pointwise choice; measurability is still carried as the separate `USER-INPUT` `hmeas`,
   see the note at that theorem.)
3. `mem_interior_arch_feasible` — the truth is **interior** to the feasible set, so no
   constraint binds at the null. This is the reason the floor is imposed on the
   *data-adapted* set and not on `K`: FY's own admissible set `{b_j ≥ 0}` would put the
   null on the boundary of `K`, contradicting the interiority hypothesis and re-opening
   the one-sided boundary problem flagged above; and `κ = c₀` would do the same on the
   `c₀` axis, which is why the floor is strict.

**What is proved and what is owed.** With the repaired hypotheses, `p = 0` is *proved* for
both statements (the two feasible sets coincide, the LR statistic is identically `0`, the
Wald form is an empty sum, and `χ²₀ = δ₀` — this fixes the degrees-of-freedom
bookkeeping). `p ≥ 1` is an honest, satisfiable **debt**: the ARCH MLE asymptotics. Its
three bricks — (a) consistency of the constrained maximizer (the ARCH analogue of
`mle_consistent`), (b) the local quadratic expansion around the interior truth, (c) the
martingale CLT for the ARCH conditional score plus continuous mapping — were listed at the
theorems. The limit-law side of (c) is already discharged here
(`charFun_map_sum_sq_gaussian`, `eq_map_sum_sq_gaussian_of_charFun`).

The `TR²` debt's `hrss`/`htss` never had this defect: a least-squares minimum is
always attained, so its hypotheses were consistent throughout and it remained an honest
debt.

## The `TR²` debt: the limit law is now identified, the LM limit is what was left

Two of the five mismatches listed above are **discharged**, both concerning the *statement*
of the limit rather than the statistic:

* the χ² **character identity** — recorded above as "not proved anywhere in the repo at
  present" — is proved here as `charFun_map_sum_sq_gaussian`:
  `charFun (law of Σ_{i<p} Z_i²) u = (1 − 2iu)^{−p/2}`, from the complex Gaussian integral
  `∫ exp(−b x²) = (π/b)^{1/2}` at `b = (1 − 2iu)/2` tensored over the `p` coordinates;
* the **conclusion form** — `eq_map_sum_sq_gaussian_of_charFun` turns `hchi` into
  `chiSq = (Measure.pi (gaussianReal 0 1)).map (Σ_i x_i²)` outright, so neither a χ²
  construction nor a `WeakConverges → charFun` bridge is needed anywhere. The debt's proof
  uses this to rewrite its goal into convergence towards that concrete law.

What that statement's `sorry` still needed is exactly Engle's LM limit: under `H₀` with
Gaussian innovations the squared data `Y_t = X_t²` are iid with mean `c₀` and variance
`2c₀² > 0`, `hrss`/`htss` make the statistic the auxiliary regression's `T·R²`, and the
normal equations turn it into a quadratic form in the lag-`1..p` sample autocovariances of
`Y`; the LLN sends the Gram matrix to `Var(Y)·I_p`, the iid CLT sends `√T γ̂` to
`N(0, Var(Y)²I_p)`, and continuous mapping finishes. Of the three bricks originally listed,
**(a) the least-squares/`R²` algebra out of `hrss` is now closed** (2026-08-09b):
`archLS_normalEq` reads the normal equations off minimality alone, `archLS_anova` gives the
split `tss = rss + ess` at an *arbitrary* centring constant (the sample mean is not needed,
which is why `htss`'s `((T:ℝ) − p)⁻¹` normalisation costs nothing), and
`archTR2Stat_eq_ess_div_tss` delivers `TR² = T · ess/tss`, with `arch_rss_le_tss` confirming
`R² ∈ [0,1]`. Two bricks remain, both probabilistic: **(b)** the `p`-dimensional iid CLT for
the autocovariance vector of `Y`, and **(c)** the continuous-mapping step (its limit-law
target is already available here). Note `p = 0` is consistent (both sides are `δ₀`); it is
*not* proved for this statement, unlike its two companions, because at `p = 0` the identity
`rss = tss` only gives `TR² = 0` on `{tss ≠ 0}`, and `tss ≠ 0` a.s. is itself the
nondegeneracy fact recorded in the next paragraph.
Also, `hgauss` is not decoration *(this remark is documented, not formalized)*: with `ε`
Rademacher, `X_t² = c₀` a.s., so response and regressors are all equal, `rss = tss = 0`, and
the statistic is the constant `T` — a law `δ_T` with no limit. Nondegeneracy of `Var(X_t²)`
is therefore needed, and `hgauss` is what supplies it.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.6,
eqs. (4.48)–(4.54) (pp. 165–168). (`FY §4.2.6`.)

**Bibliographic comments.** The LM/`TR²` test is R. F. Engle (1982) §6; the iid
likelihood asymptotics FY invokes are Serfling (1980) §4.4.4; the boundary problem is
Chernoff (1954) and Self & Liang (1987).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY §4.2.6 structural fact**: under `H₀` (all ARCH coefficients zero) the ARCH(p)
process is iid — `X_t = √c₀ · ε_t`. This is what licenses the classical iid likelihood
asymptotics for all three statistics. -/
theorem IsARCH.iid_of_b_eq_zero [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 (fun _ : Fin p => (0 : ℝ)) X ε μ) :
    (∀ t, X t =ᵐ[μ] fun ω => Real.sqrt c0 * ε t ω) ∧
      IsIIDNoise X c0 μ := by
  -- With `b = 0` the whole `Finset.sum` in the radicand vanishes, so the volatility is
  -- the *constant* `√c₀` and the recurrence reads `X_t = √c₀ · ε_t`.
  have hvol : ∀ (t : ℤ) (ω : Ω),
      archVol c0 (fun _ : Fin p => (0 : ℝ)) X t ω = Real.sqrt c0 := by
    intro t ω
    simp [archVol]
  have hX : ∀ t, X t =ᵐ[μ] fun ω => Real.sqrt c0 * ε t ω := by
    intro t
    filter_upwards [h.recurrence t] with ω hω
    rw [hω, hvol]
  refine ⟨hX, ?_⟩
  -- The scaling map `x ↦ √c₀ · x`, along which every `IsIIDNoise` field transports.
  have hsm : Measurable fun x : ℝ => Real.sqrt c0 * x := measurable_const_mul _
  have hsq : Real.sqrt c0 ^ 2 = c0 := Real.sq_sqrt h.c0_nonneg
  refine ⟨h.measurableX, ?_, ?_, ?_, ?_, ?_⟩
  · -- Independence: `iIndepFun` transports along the scaling and then along `=ᵐ`.
    have hind : iIndepFun (fun (t : ℤ) (ω : Ω) => Real.sqrt c0 * ε t ω) μ := by
      have := h.iid.iIndep.comp (fun _ : ℤ => fun x : ℝ => Real.sqrt c0 * x) fun _ => hsm
      simpa [Function.comp_def] using this
    exact (iIndepFun_congr fun t => (hX t).symm).mp hind
  · -- Identical distribution, through the scaled noise.
    intro s t
    have hs : IdentDistrib (X s) (fun ω => Real.sqrt c0 * ε s ω) μ μ :=
      IdentDistrib.of_ae_eq (h.measurableX s).aemeasurable (hX s)
    have ht : IdentDistrib (X t) (fun ω => Real.sqrt c0 * ε t ω) μ μ :=
      IdentDistrib.of_ae_eq (h.measurableX t).aemeasurable (hX t)
    exact (hs.trans ((h.iid.identDistrib s t).const_mul _)).trans ht.symm
  · exact (h.iid.memLp.const_mul (Real.sqrt c0)).ae_eq (hX 0).symm
  · rw [integral_congr_ae (hX 0)]
    have : ∫ ω, Real.sqrt c0 * ε 0 ω ∂μ = Real.sqrt c0 * ∫ ω, ε 0 ω ∂μ :=
      integral_const_mul _ _
    rw [this, h.iid.integral_eq_zero, mul_zero]
  · rw [variance_congr (hX 0), variance_const_mul, h.iid.variance_eq, mul_one, hsq]

/-- The ARCH(p) **conditional Gaussian log-likelihood** of the data at parameters
`(c₀, b)` (the `§4.2.6` likelihood: `−½ Σ_t (log σ_t² + X_t²/σ_t²)` up to constants),
written through the truncated volatility of `GARCH/Estimation.lean` with no MA part. -/
noncomputable def archLogLik {p : ℕ} (c0 : ℝ) (b : Fin p → ℝ) {T : ℕ}
    (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  -(1 / 2) * garchQuasiLik c0 b (Fin.elim0 : Fin 0 → ℝ) c0 x ν

/-- **FY eq. (4.50)**: the **likelihood-ratio statistic** `2 log S_{T,1}`, twice the
gap between the unrestricted and null-restricted maximized log-likelihoods. -/
noncomputable def archLRStat {p : ℕ} {T : ℕ} (x : Fin T → ℝ) (ν : ℕ)
    (c0hat : ℝ) (bhat : Fin p → ℝ) (c0null : ℝ) : ℝ :=
  2 * (archLogLik c0hat bhat x ν - archLogLik c0null (fun _ : Fin p => (0 : ℝ)) x ν)

/-- **FY eq. (4.53)**: Engle's `TR²` statistic — `T` times the coefficient of
determination of the auxiliary regression of `X_t²` on its `p` lags. Stated through the
regression's residual and total sums of squares. -/
noncomputable def archTR2Stat {T : ℕ} (rss tss : ℝ) : ℝ :=
  (T : ℝ) * (1 - rss / tss)

/-! ### The unrestricted ARCH quasi-likelihood has no maximizer

The witness announced in the module docstring: `hMLE`/`hMLE0` of the two likelihood-based
debts below are unsatisfiable, so those debts are vacuous. -/

/-- At `b = 0` — and with the presample value `archLogLik` uses, namely `c₀` itself — the
truncated ARCH volatility is the *constant* `c₀`, for **every** real `c₀`. No positivity
is available here and none is needed: with `q = 0` the recursion has no volatility
feedback, so a single case split on `t` replaces the induction. -/
private lemma truncVol_const {p T : ℕ} (c : ℝ) (x : Fin T → ℝ) (t : ℕ) :
    garchTruncVol c (fun _ : Fin p => (0 : ℝ)) (Fin.elim0 : Fin 0 → ℝ) c x t = c := by
  cases t with
  | zero => simp [garchTruncVol]
  | succ n => simp [garchTruncVol]

/-- The closed form of the null log-likelihood at a **negative** variance parameter `−δ`:
`Real.log (−δ) = Real.log δ`, and the quadratic term keeps the factor `(−δ)⁻¹ < 0`, whose
sign the outer `−½` flips to `+`. So both summands push the criterion *up*. -/
private lemma archLogLik_neg {p T : ℕ} (δ : ℝ) (x : Fin T → ℝ) (ν : ℕ) :
    archLogLik (-δ) (fun _ : Fin p => (0 : ℝ)) x ν
      = -(1 / 2) * (((T - ν : ℕ) : ℝ) * Real.log δ
          + (∑ t ∈ Finset.Ico ν T, (if h : t < T then x ⟨t, h⟩ else 0) ^ 2) * (-δ)⁻¹) := by
  rw [archLogLik, garchQuasiLik]
  simp only [truncVol_const, Real.log_neg_eq_log, div_eq_mul_inv]
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, Nat.card_Ico]
  simp

/-- **The witness.** As soon as the criterion's index set `Ico ν T` is nonempty, the null
ARCH log-likelihood is unbounded above on the unrestricted parameter space: take
`c₀ = −δ` with `δ = exp(−(2|M| + 2)/(T − ν))`, which makes the logarithmic part alone
equal `|M| + 1 > M` while the quadratic part is nonnegative. Hence no `(c₀, b)` maximizes
it, over the unrestricted set or over any set containing the negative axis. -/
private lemma archLogLik_unbounded {p T : ℕ} (x : Fin T → ℝ) {ν : ℕ} (hν : ν < T) (M : ℝ) :
    ∃ c : ℝ, M < archLogLik c (fun _ : Fin p => (0 : ℝ)) x ν := by
  have hn : 0 < T - ν := Nat.sub_pos_of_lt hν
  have hnR : (0 : ℝ) < ((T - ν : ℕ) : ℝ) := Nat.cast_pos.2 hn
  set δ : ℝ := Real.exp (-(2 * |M| + 2) / ((T - ν : ℕ) : ℝ)) with hδdef
  have hδ0 : 0 < δ := Real.exp_pos _
  refine ⟨-δ, ?_⟩
  rw [archLogLik_neg]
  have hlog : Real.log δ = -(2 * |M| + 2) / ((T - ν : ℕ) : ℝ) := Real.log_exp _
  have hS : 0 ≤ ∑ t ∈ Finset.Ico ν T, (if h : t < T then x ⟨t, h⟩ else 0) ^ 2 :=
    Finset.sum_nonneg fun t _ => sq_nonneg _
  have hkey : ((T - ν : ℕ) : ℝ) * Real.log δ = -(2 * |M| + 2) := by
    rw [hlog]; field_simp
  have hinv : (∑ t ∈ Finset.Ico ν T, (if h : t < T then x ⟨t, h⟩ else 0) ^ 2) * (-δ)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hS (inv_nonpos.2 (by linarith))
  have hM : M ≤ |M| := le_abs_self M
  rw [hkey]
  nlinarith [hinv, hM]

/-- The frozen `hMLE`/`hMLE0` shape — a global maximizer of the null log-likelihood, at
every sample size — is contradictory under `νseq T / T → 0`, which forces `νseq T < T` for
all large `T` and hence a nonempty criterion sum at some `T`. -/
private lemma false_of_bddAbove_archLogLik {p : ℕ} {νseq : ℕ → ℕ}
    (hνT : Tendsto (fun T : ℕ => (νseq T : ℝ) / T) atTop (𝓝 0))
    (data : (T : ℕ) → Fin T → ℝ) (F : ℕ → ℝ)
    (hmax : ∀ (T : ℕ) (c : ℝ),
      archLogLik c (fun _ : Fin p => (0 : ℝ)) (data T) (νseq T) ≤ F T) : False := by
  have h1 : ∀ᶠ T : ℕ in atTop, (νseq T : ℝ) / T < 1 / 2 :=
    hνT.eventually_lt_const (by norm_num)
  obtain ⟨T, hT, hT1⟩ := (h1.and (eventually_ge_atTop 1)).exists
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hlt : νseq T < T := by
    have : (νseq T : ℝ) < T := by
      have := (div_lt_iff₀ hTpos).1 hT
      linarith
    exact_mod_cast this
  obtain ⟨c, hc⟩ := archLogLik_unbounded (p := p) (data T) hlt (F T)
  exact absurd (hmax T c) (not_le.2 hc)

/-! ### The repair: a data-adapted admissible set on which the maximizer exists

`false_of_bddAbove_archLogLik` above is **retained as the justification** for what follows:
it is the machine-checked reason the earlier `hMLE`/`hMLE0` shape (a global maximizer over
all of `ℝ × ℝᵖ`) had to go. The replacement keeps FY's *unconstrained* parametrization for
`b` — which is what the `χ²_p` limit needs (see the boundary caveat in the module
docstring) — and instead cuts the parameter space by the **data-adapted admissible set**

  `archAdmissible κ x ν = {(c₀, b) : σ̃_t²(c₀, b) ≥ κ for every t in the criterion's range}`,

the exact locus on which the criterion's `log σ̃_t²` and `x_t²/σ̃_t²` are defined and
continuous. Two facts make this the minimal fix rather than another guess:

* it is **closed** — with `q = 0` the truncated volatility is *affine* in `(c₀, b)`
  (`continuous_truncVol`), so no recursion estimate is needed — hence `K ∩ archAdmissible`
  is compact for compact `K` and `archLogLik` attains its maximum there
  (`exists_isMaxOn_archLogLik`);
* it is **nonempty at the truth**: `(c₀, 0)` is admissible as soon as `κ ≤ c₀`
  (`mem_archAdmissible_of_b_eq_zero`, via `truncVol_const`), and `b` is *not* sign
  constrained, so the truth can sit in the **interior** of `K`. Constraining `K ⊆ {b ≥ 0}`
  instead — FY's own admissible set — would put the null on the *boundary* of `K` and so
  contradict `hK0`; that is the boundary problem FY flags, and avoiding it is why the
  variance floor is imposed on the *data-adapted* set rather than on `K`.

`exists_archMLE_sequences` then produces estimator sequences satisfying the repaired
hypotheses verbatim, so the repaired statements are **not** vacuous. -/

/-- The **data-adapted admissible set** at variance floor `κ`: the parameters `(c₀, b)` at
which the truncated conditional variance the ARCH criterion divides by stays `≥ κ`
throughout the criterion's own index range `Ico ν T`. -/
def archAdmissible (κ : ℝ) {p T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : Set (ℝ × (Fin p → ℝ)) :=
  {θ | ∀ t ∈ Finset.Ico ν T, κ ≤ garchTruncVol θ.1 θ.2 (Fin.elim0 : Fin 0 → ℝ) θ.1 x t}

/-- The **null slice** `{b = 0}` of a search region — the restricted parameter space of
`H₀ : b₁ = ⋯ = b_p = 0`. -/
def archNullSlice {p : ℕ} (K : Set (ℝ × (Fin p → ℝ))) : Set (ℝ × (Fin p → ℝ)) :=
  K ∩ {θ | θ.2 = fun _ => (0 : ℝ)}

/-- With no volatility feedback (`q = 0`) the truncated conditional variance is an *affine*
function of `(c₀, b)`: `σ̃₀² = c₀` and `σ̃_{n+1}² = c₀ + Σᵢ bᵢ x_{n−i}²`. Hence it is
continuous, with no recursion estimate and no positivity assumption. -/
private lemma continuous_truncVol {p T : ℕ} (x : Fin T → ℝ) (t : ℕ) :
    Continuous fun θ : ℝ × (Fin p → ℝ) =>
      garchTruncVol θ.1 θ.2 (Fin.elim0 : Fin 0 → ℝ) θ.1 x t := by
  cases t with
  | zero => simpa [garchTruncVol] using continuous_fst
  | succ n =>
      have hrw : (fun θ : ℝ × (Fin p → ℝ) =>
            garchTruncVol θ.1 θ.2 (Fin.elim0 : Fin 0 → ℝ) θ.1 x (n + 1))
          = fun θ : ℝ × (Fin p → ℝ) => θ.1 + ∑ i : Fin p, θ.2 i *
              (if h : n - (i : ℕ) < T then x ⟨n - (i : ℕ), h⟩ else 0) ^ 2 := by
        funext θ; rw [garchTruncVol]; simp
      rw [hrw]
      exact continuous_fst.add (continuous_finset_sum _ fun i _ =>
        ((continuous_apply i).comp continuous_snd).mul continuous_const)

/-- The admissible set is closed — a finite intersection of closed half-spaces. -/
private lemma isClosed_archAdmissible {p T : ℕ} (κ : ℝ) (x : Fin T → ℝ) (ν : ℕ) :
    IsClosed (archAdmissible (p := p) κ x ν) := by
  have hrw : archAdmissible (p := p) κ x ν
      = ⋂ t ∈ Finset.Ico ν T,
          {θ : ℝ × (Fin p → ℝ) |
            κ ≤ garchTruncVol θ.1 θ.2 (Fin.elim0 : Fin 0 → ℝ) θ.1 x t} := by
    ext θ; simp [archAdmissible]
  rw [hrw]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_truncVol x t)

/-- The null slice of a compact region is compact. -/
private lemma isCompact_archNullSlice {p : ℕ} {K : Set (ℝ × (Fin p → ℝ))} (hK : IsCompact K) :
    IsCompact (archNullSlice K) :=
  hK.inter_right (isClosed_eq continuous_snd continuous_const)

/-- **The truth is admissible.** At `b = 0` the truncated volatility is the constant `c₀`
(`truncVol_const`), so `(c₀, 0)` clears the floor exactly when `κ ≤ c₀`. -/
theorem mem_archAdmissible_of_b_eq_zero {p T : ℕ} {κ c : ℝ} (hc : κ ≤ c)
    (x : Fin T → ℝ) (ν : ℕ) :
    ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)) ∈ archAdmissible κ x ν := by
  intro t _
  rw [show ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)).1 = c from rfl,
    show ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)).2 = fun _ : Fin p => (0 : ℝ) from rfl,
    truncVol_const]
  exact hc

/-- **The truth is *interior* to the admissible set** as soon as the floor is *strict*,
`κ < c₀`. This is the second half of the de-vacuation and it is what keeps FY's boundary
problem out: the variance constraint does not bind at the null, so the maximizer is a free
(score-equation) maximizer near the truth rather than a constrained one, and the `χ²_p`
limit — as opposed to the one-sided mixture — is the right target. It is also why the
statements below carry `κ < c₀` and not `κ ≤ c₀`: at `κ = c₀` the null sits *on* the
boundary of `archAdmissible κ` and the strengthening would have re-created, on the
`c₀` axis, exactly the defect it was introduced to remove. -/
theorem mem_interior_archAdmissible {p T : ℕ} {κ c : ℝ} (hc : κ < c) (x : Fin T → ℝ) (ν : ℕ) :
    ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)) ∈
      interior (archAdmissible κ x ν) := by
  refine mem_interior.2 ⟨⋂ t ∈ Finset.Ico ν T,
    {θ : ℝ × (Fin p → ℝ) |
      κ < garchTruncVol θ.1 θ.2 (Fin.elim0 : Fin 0 → ℝ) θ.1 x t}, ?_, ?_, ?_⟩
  · intro θ hθ t ht
    simp only [Set.mem_iInter] at hθ
    exact (hθ t ht).le
  · exact isOpen_biInter_finset fun t _ =>
      isOpen_lt continuous_const (continuous_truncVol x t)
  · simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro t _
    rw [truncVol_const]
    exact hc

/-- The truth is interior to the whole **feasible set** `K ∩ archAdmissible κ`: neither the
search region nor the variance floor binds at the null. -/
theorem mem_interior_arch_feasible {p T : ℕ} {κ c : ℝ} (hc : κ < c)
    {K : Set (ℝ × (Fin p → ℝ))}
    (hK0 : ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)) ∈ interior K)
    (x : Fin T → ℝ) (ν : ℕ) :
    ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)) ∈
      interior (K ∩ archAdmissible κ x ν) := by
  rw [interior_inter]
  exact ⟨hK0, mem_interior_archAdmissible hc x ν⟩

/-- On the admissible set the criterion is continuous: the floor `κ > 0` keeps the
volatility away from the singularity of both `log` and the reciprocal. -/
private lemma continuousOn_archLogLik {p T : ℕ} {κ : ℝ} (hκ : 0 < κ) (x : Fin T → ℝ) (ν : ℕ) :
    ContinuousOn (fun θ : ℝ × (Fin p → ℝ) => archLogLik θ.1 θ.2 x ν)
      (archAdmissible κ x ν) := by
  have hne : ∀ t ∈ Finset.Ico ν T, ∀ θ ∈ archAdmissible (p := p) κ x ν,
      garchTruncVol θ.1 θ.2 (Fin.elim0 : Fin 0 → ℝ) θ.1 x t ≠ 0 := by
    intro t ht θ hθ
    exact ne_of_gt (lt_of_lt_of_le hκ (hθ t ht))
  simp only [archLogLik, garchQuasiLik]
  refine continuousOn_const.mul (continuousOn_finset_sum _ fun t ht => ?_)
  exact ((continuous_truncVol x t).continuousOn.log (hne t ht)).add
    (continuousOn_const.div (continuous_truncVol x t).continuousOn (hne t ht))

/-- **The repaired pinning is satisfiable** — the ARCH criterion *does* attain its maximum
over `K ∩ archAdmissible κ x ν` whenever that set is nonempty and `K` is compact. Contrast
`false_of_bddAbove_archLogLik`, which refutes the same demand made over all of `ℝ × ℝᵖ`. -/
theorem exists_isMaxOn_archLogLik {p T : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {K : Set (ℝ × (Fin p → ℝ))} (hK : IsCompact K) (x : Fin T → ℝ) (ν : ℕ)
    (hne : (K ∩ archAdmissible κ x ν).Nonempty) :
    ∃ θ ∈ K ∩ archAdmissible κ x ν, ∀ θ' ∈ K ∩ archAdmissible κ x ν,
      archLogLik θ'.1 θ'.2 x ν ≤ archLogLik θ.1 θ.2 x ν := by
  have hc : IsCompact (K ∩ archAdmissible κ x ν) :=
    hK.inter_right (isClosed_archAdmissible κ x ν)
  obtain ⟨θ, hθ, hmax⟩ := hc.exists_isMaxOn hne
    ((continuousOn_archLogLik hκ x ν).mono Set.inter_subset_right)
  exact ⟨θ, hθ, fun θ' hθ' => hmax hθ'⟩

/-- The null-restricted companion of `exists_isMaxOn_archLogLik`. -/
theorem exists_isMaxOn_archLogLik_null {p T : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {K : Set (ℝ × (Fin p → ℝ))} (hK : IsCompact K) (x : Fin T → ℝ) (ν : ℕ)
    (hne : (archNullSlice K ∩ archAdmissible κ x ν).Nonempty) :
    ∃ θ ∈ archNullSlice K ∩ archAdmissible κ x ν,
      ∀ θ' ∈ archNullSlice K ∩ archAdmissible κ x ν,
        archLogLik θ'.1 θ'.2 x ν ≤ archLogLik θ.1 θ.2 x ν := by
  have hc : IsCompact (archNullSlice K ∩ archAdmissible κ x ν) :=
    (isCompact_archNullSlice hK).inter_right (isClosed_archAdmissible κ x ν)
  obtain ⟨θ, hθ, hmax⟩ := hc.exists_isMaxOn hne
    ((continuousOn_archLogLik hκ x ν).mono Set.inter_subset_right)
  exact ⟨θ, hθ, fun θ' hθ' => hmax hθ'⟩

/-- **Non-vacuity certificate for the repaired statements.** Given a variance floor
`κ ≤ c₀`, a compact search region `K` containing `(c₀, 0)`, and any data, there *exist*
unrestricted and null-restricted maximizing sequences — i.e. the `hMLE` and `hMLE0` of the
removed LR and Wald debts were jointly satisfiable, exactly what
`false_of_bddAbove_archLogLik` denies for the superseded unconstrained shape.

*(Measurability of the selection is a separate matter: those theorems carried
`hmeas` as a `USER-INPUT`, and this certificate produces the sequences by pointwise choice,
not by a measurable-selection theorem. The repo's `exists_measurable_argmin_of_convex`
(`EstimationTheory/.../MeasurableArgmin.lean`) is the tool for upgrading it, and does not
apply off the shelf: the ARCH criterion is not convex in `(c₀, b)`.)* -/
theorem exists_archMLE_sequences {p : ℕ} {κ c : ℝ} (hκ : 0 < κ) (hc : κ ≤ c)
    {K : Set (ℝ × (Fin p → ℝ))} (hK : IsCompact K)
    (hK0 : ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)) ∈ K)
    (X : ℤ → Ω → ℝ) (νseq : ℕ → ℕ) :
    ∃ (c0hat : (T : ℕ) → Ω → ℝ) (bhat : (T : ℕ) → Ω → Fin p → ℝ)
      (c0null : (T : ℕ) → Ω → ℝ),
      (∀ (T : ℕ) (ω : Ω),
        ((c0hat T ω, bhat T ω) : ℝ × (Fin p → ℝ)) ∈
            K ∩ archAdmissible κ (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T) ∧
          ∀ θ ∈ K ∩ archAdmissible κ (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T),
            archLogLik θ.1 θ.2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
              ≤ archLogLik (c0hat T ω) (bhat T ω)
                  (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)) ∧
      (∀ (T : ℕ) (ω : Ω),
        ((c0null T ω, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)) ∈
            archNullSlice K ∩
              archAdmissible κ (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T) ∧
          ∀ θ ∈ archNullSlice K ∩
              archAdmissible κ (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T),
            archLogLik θ.1 θ.2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
              ≤ archLogLik (c0null T ω) (fun _ : Fin p => (0 : ℝ))
                  (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)) := by
  -- the truth `(c, 0)` is feasible for both problems, so both are nonempty
  have hmem : ∀ (T : ℕ) (ω : Ω),
      ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)) ∈
        K ∩ archAdmissible κ (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T) :=
    fun T ω => ⟨hK0, mem_archAdmissible_of_b_eq_zero hc _ _⟩
  have hmem0 : ∀ (T : ℕ) (ω : Ω),
      ((c, fun _ : Fin p => (0 : ℝ)) : ℝ × (Fin p → ℝ)) ∈
        archNullSlice K ∩ archAdmissible κ (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T) :=
    fun T ω => ⟨⟨hK0, rfl⟩, mem_archAdmissible_of_b_eq_zero hc _ _⟩
  choose θ hθ hθmax using fun (T : ℕ) (ω : Ω) =>
    exists_isMaxOn_archLogLik hκ hK (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
      ⟨_, hmem T ω⟩
  choose η hη hηmax using fun (T : ℕ) (ω : Ω) =>
    exists_isMaxOn_archLogLik_null hκ hK (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
      ⟨_, hmem0 T ω⟩
  refine ⟨fun T ω => (θ T ω).1, fun T ω => (θ T ω).2, fun T ω => (η T ω).1, ?_, ?_⟩
  · exact fun T ω => ⟨hθ T ω, hθmax T ω⟩
  · refine fun T ω => ⟨?_, ?_⟩
    · have h2 : (η T ω).2 = fun _ : Fin p => (0 : ℝ) := (hη T ω).1.2
      exact h2 ▸ hη T ω
    · intro ξ hξ
      have h2 : (η T ω).2 = fun _ : Fin p => (0 : ℝ) := (hη T ω).1.2
      simpa [h2] using hηmax T ω ξ hξ

/-- A probability space is nonempty — needed to evaluate the contradictory hypotheses at a
sample point. -/
private lemma nonempty_of_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Nonempty Ω := by
  rcases isEmpty_or_nonempty Ω with hE | hE
  · have h1 : μ (Set.univ : Set Ω) = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
    exact absurd h1 (by norm_num)
  · exact hE

/-! ### The χ²_p character identity and the identification of the abstract limit law

The three debts take their limit law abstractly, pinned only by
`hchi : charFun chiSq u = (1 − 2iu)^{−p/2}`. That normalisation is *exactly* the
characteristic function of a Gaussian quadratic form `Σ_{i<p} Z_i²`, which is proved here
(`charFun_map_sum_sq_gaussian`) and used to identify `chiSq` outright
(`eq_map_sum_sq_gaussian_of_charFun`). This discharges two of the mismatches listed in the
module docstring — the χ² character identity, recorded there as "not proved anywhere in the
repo at present", and the "conclusion form" item: no χ² *construction* is needed, and no
`WeakConverges → charFun` bridge either. The route is the Fresnel-type Gaussian integral
`∫ exp(−b x²) = (π/b)^{1/2}` at `b = (1 − 2iu)/2`, tensored over the `p` coordinates by
Fubini. These belong in `MultipleTesting/ForMathlib/ChiSquared.lean` (whose `chiSquared p`
is `Gamma(p/2, 1/2)`, and where `map_sum_sq_eq_chiSquared` already identifies the law of
`Σ Z_i²`); they are `private` here only because that file is outside this lane's touch set. -/

/-- The principal square root of a right-half-plane point has positive real part: its
argument is halved into `(−π/4, π/4)`, where the cosine is positive. -/
private lemma re_cpow_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (1 / 2 : ℂ)).re := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
  have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by
    simp [Complex.mul_im, Complex.log_im]
    ring
  rw [him]
  have harg : |w.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  rw [abs_lt] at harg
  have hcos : 0 < Real.cos (w.arg / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [harg.1], by linarith [harg.2]⟩
  exact mul_pos (Real.exp_pos _) hcos

/-- Two right-half-plane points with the same square agree — the branch-free way to compare
two square roots, used instead of `cpow` argument arithmetic. -/
private lemma eq_of_sq_eq_of_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re)
    (h : z ^ 2 = w ^ 2) : z = w := by
  have h0 : (z - w) * (z + w) = 0 := by ring_nf; linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have hre : z.re + w.re = 0 := by
      have h2 := congrArg Complex.re h1
      simp only [Complex.add_re, Complex.zero_re] at h2
      exact h2
    linarith

/-- `(w^{1/2})² = w` for the principal branch. -/
private lemma sq_cpow_half (w : ℂ) : (w ^ ((1 : ℂ) / 2)) ^ 2 = w := by
  have h := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
  norm_num at h
  exact h

/-- **The one-dimensional χ² character**: `E[exp(i u Z²)] = (1 − 2iu)^{−1/2}` for
`Z ∼ N(0,1)`. The Gaussian density folds the phase into the complex Gaussian integral at
rate `b = 1/2 − iu`, whose real part is `1/2 > 0`; the two candidate square roots are then
matched by `eq_of_sq_eq_of_re_pos` rather than by tracking arguments. -/
private lemma integral_cexp_sq_gaussianReal (u : ℝ) :
    ∫ y : ℝ, Complex.exp ((u : ℂ) * (y : ℂ) ^ 2 * Complex.I) ∂(gaussianReal 0 1)
      = (1 - 2 * Complex.I * u) ^ (-(1 : ℂ) / 2) := by
  have hb : (0 : ℝ) < ((1 / 2 : ℂ) - u * Complex.I).re := by norm_num
  have hint : ∀ y : ℝ, gaussianPDFReal 0 1 y • Complex.exp ((u : ℂ) * (y : ℂ) ^ 2 * Complex.I)
      = ((Real.sqrt (2 * Real.pi))⁻¹ : ℝ)
        * Complex.exp (-((1 / 2 : ℂ) - u * Complex.I) * (y : ℂ) ^ 2) := by
    intro y
    rw [Complex.real_smul, gaussianPDFReal]
    push_cast
    have h1 : (2 : ℝ) * Real.pi * 1 = 2 * Real.pi := by ring
    rw [mul_assoc, ← Complex.exp_add, h1]
    congr 2
    ring
  have hc : ∫ y : ℝ, ((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) *
        Complex.exp (-((1 / 2 : ℂ) - u * Complex.I) * (y : ℂ) ^ 2)
      = ((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) *
        ∫ y : ℝ, Complex.exp (-((1 / 2 : ℂ) - u * Complex.I) * (y : ℂ) ^ 2) :=
    integral_const_mul _ _
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  refine (integral_congr_ae (ae_of_all _ hint)).trans ?_
  rw [hc, integral_gaussian_complex hb]
  -- what is left is `(2π)^{-1/2}·(π/b)^{1/2} = (1−2iu)^{−1/2}` at `b = (1−2iu)/2`
  have hbne : ((1 / 2 : ℂ) - (u : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h1 : ((1 / 2 : ℂ) - (u : ℂ) * Complex.I).re = 1 / 2 := by simp
    rw [h] at h1; norm_num at h1
  have hzre : (0 : ℝ) < (1 - 2 * Complex.I * (u : ℂ)).re := by simp
  have hzne : (1 - 2 * Complex.I * (u : ℂ)) ≠ 0 := by
    intro h; rw [h] at hzre; simp at hzre
  have hw : (0 : ℝ) < ((Real.pi : ℂ) / ((1 / 2 : ℂ) - (u : ℂ) * Complex.I)).re := by
    rw [div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re]
    have h1 : ((1 / 2 : ℂ) - (u : ℂ) * Complex.I).re = 1 / 2 := by simp
    rw [h1]
    exact mul_pos Real.pi_pos (div_pos (by norm_num) (Complex.normSq_pos.2 hbne))
  have hneg : (-(1 : ℂ) / 2) = -((1 : ℂ) / 2) := by ring
  refine eq_of_sq_eq_of_re_pos ?_ ?_ ?_
  · rw [Complex.re_ofReal_mul]
    exact mul_pos (by positivity) (re_cpow_half_pos hw)
  · rw [hneg, Complex.cpow_neg, Complex.inv_re]
    have hnz : ((1 - 2 * Complex.I * (u : ℂ)) ^ ((1 : ℂ) / 2)) ≠ 0 := by
      intro h
      have hp := re_cpow_half_pos hzre
      rw [h] at hp; simp at hp
    exact div_pos (re_cpow_half_pos hzre) (Complex.normSq_pos.2 hnz)
  · rw [hneg, Complex.cpow_neg, mul_pow, inv_pow, sq_cpow_half, sq_cpow_half]
    have h2pi : (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ ^ 2 = (((2 * Real.pi : ℝ) : ℂ))⁻¹ := by
      rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast at h2pi ⊢
    rw [h2pi]
    have hpi : ((Real.pi : ℂ)) ≠ 0 := by simp
    field_simp

/-- **The χ²_p character identity, in the quadratic-form-of-Gaussians form**: the law of
`‖Z‖² = Σ_{i<p} Z_i²` for a standard Gaussian vector `Z` has characteristic function
`(1 − 2iu)^{−p/2}` — exactly the `hchi` normalisation of the frozen ARCH debts. The `p`
coordinates factor by Fubini (`integral_fintype_prod_eq_pow`), so the identity is the
one-dimensional character raised to the `p`-th power, and `x^(p·y) = (x^y)^p` needs no
branch side condition. -/
private lemma charFun_map_sum_sq_gaussian (p : ℕ) (u : ℝ) :
    charFun ((Measure.pi fun _ : Fin p => gaussianReal 0 1).map
        (fun x : Fin p → ℝ => ∑ i, x i ^ 2)) u
      = (1 - 2 * Complex.I * u) ^ (-(p : ℂ) / 2) := by
  have hφ : Measurable fun x : Fin p → ℝ => ∑ i, x i ^ 2 := by fun_prop
  rw [charFun_apply_real, integral_map hφ.aemeasurable]
  · have hpt : ∀ x : Fin p → ℝ,
        Complex.exp ((u : ℂ) * ((∑ i, x i ^ 2 : ℝ) : ℂ) * Complex.I)
          = ∏ i, Complex.exp ((u : ℂ) * ((x i : ℂ)) ^ 2 * Complex.I) := by
      intro x
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
    have hprod := integral_fintype_prod_eq_pow (ι := Fin p)
      (fun y : ℝ => Complex.exp ((u : ℂ) * (y : ℂ) ^ 2 * Complex.I))
      (μ := gaussianReal 0 1)
    rw [integral_congr_ae (ae_of_all _ hpt)]
    refine hprod.trans ?_
    -- `rw` cannot see through the integral's instance path here, so close by `congrArg`
    rw [Fintype.card_fin, show (-(p : ℂ) / 2) = (p : ℂ) * (-(1 : ℂ) / 2) by ring,
      Complex.cpow_nat_mul]
    exact congrArg (· ^ p) (integral_cexp_sq_gaussianReal u)
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable

/-- **The frozen `hchi` pins the limit law**: a probability measure on `ℝ` whose
characteristic function is `(1 − 2iu)^{−p/2}` *is* the law of `Σ_{i<p} Z_i²` for a standard
Gaussian vector, by `Measure.ext_of_charFun`. So the debts' abstract `chiSq` argument
carries no freedom, and their conclusions may be read as convergence to that concrete
law. -/
private lemma eq_map_sum_sq_gaussian_of_charFun {p : ℕ} (chiSq : Measure ℝ)
    [IsProbabilityMeasure chiSq]
    (hchi : ∀ u : ℝ, charFun chiSq u = (1 - 2 * Complex.I * u) ^ (-(p : ℂ) / 2)) :
    chiSq = (Measure.pi fun _ : Fin p => gaussianReal 0 1).map
      (fun x : Fin p → ℝ => ∑ i, x i ^ 2) := by
  have hφ : Measurable fun x : Fin p → ℝ => ∑ i, x i ^ 2 := by fun_prop
  haveI : IsProbabilityMeasure ((Measure.pi fun _ : Fin p => gaussianReal 0 1).map
      (fun x : Fin p → ℝ => ∑ i, x i ^ 2)) := Measure.isProbabilityMeasure_map hφ.aemeasurable
  exact Measure.ext_of_charFun (funext fun u => by
    rw [hchi u, charFun_map_sum_sq_gaussian])

/-! ### The `R²` algebra of the auxiliary regression

Brick (a) of the `TR²` residue: turn the `IsLeast` package `hrss` into usable algebra. The
whole content is that a least-squares fit is *orthogonal to its own design*, which for a
design containing the intercept gives the ANOVA split `tss = rss + ess` for **any** centring
constant — the sample mean is not needed. Two consequences that the LM limit will use:
`archTR2Stat` is genuinely `T` times an `R² ∈ [0, 1]`, and its numerator is the explained
sum of squares, the quadratic form the CLT acts on. -/

/-- **The scalar normal equation.** If perturbing the residual vector `r` along a direction
`g` cannot decrease the sum of squares, then `r ⟂ g`. The `B = 0` branch is not a
degeneracy to be excluded — it says `g` vanishes on the index set, where orthogonality is
free. -/
private lemma sum_mul_eq_zero_of_isMin {ι : Type*} {s : Finset ι} {r g : ι → ℝ}
    (h : ∀ lam : ℝ, ∑ t ∈ s, r t ^ 2 ≤ ∑ t ∈ s, (r t - lam * g t) ^ 2) :
    ∑ t ∈ s, r t * g t = 0 := by
  set A := ∑ t ∈ s, r t * g t with hA
  set B := ∑ t ∈ s, g t ^ 2 with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∀ lam : ℝ, ∑ t ∈ s, (r t - lam * g t) ^ 2
      = (∑ t ∈ s, r t ^ 2) - 2 * lam * A + lam ^ 2 * B := by
    intro lam
    simp only [hA, hBdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have key : ∀ lam : ℝ, 0 ≤ -(2 * lam * A) + lam ^ 2 * B := by
    intro lam
    have := h lam
    rw [hexp lam] at this
    linarith
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · -- the direction vanishes on `s`, so the inner product does too
    have hg : ∀ t ∈ s, g t = 0 := by
      intro t ht
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg (g t)).1 hB0.symm t ht
      exact pow_eq_zero_iff (two_ne_zero) |>.1 hz
    exact Finset.sum_eq_zero fun t ht => by rw [hg t ht, mul_zero]
  · by_contra hAne
    have hstep := key (A / B)
    have hrw : -(2 * (A / B) * A) + (A / B) ^ 2 * B = -(A ^ 2) / B := by
      field_simp; ring
    rw [hrw] at hstep
    have hA2 : 0 < A ^ 2 := by positivity
    have : -(A ^ 2) / B < 0 := div_neg_of_neg_of_pos (by linarith) hBpos
    linarith

/-- **The least-squares normal equations**, read off the minimality property alone: the
residuals are orthogonal to the constant regressor and to each lagged regressor. -/
theorem archLS_normalEq {ι : Type*} {p : ℕ} {s : Finset ι} {y : ι → ℝ} {z : ι → Fin p → ℝ}
    {β0 : ℝ} {β : Fin p → ℝ}
    (hmin : ∀ (γ0 : ℝ) (γ : Fin p → ℝ),
      ∑ t ∈ s, (y t - β0 - ∑ j, β j * z t j) ^ 2
        ≤ ∑ t ∈ s, (y t - γ0 - ∑ j, γ j * z t j) ^ 2) :
    (∑ t ∈ s, (y t - β0 - ∑ j, β j * z t j) = 0) ∧
      ∀ k, ∑ t ∈ s, (y t - β0 - ∑ j, β j * z t j) * z t k = 0 := by
  classical
  -- the general one-parameter perturbation `(β0 + λ d0, β + λ d)`
  have hpert : ∀ (d0 : ℝ) (d : Fin p → ℝ),
      ∑ t ∈ s, (y t - β0 - ∑ j, β j * z t j) * (d0 + ∑ j, d j * z t j) = 0 := by
    intro d0 d
    refine sum_mul_eq_zero_of_isMin (r := fun t => y t - β0 - ∑ j, β j * z t j)
      (g := fun t => d0 + ∑ j, d j * z t j) fun lam => ?_
    have hshift : ∀ t ∈ s,
        (y t - (β0 + lam * d0) - ∑ j, (β j + lam * d j) * z t j)
          = (y t - β0 - ∑ j, β j * z t j) - lam * (d0 + ∑ j, d j * z t j) := by
      intro t _
      have : ∑ j, (β j + lam * d j) * z t j
          = (∑ j, β j * z t j) + lam * ∑ j, d j * z t j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]; ring
    calc ∑ t ∈ s, (y t - β0 - ∑ j, β j * z t j) ^ 2
        ≤ ∑ t ∈ s, (y t - (β0 + lam * d0) - ∑ j, (β j + lam * d j) * z t j) ^ 2 :=
          hmin _ _
      _ = ∑ t ∈ s, ((y t - β0 - ∑ j, β j * z t j)
            - lam * (d0 + ∑ j, d j * z t j)) ^ 2 :=
          Finset.sum_congr rfl fun t ht => by rw [hshift t ht]
  constructor
  · have h1 := hpert 1 0
    simpa using h1
  · intro k
    have h1 := hpert 0 (fun j => if j = k then 1 else 0)
    simpa using h1

/-- **The ANOVA split of the auxiliary regression**, for an *arbitrary* centring constant
`c`: `Σ(y − c)² = rss + Σ(ŷ − c)²`. The cross term vanishes by `archLS_normalEq` because
`ŷ − c` is a combination of the constant regressor and the lags; in particular the split
does **not** need `c` to be the sample mean. -/
theorem archLS_anova {ι : Type*} {p : ℕ} {s : Finset ι} {y : ι → ℝ} {z : ι → Fin p → ℝ}
    {β0 : ℝ} {β : Fin p → ℝ}
    (hmin : ∀ (γ0 : ℝ) (γ : Fin p → ℝ),
      ∑ t ∈ s, (y t - β0 - ∑ j, β j * z t j) ^ 2
        ≤ ∑ t ∈ s, (y t - γ0 - ∑ j, γ j * z t j) ^ 2) (c : ℝ) :
    ∑ t ∈ s, (y t - c) ^ 2
      = (∑ t ∈ s, (y t - β0 - ∑ j, β j * z t j) ^ 2)
        + ∑ t ∈ s, ((β0 + ∑ j, β j * z t j) - c) ^ 2 := by
  obtain ⟨hconst, hlag⟩ := archLS_normalEq hmin
  -- the cross term, expanded along the design
  have hcross : ∑ t ∈ s,
      (y t - β0 - ∑ j, β j * z t j) * ((β0 + ∑ j, β j * z t j) - c) = 0 := by
    have hsplit : ∀ t ∈ s,
        (y t - β0 - ∑ j, β j * z t j) * ((β0 + ∑ j, β j * z t j) - c)
          = (β0 - c) * (y t - β0 - ∑ j, β j * z t j)
            + ∑ j, β j * ((y t - β0 - ∑ j, β j * z t j) * z t j) := by
      intro t _
      have hS : ∑ j, β j * ((y t - β0 - ∑ j, β j * z t j) * z t j)
          = (y t - β0 - ∑ j, β j * z t j) * ∑ j, β j * z t j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hS]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hconst,
      mul_zero, zero_add, Finset.sum_comm]
    exact Finset.sum_eq_zero fun j _ => by rw [← Finset.mul_sum, hlag j, mul_zero]
  have hpt : ∀ t ∈ s, (y t - c) ^ 2
      = (y t - β0 - ∑ j, β j * z t j) ^ 2 + ((β0 + ∑ j, β j * z t j) - c) ^ 2
        + 2 * ((y t - β0 - ∑ j, β j * z t j) * ((β0 + ∑ j, β j * z t j) - c)) := by
    intro t _; ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hcross, mul_zero, add_zero]

/-- **The ANOVA split at the level of the frozen `hrss`/`htss` package**: the auxiliary
regression's total sum of squares splits as `tss = rss + ess`, with `ess` the explained sum
of squares of *some* least-squares fit `(β̂₀, β̂)` — the fit itself need not be unique, and
nothing here assumes the Gram matrix is invertible. -/
theorem arch_tss_eq_rss_add_ess {p : ℕ} {X : ℤ → Ω → ℝ} {rss tss : (T : ℕ) → Ω → ℝ}
    (hrss : ∀ (T : ℕ) (ω : Ω), IsLeast
      {r : ℝ | ∃ (β0 : ℝ) (β : Fin p → ℝ), r = ∑ t ∈ Finset.Ico p T,
        (X ((t : ℤ) + 1) ω ^ 2 - β0
          - ∑ j : Fin p, β j * X ((t : ℤ) - (j : ℕ)) ω ^ 2) ^ 2} (rss T ω))
    (htss : ∀ (T : ℕ) (ω : Ω), tss T ω = ∑ t ∈ Finset.Ico p T,
      (X ((t : ℤ) + 1) ω ^ 2
        - ((T : ℝ) - p)⁻¹ * ∑ u ∈ Finset.Ico p T, X ((u : ℤ) + 1) ω ^ 2) ^ 2)
    (T : ℕ) (ω : Ω) :
    ∃ (β0 : ℝ) (β : Fin p → ℝ),
      tss T ω = rss T ω + ∑ t ∈ Finset.Ico p T,
        ((β0 + ∑ j : Fin p, β j * X ((t : ℤ) - (j : ℕ)) ω ^ 2)
          - ((T : ℝ) - p)⁻¹ * ∑ u ∈ Finset.Ico p T, X ((u : ℤ) + 1) ω ^ 2) ^ 2 := by
  obtain ⟨β0, β, hval⟩ := (hrss T ω).1
  refine ⟨β0, β, ?_⟩
  have hmin : ∀ (γ0 : ℝ) (γ : Fin p → ℝ),
      ∑ t ∈ Finset.Ico p T,
          (X ((t : ℤ) + 1) ω ^ 2 - β0 - ∑ j : Fin p, β j * X ((t : ℤ) - (j : ℕ)) ω ^ 2) ^ 2
        ≤ ∑ t ∈ Finset.Ico p T,
          (X ((t : ℤ) + 1) ω ^ 2 - γ0 - ∑ j : Fin p, γ j * X ((t : ℤ) - (j : ℕ)) ω ^ 2) ^ 2 := by
    intro γ0 γ
    rw [← hval]
    exact (hrss T ω).2 ⟨γ0, γ, rfl⟩
  have hano := archLS_anova (s := Finset.Ico p T)
    (y := fun t : ℕ => X ((t : ℤ) + 1) ω ^ 2)
    (z := fun (t : ℕ) (j : Fin p) => X ((t : ℤ) - (j : ℕ)) ω ^ 2) hmin
    (((T : ℝ) - p)⁻¹ * ∑ u ∈ Finset.Ico p T, X ((u : ℤ) + 1) ω ^ 2)
  rw [htss T ω, hano, ← hval]

/-- **`archTR2Stat` really is `T` times an `R²`.** Under the frozen `hrss`/`htss` the
residual sum of squares never exceeds the total, so `1 − rss/tss ∈ [0, 1]` whenever
`tss > 0`. This is the sanity fact the LM limit needs before any distributional step. -/
theorem arch_rss_le_tss {p : ℕ} {X : ℤ → Ω → ℝ} {rss tss : (T : ℕ) → Ω → ℝ}
    (hrss : ∀ (T : ℕ) (ω : Ω), IsLeast
      {r : ℝ | ∃ (β0 : ℝ) (β : Fin p → ℝ), r = ∑ t ∈ Finset.Ico p T,
        (X ((t : ℤ) + 1) ω ^ 2 - β0
          - ∑ j : Fin p, β j * X ((t : ℤ) - (j : ℕ)) ω ^ 2) ^ 2} (rss T ω))
    (htss : ∀ (T : ℕ) (ω : Ω), tss T ω = ∑ t ∈ Finset.Ico p T,
      (X ((t : ℤ) + 1) ω ^ 2
        - ((T : ℝ) - p)⁻¹ * ∑ u ∈ Finset.Ico p T, X ((u : ℤ) + 1) ω ^ 2) ^ 2)
    (T : ℕ) (ω : Ω) : rss T ω ≤ tss T ω := by
  obtain ⟨β0, β, hsplit⟩ := arch_tss_eq_rss_add_ess hrss htss T ω
  have hess : 0 ≤ ∑ t ∈ Finset.Ico p T,
      ((β0 + ∑ j : Fin p, β j * X ((t : ℤ) - (j : ℕ)) ω ^ 2)
        - ((T : ℝ) - p)⁻¹ * ∑ u ∈ Finset.Ico p T, X ((u : ℤ) + 1) ω ^ 2) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- **Brick (a) of the `TR²` residue, in its deliverable form**: Engle's statistic *is*
`T · ess/tss`, the explained sum of squares of the auxiliary regression normalised by the
total. This is the object the LM limit theory acts on — the normal equations turn `ess`
into the quadratic form `γ̂ᵀ Γ̂⁻¹ γ̂` in the lag-`1..p` sample autocovariances — so with this
identity the residual `sorry` below is purely probabilistic (bricks (b) and (c)). -/
theorem archTR2Stat_eq_ess_div_tss {p : ℕ} {X : ℤ → Ω → ℝ} {rss tss : (T : ℕ) → Ω → ℝ}
    (hrss : ∀ (T : ℕ) (ω : Ω), IsLeast
      {r : ℝ | ∃ (β0 : ℝ) (β : Fin p → ℝ), r = ∑ t ∈ Finset.Ico p T,
        (X ((t : ℤ) + 1) ω ^ 2 - β0
          - ∑ j : Fin p, β j * X ((t : ℤ) - (j : ℕ)) ω ^ 2) ^ 2} (rss T ω))
    (htss : ∀ (T : ℕ) (ω : Ω), tss T ω = ∑ t ∈ Finset.Ico p T,
      (X ((t : ℤ) + 1) ω ^ 2
        - ((T : ℝ) - p)⁻¹ * ∑ u ∈ Finset.Ico p T, X ((u : ℤ) + 1) ω ^ 2) ^ 2)
    (T : ℕ) (ω : Ω) (hne : tss T ω ≠ 0) :
    ∃ (β0 : ℝ) (β : Fin p → ℝ),
      archTR2Stat (T := T) (rss T ω) (tss T ω)
        = (T : ℝ) * ((∑ t ∈ Finset.Ico p T,
            ((β0 + ∑ j : Fin p, β j * X ((t : ℤ) - (j : ℕ)) ω ^ 2)
              - ((T : ℝ) - p)⁻¹ * ∑ u ∈ Finset.Ico p T, X ((u : ℤ) + 1) ω ^ 2) ^ 2)
            / tss T ω) := by
  obtain ⟨β0, β, hsplit⟩ := arch_tss_eq_rss_add_ess hrss htss T ω
  refine ⟨β0, β, ?_⟩
  have key : ∀ a b e : ℝ, b ≠ 0 → b = a + e → 1 - a / b = e / b := by
    intro a b e hb hbe
    field_simp
    linarith
  rw [archTR2Stat, key _ _ _ hne hsplit]

end StatLean.TimeSeries
