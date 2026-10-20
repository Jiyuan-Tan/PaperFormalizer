module
public import StatLean.TimeSeries.Process.Defs
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Time series — model definitions (noise classes, ARMA/ARIMA, ARCH/GARCH, TAR, SV)

The model classes of FY chapters 1 and 4, as `Prop`-valued predicates on given processes.
Two noise regimes, exactly as the book prescribes (FY §1.5 chapeau): the **linear** models
(§1.3) take *white noise* (uncorrelated, second-moment) innovations, while the
**nonlinear** models (§1.5, ch. 4) take *i.i.d.* innovations.

* `IsWhiteNoise` (`WN(0,σ²)`, §1.3.1), `IsIIDNoise` (`IID(0,σ²)`, §1.3.1);
* `SatisfiesARMA` (bare a.e. recurrence), `IsARMA` (eq. (1.3)), `IsAR` (eq. (1.1)),
  `IsMA` (eq. (1.2)); the lag polynomials `arPoly` (`b(z) = 1 - b₁z - ⋯ - b_pz^p`) and
  `maPoly` (`a(z) = 1 + a₁z + ⋯ + a_qz^q`) with the book's sign conventions (§1.3.4);
* `diff` and `IsARIMA` (§1.3.5): `Y ~ ARIMA(p,d,q)` iff `(1-B)^d Y` is a *stationary*
  ARMA(p,q);
* `archVol`, `IsARCH` (ch. 4, Definition 4.2, eq. (4.15)) and `IsGARCH` (Definition 4.3,
  eq. (4.24)) — ch. 4 notation (`c₀`, order `p`), not the ch. 1 variant;
* `IsTAR` (ch. 4, Definition 4.1, eq. (4.1)) — `k`-regime threshold autoregression;
* `IsSV` (§4.2.9) — stochastic volatility with latent AR(1) log-volatility.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003: §1.3.1–§1.3.5
(pp. 10–14, eqs. (1.1)–(1.3)); §1.5 (pp. 16–18, eqs. (1.6)–(1.8)); §4.1.1 Definition 4.1
(p. 126, eq. (4.1)); §4.2.1 Definition 4.2 (p. 143, eq. (4.15)); §4.2.2 Definition 4.3
(p. 147, eq. (4.24)); §4.2.9 (pp. 179–180). (`FY §1.3, §1.5, §4.1.1 Def 4.1, §4.2.1–4.2.2
Def 4.2–4.3, §4.2.9`.)

**Proof formalization notes.**
* Model recurrences hold `μ`-a.e. per time point (`=ᵐ[μ]`) — the distributional reading
  of the book's displayed equations.
* ARCH follows ch. 4's Definition 4.2, which (unlike ch. 1's eq. (1.6)) makes the clause
  "`ε_t` independent of `{X_{t-k}, k ≥ 1}`" explicit; we state it as independence of
  `σ(ε_t)` from `sigmaLT X t`.
* In `IsARCH` the volatility `σ_t = archVol …` is explicit (a measurable function of
  `X_{t-1}, …, X_{t-p}`), taking `Real.sqrt` of the manifestly nonnegative affine form.
  In `IsGARCH` the volatility is carried as a separate process `σvol` with an
  `adapted` field (`σvol t` is `σ{X_s : s < t}`-measurable) — constitutive of
  "conditional heteroscedasticity" (FY §4.2.2: `σ_t²` *is* the conditional variance
  given the infinite past, Proposition 4.2(i)); Theorem 4.4's stationary construction
  verifies it.
* `IsTAR` uses a common max order `P` with zero-padding for the book's per-regime orders
  `p_i` (LEAN-ONLY reparametrization: choosing `p_i < P` is setting trailing regime
  coefficients to `0`; no scope change). The book's misprint `σ₁ = ⋯ = σ_p` (p. 126) is
  a typo for `σ_k` and does not affect the definition.
* `IsARIMA` requires `IsStationary` of the differenced process, imported from
  `Process/Defs.lean` — the book's forward reference from §1.3.5 to §2.1.

**Bibliographic comments.** Autoregressions are due to G. U. Yule ("On a method of
investigating periodicities in disturbed series", *Phil. Trans. Roy. Soc. A* **226**
(1927), 267–298); moving averages to E. Slutsky (1927/1937); the ARMA synthesis and the
foundational role of white noise to H. Wold (1938). ARIMA modeling is G. E. P. Box and
G. M. Jenkins, *Time Series Analysis: Forecasting and Control*, Holden-Day, 1970. ARCH is
R. F. Engle ("Autoregressive conditional heteroscedasticity with estimates of the variance
of United Kingdom inflation", *Econometrica* **50** (1982), 987–1008); GARCH is
T. Bollerslev ("Generalized autoregressive conditional heteroskedasticity",
*J. Econometrics* **31** (1986), 307–327). Threshold autoregression is H. Tong (1977/1978;
H. Tong and K. S. Lim, "Threshold autoregression, limit cycles and cyclical data",
*JRSS B* **42** (1980), 245–292; H. Tong, *Non-linear Time Series*, Oxford, 1990).
Stochastic volatility in the form used here is S. J. Taylor, *Modelling Financial Time
Series*, Wiley, 1986.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Noise classes (FY §1.3.1) -/

/-- **White noise** `WN(0, σ²)` (FY §1.3.1): mean zero, common variance `σ²`, pairwise
uncorrelated — a second-moment-only notion (explicitly *not* independence). -/
structure IsWhiteNoise (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (implicit in FY: each `ε_t` is a random variable). -/
  measurable : ∀ t, Measurable (ε t)
  /-- Constitutive (FY §1.3.1): finite second moments. -/
  memLp : ∀ t, MemLp (ε t) 2 μ
  /-- Constitutive (FY §1.3.1): `E ε_t = 0`. -/
  integral_eq_zero : ∀ t, ∫ ω, ε t ω ∂μ = 0
  /-- Constitutive (FY §1.3.1): `Var ε_t = σ²`, the same at every time. -/
  variance_eq : ∀ t, variance (ε t) μ = σ2
  /-- Constitutive (FY §1.3.1): `Cov(ε_s, ε_t) = 0` for `s ≠ t`. -/
  uncorrelated : ∀ s t, s ≠ t → cov[ε s, ε t; μ] = 0

/-- **I.i.d. noise** `IID(0, σ²)` (FY §1.3.1): independent, identically distributed,
mean zero, variance `σ²`. The §1.5/ch. 4 nonlinear models use this stronger class
(FY §1.5 standing convention). -/
structure IsIIDNoise (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (implicit in FY: each `ε_t` is a random variable). -/
  measurable : ∀ t, Measurable (ε t)
  /-- Constitutive (FY §1.3.1): mutual independence of the family. -/
  iIndep : iIndepFun ε μ
  /-- Constitutive (FY §1.3.1): identical distribution. -/
  identDistrib : ∀ s t, IdentDistrib (ε s) (ε t) μ μ
  /-- Constitutive (FY §1.3.1): finite second moment (stated at time `0`; propagates by
  identical distribution). -/
  memLp : MemLp (ε 0) 2 μ
  /-- Constitutive (FY §1.3.1): `E ε_0 = 0`. -/
  integral_eq_zero : ∫ ω, ε 0 ω ∂μ = 0
  /-- Constitutive (FY §1.3.1): `Var ε_0 = σ²`. -/
  variance_eq : variance (ε 0) μ = σ2

/-! ## Linear models (FY §1.3) -/

/-- The bare **ARMA recurrence** (FY eq. (1.3)), holding `μ`-a.e. at every time:
`X_t = b₁ X_{t-1} + ⋯ + b_p X_{t-p} + ε_t + a₁ ε_{t-1} + ⋯ + a_q ε_{t-q}`.
Separated from the noise condition so that structural lemmas can be stated without it. -/
def SatisfiesARMA {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (X ε : ℤ → Ω → ℝ)
    (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, X t =ᵐ[μ] fun ω =>
    (∑ i, b i * X (t - 1 - (i : ℕ)) ω) + ε t ω + ∑ j, a j * ε (t - 1 - (j : ℕ)) ω

/-- **ARMA(p, q) model** (FY §1.3.4, eq. (1.3)): the recurrence `SatisfiesARMA` driven by
white noise `WN(0, σ²)`. No stationarity/causality/invertibility conditions are part of
the model definition (they are §2.1 theorems). -/
structure IsARMA {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (σ2 : ℝ) (X ε : ℤ → Ω → ℝ)
    (μ : Measure Ω) : Prop where
  /-- Constitutive (implicit in FY: `X_t` is a random variable). -/
  measurableX : ∀ t, Measurable (X t)
  /-- Constitutive (FY §1.3.4): the innovations are white noise `WN(0, σ²)`. -/
  whiteNoise : IsWhiteNoise ε σ2 μ
  /-- Constitutive (FY eq. (1.3)): the ARMA recurrence. -/
  recurrence : SatisfiesARMA b a X ε μ

/-- **AR(p) model** (FY §1.3.2, eq. (1.1)): ARMA(p, 0). -/
abbrev IsAR {p : ℕ} (b : Fin p → ℝ) (σ2 : ℝ) (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  IsARMA b (Fin.elim0 : Fin 0 → ℝ) σ2 X ε μ

/-- **MA(q) model** (FY §1.3.3, eq. (1.2)): ARMA(0, q). -/
abbrev IsMA {q : ℕ} (a : Fin q → ℝ) (σ2 : ℝ) (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  IsARMA (Fin.elim0 : Fin 0 → ℝ) a σ2 X ε μ

/-- The **AR polynomial** `b(z) = 1 - b₁ z - ⋯ - b_p z^p` (FY §1.3.4 sign convention:
AR coefficients enter with minus signs). -/
noncomputable def arPoly {p : ℕ} (b : Fin p → ℝ) : Polynomial ℝ :=
  1 - ∑ i, Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1)

/-- The **MA polynomial** `a(z) = 1 + a₁ z + ⋯ + a_q z^q` (FY §1.3.4 sign convention:
MA coefficients enter with plus signs). -/
noncomputable def maPoly {q : ℕ} (a : Fin q → ℝ) : Polynomial ℝ :=
  1 + ∑ j, Polynomial.C (a j) * Polynomial.X ^ ((j : ℕ) + 1)

/-- The **differencing operator** `(1 - B)`: `(diff Y) t = Y t - Y (t-1)` (FY §1.3.5).
`d`-fold differencing is `diff^[d]`. -/
def diff (Y : ℤ → Ω → ℝ) : ℤ → Ω → ℝ := fun t ω => Y t ω - Y (t - 1) ω

/-- **ARIMA(p, d, q) model** (FY §1.3.5): `Y` is ARIMA iff its `d`-fold difference
`(1-B)^d Y` is a *stationary* ARMA(p, q), `d ≥ 1`. Not self-contained in FY ch. 1 — the
stationarity notion is §2.1's, imported here from `Process/Defs.lean`. -/
structure IsARIMA {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (d : ℕ) (σ2 : ℝ)
    (Y ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (FY §1.3.5): the differencing order is at least one. -/
  one_le_d : 1 ≤ d
  /-- Constitutive (FY §1.3.5): the `d`-fold difference is an ARMA(p, q) process. -/
  isARMA : IsARMA b a σ2 (diff^[d] Y) ε μ
  /-- Constitutive (FY §1.3.5): the `d`-fold difference is stationary (§2.1 sense). -/
  stationary : IsStationary (diff^[d] Y) μ

/-! ## ARCH / GARCH (FY §4.2, Definitions 4.2–4.3) -/

/-- The **ARCH volatility** `σ_t = √(c₀ + b₁ X_{t-1}² + ⋯ + b_p X_{t-p}²)` (FY eq.
(4.15)). The radicand is nonnegative whenever `0 ≤ c₀` and `0 ≤ b i`, so `Real.sqrt`
introduces no junk under the model hypotheses. -/
noncomputable def archVol (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (X : ℤ → Ω → ℝ) (t : ℤ)
    (ω : Ω) : ℝ :=
  Real.sqrt (c0 + ∑ i, b i * X (t - 1 - (i : ℕ)) ω ^ 2)

/-- **ARCH(p) model** (FY §4.2.1, Definition 4.2, eq. (4.15)): `X_t = σ_t ε_t` with
`σ_t² = c₀ + b₁ X_{t-1}² + ⋯ + b_p X_{t-p}²`, i.i.d. unit-variance noise independent of
the past. (Ch. 1's eq. (1.6) is the same model in different notation.) -/
structure IsARCH (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) :
    Prop where
  /-- Constitutive (FY Def 4.2): `c₀ ≥ 0`. -/
  c0_nonneg : 0 ≤ c0
  /-- Constitutive (FY Def 4.2): `b_j ≥ 0`. -/
  b_nonneg : ∀ i, 0 ≤ b i
  /-- Constitutive (implicit in FY: `X_t` is a random variable). -/
  measurableX : ∀ t, Measurable (X t)
  /-- Constitutive (FY Def 4.2): `{ε_t} ∼ IID(0, 1)`. -/
  iid : IsIIDNoise ε 1 μ
  /-- Constitutive (FY Def 4.2): `ε_t` is independent of `{X_{t-k}, k ≥ 1}`. -/
  indep_past : ∀ t : ℤ,
    Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT X t) μ
  /-- Constitutive (FY eq. (4.15)): `X_t = σ_t ε_t` a.e. -/
  recurrence : ∀ t : ℤ, X t =ᵐ[μ] fun ω => archVol c0 b X t ω * ε t ω

/-- **GARCH(p, q) model** (FY §4.2.2, Definition 4.3, eq. (4.24)): `X_t = σ_t ε_t`,
`σ_t² = c₀ + Σᵢ bᵢ X_{t-i}² + Σⱼ aⱼ σ_{t-j}²`, with the volatility carried as an
explicit past-adapted process `σvol`. -/
structure IsGARCH (c0 : ℝ) {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (X σvol ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (FY Def 4.3): `c₀ ≥ 0`. -/
  c0_nonneg : 0 ≤ c0
  /-- Constitutive (FY Def 4.3): `bᵢ ≥ 0`. -/
  b_nonneg : ∀ i, 0 ≤ b i
  /-- Constitutive (FY Def 4.3): `aⱼ ≥ 0`. -/
  a_nonneg : ∀ j, 0 ≤ a j
  /-- Constitutive (implicit in FY: `X_t` is a random variable). -/
  measurableX : ∀ t, Measurable (X t)
  /-- Constitutive (implicit in FY: `σ_t` is a random variable). -/
  measurableVol : ∀ t, Measurable (σvol t)
  /-- Constitutive (FY §4.2.2: `σ_t` is a volatility): `σ_t ≥ 0` a.e. -/
  vol_nonneg : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ σvol t ω
  /-- Constitutive (FY §4.2.2, Prop 4.2(i): `σ_t²` is the conditional variance given the
  past — the volatility is determined by the strict past of `X`). Theorem 4.4's
  stationary construction realizes this field. -/
  adapted : ∀ t, Measurable[sigmaLT X t] (σvol t)
  /-- Constitutive (FY Def 4.3): `{ε_t} ∼ IID(0, 1)`. -/
  iid : IsIIDNoise ε 1 μ
  /-- Constitutive (FY Def 4.3): `ε_t` is independent of `{X_{t-k}, k ≥ 1}`. -/
  indep_past : ∀ t : ℤ,
    Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT X t) μ
  /-- Constitutive (FY eq. (4.24), first equation): `X_t = σ_t ε_t` a.e. -/
  recX : ∀ t : ℤ, X t =ᵐ[μ] fun ω => σvol t ω * ε t ω
  /-- Constitutive (FY eq. (4.24), second equation): the volatility recursion a.e. -/
  recVol : ∀ t : ℤ, (fun ω => σvol t ω ^ 2) =ᵐ[μ] fun ω =>
    c0 + (∑ i, b i * X (t - 1 - (i : ℕ)) ω ^ 2) + ∑ j, a j * σvol (t - 1 - (j : ℕ)) ω ^ 2

/-! ## ARCH(∞) (FY §2.1.5, eq. (2.15)) -/

/-- **ARCH(∞) model** (FY §2.1.5, eq. (2.15)): `Y_t = ρ_t ξ_t` with
`ρ_t = a + Σ_{j≥1} b_j Y_{t-1-j+1}` — in our indexing, coefficient `bc j` multiplies
`Y_{t-1-j}`, matching the book's `b_{j+1} Y_{t-(j+1)}` — where `{ξ_t}` is a nonnegative
i.i.d. family with mean `1`, and `a ≥ 0`, `bc j ≥ 0`. Contains the standard ARCH(q) via
`Y_t = X_t²`, `ξ_t = ε_t²`, and GARCH under `Σaᵢ < 1` (FY §2.1.5). The infinite sum is a
`tsum` (junk `0` when not a.e. summable; the §2.1.5 theory works under `Σ bc < 1`, where
the constructed solutions are a.e. summable). -/
structure IsARCHInf (a : ℝ) (bc : ℕ → ℝ) (Y ξ : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (FY eq. (2.15)): `a ≥ 0`. -/
  a_nonneg : 0 ≤ a
  /-- Constitutive (FY eq. (2.15)): `b_j ≥ 0`. -/
  bc_nonneg : ∀ j, 0 ≤ bc j
  /-- Constitutive (implicit in FY: the solution and noise are random variables). -/
  measurableY : ∀ t, Measurable (Y t)
  measurableXi : ∀ t, Measurable (ξ t)
  /-- Constitutive (FY eq. (2.15)): the noise is nonnegative. -/
  xi_nonneg : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ ξ t ω
  /-- Constitutive (FY eq. (2.15)): the noise is i.i.d. -/
  iIndep : iIndepFun ξ μ
  identDistrib : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ
  /-- Constitutive (FY eq. (2.15)): unit mean, `E ξ_t = 1`. -/
  integrable_xi : Integrable (ξ 0) μ
  integral_xi : ∫ ω, ξ 0 ω ∂μ = 1
  /-- Constitutive (FY §2.7.1 model semantics, surfaced): `ξ_t` is independent of the
  past of the solution — the implicit assumption FY's uniqueness proof uses. -/
  indep_past : ∀ t : ℤ,
    Indep (MeasurableSpace.comap (ξ t) inferInstance) (sigmaLT Y t) μ
  /-- Constitutive (FY eq. (2.15)): the solution is nonnegative. -/
  Y_nonneg : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Y t ω
  /-- Constitutive (FY eq. (2.15)): `Y_t = (a + Σ_j bc_j Y_{t-1-j}) ξ_t` a.e. -/
  recurrence : ∀ t : ℤ, Y t =ᵐ[μ]
    fun ω => (a + ∑' j : ℕ, bc j * Y (t - 1 - (j : ℕ)) ω) * ξ t ω

/-! ## Threshold autoregression (FY §4.1.1, Definition 4.1) -/

/-- **TAR model with `k` regimes** (FY Definition 4.1, eq. (4.1)):
`X_t = Σᵢ {b_{i0} + b_{i1} X_{t-1} + ⋯ + b_{iP} X_{t-P} + σᵢ ε_t} · I(X_{t-d} ∈ Aᵢ)`,
where `{Aᵢ}` is a measurable partition of `ℝ`, `d ≥ 1` is the delay, and
`{ε_t} ∼ IID(0,1)`. LEAN-ONLY: a common max order `P` with zero-padding replaces the
book's per-regime orders `p_i` (no scope change). -/
structure IsTAR {k P : ℕ} (b0 : Fin k → ℝ) (b : Fin k → Fin P → ℝ) (σ : Fin k → ℝ)
    (A : Fin k → Set ℝ) (d : ℕ) (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (FY Def 4.1): the delay is a positive integer. -/
  one_le_d : 1 ≤ d
  /-- Constitutive (FY Def 4.1): regime noise scales `σᵢ > 0`. -/
  sigma_pos : ∀ i, 0 < σ i
  /-- Constitutive (implicit in FY: regimes are events for `X_{t-d}`). -/
  measurableA : ∀ i, MeasurableSet (A i)
  /-- Constitutive (FY Def 4.1): the regimes are pairwise disjoint. -/
  disjointA : Pairwise fun i j => Disjoint (A i) (A j)
  /-- Constitutive (FY Def 4.1): the regimes cover `ℝ`. -/
  iUnion_eq_univ : (⋃ i, A i) = Set.univ
  /-- Constitutive (implicit in FY: `X_t` is a random variable). -/
  measurableX : ∀ t, Measurable (X t)
  /-- Constitutive (FY Def 4.1): `{ε_t} ∼ IID(0, 1)`. -/
  iid : IsIIDNoise ε 1 μ
  /-- Constitutive (FY §4.1 generative reading, as in Def 4.2): `ε_t` independent of the
  past of `X`. -/
  indep_past : ∀ t : ℤ,
    Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT X t) μ
  /-- Constitutive (FY eq. (4.1)): the regime-switching recurrence a.e. -/
  recurrence : ∀ t : ℤ, X t =ᵐ[μ] fun ω =>
    ∑ i, (A i).indicator
      (fun _ => b0 i + (∑ j, b i j * X (t - 1 - (j : ℕ)) ω) + σ i * ε t ω)
      (X (t - (d : ℤ)) ω)

/-! ## Stochastic volatility (FY §4.2.9) -/

/-- **Stochastic volatility model** (FY §4.2.9): `X_t = ε_t · g(h_t)` with latent AR(1)
log-volatility `h_t = a₀ + a₁ h_{t-1} + e_t`, the two noise families independent of each
other; `{ε_t} ∼ IID(0,1)`, `{e_t} ∼ IID(0, σ_e²)`, `g > 0` known. -/
structure IsSV (g : ℝ → ℝ) (a0 a1 σe2 : ℝ) (X h ε e : ℤ → Ω → ℝ) (μ : Measure Ω) :
    Prop where
  /-- Constitutive (FY §4.2.9): the volatility transform is positive. -/
  g_pos : ∀ x, 0 < g x
  /-- Constitutive (implicit in FY): `X_t`, `h_t` are random variables. -/
  measurableX : ∀ t, Measurable (X t)
  measurableH : ∀ t, Measurable (h t)
  /-- Constitutive (FY §4.2.9): `{ε_t} ∼ IID(0, 1)`. -/
  iidNoise : IsIIDNoise ε 1 μ
  /-- Constitutive (FY §4.2.9): `{e_t} ∼ IID(0, σ_e²)`. -/
  iidLatent : IsIIDNoise e σe2 μ
  /-- Constitutive (FY §4.2.9): the observation and latent noise families are independent. -/
  indep_families :
    Indep (⨆ t : ℤ, MeasurableSpace.comap (ε t) inferInstance)
      (⨆ t : ℤ, MeasurableSpace.comap (e t) inferInstance) μ
  /-- Constitutive (FY §4.2.9, first equation): `X_t = ε_t g(h_t)` a.e. -/
  recX : ∀ t : ℤ, X t =ᵐ[μ] fun ω => ε t ω * g (h t ω)
  /-- Constitutive (FY §4.2.9, second equation): `h_t = a₀ + a₁ h_{t-1} + e_t` a.e. -/
  recH : ∀ t : ℤ, h t =ᵐ[μ] fun ω => a0 + a1 * h (t - 1) ω + e t ω

end StatLean.TimeSeries
