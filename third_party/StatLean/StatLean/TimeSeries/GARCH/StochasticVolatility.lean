module
public import StatLean.TimeSeries.Models.Defs
public import StatLean.TimeSeries.Process.LinearProcess
public import StatLean.TimeSeries.Process.SecondOrder
public import StatLean.TimeSeries.Process.Stationary
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
# Stochastic volatility models (FY §4.2.9, eqs. (4.60)–(4.62))

The SV model `X_t = ε_t g(h_t)` with latent AR(1) log-volatility
`h_t = a₀ + a₁ h_{t−1} + e_t` is `Models/Defs.lean`'s `IsSV`. This file carries the
three in-text results, all elementary once the AR(1) facts and the lognormal moment
formula are available:

* **eq. (4.60)**: `|a₁| < 1` ⇒ the latent process is (strictly) stationary with
  `μ_h = a₀/(1 − a₁)` and `γ_h(k) = σ_e²a₁^{|k|}/(1 − a₁²)`, hence `X` is strictly
  stationary;
* **eq. (4.61)** (Taylor's lognormal SV, `g = exp(·/2)` and Gaussian `ε`): the even
  moments `E X_t^{2k} = (2k)!·exp(kμ_h + k²σ_h²/2)/(2^k k!)`, and in particular the
  kurtosis `κ_x = 3e^{σ_h²} > 3` — SV is always leptokurtic;
* **eq. (4.62)**: `log X_t² = h_t + log ε_t²`, an ARMA(1,1) in its first two moments
  (compare Example 2.7), together with the squared-process autocorrelation
  `Corr(X_t², X_{t−k}²) = (exp(σ_h² a₁^{|k|}) − 1)/(exp(σ_h²) − 1)`.

Estimation for SV models (GMM, Kalman filtering on (4.62), MCMC) is citation-only in
FY §4.2.9 and is not formalized.

**Proof formalization notes.**
* The standard-normal even moment `∫ x^{2k} dN(0,1) = (2k)!/(2^k k!)` is absent from the
  Mathlib pin and is built here (`integral_pow_even_gaussianReal`) out of the m.g.f.
  `e^{t²/2}` via the Leibniz recursion `f^{(n+1)} = y f^{(n)} + n f^{(n−1)}`
  (`iteratedDeriv_id_mul`), which gives `f^{(n+1)}(0) = n f^{(n−1)}(0)`.
* Four hypotheses that FY's §4.2.9 has but the frozen Lean statements did not carry were
  once recorded here as *named debts*; all four are now **supplied explicitly** and the
  file is `sorry`-free. Each carries a `Statement strengthening (documented)` paragraph
  in the style of `ForMathlib/Markov/GeometricErgodicity.lean`'s
  `nlARKernel_geometricallyErgodic`, together with the witness showing the statement is
  false or unprovable without it. They are: the **causal representation** `hcausal` of
  the latent AR(1) chain (`IsSV` alone does not force `σ{ε} ⟂ σ{h}` — the recursion
  admits non-causal solutions, and then even (4.61) fails); `Measurable g` (recovering it
  from `hSV.measurableX` is a descriptive-set-theoretic statement, unavailable for an
  abstract `Ω`); Gaussian observation noise `hgauss`, which gives `μ{ε_t = 0} = 0`
  (`IsIIDNoise ε 1` does not); and Gaussianity of the latent chain `hjoint`, which gives
  joint normality of `(h_k, h_0)` (the marginal `hlatent` plus `hacvf` does not).
  All four hold in FY's model (4.60)–(4.62): `g = exp(·/2)` is continuous, `e_t` and
  `ε_t` are Gaussian, and the latent chain is the causal solution of (4.60).
* **`IsSV.acf_sq_lognormal` is false as printed** whenever `a₁ ≠ 0` and `k ≠ 0`: the
  denominator of `Corr(X_t², X_{t−k}²)` is `3e^{σ_h²} − 1`, not `e^{σ_h²} − 1`, the `3`
  being `E ε⁴` in `Var(X_t²)`. The corrected identity is proved here as
  `acf_sq_lognormal_corrected`, and `IsSV.acf_sq_lognormal` states it at nonzero lags
  (at lag `0` the autocorrelation is `1`, the one place FY's printed denominator is the
  right one). See that theorem's docstring for the verification.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.9,
eqs. (4.60)–(4.62) (pp. 179–181). (`FY §4.2.9`.)

**Bibliographic comments.** The lognormal SV model is S. J. Taylor, *Modelling Financial
Time Series* (Wiley, 1986); the ARMA(1,1) representation of `log X_t²` and the
quasi-likelihood/Kalman route are Harvey, Ruiz & Shephard (1994).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A linear process over mean-zero (white) noise has mean zero: the mean is the limit
of the (vanishing) means of the `L²`-approximating partial sums, the `L¹` defect being
dominated by the `L²` defect on a probability space. -/
private lemma integral_eq_zero_of_isLinearProcessOf [IsProbabilityMeasure μ]
    {ψ : ℕ → ℝ} {σ2 : ℝ} {Y ε : ℤ → Ω → ℝ} (hY : IsLinearProcessOf ψ Y ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (Y t)) (t : ℤ) : ∫ ω, Y t ω ∂μ = 0 := by
  have hmem : MemLp (Y t) 2 μ := hY.memLp hψ hε hmeas t
  have hint : Integrable (Y t) μ := hmem.integrable one_le_two
  have hεint : ∀ s : ℤ, Integrable (ε s) μ := fun s => (hε.memLp s).integrable one_le_two
  have hSmem : ∀ N : ℕ,
      MemLp (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ := by
    intro N
    have := memLp_finset_sum (μ := μ) (p := 2) (Finset.range N)
      (f := fun (j : ℕ) ω => ψ j * ε (t - (j : ℕ)) ω)
      (fun j _ => (hε.memLp (t - (j : ℕ))).const_mul (ψ j))
    simpa using this
  have hSint : ∀ (N : ℕ),
      Integrable (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) μ :=
    fun N => (hSmem N).integrable one_le_two
  have hS0 : ∀ N : ℕ, ∫ ω, (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ = 0 := by
    intro N
    rw [integral_finset_sum _ fun j _ => (hεint _).const_mul _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, hε.integral_eq_zero, mul_zero]
  have hbound : ∀ N : ℕ, |∫ ω, Y t ω ∂μ|
      ≤ (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ).toReal := by
    intro N
    have hfmem : MemLp (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ :=
      hmem.sub (hSmem N)
    have hfint : Integrable (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) μ :=
      hint.sub (hSint N)
    have hval : ∫ ω, (Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ
        = ∫ ω, Y t ω ∂μ := by
      rw [integral_sub hint (hSint N), hS0 N, sub_zero]
    have h1 : |∫ ω, (Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ|
        ≤ ∫ ω, |Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω| ∂μ :=
      abs_integral_le_integral_abs
    have h2 : ∫ ω, |Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω| ∂μ
        = (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω)
            1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      rw [← integral_norm_eq_lintegral_enorm hfint.aestronglyMeasurable]
      simp [Real.norm_eq_abs]
    have h3 : eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 1 μ
        ≤ eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le one_le_two hfmem.aestronglyMeasurable
    rw [hval] at h1
    refine h1.trans ?_
    rw [h2]
    exact ENNReal.toReal_mono hfmem.eLpNorm_ne_top h3
  have htend : Tendsto
      (fun N => (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω)
        2 μ).toReal) atTop (𝓝 0) := by
    simpa using! (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hY t)
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto' htend hbound) (abs_nonneg _))

/-- **FY eq. (4.60)**: with `|a₁| < 1` the latent log-volatility is second-order
stationary with mean `a₀/(1 − a₁)` and autocovariance `σ_e² a₁^{|k|}/(1 − a₁²)`. -/
theorem IsSV.latent_stationary [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: causal AR(1) latent process; FY eq. (4.60)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (hmeas : ∀ t, Measurable (h t)) :
    IsStationary h μ ∧ (∀ t, ∫ ω, h t ω ∂μ = a0 / (1 - a1)) ∧
      ∀ k : ℤ, acvf h μ k = σe2 * a1 ^ k.natAbs / (1 - a1 ^ 2) := by
  have hWN : IsWhiteNoise e σe2 μ := hSV.iidLatent.isWhiteNoise
  have hψ : Summable fun j : ℕ => |a1 ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg a1) ha1
  have hYm : ∀ t : ℤ, Measurable (fun ω => h t ω - a0 / (1 - a1)) :=
    fun t => (hmeas t).sub_const _
  obtain ⟨hstatY, hacvfY⟩ := hcausal.isStationary hψ hWN hYm
  -- the centred process has vanishing mean, so `E h_t = a₀/(1 − a₁)`
  have hYint : ∀ t : ℤ, Integrable (fun ω => h t ω - a0 / (1 - a1)) μ :=
    fun t => (hstatY.memLp t).integrable one_le_two
  have heq : ∀ t : ℤ,
      ((fun ω => h t ω - a0 / (1 - a1)) + fun _ : Ω => a0 / (1 - a1)) = h t := by
    intro t; funext ω; simp
  have hhint : ∀ t : ℤ, Integrable (h t) μ := by
    intro t
    have h1 := (hYint t).add (integrable_const (a0 / (1 - a1)))
    rwa [heq t] at h1
  have hmean : ∀ t : ℤ, ∫ ω, h t ω ∂μ = a0 / (1 - a1) := by
    intro t
    have h0 := integral_eq_zero_of_isLinearProcessOf hcausal hψ hWN hYm t
    rw [integral_sub (hhint t) (integrable_const _)] at h0
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
    linarith
  -- covariances are unchanged by centring
  have hcov : ∀ s t : ℤ, cov[fun ω => h s ω - a0 / (1 - a1),
      fun ω => h t ω - a0 / (1 - a1); μ] = cov[h s, h t; μ] := by
    intro s t
    rw [covariance_sub_const_left (hhint s), covariance_sub_const_right (hhint t)]
  -- the geometric autocovariance
  have hgeo : ∀ n : ℕ, (∑' j : ℕ, a1 ^ j * a1 ^ (j + n)) = a1 ^ n / (1 - a1 ^ 2) := by
    intro n
    have hterm : ∀ j : ℕ, a1 ^ j * a1 ^ (j + n) = a1 ^ n * (a1 ^ 2) ^ j := by
      intro j; ring
    have hsq : a1 ^ 2 < 1 := by nlinarith [abs_nonneg a1, sq_abs a1, abs_lt.mp ha1]
    calc (∑' j : ℕ, a1 ^ j * a1 ^ (j + n)) = ∑' j : ℕ, a1 ^ n * (a1 ^ 2) ^ j :=
          tsum_congr hterm
      _ = a1 ^ n * ∑' j : ℕ, (a1 ^ 2) ^ j := tsum_mul_left
      _ = a1 ^ n / (1 - a1 ^ 2) := by
          rw [tsum_geometric_of_lt_one (sq_nonneg a1) hsq, div_eq_mul_inv]
  refine ⟨⟨fun t => ?_, fun s t => by rw [hmean s, hmean t], fun t k => ?_⟩, hmean, fun k => ?_⟩
  · have h1 := (hstatY.memLp t).add (memLp_const (μ := μ) (p := 2) (a0 / (1 - a1)))
    rwa [heq t] at h1
  · have h1 := hstatY.cov_shift t k
    rw [hcov (t + k) t, hcov k 0] at h1
    exact h1
  · have h1 := hacvfY k
    rw [acvf, hcov k 0] at h1
    rw [acvf, h1, hgeo k.natAbs, mul_div_assoc]

omit [MeasurableSpace Ω] in
private lemma comap_window_le {ι : Type*} (f : ℤ → Ω → ℝ) (u : ι → ℤ) :
    MeasurableSpace.comap (fun ω (i : ι) => f (u i) ω) inferInstance
      ≤ ⨆ s : ℤ, MeasurableSpace.comap (f s) inferInstance := by
  have h1 : (inferInstance : MeasurableSpace (ι → ℝ))
      = ⨆ i : ι, MeasurableSpace.comap (fun v : ι → ℝ => v i) inferInstance := rfl
  rw [h1, MeasurableSpace.comap_iSup]
  refine iSup_le fun i => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup (fun s : ℤ => MeasurableSpace.comap (f s) inferInstance) (u i)

/-- The a.e. limit of the causal partial sums, taken as a *pointwise* `limUnder`, is
measurable for whatever σ-algebra the innovations are measurable for — in particular for
`σ{e_s : s ∈ ℤ}`. The σ-algebra is an explicit argument (not an instance) so that it can
be instantiated at a non-ambient one. -/
private lemma measurable_limUnder_psum {Ω' : Type*} (m : MeasurableSpace Ω') {a1 : ℝ}
    {e : ℤ → Ω' → ℝ} (hem : ∀ s : ℤ, Measurable[m] (e s)) (t : ℤ) :
    Measurable[m] fun ω =>
      limUnder atTop (fun N => ∑ j ∈ Finset.range N, a1 ^ j * e (t - (j : ℕ)) ω) := by
  letI := m
  exact (MeasureTheory.StronglyMeasurable.limUnder (l := atTop)
    (fun _N => (Finset.measurable_sum _ fun _j _ =>
      (hem _).const_mul _).stronglyMeasurable)).measurable

/-- A window of `m`-measurable coordinates generates a sub-σ-algebra of `m`. -/
private lemma comap_window_le_of_measurable {Ω' : Type*} (m : MeasurableSpace Ω')
    {κ : Type*} (F : κ → Ω' → ℝ) (hF : ∀ j, Measurable[m] (F j)) :
    MeasurableSpace.comap (fun ω (j : κ) => F j ω) inferInstance ≤ m := by
  letI := m
  exact measurable_iff_comap_le.1 (measurable_pi_lambda _ fun j => hF j)

/-- **FY eq. (4.60)**: the causal latent chain is strictly stationary. The centred chain
is a linear process over i.i.d. innovations, hence strictly stationary
(`IsLinearProcessOf.isStrictlyStationary`), and adding the constant `a₀/(1−a₁)` is a
fixed measurable map through which every finite-dimensional law is pushed. -/
private lemma isStrictlyStationary_latent [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a0 a1 σe2 : ℝ} {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ) :
    IsStrictlyStationary h μ := by
  have hψ : Summable fun j : ℕ => |a1 ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg a1) ha1
  have hYm : ∀ t : ℤ, Measurable fun ω => h t ω - a0 / (1 - a1) :=
    fun t => (hSV.measurableH t).sub_const _
  have hY := hcausal.isStrictlyStationary hψ hSV.iidLatent hYm
  intro n tt k
  have hc : Measurable fun v : Fin n → ℝ => fun i => v i + a0 / (1 - a1) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).add_const _
  have hYw : ∀ c : ℤ, Measurable fun ω (i : Fin n) => h (tt i + c) ω - a0 / (1 - a1) :=
    fun c => measurable_pi_lambda _ fun i => hYm _
  have e1 : ∀ c : ℤ, (fun ω (i : Fin n) => h (tt i + c) ω)
      = (fun v : Fin n → ℝ => fun i => v i + a0 / (1 - a1))
        ∘ (fun ω (i : Fin n) => h (tt i + c) ω - a0 / (1 - a1)) := by
    intro c; funext ω i; simp
  have e0 : (fun ω (i : Fin n) => h (tt i) ω)
      = (fun v : Fin n → ℝ => fun i => v i + a0 / (1 - a1))
        ∘ (fun ω (i : Fin n) => h (tt i) ω - a0 / (1 - a1)) := by
    funext ω i; simp
  rw [e1 k, e0, ← Measure.map_map hc (hYw k), ← Measure.map_map hc
    (measurable_pi_lambda _ fun i => hYm (tt i))]
  congr 1
  simpa using hY n tt k

/-- **The observation noise is independent of the latent chain** — on finite windows,
which is all any consumer needs: `(ε_{u i})_i ⟂ (h_{w j})_j`.

**Statement strengthening (documented).** *Added*: the causal representation `hcausal`
(with `|a₁| < 1`), i.e. `h_t − a₀/(1−a₁) = Σ_{j≥0} a₁^j e_{t−j}` in `L²`.

*Why it is needed.* The conclusion is **not** derivable from `IsSV` alone. The structure
carries `indep_families` (`σ{ε_t} ⟂ σ{e_t}`) together with the pointwise recursion
`h_t = a₀ + a₁h_{t−1} + e_t`, and the recursion does not tie `h` to `σ{e_t}`: it is
satisfied by every solution, including ones whose "initial condition at `−∞`" is built
out of `ε`. Witness: take `a₀ = 0`, `a₁ = 1`, `h_0 := μ_h + √σ_h² ε_0`,
`h_t := h_0 + Σ_{0<s≤t} e_s` for `t > 0` and `h_t := h_0 − Σ_{t<s≤0} e_s` for `t < 0`.
Every field of `IsSV` holds, `h_0` is `N(μ_h, σ_h²)` and `ε_0` is `N(0,1)`, so all
hypotheses of (4.61) hold, yet `E X_0² = e^{μ_h+σ_h²/2}(1+σ_h²) ≠ e^{μ_h+σ_h²/2}`.

*Why FY supplies it.* In FY the latent chain **is** the causal solution of (4.60) — the
`|a₁| < 1` stationary AR(1) — which is exactly `hcausal`; `IsSV.latent_stationary`
already carries it. Given it, `h_t` agrees a.e. with the pointwise `limUnder` of the
causal partial sums, which is `σ{e_s}`-measurable, and `indep_families` transfers along
`IndepFun.congr`. -/
private lemma indep_noise_latent_window [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a0 a1 σe2 : ℝ} {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: the latent chain is the causal (stationary) solution of (4.60);
    -- FY §4.3, eq. (4.60)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    {ι κ : Type*} [Finite κ] (u : ι → ℤ) (w : κ → ℤ) :
    IndepFun (fun ω (i : ι) => ε (u i) ω) (fun ω (j : κ) => h (w j) ω) μ := by
  classical
  haveI : Countable κ := Finite.to_countable
  have hψ : Summable fun j : ℕ => |a1 ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg a1) ha1
  have hYm : ∀ t : ℤ, Measurable fun ω => h t ω - a0 / (1 - a1) :=
    fun t => (hSV.measurableH t).sub_const _
  have hem : ∀ s : ℤ,
      Measurable[⨆ t : ℤ, MeasurableSpace.comap (e t) inferInstance] (e s) := fun s =>
    measurable_iff_comap_le.2
      (le_iSup (fun t : ℤ => MeasurableSpace.comap (e t) inferInstance) s)
  -- the a.e. version of the latent chain, built from the innovations alone
  set H : ℤ → Ω → ℝ := fun t ω =>
    limUnder atTop (fun N => ∑ j ∈ Finset.range N, a1 ^ j * e (t - (j : ℕ)) ω)
      + a0 / (1 - a1) with hHdef
  have hHm : ∀ t : ℤ,
      Measurable[⨆ s : ℤ, MeasurableSpace.comap (e s) inferInstance] (H t) := by
    intro t
    have h1 : Measurable[⨆ s : ℤ, MeasurableSpace.comap (e s) inferInstance] fun ω =>
        limUnder atTop (fun N => ∑ j ∈ Finset.range N, a1 ^ j * e (t - (j : ℕ)) ω) :=
      measurable_limUnder_psum _ hem t
    exact h1.add_const _
  have hae : ∀ t : ℤ, H t =ᵐ[μ] h t := by
    intro t
    filter_upwards [hcausal.ae_tendsto hψ hSV.iidLatent hYm t] with ω hω
    have hl := hω.limUnder_eq
    simp only [hHdef]
    rw [hl]
    ring
  have h1 : IndepFun (fun ω (i : ι) => ε (u i) ω) (fun ω (j : κ) => H (w j) ω) μ :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hSV.indep_families (comap_window_le ε u))
      (comap_window_le_of_measurable _ (fun j => H (w j)) fun j => hHm (w j))
  refine h1.congr (ae_eq_refl _) ?_
  filter_upwards [ae_all_iff.2 fun j : κ => hae (w j)] with ω hω
  funext j
  exact hω j

/-- The one-coordinate case of `indep_noise_latent_window`. -/
private lemma indepFun_noise_latent [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ) (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (s t : ℤ) : IndepFun (ε s) (h t) μ :=
  (indep_noise_latent_window hSV ha1 hcausal (fun _ : Unit => s) (fun _ : Unit => t)).comp
    (measurable_pi_apply ()) (measurable_pi_apply ())

/-- The two-coordinate case of `indep_noise_latent_window`. -/
private lemma indepFun_pair_noise_latent [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a0 a1 σe2 : ℝ} {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (s t : ℤ) :
    IndepFun (fun ω => (ε s ω, ε t ω)) (fun ω => (h s ω, h t ω)) μ := by
  have hφ : Measurable fun v : Fin 2 → ℝ => (v 0, v 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  exact (indep_noise_latent_window hSV ha1 hcausal
    (fun i : Fin 2 => ![s, t] i) (fun i : Fin 2 => ![s, t] i)).comp hφ hφ

private lemma map_noise_block' [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    {A : Type*} [Finite A] (hε : IsIIDNoise ε σ2 μ) (u : A → ℤ) (k : ℤ) :
    μ.map (fun ω a => ε (u a + k) ω) = μ.map (fun ω a => ε (u a) ω) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  set S : Finset ℤ := Finset.image u Finset.univ with hS
  set ρ : A → {x // x ∈ S} :=
    fun a => ⟨u a, Finset.mem_image_of_mem u (Finset.mem_univ a)⟩ with hρ
  have hlaw : ∀ c : ℤ, μ.map (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω)
      = Measure.pi (fun _ : {x // x ∈ S} => μ.map (ε 0)) := by
    intro c
    have hinj : Function.Injective (fun b : {x // x ∈ S} => (b : ℤ) + c) := by
      intro b1 b2 h
      exact Subtype.ext (by simpa using h)
    have hindep : iIndepFun (fun b : {x // x ∈ S} => ε ((b : ℤ) + c)) μ :=
      hε.iIndep.precomp hinj
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun b => (hε.measurable _).aemeasurable).1 hindep]
    exact congrArg Measure.pi (funext fun b => (hε.identDistrib _ 0).map_eq)
  have hmb : ∀ c : ℤ, Measurable (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω) :=
    fun c => measurable_pi_lambda _ fun b => hε.measurable _
  have hcomp : Measurable (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) :=
    measurable_pi_lambda _ fun a => measurable_pi_apply (ρ a)
  have hfac : ∀ c : ℤ, (fun ω a => ε (u a + c) ω)
      = (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) ∘ (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω) :=
    fun c => rfl
  have hzero : (fun ω a => ε (u a) ω)
      = (fun v : {x // x ∈ S} → ℝ => v ∘ ρ)
        ∘ (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + 0) ω) := by
    funext ω a
    simp only [Function.comp_apply, add_zero, hρ]
  rw [hfac k, hzero, ← Measure.map_map hcomp (hmb k), ← Measure.map_map hcomp (hmb 0),
    hlaw k, hlaw 0]

/-- **FY eq. (4.60), conclusion**: a stationary latent process makes the observed SV
process strictly stationary.

**Statement strengthening (documented).** *Added*: `hg : Measurable g`. (The former
hypothesis `hstath : IsStrictlyStationary h μ` has been **removed**: it now follows from
`hcausal` via `isStrictlyStationary_latent`.)

*Why it is needed.* `IsSV` requires only `g_pos`. The proof pushes the shift through the
joint law of the pair of windows `((ε_{t_i+k})_i, (h_{t_i+k})_i)` and then composes with
the fixed map `(a, b) ↦ (a_i g(b_i))_i`; that last step is a `Measure.map` composition
and needs the map to be measurable. `hSV.measurableX` gives measurability of each `X_t`,
which pins `g` down only on `{ε_t ≠ 0}` and only through `h_t` (`g(h_t) = X_t/ε_t`
there); recovering a measurable `g` from that is a descriptive-set-theoretic statement
about the fibres of `(ε_t, h_t)`, not available for an abstract measurable space `Ω`.

*Why FY supplies it.* Every concrete FY instance of (4.60)–(4.62) has
`g = exp(·/2)`, which is continuous, hence measurable. -/
theorem IsSV.isStrictlyStationary [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a0 a1 σe2 : ℝ} {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: the volatility transform is measurable (FY's `g = exp(·/2)` is
    -- continuous); FY §4.3, eq. (4.60)
    (hg : Measurable g)
    -- USER-INPUT: the latent chain is the causal (stationary) solution of (4.60);
    -- FY §4.3, eq. (4.60)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ) :
    IsStrictlyStationary X μ := by
  classical
  have hstath : IsStrictlyStationary h μ := isStrictlyStationary_latent hSV ha1 hcausal
  intro n tt k
  have hmε : ∀ s : ℤ, Measurable (ε s) := hSV.iidNoise.measurable
  have hmh : ∀ s : ℤ, Measurable (h s) := hSV.measurableH
  set Φ : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) := fun p i => p.1 i * g (p.2 i) with hΦdef
  have hΦ : Measurable Φ := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst).mul
      (hg.comp ((measurable_pi_apply i).comp measurable_snd))
  have hEm : ∀ c : ℤ, Measurable (fun ω (i : Fin n) => ε (tt i + c) ω) :=
    fun c => measurable_pi_lambda _ fun i => hmε _
  have hHm : ∀ c : ℤ, Measurable (fun ω (i : Fin n) => h (tt i + c) ω) :=
    fun c => measurable_pi_lambda _ fun i => hmh _
  -- the noise window and the latent window are independent
  have hindep : ∀ c : ℤ, IndepFun (fun ω (i : Fin n) => ε (tt i + c) ω)
      (fun ω (i : Fin n) => h (tt i + c) ω) μ := fun c =>
    indep_noise_latent_window hSV ha1 hcausal
      (fun i : Fin n => tt i + c) (fun i : Fin n => tt i + c)
  have hpair : ∀ c : ℤ,
      μ.map (fun ω => ((fun (i : Fin n) => ε (tt i + c) ω), (fun (i : Fin n) => h (tt i + c) ω)))
        = (μ.map fun ω (i : Fin n) => ε (tt i + c) ω).prod
          (μ.map fun ω (i : Fin n) => h (tt i + c) ω) :=
    fun c => (indepFun_iff_map_prod_eq_prod_map_map (hEm c).aemeasurable
      (hHm c).aemeasurable).1 (hindep c)
  -- every window of `X` is the same measurable function of the pair of windows
  have hX : ∀ c : ℤ, μ.map (fun ω (i : Fin n) => X (tt i + c) ω)
      = (μ.map (fun ω => ((fun (i : Fin n) => ε (tt i + c) ω),
          (fun (i : Fin n) => h (tt i + c) ω)))).map Φ := by
    intro c
    have hall : ∀ᵐ ω ∂μ, ∀ i : Fin n, X (tt i + c) ω = ε (tt i + c) ω * g (h (tt i + c) ω) :=
      ae_all_iff.2 fun i => hSV.recX (tt i + c)
    have hae : (fun ω (i : Fin n) => X (tt i + c) ω)
        =ᵐ[μ] fun ω (i : Fin n) => ε (tt i + c) ω * g (h (tt i + c) ω) := by
      filter_upwards [hall] with ω hω
      funext i
      exact hω i
    rw [Measure.map_congr hae, Measure.map_map hΦ ((hEm c).prodMk (hHm c))]
    rfl
  have hh : (μ.map fun ω (i : Fin n) => h (tt i + k) ω)
      = μ.map fun ω (i : Fin n) => h (tt i + 0) ω := by
    simpa using hstath n tt k
  have hgoal0 : (fun ω (i : Fin n) => X (tt i) ω) = fun ω (i : Fin n) => X (tt i + 0) ω := by
    simp
  rw [hgoal0, hX k, hX 0, hpair k, hpair 0, hh,
    map_noise_block' hSV.iidNoise tt k, map_noise_block' hSV.iidNoise tt 0]


/-! ### Gaussian even moments -/

private noncomputable def gexp : ℝ → ℝ := fun y => Real.exp (y ^ 2 / 2)

private lemma contDiff_gexp : ContDiff ℝ (⊤ : ℕ∞) gexp :=
  Real.contDiff_exp.comp ((contDiff_id.pow 2).div_const 2)

private lemma differentiable_iteratedDeriv_gexp (m : ℕ) :
    Differentiable ℝ (iteratedDeriv m gexp) :=
  contDiff_gexp.differentiable_iteratedDeriv m (by exact_mod_cast lt_top_iff_ne_top.2 (by simp))

private lemma deriv_gexp : deriv gexp = fun y => y * gexp y := by
  funext y
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
    simpa using (hasDerivAt_pow 2 y).div_const 2
  have := (Real.hasDerivAt_exp (y ^ 2 / 2)).comp y h1
  simpa [gexp, Function.comp_def, mul_comm] using! this.deriv

private lemma iteratedDeriv_id_mul {g : ℝ → ℝ} (hg : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m g))
    (n : ℕ) : iteratedDeriv n (fun y => y * g y)
      = fun y => y * iteratedDeriv n g y + (n : ℝ) * iteratedDeriv (n - 1) g y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : ∀ y : ℝ, HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g y) y := by
      intro y
      have := (hg n y).hasDerivAt
      rwa [← iteratedDeriv_succ] at this
    have hB : ∀ y : ℝ, HasDerivAt (iteratedDeriv (n - 1) g) (iteratedDeriv (n - 1 + 1) g y) y := by
      intro y
      have := (hg (n - 1) y).hasDerivAt
      rwa [← iteratedDeriv_succ] at this
    rw [iteratedDeriv_succ, ih]
    funext y
    have hd : HasDerivAt
        (fun y : ℝ => y * iteratedDeriv n g y + (n : ℝ) * iteratedDeriv (n - 1) g y)
        (1 * iteratedDeriv n g y + y * iteratedDeriv (n + 1) g y
          + (n : ℝ) * iteratedDeriv (n - 1 + 1) g y) y :=
      ((hasDerivAt_id y).mul (hA y)).add ((hB y).const_mul (n : ℝ))
    rw [hd.deriv]
    cases n with
    | zero => simp; ring
    | succ m =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

private lemma iteratedDeriv_gexp_recur (n : ℕ) :
    iteratedDeriv (n + 1) gexp 0 = (n : ℝ) * iteratedDeriv (n - 1) gexp 0 := by
  rw [iteratedDeriv_succ', deriv_gexp,
    iteratedDeriv_id_mul differentiable_iteratedDeriv_gexp n]
  simp

private lemma iteratedDeriv_gexp_even (k : ℕ) :
    iteratedDeriv (2 * k) gexp 0
      = (Nat.factorial (2 * k) : ℝ) / (2 ^ k * Nat.factorial k) := by
  induction k with
  | zero => simp [gexp]
  | succ k ih =>
    have hstep : iteratedDeriv (2 * (k + 1)) gexp 0
        = (2 * k + 1 : ℝ) * iteratedDeriv (2 * k) gexp 0 := by
      have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [h1, iteratedDeriv_gexp_recur (2 * k + 1)]
      simp
    rw [hstep, ih]
    have h2 : Nat.factorial (2 * (k + 1))
        = (2 * k + 2) * ((2 * k + 1) * Nat.factorial (2 * k)) := by
      have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, Nat.factorial_succ, Nat.factorial_succ]
    rw [h2, Nat.factorial_succ]
    have hk : (0:ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    push_cast
    field_simp
    ring

private lemma integral_pow_even_gaussianReal (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1)
      = (Nat.factorial (2 * k) : ℝ) / (2 ^ k * Nat.factorial k) := by
  have hmgf : mgf id (gaussianReal 0 1) = gexp := by
    rw [mgf_id_gaussianReal]
    funext t
    norm_num [gexp]
  have hint : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by simp
  have hkey := iteratedDeriv_mgf_zero (X := (id : ℝ → ℝ)) (μ := gaussianReal 0 1) hint (2 * k)
  rw [hmgf, iteratedDeriv_gexp_even k] at hkey
  have hpi : ((gaussianReal 0 1)[(id : ℝ → ℝ) ^ (2 * k)])
      = ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1) := by simp
  rw [hpi] at hkey
  exact hkey.symm

/-- **The noise does not charge `0`.**

**Statement strengthening (documented).** *Added*: `hgauss : μ.map (ε 0) = gaussianReal
0 1`, standard normal observation noise.

*Why it is needed.* `IsIIDNoise ε 1` constrains only the first two moments, and a
mean-zero unit-variance law may well have an atom at `0` (e.g. `P(ε = ±√2) = 1/4`,
`P(ε = 0) = 1/2`). On `{ε_t = 0}` one has `log X_t² = log 0 = 0` while
`h_t + log ε_t² = h_t + 0 = h_t`, so (4.62) fails there unless `h_t = 0`: with such noise
the frozen statement of `log_sq_decomposition` is false (take `a₁ = 0`, `h_t = e_t`
standard normal).

*Why FY supplies it.* FY's (4.61)–(4.62) is Taylor's lognormal SV model, whose
observation noise is standard normal; `nullSingletonClass_gaussianReal` then gives the conclusion
for `ε_0`, and `IsIIDNoise.identDistrib` propagates it to every `ε_t`. -/
private lemma noise_ne_zero_ae [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: standard normal observation noise; FY §4.3, eq. (4.61)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1) (t : ℤ) :
    μ {ω | ε t ω = 0} = 0 := by
  have hmε : Measurable (ε t) := hSV.iidNoise.measurable t
  have hmap : μ.map (ε t) = gaussianReal 0 1 := by
    rw [(hSV.iidNoise.identDistrib t 0).map_eq, hgauss]
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h0 : (μ.map (ε t)) {(0 : ℝ)} = 0 := by rw [hmap]; exact measure_singleton 0
  rwa [Measure.map_apply hmε (measurableSet_singleton 0)] at h0

/-- **FY eq. (4.61)** (Taylor's lognormal SV): with `g(x) = e^{x/2}`, standard normal
`ε`, and a stationary Gaussian latent process with mean `μ_h` and variance `σ_h²`,
`E X_t^{2k} = (2k)! · exp(k μ_h + k²σ_h²/2) / (2^k k!)`.

**Statement strengthening (documented).** *Added*: the causal representation `hcausal`
(with `|a₁| < 1`) of the latent chain. It is what makes `ε_0` independent of `h_0`, and
the identity is **false** without it: `indep_noise_latent_window`'s witness satisfies
every other hypothesis of this theorem and gives
`E X_0² = e^{μ_h+σ_h²/2}(1+σ_h²) ≠ e^{μ_h+σ_h²/2}`. FY's latent chain is the causal
solution of (4.60), so the hypothesis is part of FY's model. -/
theorem IsSV.moment_even_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: standard normal observation noise; FY eq. (4.61)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    -- USER-INPUT: the latent chain is the causal (stationary) solution of (4.60);
    -- FY §4.3, eq. (4.60)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    -- USER-INPUT: stationary Gaussian latent law; FY eq. (4.61)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    (k : ℕ) :
    (∫ ω, X 0 ω ^ (2 * k) ∂μ)
      = (Nat.factorial (2 * k) : ℝ) * Real.exp (k * μh + (k : ℝ) ^ 2 * σh2 / 2)
        / (2 ^ k * Nat.factorial k) := by
  have hmε : Measurable (ε 0) := hSV.iidNoise.measurable 0
  have hmh : Measurable (h 0) := hSV.measurableH 0
  -- (a) the standard-normal even moment `(2k)!/(2^k k!)`
  have hA : ∫ ω, ε 0 ω ^ (2 * k) ∂μ
      = (Nat.factorial (2 * k) : ℝ) / (2 ^ k * Nat.factorial k) := by
    rw [← integral_pow_even_gaussianReal k, ← hgauss,
      integral_map hmε.aemeasurable
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ (2 * k)) _)]
  -- (b) the lognormal moment: the Gaussian m.g.f. at `t = k`
  have hB : ∫ ω, Real.exp ((k : ℝ) * h 0 ω) ∂μ
      = Real.exp ((k : ℝ) * μh + (k : ℝ) ^ 2 * σh2 / 2) := by
    have hm := mgf_gaussianReal hlatent (k : ℝ)
    rw [Real.coe_toNNReal σh2 hσh.le] at hm
    rw [show (∫ ω, Real.exp ((k : ℝ) * h 0 ω) ∂μ) = mgf (h 0) μ (k : ℝ) from rfl, hm]
    ring_nf
  -- (c) split the product along `ε ⟂ h`
  have hindep : IndepFun (fun ω => ε 0 ω ^ (2 * k)) (fun ω => Real.exp ((k : ℝ) * h 0 ω)) μ :=
    (indepFun_noise_latent hSV ha1 hcausal 0 0).comp (measurable_id.pow_const (2 * k))
      ((measurable_id.const_mul (k : ℝ)).exp)
  have hprod : ∫ ω, (ε 0 ω ^ (2 * k) * Real.exp ((k : ℝ) * h 0 ω)) ∂μ
      = (∫ ω, ε 0 ω ^ (2 * k) ∂μ) * ∫ ω, Real.exp ((k : ℝ) * h 0 ω) ∂μ :=
    hindep.integral_fun_mul_eq_mul_integral
      (hmε.pow_const (2 * k)).aestronglyMeasurable
      ((hmh.const_mul (k : ℝ)).exp).aestronglyMeasurable
  -- (d) the model equation, squared `k` times
  have hae : (fun ω => X 0 ω ^ (2 * k))
      =ᵐ[μ] fun ω => ε 0 ω ^ (2 * k) * Real.exp ((k : ℝ) * h 0 ω) := by
    filter_upwards [hSV.recX 0] with ω hω
    rw [hω, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [integral_congr_ae hae, hprod, hA, hB]
  ring


/-- **FY eq. (4.61), kurtosis**: the lognormal SV kurtosis is `3e^{σ_h²} > 3` — SV is
strictly leptokurtic (stated multiplicatively to avoid division).

**Statement strengthening (documented).** *Added*: the causal representation `hcausal`
(with `|a₁| < 1`), inherited from `IsSV.moment_even_lognormal`; see there. -/
theorem IsSV.kurtosis_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    -- USER-INPUT: the latent chain is the causal (stationary) solution of (4.60);
    -- FY §4.3, eq. (4.60)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2) :
    (∫ ω, X 0 ω ^ 4 ∂μ) = 3 * Real.exp σh2 * (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2 ∧
      3 < 3 * Real.exp σh2 := by
  have h4 := hSV.moment_even_lognormal hgauss ha1 hcausal hlatent hσh 2
  have h2 := hSV.moment_even_lognormal hgauss ha1 hcausal hlatent hσh 1
  norm_num at h4 h2
  refine ⟨?_, ?_⟩
  · rw [h4, h2, sq]
    have he : Real.exp σh2 * (Real.exp (μh + σh2 / 2) * Real.exp (μh + σh2 / 2))
        = Real.exp (2 * μh + 4 * σh2 / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    linarith
  · nlinarith [Real.add_one_lt_exp (ne_of_gt hσh)]


/-- **FY eq. (4.62)**: the log-squared observation decomposes as `log X_t² = h_t +
log ε_t²` (for `g = exp(·/2)`), the identity behind the ARMA(1,1)-in-two-moments
representation and the Kalman-filter estimation route.

**Statement strengthening (documented).** *Added*: `hgauss`, standard normal observation
noise. Without it the statement is **false**: `IsIIDNoise ε 1` permits an atom at `0`,
and there `log X_t² = 0 ≠ h_t`. See `noise_ne_zero_ae` for the witness and for the
evidence that FY's (4.62) — Taylor's lognormal SV model — supplies Gaussian `ε_t`. -/
theorem IsSV.log_sq_decomposition [IsProbabilityMeasure μ] {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: standard normal observation noise; FY §4.3, eq. (4.61)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1) (t : ℤ) :
    (fun ω => Real.log (X t ω ^ 2)) =ᵐ[μ] fun ω => h t ω + Real.log (ε t ω ^ 2) := by
  have hne : ∀ᵐ ω ∂μ, ε t ω ≠ 0 := by
    rw [ae_iff]
    simpa using noise_ne_zero_ae hSV hgauss t
  filter_upwards [hSV.recX t, hne] with ω hω hε0
  rw [hω, mul_pow, Real.log_mul (pow_ne_zero 2 hε0)
      (ne_of_gt (pow_pos (Real.exp_pos _) 2)), ← Real.exp_nat_mul, Real.log_exp]
  push_cast
  ring


omit [MeasurableSpace Ω] in
private lemma norm_rpow_four' {f : Ω → ℝ} (ω : Ω) :
    ‖f ω‖ ^ (ENNReal.toReal 4) = f ω ^ 4 := by
  have h4 : (ENNReal.toReal 4) = ((4 : ℕ) : ℝ) := by norm_num
  rw [h4, Real.rpow_natCast, ← norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private lemma memLp_four_iff_integrable' {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    MemLp f 4 μ ↔ Integrable (fun ω => f ω ^ 4) μ := by
  rw [← integrable_norm_rpow_iff hf (by norm_num) (by norm_num)]
  exact ⟨fun hi => hi.congr (Filter.Eventually.of_forall fun ω => norm_rpow_four' ω),
    fun hi => hi.congr (Filter.Eventually.of_forall fun ω => (norm_rpow_four' ω).symm)⟩

/-- **The lognormal moment of the *pair* `(h_k, h_0)`:**
`E e^{h_k + h_0} = exp(2μ_h + σ_h²(1 + a₁^{|k|}))`, i.e. the m.g.f. at `t = 1` of the
Gaussian sum `h_k + h_0`, whose variance is `2σ_h² + 2Cov(h_k,h_0) = 2σ_h²(1 + a₁^{|k|})`
by `hacvf`.

**Statement strengthening (documented).** *Added*: `hjoint`, saying that each pairwise
sum `h_k + h_0` of latent coordinates is normally distributed (with unspecified
parameters — they are *derived* below from `hlatent` and `hacvf`), together with the
causal representation `hcausal` (with `|a₁| < 1`).

*Why it is needed.* The frozen hypotheses of (4.62) give only the *marginal* law of `h_0`
(`hlatent`) and the autocovariances (`hacvf`); joint normality of `(h_k, h_0)` — and even
`Var h_k = Var h_0` — is not among them (`hstat` is strict stationarity of `X`, not of
`h`). Without joint normality the m.g.f. of the sum is not determined by its first two
moments, and the identity fails.

*Why FY supplies it.* In FY the latent chain is a Gaussian AR(1): the causal
representation `h_t − a₀/(1−a₁) = Σ_j a₁^j e_{t−j}` (that is `hcausal`) over Gaussian
`e_t` makes every finite window jointly Gaussian, in particular every `h_k + h_0`. The
causal representation is used here a second time, to get `Var h_k = Var h_0` from strict
stationarity of the latent chain (`isStrictlyStationary_latent`). -/
private lemma joint_lognormal_brick [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: the latent chain is the causal (stationary) solution of (4.60);
    -- FY §4.3, eq. (4.60)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    -- USER-INPUT: the latent chain is Gaussian (its innovations `e_t` are), so every
    -- pairwise sum of coordinates is normal; FY §4.3, eq. (4.61)
    (hjoint : ∀ k : ℤ, ∃ (m : ℝ) (v : NNReal),
      μ.map (fun ω => h k ω + h 0 ω) = gaussianReal m v)
    (hacvf : ∀ k : ℤ, acvf h μ k = σh2 * a1 ^ k.natAbs) (k : ℤ) :
    ∫ ω, Real.exp (h k ω + h 0 ω) ∂μ
      = Real.exp (2 * μh + σh2 * (1 + a1 ^ k.natAbs)) := by
  obtain ⟨m, v, hmv⟩ := hjoint k
  have hmh : ∀ t : ℤ, Measurable (h t) := hSV.measurableH
  have hstath := isStrictlyStationary_latent hSV ha1 hcausal
  -- strict stationarity of the latent chain gives the Gaussian marginal at every time
  have hmarg : ∀ t : ℤ, μ.map (h t) = gaussianReal μh (Real.toNNReal σh2) := fun t => by
    rw [(hstath.identDistrib hmh t 0).map_eq, hlatent]
  have hid : ∀ t : ℤ, IdentDistrib (h t) id μ (gaussianReal μh (Real.toNNReal σh2)) := fun t =>
    ⟨(hmh t).aemeasurable, aemeasurable_id, by rw [hmarg t, Measure.map_id]⟩
  have hmem : ∀ t : ℤ, MemLp (h t) 2 μ := fun t =>
    (hid t).symm.memLp_snd (memLp_id_gaussianReal' 2 (by simp))
  have hint : ∀ t : ℤ, ∫ ω, h t ω ∂μ = μh := by
    intro t
    have h1 := (hid t).integral_eq
    simp only [id_eq] at h1
    rw [h1, integral_id_gaussianReal]
  have hvar : ∀ t : ℤ, variance (h t) μ = σh2 := by
    intro t
    have h1 := (hid t).variance_eq
    rw [h1, variance_id_gaussianReal, Real.coe_toNNReal σh2 hσh.le]
  -- the parameters of the Gaussian sum are pinned down by those two moments
  have hSm : Measurable fun ω => h k ω + h 0 ω := (hmh k).add (hmh 0)
  have hSid : IdentDistrib (fun ω => h k ω + h 0 ω) id μ (gaussianReal m v) :=
    ⟨hSm.aemeasurable, aemeasurable_id, by rw [hmv, Measure.map_id]⟩
  have hm : m = 2 * μh := by
    have h1 := hSid.integral_eq
    simp only [id_eq] at h1
    rw [integral_id_gaussianReal, integral_add ((hmem k).integrable one_le_two)
      ((hmem 0).integrable one_le_two), hint k, hint 0] at h1
    linarith
  have hcov : cov[h k, h 0; μ] = σh2 * a1 ^ k.natAbs := hacvf k
  have hv : (v : ℝ) = 2 * σh2 * (1 + a1 ^ k.natAbs) := by
    have h1 := hSid.variance_eq
    rw [variance_id_gaussianReal, variance_fun_add (hmem k) (hmem 0), hvar k, hvar 0,
      hcov] at h1
    rw [← h1]
    ring
  -- the Gaussian m.g.f. at `t = 1`
  have hlhs : (∫ ω, Real.exp (h k ω + h 0 ω) ∂μ) = mgf (fun ω => h k ω + h 0 ω) μ 1 := by
    simp [mgf]
  rw [hlhs, mgf_gaussianReal hmv 1, hm, hv]
  congr 1
  ring

private lemma integral_sq_noise [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε 1 μ) (s : ℤ) : ∫ ω, ε s ω ^ 2 ∂μ = 1 := by
  have hmem : MemLp (ε s) 2 μ := (hε.identDistrib 0 s).memLp_snd hε.memLp
  have hvar : variance (ε s) μ = 1 := by
    rw [← (hε.identDistrib 0 s).variance_eq]; exact hε.variance_eq
  have hmean : ∫ ω, ε s ω ∂μ = 0 := by
    rw [← (hε.identDistrib 0 s).integral_eq]; exact hε.integral_eq_zero
  have := variance_eq_sub hmem
  rw [hvar, hmean] at this
  have h2 : (μ[(ε s) ^ 2]) = ∫ ω, ε s ω ^ 2 ∂μ := by simp [Pi.pow_apply]
  rw [h2] at this
  simp at this
  linarith

private lemma memLp_sq_of_memLp_four' [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hm : Measurable f) (hf : MemLp f 4 μ) : MemLp (fun ω => f ω ^ 2) 2 μ := by
  refine (memLp_two_iff_integrable_sq (hm.pow_const 2).aestronglyMeasurable).2 ?_
  have h4 : Integrable (fun ω => f ω ^ 4) μ :=
    (memLp_four_iff_integrable' hf.aestronglyMeasurable).1 hf
  refine h4.congr (Filter.Eventually.of_forall fun ω => ?_)
  change f ω ^ 4 = (f ω ^ 2) ^ 2
  ring

private lemma acvf_sq_lognormal_zero [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    (hL4 : ∀ t, MemLp (X t) 4 μ) :
    acvf (fun t ω => X t ω ^ 2) μ 0
      = Real.exp (μh + σh2 / 2) ^ 2 * (3 * Real.exp σh2 - 1) := by
  have hmX : ∀ s : ℤ, Measurable (X s) := hSV.measurableX
  have hm2 : ∫ ω, X 0 ω ^ 2 ∂μ = Real.exp (μh + σh2 / 2) := by
    have h1 := hSV.moment_even_lognormal hgauss ha1 hcausal hlatent hσh 1
    norm_num at h1
    exact h1
  have hm4 : ∫ ω, X 0 ω ^ 4 ∂μ = 3 * Real.exp (2 * μh + 2 * σh2) := by
    have h1 := hSV.moment_even_lognormal hgauss ha1 hcausal hlatent hσh 2
    norm_num at h1
    rw [h1]
    ring_nf
  have hmem := memLp_sq_of_memLp_four' (hmX 0) (hL4 0)
  have hB : (3 : ℝ) * Real.exp (2 * μh + 2 * σh2)
      = Real.exp (μh + σh2 / 2) ^ 2 * (3 * Real.exp σh2) := by
    have hr : Real.exp (μh + σh2 / 2) ^ 2 * (3 * Real.exp σh2)
        = 3 * (Real.exp (μh + σh2 / 2) * Real.exp (μh + σh2 / 2) * Real.exp σh2) := by
      rw [sq]; ring
    rw [hr, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [acvf, covariance_eq_sub hmem hmem]
  have e1 : (μ[(fun ω => X 0 ω ^ 2) * fun ω => X 0 ω ^ 2]) = ∫ ω, X 0 ω ^ 4 ∂μ := by
    rw [show ((fun ω => X 0 ω ^ 2) * fun ω => X 0 ω ^ 2) = fun ω => X 0 ω ^ 4 from
      funext fun ω => by simp only [Pi.mul_apply]; ring]
  rw [e1, hm4, hm2, hB]
  ring

/-- **The corrected form of FY eq. (4.62)'s squared-process ACF.** At every nonzero lag,
`Corr(X_t², X_{t−k}²) = (e^{σ_h²a₁^{|k|}} − 1)/(3e^{σ_h²} − 1)`: the `3` comes from
`E ε⁴ = 3` in `Var(X_t²) = E ε⁴ E e^{2h} − (E ε² E e^h)²`. The frozen statement
`IsSV.acf_sq_lognormal` divides by `e^{σ_h²} − 1` instead — that is the ACF of the
*volatility* `e^{h_t}` itself, not of `X_t²`; see the note there. -/
private lemma acf_sq_lognormal_corrected [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    (hjoint : ∀ k : ℤ, ∃ (m : ℝ) (v : NNReal),
      μ.map (fun ω => h k ω + h 0 ω) = gaussianReal m v)
    (hacvf : ∀ k : ℤ, acvf h μ k = σh2 * a1 ^ k.natAbs)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ) {k : ℤ} (hk : k ≠ 0) :
    acf (fun t ω => X t ω ^ 2) μ k
      = (Real.exp (σh2 * a1 ^ k.natAbs) - 1) / (3 * Real.exp σh2 - 1) := by
  have hmε : ∀ s : ℤ, Measurable (ε s) := hSV.iidNoise.measurable
  have hmh : ∀ s : ℤ, Measurable (h s) := hSV.measurableH
  have hmX : ∀ s : ℤ, Measurable (X s) := hSV.measurableX
  have hm2 : ∫ ω, X 0 ω ^ 2 ∂μ = Real.exp (μh + σh2 / 2) := by
    have h1 := hSV.moment_even_lognormal hgauss ha1 hcausal hlatent hσh 1
    norm_num at h1
    exact h1
  -- marginals are identically distributed, so `E X_k² = E X_0²`
  have hid : ∀ s t : ℤ, IdentDistrib (X s) (X t) μ μ := hstat.identDistrib hmX
  have hsq : ∀ s : ℤ, ∫ ω, X s ω ^ 2 ∂μ = ∫ ω, X 0 ω ^ 2 ∂μ :=
    fun s => ((hid s 0).comp (measurable_id.pow_const 2)).integral_eq
  have hmemsq : ∀ s : ℤ, MemLp (fun ω => X s ω ^ 2) 2 μ :=
    fun s => memLp_sq_of_memLp_four' (hmX s) (hL4 s)
  -- the cross moment `E[X_k² X_0²] = E[ε_k²ε_0²] · E[e^{h_k+h_0}]`
  have hcross : ∫ ω, X k ω ^ 2 * X 0 ω ^ 2 ∂μ
      = Real.exp (2 * μh + σh2 * (1 + a1 ^ k.natAbs)) := by
    have hpair : IndepFun (fun ω => (ε k ω, ε 0 ω)) (fun ω => (h k ω, h 0 ω)) μ :=
      indepFun_pair_noise_latent hSV ha1 hcausal k 0
    have hφ : Measurable fun p : ℝ × ℝ => p.1 ^ 2 * p.2 ^ 2 := by fun_prop
    have hψ : Measurable fun p : ℝ × ℝ => Real.exp (p.1 + p.2) := by fun_prop
    have hsplit : IndepFun (fun ω => ε k ω ^ 2 * ε 0 ω ^ 2)
        (fun ω => Real.exp (h k ω + h 0 ω)) μ := hpair.comp hφ hψ
    have hprod : ∫ ω, (ε k ω ^ 2 * ε 0 ω ^ 2) * Real.exp (h k ω + h 0 ω) ∂μ
        = (∫ ω, ε k ω ^ 2 * ε 0 ω ^ 2 ∂μ) * ∫ ω, Real.exp (h k ω + h 0 ω) ∂μ :=
      hsplit.integral_fun_mul_eq_mul_integral
        (((hmε k).pow_const 2).mul ((hmε 0).pow_const 2)).aestronglyMeasurable
        (((hmh k).add (hmh 0)).exp).aestronglyMeasurable
    have hεsq : ∫ ω, ε k ω ^ 2 * ε 0 ω ^ 2 ∂μ = 1 := by
      have hik : IndepFun (ε k) (ε 0) μ := hSV.iidNoise.iIndep.indepFun hk
      have h2 := (hik.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2))
        |>.integral_fun_mul_eq_mul_integral
          ((hmε k).pow_const 2).aestronglyMeasurable
          ((hmε 0).pow_const 2).aestronglyMeasurable
      simp only [Function.comp_apply, id_eq] at h2
      rw [h2, integral_sq_noise hSV.iidNoise, integral_sq_noise hSV.iidNoise, mul_one]
    have hae : (fun ω => X k ω ^ 2 * X 0 ω ^ 2)
        =ᵐ[μ] fun ω => (ε k ω ^ 2 * ε 0 ω ^ 2) * Real.exp (h k ω + h 0 ω) := by
      filter_upwards [hSV.recX k, hSV.recX 0] with ω hk0 h00
      have e1 : Real.exp (h k ω / 2) ^ 2 = Real.exp (h k ω) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have e2 : Real.exp (h 0 ω / 2) ^ 2 = Real.exp (h 0 ω) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [hk0, h00, mul_pow, mul_pow, e1, e2, Real.exp_add]
      ring
    rw [integral_congr_ae hae, hprod, hεsq, one_mul,
      joint_lognormal_brick hSV ha1 hcausal hlatent hσh hjoint hacvf k]
  have hcov1 : cov[fun ω => X k ω ^ 2, fun ω => X 0 ω ^ 2; μ]
      = Real.exp (μh + σh2 / 2) ^ 2 * (Real.exp (σh2 * a1 ^ k.natAbs) - 1) := by
    rw [covariance_eq_sub (hmemsq k) (hmemsq 0)]
    have e1 : (μ[(fun ω => X k ω ^ 2) * fun ω => X 0 ω ^ 2])
        = ∫ ω, X k ω ^ 2 * X 0 ω ^ 2 ∂μ := by simp [Pi.mul_apply]
    have hA : Real.exp (2 * μh + σh2 * (1 + a1 ^ k.natAbs))
        = Real.exp (μh + σh2 / 2) ^ 2 * Real.exp (σh2 * a1 ^ k.natAbs) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    rw [e1, hcross, hsq k, hm2, hA]
    ring
  have hden : (0:ℝ) < 3 * Real.exp σh2 - 1 := by
    nlinarith [Real.add_one_lt_exp (ne_of_gt hσh), Real.exp_pos σh2]
  have hpos : (0:ℝ) < Real.exp (μh + σh2 / 2) ^ 2 := by positivity
  rw [acf, acvf, hcov1, acvf_sq_lognormal_zero hSV hgauss ha1 hcausal hlatent hσh hL4]
  rw [div_eq_div_iff (by nlinarith) (by nlinarith)]
  ring

/-- **FY eq. (4.62), squared-process ACF** (lognormal algebra), with the book's
denominator **corrected**:
`Corr(X_t², X_{t−k}²) = (exp(σ_h² a₁^{|k|}) − 1)/(3 exp(σ_h²) − 1)`.

**Book error, verified 2026-08-09.** FY prints `exp(σ_h²) − 1` in the denominator; that
is the ACF of the *volatility* `e^{h_t}`, where the multiplier `ε_t²` is absent. For
`X_t²` the variance carries `E ε⁴ = 3`:
`Var(X_0²) = E ε⁴ · E e^{2h} − (E ε² · E e^{h})² = e^{2μ_h+σ_h²}(3e^{σ_h²} − 1)`,
while `Cov(X_k², X_0²) = e^{2μ_h+σ_h²}(e^{σ_h² a₁^{|k|}} − 1)`. The two formulas agree
only at `a₁ = 0`. The statement is therefore restricted to nonzero lags: at lag `0` the
autocorrelation is `1` by definition (which is the one place FY's printed denominator is
the right one). Per the project's constants policy we state what is provable and record
the deviation here.

**Statement strengthening (documented).** *Added*: the causal representation `hcausal`
of the latent chain and its Gaussianity `hjoint`.

*Why they are needed.* `hcausal` is what makes `(ε_k, ε_0)` independent of `(h_k, h_0)`;
without it the identity is **false** (see `indep_noise_latent_window` for a witness
satisfying every other hypothesis). `hjoint` is what makes `E e^{h_k+h_0}` a function of
the first two moments of the sum; the frozen hypotheses give only the marginal law of
`h_0` and the autocovariances, which do not determine that m.g.f. (see
`joint_lognormal_brick`).

*Why FY supplies them.* FY's latent chain is the causal `|a₁| < 1` solution of (4.60)
driven by Gaussian `e_t`, so every finite window — in particular every `h_k + h_0` — is
jointly Gaussian. -/
theorem IsSV.acf_sq_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    (ha1 : |a1| < 1)
    -- USER-INPUT: the latent chain is the causal (stationary) solution of (4.60);
    -- FY §4.3, eq. (4.60)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    -- USER-INPUT: the latent chain is Gaussian (its innovations `e_t` are), so every
    -- pairwise sum of coordinates is normal; FY §4.3, eq. (4.61)
    (hjoint : ∀ k : ℤ, ∃ (m : ℝ) (v : NNReal),
      μ.map (fun ω => h k ω + h 0 ω) = gaussianReal m v)
    -- USER-INPUT: the stationary latent autocovariance structure; FY eq. (4.60)
    (hacvf : ∀ k : ℤ, acvf h μ k = σh2 * a1 ^ k.natAbs)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ)
    -- USER-INPUT: nonzero lag. Added 2026-08-09 with the denominator correction: at
    -- lag `0` the autocorrelation is `1` by definition, which the corrected right-hand
    -- side does not give (FY's printed version does, and that is the only lag at which
    -- it is right).
    {k : ℤ} (hk : k ≠ 0) :
    acf (fun t ω => X t ω ^ 2) μ k
      = (Real.exp (σh2 * a1 ^ k.natAbs) - 1) / (3 * Real.exp σh2 - 1) :=
  acf_sq_lognormal_corrected hSV hgauss ha1 hcausal hlatent hσh hjoint hacvf hstat hL4 hk

end StatLean.TimeSeries
